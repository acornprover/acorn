use std::any::Any;
use std::collections::{BTreeMap, BinaryHeap, HashMap, HashSet, VecDeque};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::Path;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Condvar, Mutex};
use std::time::Duration;

use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Range};

use crate::build_cache::BuildCache;
use crate::certificate::{Certificate, CertificateStore, CertificateWorklist};
use crate::elaborator::error::Error as ElaborationError;
use crate::elaborator::goal::Goal;
use crate::elaborator::lowered_module::{LoweredItem, LoweredModule};
use crate::elaborator::lowering::LoweredGoal;
use crate::elaborator::node::NodeCursor;
use crate::elaborator::source::SourceType;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::processor::Processor;
use crate::project::{Project, ProjectLookup, ProjectView, ProjectViewModule};
use crate::proof_display::display_certificate_lines;
use crate::prover::{Outcome, ProverMode, SearchStats};

static NEXT_BUILD_ID: AtomicU32 = AtomicU32::new(1);
const MAX_CHECK_CERT_ERROR_CHARS: usize = 600;
const CHECK_CERT_ERROR_PREFIX_CHARS: usize = 320;
const CHECK_CERT_ERROR_SUFFIX_CHARS: usize = 140;

fn truncate_middle(
    text: &str,
    max_chars: usize,
    prefix_chars: usize,
    suffix_chars: usize,
) -> String {
    let char_count = text.chars().count();
    if char_count <= max_chars {
        return text.to_string();
    }

    let prefix_len = prefix_chars.min(char_count);
    let suffix_len = suffix_chars.min(char_count.saturating_sub(prefix_len));
    let prefix: String = text.chars().take(prefix_len).collect();
    let suffix: String = text
        .chars()
        .skip(char_count.saturating_sub(suffix_len))
        .collect();
    let omitted = char_count.saturating_sub(prefix_len + suffix_len);
    format!("{} ... [{} chars omitted] ... {}", prefix, omitted, suffix)
}

fn compact_check_cert_error(error: &str) -> String {
    let marker = "(generic debug:";
    let trimmed = match error.find(marker) {
        Some(index) => error[..index].trim_end(),
        None => error.trim_end(),
    };
    truncate_middle(
        trimmed,
        MAX_CHECK_CERT_ERROR_CHARS,
        CHECK_CERT_ERROR_PREFIX_CHARS,
        CHECK_CERT_ERROR_SUFFIX_CHARS,
    )
}

fn panic_payload_to_string(payload: Box<dyn Any + Send>) -> String {
    match payload.downcast::<String>() {
        Ok(message) => *message,
        Err(payload) => match payload.downcast::<&'static str>() {
            Ok(message) => (*message).to_string(),
            Err(_) => "panic with non-string payload".to_string(),
        },
    }
}

fn format_goal_panic_message(panic_message: &str, module_name: &str, external_line: u32) -> String {
    format!(
        "panic during certificate generation at {module_name}:{external_line}: {panic_message}\nRepro command: acorn verify {module_name} --line {external_line} --force-search",
    )
}

fn print_displayed_proof(
    bindings: &crate::elaborator::binding_map::BindingMap,
    lines: &[crate::certificate::CertificateLine],
) {
    let displayed = display_certificate_lines(bindings, lines);
    println!("displayed proof:");
    if displayed.is_empty() {
        println!("  <no proof>");
        return;
    }
    println!();

    let max_statement_width = displayed
        .iter()
        .map(|line| line.statement.len())
        .max()
        .unwrap_or(20)
        .max(20);
    println!(
        "  {:<width$}    Reason",
        "Statement",
        width = max_statement_width
    );
    for line in displayed {
        println!(
            "  {:<width$}    {}",
            line.statement,
            line.reason,
            width = max_statement_width
        );
    }
}

/// Filter for which goals to verify.
/// Line numbers are internal (0-based).
#[derive(Clone, Debug)]
pub enum GoalFilter {
    /// Verify only the goal at this exact line.
    SingleLine {
        module: ModuleDescriptor,
        line: u32,
        goal_index: Option<usize>,
    },
    /// Verify goals whose first_line falls within [start, end] (inclusive).
    LineRange {
        module: ModuleDescriptor,
        start: u32,
        end: u32,
    },
}

#[derive(Clone, Debug)]
struct EvalSkipTail<T> {
    max_skip: usize,
    checkpoints: Vec<T>,
}

impl<T: Clone> EvalSkipTail<T> {
    fn new(max_skip: usize) -> Self {
        Self {
            max_skip,
            checkpoints: Vec::new(),
        }
    }

    fn record_plain(&mut self, checkpoint: T) {
        if self.max_skip == 0 {
            return;
        }
        self.checkpoints.push(checkpoint);
        if self.checkpoints.len() > self.max_skip {
            self.checkpoints.remove(0);
        }
    }

    fn record_barrier(&mut self) {
        self.checkpoints.clear();
    }

    fn checkpoint_for(&self, skip: usize) -> Option<T> {
        if skip == 0 || skip > self.checkpoints.len() {
            return None;
        }
        self.checkpoints.get(self.checkpoints.len() - skip).cloned()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EvalProofKind {
    Empty,
    Nonempty,
}

#[derive(Clone, Debug, Default)]
struct EvalGoalCounts {
    empty: usize,
    nonempty: usize,
}

impl EvalGoalCounts {
    fn total(&self) -> usize {
        self.empty + self.nonempty
    }

    fn take(&mut self) -> Option<EvalProofKind> {
        if self.nonempty > 0 {
            self.nonempty -= 1;
            return Some(EvalProofKind::Nonempty);
        }
        if self.empty > 0 {
            self.empty -= 1;
            return Some(EvalProofKind::Empty);
        }
        None
    }
}

/// The Builder contains all the mutable state for a single build.
/// This is separate from the Project because you can read information from the Project from other
/// threads while a build is ongoing, but a Builder is only used by the build itself.
pub struct Builder<'a> {
    /// Read-only project state visible to the build.
    project: ProjectView,

    /// A single event handler is used across all modules.
    event_handler: Box<dyn FnMut(BuildEvent) + 'a>,

    pub status: BuildStatus,

    /// A unique id for each build.
    pub id: u32,

    /// Build metrics collected during verification.
    pub metrics: BuildMetrics,

    /// Per-module timing data collected during verification.
    pub module_timings: Vec<ModuleTiming>,

    /// When this flag is set, we emit build events when a goal is slow.
    pub log_when_slow: bool,

    /// When this flag is set, we emit build events for secondary errors.
    /// I.e., errors that happen when you try to import a module that itself has an error.
    pub log_secondary_errors: bool,

    /// In check mode, we make sure all goals are covered by existing certs.
    /// In this situation, it's an error if we run into any goal that is missing a cert,
    /// or any cert that fails checking.
    /// In normal mode, this is okay, because it could be that we modified the file.
    pub check_mode: bool,

    /// Whether we skip goals that match hashes in the cache.
    pub check_hashes: bool,

    /// In strict mode, reject any use of the axiom keyword.
    pub strict: bool,

    /// When this flag is set, the build exits immediately upon encountering any warning.
    /// This is useful for operations like the cleaner where any warning means the change
    /// should be reverted, so there's no point continuing verification.
    pub exit_on_warning: bool,

    /// Force proof search instead of using cached certificates.
    pub force_search: bool,

    /// Only search goals that have a nonempty cached proof, for prover evaluation.
    pub eval_mode: bool,

    /// Eval skip modes to run for each benchmark goal.
    pub eval_skip_modes: Vec<usize>,

    /// Owned module-local work for batch builds. When present, the Project only retains
    /// module exports and the builder consumes these lowered work packets.
    module_work: Option<Vec<(ModuleDescriptor, LoweredModule)>>,

    /// The current module we are proving.
    current_module: Option<ModuleDescriptor>,

    /// Number of goals encountered so far on the selected line for a single-line goal filter.
    single_line_goal_count: usize,

    /// Whether the current module has neither errors nor warnings.
    /// I guess if there is no current module, it's vacuously good.
    current_module_good: bool,

    /// The new build cache, that is being produced as a result of this build.
    pub build_cache: Option<BuildCache>,

    /// Tracks the number of used certificates per module (before appending unused certs).
    /// Used to trim unused certs if the final build status is Good.
    used_cert_counts: HashMap<ModuleDescriptor, usize>,

    /// When this is set, the builder only builds goals matching the filter.
    /// Line numbers are internal (0-based).
    pub goal_filter: Option<GoalFilter>,

    /// Print the checked, human-readable proof display for successful verification.
    /// Don't set it from within the language server.
    pub print_proof: bool,

    /// Print the detailed proof found by the prover for a successful search.
    /// Don't set it from within the language server.
    pub print_found_proof: bool,

    /// Print every activated clause in quoted source syntax after a search.
    /// Don't set it from within the language server.
    pub verbose: bool,

    /// Cancellation token to stop the build.
    cancellation_token: CancellationToken,

    /// When set, use this certificate instead of the cached one for single-goal verification.
    /// Only used when single_goal is also set.
    pub cert_override: Option<Certificate>,

    /// The verb to use in failure messages (e.g., "verified", "checked", "reproved").
    pub operation_verb: &'static str,

    /// Restrict proof search to the shallow fragment.
    pub shallow_search: bool,

    /// Timeout in seconds for proof search. Defaults to 5.0.
    pub timeout_secs: f32,

    /// Maximum number of non-factual activations before returning
    /// `ShallowExplosion` or `ActivationCap`.
    pub activation_limit: i32,

    /// Number of worker threads to use for full-module batch work.
    pub check_jobs: usize,
}

struct ModuleBuildResult {
    index: usize,
    status: BuildStatus,
    metrics: BuildMetrics,
    module_timings: Vec<ModuleTiming>,
    build_cache: Option<BuildCache>,
    used_cert_counts: HashMap<ModuleDescriptor, usize>,
    events: Vec<BuildEvent>,
}

struct ScheduledModule<'a> {
    index: usize,
    target: ModuleDescriptor,
    lowered: &'a LoweredModule,
    work_estimate: usize,
}

struct OwnedScheduledModule {
    index: usize,
    target: ModuleDescriptor,
    lowered: LoweredModule,
    work_estimate: usize,
}

pub(crate) struct LoadedModuleWorkBatch {
    pub project: Option<ProjectView>,
    pub modules: Vec<(ModuleDescriptor, LoweredModule)>,
    pub load_elapsed: Duration,
}

struct PipelineQueuedModule {
    index: usize,
    target: ModuleDescriptor,
    lowered: LoweredModule,
    project: ProjectView,
    work_estimate: usize,
}

impl PartialEq for PipelineQueuedModule {
    fn eq(&self, other: &Self) -> bool {
        self.work_estimate == other.work_estimate && self.index == other.index
    }
}

impl Eq for PipelineQueuedModule {}

impl PartialOrd for PipelineQueuedModule {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PipelineQueuedModule {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.work_estimate
            .cmp(&other.work_estimate)
            .then_with(|| other.index.cmp(&self.index))
    }
}

struct PipelineQueueState {
    modules: BinaryHeap<PipelineQueuedModule>,
    closed: bool,
    capacity: usize,
}

impl PipelineQueueState {
    fn new(capacity: usize) -> Self {
        Self {
            modules: BinaryHeap::new(),
            closed: false,
            capacity,
        }
    }
}

#[derive(Clone)]
struct ModuleWorkerConfig {
    check_mode: bool,
    check_hashes: bool,
    strict: bool,
    exit_on_warning: bool,
    force_search: bool,
    eval_mode: bool,
    eval_skip_modes: Vec<usize>,
    operation_verb: &'static str,
    shallow_search: bool,
    timeout_secs: f32,
    activation_limit: i32,
}

impl ModuleWorkerConfig {
    fn from_builder(builder: &Builder<'_>) -> Self {
        Self {
            check_mode: builder.check_mode,
            check_hashes: builder.check_hashes,
            strict: builder.strict,
            exit_on_warning: builder.exit_on_warning,
            force_search: builder.force_search,
            eval_mode: builder.eval_mode,
            eval_skip_modes: builder.eval_skip_modes.clone(),
            operation_verb: builder.operation_verb,
            shallow_search: builder.shallow_search,
            timeout_secs: builder.timeout_secs,
            activation_limit: builder.activation_limit,
        }
    }

    fn apply_to(&self, builder: &mut Builder<'_>) {
        builder.check_mode = self.check_mode;
        builder.check_hashes = self.check_hashes;
        builder.strict = self.strict;
        builder.exit_on_warning = self.exit_on_warning;
        builder.force_search = self.force_search;
        builder.eval_mode = self.eval_mode;
        builder.eval_skip_modes = self.eval_skip_modes.clone();
        builder.operation_verb = self.operation_verb;
        builder.shallow_search = self.shallow_search;
        builder.timeout_secs = self.timeout_secs;
        builder.activation_limit = self.activation_limit;
    }
}

/// Metrics collected during a build.
#[derive(Clone, Debug, Default)]
pub struct BuildMetrics {
    /// The total number of modules to be built.
    pub modules_total: i32,

    /// The number of modules we skipped due to caching.
    pub modules_cached: i32,

    /// The total number of goals to be verified.
    pub goals_total: i32,

    /// The number of goals that we have processed in the build.
    pub goals_done: i32,

    /// The number of goals that were successfully proven.
    pub goals_success: i32,

    /// The number of pending modules that were elaborated without proof checking.
    pub pending_modules_total: i32,

    /// The number of pending goals that were elaborated without proof checking.
    pub pending_goals_total: i32,

    /// How many certificates were reused from the cache.
    pub certs_cached: i32,

    /// How many cached certificates were checked.
    pub cert_checks_total: i32,

    /// How many cached certificate checks succeeded.
    pub cert_checks_success: i32,

    /// The total amount of time spent checking cached certificates, in seconds.
    pub cert_check_time: f64,

    /// How many cached certificates were unused.
    pub certs_unused: i32,

    /// How many new certificates were created in this build.
    pub certs_created: i32,

    /// How many proof searches we did.
    pub searches_total: i32,

    /// Number of proof searches that ended in success.
    pub searches_success: i32,

    /// The total amount of time spent in proof search, in seconds.
    pub search_time: f64,

    /// Number of proof searches that timed out.
    pub searches_timeout: i32,

    /// Number of proof searches that exhausted the search space.
    pub searches_exhausted: i32,

    /// Number of proof searches that hit the activation cap.
    pub searches_activation_cap: i32,

    /// Number of shallow searches that exhausted the shallow fragment.
    pub searches_shallow_exhausted: i32,

    /// Number of shallow searches that hit the shallow explosion guard.
    pub searches_shallow_explosion: i32,

    /// Number of proof searches that found an inconsistency.
    pub searches_inconsistent: i32,

    /// Number of proof searches that were interrupted.
    pub searches_interrupted: i32,

    /// Whether the build is a prover evaluation run.
    pub eval_mode: bool,

    /// Number of cached proof certificates in the selected benchmark corpus.
    pub eval_corpus_total: i32,

    /// Number of included benchmark proofs whose cached proof is empty.
    pub eval_corpus_empty: i32,

    /// Number of cached benchmark proofs that matched a current source goal.
    pub eval_corpus_matched: i32,

    /// Number of cached benchmark proofs that did not match a current source goal.
    pub eval_corpus_unmatched: i32,

    /// Number of current source goals skipped because they are not in the benchmark corpus.
    pub eval_goals_skipped_uncertified: i32,

    /// Per-skip proof search metrics for eval runs.
    pub eval_skip_metrics: Vec<EvalSkipMetrics>,

    /// Aggregate search instrumentation for eval runs.
    pub eval_search_instrumentation: EvalSearchInstrumentation,

    /// Time spent collecting loaded environments and reporting load errors.
    pub loading_time: f64,

    /// Time spent verifying goals, checking certificates, or running prover search.
    pub verification_time: f64,
}

#[derive(Clone, Debug, Default)]
pub struct EvalSkipMetrics {
    pub skip: usize,
    pub ineligible: i32,
    pub searches_total: i32,
    pub searches_success: i32,
    pub search_time: f64,
    pub searches_timeout: i32,
    pub searches_exhausted: i32,
    pub searches_activation_cap: i32,
    pub searches_shallow_exhausted: i32,
    pub searches_shallow_explosion: i32,
    pub searches_inconsistent: i32,
    pub searches_interrupted: i32,
}

impl EvalSkipMetrics {
    fn new(skip: usize) -> Self {
        Self {
            skip,
            ..Self::default()
        }
    }

    fn add(&mut self, other: &Self) {
        assert_eq!(self.skip, other.skip);
        self.ineligible += other.ineligible;
        self.searches_total += other.searches_total;
        self.searches_success += other.searches_success;
        self.search_time += other.search_time;
        self.searches_timeout += other.searches_timeout;
        self.searches_exhausted += other.searches_exhausted;
        self.searches_activation_cap += other.searches_activation_cap;
        self.searches_shallow_exhausted += other.searches_shallow_exhausted;
        self.searches_shallow_explosion += other.searches_shallow_explosion;
        self.searches_inconsistent += other.searches_inconsistent;
        self.searches_interrupted += other.searches_interrupted;
    }

    fn record_search(&mut self, outcome: Outcome, elapsed_secs: f64) {
        self.searches_total += 1;
        self.search_time += elapsed_secs;
        match outcome {
            Outcome::Success => self.searches_success += 1,
            Outcome::ShallowExhausted => self.searches_shallow_exhausted += 1,
            Outcome::ShallowExplosion => self.searches_shallow_explosion += 1,
            Outcome::Exhausted => self.searches_exhausted += 1,
            Outcome::Inconsistent => self.searches_inconsistent += 1,
            Outcome::Timeout => self.searches_timeout += 1,
            Outcome::Interrupted => self.searches_interrupted += 1,
            Outcome::ActivationCap => self.searches_activation_cap += 1,
        }
    }

    fn failure_buckets(&self) -> Vec<String> {
        search_failure_buckets(
            self.searches_timeout,
            self.searches_exhausted,
            self.searches_activation_cap,
            self.searches_shallow_exhausted,
            self.searches_shallow_explosion,
            self.searches_inconsistent,
            self.searches_interrupted,
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct EvalSearchInstrumentation {
    pub searches: i32,
    pub initial_passive_total: usize,
    pub initial_active_total: usize,
    pub final_passive_total: usize,
    pub final_active_total: usize,
    pub max_passive_total: usize,
    pub max_passive_peak: usize,
    pub activated_steps: usize,
    pub factual_activations: usize,
    pub nonfactual_activations: usize,
    pub generated_steps: usize,
    pub accepted_steps: usize,
    pub auto_rejected_steps: usize,
    pub simplified_away_steps: usize,
    pub passive_simplification_steps: usize,
    pub scoring_time_secs: f64,
    pub passive_indexing_time_secs: f64,
    pub activation_time_secs: f64,
    pub active_inference_time_secs: f64,
    pub active_simplification_time_secs: f64,
    pub passive_simplification_time_secs: f64,
    pub activated_by_rule: BTreeMap<String, usize>,
    pub generated_by_rule: BTreeMap<String, usize>,
}

impl EvalSearchInstrumentation {
    fn add_search(&mut self, stats: &SearchStats) {
        self.searches += 1;
        self.initial_passive_total += stats.initial_passive_len;
        self.initial_active_total += stats.initial_active_len;
        self.final_passive_total += stats.final_passive_len;
        self.final_active_total += stats.final_active_len;
        self.max_passive_total += stats.max_passive_len;
        self.max_passive_peak = self.max_passive_peak.max(stats.max_passive_len);
        self.activated_steps += stats.activated_steps;
        self.factual_activations += stats.factual_activations;
        self.nonfactual_activations += stats.nonfactual_activations;
        self.generated_steps += stats.generated_steps;
        self.accepted_steps += stats.accepted_steps;
        self.auto_rejected_steps += stats.auto_rejected_steps;
        self.simplified_away_steps += stats.simplified_away_steps;
        self.passive_simplification_steps += stats.passive_simplification_steps;
        self.scoring_time_secs += stats.scoring_time_secs;
        self.passive_indexing_time_secs += stats.passive_indexing_time_secs;
        self.activation_time_secs += stats.activation_time_secs;
        self.active_inference_time_secs += stats.active_inference_time_secs;
        self.active_simplification_time_secs += stats.active_simplification_time_secs;
        self.passive_simplification_time_secs += stats.passive_simplification_time_secs;
        for (rule, count) in &stats.activated_by_rule {
            *self.activated_by_rule.entry(rule.clone()).or_default() += count;
        }
        for (rule, count) in &stats.generated_by_rule {
            *self.generated_by_rule.entry(rule.clone()).or_default() += count;
        }
    }

    fn add(&mut self, other: &Self) {
        self.searches += other.searches;
        self.initial_passive_total += other.initial_passive_total;
        self.initial_active_total += other.initial_active_total;
        self.final_passive_total += other.final_passive_total;
        self.final_active_total += other.final_active_total;
        self.max_passive_total += other.max_passive_total;
        self.max_passive_peak = self.max_passive_peak.max(other.max_passive_peak);
        self.activated_steps += other.activated_steps;
        self.factual_activations += other.factual_activations;
        self.nonfactual_activations += other.nonfactual_activations;
        self.generated_steps += other.generated_steps;
        self.accepted_steps += other.accepted_steps;
        self.auto_rejected_steps += other.auto_rejected_steps;
        self.simplified_away_steps += other.simplified_away_steps;
        self.passive_simplification_steps += other.passive_simplification_steps;
        self.scoring_time_secs += other.scoring_time_secs;
        self.passive_indexing_time_secs += other.passive_indexing_time_secs;
        self.activation_time_secs += other.activation_time_secs;
        self.active_inference_time_secs += other.active_inference_time_secs;
        self.active_simplification_time_secs += other.active_simplification_time_secs;
        self.passive_simplification_time_secs += other.passive_simplification_time_secs;
        for (rule, count) in &other.activated_by_rule {
            *self.activated_by_rule.entry(rule.clone()).or_default() += count;
        }
        for (rule, count) in &other.generated_by_rule {
            *self.generated_by_rule.entry(rule.clone()).or_default() += count;
        }
    }

    fn avg_usize(value: usize, searches: i32) -> f64 {
        if searches == 0 {
            0.0
        } else {
            value as f64 / searches as f64
        }
    }

    fn avg_secs_ms(value: f64, searches: i32) -> f64 {
        if searches == 0 {
            0.0
        } else {
            1000.0 * value / searches as f64
        }
    }
}

fn search_failure_buckets(
    searches_timeout: i32,
    searches_exhausted: i32,
    searches_activation_cap: i32,
    searches_shallow_exhausted: i32,
    searches_shallow_explosion: i32,
    searches_inconsistent: i32,
    searches_interrupted: i32,
) -> Vec<String> {
    let mut buckets = Vec::new();
    if searches_timeout > 0 {
        buckets.push(format!("{} timeout", searches_timeout));
    }
    if searches_exhausted > 0 {
        buckets.push(format!("{} exhausted", searches_exhausted));
    }
    if searches_activation_cap > 0 {
        buckets.push(format!("{} activation cap", searches_activation_cap));
    }
    if searches_shallow_exhausted > 0 {
        buckets.push(format!("{} shallow exhausted", searches_shallow_exhausted));
    }
    if searches_shallow_explosion > 0 {
        buckets.push(format!("{} shallow explosion", searches_shallow_explosion));
    }
    if searches_inconsistent > 0 {
        buckets.push(format!("{} inconsistent", searches_inconsistent));
    }
    if searches_interrupted > 0 {
        buckets.push(format!("{} interrupted", searches_interrupted));
    }
    buckets
}

fn top_rule_summary(counts: &BTreeMap<String, usize>, limit: usize) -> Option<String> {
    if counts.is_empty() {
        return None;
    }

    let mut entries = counts.iter().collect::<Vec<_>>();
    entries.sort_by(|(rule_a, count_a), (rule_b, count_b)| {
        count_b.cmp(count_a).then_with(|| rule_a.cmp(rule_b))
    });

    let mut parts = entries
        .iter()
        .take(limit)
        .map(|(rule, count)| format!("{} {}", count, rule))
        .collect::<Vec<_>>();
    if entries.len() > limit {
        let other = entries
            .iter()
            .skip(limit)
            .map(|(_, count)| **count)
            .sum::<usize>();
        parts.push(format!("{} other", other));
    }
    Some(parts.join(", "))
}

/// Timing data for work performed on one module during the verification phase.
#[derive(Clone, Debug)]
pub struct ModuleTiming {
    pub module: ModuleDescriptor,
    pub goals_total: i32,
    pub goals_done: i32,
    pub certs_cached: i32,
    pub certs_created: i32,
    pub cert_checks_total: i32,
    pub cert_checks_success: i32,
    pub cert_check_time: f64,
    pub searches_total: i32,
    pub searches_success: i32,
    pub search_time: f64,
    pub elapsed: f64,
    pub skipped: bool,
}

#[derive(Debug)]
pub struct BuildError {
    pub range: Range,
    pub message: String,
}

impl BuildError {
    pub fn new(range: Range, message: impl Into<String>) -> Self {
        BuildError {
            range,
            message: message.into(),
        }
    }

    /// A build error that occurred at a particular goal.
    fn goal(goal: &Goal, message: impl Into<String>) -> Self {
        let message = format!("{} {}", goal.name, message.into());
        BuildError {
            range: goal.proposition.source.range,
            message,
        }
    }
}

impl From<BuildError> for String {
    fn from(error: BuildError) -> String {
        error.message
    }
}

impl BuildMetrics {
    pub fn new() -> Self {
        Self::default()
    }

    fn eval_skip_metrics_mut(&mut self, skip: usize) -> &mut EvalSkipMetrics {
        if let Some(index) = self
            .eval_skip_metrics
            .iter()
            .position(|metrics| metrics.skip == skip)
        {
            return &mut self.eval_skip_metrics[index];
        }
        self.eval_skip_metrics.push(EvalSkipMetrics::new(skip));
        self.eval_skip_metrics
            .sort_unstable_by_key(|metrics| metrics.skip);
        let index = self
            .eval_skip_metrics
            .iter()
            .position(|metrics| metrics.skip == skip)
            .expect("just inserted skip metrics");
        &mut self.eval_skip_metrics[index]
    }

    fn ensure_eval_skip_metrics(&mut self, skip: usize) {
        self.eval_skip_metrics_mut(skip);
    }

    fn record_eval_skip_ineligible(&mut self, skip: usize) {
        self.eval_skip_metrics_mut(skip).ineligible += 1;
    }

    fn record_eval_skip_search(&mut self, skip: usize, outcome: Outcome, elapsed_secs: f64) {
        self.eval_skip_metrics_mut(skip)
            .record_search(outcome, elapsed_secs);
    }

    fn record_eval_search_instrumentation(&mut self, stats: &SearchStats) {
        self.eval_search_instrumentation.add_search(stats);
    }

    fn add_module_result(&mut self, result: &BuildMetrics) {
        self.modules_cached += result.modules_cached;
        self.goals_done += result.goals_done;
        self.goals_success += result.goals_success;
        self.certs_cached += result.certs_cached;
        self.cert_checks_total += result.cert_checks_total;
        self.cert_checks_success += result.cert_checks_success;
        self.cert_check_time += result.cert_check_time;
        self.certs_unused += result.certs_unused;
        self.certs_created += result.certs_created;
        self.searches_total += result.searches_total;
        self.searches_success += result.searches_success;
        self.search_time += result.search_time;
        self.searches_timeout += result.searches_timeout;
        self.searches_exhausted += result.searches_exhausted;
        self.searches_activation_cap += result.searches_activation_cap;
        self.searches_shallow_exhausted += result.searches_shallow_exhausted;
        self.searches_shallow_explosion += result.searches_shallow_explosion;
        self.searches_inconsistent += result.searches_inconsistent;
        self.searches_interrupted += result.searches_interrupted;
        self.eval_mode |= result.eval_mode;
        self.eval_corpus_total += result.eval_corpus_total;
        self.eval_corpus_empty += result.eval_corpus_empty;
        self.eval_corpus_matched += result.eval_corpus_matched;
        self.eval_corpus_unmatched += result.eval_corpus_unmatched;
        self.eval_goals_skipped_uncertified += result.eval_goals_skipped_uncertified;
        for skip_metrics in &result.eval_skip_metrics {
            self.eval_skip_metrics_mut(skip_metrics.skip)
                .add(skip_metrics);
        }
        self.eval_search_instrumentation
            .add(&result.eval_search_instrumentation);
    }

    pub fn info_lines(&self) -> Vec<String> {
        let mut lines = Vec::new();

        if self.eval_mode {
            lines.push(format!(
                "{} benchmark proofs with eligible cached proofs",
                self.eval_corpus_total
            ));
            if self.eval_corpus_empty > 0 {
                lines.push(format!(
                    "{} benchmark proofs have empty cached proofs (omitted for skip=0)",
                    self.eval_corpus_empty
                ));
            }
            lines.push(format!(
                "{} benchmark goals matched current source",
                self.eval_corpus_matched
            ));
            if self.eval_corpus_unmatched > 0 {
                lines.push(format!(
                    "{} benchmark proofs unmatched by current source",
                    self.eval_corpus_unmatched
                ));
            }
            if self.eval_goals_skipped_uncertified > 0 {
                lines.push(format!(
                    "{} current goals skipped without eligible cached proofs",
                    self.eval_goals_skipped_uncertified
                ));
            }
        }

        if !self.eval_mode {
            if self.modules_cached > 0 {
                lines.push(format!(
                    "{}/{} modules cached",
                    self.modules_cached, self.modules_total
                ));
            }
            if self.certs_created > 0 {
                lines.push(format!("{} certificates created", self.certs_created));
            }
            if self.certs_cached > 0 {
                lines.push(format!("{} certificates cached", self.certs_cached));
            }
            if self.certs_unused > 0 {
                lines.push(format!("{} certificates unused", self.certs_unused));
            }
        }
        lines.push(format!("{} searches performed", self.searches_total));
        if self.searches_total > 0 {
            let success_percent = 100.0 * self.searches_success as f64 / self.searches_total as f64;
            lines.push(format!("{:.2}% search success rate", success_percent));
            let search_time_ms = 1000.0 * self.search_time / self.searches_total as f64;
            lines.push(format!("{:.1} ms average search time", search_time_ms));
        }
        let failures = self.searches_total - self.searches_success;
        if failures > 0 {
            let buckets = search_failure_buckets(
                self.searches_timeout,
                self.searches_exhausted,
                self.searches_activation_cap,
                self.searches_shallow_exhausted,
                self.searches_shallow_explosion,
                self.searches_inconsistent,
                self.searches_interrupted,
            );
            if !buckets.is_empty() {
                lines.push(format!("search failures: {}", buckets.join(", ")));
            }
        }
        if self.eval_mode && self.eval_search_instrumentation.searches > 0 {
            let stats = &self.eval_search_instrumentation;
            let searches = stats.searches;
            lines.push(format!(
                "eval internals: {:.1} initial passive avg, {:.1} max passive avg ({} peak), {:.1} final passive avg",
                EvalSearchInstrumentation::avg_usize(stats.initial_passive_total, searches),
                EvalSearchInstrumentation::avg_usize(stats.max_passive_total, searches),
                stats.max_passive_peak,
                EvalSearchInstrumentation::avg_usize(stats.final_passive_total, searches),
            ));
            lines.push(format!(
                "eval activations: {} factual ({:.1}/search), {} non-factual ({:.1}/search)",
                stats.factual_activations,
                EvalSearchInstrumentation::avg_usize(stats.factual_activations, searches),
                stats.nonfactual_activations,
                EvalSearchInstrumentation::avg_usize(stats.nonfactual_activations, searches),
            ));
            lines.push(format!(
                "eval generated: {} candidates ({:.1}/search), {} accepted, {} auto-rejected, {} simplified away, {} passive simplifications",
                stats.generated_steps,
                EvalSearchInstrumentation::avg_usize(stats.generated_steps, searches),
                stats.accepted_steps,
                stats.auto_rejected_steps,
                stats.simplified_away_steps,
                stats.passive_simplification_steps,
            ));
            lines.push(format!(
                "eval timing internals: {:.1} ms active inference/search, {:.1} ms active simplification/search, {:.1} ms passive simplification/search, {:.1} ms scoring/search, {:.1} ms passive indexing/search",
                EvalSearchInstrumentation::avg_secs_ms(stats.active_inference_time_secs, searches),
                EvalSearchInstrumentation::avg_secs_ms(stats.active_simplification_time_secs, searches),
                EvalSearchInstrumentation::avg_secs_ms(stats.passive_simplification_time_secs, searches),
                EvalSearchInstrumentation::avg_secs_ms(stats.scoring_time_secs, searches),
                EvalSearchInstrumentation::avg_secs_ms(stats.passive_indexing_time_secs, searches),
            ));
            if let Some(summary) = top_rule_summary(&stats.activated_by_rule, 6) {
                lines.push(format!("eval activated rules: {}", summary));
            }
            if let Some(summary) = top_rule_summary(&stats.generated_by_rule, 6) {
                lines.push(format!("eval generated rules: {}", summary));
            }
        }
        let show_skip_metrics = self.eval_mode
            && self
                .eval_skip_metrics
                .iter()
                .any(|metrics| metrics.skip != 0 || metrics.ineligible > 0);
        if show_skip_metrics {
            for metrics in &self.eval_skip_metrics {
                let mut line = format!(
                    "skip={}: {}/{} searches succeeded",
                    metrics.skip, metrics.searches_success, metrics.searches_total
                );
                if metrics.ineligible > 0 {
                    line.push_str(&format!(", {} ineligible", metrics.ineligible));
                }
                if metrics.searches_total > 0 {
                    let search_time_ms =
                        1000.0 * metrics.search_time / metrics.searches_total as f64;
                    line.push_str(&format!(", {:.1} ms average", search_time_ms));
                }
                lines.push(line);
                let buckets = metrics.failure_buckets();
                if !buckets.is_empty() {
                    lines.push(format!(
                        "skip={} search failures: {}",
                        metrics.skip,
                        buckets.join(", ")
                    ));
                }
            }
        }
        if self.eval_mode {
            lines.push(format!(
                "{}/{} benchmark searches succeeded",
                self.searches_success, self.searches_total
            ));
        } else {
            lines.push(format!("{}/{} OK", self.goals_success, self.goals_total));
            if self.pending_modules_total > 0 {
                lines.push(format!(
                    "{} pending goals elaborated in {} modules",
                    self.pending_goals_total, self.pending_modules_total
                ));
            }
        }

        lines
    }

    pub fn print(&self, status: BuildStatus) {
        println!();
        for line in self.info_lines() {
            println!("{}", line);
        }
        match status {
            BuildStatus::Error => {
                println!("Build failed.");
            }
            BuildStatus::Warning => {
                if self.eval_mode {
                    println!("Evaluation completed with failed searches.");
                } else {
                    println!("Verification failed.");
                }
            }
            BuildStatus::Good => {
                if self.eval_mode {
                    println!("Evaluation succeeded.");
                } else {
                    println!("Verification succeeded.");
                }
            }
        }
    }
}

impl ModuleTiming {
    fn from_metrics_delta(
        module: ModuleDescriptor,
        goals_total: i32,
        before: &BuildMetrics,
        after: &BuildMetrics,
        elapsed: Duration,
        skipped: bool,
    ) -> Self {
        Self {
            module,
            goals_total,
            goals_done: after.goals_done - before.goals_done,
            certs_cached: after.certs_cached - before.certs_cached,
            certs_created: after.certs_created - before.certs_created,
            cert_checks_total: after.cert_checks_total - before.cert_checks_total,
            cert_checks_success: after.cert_checks_success - before.cert_checks_success,
            cert_check_time: after.cert_check_time - before.cert_check_time,
            searches_total: after.searches_total - before.searches_total,
            searches_success: after.searches_success - before.searches_success,
            search_time: after.search_time - before.search_time,
            elapsed: elapsed.as_secs_f64(),
            skipped,
        }
    }
}

/// A "build" is when we verify a set of goals, determined by a Project.
/// For each build, we report many  build events.
#[derive(Debug, Clone)]
pub struct BuildEvent {
    /// Which build this is an event for.
    pub build_id: u32,

    /// Current progress is done / total.
    /// This is across all modules.
    pub progress: Option<(i32, i32)>,

    /// Human-readable
    pub log_message: Option<String>,

    /// The module that the build event is coming from.
    pub module: ModuleDescriptor,

    /// Whenever we run into a problem, report a diagnostic.
    pub diagnostic: Option<Diagnostic>,

    /// Whenever we verify a goal, report the lines that the goal covers.
    /// Note that this is only the final goal. Subgoals might have failed to verify.
    pub verified: Option<(u32, u32)>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BuildStatus {
    /// No problems of any kind
    Good,

    /// Warnings indicate code that parses okay but can't be verified
    Warning,

    /// Errors indicate either the user entered bad code, or we ran into a bug in the build process
    Error,
}

impl BuildStatus {
    pub fn verb(&self) -> &str {
        match self {
            BuildStatus::Good => "succeeded",
            BuildStatus::Warning => "warned",
            BuildStatus::Error => "errored",
        }
    }

    pub fn warn(&mut self) {
        if *self == BuildStatus::Good {
            *self = BuildStatus::Warning;
        }
    }

    pub fn is_error(&self) -> bool {
        matches!(self, BuildStatus::Error)
    }

    pub fn is_good(&self) -> bool {
        matches!(self, BuildStatus::Good)
    }
}

impl<'a> Builder<'a> {
    pub fn new(
        project: &'a Project,
        cancellation_token: CancellationToken,
        event_handler: impl FnMut(BuildEvent) + 'a,
    ) -> Self {
        Self::new_with_view(ProjectView::new(project), cancellation_token, event_handler)
    }

    pub fn new_with_view(
        project: ProjectView,
        cancellation_token: CancellationToken,
        event_handler: impl FnMut(BuildEvent) + 'a,
    ) -> Self {
        let event_handler = Box::new(event_handler);
        Builder {
            project,
            event_handler,
            status: BuildStatus::Good,
            id: NEXT_BUILD_ID.fetch_add(1, Ordering::SeqCst),
            metrics: BuildMetrics::new(),
            module_timings: Vec::new(),
            log_when_slow: false,
            log_secondary_errors: true,
            check_mode: false,
            check_hashes: true,
            strict: false,
            exit_on_warning: false,
            force_search: false,
            eval_mode: false,
            eval_skip_modes: vec![0, 1],
            module_work: None,
            current_module: None,
            single_line_goal_count: 0,
            current_module_good: true,
            build_cache: None,
            used_cert_counts: HashMap::new(),
            goal_filter: None,
            print_proof: false,
            print_found_proof: false,
            verbose: false,
            cancellation_token,
            cert_override: None,
            operation_verb: "verified",
            shallow_search: false,
            timeout_secs: 5.0,
            activation_limit: 2000,
            check_jobs: 1,
        }
    }

    fn project(&self) -> &ProjectView {
        &self.project
    }

    pub fn set_module_work(&mut self, module_work: Vec<(ModuleDescriptor, LoweredModule)>) {
        self.module_work = Some(module_work);
    }

    pub fn set_project_view(&mut self, project: ProjectView) {
        self.project = project;
    }

    pub fn begin_module_work_build(&mut self, target_count: usize) {
        self.prepare_eval_mode();
        self.build_cache = Some(BuildCache::new(self.project().build_dir().clone()));
        self.log_global(format!("verifying {} modules...", target_count));
    }

    pub fn add_loaded_module_work(&mut self, modules: &[(ModuleDescriptor, LoweredModule)]) {
        for (_, lowered) in modules {
            self.lowered_module_loaded(lowered);
        }
        self.metrics.modules_total += modules.len() as i32;
    }

    pub fn process_module_work_batch(
        &mut self,
        modules: Vec<(ModuleDescriptor, LoweredModule)>,
        next_index: &mut usize,
    ) {
        if modules.is_empty() || self.status.is_error() {
            return;
        }

        let verification_start = std::time::Instant::now();
        if self.can_build_modules_in_parallel(modules.len()) {
            let modules = modules
                .into_iter()
                .map(|(target, lowered)| {
                    let index = *next_index;
                    *next_index += 1;
                    (index, target, lowered)
                })
                .collect();
            self.build_owned_modules_parallel(modules);
            self.metrics.verification_time += verification_start.elapsed().as_secs_f64();
            return;
        }

        for (target, lowered) in modules {
            let index = *next_index;
            *next_index += 1;
            self.process_one_owned_module(index, target, lowered);
            if self.exit_on_warning && !self.status.is_good() {
                break;
            }
            if self.status.is_error() {
                break;
            }
        }
        self.metrics.verification_time += verification_start.elapsed().as_secs_f64();
    }

    pub(crate) fn can_pipeline_module_work(&self, target_count: usize) -> bool {
        self.can_build_modules_in_parallel(target_count)
    }

    pub(crate) fn process_module_work_pipeline<L>(
        &mut self,
        mut load_next: L,
    ) -> Result<(Duration, HashSet<ModuleDescriptor>), String>
    where
        L: FnMut() -> Result<Option<LoadedModuleWorkBatch>, String>,
    {
        let worker_count = self.check_jobs.max(1);
        // Keep the producer from retaining too many lowered modules while workers are busy.
        // The modules are large enough that a deep queue costs more memory than it saves time.
        let queue_capacity = (worker_count / 2).max(1);
        let queue = Arc::new((
            Mutex::new(PipelineQueueState::new(queue_capacity)),
            Condvar::new(),
        ));
        let (result_tx, result_rx) = mpsc::channel();
        let worker_config = ModuleWorkerConfig::from_builder(self);
        let cancellation_token = self.cancellation_token.clone();
        let mut processed = HashSet::new();
        let mut next_index = 0usize;
        let mut next_merge_index = 0usize;
        let mut pending_results = BTreeMap::new();
        let mut active_jobs = 0usize;
        let mut load_elapsed = Duration::default();
        let mut verification_start = None;
        let mut loader_error = None;

        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..worker_count {
                let queue = Arc::clone(&queue);
                let result_tx = result_tx.clone();
                let token = cancellation_token.clone();
                let config = worker_config.clone();
                handles.push(scope.spawn(move || loop {
                    let module = {
                        let (lock, cvar) = &*queue;
                        let mut state = lock.lock().expect("pipeline work queue poisoned");
                        loop {
                            if let Some(module) = state.modules.pop() {
                                cvar.notify_all();
                                break Some(module);
                            }
                            if state.closed {
                                break None;
                            }
                            state = cvar.wait(state).expect("pipeline work queue poisoned");
                        }
                    };
                    let Some(module) = module else {
                        break;
                    };
                    let result = Self::build_module_on_worker(
                        module.project,
                        token.clone(),
                        module.index,
                        module.target,
                        &module.lowered,
                        &config,
                    );
                    if result_tx.send(result).is_err() {
                        break;
                    }
                }));
            }
            drop(result_tx);

            loop {
                self.drain_pipeline_results(
                    &result_rx,
                    &mut active_jobs,
                    &mut pending_results,
                    &mut next_merge_index,
                );
                if self.status.is_error() || (self.exit_on_warning && !self.status.is_good()) {
                    break;
                }

                match load_next() {
                    Ok(Some(batch)) => {
                        load_elapsed += batch.load_elapsed;
                        if batch.modules.is_empty() {
                            continue;
                        }
                        let project = batch
                            .project
                            .expect("nonempty module work batches should include a project view");
                        self.set_project_view(project.clone());
                        self.add_loaded_module_work(&batch.modules);
                        for (target, lowered) in batch.modules {
                            processed.insert(target.clone());
                            let work_estimate = self.module_work_estimate(&target, &lowered);
                            let module = PipelineQueuedModule {
                                index: next_index,
                                target,
                                lowered,
                                project: project.clone(),
                                work_estimate,
                            };
                            verification_start.get_or_insert_with(std::time::Instant::now);
                            next_index += 1;
                            self.enqueue_pipeline_module(&queue, module);
                            active_jobs += 1;
                            self.drain_pipeline_results(
                                &result_rx,
                                &mut active_jobs,
                                &mut pending_results,
                                &mut next_merge_index,
                            );
                            if self.status.is_error()
                                || (self.exit_on_warning && !self.status.is_good())
                            {
                                break;
                            }
                        }
                    }
                    Ok(None) => break,
                    Err(error) => {
                        loader_error = Some(error);
                        break;
                    }
                }
            }

            {
                let (lock, cvar) = &*queue;
                let mut state = lock.lock().expect("pipeline work queue poisoned");
                state.closed = true;
                cvar.notify_all();
            }

            while active_jobs > 0 {
                match result_rx.recv() {
                    Ok(result) => {
                        active_jobs -= 1;
                        self.merge_pipeline_result(
                            result,
                            &mut pending_results,
                            &mut next_merge_index,
                        );
                    }
                    Err(_) => break,
                }
            }

            for handle in handles {
                match handle.join() {
                    Ok(()) => {}
                    Err(payload) => std::panic::resume_unwind(payload),
                }
            }
        });

        if let Some(verification_start) = verification_start {
            self.metrics.verification_time += verification_start.elapsed().as_secs_f64();
        }

        if let Some(error) = loader_error {
            return Err(error);
        }
        Ok((load_elapsed, processed))
    }

    fn enqueue_pipeline_module(
        &self,
        queue: &Arc<(Mutex<PipelineQueueState>, Condvar)>,
        module: PipelineQueuedModule,
    ) {
        let (lock, cvar) = &**queue;
        let mut state = lock.lock().expect("pipeline work queue poisoned");
        while state.modules.len() >= state.capacity && !state.closed {
            state = cvar.wait(state).expect("pipeline work queue poisoned");
        }
        if state.closed {
            return;
        }
        state.modules.push(module);
        cvar.notify_all();
    }

    fn drain_pipeline_results(
        &mut self,
        result_rx: &mpsc::Receiver<ModuleBuildResult>,
        active_jobs: &mut usize,
        pending_results: &mut BTreeMap<usize, ModuleBuildResult>,
        next_merge_index: &mut usize,
    ) {
        while let Ok(result) = result_rx.try_recv() {
            *active_jobs = active_jobs.saturating_sub(1);
            self.merge_pipeline_result(result, pending_results, next_merge_index);
        }
    }

    fn merge_pipeline_result(
        &mut self,
        result: ModuleBuildResult,
        pending_results: &mut BTreeMap<usize, ModuleBuildResult>,
        next_merge_index: &mut usize,
    ) {
        pending_results.insert(result.index, result);
        while let Some(result) = pending_results.remove(&*next_merge_index) {
            self.merge_module_build_result(result);
            *next_merge_index += 1;
        }
    }

    fn merge_module_build_result(&mut self, result: ModuleBuildResult) {
        self.metrics.add_module_result(&result.metrics);
        self.module_timings.extend(result.module_timings);
        if let Some(build_cache) = result.build_cache {
            self.build_cache
                .as_mut()
                .expect("parallel module builds should have a parent build cache")
                .merge_updates_from(build_cache);
        }
        self.used_cert_counts.extend(result.used_cert_counts);
        match result.status {
            BuildStatus::Error => self.status = BuildStatus::Error,
            BuildStatus::Warning if self.status.is_good() => self.status = BuildStatus::Warning,
            BuildStatus::Good | BuildStatus::Warning => {}
        }

        for mut event in result.events {
            event.build_id = self.id;
            if event.progress.is_some() {
                event.progress = Some((self.metrics.goals_done, self.metrics.goals_total));
            }
            (self.event_handler)(event);
        }
    }

    pub fn finish_module_work_build(&mut self) {
        if self.status.is_good() {
            self.trim_unused_certificates();
        }
    }

    pub fn log_unprocessed_target_states(
        &mut self,
        targets: &[ModuleDescriptor],
        processed: &HashSet<ModuleDescriptor>,
    ) {
        for target in targets {
            if processed.contains(target) {
                continue;
            }
            let project = self.project().clone();
            match project.get_module(target) {
                ProjectViewModule::Ok(_) => {
                    self.log_global(format!("error: module {} has no lowered work", target));
                }
                ProjectViewModule::Error(e) => {
                    if e.indirect {
                        if self.log_secondary_errors {
                            self.log_global(e.to_string());
                        }
                    } else {
                        self.log_loading_error(target, e);
                    }
                }
                ProjectViewModule::None => {
                    self.log_global(format!("error: module {} is not loaded", target));
                }
                ProjectViewModule::Loading | ProjectViewModule::Registered => {}
            }
        }
    }

    fn record_module_timing(
        &mut self,
        module: ModuleDescriptor,
        goals_total: i32,
        before: &BuildMetrics,
        elapsed: Duration,
        skipped: bool,
    ) {
        self.module_timings.push(ModuleTiming::from_metrics_delta(
            module,
            goals_total,
            before,
            &self.metrics,
            elapsed,
            skipped,
        ));
    }

    fn record_cert_check(&mut self, elapsed: Duration, succeeded: bool) {
        self.metrics.cert_checks_total += 1;
        if succeeded {
            self.metrics.cert_checks_success += 1;
        }
        self.metrics.cert_check_time += elapsed.as_secs_f64();
    }

    fn eval_goal_counts(
        &self,
        target: &ModuleDescriptor,
    ) -> Option<HashMap<String, EvalGoalCounts>> {
        if !self.eval_mode {
            return None;
        }

        let include_empty = self.eval_skip_modes.iter().any(|&skip| skip > 0);
        let mut counts: HashMap<String, EvalGoalCounts> = HashMap::new();
        if let Some(store) = self.project().build_cache().get_certificates(target) {
            for cert in &store.certs {
                if let Some(proof) = &cert.proof {
                    if proof.is_empty() {
                        if include_empty {
                            counts.entry(cert.goal.clone()).or_default().empty += 1;
                        }
                    } else {
                        counts.entry(cert.goal.clone()).or_default().nonempty += 1;
                    }
                }
            }
        }
        Some(counts)
    }

    fn default_event(&self) -> BuildEvent {
        BuildEvent {
            build_id: self.id,
            progress: None,
            log_message: None,
            module: self.module().clone(),
            diagnostic: None,
            verified: None,
        }
    }

    /// Returns Anonymous while loading
    fn module(&self) -> ModuleDescriptor {
        match &self.current_module {
            None => ModuleDescriptor::Anonymous,
            Some(m) => m.clone(),
        }
    }

    pub fn lowered_module_loaded(&mut self, lowered: &LoweredModule) {
        let goal_count = lowered.goal_count() as i32;
        if self.project().is_surface_check_module(lowered.module_id) {
            self.metrics.pending_modules_total += 1;
            self.metrics.pending_goals_total += goal_count;
        } else {
            self.metrics.goals_total += goal_count;
        }
    }

    /// Called when the entire loading phase is done.
    pub fn loading_phase_complete(&mut self) {
        let event = BuildEvent {
            progress: Some((0, self.metrics.goals_total)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    /// Logs an informational message not tied to any particular location.
    /// In VS Code this will only appear in a pane, so it's only useful for debugging.
    /// You can't expect a typical user to see these.
    /// This doesn't change build status.
    pub fn log_global(&mut self, message: String) {
        let event = BuildEvent {
            log_message: Some(message),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    /// Logs an error during the loading phase, that can be localized to a particular place.
    pub fn log_loading_error(&mut self, descriptor: &ModuleDescriptor, error: &ElaborationError) {
        let display_path = self.project().display_path(descriptor);
        let line = error.range().start.line + 1;
        let log_message = format!(
            "{}, line {}: elaboration error: {}",
            display_path, line, error
        );
        let diagnostic = Diagnostic {
            range: error.range(),
            severity: Some(DiagnosticSeverity::ERROR),
            message: error.to_string(),
            ..Diagnostic::default()
        };
        let event = BuildEvent {
            log_message: Some(log_message),
            module: descriptor.clone(),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        };
        (self.event_handler)(event);
        self.status = BuildStatus::Error;
    }

    /// Called when we start proving a module.
    pub fn module_proving_started(&mut self, descriptor: ModuleDescriptor) {
        self.current_module = Some(descriptor);
        self.current_module_good = true;
    }

    /// Returns whether the module completed without any errors or warnings.
    pub fn module_proving_good(&mut self, module: &ModuleDescriptor) -> bool {
        assert_eq!(&self.module(), module);
        let answer = self.current_module_good;
        self.current_module = None;
        self.current_module_good = true;
        answer
    }

    /// Called when a single proof search completes.
    /// Statistics are tracked here.
    /// env should be the environment that the proof happened in.
    pub fn search_finished(
        &mut self,
        goal: &Goal,
        outcome: Outcome,
        elapsed: Duration,
        eval_skip: Option<usize>,
    ) {
        // Time conversion
        let secs = elapsed.as_secs() as f64;
        let subsec_nanos = elapsed.subsec_nanos() as f64;
        let elapsed_f64 = secs + subsec_nanos * 1e-9;
        let elapsed_str = format!("{:.3}s", elapsed_f64);

        // Tracking statistics
        let counts_goal_progress = !self.eval_mode || eval_skip == Some(0);
        if counts_goal_progress {
            self.metrics.goals_done += 1;
        }
        self.metrics.searches_total += 1;
        self.metrics.search_time += elapsed_f64;
        if let Some(skip) = eval_skip {
            self.metrics
                .record_eval_skip_search(skip, outcome, elapsed_f64);
        }
        let skip_phrase = match eval_skip {
            Some(skip) if self.eval_mode => format!(" with skip={}", skip),
            _ => String::new(),
        };

        match outcome {
            Outcome::Success => {
                // The search was a success.
                if counts_goal_progress {
                    self.metrics.goals_success += 1;
                }
                self.metrics.searches_success += 1;
                if self.log_when_slow && elapsed_f64 > 0.1 {
                    self.log_info(&goal, &format!("took {}", elapsed_str));
                }
                if counts_goal_progress {
                    self.log_verified(goal.first_line, goal.last_line);
                }
            }
            Outcome::ShallowExhausted => {
                self.metrics.searches_shallow_exhausted += 1;
                self.log_warning(
                    &goal,
                    &format!(
                        "could not be {}{} (shallow exhaustion)",
                        self.operation_verb, skip_phrase
                    ),
                )
            }
            Outcome::ShallowExplosion => {
                self.metrics.searches_shallow_explosion += 1;
                self.log_warning(
                    &goal,
                    &format!(
                        "could not be {}{} (shallow explosion)",
                        self.operation_verb, skip_phrase
                    ),
                )
            }
            Outcome::Exhausted => {
                self.metrics.searches_exhausted += 1;
                self.log_warning(
                    &goal,
                    &format!(
                        "could not be {}{} (exhaustion)",
                        self.operation_verb, skip_phrase
                    ),
                )
            }
            Outcome::Inconsistent => {
                self.metrics.searches_inconsistent += 1;
                self.log_warning(
                    &goal,
                    &format!("prover found inconsistent assumptions{}", skip_phrase),
                )
            }
            Outcome::Timeout => {
                self.metrics.searches_timeout += 1;
                self.log_warning(
                    &goal,
                    &format!(
                        "could not be {}{} (timeout after {})",
                        self.operation_verb, skip_phrase, elapsed_str
                    ),
                )
            }
            Outcome::Interrupted => {
                self.metrics.searches_interrupted += 1;
                // Should this really be an error?
                let error = BuildError::goal(&goal, "was interrupted");
                self.log_build_error(&error);
            }
            Outcome::ActivationCap => {
                self.metrics.searches_activation_cap += 1;
                self.log_warning(
                    &goal,
                    &format!(
                        "could not be {}{} (hit activation cap)",
                        self.operation_verb, skip_phrase
                    ),
                )
            }
        }
    }

    /// Logs a successful verification.
    /// This can either be a proof, or something that doesn't require proving.
    pub fn log_verified(&mut self, first_line: u32, last_line: u32) {
        let event = BuildEvent {
            progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
            verified: Some((first_line, last_line)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    /// Logs a cache hit for this node and every child of it.
    /// Returns the cursor to its initial state when done.
    pub fn log_proving_cache_hit(&mut self, cursor: &mut NodeCursor) {
        if cursor.num_children() > 0 {
            cursor.descend(0);
            loop {
                self.log_proving_cache_hit(cursor);
                if cursor.has_next() {
                    cursor.next();
                } else {
                    break;
                }
            }
            cursor.ascend();
        }
        if cursor.node().has_goal() {
            let goal = cursor.goal().unwrap();
            self.metrics.goals_done += 1;
            self.metrics.goals_success += 1;
            self.log_verified(goal.first_line, goal.last_line);
        }
    }

    /// Create a build event for something that is localized.
    /// Short message goes into the diagnostic, long message goes into the log.
    /// If sev is None, there message only appears in the logs, not in visible UI.
    fn make_event(
        &mut self,
        range: Range,
        short_message: &str,
        sev: Option<DiagnosticSeverity>,
    ) -> BuildEvent {
        let display_path = self.project().display_path(&self.module());
        let line = range.start.line + 1;
        let long_message = format!("{}, line {}: {}", display_path, line, short_message);
        let diagnostic = sev.map(|severity| Diagnostic {
            range,
            severity: Some(severity),
            message: short_message.to_string(),
            ..Diagnostic::default()
        });
        BuildEvent {
            progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
            log_message: Some(long_message),
            diagnostic,
            ..self.default_event()
        }
    }

    /// Note that this will blue-squiggle in VS Code, so don't just use this willy-nilly.
    fn log_info(&mut self, goal: &Goal, message: &str) {
        let full_message = format!("{} {}", goal.name, message);
        let event = self.make_event(
            goal.proposition.source.range,
            &full_message,
            Some(DiagnosticSeverity::INFORMATION),
        );
        (self.event_handler)(event);
    }

    /// Logs a warning that is associated with a particular goal.
    /// This will cause a yellow squiggle in VS Code.
    /// This will mark the build as "not good", so we won't cache it.
    fn log_warning(&mut self, goal: &Goal, message: &str) {
        let full_message = format!("{} {}", goal.name, message);
        let event = self.make_event(
            goal.proposition.source.range,
            &full_message,
            Some(DiagnosticSeverity::WARNING),
        );
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status.warn();
    }

    /// Logs an error that is associated with a particular goal.
    /// This will cause a red squiggle in VS Code.
    /// This will halt the build.
    fn log_build_error(&mut self, build_error: &BuildError) {
        let mut event = self.make_event(
            build_error.range,
            &build_error.message,
            Some(DiagnosticSeverity::ERROR),
        );

        // Set progress as complete, because an error will halt the build
        event.progress = Some((self.metrics.goals_total, self.metrics.goals_total));
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status = BuildStatus::Error;
    }

    /// Sets the builder to only build a single goal.
    /// Takes a target module name and an external line number (1-based).
    /// Does not check that there is a goal at this line.
    /// Requires that the target module is already loaded.
    pub fn set_single_goal(
        &mut self,
        target: &str,
        external_line_number: u32,
    ) -> Result<(), String> {
        self.set_single_goal_with_index(target, external_line_number, None)
    }

    /// Sets the builder to only build a single goal at a single line, optionally selecting a
    /// 1-based goal index among all goals that start on that line.
    pub fn set_single_goal_with_index(
        &mut self,
        target: &str,
        external_line_number: u32,
        goal_index: Option<usize>,
    ) -> Result<(), String> {
        // Convert from 1-based (external) to 0-based (internal) line number
        let internal_line_number = external_line_number - 1;

        let module_descriptor = self.target_descriptor(target)?;

        self.goal_filter = Some(GoalFilter::SingleLine {
            module: module_descriptor,
            line: internal_line_number,
            goal_index,
        });
        self.single_line_goal_count = 0;
        Ok(())
    }

    /// Sets the builder to only build goals within a line range.
    /// Takes a target module name and external line numbers (1-based), inclusive.
    /// Verifies goals whose first_line falls within [start, end].
    /// Requires that the target module is already loaded.
    pub fn set_goal_range(
        &mut self,
        target: &str,
        external_start: u32,
        external_end: u32,
    ) -> Result<(), String> {
        // Convert from 1-based (external) to 0-based (internal) line numbers
        let internal_start = external_start - 1;
        let internal_end = external_end - 1;

        let module_descriptor = self.target_descriptor(target)?;

        self.goal_filter = Some(GoalFilter::LineRange {
            module: module_descriptor,
            start: internal_start,
            end: internal_end,
        });
        self.single_line_goal_count = 0;
        Ok(())
    }

    fn target_descriptor(&self, target: &str) -> Result<ModuleDescriptor, String> {
        if target.ends_with(".ac") {
            return self
                .project()
                .descriptor_from_path(Path::new(target))
                .map_err(|e| format!("Module '{}' not found: {}", target, e));
        }

        let module_id = self
            .project()
            .get_module_id_by_name(target)
            .ok_or_else(|| format!("Module '{}' not found", target))?;

        self.project()
            .get_module_descriptor(module_id)
            .cloned()
            .ok_or_else(|| format!("No descriptor found for module '{}'", target))
    }

    pub fn validate_goal_filter(&self) -> Result<(), String> {
        if let Some(GoalFilter::SingleLine {
            line,
            goal_index: Some(goal_index),
            ..
        }) = &self.goal_filter
        {
            if self.single_line_goal_count < *goal_index {
                return Err(format!(
                    "goal {} is out of range for selected line {} (found {} goal{})",
                    goal_index,
                    line + 1,
                    self.single_line_goal_count,
                    if self.single_line_goal_count == 1 {
                        ""
                    } else {
                        "s"
                    }
                ));
            }
        }
        Ok(())
    }

    /// Verifies a goal.
    /// env should be the environment that the proof happens in.
    /// lowered_goal is the lowered goal from the lowering pass, used for validation.
    fn verify_goal(
        &mut self,
        mut processor: Rc<Processor>,
        goal: &Goal,
        bindings: &crate::elaborator::binding_map::BindingMap,
        new_certs: &mut Vec<Certificate>,
        worklist: &mut CertificateWorklist,
        lowered_goal: Option<&LoweredGoal>,
        eval_skip: Option<usize>,
    ) -> Result<(), BuildError> {
        // Check if we've been cancelled before starting any work
        if self.cancellation_token.is_cancelled() {
            return Err(BuildError::goal(goal, "was interrupted"));
        }

        // If there's a cert override for single-goal verification, use it instead of the worklist
        if let Some(ref cert) = self.cert_override {
            let normalized_goal =
                lowered_goal.ok_or_else(|| BuildError::goal(goal, "missing lowered goal"))?;
            let goal_kernel_context = &normalized_goal.kernel_context;
            let check_start = std::time::Instant::now();
            let result = processor.check_cert(
                cert,
                Some(normalized_goal),
                goal_kernel_context,
                self.project(),
                bindings,
            );
            let check_elapsed = check_start.elapsed();
            let check_succeeded = result.is_ok();
            self.record_cert_check(check_elapsed, check_succeeded);
            match result {
                Ok(_steps) => {
                    self.metrics.goals_done += 1;
                    self.metrics.goals_success += 1;
                    self.log_verified(goal.first_line, goal.last_line);
                    return Ok(());
                }
                Err(e) => {
                    return Err(BuildError::goal(
                        goal,
                        format!("certificate override failed to verify: {}", e),
                    ));
                }
            }
        }

        if !self.print_found_proof && !self.force_search {
            // Check for a cached cert
            let indexes = worklist.get_indexes(&goal.name);
            for i in indexes {
                let cert = worklist.get_cert(*i).unwrap().clone();

                let normalized_goal =
                    lowered_goal.ok_or_else(|| BuildError::goal(goal, "missing lowered goal"))?;
                let goal_kernel_context = &normalized_goal.kernel_context;
                let check_start = std::time::Instant::now();
                let result = processor.check_cert_with_usage(
                    &cert,
                    Some(normalized_goal),
                    goal_kernel_context,
                    self.project(),
                    bindings,
                );
                let check_elapsed = check_start.elapsed();
                let check_succeeded = result.is_ok();
                self.record_cert_check(check_elapsed, check_succeeded);
                let (cert_to_use, check_result) = match result {
                    Ok(checked_cert) => (
                        cert.trim_to_consumed_prefix(checked_cert.consumed_proof_steps),
                        Ok(checked_cert.lines),
                    ),
                    Err(e) => (cert, Err(e)),
                };

                match check_result {
                    Ok(_steps) => {
                        self.metrics.certs_cached += 1;
                        self.metrics.goals_done += 1;
                        self.metrics.goals_success += 1;
                        self.log_verified(goal.first_line, goal.last_line);
                        new_certs.push(cert_to_use.clone());
                        worklist.remove(&goal.name, *i);

                        return Ok(());
                    }
                    Err(e) if self.check_mode => {
                        // In check mode, a bad cert is an error
                        if false {
                            // Print a command to reproduce this failure
                            let module_name = self
                                .current_module
                                .as_ref()
                                .map(|m| m.to_string())
                                .unwrap_or_else(|| "unknown".to_string());
                            let external_line = goal.first_line + 1;
                            let cert_json = serde_json::to_string(&cert_to_use).unwrap_or_default();
                            self.log_global(format!(
                                "To reproduce: acorn check {} --line {} --cert '{}'",
                                module_name, external_line, cert_json
                            ));
                        }
                        return Err(BuildError::goal(
                            goal,
                            format!("certificate failed to verify: {}", e),
                        ));
                    }
                    Err(_) => {
                        // The cert is bad, but maybe another one is good.
                        // That can happen with code edits.
                    }
                }
            }
        }

        // In check mode, we should never reach the search phase
        if self.check_mode {
            return Err(BuildError::goal(goal, "no certificate found"));
        }

        // Try searching
        let processor = Rc::make_mut(&mut processor);

        // Use lowered goal data only; do not lower during phase three.
        let normalized_goal =
            lowered_goal.ok_or_else(|| BuildError::goal(goal, "missing lowered goal"))?;
        let goal_kernel_context = &normalized_goal.kernel_context;
        processor.set_lowered_goal(normalized_goal);

        let start = std::time::Instant::now();
        let mode = if self.shallow_search {
            ProverMode::Shallow {
                timeout_secs: self.timeout_secs,
                activation_limit: self.activation_limit,
            }
        } else {
            ProverMode::Interactive {
                timeout_secs: self.timeout_secs,
                activation_limit: self.activation_limit,
            }
        };
        let outcome = processor.search(mode, goal_kernel_context);
        if self.eval_mode {
            if let Some(stats) = processor.last_search_stats() {
                self.metrics.record_eval_search_instrumentation(stats);
            }
        }
        if self.verbose {
            processor
                .prover()
                .print_active_steps(outcome, bindings, goal_kernel_context);
        }
        if outcome == Outcome::Success {
            let cert_result = catch_unwind(AssertUnwindSafe(|| {
                processor.make_cert(bindings, goal_kernel_context, self.print_found_proof)
            }));
            match cert_result {
                Err(payload) => {
                    let module_name = self
                        .current_module
                        .as_ref()
                        .map(|m| m.to_string())
                        .unwrap_or_else(|| "unknown".to_string());
                    let external_line = goal.first_line + 1;
                    return Err(BuildError::goal(
                        goal,
                        format_goal_panic_message(
                            &panic_payload_to_string(payload),
                            &module_name,
                            external_line,
                        ),
                    ));
                }
                Ok(result) => match result {
                    Ok(cert) => {
                        let mut checked_cert_lines = None;
                        #[cfg(feature = "validate")]
                        {
                            // Validate the cert immediately after generation.
                            match processor.check_generated_cert(
                                &cert,
                                Some(normalized_goal),
                                goal_kernel_context,
                                self.project(),
                                bindings,
                            ) {
                                Ok(lines) => {
                                    if self.print_proof {
                                        checked_cert_lines = Some(lines);
                                    }
                                }
                                Err(e) => {
                                    let module_name = self
                                        .current_module
                                        .as_ref()
                                        .map(|m| m.to_string())
                                        .unwrap_or_else(|| "unknown".to_string());
                                    let external_line = goal.first_line + 1;
                                    let compact_error = compact_check_cert_error(&e.to_string());
                                    panic!(
                                        "newly generated cert should be checkable for goal '{}' at {}:{}: {}\n\
                                         Repro command: acorn verify {} --line {} --force-search",
                                        goal.name,
                                        module_name,
                                        external_line,
                                        compact_error,
                                        module_name,
                                        external_line
                                    );
                                }
                            }
                        }
                        #[cfg(not(feature = "validate"))]
                        if self.print_proof {
                            // Since we aren't performance-sensitive, check the cert.
                            match processor.check_cert(
                                &cert,
                                Some(normalized_goal),
                                goal_kernel_context,
                                self.project(),
                                bindings,
                            ) {
                                Ok(lines) => checked_cert_lines = Some(lines),
                                Err(e) => {
                                    let module_name = self
                                        .current_module
                                        .as_ref()
                                        .map(|m| m.to_string())
                                        .unwrap_or_else(|| "unknown".to_string());
                                    let external_line = goal.first_line + 1;
                                    let compact_error = compact_check_cert_error(&e.to_string());
                                    panic!(
                                        "newly generated cert should be checkable for goal '{}' at {}:{}: {}\n\
                                         Repro command: acorn verify {} --line {} --force-search",
                                        goal.name,
                                        module_name,
                                        external_line,
                                        compact_error,
                                        module_name,
                                        external_line
                                    );
                                }
                            }
                        }
                        if let Some(lines) = checked_cert_lines.as_ref() {
                            let display_bindings = Processor::bindings_with_type_params(
                                bindings,
                                &goal.proposition.params,
                            );
                            print_displayed_proof(display_bindings.as_ref(), lines);
                        }
                        new_certs.push(cert);
                        self.metrics.certs_created += 1;
                    }
                    Err(e) => {
                        #[cfg(feature = "validate")]
                        {
                            let module_name = self
                                .current_module
                                .as_ref()
                                .map(|m| m.to_string())
                                .unwrap_or_else(|| "unknown".to_string());
                            let external_line = goal.first_line + 1;
                            panic!(
                                "full prover should create a certificate for goal '{}' at {}:{}: {}\n\
                                 Repro command: acorn verify {} --line {} --force-search",
                                goal.name, module_name, external_line, e, module_name, external_line
                            );
                        }

                        #[cfg(not(feature = "validate"))]
                        return Err(BuildError::goal(
                            goal,
                            format!("full prover failed to create certificate: {}", e),
                        ));
                    }
                },
            }
        }
        self.search_finished(goal, outcome, start.elapsed(), eval_skip);
        Ok(())
    }

    fn eval_max_skip(&self) -> usize {
        if !self.eval_mode {
            return 0;
        }
        self.eval_skip_modes.iter().copied().max().unwrap_or(0)
    }

    fn processor_with_imports(
        &self,
        mut processor: Rc<Processor>,
        bindings: &crate::elaborator::binding_map::BindingMap,
    ) -> Result<Rc<Processor>, BuildError> {
        if !processor.has_imports_for_bindings(bindings) {
            Rc::make_mut(&mut processor).add_imports_from_bindings(bindings, self.project())?;
        }
        Ok(processor)
    }

    fn verify_eval_goal(
        &mut self,
        processor: Rc<Processor>,
        goal: &Goal,
        bindings: &crate::elaborator::binding_map::BindingMap,
        new_certs: &mut Vec<Certificate>,
        worklist: &mut CertificateWorklist,
        lowered_goal: Option<&LoweredGoal>,
        eval_skip_tail: &EvalSkipTail<Rc<Processor>>,
        eval_proof_kind: EvalProofKind,
    ) -> Result<(), BuildError> {
        let skip_modes = self.eval_skip_modes.clone();
        for skip in skip_modes {
            if skip == 0 && eval_proof_kind == EvalProofKind::Empty {
                continue;
            }
            let search_processor = if skip == 0 {
                Rc::clone(&processor)
            } else {
                match eval_skip_tail.checkpoint_for(skip) {
                    Some(checkpoint) => checkpoint,
                    None => {
                        self.metrics.record_eval_skip_ineligible(skip);
                        continue;
                    }
                }
            };
            let search_processor = self.processor_with_imports(search_processor, bindings)?;
            self.verify_goal(
                search_processor,
                goal,
                bindings,
                new_certs,
                worklist,
                lowered_goal,
                Some(skip),
            )?;
            if self.exit_on_warning && !self.status.is_good() {
                break;
            }
        }
        Ok(())
    }

    fn is_plain_anonymous_lowered_goal(goal: &Goal) -> bool {
        matches!(goal.proposition.source.source_type, SourceType::Anonymous)
    }

    fn update_eval_skip_tail_for_lowered_goal(
        &self,
        tail: &mut EvalSkipTail<Rc<Processor>>,
        goal: &Goal,
        checkpoint_before_node: Rc<Processor>,
    ) {
        if !self.eval_mode || self.eval_max_skip() == 0 {
            return;
        }
        if Self::is_plain_anonymous_lowered_goal(goal) {
            tail.record_plain(checkpoint_before_node);
        } else {
            tail.record_barrier();
        }
    }

    fn record_lowered_barrier(&self, tail: &mut EvalSkipTail<Rc<Processor>>) {
        if self.eval_mode && self.eval_max_skip() > 0 {
            tail.record_barrier();
        }
    }

    fn verify_lowered_claim(
        &mut self,
        processor: Rc<Processor>,
        lowered: &LoweredModule,
        item: &LoweredItem,
        new_certs: &mut Vec<Certificate>,
        worklist: &mut CertificateWorklist,
        eval_goal_counts: &mut Option<HashMap<String, EvalGoalCounts>>,
        eval_skip_tail: &EvalSkipTail<Rc<Processor>>,
    ) -> Result<(), BuildError> {
        let LoweredItem::Claim { goal, .. } = item else {
            return Ok(());
        };
        let entry = lowered.goal(*goal);
        let normalized_goal = &entry.lowered_goal;
        let goal = &normalized_goal.goal;
        if let Some(ref filter) = self.goal_filter {
            let matches = match filter {
                GoalFilter::SingleLine {
                    line, goal_index, ..
                } => {
                    if goal.first_line != *line {
                        false
                    } else {
                        self.single_line_goal_count += 1;
                        match goal_index {
                            Some(index) => self.single_line_goal_count == *index,
                            None => true,
                        }
                    }
                }
                GoalFilter::LineRange { start, end, .. } => {
                    goal.first_line >= *start && goal.first_line <= *end
                }
            };
            if !matches {
                return Ok(());
            }
        }
        let eval_proof_kind = if let Some(counts) = eval_goal_counts.as_mut() {
            let Some(counts) = counts.get_mut(&goal.name) else {
                self.metrics.eval_goals_skipped_uncertified += 1;
                return Ok(());
            };
            match counts.take() {
                Some(kind) => {
                    self.metrics.eval_corpus_matched += 1;
                    Some(kind)
                }
                None => {
                    self.metrics.eval_goals_skipped_uncertified += 1;
                    return Ok(());
                }
            }
        } else {
            None
        };

        let processor = self.processor_with_imports(processor, &entry.bindings)?;
        if self.eval_mode {
            self.verify_eval_goal(
                processor,
                goal,
                &entry.bindings,
                new_certs,
                worklist,
                Some(normalized_goal),
                eval_skip_tail,
                eval_proof_kind.expect("eval mode has proof kind"),
            )?;
        } else {
            self.verify_goal(
                processor,
                goal,
                &entry.bindings,
                new_certs,
                worklist,
                Some(normalized_goal),
                None,
            )?;
        }
        Ok(())
    }

    fn verify_lowered_items(
        &mut self,
        processor: &mut Rc<Processor>,
        lowered: &LoweredModule,
        items: &[LoweredItem],
        top_level: bool,
        new_certs: &mut Vec<Certificate>,
        worklist: &mut CertificateWorklist,
        eval_goal_counts: &mut Option<HashMap<String, EvalGoalCounts>>,
        eval_skip_tail: &mut EvalSkipTail<Rc<Processor>>,
    ) -> Result<(), BuildError> {
        for item in items {
            match item {
                LoweredItem::Fact {
                    fact,
                    first_line,
                    last_line,
                } => {
                    if top_level {
                        self.log_verified(*first_line, *last_line);
                    }
                    Rc::make_mut(processor).add_lowered_fact(lowered.fact(*fact))?;
                    self.record_lowered_barrier(eval_skip_tail);
                }
                LoweredItem::Claim { post_fact, .. } => {
                    let LoweredItem::Claim { goal, .. } = item else {
                        unreachable!();
                    };
                    let entry = lowered.goal(*goal);
                    *processor =
                        self.processor_with_imports(Rc::clone(processor), &entry.bindings)?;
                    let checkpoint_before_node = if self.eval_mode && self.eval_max_skip() > 0 {
                        Some(Rc::clone(processor))
                    } else {
                        None
                    };
                    self.verify_lowered_claim(
                        Rc::clone(processor),
                        lowered,
                        item,
                        new_certs,
                        worklist,
                        eval_goal_counts,
                        eval_skip_tail,
                    )?;
                    Rc::make_mut(processor).add_lowered_fact(lowered.fact(*post_fact))?;
                    if let Some(checkpoint_before_node) = checkpoint_before_node {
                        let goal = &lowered.goal(*goal).lowered_goal.goal;
                        self.update_eval_skip_tail_for_lowered_goal(
                            eval_skip_tail,
                            goal,
                            checkpoint_before_node,
                        );
                    }
                }
                LoweredItem::Block {
                    items,
                    external_fact,
                    first_line,
                    last_line,
                } => {
                    if items.is_empty() && top_level {
                        self.log_verified(*first_line, *last_line);
                    } else {
                        let mut child_processor = Rc::clone(processor);
                        let mut child_eval_skip_tail = EvalSkipTail::new(self.eval_max_skip());
                        self.verify_lowered_items(
                            &mut child_processor,
                            lowered,
                            items,
                            false,
                            new_certs,
                            worklist,
                            eval_goal_counts,
                            &mut child_eval_skip_tail,
                        )?;
                    }
                    if let Some(fact) = external_fact {
                        Rc::make_mut(processor).add_lowered_fact(lowered.fact(*fact))?;
                    }
                    self.record_lowered_barrier(eval_skip_tail);
                }
            }

            if self.exit_on_warning && !self.status.is_good() {
                break;
            }
        }
        Ok(())
    }

    pub fn verify_lowered_module(
        &mut self,
        target: &ModuleDescriptor,
        lowered: &LoweredModule,
    ) -> Result<(), BuildError> {
        if self.strict {
            for range in &lowered.top_level_axiom_ranges {
                let event = self.make_event(
                    *range,
                    "axiom keyword is not allowed in strict mode",
                    Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR),
                );
                (self.event_handler)(event);
                self.status = BuildStatus::Error;
                return Err(BuildError::new(
                    *range,
                    "axiom keyword is not allowed in strict mode",
                ));
            }
        }

        let mut worklist = if self.project().config().read_cache {
            self.project().build_cache().make_worklist(target)
        } else {
            CertificateWorklist::new(CertificateStore { certs: vec![] })
        };
        let mut eval_goal_counts = self.eval_goal_counts(target);
        if let Some(counts) = &eval_goal_counts {
            self.metrics.eval_corpus_total +=
                counts.values().map(EvalGoalCounts::total).sum::<usize>() as i32;
            self.metrics.eval_corpus_empty +=
                counts.values().map(|counts| counts.empty).sum::<usize>() as i32;
        }
        let mut new_certs = vec![];

        if self.project().is_surface_check_target(target) {
            return Ok(());
        }

        if !lowered.is_empty() {
            self.module_proving_started(target.clone());
            let processor = if self.check_mode {
                Processor::with_imports_for_checking(
                    Some(self.cancellation_token.clone()),
                    &lowered.initial_bindings,
                    self.project(),
                )?
            } else {
                Processor::with_imports(
                    Some(self.cancellation_token.clone()),
                    &lowered.initial_bindings,
                    self.project(),
                )?
            };
            let mut processor = Rc::new(processor);
            let mut eval_skip_tail = EvalSkipTail::new(self.eval_max_skip());
            self.verify_lowered_items(
                &mut processor,
                lowered,
                &lowered.items,
                true,
                &mut new_certs,
                &mut worklist,
                &mut eval_goal_counts,
                &mut eval_skip_tail,
            )?;
        }

        if let Some(counts) = &eval_goal_counts {
            self.metrics.eval_corpus_unmatched +=
                counts.values().map(EvalGoalCounts::total).sum::<usize>() as i32;
        }

        let module_good = if lowered.is_empty() {
            true
        } else {
            self.module_proving_good(target)
        };

        if self.goal_filter.is_some() {
            return Ok(());
        }

        self.metrics.certs_unused += worklist.unused() as i32;

        let used_cert_count = new_certs.len();
        let mut cert_store = CertificateStore { certs: new_certs };
        cert_store.append(&worklist);
        self.used_cert_counts
            .insert(target.clone(), used_cert_count);

        let content_hash = if module_good {
            self.project().get_module_content_hash(lowered.module_id)
        } else {
            None
        };

        self.build_cache
            .as_mut()
            .unwrap()
            .insert(target.clone(), cert_store, content_hash);

        Ok(())
    }

    fn can_build_modules_in_parallel(&self, target_count: usize) -> bool {
        let config = self.project().config();
        let can_parallelize_read_only_mode = self.check_mode || self.eval_mode;
        let can_parallelize_verify_mode = !self.check_mode && !self.eval_mode && !self.force_search;

        (can_parallelize_read_only_mode || can_parallelize_verify_mode)
            && self.check_jobs > 1
            && target_count > 1
            && self.goal_filter.is_none()
            && self.cert_override.is_none()
            && !self.print_proof
            && !self.print_found_proof
            && !self.exit_on_warning
            && config.read_cache
            && (can_parallelize_verify_mode || !config.write_cache)
    }

    fn eval_module_search_estimate(&self, target: &ModuleDescriptor) -> usize {
        let has_skip_zero = self.eval_skip_modes.contains(&0);
        let nonzero_skip_count = self
            .eval_skip_modes
            .iter()
            .filter(|&&skip| skip > 0)
            .count();

        let Some(store) = self.project().build_cache().get_certificates(target) else {
            return 0;
        };
        store
            .certs
            .iter()
            .map(|cert| match &cert.proof {
                Some(proof) if proof.is_empty() => nonzero_skip_count,
                Some(_) => nonzero_skip_count + usize::from(has_skip_zero),
                None => 0,
            })
            .sum()
    }

    fn module_work_estimate(&self, target: &ModuleDescriptor, lowered: &LoweredModule) -> usize {
        if self.eval_mode {
            self.eval_module_search_estimate(target)
        } else if self.check_mode {
            self.check_module_work_estimate(lowered)
        } else {
            lowered.goal_count()
        }
    }

    fn check_module_work_estimate(&self, lowered: &LoweredModule) -> usize {
        let mut imported_modules = HashSet::new();
        for dep_id in lowered.initial_bindings.direct_dependencies() {
            for module_id in self
                .project()
                .all_dependencies(dep_id)
                .into_iter()
                .chain(std::iter::once(dep_id))
            {
                imported_modules.insert(module_id);
            }
        }
        let imported_facts = imported_modules
            .into_iter()
            .filter_map(|module_id| self.project().get_module_export(module_id))
            .map(|export| export.fact_count())
            .sum::<usize>();
        let local_fact_steps = lowered.facts().map(|fact| fact.steps.len()).sum::<usize>();
        let local_goal_steps = lowered
            .goals()
            .map(|(_, goal)| goal.lowered_goal.steps.len())
            .sum::<usize>();
        lowered.goal_count() + imported_facts + local_fact_steps + local_goal_steps
    }

    fn build_module_on_worker(
        project: ProjectView,
        cancellation_token: CancellationToken,
        index: usize,
        target: ModuleDescriptor,
        lowered: &LoweredModule,
        config: &ModuleWorkerConfig,
    ) -> ModuleBuildResult {
        let mut events = Vec::new();
        let build_dir = project.build_dir().clone();
        let mut builder =
            Builder::new_with_view(project, cancellation_token, |event| events.push(event));
        config.apply_to(&mut builder);
        builder.metrics.modules_total = 1;
        let goal_count = lowered.goal_count() as i32;
        builder.metrics.goals_total = goal_count;
        builder.build_cache = Some(BuildCache::new(build_dir));
        builder.prepare_eval_mode();

        let skip_metrics_before = builder.metrics.clone();
        let skip_start = std::time::Instant::now();
        if builder.try_skip_unchanged_module(lowered.module_id, &target) {
            builder.metrics.goals_done += goal_count;
            builder.metrics.goals_success += goal_count;
            builder.metrics.certs_cached += goal_count;
            builder.metrics.modules_cached += 1;
            builder.record_module_timing(
                target.clone(),
                goal_count,
                &skip_metrics_before,
                skip_start.elapsed(),
                true,
            );

            let event = BuildEvent {
                progress: Some((builder.metrics.goals_done, builder.metrics.goals_total)),
                ..builder.default_event()
            };
            (builder.event_handler)(event);
        } else {
            if builder.goal_filter.is_none()
                && !builder.project().config().read_cache
                && !builder.check_mode
            {
                builder.log_global(format!("force-searching: {}", target));
            }

            let module_metrics_before = builder.metrics.clone();
            let module_start = std::time::Instant::now();
            let result = builder.verify_lowered_module(&target, lowered);
            builder.record_module_timing(
                target.clone(),
                goal_count,
                &module_metrics_before,
                module_start.elapsed(),
                false,
            );
            if let Err(e) = result {
                builder.log_build_error(&e);
            }
        }

        let status = builder.status;
        let metrics = builder.metrics.clone();
        let module_timings = builder.module_timings.clone();
        let used_cert_counts = std::mem::take(&mut builder.used_cert_counts);
        let build_cache = builder.take_build_cache();
        drop(builder);

        ModuleBuildResult {
            index,
            status,
            metrics,
            module_timings,
            build_cache,
            used_cert_counts,
            events,
        }
    }

    fn build_modules_parallel(&mut self, modules: Vec<(usize, ModuleDescriptor, &LoweredModule)>) {
        let worker_count = self.check_jobs.min(modules.len()).max(1);
        let mut modules = modules
            .into_iter()
            .map(|(index, target, lowered)| ScheduledModule {
                work_estimate: self.module_work_estimate(&target, lowered),
                index,
                target,
                lowered,
            })
            .collect::<Vec<_>>();
        modules.sort_by(|a, b| {
            b.work_estimate
                .cmp(&a.work_estimate)
                .then_with(|| a.index.cmp(&b.index))
        });

        let project = self.project().clone();
        let worker_config = ModuleWorkerConfig::from_builder(self);
        let cancellation_token = self.cancellation_token.clone();
        let next_module = AtomicUsize::new(0);
        let mut results = Vec::new();

        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..worker_count {
                let token = cancellation_token.clone();
                let config = worker_config.clone();
                let modules = &modules;
                let next_module = &next_module;
                let project = project.clone();
                handles.push(scope.spawn(move || {
                    let mut worker_results = Vec::new();
                    loop {
                        let module_index = next_module.fetch_add(1, Ordering::Relaxed);
                        let Some(module) = modules.get(module_index) else {
                            break;
                        };
                        worker_results.push(Self::build_module_on_worker(
                            project.clone(),
                            token.clone(),
                            module.index,
                            module.target.clone(),
                            module.lowered,
                            &config,
                        ));
                    }
                    worker_results
                }));
            }

            for handle in handles {
                match handle.join() {
                    Ok(mut worker_results) => results.append(&mut worker_results),
                    Err(payload) => std::panic::resume_unwind(payload),
                }
            }
        });

        results.sort_by_key(|result| result.index);

        for result in results {
            self.metrics.add_module_result(&result.metrics);
            self.module_timings.extend(result.module_timings);
            match result.status {
                BuildStatus::Error => self.status = BuildStatus::Error,
                BuildStatus::Warning if self.status.is_good() => self.status = BuildStatus::Warning,
                BuildStatus::Good | BuildStatus::Warning => {}
            }

            for mut event in result.events {
                event.build_id = self.id;
                if event.progress.is_some() {
                    event.progress = Some((self.metrics.goals_done, self.metrics.goals_total));
                }
                (self.event_handler)(event);
            }
        }
    }

    fn build_owned_modules_parallel(
        &mut self,
        modules: Vec<(usize, ModuleDescriptor, LoweredModule)>,
    ) {
        let worker_count = self.check_jobs.min(modules.len()).max(1);
        let mut modules = modules
            .into_iter()
            .map(|(index, target, lowered)| OwnedScheduledModule {
                work_estimate: self.module_work_estimate(&target, &lowered),
                index,
                target,
                lowered,
            })
            .collect::<Vec<_>>();
        modules.sort_by(|a, b| {
            b.work_estimate
                .cmp(&a.work_estimate)
                .then_with(|| a.index.cmp(&b.index))
        });

        let work_queue = Mutex::new(VecDeque::from(modules));
        let project = self.project().clone();
        let worker_config = ModuleWorkerConfig::from_builder(self);
        let cancellation_token = self.cancellation_token.clone();
        let mut results = Vec::new();

        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for _ in 0..worker_count {
                let token = cancellation_token.clone();
                let config = worker_config.clone();
                let work_queue = &work_queue;
                let project = project.clone();
                handles.push(scope.spawn(move || {
                    let mut worker_results = Vec::new();
                    loop {
                        let module = {
                            let mut queue = work_queue.lock().expect("module work queue poisoned");
                            queue.pop_front()
                        };
                        let Some(module) = module else {
                            break;
                        };
                        worker_results.push(Self::build_module_on_worker(
                            project.clone(),
                            token.clone(),
                            module.index,
                            module.target,
                            &module.lowered,
                            &config,
                        ));
                    }
                    worker_results
                }));
            }

            for handle in handles {
                match handle.join() {
                    Ok(mut worker_results) => results.append(&mut worker_results),
                    Err(payload) => std::panic::resume_unwind(payload),
                }
            }
        });

        results.sort_by_key(|result| result.index);

        for result in results {
            self.metrics.add_module_result(&result.metrics);
            self.module_timings.extend(result.module_timings);
            match result.status {
                BuildStatus::Error => self.status = BuildStatus::Error,
                BuildStatus::Warning if self.status.is_good() => self.status = BuildStatus::Warning,
                BuildStatus::Good | BuildStatus::Warning => {}
            }

            for mut event in result.events {
                event.build_id = self.id;
                if event.progress.is_some() {
                    event.progress = Some((self.metrics.goals_done, self.metrics.goals_total));
                }
                (self.event_handler)(event);
            }
        }
    }

    fn prepare_eval_mode(&mut self) {
        if !self.eval_mode {
            return;
        }
        self.force_search = true;
        self.check_hashes = false;
        self.metrics.eval_mode = true;
        if self.eval_skip_modes.is_empty() {
            self.eval_skip_modes.extend([0, 1]);
        }
        self.eval_skip_modes.sort_unstable();
        self.eval_skip_modes.dedup();
        for skip in self.eval_skip_modes.clone() {
            self.metrics.ensure_eval_skip_metrics(skip);
        }
    }

    fn build_owned_module_work(
        &mut self,
        targets: Vec<ModuleDescriptor>,
        module_work: Vec<(ModuleDescriptor, LoweredModule)>,
    ) {
        let loading_start = std::time::Instant::now();
        let mut work_by_target: HashMap<ModuleDescriptor, LoweredModule> =
            module_work.into_iter().collect();
        let mut lowered_modules = Vec::new();
        let project = self.project().clone();
        for target in &targets {
            let module = project.get_module(target);
            match module {
                ProjectViewModule::Ok(_) => {
                    if let Some(lowered) = work_by_target.remove(target) {
                        self.lowered_module_loaded(&lowered);
                        lowered_modules.push((target.clone(), lowered));
                    } else {
                        self.log_global(format!("error: module {} has no lowered work", target));
                    }
                }
                ProjectViewModule::Error(e) => {
                    if e.indirect {
                        if self.log_secondary_errors {
                            self.log_global(e.to_string());
                        }
                    } else {
                        self.log_loading_error(target, e);
                    }
                }
                ProjectViewModule::None => {
                    self.log_global(format!("error: module {} is not loaded", target));
                }
                ProjectViewModule::Loading | ProjectViewModule::Registered => {}
            }
        }
        self.metrics.loading_time = loading_start.elapsed().as_secs_f64();

        if self.status.is_error() {
            return;
        }

        self.loading_phase_complete();
        self.metrics.modules_total = lowered_modules.len() as i32;

        if self.can_build_modules_in_parallel(lowered_modules.len()) {
            let modules = lowered_modules
                .into_iter()
                .enumerate()
                .map(|(index, (target, lowered))| (index, target, lowered))
                .collect();
            let verification_start = std::time::Instant::now();
            self.build_owned_modules_parallel(modules);
            self.metrics.verification_time = verification_start.elapsed().as_secs_f64();
            return;
        }

        let verification_start = std::time::Instant::now();
        for (target, lowered) in lowered_modules {
            let goal_count = lowered.goal_count() as i32;

            if let Some(ref filter) = self.goal_filter {
                let filter_module = match filter {
                    GoalFilter::SingleLine { module, .. } => module,
                    GoalFilter::LineRange { module, .. } => module,
                };
                if filter_module != &target {
                    continue;
                }
            }

            let skip_metrics_before = self.metrics.clone();
            let skip_start = std::time::Instant::now();
            if self.try_skip_unchanged_module(lowered.module_id, &target) {
                self.metrics.goals_done += goal_count;
                self.metrics.goals_success += goal_count;
                self.metrics.certs_cached += goal_count;
                self.metrics.modules_cached += 1;
                self.record_module_timing(
                    target.clone(),
                    goal_count,
                    &skip_metrics_before,
                    skip_start.elapsed(),
                    true,
                );

                let event = BuildEvent {
                    progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
                    ..self.default_event()
                };
                (self.event_handler)(event);

                continue;
            }

            if self.goal_filter.is_none() && !self.project().config().read_cache && !self.check_mode
            {
                self.log_global(format!("force-searching: {}", target));
            }

            let module_metrics_before = self.metrics.clone();
            let module_start = std::time::Instant::now();
            if let Err(e) = self.verify_lowered_module(&target, &lowered) {
                self.record_module_timing(
                    target.clone(),
                    goal_count,
                    &module_metrics_before,
                    module_start.elapsed(),
                    false,
                );
                self.log_build_error(&e);
                self.metrics.verification_time = verification_start.elapsed().as_secs_f64();
                return;
            }
            self.record_module_timing(
                target.clone(),
                goal_count,
                &module_metrics_before,
                module_start.elapsed(),
                false,
            );

            if self.exit_on_warning && !self.status.is_good() {
                self.metrics.verification_time = verification_start.elapsed().as_secs_f64();
                return;
            }
        }
        self.metrics.verification_time = verification_start.elapsed().as_secs_f64();

        self.trim_unused_certificates();
    }

    fn process_one_owned_module(
        &mut self,
        _index: usize,
        target: ModuleDescriptor,
        lowered: LoweredModule,
    ) {
        let goal_count = lowered.goal_count() as i32;

        if let Some(ref filter) = self.goal_filter {
            let filter_module = match filter {
                GoalFilter::SingleLine { module, .. } => module,
                GoalFilter::LineRange { module, .. } => module,
            };
            if filter_module != &target {
                return;
            }
        }

        let skip_metrics_before = self.metrics.clone();
        let skip_start = std::time::Instant::now();
        if self.try_skip_unchanged_module(lowered.module_id, &target) {
            self.metrics.goals_done += goal_count;
            self.metrics.goals_success += goal_count;
            self.metrics.certs_cached += goal_count;
            self.metrics.modules_cached += 1;
            self.record_module_timing(
                target.clone(),
                goal_count,
                &skip_metrics_before,
                skip_start.elapsed(),
                true,
            );

            let event = BuildEvent {
                progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
                ..self.default_event()
            };
            (self.event_handler)(event);

            return;
        }

        if self.goal_filter.is_none() && !self.project().config().read_cache && !self.check_mode {
            self.log_global(format!("force-searching: {}", target));
        }

        let module_metrics_before = self.metrics.clone();
        let module_start = std::time::Instant::now();
        if let Err(e) = self.verify_lowered_module(&target, &lowered) {
            self.record_module_timing(
                target.clone(),
                goal_count,
                &module_metrics_before,
                module_start.elapsed(),
                false,
            );
            self.log_build_error(&e);
            return;
        }
        self.record_module_timing(
            target,
            goal_count,
            &module_metrics_before,
            module_start.elapsed(),
            false,
        );
    }

    fn trim_unused_certificates(&mut self) {
        if !self.status.is_good() {
            return;
        }
        if let Some(ref mut cache) = self.build_cache {
            for (descriptor, used_cert_count) in &self.used_cert_counts {
                if let Some(cert_store) = cache.get_certificates_mut(descriptor) {
                    cert_store.certs.truncate(*used_cert_count);
                }
            }
        }
    }

    /// Builds all open modules, logging build events.
    pub fn build(&mut self) {
        self.prepare_eval_mode();

        // Initialize the build cache
        self.build_cache = Some(BuildCache::new(self.project().build_dir().clone()));

        // Build in alphabetical order by module name for consistency.
        let mut targets = self.project().targets().iter().cloned().collect::<Vec<_>>();
        targets.sort();

        let verification_message = if targets.len() > 5 {
            format!("verifying {} modules...", targets.len())
        } else {
            format!(
                "verifying modules: {}",
                targets
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        self.log_global(verification_message);

        if let Some(module_work) = self.module_work.take() {
            self.build_owned_module_work(targets, module_work);
            return;
        }

        // The first phase is the "loading phase". We load modules and look for errors.
        // If there are errors, we won't try to do proving.
        let loading_start = std::time::Instant::now();
        let mut lowered_modules = vec![];
        let project = self.project().clone();
        for target in &targets {
            let module = project.get_module(target);
            match module {
                ProjectViewModule::Ok(_) => {
                    if let Some(lowered) = project.get_lowered_module(target) {
                        self.lowered_module_loaded(lowered);
                        lowered_modules.push(lowered);
                    } else {
                        self.log_global(format!("error: module {} has no lowered work", target));
                    }
                }
                ProjectViewModule::Error(e) => {
                    if e.indirect {
                        if self.log_secondary_errors {
                            // The real problem is in a different module.
                            // So we don't want to locate the error in this module.
                            self.log_global(e.to_string());
                        }
                    } else {
                        self.log_loading_error(target, e);
                    }
                }
                ProjectViewModule::None => {
                    // Targets are supposed to be loaded already.
                    self.log_global(format!("error: module {} is not loaded", target));
                }
                ProjectViewModule::Loading | ProjectViewModule::Registered => {}
            }
        }
        self.metrics.loading_time = loading_start.elapsed().as_secs_f64();

        if self.status.is_error() {
            return;
        }

        self.loading_phase_complete();

        // Track the total number of modules to build
        self.metrics.modules_total = lowered_modules.len() as i32;

        if self.can_build_modules_in_parallel(targets.len()) {
            let modules = targets
                .into_iter()
                .zip(lowered_modules)
                .enumerate()
                .map(|(index, (target, lowered))| (index, target.clone(), lowered))
                .collect();
            let verification_start = std::time::Instant::now();
            self.build_modules_parallel(modules);
            self.metrics.verification_time = verification_start.elapsed().as_secs_f64();
            return;
        }

        // The second pass is the "proving phase".
        let verification_start = std::time::Instant::now();
        for (target, lowered) in targets.iter().zip(lowered_modules) {
            let goal_count = lowered.goal_count() as i32;

            // Skip modules that don't match the goal filter
            if let Some(ref filter) = self.goal_filter {
                let filter_module = match filter {
                    GoalFilter::SingleLine { module, .. } => module,
                    GoalFilter::LineRange { module, .. } => module,
                };
                if filter_module != target {
                    continue;
                }
            }

            let skip_metrics_before = self.metrics.clone();
            let skip_start = std::time::Instant::now();
            if self.try_skip_unchanged_module(lowered.module_id, target) {
                // Update metrics to count the goals in this module as a success
                self.metrics.goals_done += goal_count;
                self.metrics.goals_success += goal_count;
                self.metrics.certs_cached += goal_count;
                self.metrics.modules_cached += 1;
                self.record_module_timing(
                    target.clone(),
                    goal_count,
                    &skip_metrics_before,
                    skip_start.elapsed(),
                    true,
                );

                let event = BuildEvent {
                    progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
                    ..self.default_event()
                };
                (self.event_handler)(event);

                continue;
            }

            // Log module name when forcing whole-project proof search.
            if self.goal_filter.is_none() && !self.project().config().read_cache && !self.check_mode
            {
                self.log_global(format!("force-searching: {}", target));
            }

            let module_metrics_before = self.metrics.clone();
            let module_start = std::time::Instant::now();
            if let Err(e) = self.verify_lowered_module(target, lowered) {
                self.record_module_timing(
                    target.clone(),
                    goal_count,
                    &module_metrics_before,
                    module_start.elapsed(),
                    false,
                );
                self.log_build_error(&e);
                self.metrics.verification_time = verification_start.elapsed().as_secs_f64();
                return;
            }
            self.record_module_timing(
                target.clone(),
                goal_count,
                &module_metrics_before,
                module_start.elapsed(),
                false,
            );

            // Early exit if we have a warning and exit_on_warning is enabled
            if self.exit_on_warning && !self.status.is_good() {
                self.metrics.verification_time = verification_start.elapsed().as_secs_f64();
                return;
            }
        }
        self.metrics.verification_time = verification_start.elapsed().as_secs_f64();

        // If the build succeeded, remove unused certs that were preserved during verification
        if self.status.is_good() {
            if let Some(ref mut cache) = self.build_cache {
                for (descriptor, used_cert_count) in &self.used_cert_counts {
                    if let Some(cert_store) = cache.get_certificates_mut(descriptor) {
                        // Trim to only keep the used certs (remove unused/old certs)
                        cert_store.certs.truncate(*used_cert_count);
                    }
                }
            }
        }
    }

    /// Tries to skip building a module if it and all its dependencies are unchanged.
    /// If successful, copies certificates to the new build cache and returns true.
    /// This only works when check_hashes is true.
    fn try_skip_unchanged_module(
        &mut self,
        module_id: ModuleId,
        target: &ModuleDescriptor,
    ) -> bool {
        if !self.check_hashes || self.force_search {
            return false;
        }

        let Some(descriptor) = self.project().get_module_descriptor(module_id) else {
            return false;
        };

        let Some(current_hash) = self.project().get_module_content_hash(module_id) else {
            return false;
        };

        if !self
            .project()
            .build_cache()
            .manifest_matches(descriptor, current_hash)
        {
            return false;
        }

        // Check all dependencies recursively
        for dep_id in self.project().all_dependencies(module_id) {
            let Some(dep_descriptor) = self.project().get_module_descriptor(dep_id) else {
                return false;
            };

            let Some(dep_hash) = self.project().get_module_content_hash(dep_id) else {
                return false;
            };

            if !self
                .project()
                .build_cache()
                .manifest_matches(dep_descriptor, dep_hash)
            {
                return false;
            }
        }

        let Some(_existing_certs) = self.project().build_cache().get_certificates(target) else {
            // This is a bad case. The different build files are inconsistent.
            // Well, just ignore it.
            return false;
        };

        // We verified that certificates exist, but we don't copy them to the new cache.
        // They'll be handled during the merge in update_build_cache.
        // We still need to update the manifest though.
        if let ModuleDescriptor::Name(parts) = target {
            self.build_cache
                .as_mut()
                .unwrap()
                .manifest
                .insert(parts, current_hash);
        }

        true
    }

    /// Consumes the builder and returns the build cache if the build was successful
    /// and we should update the cache.
    /// Note: write_cache is NOT checked here - that's handled by update_build_cache
    /// which decides whether to write to disk. We always return the cache so that
    /// in-memory certificate lookups work (e.g., for selection requests).
    pub fn into_build_cache(self) -> Option<BuildCache> {
        // We save certificates even when there are warnings (partially verified modules)
        // so that selection requests can show proofs for individual verified statements
        if !self.status.is_error() && self.goal_filter.is_none() {
            self.build_cache
        } else {
            None
        }
    }

    /// Returns the build cache if the build was successful and leaves the builder
    /// otherwise intact. This is useful for owners that need their own Drop logic.
    pub fn take_build_cache(&mut self) -> Option<BuildCache> {
        if !self.status.is_error() && self.goal_filter.is_none() {
            self.build_cache.take()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        compact_check_cert_error, format_goal_panic_message, panic_payload_to_string, BuildMetrics,
        EvalSkipTail,
    };

    #[test]
    fn test_info_lines_put_pending_elaboration_after_ok() {
        let metrics = BuildMetrics {
            goals_total: 2,
            goals_success: 2,
            pending_modules_total: 1,
            pending_goals_total: 3,
            ..BuildMetrics::default()
        };

        let lines = metrics.info_lines();
        let ok_index = lines
            .iter()
            .position(|line| line == "2/2 OK")
            .expect("OK summary should be present");
        let pending_index = lines
            .iter()
            .position(|line| line == "3 pending goals elaborated in 1 modules")
            .expect("pending elaboration summary should be present");

        assert!(pending_index > ok_index);
    }

    #[test]
    fn test_eval_skip_tail_tracks_consecutive_plain_checkpoints() {
        let mut tail = EvalSkipTail::new(2);
        assert_eq!(tail.checkpoint_for(1), None);

        tail.record_plain(10);
        assert_eq!(tail.checkpoint_for(0), None);
        assert_eq!(tail.checkpoint_for(1), Some(10));
        assert_eq!(tail.checkpoint_for(2), None);

        tail.record_plain(20);
        assert_eq!(tail.checkpoint_for(1), Some(20));
        assert_eq!(tail.checkpoint_for(2), Some(10));

        tail.record_plain(30);
        assert_eq!(tail.checkpoint_for(1), Some(30));
        assert_eq!(tail.checkpoint_for(2), Some(20));
        assert_eq!(tail.checkpoint_for(3), None);

        tail.record_barrier();
        assert_eq!(tail.checkpoint_for(1), None);
    }

    #[test]
    fn test_eval_skip_tail_disabled_when_max_skip_is_zero() {
        let mut tail = EvalSkipTail::new(0);
        tail.record_plain(10);
        assert_eq!(tail.checkpoint_for(1), None);
    }

    #[test]
    fn test_compact_check_cert_error_strips_generic_debug() {
        let error = "Claim failed\n(generic debug: huge blob)";
        assert_eq!(compact_check_cert_error(error), "Claim failed");
    }

    #[test]
    fn test_compact_check_cert_error_truncates_middle() {
        let error = format!("prefix {} suffix", "x".repeat(1000));
        let compact = compact_check_cert_error(&error);
        assert!(compact.contains("["));
        assert!(compact.contains("chars omitted"));
        assert!(compact.starts_with("prefix "));
        assert!(compact.ends_with(" suffix"));
    }

    #[test]
    fn test_panic_payload_to_string_accepts_string_payloads() {
        assert_eq!(
            panic_payload_to_string(Box::new("oops".to_string())),
            "oops"
        );
        assert_eq!(panic_payload_to_string(Box::new("oops")), "oops");
    }

    #[test]
    fn test_format_goal_panic_message_includes_repro_context() {
        let message = format_goal_panic_message("internal panic", "finite_group", 114);
        assert!(message.contains("internal panic"));
        assert!(message.contains("panic during certificate generation at finite_group:114"));
        assert!(message.contains("acorn verify finite_group --line 114 --force-search"));
    }
}
