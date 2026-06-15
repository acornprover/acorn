use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::builder::Builder;
use crate::elaborator::lowered_module::{LoweredFactId, LoweredGoalId, LoweredItem, LoweredModule};
use crate::elaborator::lowering::LoweredFact;
use crate::elaborator::source::SourceType;
use crate::kernel::proof_step::Rule;
use crate::module::{LoadState, ModuleDescriptor};
use crate::processor::Processor;
use crate::project::{Project, ProjectConfig, UsageMode};
use crate::prover::{Outcome, ProverMode, ScoringConfig};
use tokio_util::sync::CancellationToken;

const DEFAULT_SIMPLIFY_TIMEOUT_SECS: f32 = 0.1;
const DEFAULT_SIMPLIFY_ACTIVATION_LIMIT: i32 = 2000;

#[derive(Clone, Debug)]
pub struct SimplifyOptions {
    pub timeout_secs: f32,
    pub activation_limit: i32,
    pub dry_run: bool,
}

impl Default for SimplifyOptions {
    fn default() -> Self {
        Self {
            timeout_secs: DEFAULT_SIMPLIFY_TIMEOUT_SECS,
            activation_limit: DEFAULT_SIMPLIFY_ACTIVATION_LIMIT,
            dry_run: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimplifyRemoval {
    pub first_line: u32,
    pub last_line: u32,
    pub affected_goals: usize,
}

#[derive(Clone, Debug)]
pub struct SimplifyReport {
    pub target_path: PathBuf,
    pub considered: usize,
    pub removed: Vec<SimplifyRemoval>,
    pub dry_run: bool,
}

impl SimplifyReport {
    pub fn removed_count(&self) -> usize {
        self.removed.len()
    }
}

struct LoadedTarget {
    project: Project,
    descriptor: ModuleDescriptor,
    target_path: PathBuf,
    source: String,
    lowered: LoweredModule,
}

#[derive(Clone, Copy, Debug)]
struct Candidate {
    goal: LoweredGoalId,
    post_fact: LoweredFactId,
    first_line: u32,
    last_line: u32,
}

pub fn simplify_file(
    start_path: &Path,
    target: &str,
    options: SimplifyOptions,
) -> Result<SimplifyReport, String> {
    if target.trim().is_empty() {
        return Err("simplify requires a target file or module".to_string());
    }
    if target == "-" {
        return Err("simplify cannot read from stdin because it edits a source file".to_string());
    }
    if options.timeout_secs <= 0.0 {
        return Err("--timeout must be greater than 0".to_string());
    }
    if options.activation_limit <= 0 {
        return Err("--activations must be at least 1".to_string());
    }

    let mut cursor_line = 0;
    let mut considered = 0;
    let mut removed = Vec::new();
    let mut working_source: Option<String> = None;

    let target_path = loop {
        let loaded = load_target(start_path, target, working_source.as_deref(), false)?;
        let current_target_path = loaded.target_path.clone();
        let candidates = collect_candidates(&loaded.lowered, cursor_line);
        let Some(candidate) = candidates.first().copied() else {
            break current_target_path;
        };
        considered += 1;

        let affected_goals = affected_goals(&loaded.lowered, candidate.post_fact);
        if can_remove_candidate(&loaded, candidate, &affected_goals, &options)? {
            let edited =
                remove_line_range(&loaded.source, candidate.first_line, candidate.last_line)
                    .ok_or_else(|| {
                        format!(
                            "candidate line range {}-{} is outside {}",
                            candidate.first_line + 1,
                            candidate.last_line + 1,
                            loaded.target_path.display()
                        )
                    })?;

            let edited_loaded =
                load_target(start_path, target, Some(&edited), true).map_err(|e| {
                    simplify_bug_message(
                        candidate,
                        "candidate passed masked reproving but edited source does not load",
                        &e,
                    )
                })?;
            verify_edited_target(&edited_loaded).map_err(|e| {
                simplify_bug_message(
                    candidate,
                    "candidate passed masked reproving but edited source does not verify",
                    &e,
                )
            })?;

            if options.dry_run {
                working_source = Some(edited);
            } else {
                std::fs::write(&loaded.target_path, &edited).map_err(|e| {
                    format!("error writing {}: {}", loaded.target_path.display(), e)
                })?;
                working_source = None;
            }
            removed.push(SimplifyRemoval {
                first_line: candidate.first_line,
                last_line: candidate.last_line,
                affected_goals: affected_goals.len(),
            });
            cursor_line = candidate.first_line;
        } else {
            cursor_line = candidate.last_line + 1;
        }
    };

    Ok(SimplifyReport {
        target_path,
        considered,
        removed,
        dry_run: options.dry_run,
    })
}

fn load_target(
    start_path: &Path,
    target: &str,
    source_override: Option<&str>,
    read_cache: bool,
) -> Result<LoadedTarget, String> {
    let config = ProjectConfig {
        usage_mode: UsageMode::Verify,
        use_filesystem: true,
        read_cache,
        write_cache: false,
        update_version: false,
    };
    let mut project = Project::new_local(start_path, config).map_err(|e| e.cli_message())?;
    let target_path = resolve_target_path(&project, start_path, target)?;

    if let Some(source) = source_override {
        project
            .update_file(target_path.clone(), source, 1)
            .map_err(|e| format!("Error loading target '{}': {}", target, e))?;
    } else {
        project
            .add_target_by_path(&target_path)
            .map_err(|e| format!("Error loading target '{}': {}", target, e))?;
    }

    let descriptor = project
        .descriptor_from_path(&target_path)
        .map_err(|e| format!("Error resolving target '{}': {}", target, e))?;
    let source = match source_override {
        Some(source) => source.to_string(),
        None => std::fs::read_to_string(&target_path)
            .map_err(|e| format!("error reading {}: {}", target_path.display(), e))?,
    };
    let lowered = match project.get_module(&descriptor) {
        LoadState::Ok(module) => module
            .lowered()
            .ok_or_else(|| format!("Error loading target '{}': missing lowered module", target))?
            .clone(),
        LoadState::Error(error) => {
            return Err(format!("Error loading target '{}': {}", target, error));
        }
        LoadState::None => {
            return Err(format!("Error loading target '{}': no such module", target))
        }
        LoadState::Registered | LoadState::Loading => {
            return Err(format!("Error loading target '{}'", target));
        }
    };

    Ok(LoadedTarget {
        project,
        descriptor,
        target_path,
        source,
        lowered,
    })
}

fn simplify_bug_message(candidate: Candidate, reason: &str, detail: &str) -> String {
    format!(
        "simplify bug: {} at lines {}-{}\n{}",
        reason,
        candidate.first_line + 1,
        candidate.last_line + 1,
        detail
    )
}

fn verify_edited_target(loaded: &LoadedTarget) -> Result<(), String> {
    let mut events = Vec::new();
    let (status, result) = {
        let mut builder = Builder::new(&loaded.project, CancellationToken::new(), |event| {
            if let Some(message) = event.log_message {
                events.push(message);
            }
        });
        builder.check_hashes = false;
        builder.exit_on_warning = true;
        builder.operation_verb = "simplified";
        builder.begin_module_work_build(1);
        let result = builder
            .verify_lowered_module(&loaded.descriptor, &loaded.lowered)
            .map_err(|e| e.message);
        builder.finish_module_work_build();
        (builder.status, result)
    };

    if let Err(error) = result {
        events.push(error);
        return Err(events.join("\n"));
    }
    if status.is_good() {
        return Ok(());
    }

    let details = if events.is_empty() {
        format!("verification status: {}", status.verb())
    } else {
        events.join("\n")
    };
    Err(details)
}

fn resolve_target_path(
    project: &Project,
    start_path: &Path,
    target: &str,
) -> Result<PathBuf, String> {
    let path = PathBuf::from(target);
    let looks_like_path = path.is_absolute()
        || target.contains('/')
        || target.starts_with('.')
        || target.ends_with(".ac");
    if looks_like_path {
        return Ok(if path.is_relative() {
            start_path.join(path)
        } else {
            path
        });
    }
    project
        .path_from_module_name(target)
        .map_err(|e| format!("Error resolving module '{}': {}", target, e))
}

fn collect_candidates(lowered: &LoweredModule, cursor_line: u32) -> Vec<Candidate> {
    let mut exported_claims = HashSet::new();
    collect_exported_claims(&lowered.items, &mut exported_claims);

    let mut candidates = Vec::new();
    collect_candidates_in_items(
        lowered,
        &lowered.items,
        0,
        cursor_line,
        &exported_claims,
        &mut candidates,
    );
    candidates.sort_by_key(|candidate| {
        (
            candidate.first_line,
            candidate.last_line,
            candidate.post_fact.index(),
            candidate.goal.index(),
        )
    });
    candidates
}

fn collect_candidates_in_items(
    lowered: &LoweredModule,
    items: &[LoweredItem],
    depth: usize,
    cursor_line: u32,
    exported_claims: &HashSet<LoweredFactId>,
    candidates: &mut Vec<Candidate>,
) {
    for item in items {
        match item {
            LoweredItem::Claim {
                goal,
                post_fact,
                first_line,
                last_line,
            } => {
                let lowered_goal = &lowered.goal(*goal).lowered_goal.goal;
                if depth > 0
                    && *first_line >= cursor_line
                    && !exported_claims.contains(post_fact)
                    && matches!(
                        lowered_goal.proposition.source.source_type,
                        SourceType::Anonymous
                    )
                    && fact_is_anonymous(lowered.fact(*post_fact))
                {
                    candidates.push(Candidate {
                        goal: *goal,
                        post_fact: *post_fact,
                        first_line: *first_line,
                        last_line: *last_line,
                    });
                }
            }
            LoweredItem::Block { items, .. } => {
                collect_candidates_in_items(
                    lowered,
                    items,
                    depth + 1,
                    cursor_line,
                    exported_claims,
                    candidates,
                );
            }
            LoweredItem::Fact { .. } => {}
        }
    }
}

fn collect_exported_claims(items: &[LoweredItem], exported_claims: &mut HashSet<LoweredFactId>) {
    for item in items {
        if let LoweredItem::Block {
            items,
            external_fact: Some(_),
            ..
        } = item
        {
            if let Some(fact) = last_claim_fact(items) {
                exported_claims.insert(fact);
            }
        }
        if let LoweredItem::Block { items, .. } = item {
            collect_exported_claims(items, exported_claims);
        }
    }
}

fn last_claim_fact(items: &[LoweredItem]) -> Option<LoweredFactId> {
    for item in items.iter().rev() {
        match item {
            LoweredItem::Claim { post_fact, .. } => return Some(*post_fact),
            LoweredItem::Block { items, .. } => {
                if let Some(fact) = last_claim_fact(items) {
                    return Some(fact);
                }
            }
            LoweredItem::Fact { .. } => {}
        }
    }
    None
}

fn fact_is_anonymous(fact: &LoweredFact) -> bool {
    !fact.steps.is_empty()
        && fact.steps.iter().all(|step| match &step.rule {
            Rule::Assumption(info) => matches!(info.source.source_type, SourceType::Anonymous),
            _ => false,
        })
}

fn affected_goals(lowered: &LoweredModule, excluded_fact: LoweredFactId) -> Vec<LoweredGoalId> {
    lowered
        .goals()
        .filter_map(|(goal_id, _)| {
            let visible = lowered.visible_fact_ids_for(goal_id)?;
            visible.contains(&excluded_fact).then_some(goal_id)
        })
        .collect()
}

fn can_remove_candidate(
    loaded: &LoadedTarget,
    candidate: Candidate,
    affected_goals: &[LoweredGoalId],
    options: &SimplifyOptions,
) -> Result<bool, String> {
    for goal_id in affected_goals {
        if !prove_without_fact(loaded, *goal_id, candidate.post_fact, options)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn prove_without_fact(
    loaded: &LoadedTarget,
    goal_id: LoweredGoalId,
    excluded_fact: LoweredFactId,
    options: &SimplifyOptions,
) -> Result<bool, String> {
    let entry = loaded.lowered.goal(goal_id);
    let visible = loaded
        .lowered
        .visible_fact_ids_for(goal_id)
        .ok_or_else(|| {
            format!(
                "lowered goal {} not found in {}",
                goal_id.index(),
                loaded.target_path.display()
            )
        })?;
    let mut processor = Processor::with_imports_and_scoring_config(
        None,
        &entry.bindings,
        &loaded.project,
        ScoringConfig::default(),
    )
    .map_err(|e| e.message)?;
    for fact_id in visible {
        if fact_id != excluded_fact {
            processor
                .add_lowered_fact(loaded.lowered.fact(fact_id))
                .map_err(|e| e.message)?;
        }
    }
    processor.set_lowered_goal(&entry.lowered_goal);
    let outcome = processor.search(
        ProverMode::Interactive {
            timeout_secs: options.timeout_secs,
            activation_limit: options.activation_limit,
        },
        &entry.lowered_goal.kernel_context,
    );
    Ok(outcome == Outcome::Success)
}

fn remove_line_range(source: &str, first_line: u32, last_line: u32) -> Option<String> {
    if first_line > last_line {
        return None;
    }
    let mut lines: Vec<&str> = source.split_inclusive('\n').collect();
    let first = first_line as usize;
    let last = last_line as usize;
    if first >= lines.len() || last >= lines.len() {
        return None;
    }
    lines.drain(first..=last);
    Some(lines.concat())
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    fn write_project(source: &str) -> (tempfile::TempDir, PathBuf) {
        let temp = tempfile::TempDir::new().expect("temp project should be created");
        let root = temp.path();
        fs::write(root.join("acorn.toml"), "").expect("acorn.toml should be written");
        fs::create_dir(root.join("src")).expect("src directory should be created");
        fs::create_dir(root.join("build")).expect("build directory should be created");
        let path = root.join("src/main.ac");
        fs::write(&path, source).expect("main.ac should be written");
        (temp, path)
    }

    #[test]
    fn remove_line_range_preserves_other_lines() {
        assert_eq!(
            remove_line_range("a\nb\nc\n", 1, 1).as_deref(),
            Some("a\nc\n")
        );
        assert_eq!(remove_line_range("a\nb", 0, 0).as_deref(), Some("b"));
        assert!(remove_line_range("a\n", 2, 2).is_none());
    }

    #[test]
    fn simplify_removes_redundant_proof_local_claim() {
        let source = concat!(
            "let a: Bool = axiom\n",
            "let b: Bool = axiom\n",
            "axiom ab {\n",
            "    a implies b\n",
            "}\n",
            "theorem goal {\n",
            "    a implies b\n",
            "} by {\n",
            "    a implies b\n",
            "    a implies b\n",
            "}\n",
        );
        let (temp, path) = write_project(source);

        let report = simplify_file(
            temp.path(),
            "src/main.ac",
            SimplifyOptions {
                timeout_secs: 0.1,
                activation_limit: 2000,
                dry_run: false,
            },
        )
        .expect("simplify should run");

        assert_eq!(report.target_path, path);
        assert_eq!(report.removed_count(), 2);
        assert_eq!(
            fs::read_to_string(&path).expect("source should be readable"),
            concat!(
                "let a: Bool = axiom\n",
                "let b: Bool = axiom\n",
                "axiom ab {\n",
                "    a implies b\n",
                "}\n",
                "theorem goal {\n",
                "    a implies b\n",
                "} by {\n",
                "}\n",
            )
        );
    }

    #[test]
    fn simplify_dry_run_does_not_write_source() {
        let source = concat!(
            "let a: Bool = axiom\n",
            "let b: Bool = axiom\n",
            "axiom ab {\n",
            "    a implies b\n",
            "}\n",
            "theorem goal {\n",
            "    a implies b\n",
            "} by {\n",
            "    a implies b\n",
            "    a implies b\n",
            "}\n",
        );
        let (temp, path) = write_project(source);

        let report = simplify_file(
            temp.path(),
            "main",
            SimplifyOptions {
                timeout_secs: 0.1,
                activation_limit: 2000,
                dry_run: true,
            },
        )
        .expect("simplify should run");

        assert!(report.dry_run);
        assert_eq!(report.removed_count(), 2);
        assert_eq!(
            fs::read_to_string(&path).expect("source should be readable"),
            source
        );
    }
}
