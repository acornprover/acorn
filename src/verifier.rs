use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::io::BufRead;
use std::io::IsTerminal;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use tokio_util::sync::CancellationToken;

use crate::builder::{
    BuildEvent, BuildMetrics, BuildStatus, Builder, LoadedModuleWorkBatch, ModuleTiming,
};
use crate::module::ModuleDescriptor;
use crate::project::{
    ImportError, ParallelProjectLoader, Project, ProjectConfig, ProjectError, ProjectView,
    UsageMode,
};

fn resolve_target_path(start_path: &std::path::Path, target: &str) -> PathBuf {
    let path = PathBuf::from(target);
    if path.is_relative() {
        start_path.join(path)
    } else {
        path
    }
}

fn read_stdin_appended_target(
    project: &Project,
    path: &std::path::Path,
    stdin_override: Option<&str>,
) -> Result<String, String> {
    let mut text = project
        .read_file(&path.to_path_buf())
        .map_err(|e| e.to_string())?;
    if let Some(stdin_override) = stdin_override {
        text.push_str(stdin_override);
        return Ok(text);
    }

    if std::io::stdin().is_terminal() {
        return Err("cannot read stdin in an active terminal".to_string());
    }

    let stdin = std::io::stdin();
    let locked = stdin.lock();
    for line in locked.lines() {
        text.push_str(&line.map_err(|e| e.to_string())?);
        text.push('\n');
    }
    Ok(text)
}

#[derive(Debug)]
pub enum VerifierSetupError {
    Message(String),
    Project(ProjectError),
}

impl VerifierSetupError {
    pub fn cli_message(&self) -> String {
        match self {
            Self::Message(message) => message.clone(),
            Self::Project(error) => error.cli_message(),
        }
    }
}

impl From<String> for VerifierSetupError {
    fn from(error: String) -> Self {
        Self::Message(error)
    }
}

impl From<ImportError> for VerifierSetupError {
    fn from(error: ImportError) -> Self {
        Self::Message(error.to_string())
    }
}

impl From<ProjectError> for VerifierSetupError {
    fn from(error: ProjectError) -> Self {
        Self::Project(error)
    }
}

impl fmt::Display for VerifierSetupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Message(message) => write!(f, "{}", message),
            Self::Project(error) => write!(f, "{}", error),
        }
    }
}

/// Output from running the verifier
#[derive(Debug)]
pub struct VerifierOutput {
    /// The overall build status
    pub status: BuildStatus,

    /// Build metrics collected during verification
    pub metrics: BuildMetrics,

    /// Timing information collected during verification.
    pub timings: VerifierTimings,

    /// Per-module timing information collected during the build phase.
    pub module_timings: Vec<ModuleTiming>,

    /// All build events collected during verification
    pub events: Vec<BuildEvent>,
}

/// Timing information for one verifier run.
#[derive(Clone, Copy, Debug, Default)]
pub struct VerifierTimings {
    /// Total time spent constructing the verifier before target loading.
    pub setup: Duration,

    /// Time spent loading the build cache.
    pub cache_load: Duration,

    /// Time spent loading and elaborating target modules.
    pub target_load: Duration,

    /// Time spent in the builder's module-work staging phase.
    pub build_loading: Duration,

    /// Time spent in the builder verification phase.
    pub build_verification: Duration,

    /// Total time spent loading targets and running builder work after setup.
    pub build_total: Duration,
}

impl VerifierOutput {
    /// How many verification events were collected.
    pub fn num_verified(&self) -> usize {
        self.events.iter().filter(|e| e.verified.is_some()).count()
    }

    pub fn is_success(&self) -> bool {
        self.status == BuildStatus::Good
    }

    fn format_duration(duration: Duration) -> String {
        let seconds = duration.as_secs_f64();
        if seconds >= 1.0 {
            format!("{:.3}s", seconds)
        } else {
            format!("{:.1}ms", seconds * 1000.0)
        }
    }

    fn format_seconds(seconds: f64) -> String {
        Self::format_duration(Duration::from_secs_f64(seconds.max(0.0)))
    }

    /// Print a command-specific timing breakdown.
    pub fn print_timing_breakdown(
        &self,
        title: &str,
        build_phase_label: &str,
        include_cert_throughput: bool,
    ) {
        let total = self.timings.setup + self.timings.build_total;

        println!();
        println!("{} timing:", title);
        println!(
            "project setup: {}",
            Self::format_duration(self.timings.setup)
        );
        println!(
            "  cache load: {}",
            Self::format_duration(self.timings.cache_load)
        );
        println!(
            "target/module load: {}",
            Self::format_duration(self.timings.target_load)
        );
        println!(
            "build loading phase: {}",
            Self::format_duration(self.timings.build_loading)
        );
        println!(
            "{}: {}",
            build_phase_label,
            Self::format_duration(self.timings.build_verification)
        );
        if self.metrics.cert_checks_total > 0 {
            println!(
                "  cached cert checks: {} ({} ok / {} attempted)",
                Self::format_seconds(self.metrics.cert_check_time),
                self.metrics.cert_checks_success,
                self.metrics.cert_checks_total
            );
        }
        if self.metrics.searches_total > 0 {
            println!(
                "  proof search: {} ({} ok / {} attempted)",
                Self::format_seconds(self.metrics.search_time),
                self.metrics.searches_success,
                self.metrics.searches_total
            );
        }
        let accounted_time = self.metrics.cert_check_time + self.metrics.search_time;
        let other_verification = self.timings.build_verification.as_secs_f64() - accounted_time;
        if (self.metrics.cert_checks_total > 0 || self.metrics.searches_total > 0)
            && other_verification > 0.001
        {
            println!(
                "  other verification: {}",
                Self::format_seconds(other_verification)
            );
        }
        println!("total measured: {}", Self::format_duration(total));

        if include_cert_throughput
            && self.metrics.certs_cached > 0
            && self.timings.build_verification.as_secs_f64() > 0.0
        {
            let certs_per_second =
                self.metrics.certs_cached as f64 / self.timings.build_verification.as_secs_f64();
            println!("certificate throughput: {:.0} certs/s", certs_per_second);
        }
    }

    /// Print per-module timing details for build runs.
    pub fn print_verify_module_timing(&self) {
        let skipped_count = self
            .module_timings
            .iter()
            .filter(|timing| timing.skipped)
            .count();
        let mut rebuilt = self
            .module_timings
            .iter()
            .filter(|timing| !timing.skipped)
            .collect::<Vec<_>>();

        println!();
        println!("Module timing:");
        println!("skipped modules: {}", skipped_count);
        println!("rebuilt modules: {}", rebuilt.len());

        if rebuilt.is_empty() {
            return;
        }

        rebuilt.sort_by(|a, b| b.elapsed.total_cmp(&a.elapsed));
        let limit = 12;

        println!(
            "  {:<32} {:>9} {:>9} {:>5} {:>10} {:>8} {:>11} {:>8}",
            "module", "goals", "certs", "new", "cert time", "searches", "search time", "total"
        );
        for timing in rebuilt.iter().take(limit) {
            let goals = format!("{}/{}", timing.goals_done, timing.goals_total);
            let certs = if timing.cert_checks_total == 0 {
                "-".to_string()
            } else {
                format!(
                    "{}/{}",
                    timing.cert_checks_success, timing.cert_checks_total
                )
            };
            let searches = if timing.searches_total == 0 {
                "-".to_string()
            } else {
                format!("{}/{}", timing.searches_success, timing.searches_total)
            };
            println!(
                "  {:<32} {:>9} {:>9} {:>5} {:>10} {:>8} {:>11} {:>8}",
                timing.module.to_string(),
                goals,
                certs,
                timing.certs_created,
                Self::format_seconds(timing.cert_check_time),
                searches,
                Self::format_seconds(timing.search_time),
                Self::format_seconds(timing.elapsed)
            );
        }

        if rebuilt.len() > limit {
            println!("  ... {} more rebuilt modules", rebuilt.len() - limit);
        }
    }
}

/// Represents a line selection for verification: either a single line or a range.
#[derive(Clone, Debug)]
pub enum LineSelection {
    /// A single line number (1-based, external)
    Single(u32),
    /// A range of lines, inclusive (1-based, external)
    Range(u32, u32),
}

#[derive(Clone, Debug)]
enum TargetSpec {
    All,
    Path(PathBuf),
    Name(String),
}

/// The Verifier manages the run of a single build.
/// It creates its own project.
pub struct Verifier {
    /// Pointer to the manually managed project for cleanup
    project_ptr: *mut Project,

    /// The target module to verify.
    /// If None, all modules are verified.
    target: Option<String>,

    target_spec: TargetSpec,

    include_surface_check_dirs: bool,
    surface_check_explicit_targets: bool,

    /// Optional line selection (1-based, external) to verify specific goal(s).
    /// If this is set, target must be as well.
    pub line_selection: Option<LineSelection>,

    /// Optional 1-based goal index for a single selected line.
    pub goal_index: Option<usize>,

    /// When this flag is set, verification exits immediately upon encountering any warning.
    /// This is useful for operations like the cleaner where any warning means the change
    /// should be reverted, so there's no point continuing verification.
    pub exit_on_warning: bool,

    /// Events collected during verification
    events: Rc<RefCell<Vec<BuildEvent>>>,

    /// The builder for verification
    pub builder: Builder<'static>,

    /// Total time spent constructing this verifier.
    setup_time: Duration,

    /// Time spent loading the build cache.
    cache_load_time: Duration,

    /// Time spent loading target modules.
    target_load_time: Duration,
}

impl Verifier {
    pub fn new(
        start_path: PathBuf,
        config: ProjectConfig,
        target: Option<String>,
    ) -> Result<Self, VerifierSetupError> {
        Self::new_inner(start_path, config, target, None, false, false)
    }

    pub fn new_for_check(
        start_path: PathBuf,
        mut config: ProjectConfig,
        target: Option<String>,
    ) -> Result<Self, VerifierSetupError> {
        config.usage_mode = UsageMode::Check;
        Self::new_inner(start_path, config, target, None, true, true)
    }

    fn new_inner(
        start_path: PathBuf,
        config: ProjectConfig,
        target: Option<String>,
        stdin_override: Option<&str>,
        include_surface_check_dirs: bool,
        surface_check_explicit_targets: bool,
    ) -> Result<Self, VerifierSetupError> {
        let setup_start = std::time::Instant::now();
        let mut project = Project::new_local(&start_path, config.clone())?;
        let cache_load_time = project.cache_load_time;
        let mut normalized_target = target.clone();

        let target_spec = if let Some(ref target) = target {
            if target == "-" {
                TargetSpec::Path(PathBuf::from("<stdin>"))
            } else if let Some(inner_target) = target.strip_prefix("-:") {
                let path = resolve_target_path(&start_path, inner_target);
                let text = read_stdin_appended_target(&project, &path, stdin_override)?;
                project.update_file(path.clone(), &text, 0)?;
                normalized_target = Some(path.to_string_lossy().into_owned());
                TargetSpec::Path(path)
            } else if target.ends_with(".ac") {
                let path = resolve_target_path(&start_path, target);
                normalized_target = Some(path.to_string_lossy().into_owned());
                TargetSpec::Path(path)
            } else {
                TargetSpec::Name(target.clone())
            }
        } else {
            TargetSpec::All
        };
        let target_load_time = Duration::default();

        // Unsafe is to make this self-referential
        let project_box = Box::new(project);
        let project_ptr = Box::into_raw(project_box);
        let project: &'static Project = unsafe { &*project_ptr };
        let events = Rc::new(RefCell::new(Vec::new()));
        let events_clone = events.clone();

        // Set up the builder with event handler
        let mut builder = Builder::new(project, CancellationToken::new(), move |event| {
            if let Some(m) = &event.log_message {
                println!("{}", m);
            }

            // Store the event
            events_clone.borrow_mut().push(event);
        });

        if target.is_none() {
            builder.log_secondary_errors = false;
        }

        Ok(Self {
            project_ptr,
            target: normalized_target,
            target_spec,
            include_surface_check_dirs,
            surface_check_explicit_targets,
            line_selection: None,
            goal_index: None,
            exit_on_warning: false,
            events,
            builder,
            setup_time: setup_start.elapsed(),
            cache_load_time,
            target_load_time,
        })
    }

    #[cfg(test)]
    fn new_for_test(
        start_path: PathBuf,
        config: ProjectConfig,
        target: Option<String>,
        stdin_override: Option<&str>,
    ) -> Result<Self, VerifierSetupError> {
        Self::new_inner(start_path, config, target, stdin_override, false, false)
    }

    fn project_mut(&mut self) -> &mut Project {
        unsafe { &mut *self.project_ptr }
    }

    fn prepare_targets(
        &mut self,
    ) -> Result<(Vec<ModuleDescriptor>, Vec<ModuleDescriptor>), String> {
        let target_spec = self.target_spec.clone();
        let include_surface_check_dirs = self.include_surface_check_dirs;
        let surface_check_explicit_targets = self.surface_check_explicit_targets;
        let project = self.project_mut();
        let mut targets = Vec::new();
        let mut load_order = Vec::new();

        match target_spec {
            TargetSpec::All => {
                for descriptor in project.src_target_descriptors() {
                    let descriptor = project.add_unloaded_target_by_descriptor(&descriptor);
                    let build_descriptors = project.build_descriptors_for_target(&descriptor);
                    targets.extend(build_descriptors.clone());
                    load_order.extend(build_descriptors);
                }
                if include_surface_check_dirs {
                    for descriptor in project.surface_check_target_descriptors() {
                        let descriptor =
                            project.add_unloaded_surface_target_by_descriptor(&descriptor);
                        targets.push(descriptor.clone());
                        load_order.push(descriptor);
                    }
                }
            }
            TargetSpec::Path(path) => {
                let descriptor = project
                    .descriptor_from_path(&path)
                    .map_err(|e| format!("Error resolving target '{}': {}", path.display(), e))?;
                let descriptor =
                    if surface_check_explicit_targets && project.is_surface_check_path(&path) {
                        project.add_unloaded_surface_target_by_descriptor(&descriptor)
                    } else {
                        project.add_unloaded_target_by_descriptor(&descriptor)
                    };
                let build_descriptors = project.build_descriptors_for_target(&descriptor);
                targets.extend(build_descriptors.clone());
                load_order.extend(build_descriptors);
            }
            TargetSpec::Name(name) => {
                let descriptor =
                    project.add_unloaded_target_by_descriptor(&ModuleDescriptor::name(&name));
                let build_descriptors = project.build_descriptors_for_target(&descriptor);
                targets.extend(build_descriptors.clone());
                load_order.extend(build_descriptors);
            }
        }

        targets.sort();
        targets.dedup();
        load_order.sort();
        load_order.dedup();
        load_order.sort_by(|left, right| {
            project
                .cached_module_work_estimate(right)
                .cmp(&project.cached_module_work_estimate(left))
                .then_with(|| left.cmp(right))
        });
        Ok((targets, load_order))
    }

    fn load_targets_regular(&mut self) -> Result<Duration, String> {
        let start = std::time::Instant::now();
        let target_spec = self.target_spec.clone();
        let include_surface_check_dirs = self.include_surface_check_dirs;
        let surface_check_explicit_targets = self.surface_check_explicit_targets;
        let project = self.project_mut();
        match target_spec {
            TargetSpec::All => {
                project.add_src_targets();
                if include_surface_check_dirs {
                    project.add_surface_check_dir_targets();
                }
            }
            TargetSpec::Path(path) => {
                if surface_check_explicit_targets && project.is_surface_check_path(&path) {
                    project
                        .add_surface_target_by_path(&path)
                        .map_err(|e| format!("Error loading target '{}': {}", path.display(), e))?;
                } else {
                    project
                        .add_target_by_path(&path)
                        .map_err(|e| format!("Error loading target '{}': {}", path.display(), e))?;
                }
            }
            TargetSpec::Name(name) => {
                project
                    .add_target_by_name(&name)
                    .map_err(|e| format!("Error loading module '{}': {}", name, e))?;
            }
        }
        Ok(start.elapsed())
    }

    fn load_and_build_streaming(&mut self) -> Result<Duration, String> {
        let (targets, load_order) = self.prepare_targets()?;
        let target_set = targets.iter().cloned().collect::<HashSet<_>>();
        let batch_limit = self.builder.check_jobs.max(1);
        let propagate_load_errors = !matches!(self.target_spec, TargetSpec::All);

        self.builder.begin_module_work_build(targets.len());

        if self.builder.can_pipeline_module_work(targets.len()) {
            if matches!(self.target_spec, TargetSpec::All) {
                // Elaboration/lowering has higher per-worker memory pressure than certificate
                // checking, so use a smaller loader pool and let the checker consume with
                // its normal --jobs parallelism.
                let loader_jobs = (self.builder.check_jobs / 4).max(1);
                let project_ptr = self.project_ptr;
                let mut loader = {
                    let project = unsafe { &mut *project_ptr };
                    ParallelProjectLoader::new(project, &targets, &load_order, loader_jobs)
                        .map_err(|error| format!("Error loading targets: {}", error))?
                };
                let (load_elapsed, processed) =
                    self.builder.process_module_work_pipeline(|| {
                        let load_start = std::time::Instant::now();
                        let project = unsafe { &mut *project_ptr };
                        match loader.next_loaded_modules(project, &target_set) {
                            Ok(Some(work)) => {
                                let project_view = ProjectView::new_without_lowered(project);
                                Ok(Some(LoadedModuleWorkBatch {
                                    project: Some(project_view),
                                    modules: work,
                                    load_elapsed: load_start.elapsed(),
                                }))
                            }
                            Ok(None) => Ok(None),
                            Err(error) => Err(format!("Error loading targets: {}", error)),
                        }
                    })?;

                let project_view = unsafe { ProjectView::new_without_lowered(&*self.project_ptr) };
                self.builder.set_project_view(project_view);
                self.builder
                    .log_unprocessed_target_states(&targets, &processed);
                self.builder.finish_module_work_build();
                return Ok(load_elapsed);
            }

            let project_ptr = self.project_ptr;
            let mut load_index = 0usize;
            let (load_elapsed, processed) = self.builder.process_module_work_pipeline(|| {
                let Some(descriptor) = load_order.get(load_index) else {
                    return Ok(None);
                };
                load_index += 1;

                let load_start = std::time::Instant::now();
                let load_result =
                    unsafe { (&mut *project_ptr).load_target_by_descriptor(descriptor) };
                if let Err(error) = load_result {
                    if propagate_load_errors {
                        return Err(format!("Error loading target '{}': {}", descriptor, error));
                    }
                }

                let work =
                    unsafe { (&mut *project_ptr).take_lowered_modules_for_target_set(&target_set) };
                let project = if work.is_empty() {
                    None
                } else {
                    Some(unsafe { ProjectView::new_without_lowered(&*project_ptr) })
                };
                Ok(Some(LoadedModuleWorkBatch {
                    project,
                    modules: work,
                    load_elapsed: load_start.elapsed(),
                }))
            })?;

            let project_view = unsafe { ProjectView::new_without_lowered(&*self.project_ptr) };
            self.builder.set_project_view(project_view);
            self.builder
                .log_unprocessed_target_states(&targets, &processed);
            self.builder.finish_module_work_build();
            return Ok(load_elapsed);
        }

        let mut processed = HashSet::new();
        let mut batch = Vec::new();
        let mut next_index = 0usize;
        let mut load_elapsed = Duration::default();

        for descriptor in &load_order {
            let load_start = std::time::Instant::now();
            let load_result =
                unsafe { (&mut *self.project_ptr).load_target_by_descriptor(descriptor) };
            if let Err(error) = load_result {
                if propagate_load_errors {
                    return Err(format!("Error loading target '{}': {}", descriptor, error));
                }
            }

            let work = unsafe {
                (&mut *self.project_ptr).take_lowered_modules_for_target_set(&target_set)
            };
            if !work.is_empty() {
                let project_view = unsafe { ProjectView::new_without_lowered(&*self.project_ptr) };
                self.builder.set_project_view(project_view);
            }
            let (work, skipped) = self.builder.prepare_loaded_module_work(work);
            processed.extend(skipped);
            for (descriptor, _) in &work {
                processed.insert(descriptor.clone());
            }
            batch.extend(work);
            load_elapsed += load_start.elapsed();

            if batch.len() >= batch_limit {
                let ready = std::mem::take(&mut batch);
                let project_view = unsafe { ProjectView::new_without_lowered(&*self.project_ptr) };
                self.builder.set_project_view(project_view);
                self.builder
                    .process_module_work_batch(ready, &mut next_index);
                if self.builder.status.is_error() {
                    break;
                }
            }
        }

        if !batch.is_empty() && !self.builder.status.is_error() {
            let project_view = unsafe { ProjectView::new_without_lowered(&*self.project_ptr) };
            self.builder.set_project_view(project_view);
            self.builder
                .process_module_work_batch(batch, &mut next_index);
        }

        let project_view = unsafe { ProjectView::new_without_lowered(&*self.project_ptr) };
        self.builder.set_project_view(project_view);
        self.builder
            .log_unprocessed_target_states(&targets, &processed);
        self.builder.finish_module_work_build();
        Ok(load_elapsed)
    }

    fn validate_changed_packages(&mut self) {
        if !self.builder.status.is_good() || self.builder.check_mode || self.builder.eval_mode {
            return;
        }
        let descriptors = self
            .builder
            .module_timings
            .iter()
            .filter(|timing| !timing.skipped)
            .map(|timing| timing.module.clone())
            .collect::<Vec<_>>();
        if descriptors.is_empty() {
            return;
        }

        let errors = unsafe { (*self.project_ptr).validate_packages_for_descriptors(descriptors) };
        if errors.is_empty() {
            return;
        }
        self.builder.status = BuildStatus::Error;
        for (_descriptor, error) in errors {
            self.builder.log_global(error.to_string());
        }
    }

    /// Returns VerifierOutput on success or clean failure.
    /// Returns an error string if verification fails during setup.
    pub fn run(mut self) -> Result<VerifierOutput, String> {
        self.builder.exit_on_warning = self.exit_on_warning;

        let can_stream_module_work = unsafe { (*self.project_ptr).config.usage_mode.is_batch() }
            && self.line_selection.is_none()
            && self.builder.cert_override.is_none();

        let build_start = std::time::Instant::now();
        let streamed = if can_stream_module_work {
            self.target_load_time = self.load_and_build_streaming()?;
            true
        } else {
            self.target_load_time = self.load_targets_regular()?;
            let project_view = unsafe { ProjectView::new(&*self.project_ptr) };
            self.builder.set_project_view(project_view);
            false
        };

        // If a specific line selection is provided along with a target, set up goal filtering
        if let Some(ref line_sel) = self.line_selection {
            let Some(target) = &self.target else {
                panic!("line_selection set without target");
            };
            // line values are external line numbers (1-based)
            match line_sel {
                LineSelection::Single(line) => {
                    if let Err(e) =
                        self.builder
                            .set_single_goal_with_index(target, *line, self.goal_index)
                    {
                        return Err(format!("Failed to set single goal: {}", e));
                    }
                }
                LineSelection::Range(start, end) => {
                    if let Err(e) = self.builder.set_goal_range(target, *start, *end) {
                        return Err(format!("Failed to set goal range: {}", e));
                    }
                }
            }
        }

        if !streamed {
            self.builder.build();
        }
        self.validate_changed_packages();
        let is_partial_build = self.target.is_some();
        self.builder
            .validate_strict_dependency_manifests(is_partial_build);
        let build_total = build_start.elapsed();
        self.builder.validate_goal_filter()?;
        self.builder.metrics.print(self.builder.status);

        // Create the output
        let status = self.builder.status;
        let metrics = self.builder.metrics.clone();
        let module_timings = self.builder.module_timings.clone();
        let timings = VerifierTimings {
            setup: self.setup_time,
            cache_load: self.cache_load_time,
            target_load: self.target_load_time,
            build_loading: Duration::from_secs_f64(metrics.loading_time),
            build_verification: Duration::from_secs_f64(metrics.verification_time),
            build_total,
        };
        let events = self.events.take();
        let output = VerifierOutput {
            status,
            metrics,
            timings,
            module_timings,
            events,
        };

        // Update the build cache if the build was successful
        // Pass is_partial_build flag: true if we have a specific target, false for full build
        if !self.builder.status.is_error() {
            if let Some(build_cache) = self.builder.take_build_cache() {
                unsafe {
                    (*self.project_ptr).update_build_cache(build_cache, is_partial_build);
                }
            }
        }

        Ok(output)
    }
}

impl Drop for Verifier {
    fn drop(&mut self) {
        if self.project_ptr.is_null() {
            return;
        }
        unsafe {
            drop(Box::from_raw(self.project_ptr));
        }
        self.project_ptr = std::ptr::null_mut();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certificate::{Certificate, CertificateStore};
    use crate::goal_partition::{goal_bucket, GoalBucketFilter};
    use crate::prover::trace::{trace_metadata_path, SearchTraceWriter};
    use assert_fs::fixture::ChildPath;
    use assert_fs::prelude::*;
    use assert_fs::TempDir;
    use std::io::Read;

    /// Creates a standard Acorn project layout with acorn.toml, src/, and build/ directories.
    /// Returns (project dir, src_dir, build_dir) for use in tests.
    /// Close the project directory after use to clean up.
    fn setup() -> (TempDir, ChildPath, ChildPath) {
        let temp = TempDir::new().unwrap();
        temp.child("acorn.toml").write_str("").unwrap();
        let src = temp.child("src");
        src.create_dir_all().unwrap();
        let build = temp.child("build");
        build.create_dir_all().unwrap();
        (temp, src, build)
    }

    fn cert_for_source(src: &ChildPath, source_rel: &str) -> ChildPath {
        let source_rel = std::path::Path::new(source_rel);
        let mut cert_rel = std::path::PathBuf::new();
        if let Some(parent) = source_rel.parent() {
            cert_rel.push(parent);
        }
        let stem = source_rel.file_stem().unwrap().to_string_lossy();
        cert_rel.push("certs");
        cert_rel.push(format!("{}.jsonl", stem));
        src.child(cert_rel.to_string_lossy().as_ref())
    }

    fn manifest_for_package(src: &ChildPath, package_rel: &str) -> ChildPath {
        let mut manifest_rel = std::path::PathBuf::new();
        if !package_rel.is_empty() {
            manifest_rel.push(package_rel);
        }
        manifest_rel.push("certs");
        manifest_rel.push("manifest.json");
        src.child(manifest_rel.to_string_lossy().as_ref())
    }

    fn save_cert_store(path: &ChildPath, store: CertificateStore) {
        std::fs::create_dir_all(path.path().parent().unwrap()).unwrap();
        store.save(path.path()).unwrap();
    }

    fn cert_from_lines(goal: &str, lines: &[&str]) -> Certificate {
        Certificate::new(
            goal.to_string(),
            crate::certificate_trace::ProofTrace {
                steps: lines
                    .iter()
                    .map(|line| crate::certificate_trace::TraceStep::claim((*line).to_string()))
                    .collect(),
            },
        )
    }

    fn empty_cert(goal: &str) -> Certificate {
        Certificate::new(
            goal.to_string(),
            crate::certificate_trace::ProofTrace { steps: vec![] },
        )
    }

    fn log_text(output: &VerifierOutput) -> String {
        output
            .events
            .iter()
            .filter_map(|e| e.log_message.as_ref())
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn write_imported_dependent_structure_repro(src: &ChildPath) {
        src.child("prelude.ac")
            .write_str(
                r#"
                inductive Option[T] {
                    none
                    some(T)
                }
                "#,
            )
            .unwrap();
        src.child("tiny_fin_base.ac")
            .write_str(
                r#"
                inductive Index {
                    zero
                    suc(Index)
                }

                inductive Value {
                    value
                }

                define okay(value: Value, n: Index) -> Bool {
                    true
                }

                structure TinyFin[n: Index] {
                    value: Value
                } constraint {
                    okay(value, n)
                }

                let tiny_zero(n: Index) -> result: TinyFin[Index.suc(n)] satisfy {
                    TinyFin[Index.suc(n)].new(Value.value) = Option.some(result)
                } by {
                    true
                }
                "#,
            )
            .unwrap();
        src.child("tiny_fin_constructor_user.ac")
            .write_str(
                r#"
                from tiny_fin_base import Index, Value, TinyFin, tiny_zero

                theorem tiny_zero_constructor_replay(n: Index) {
                    TinyFin[Index.suc(n)].new(Value.value) = Option.some(tiny_zero(n))
                }
                "#,
            )
            .unwrap();
        src.child("tiny_fin_projection_user.ac")
            .write_str(
                r#"
                from tiny_fin_base import Index, TinyFin, okay

                theorem tiny_field_projection_replay(n: Index, x: TinyFin[n]) {
                    okay(x.value, n)
                }
                "#,
            )
            .unwrap();
    }

    fn verify_then_strict_check(acornlib: &TempDir, target: &str) {
        let mut verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some(target.to_string()),
        )
        .unwrap();
        verify.builder.check_hashes = false;
        let verify_output = verify.run().unwrap();
        assert_eq!(
            verify_output.status,
            BuildStatus::Good,
            "verify should write a certificate before strict replay\n{}",
            log_text(&verify_output)
        );
        assert_eq!(verify_output.metrics.searches_success, 1);

        let check_config = ProjectConfig {
            usage_mode: UsageMode::Check,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        };
        let mut check = Verifier::new_for_check(
            acornlib.path().to_path_buf(),
            check_config,
            Some(target.to_string()),
        )
        .unwrap();
        check.builder.check_mode = true;
        check.builder.check_hashes = false;
        check.builder.strict = true;
        let check_output = check.run().unwrap();
        assert_eq!(
            check_output.status,
            BuildStatus::Good,
            "strict check should replay the certificate written by verify\n{}",
            log_text(&check_output)
        );
    }

    #[test]
    fn test_verifier_rejects_real_acornlib_in_unit_tests() {
        let project_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        if Project::find_local_acorn_library(&project_root).is_none() {
            return;
        }

        let err = match Verifier::new(project_root, ProjectConfig::default(), None) {
            Ok(_) => panic!("verifier should reject the real acornlib in unit tests"),
            Err(err) => err,
        };
        let err = err.to_string();
        assert!(
            err.contains("you should not use real acornlib during the unit tests"),
            "{err}"
        );
    }

    #[test]
    fn test_verifier_basic() {
        let (acornlib, src, build) = setup();

        // Create foo.ac inside the src directory
        let foo_ac = src.child("foo.ac");
        foo_ac
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier starting from the acornlib directory
        // Verify all modules (None) to test certificate caching
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;

        // Test that the verifier can run successfully on our theorem in the src directory
        let result = verifier1.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify the theorem in src directory: {:?}",
            result
        );

        // Check that we proved one goal, via search
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1);
        assert_eq!(output.metrics.goals_success, 1);
        assert_eq!(output.metrics.certs_cached, 0);
        assert_eq!(output.metrics.certs_unused, 0);
        assert_eq!(output.metrics.searches_total, 1);

        // With certificates enabled, we should NOT create YAML files
        let build_file = build.child("foo.yaml");
        assert!(
            !build_file.exists(),
            "Module cache YAML file should NOT exist when using certificates"
        );

        // Check that the cert file has one line
        let cert_file = cert_for_source(&src, "foo.ac");
        assert!(cert_file.exists(), "src/certs/foo.jsonl should exist");
        let jsonl_content = std::fs::read_to_string(cert_file.path()).unwrap();
        let line_count = jsonl_content.lines().count();
        assert_eq!(line_count, 1,);

        assert!(manifest_for_package(&src, "").exists());

        // Verify again (all modules)
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let result2 = verifier2.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        // Check that we proved one goal, via cached cert
        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(output2.metrics.goals_total, 1);
        assert_eq!(output2.metrics.goals_success, 1);
        assert_eq!(output2.metrics.certs_cached, 1);
        assert_eq!(output2.metrics.certs_unused, 0);
        assert_eq!(output2.metrics.searches_total, 0);

        // Check that the cert file still has one line
        assert!(cert_file.exists(), "src/certs/foo.jsonl should exist");
        let jsonl_content = std::fs::read_to_string(cert_file.path()).unwrap();
        let line_count = jsonl_content.lines().count();
        assert_eq!(line_count, 1,);

        // Now test check mode with verifier3 (all modules)
        let mut verifier3 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier3.builder.check_hashes = false;
        verifier3.builder.check_mode = true;
        let result3 = verifier3.run();
        assert!(
            result3.is_ok(),
            "Third verifier in check mode should successfully run: {:?}",
            result3
        );

        // Check that we proved one goal in check mode, via cached cert
        let output3 = result3.unwrap();
        assert_eq!(output3.status, BuildStatus::Good);
        assert_eq!(output3.metrics.goals_total, 1);
        assert_eq!(output3.metrics.goals_success, 1);
        assert_eq!(output3.metrics.certs_cached, 1);
        assert_eq!(output3.metrics.certs_unused, 0);
        // In check mode, we should never reach the search phase
        assert_eq!(output3.metrics.searches_total, 0);
    }

    #[test]
    fn test_explicit_surface_check_target_does_not_write_jsonl() {
        let (acornlib, _src, _build) = setup();
        let pending = acornlib.child("pending");
        pending.create_dir_all().unwrap();
        pending
            .child("ready.ac")
            .write_str(
                r#"
                theorem ready {
                    true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("pending/ready.ac".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(
            !pending.child("ready.jsonl").exists(),
            "surface-check directory targets should not write sidecar JSONL files"
        );
    }

    #[test]
    fn test_strict_check_allows_surface_check_axiom_statements() {
        let (acornlib, _src, _build) = setup();
        let pending = acornlib.child("pending");
        pending.create_dir_all().unwrap();
        pending
            .child("draft.ac")
            .write_str(
                r#"
                axiom draft_axiom {
                    true
                }
                "#,
            )
            .unwrap();

        let check_config = ProjectConfig {
            usage_mode: UsageMode::Check,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        };
        let mut verifier =
            Verifier::new_for_check(acornlib.path().to_path_buf(), check_config, None).unwrap();
        verifier.builder.check_mode = true;
        verifier.builder.check_hashes = false;
        verifier.builder.strict = true;

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.pending_modules_total, 1);
    }

    #[test]
    fn test_strict_replay_imported_dependent_constructor() {
        let (acornlib, src, _build) = setup();
        write_imported_dependent_structure_repro(&src);

        verify_then_strict_check(&acornlib, "tiny_fin_constructor_user");
    }

    #[test]
    fn test_strict_replay_imported_dependent_field_projection() {
        let (acornlib, src, _build) = setup();
        write_imported_dependent_structure_repro(&src);

        verify_then_strict_check(&acornlib, "tiny_fin_projection_user");
    }

    #[test]
    fn test_strict_check_allows_package_interface_theorem_declarations() {
        let (acornlib, src, _build) = setup();
        src.child("pkg").create_dir_all().unwrap();
        src.child("pkg/interface.ac")
            .write_str(
                r#"
                theorem public {
                    true
                }
                "#,
            )
            .unwrap();
        src.child("pkg/internal.ac")
            .write_str(
                r#"
                theorem public {
                    true
                } by {
                    true
                }
                "#,
            )
            .unwrap();

        let mut verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("pkg".to_string()),
        )
        .unwrap();
        verify.builder.check_hashes = false;
        let verify_output = verify.run().unwrap();
        assert_eq!(
            verify_output.status,
            BuildStatus::Good,
            "verify should write package certificates before strict replay\n{}",
            log_text(&verify_output)
        );

        let check_config = ProjectConfig {
            usage_mode: UsageMode::Check,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        };
        let mut check = Verifier::new_for_check(
            acornlib.path().to_path_buf(),
            check_config,
            Some("pkg".to_string()),
        )
        .unwrap();
        check.builder.check_mode = true;
        check.builder.check_hashes = false;
        check.builder.strict = true;
        let check_output = check.run().unwrap();
        assert_eq!(
            check_output.status,
            BuildStatus::Good,
            "strict check should allow package interface theorem declarations\n{}",
            log_text(&check_output)
        );
    }

    #[test]
    fn test_strict_check_rejects_stale_dependency_hashes() {
        let (acornlib, src, _build) = setup();
        src.child("pkg").create_dir_all().unwrap();
        src.child("pkg/interface.ac")
            .write_str(
                r#"
                theorem public {
                    true
                }
                "#,
            )
            .unwrap();
        src.child("pkg/internal.ac")
            .write_str(
                r#"
                theorem public {
                    true
                } by {
                    true
                }
                "#,
            )
            .unwrap();
        src.child("use_public.ac")
            .write_str(
                r#"
                from pkg import public

                theorem use_public {
                    public
                }
                "#,
            )
            .unwrap();

        let mut verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verify.builder.check_hashes = false;
        let verify_output = verify.run().unwrap();
        assert_eq!(
            verify_output.status,
            BuildStatus::Good,
            "verify should write dependency hashes before strict replay\n{}",
            log_text(&verify_output)
        );

        let manifest_file = manifest_for_package(&src, "");
        let manifest_before = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_before).unwrap();
        assert!(
            manifest.dependencies.contains_key("pkg"),
            "root manifest should record the imported package dependency"
        );

        src.child("pkg/interface.ac")
            .write_str(
                r#"

                theorem public {
                    true
                }
                "#,
            )
            .unwrap();

        let check_config = ProjectConfig {
            usage_mode: UsageMode::Check,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        };
        let mut check =
            Verifier::new_for_check(acornlib.path().to_path_buf(), check_config, None).unwrap();
        check.builder.check_mode = true;
        check.builder.check_hashes = false;
        check.builder.strict = true;
        let check_output = check.run().unwrap();
        assert_eq!(check_output.status, BuildStatus::Error);
        let log = log_text(&check_output);
        assert!(
            log.contains("dependency hashes in package manifests are out of date"),
            "strict check should explain the stale dependency hash\n{}",
            log
        );
        assert!(
            log.contains("acorn verify"),
            "strict check should tell users how to update dependency hashes\n{}",
            log
        );
        assert_eq!(
            std::fs::read_to_string(manifest_file.path()).unwrap(),
            manifest_before,
            "check should not rewrite manifest files"
        );
    }

    #[test]
    fn test_package_interface_exports_attribute_members_individually() {
        let (acornlib, src, _build) = setup();
        src.child("pkg").create_dir_all().unwrap();
        src.child("pkg/interface.ac")
            .write_str(
                r#"
                structure Box {
                    value: Bool
                }

                attributes Box {
                    define public(self) -> Bool {
                        true
                    }
                }

                attributes Box {
                    define also_public(self) -> Bool {
                        self.public
                    }
                }
                "#,
            )
            .unwrap();
        src.child("pkg/box.ac")
            .write_str(
                r#"
                structure Box {
                    value: Bool
                }

                attributes Box {
                    define public(self) -> Bool {
                        true
                    }

                    define private(self) -> Bool {
                        true
                    }
                }

                attributes Box {
                    define also_public(self) -> Bool {
                        self.public
                    }
                }

                theorem private_inside(x: Box) {
                    x.private
                }
                "#,
            )
            .unwrap();
        src.child("use_public.ac")
            .write_str(
                r#"
                from pkg import Box

                theorem public_outside(x: Box) {
                    x.public and x.also_public
                }
                "#,
            )
            .unwrap();
        src.child("use_private.ac")
            .write_str(
                r#"
                from pkg import Box

                theorem private_outside(x: Box) {
                    x.private
                }
                "#,
            )
            .unwrap();

        let mut package_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("pkg".to_string()),
        )
        .unwrap();
        package_verify.builder.check_hashes = false;
        let package_output = package_verify.run().unwrap();
        assert_eq!(
            package_output.status,
            BuildStatus::Good,
            "package validation should allow interface-exported attributes and ignore private ones\n{}",
            log_text(&package_output)
        );

        let mut public_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("use_public".to_string()),
        )
        .unwrap();
        public_verify.builder.check_hashes = false;
        let public_output = public_verify.run().unwrap();
        assert_eq!(
            public_output.status,
            BuildStatus::Good,
            "outside module should see attributes declared in the interface\n{}",
            log_text(&public_output)
        );

        let mut private_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("use_private".to_string()),
        )
        .unwrap();
        private_verify.builder.check_hashes = false;
        let private_output = private_verify.run().unwrap();
        assert_eq!(private_output.status, BuildStatus::Error);
        assert!(
            log_text(&private_output).contains("attribute Box.private not found"),
            "outside module should not see implementation-only attributes\n{}",
            log_text(&private_output)
        );
    }

    #[test]
    fn test_package_interface_exports_destructuring_let_bound_name() {
        let (acornlib, src, _build) = setup();
        src.child("pkg").create_dir_all().unwrap();
        src.child("pkg/interface.ac")
            .write_str(
                r#"
                inductive Option[T] {
                    none
                    some(T)
                }

                let Option.some(public_flag) = Option.some(true)

                theorem public_flag_reflexive {
                    public_flag = public_flag
                }
                "#,
            )
            .unwrap();
        src.child("pkg/internal.ac")
            .write_str(
                r#"
                inductive Option[T] {
                    none
                    some(T)
                }

                let Option.some(public_flag) = Option.some(true) by {
                    true
                }

                theorem public_flag_reflexive {
                    public_flag = public_flag
                }
                "#,
            )
            .unwrap();
        src.child("use_public.ac")
            .write_str(
                r#"
                from pkg import public_flag

                theorem use_public_flag {
                    public_flag = public_flag
                }
                "#,
            )
            .unwrap();

        let mut package_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("pkg".to_string()),
        )
        .unwrap();
        package_verify.builder.check_hashes = false;
        let package_output = package_verify.run().unwrap();
        assert_eq!(
            package_output.status,
            BuildStatus::Good,
            "package validation should allow interface-exported destructuring lets\n{}",
            log_text(&package_output)
        );

        let mut public_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("use_public".to_string()),
        )
        .unwrap();
        public_verify.builder.check_hashes = false;
        let public_output = public_verify.run().unwrap();
        assert_eq!(
            public_output.status,
            BuildStatus::Good,
            "outside module should see names bound by interface destructuring lets\n{}",
            log_text(&public_output)
        );
    }

    #[test]
    fn test_package_interface_requires_destructuring_let_implementation() {
        let (acornlib, src, _build) = setup();
        src.child("pkg").create_dir_all().unwrap();
        src.child("pkg/interface.ac")
            .write_str(
                r#"
                inductive Option[T] {
                    none
                    some(T)
                }

                let Option.some(public_flag) = Option.some(true)
                "#,
            )
            .unwrap();
        src.child("pkg/internal.ac")
            .write_str(
                r#"
                inductive Option[T] {
                    none
                    some(T)
                }
                "#,
            )
            .unwrap();

        let mut package_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("pkg".to_string()),
        )
        .unwrap();
        package_verify.builder.check_hashes = false;
        let package_output = package_verify.run().unwrap();
        assert_eq!(package_output.status, BuildStatus::Error);
        assert!(
            log_text(&package_output)
                .contains("missing implementation for interface declaration 'public_flag'"),
            "package validation should require destructuring-bound interface names\n{}",
            log_text(&package_output)
        );
    }

    #[test]
    fn test_default_verify_validates_changed_package_interfaces() {
        let (acornlib, src, _build) = setup();
        src.child("pkg").create_dir_all().unwrap();
        src.child("pkg/interface.ac")
            .write_str(
                r#"
                structure Box {
                    value: Bool
                }

                attributes Box {
                    define public(self) -> Bool {
                        true
                    }
                }
                "#,
            )
            .unwrap();
        src.child("pkg/box.ac")
            .write_str(
                r#"
                structure Box {
                    value: Bool
                }

                attributes Box {
                    define public(self) -> Bool {
                        true
                    }
                }
                "#,
            )
            .unwrap();

        let first_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        let first_output = first_verify.run().unwrap();
        assert_eq!(
            first_output.status,
            BuildStatus::Good,
            "initial default verify should populate caches\n{}",
            log_text(&first_output)
        );

        src.child("pkg/interface.ac")
            .write_str(
                r#"
                structure Box {
                    value: Bool
                }

                attributes Box {
                    define public(self) -> Bool {
                        self.value
                    }
                }
                "#,
            )
            .unwrap();

        let second_verify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        let second_output = second_verify.run().unwrap();
        assert_eq!(second_output.status, BuildStatus::Error);
        assert!(
            log_text(&second_output).contains("does not match interface declaration"),
            "default verify should validate packages affected by changed modules\n{}",
            log_text(&second_output)
        );
    }

    #[test]
    fn test_verify_parallel_cache_writes_preserve_manifest() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem foo_goal {
                    true
                }
                "#,
            )
            .unwrap();
        src.child("bar.ac")
            .write_str(
                r#"
                theorem bar_goal {
                    true
                }
                "#,
            )
            .unwrap();

        let mut initial = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        initial.builder.check_hashes = false;
        let initial_output = initial.run().unwrap();
        assert_eq!(initial_output.status, BuildStatus::Good);
        assert_eq!(initial_output.metrics.searches_success, 2);

        let manifest_file = manifest_for_package(&src, "");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let read_manifest = || {
            let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
            serde_json::from_str::<crate::manifest::PackageManifest>(&manifest_content).unwrap()
        };
        assert_eq!(read_manifest().implementation.len(), 2);

        let mut replay = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        replay.builder.check_hashes = false;
        replay.builder.check_jobs = 2;
        let replay_output = replay.run().unwrap();
        assert_eq!(replay_output.status, BuildStatus::Good);
        assert_eq!(replay_output.metrics.certs_cached, 2);
        assert_eq!(replay_output.metrics.searches_total, 0);
        assert_eq!(read_manifest().implementation.len(), 2);

        let mut skipped = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        skipped.builder.check_jobs = 2;
        let skipped_output = skipped.run().unwrap();
        assert_eq!(skipped_output.status, BuildStatus::Good);
        assert_eq!(skipped_output.metrics.modules_cached, 2);
        assert_eq!(read_manifest().implementation.len(), 2);
    }

    #[test]
    fn test_rejects_cached_certificate_unimported_lib_reference() {
        let (acornlib, src, _build) = setup();

        src.child("util.ac")
            .write_str("let contradiction: Bool = false\n")
            .unwrap();
        src.child("main.ac")
            .write_str("theorem goal { false }\n")
            .unwrap();

        let cert_path = cert_for_source(&src, "main.ac");
        save_cert_store(
            &cert_path,
            CertificateStore {
                certs: vec![cert_from_lines("goal", &["lib(util).contradiction"])],
            },
        );

        let mut verifier = Verifier::new_for_check(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_mode = true;
        verifier.builder.check_hashes = false;

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Error);
        assert_eq!(output.metrics.cert_checks_total, 1);
        assert_eq!(output.metrics.searches_total, 0);
        assert!(output.events.iter().any(|event| {
            event.log_message.as_ref().is_some_and(|message| {
                message.contains("module 'util' is not available through this module's imports")
            })
        }));
    }

    #[test]
    fn test_allows_imported_lib_reference_in_certificate_line() {
        let (_acornlib, src, build) = setup();

        src.child("util.ac")
            .write_str("let util_fact: Bool = true\n")
            .unwrap();
        src.child("main.ac")
            .write_str(
                r#"
                from util import util_fact

                theorem goal { true }
                "#,
            )
            .unwrap();

        let mut project = Project::new(
            src.path().to_path_buf(),
            build.path().to_path_buf(),
            ProjectConfig::default(),
        )
        .unwrap();
        project.add_src_targets();
        let main_id = project.get_module_id_by_name("main").unwrap();
        let mut bindings = std::borrow::Cow::Borrowed(project.get_bindings(main_id).unwrap());
        let mut kernel_context =
            std::borrow::Cow::Owned(crate::kernel::kernel_context::KernelContext::new());

        Certificate::parse_code_line(
            "lib(util).util_fact",
            &project,
            &mut bindings,
            &mut kernel_context,
        )
        .expect("strict imports should allow certificate references to imported modules");
    }

    #[test]
    fn test_verify_trims_unused_cached_cert_steps() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        let cert_path = cert_for_source(&src, "foo.ac");
        save_cert_store(
            &cert_path,
            CertificateStore {
                certs: vec![cert_from_lines("simple_truth", &["true"])],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.certs_cached, 1);
        assert_eq!(output.metrics.searches_total, 0);

        let loaded = CertificateStore::load(cert_path.path()).unwrap();
        assert_eq!(loaded.certs.len(), 1);
        assert_eq!(loaded.certs[0].goal, "simple_truth");
        assert_eq!(loaded.certs[0].proof_step_count(), 0);
    }

    #[test]
    fn test_eval_only_searches_goals_with_nonempty_cached_proofs() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem benchmark {
                    true
                }

                theorem skipped {
                    true
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![
                    cert_from_lines("benchmark", &["dummy proof step"]),
                    empty_cert("skipped"),
                ],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.eval_corpus_total, 1);
        assert_eq!(output.metrics.eval_corpus_empty, 0);
        assert_eq!(output.metrics.eval_corpus_matched, 1);
        assert_eq!(output.metrics.eval_corpus_unmatched, 0);
        assert_eq!(output.metrics.eval_goals_skipped_uncertified, 1);
        assert_eq!(output.metrics.searches_total, 1);
        assert_eq!(output.metrics.searches_success, 1);
    }

    #[test]
    fn test_eval_counts_inconsistent_search_as_success() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                type Nat: axiom
                let zero: Nat = axiom
                let foo: Nat -> Bool = axiom
                let bar: Nat -> Bool = axiom
                axiom foo_true { foo(zero) }
                axiom foo_false { not foo(zero) }
                theorem goal { bar(zero) }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("goal", &["dummy proof step"])],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.searches_total, 1);
        assert_eq!(output.metrics.searches_success, 1);
        assert_eq!(output.metrics.searches_inconsistent, 1);

        let skip0 = output
            .metrics
            .eval_skip_metrics
            .iter()
            .find(|metrics| metrics.skip == 0)
            .expect("skip=0 metrics should exist");
        assert_eq!(skip0.searches_total, 1);
        assert_eq!(skip0.searches_success, 1);
        assert_eq!(skip0.searches_inconsistent, 1);

        let info = output.metrics.info_lines().join("\n");
        assert!(info.contains("1 searches found inconsistent assumptions"));
        assert!(!info.contains("search failures"));
    }

    #[test]
    fn test_eval_writes_successful_search_trace() {
        let (acornlib, src, build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem excluded_middle(b: Bool) {
                    b = true or b = false
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("excluded_middle", &["dummy proof step"])],
            },
        );

        let trace_file = build.child("trace.jsonl.zst");
        let trace_writer =
            SearchTraceWriter::create(trace_file.path()).expect("trace writer should open");

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";
        verifier.builder.trace_writer = Some(trace_writer.clone());

        let output = verifier.run().expect("eval should run");
        trace_writer.flush().expect("trace should flush");
        assert_eq!(output.status, BuildStatus::Good);

        let metadata = std::fs::read_to_string(trace_metadata_path(trace_file.path()))
            .expect("trace metadata file should exist");
        let metadata: serde_json::Value =
            serde_json::from_str(&metadata).expect("trace metadata should be valid JSON");
        assert_eq!(metadata["schema"], "acorn-activated-step-trace-v2");
        let feature_names = metadata["feature_vector"]
            .as_array()
            .expect("feature vector names should be an array");
        assert!(
            feature_names.len() > 9,
            "trace should export the wide feature catalog"
        );

        let trace_file_reader =
            std::fs::File::open(trace_file.path()).expect("trace file should exist");
        let mut trace = String::new();
        zstd::stream::read::Decoder::new(trace_file_reader)
            .expect("zstd trace decoder should initialize")
            .read_to_string(&mut trace)
            .expect("trace file should decode as zstd JSONL");
        assert!(!trace.trim().is_empty(), "trace file should not be empty");

        let mut saw_positive = false;
        for line in trace.lines() {
            let record: serde_json::Value =
                serde_json::from_str(line).expect("trace line should be valid JSON");
            assert_eq!(record["schema"], "acorn-activated-step-trace-v2");
            assert_eq!(record["module"], "foo");
            assert_eq!(record["goal"], "excluded_middle");
            assert_eq!(
                record["goal_bucket"].as_u64(),
                Some(u64::from(goal_bucket("foo", "excluded_middle")))
            );
            assert_eq!(record["skip"], 0);
            assert_eq!(record["policy"], "model-20260705-consistent-h128-l3");
            assert!(record["activation_index"].as_u64().is_some());
            assert!(record["passive_id"].as_u64().is_some());
            assert!(record["active_id"].is_u64() || record["active_id"].is_null());
            assert!(record["feature_vector"]
                .as_array()
                .is_some_and(|values| values.len() == feature_names.len()));
            assert!(record["features"].is_null());
            saw_positive |= record["used_in_final_proof"].as_bool() == Some(true);
        }
        assert!(
            saw_positive,
            "trace should contain at least one positive label"
        );
    }

    #[test]
    fn test_eval_writes_failed_search_trace() {
        let (acornlib, src, build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                let p: Bool = axiom
                let q: Bool = axiom

                theorem wrapper {
                    p or q
                } by {
                    p
                    p or q
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("p or q", &["dummy proof step"])],
            },
        );

        let trace_file = build.child("trace-failed.jsonl.zst");
        let trace_writer =
            SearchTraceWriter::create(trace_file.path()).expect("trace writer should open");

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0, 1];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";
        verifier.builder.trace_writer = Some(trace_writer.clone());

        let output = verifier.run().expect("eval should run");
        trace_writer.flush().expect("trace should flush");
        assert_eq!(output.status, BuildStatus::Warning);
        assert_eq!(output.metrics.searches_total, 2);
        assert_eq!(output.metrics.searches_success, 1);

        let trace_file_reader =
            std::fs::File::open(trace_file.path()).expect("trace file should exist");
        let mut trace = String::new();
        zstd::stream::read::Decoder::new(trace_file_reader)
            .expect("zstd trace decoder should initialize")
            .read_to_string(&mut trace)
            .expect("trace file should decode as zstd JSONL");

        let mut failed_rows = 0;
        for line in trace.lines() {
            let record: serde_json::Value =
                serde_json::from_str(line).expect("trace line should be valid JSON");
            if record["skip"].as_u64() == Some(1) {
                failed_rows += 1;
                assert_ne!(record["outcome"].as_str(), Some("Success"));
                assert_eq!(record["used_in_final_proof"].as_bool(), Some(false));
            }
        }
        assert!(
            failed_rows > 0,
            "failed eval search should write trace rows"
        );
    }

    #[test]
    fn test_eval_sample_skips_goals_outside_bucket_filter() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem first {
                    true
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("first", &["dummy proof step"])],
            },
        );

        let excluded_bucket = goal_bucket("foo", "first");
        let included_bucket = (excluded_bucket + 1) % 100;
        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0];
        verifier.builder.eval_bucket_filter = Some(GoalBucketFilter::single(included_bucket));
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.eval_corpus_total, 0);
        assert_eq!(output.metrics.eval_goals_skipped_sample, 1);
        assert_eq!(output.metrics.eval_goals_skipped_uncertified, 0);
        assert_eq!(output.metrics.searches_total, 0);
    }

    #[test]
    fn test_line_selection_works_with_interface_module_dependency() {
        // Regression: interface-role modules are excluded from the lowered
        // module list but stayed in the sorted target list, and the proving
        // loop zipped the two lists together. Any interface dependency then
        // shifted every pairing by one, so line-targeted verification silently
        // verified nothing and reported success.
        let (acornlib, src, _build) = setup();

        src.child("pkg/interface.ac")
            .write_str("define foo_id(b: Bool) -> Bool {\n    b\n}\n")
            .unwrap();
        src.child("pkg/member.ac")
            .write_str(
                r#"
define foo_id(b: Bool) -> Bool {
    b
}

theorem member_thm(b: Bool) {
    foo_id(b) = b
}
"#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: false,
                write_cache: false,
                update_version: false,
            },
            Some("pkg.member".to_string()),
        )
        .expect("verifier should construct");
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(6));

        let output = verifier.run().expect("verify should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert!(
            output.metrics.searches_total >= 1,
            "line-targeted verification should search the selected goal, got {} searches",
            output.metrics.searches_total
        );
    }

    #[test]
    fn test_eval_line_selection_searches_only_selected_benchmark_goal() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem first {
                    true
                }

                theorem second {
                    true
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![
                    cert_from_lines("first", &["dummy proof step"]),
                    cert_from_lines("second", &["dummy proof step"]),
                ],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";
        verifier.line_selection = Some(LineSelection::Single(6));

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.eval_corpus_total, 2);
        assert_eq!(output.metrics.eval_corpus_matched, 1);
        assert_eq!(output.metrics.eval_corpus_unmatched, 1);
        assert_eq!(output.metrics.searches_total, 1);
        assert_eq!(output.metrics.searches_success, 1);
    }

    #[test]
    fn test_eval_can_search_modules_in_parallel() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem foo_goal {
                    true
                }
                "#,
            )
            .unwrap();
        src.child("bar.ac")
            .write_str(
                r#"
                theorem bar_goal {
                    true
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("foo_goal", &["dummy proof step"])],
            },
        );
        save_cert_store(
            &cert_for_source(&src, "bar.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("bar_goal", &["dummy proof step"])],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            None,
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.check_jobs = 2;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("parallel eval should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.eval_corpus_total, 2);
        assert_eq!(output.metrics.eval_corpus_matched, 2);
        assert_eq!(output.metrics.eval_corpus_unmatched, 0);
        assert_eq!(output.metrics.searches_total, 2);
        assert_eq!(output.metrics.searches_success, 2);
        assert_eq!(output.module_timings.len(), 2);
    }

    #[test]
    fn test_eval_skip_omits_previous_plain_proposition() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                let p: Bool = axiom
                let q: Bool = axiom

                theorem wrapper {
                    p or q
                } by {
                    p
                    p or q
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("p or q", &["dummy proof step"])],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0, 1];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Warning);
        assert_eq!(output.metrics.eval_corpus_total, 1);
        assert_eq!(output.metrics.eval_corpus_matched, 1);
        assert!(output.metrics.eval_goals_skipped_uncertified > 0);
        assert_eq!(output.metrics.searches_total, 2);
        assert_eq!(output.metrics.searches_success, 1);

        let skip0 = output
            .metrics
            .eval_skip_metrics
            .iter()
            .find(|metrics| metrics.skip == 0)
            .expect("skip=0 metrics should exist");
        assert_eq!(skip0.searches_total, 1);
        assert_eq!(skip0.searches_success, 1);
        assert_eq!(skip0.ineligible, 0);

        let skip1 = output
            .metrics
            .eval_skip_metrics
            .iter()
            .find(|metrics| metrics.skip == 1)
            .expect("skip=1 metrics should exist");
        assert_eq!(skip1.searches_total, 1);
        assert_eq!(skip1.searches_success, 0);
        assert_eq!(skip1.ineligible, 0);
    }

    #[test]
    fn test_eval_skip_includes_empty_cached_proofs_for_nonzero_skip() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                let p: Bool = axiom
                let q: Bool = axiom

                theorem wrapper {
                    p or q
                } by {
                    p
                    p or q
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![empty_cert("p or q")],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0, 1];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Warning);
        assert_eq!(output.metrics.eval_corpus_total, 1);
        assert_eq!(output.metrics.eval_corpus_empty, 1);
        assert_eq!(output.metrics.eval_corpus_matched, 1);
        assert_eq!(output.metrics.searches_total, 1);
        assert_eq!(output.metrics.searches_success, 0);

        let skip0 = output
            .metrics
            .eval_skip_metrics
            .iter()
            .find(|metrics| metrics.skip == 0)
            .expect("skip=0 metrics should exist");
        assert_eq!(skip0.searches_total, 0);

        let skip1 = output
            .metrics
            .eval_skip_metrics
            .iter()
            .find(|metrics| metrics.skip == 1)
            .expect("skip=1 metrics should exist");
        assert_eq!(skip1.searches_total, 1);
        assert_eq!(skip1.searches_success, 0);
        assert_eq!(skip1.ineligible, 0);
    }

    #[test]
    fn test_eval_skip_respects_non_plain_barrier() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                let p: Bool = axiom
                let q: Bool = axiom

                theorem wrapper {
                    p or q
                } by {
                    p

                    let r: Bool = axiom

                    p or q
                }
                "#,
            )
            .unwrap();

        save_cert_store(
            &cert_for_source(&src, "foo.ac"),
            CertificateStore {
                certs: vec![cert_from_lines("p or q", &["dummy proof step"])],
            },
        );

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig {
                usage_mode: UsageMode::Verify,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
            Some("foo".to_string()),
        )
        .expect("eval verifier should construct");
        verifier.builder.eval_mode = true;
        verifier.builder.eval_skip_modes = vec![0, 1];
        verifier.builder.force_search = true;
        verifier.builder.check_hashes = false;
        verifier.builder.operation_verb = "proved";

        let output = verifier.run().expect("eval should run");
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.searches_total, 1);
        assert_eq!(output.metrics.searches_success, 1);

        let skip1 = output
            .metrics
            .eval_skip_metrics
            .iter()
            .find(|metrics| metrics.skip == 1)
            .expect("skip=1 metrics should exist");
        assert_eq!(skip1.searches_total, 0);
        assert_eq!(skip1.ineligible, 1);
    }

    #[test]
    fn test_read_only_check_does_not_trim_cached_cert_steps() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        let cert_path = cert_for_source(&src, "foo.ac");
        save_cert_store(
            &cert_path,
            CertificateStore {
                certs: vec![cert_from_lines("simple_truth", &["true"])],
            },
        );
        let original = std::fs::read_to_string(cert_path.path()).unwrap();

        let config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        };
        let mut verifier = Verifier::new(acornlib.path().to_path_buf(), config, None).unwrap();
        verifier.builder.check_hashes = false;
        verifier.builder.check_mode = true;

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.certs_cached, 1);
        assert_eq!(output.metrics.searches_total, 0);

        let after = std::fs::read_to_string(cert_path.path()).unwrap();
        assert_eq!(after, original);

        let loaded = CertificateStore::load(cert_path.path()).unwrap();
        assert_eq!(loaded.certs.len(), 1);
        assert_eq!(loaded.certs[0].goal, "simple_truth");
        assert_eq!(loaded.certs[0].proof_step_count(), 1);
    }

    #[test]
    fn test_verify_relative_src_path_uses_canonical_module_cache() {
        let (acornlib, src, _build) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("src/foo.ac".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;

        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);
        assert_eq!(output1.metrics.certs_cached, 0);
        assert_eq!(output1.metrics.searches_total, 1);

        assert!(
            cert_for_source(&src, "foo.ac").exists(),
            "relative src/ path should write the canonical certificate file"
        );

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;

        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(output2.metrics.certs_cached, 1);
        assert_eq!(output2.metrics.searches_total, 0);
    }

    #[test]
    fn test_single_line_goal_index_selects_specific_goal() {
        let (acornlib, src, _build) = setup();

        src.child("test.ac")
            .write_str(
                r#"type Nat: axiom
typeclass T: Two {
    first(x: T) { true }
    second(x: T) { true }
}
instance Nat: Two
"#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("test".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(6));
        verifier.goal_index = Some(2);

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 2);
        assert_eq!(output.metrics.goals_success, 2);
    }

    #[test]
    fn test_single_line_goal_index_out_of_range_is_error() {
        let (acornlib, src, _build) = setup();

        src.child("test.ac")
            .write_str(
                r#"type Nat: axiom
typeclass T: Two {
    first(x: T) { true }
    second(x: T) { true }
}
instance Nat: Two
"#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("test".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(6));
        verifier.goal_index = Some(3);

        let error = verifier.run().unwrap_err();
        assert!(error.contains("out of range"));
    }

    #[test]
    fn test_single_line_verification_accepts_relative_file_target() {
        let (acornlib, src, _build) = setup();

        src.child("test.ac")
            .write_str(
                r#"
                theorem first {
                    true
                }

                theorem second {
                    true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("src/test.ac".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(6));

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 2);
        assert_eq!(output.metrics.goals_success, 2);
    }

    #[test]
    fn test_single_line_verification_accepts_relative_stdin_append_file_target() {
        let (acornlib, src, _build) = setup();

        let nested = src.child("nested");
        nested.create_dir_all().unwrap();
        nested
            .child("test.ac")
            .write_str(
                r#"
                theorem first {
                    true
                }

                theorem second {
                    true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new_for_test(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("-:src/nested/test.ac".to_string()),
            Some(""),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(6));

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 2);
        assert_eq!(output.metrics.goals_success, 2);
        assert_eq!(output.metrics.searches_total, 2);
        assert!(!cert_for_source(&src, "nested/test.ac").exists());
    }

    #[test]
    fn test_single_line_verifies_prior_witness_obligation() {
        let (acornlib, src, _build) = setup();

        src.child("test.ac")
            .write_str(
                r#"
                type Empty: axiom

                let x: Empty satisfy {
                    true
                }

                theorem bad {
                    x = x
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("test".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(8));

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Warning);
        assert!(output.metrics.goals_success < output.metrics.goals_done);
    }

    #[test]
    fn test_single_line_verifies_prior_theorem() {
        let (acornlib, src, _build) = setup();

        src.child("test.ac")
            .write_str(
                r#"let p: Bool = axiom

theorem bad {
    p
}

theorem later {
    p
}
"#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("test".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(7));

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Warning);
        assert_eq!(output.metrics.goals_total, 2);
        assert_eq!(output.metrics.goals_done, 2);
        assert_eq!(output.metrics.goals_success, 1);
    }

    #[test]
    fn test_line_range_verifies_prior_theorem() {
        let (acornlib, src, _build) = setup();

        src.child("test.ac")
            .write_str(
                r#"let p: Bool = axiom

theorem bad {
    p
}

theorem later {
    p
}
"#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("test".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Range(7, 9));

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Warning);
        assert_eq!(output.metrics.goals_total, 2);
        assert_eq!(output.metrics.goals_done, 2);
        assert_eq!(output.metrics.goals_success, 1);
    }

    #[test]
    fn test_single_line_does_not_assume_unverified_imported_theorem() {
        let (acornlib, src, _build) = setup();

        src.child("a.ac")
            .write_str(
                r#"let p: Bool = axiom

theorem bad {
    p
}
"#,
            )
            .unwrap();
        src.child("b.ac")
            .write_str(
                r#"from a import bad

theorem later {
    bad and true
}
"#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("b".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.line_selection = Some(LineSelection::Single(3));

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Warning);
        assert_eq!(output.metrics.goals_total, 1);
        assert_eq!(output.metrics.goals_done, 1);
        assert_eq!(output.metrics.goals_success, 0);
    }

    #[test]
    fn test_verifier_stdin_append_target_uses_resolved_cache_path() {
        let (acornlib, src, _build) = setup();

        let nested = src.child("nested");
        nested.create_dir_all().unwrap();
        nested
            .child("test.ac")
            .write_str(
                r#"
                theorem first {
                    true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new_for_test(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("-:src/nested/test.ac".to_string()),
            Some(""),
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1);
        assert_eq!(output.metrics.goals_success, 1);
        assert!(
            cert_for_source(&src, "nested/test.ac").exists(),
            "src/nested/certs/test.jsonl should exist"
        );
    }

    #[cfg(feature = "validate")]
    #[test]
    fn test_validate_handles_exists_conjunction_in_generated_cert() {
        let (acornlib, src, _build) = setup();

        let bug_ac = src.child("bug.ac");
        bug_ac
            .write_str(
                r#"
                type Foo: axiom
                let f: Foo -> Bool = axiom
                let g: Foo -> Bool = axiom
                let h1: (Foo, Foo) -> Bool = axiom
                let h2: (Foo, Foo) -> Bool = axiom

                axiom axiom1(x: Foo) {
                    f(x) implies g(x)
                }

                axiom axiom2(x: Foo) {
                    g(x) implies exists(y: Foo, z: Foo) { h1(x, y) and h2(y, z) }
                }

                theorem goal(a: Foo) {
                    f(a) implies exists(y: Foo, z: Foo) { h1(a, y) and h2(y, z) }
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("bug".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        let output = verifier.run().expect(
            "validate verify should not panic/check-cert-fail on exists conjunction certificates",
        );
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[cfg(feature = "validate")]
    #[test]
    fn test_validate_handles_is_constant_goal_with_explicit_witness() {
        let (acornlib, src, _build) = setup();

        let bug_ac = src.child("bug.ac");
        bug_ac
            .write_str(
                r#"
                define is_constant[T, U](f: T -> U) -> Bool {
                    exists(y: U) {
                        forall(x: T) {
                            f(x) = y
                        }
                    }
                }

                type Foo: axiom
                type Bar: axiom
                let g: Foo -> Bar = axiom
                let y: Bar = axiom

                axiom g_is_y(x: Foo) {
                    g(x) = y
                }

                theorem goal {
                    is_constant(g)
                } by {
                    forall(x: Foo) {
                        g(x) = y
                    }
                    exists(y0: Bar) {
                        forall(x: Foo) {
                            g(x) = y0
                        }
                    }
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("bug".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        let output = verifier
            .run()
            .expect("validate verify should not panic/check-cert-fail on is_constant certificates");
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[test]
    fn test_verify_basic_induction() {
        use crate::processor::Processor;
        use crate::prover::{Outcome, ProverMode};

        let (mut processor, _bindings, normalized_goal) = Processor::test_goal(
            r#"
            inductive Nat {
                zero
                suc(Nat)
            }

            let p: Nat -> Bool = axiom

            axiom base {
                p(Nat.zero)
            }

            axiom step(x: Nat) {
                p(x) implies p(x.suc)
            }

            theorem goal(n: Nat) {
                p(n)
            }
            "#,
        );

        let outcome = processor.search(ProverMode::Test, &normalized_goal.kernel_context);
        let expected = Outcome::Success;
        assert_eq!(outcome, expected);
    }

    #[test]
    fn test_verifier_uses_nested_cache() {
        let (acornlib, src, build) = setup();

        // Create a nested directory structure
        let foo_dir = src.child("foo");
        foo_dir.create_dir_all().unwrap();

        // Create a file at foo/bar.ac with one theorem
        let bar_ac = foo_dir.child("bar.ac");
        bar_ac
            .write_str(
                r#"
                theorem nested_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier for all modules to test certificate caching
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;

        // Run the verifier the first time
        let result = verifier1.run();
        assert!(
            result.is_ok(),
            "First verifier run should succeed: {:?}",
            result
        );

        // Check that we actually proved something
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(output.metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(output.metrics.searches_total > 0); // Should have performed at least one search

        // With certificates enabled, we should NOT create YAML files
        let build_file = build.child("foo").child("bar.yaml");
        assert!(
            !build_file.exists(),
            "YAML cache file should NOT exist when using certificates"
        );

        // Check that we created a JSONL file for certificates in the nested directory
        let cert_file = cert_for_source(&src, "foo/bar.ac");
        assert!(
            cert_file.exists(),
            "Certificate file should exist at src/foo/certs/bar.jsonl"
        );

        assert!(manifest_for_package(&src, "").exists());

        // Verify again (all modules)
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let result2 = verifier2.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
    }

    #[test]
    fn test_verifier_filter_picks_up_imported_extends() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property[B: Bar] {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }
        "#,
            )
            .unwrap();

        src.child("main.ac")
            .write_str(
                r#"
            from foo import Baz

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property[B: Baz] {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output = verifier1.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[test]
    fn test_verifier_filter_picks_up_local_extends() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property[B: Bar] {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property[B: Baz] {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output = verifier1.run().unwrap();
        assert_eq!(output.num_verified(), 5);

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good,);
        assert_eq!(output.num_verified(), 5);
    }

    #[test]
    fn test_verifier_fails_on_circular_import() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac")
            .write_str("from bar import Bar")
            .unwrap();
        src.child("bar.ac")
            .write_str("from foo import Foo")
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        let result = verifier.run();

        let Err(err) = result else {
            panic!("Verifier::run should fail on circular import");
        };

        assert!(
            err.contains("circular"),
            "Expected circular import error, got: {}",
            err
        );

        if err.lines().map(|l| l.contains("^^^^^")).count() != 1 {
            panic!(
                "Expected exactly one ^^^^^^ line in the error message, got:\n{}",
                err
            );
        }
    }

    #[test]
    fn test_module_skipping() {
        let (acornlib, src, _build) = setup();

        // Create foo.ac with a theorem
        src.child("foo.ac")
            .write_str(
                r#"
                let thing: Bool = axiom
                theorem foo_goal {
                    thing = thing
                }
                "#,
            )
            .unwrap();

        let config = ProjectConfig::default();

        // First build with all modules (just foo.ac for now)
        let verifier1 = Verifier::new(acornlib.path().to_path_buf(), config.clone(), None).unwrap();
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);
        assert_eq!(output1.metrics.modules_total, 1);
        assert_eq!(output1.metrics.modules_cached, 0);

        // Check that manifest was created after first run
        let manifest = manifest_for_package(&src, "");
        assert!(
            manifest.exists(),
            "manifest.json should exist after first build"
        );

        src.child("bar.ac")
            .write_str(
                r#"
                from foo import thing
                theorem bar_goal {
                    thing = thing
                }
                "#,
            )
            .unwrap();

        // Second build with both modules - foo should be cached
        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            None, // Build all modules
        )
        .unwrap();
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(output2.metrics.modules_total, 2);

        assert_eq!(
            output2.metrics.modules_cached, 1,
            "foo module should have been cached"
        );
    }

    #[test]
    fn test_unchanged_jsonl_not_rewritten() {
        let (acornlib, src, _build) = setup();

        // Create foo.ac with a theorem
        src.child("foo.ac")
            .write_str(
                r#"
                let thing: Bool = axiom
                theorem foo_goal {
                    thing = thing
                }
                "#,
            )
            .unwrap();

        let config = ProjectConfig::default();

        // First build with all modules (just foo.ac for now)
        let verifier1 = Verifier::new(acornlib.path().to_path_buf(), config.clone(), None).unwrap();
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Get the modification time of the foo.jsonl file
        let foo_jsonl = cert_for_source(&src, "foo.ac");
        assert!(
            foo_jsonl.exists(),
            "foo.jsonl should exist after first build"
        );
        let metadata1 = std::fs::metadata(foo_jsonl.path()).unwrap();
        let modified1 = metadata1.modified().unwrap();

        // Sleep briefly to ensure filesystem timestamp granularity
        std::thread::sleep(std::time::Duration::from_millis(10));

        // Now add bar.ac that depends on foo.ac
        src.child("bar.ac")
            .write_str(
                r#"
                from foo import thing
                theorem bar_goal {
                    thing = thing
                }
                "#,
            )
            .unwrap();

        // Second build with both modules - foo should be cached
        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            None, // Build all modules
        )
        .unwrap();
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(
            output2.metrics.modules_cached, 1,
            "foo module should have been cached"
        );

        // Check that foo.jsonl was NOT rewritten (modification time unchanged)
        let metadata2 = std::fs::metadata(foo_jsonl.path()).unwrap();
        let modified2 = metadata2.modified().unwrap();
        assert_eq!(
            modified1, modified2,
            "foo.jsonl should not have been rewritten for unchanged module"
        );

        // Check that bar.jsonl was created
        let bar_jsonl = cert_for_source(&src, "bar.ac");
        assert!(
            bar_jsonl.exists(),
            "bar.jsonl should exist after second build"
        );
    }

    #[test]
    fn test_verifier_concrete_scoped_constants() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
        inductive Nat {
            0
            suc(Nat)
        }
        attributes Nat {
            define add(self, other: Nat) -> Nat {
                match other {
                    Nat.0 {
                        self
                    }
                    Nat.suc(pred) {
                        self.add(pred).suc
                    }
                }
            }
        }

        numerals Nat

        theorem goal(a: Nat) {
            a + 0 = a
        }
        "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output = verifier1.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[test]
    fn test_manifest_preserved_when_verifying_single_module() {
        let (acornlib, src, _build) = setup();

        // Create two modules
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem a_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem b_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        // Phase 1: Verify all modules - manifest should have two entries
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check manifest has two entries
        let manifest_file = manifest_for_package(&src, "");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.implementation.len(),
            2,
            "manifest should have 2 entries after verifying both modules"
        );

        // Phase 2: Verify only module_a - manifest should STILL have two entries
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("module_a".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        // Check manifest STILL has two entries (this is the bug - it will only have one)
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.implementation.len(),
            2,
            "BUG: manifest should still have 2 entries after verifying only module_a, but other entries were deleted"
        );
    }

    #[test]
    fn test_manifest_preserved_when_reproving_single_module() {
        // This test mimics the `reprove <module> --save-results` command behavior.
        // The key difference from verify is: read_cache: false, write_cache: true
        let (acornlib, src, _build) = setup();

        // Create two modules
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem a_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem b_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        // Phase 1: Verify all modules normally - manifest should have two entries
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check manifest has two entries
        let manifest_file = manifest_for_package(&src, "");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.implementation.len(),
            2,
            "manifest should have 2 entries after verifying both modules"
        );

        // Phase 2: Reprove only module_a with reprove-style config (read_cache: false, write_cache: true)
        // This is what `reprove module_a --save-results` does
        let reprove_config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: false,
            write_cache: true,
            update_version: false,
        };
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("module_a".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        // Check manifest STILL has two entries
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.implementation.len(),
            2,
            "manifest should still have 2 entries after reproving only module_a"
        );
    }

    #[test]
    fn test_reprove_default_file_writes_ordinary_cache_path() {
        let (acornlib, src, build) = setup();

        src.child("rat").create_dir_all().unwrap();
        src.child("rat")
            .child("default.ac")
            .write_str(
                r#"
                theorem t {
                    true
                }
                "#,
            )
            .unwrap();

        let reprove_config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: false,
            write_cache: true,
            update_version: false,
        };
        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("rat.default".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.builder.check_mode = false;
        verifier.builder.operation_verb = "reproved";
        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);

        assert!(
            cert_for_source(&src, "rat/default.ac").exists(),
            "cache file should be written for rat/default.ac"
        );
        assert!(
            !build.child("rat.jsonl").exists(),
            "default.ac should not be treated as the parent module cache"
        );

        let mut check = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        check.builder.check_mode = true;
        check.builder.check_hashes = false;
        let check_output = check.run().unwrap();
        assert_eq!(check_output.status, BuildStatus::Good);
    }

    #[test]
    fn test_reprove_single_line_nested_match_goal_generates_checkable_cert() {
        let (acornlib, src, _) = setup();

        let module_text = r#"
inductive Nat {
    zero
    suc(Nat)
}

inductive Int {
    from_nat(Nat)
    neg_suc(Nat)
}

define neg_nat(n: Nat) -> Int {
    match n {
        Nat.zero {
            Int.from_nat(Nat.zero)
        }
        Nat.suc(k) {
            Int.neg_suc(k)
        }
    }
}

define neg(a: Int) -> Int {
    match a {
        Int.from_nat(n) {
            neg_nat(n)
        }
        Int.neg_suc(n) {
            Int.from_nat(Nat.suc(n))
        }
    }
}

theorem fix_neg(a: Int) {
    neg(a) = a implies a = Int.from_nat(Nat.zero)
} by {
    if neg(a) = a {
        match a {
            Int.from_nat(n) {
                n = Nat.zero
                a = Int.from_nat(Nat.zero)
            }
            Int.neg_suc(n) {
            }
        }
    }
}
"#;
        src.child("test.ac").write_str(module_text).unwrap();

        let claim_line = module_text
            .lines()
            .position(|line| line.contains("n = Nat.zero"))
            .expect("claim line should exist") as u32
            + 1;

        let reprove_config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: false,
            write_cache: false,
            update_version: false,
        };
        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("test".to_string()),
        )
        .expect("single-line reprove verifier should construct");
        verifier.builder.check_hashes = false;
        verifier.builder.print_proof = true;
        verifier.builder.operation_verb = "reproved";
        verifier.line_selection = Some(LineSelection::Single(claim_line));

        let output = verifier
            .run()
            .expect("single-line reprove should not panic or fail cert checking");
        assert_eq!(output.status, BuildStatus::Good);
    }

    /// Focused reproducer for `reprove real.abs_conv --line 1255`.
    ///
    /// The essential shape is:
    /// - a local `define p(n)` inside a proof
    /// - `p` closes over an outer higher-order parameter `s: Nat -> Container`
    /// - `p(n)` expands to an implication whose consequent is an existential
    /// - the proof of `p(Nat.zero)` comes from resolving that definition with
    ///   a prior `forall(big_n) { set_lower_bound(s(big_n), Nat.zero) }`
    ///
    /// This should generate a checkable certificate.
    #[test]
    fn test_reprove_single_line_local_define_exists_simplification_generates_checkable_cert() {
        let (acornlib, src, _) = setup();

        let module_text = r#"
inductive Nat {
    zero
    suc(Nat)
}

structure Container {
    member: Nat -> Bool
}

let gte: (Nat, Nat) -> Bool = axiom

axiom nat_zero_lower_bound(k: Nat) {
    gte(k, Nat.zero)
}

define set_lower_bound(c: Container, n: Nat) -> Bool {
    forall(k: Nat) {
        c.member(k) implies gte(k, n)
    }
}

theorem goal(s: Nat -> Container, h: Bool) {
    h implies exists(big_n: Nat) {
        set_lower_bound(s(big_n), Nat.zero)
    }
} by {
    define p(n: Nat) -> Bool {
        h implies exists(big_n: Nat) {
            set_lower_bound(s(big_n), n)
        }
    }

    forall(big_n: Nat) {
        forall(k: Nat) {
            if s(big_n).member(k) {
                nat_zero_lower_bound(k)
            }
        }
        set_lower_bound(s(big_n), Nat.zero)
    }
    p(Nat.zero)
}
"#;
        src.child("test.ac").write_str(module_text).unwrap();

        let claim_line = module_text
            .lines()
            .position(|line| line.contains("p(Nat.zero)"))
            .expect("claim line should exist") as u32
            + 1;

        let reprove_config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: false,
            write_cache: false,
            update_version: false,
        };
        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("test".to_string()),
        )
        .expect("single-line reprove verifier should construct");
        verifier.builder.check_hashes = false;
        verifier.builder.print_proof = true;
        verifier.builder.operation_verb = "reproved";
        verifier.line_selection = Some(LineSelection::Single(claim_line));

        let output = verifier
            .run()
            .expect("single-line reprove should not panic or fail cert checking");
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[test]
    fn test_check_replays_typeclass_equal_type_lambda_certificate() {
        let (acornlib, src, _) = setup();

        src.child("bug.ac")
            .write_str(
                r#"
typeclass T: TcB {
    op: T -> T -> T
}

define preserves_op[Y: TcB, Z: TcB](f: Y -> Z) -> Bool {
    forall(y1: Y, y2: Y) {
        f(Y.op(y1, y2)) = Z.op(f(y1), f(y2))
    }
}

theorem identity_lambda_preserves_op[Y: TcB] {
    preserves_op[Y, Y](function(y: Y) { y })
} by {
    forall(y1: Y, y2: Y) {
        function(y: Y) { y }(Y.op(y1, y2)) = Y.op(y1, y2)
        function(y: Y) { y }(y1) = y1
        function(y: Y) { y }(y2) = y2
    }
}
"#,
            )
            .unwrap();

        let reprove_config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: false,
            write_cache: true,
            update_version: false,
        };
        let mut reprove = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("bug".to_string()),
        )
        .expect("reprove verifier should construct");
        reprove.builder.check_hashes = false;
        reprove.builder.operation_verb = "reproved";

        let output = reprove
            .run()
            .expect("initial reprove should create a certificate");
        assert_eq!(output.status, BuildStatus::Good);

        let check_config = ProjectConfig {
            usage_mode: UsageMode::Check,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        };
        let mut check = Verifier::new(
            acornlib.path().to_path_buf(),
            check_config,
            Some("bug".to_string()),
        )
        .expect("check verifier should construct");
        check.builder.check_hashes = false;
        check.builder.check_mode = true;
        check.builder.operation_verb = "checked";

        let output = check
            .run()
            .expect("check should replay the generated certificate");
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[test]
    fn test_deleted_module_removed_from_manifest_on_full_verify() {
        let (acornlib, src, _build) = setup();

        // Create two modules
        let module_a = src.child("module_a.ac");
        module_a
            .write_str(
                r#"
                type Nat: axiom
                theorem a_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        let module_b = src.child("module_b.ac");
        module_b
            .write_str(
                r#"
                type Nat: axiom
                theorem b_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        // Phase 1: Verify all modules - manifest should have two entries
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check manifest has two entries
        let manifest_file = manifest_for_package(&src, "");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.implementation.len(),
            2,
            "manifest should have 2 entries after verifying both modules"
        );

        // Phase 2: Delete module_b
        std::fs::remove_file(module_b.path()).unwrap();

        // Phase 3: Run full verify again - manifest should now only have one entry
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        // Check manifest now only has one entry (module_b should be removed)
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::PackageManifest =
            serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.implementation.len(),
            1,
            "manifest should have only 1 entry after deleting module_b and running full verify"
        );

        // Verify the remaining entry is module_a
        assert!(
            manifest.implementation.contains_key("module_a.ac"),
            "manifest should still contain module_a"
        );
    }

    #[test]
    fn test_global_certificate_preservation_across_modules() {
        let (acornlib, src, _build) = setup();

        // Phase 1: Initial build - both modules verify successfully
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem a_theorem_1(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem b_theorem_1(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check initial certificates: both modules should have 1 cert each
        let cert_a = cert_for_source(&src, "module_a.ac");
        let cert_b = cert_for_source(&src, "module_b.ac");
        assert!(cert_a.exists(), "module_a.jsonl should exist");
        assert!(cert_b.exists(), "module_b.jsonl should exist");

        let cert_a_content = std::fs::read_to_string(cert_a.path()).unwrap();
        let cert_b_content = std::fs::read_to_string(cert_b.path()).unwrap();
        assert_eq!(
            cert_a_content.lines().count(),
            1,
            "module_a should have 1 cert"
        );
        assert_eq!(
            cert_b_content.lines().count(),
            1,
            "module_b should have 1 cert"
        );

        // Phase 2: Mixed build - module A renames its theorem, module B adds bad theorem
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem a_theorem_renamed(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem b_theorem_1(x: Nat) {
                    x = x
                }

                theorem b_bad_theorem(x: Nat, y: Nat) {
                    x = y
                }
                "#,
            )
            .unwrap();

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        // Build should have warnings (module_b has unverified theorem)
        assert_eq!(output2.status, BuildStatus::Warning);

        // Check certificates after mixed build:
        // Module A should have 2 certs (new cert for a_theorem_renamed + old cert for a_theorem_1 preserved due to global warning)
        // Module B should have 1 cert (only the old cert, new theorem didn't verify)
        let cert_a_content = std::fs::read_to_string(cert_a.path()).unwrap();
        let cert_b_content = std::fs::read_to_string(cert_b.path()).unwrap();
        assert_eq!(
            cert_a_content.lines().count(),
            2,
            "module_a should have 2 certs (a_theorem_renamed + old a_theorem_1 preserved due to global warning)"
        );
        assert_eq!(
            cert_b_content.lines().count(),
            1,
            "module_b should still have 1 cert (only the old one)"
        );

        // Phase 3: Clean build - fix module B so it verifies
        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem b_theorem_1(x: Nat) {
                    x = x
                }

                theorem b_theorem_2(x: Nat, y: Nat) {
                    y = y
                }
                "#,
            )
            .unwrap();

        let mut verifier3 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier3.builder.check_hashes = false;
        let output3 = verifier3.run().unwrap();
        // Build should be good now
        assert_eq!(output3.status, BuildStatus::Good);

        // Check certificates after clean build:
        // Module A should have only its current cert (old a_theorem_1 cert flushed)
        // Module B should have both its certs
        let cert_a_content = std::fs::read_to_string(cert_a.path()).unwrap();
        let cert_b_content = std::fs::read_to_string(cert_b.path()).unwrap();
        assert_eq!(
            cert_a_content.lines().count(),
            1,
            "module_a should have 1 cert (only a_theorem_renamed, old a_theorem_1 flushed)"
        );
        assert_eq!(
            cert_b_content.lines().count(),
            2,
            "module_b should have 2 certs (b_theorem_1 and b_theorem_2)"
        );
    }

    #[test]
    fn test_verifier_function_satisfy() {
        let (acornlib, src, _) = setup();

        // Create a file with a function satisfy and prove it works correctly
        src.child("main.ac")
            .write_str(
                r#"
                // Define an identity function using function satisfy
                let identity(x: Bool) -> r: Bool satisfy {
                    r = x
                }

                // Prove that identity returns its input
                theorem identity_true {
                    identity(true) = true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify function satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(output.metrics.goals_success >= 1);
    }

    #[test]
    fn test_verifier_polymorphic_variable_satisfy() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
                typeclass Z: Zero {
                    0: Z
                }

                let zero1[Z: Zero]: Z satisfy {
                    zero1 = Z.0
                }

                let zero2[Z: Zero]: Z satisfy {
                    zero2 = Z.0
                }

                theorem goal[Z: Zero] {
                    zero1[Z] = zero2[Z]
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully elaborate polymorphic variable satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert!(
            output.status == BuildStatus::Good,
            "Expected Good status, got {:?}",
            output.status
        );
    }

    #[test]
    fn test_verifier_polymorphic_function_satisfy() {
        let (acornlib, src, _) = setup();

        // Test polymorphic function satisfy with a theorem proving it works
        src.child("main.ac")
            .write_str(
                r#"
                // Define a polymorphic identity function using function satisfy
                let identity[T](x: T) -> r: T satisfy {
                    r = x
                }

                // Prove that identity returns its input
                theorem identity_true {
                    identity[Bool](true) = true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify polymorphic function satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(output.metrics.goals_success >= 1);
    }

    #[test]
    fn test_verifier_dependent_function_satisfy() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
                type Nat: axiom

                structure Fin[n: Nat] {
                    value: Nat
                }

                let choose_self(n: Nat, x: Fin[n]) -> result: Fin[n] satisfy {
                    result = x
                }

                theorem goal(n: Nat, x: Fin[n]) {
                    choose_self(n, x) = x
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify dependent function satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(output.metrics.goals_success >= 1);
    }

    #[test]
    fn test_verifier_constrained_dependent_function_satisfy() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
                type Nat: axiom
                let lt: (Nat, Nat) -> Bool = axiom

                structure Fin[n: Nat] {
                    value: Nat
                } constraint {
                    lt(value, n)
                }

                let choose_self(n: Nat, x: Fin[n]) -> result: Fin[n] satisfy {
                    result = x
                }

                theorem goal(n: Nat, x: Fin[n]) {
                    choose_self(n, x) = x
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify constrained dependent function satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(output.metrics.goals_success >= 1);
    }
}
