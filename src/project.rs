use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::{fmt, io};

use regex::Regex;
use tower_lsp::lsp_types::{CompletionItem, Hover, HoverContents, MarkedString, Url};
use walkdir::WalkDir;

use crate::acorn_type::{AcornType, Datatype, Typeclass};
use crate::acorn_value::AcornValue;
use crate::binding_map::BindingMap;
use crate::block::{Node, NodeCursor};
use crate::build_cache::BuildCache;
use crate::builder::{BuildEvent, BuildStatus, Builder};
use crate::code_generator::{self, CodeGenerator};
use crate::compilation;
use crate::environment::Environment;
use crate::fact::Fact;
use crate::goal::GoalContext;
use crate::module::{LoadState, Module, ModuleDescriptor, ModuleId};
use crate::module_cache::{ModuleCache, ModuleHash};
use crate::named_entity::NamedEntity;
use crate::names::ConstantName;
use crate::prover::{Outcome, Prover};
use crate::token::Token;
use crate::token_map::TokenInfo;
use crate::verifier::ProverMode;

// The Project is responsible for importing different files and assigning them module ids.
pub struct Project {
    // The root directory of the library.
    // This is used to resolve all imports.
    // Note that it may be different from the editor root, which is where the user is working.
    // Set to "/mock" for mock projects.
    library_root: PathBuf,

    // Whether we permit loading files from the filesystem
    use_filesystem: bool,

    // For "open" files, we use the content we are storing rather than the content on disk.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress whose state is "owned" by an IDE via the language server protocol.
    //
    // Maps filename -> (contents, version number).
    // The version number can mean whatever the caller wants it to mean.
    // From vscode, it'll be the vscode version number.
    open_files: HashMap<PathBuf, (String, i32)>,

    // modules[module_id] is the (ref, Module, hash) for the given module id.
    // Built-in modules have no name.
    modules: Vec<Module>,

    // module_map maps from a module's descriptor to its id
    module_map: HashMap<ModuleDescriptor, ModuleId>,

    // The module names that we want to build.
    targets: HashSet<ModuleDescriptor>,

    // The cache contains a hash for each module from the last time it was cleanly built.
    pub build_cache: BuildCache,

    // Used as a flag to stop a build in progress.
    pub build_stopped: Arc<AtomicBool>,

    // Whether we skip goals that match hashes in the cache.
    // Defaults to true.
    pub check_hashes: bool,

    // Whether to check concrete proofs.
    // Defaults to false.
    pub check_concrete: bool,
}

// General project-level errors (file operations, setup, etc.)
#[derive(Debug)]
pub struct ProjectError(pub String);

impl From<io::Error> for ProjectError {
    fn from(error: io::Error) -> Self {
        ProjectError(format!("{}", error))
    }
}

impl fmt::Display for ProjectError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Errors specific to importing modules.
// Each string is a human-readable error message.
#[derive(Debug)]
pub enum ImportError {
    // The module file doesn't exist (e.g., typo in import statement)
    NotFound(String),

    // There's a circular dependency.
    // The module id is the module that the error occurs in, not the one we're trying to import.
    Circular(ModuleId),
}

impl From<io::Error> for ImportError {
    fn from(error: io::Error) -> Self {
        ImportError::NotFound(format!("{}", error))
    }
}

impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ImportError::NotFound(message) => write!(f, "{}", message),
            ImportError::Circular(module_id) => {
                write!(f, "circular import of module {}", module_id)
            }
        }
    }
}

fn check_valid_module_part(s: &str, error_name: &str) -> Result<(), ImportError> {
    if s.is_empty() {
        return Err(ImportError::NotFound(format!(
            "empty module part: {}",
            error_name
        )));
    }
    if !s.chars().next().unwrap().is_ascii_lowercase() {
        return Err(ImportError::NotFound(format!(
            "module parts must start with a lowercase letter: {}",
            error_name
        )));
    }
    for char in s.chars() {
        if !char.is_ascii_alphanumeric() && char != '_' {
            return Err(ImportError::NotFound(format!(
                "invalid character in module name: '{}' in {}",
                char, error_name
            )));
        }
    }
    Ok(())
}

impl Project {
    // Create a new project.
    // Flags control whether we read the cache, and whether we write the cache.
    pub fn new(
        library_root: PathBuf,
        cache_dir: PathBuf,
        read_cache: bool,
        write_cache: bool,
    ) -> Project {
        // Check if the directory exists
        let build_cache = if read_cache && cache_dir.is_dir() {
            BuildCache::new(Some(cache_dir), write_cache)
        } else {
            BuildCache::new(None, false)
        };

        Project {
            library_root,
            use_filesystem: true,
            open_files: HashMap::new(),
            modules: vec![],
            module_map: HashMap::new(),
            targets: HashSet::new(),
            build_cache,
            build_stopped: Arc::new(AtomicBool::new(false)),
            check_hashes: true,
            check_concrete: false,
        }
    }

    // Finds an acorn library directory, based on the provided path.
    // It can be either:
    //   - a parent directory named "acornlib"
    //   - a parent directory containing "acorn.toml"
    //   - a directory named "acornlib" next to one named "acorn"
    // Returns (library_root, cache_dir) where:
    //   - For new format (with acorn.toml): library_root is src/, cache_dir is build/
    //   - For old format: library_root is acornlib/, cache_dir is acornlib/build/
    pub fn find_local_acorn_library(start: &Path) -> Option<(PathBuf, PathBuf)> {
        let mut current = Some(start);

        while let Some(path) = current {
            // Check if path is an acornlib directory
            if path.ends_with("acornlib") {
                return Self::check_acornlib_layout(path);
            }

            // Check if path contains acorn.toml (new format)
            if path.join("acorn.toml").is_file() {
                return Self::check_acornlib_layout(path);
            }

            // Check if path has a sibling named acornlib (only if current dir is "acorn")
            if path.ends_with("acorn") {
                let library_path = path.with_file_name("acornlib");
                if library_path.is_dir() {
                    return Self::check_acornlib_layout(&library_path);
                }
            }

            current = path.parent();
        }

        None
    }

    // Helper function to check if an acornlib directory uses the new format
    // with acorn.toml and src directory. If so, returns (src_dir, build_dir).
    // Otherwise, returns (acornlib_dir, build_dir_within_acornlib).
    fn check_acornlib_layout(acornlib_path: &Path) -> Option<(PathBuf, PathBuf)> {
        let acorn_toml = acornlib_path.join("acorn.toml");
        let src_dir = acornlib_path.join("src");

        if acorn_toml.is_file() && src_dir.is_dir() {
            // New format: library root is src/, cache dir is build/ at same level as src/
            let cache_dir = acornlib_path.join("build");
            Some((src_dir, cache_dir))
        } else {
            // Old format: library root is acornlib/, cache dir is build/ within acornlib/
            let cache_dir = acornlib_path.join("build");
            Some((acornlib_path.to_path_buf(), cache_dir))
        }
    }

    // A Project based on the provided starting path.
    // Returns an error if we can't find an acorn library.
    pub fn new_local(start_path: &Path, mode: ProverMode) -> Result<Project, ProjectError> {
        let (library_root, cache_dir) =
            Project::find_local_acorn_library(start_path).ok_or_else(|| {
                ProjectError(
                    "Could not find acornlib.\n\
                Please run this from within the acornlib directory.\n\
                See https://github.com/acornprover/acornlib for details."
                        .to_string(),
                )
            })?;
        let use_cache = mode != ProverMode::Full;
        let mut project = Project::new(library_root, cache_dir, use_cache, use_cache);
        if mode == ProverMode::Filtered {
            project.check_hashes = false;
        }
        Ok(project)
    }

    // Create a Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mock_dir = PathBuf::from("/mock");
        let cache_dir = mock_dir.join("build");
        let mut p = Project::new(mock_dir, cache_dir, false, false);
        p.use_filesystem = false;
        p
    }

    // Dropping existing modules lets you update the project for new data.
    // TODO: do this incrementally instead of dropping everything.
    fn drop_modules(&mut self) {
        self.modules = vec![];
        self.module_map = HashMap::new();
    }

    // You only need read access to an RwLock<Project> to stop the build.
    // When the build is stopped, threads that didn't stop the build themselves should
    // finish any long-running process with an "interrupted" behavior, and give up their
    // locks on the project.
    pub fn stop_build(&self) {
        self.build_stopped
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    // You need to have write access to a RwLock<Project> to re-allow the build.
    //
    // To change the project, acquire a read lock, stop the build, acquire a write lock, mess
    // around with the project state however you wanted, then re-allow the build.
    //
    // This asymmetry ensures that when we quickly stop and re-allow the build, any build in
    // progress will in fact stop.
    pub fn allow_build(&mut self) {
        self.build_stopped = Arc::new(AtomicBool::new(false));
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    // Either way, it's still added as a target.
    fn add_target_by_descriptor(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> Result<(), ImportError> {
        let result = self.load_module(descriptor);
        self.targets.insert(descriptor.clone());
        result.map(|_| ())
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    pub fn add_target_by_name(&mut self, module_name: &str) -> Result<(), ImportError> {
        self.add_target_by_descriptor(&ModuleDescriptor::name(module_name))
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    pub fn add_target_by_path(&mut self, path: &Path) -> Result<(), ImportError> {
        let descriptor = self.descriptor_from_path(path)?;
        self.add_target_by_descriptor(&descriptor)
    }

    // Adds a target for all files in this directory.
    pub fn add_all_targets(&mut self) {
        if !self.use_filesystem {
            panic!("cannot add all targets without filesystem access")
        }
        for entry in WalkDir::new(&self.library_root)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if entry.file_type().is_file() {
                let path = entry.path();

                // TODO: remove this when we want to check problems
                // Skip the file if it has the word "problems" in it
                if path.to_str().unwrap().contains("problems") {
                    continue;
                }

                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    // Ignore errors when adding all targets
                    let _ = self.add_target_by_path(path);
                }
            }
        }
    }

    // Whether we currently have this version of a file.
    pub fn has_version(&self, path: &PathBuf, version: i32) -> bool {
        if let Some((_, v)) = self.open_files.get(path) {
            &version == v
        } else {
            false
        }
    }

    // Returns None if we don't have this file at all.
    pub fn get_version(&self, path: &PathBuf) -> Option<i32> {
        self.open_files.get(path).map(|(_, version)| *version)
    }

    // The ModuleHash corresponding to the current build, *not* the known-good build.
    pub fn get_hash(&self, module_id: ModuleId) -> Option<&ModuleHash> {
        self.modules[module_id.get() as usize].hash.as_ref()
    }

    // Updating a file makes us treat it as "open". When a file is open, we use the
    // content in memory for it, rather than the content on disk.
    // Updated files are also added as build targets.
    pub fn update_file(
        &mut self,
        path: PathBuf,
        content: &str,
        version: i32,
    ) -> Result<(), ImportError> {
        if self.has_version(&path, version) {
            // No need to do anything
            return Ok(());
        }
        let descriptor = self.descriptor_from_path(&path)?;
        let mut reload_modules = vec![descriptor];
        if self.open_files.contains_key(&path) {
            // We're changing the value of an existing file. This could invalidate
            // current modules.
            // For now, we just drop everything and reload the targets.
            // TODO: figure out precisely which ones are invalidated.
            self.drop_modules();
            for target in &self.targets {
                reload_modules.push(target.clone());
            }
        }
        self.open_files.insert(path, (content.to_string(), version));
        for descriptor in &reload_modules {
            // Ignore errors when reloading
            let _ = self.add_target_by_descriptor(descriptor);
        }
        Ok(())
    }

    pub fn close_file(&mut self, path: PathBuf) -> Result<(), ImportError> {
        if !self.open_files.contains_key(&path) {
            // No need to do anything
            return Ok(());
        }
        self.open_files.remove(&path);
        let descriptor = self.descriptor_from_path(&path)?;
        self.drop_modules();
        self.targets.remove(&descriptor);
        let targets = self.targets.clone();
        for target in targets {
            // Ignore errors when reloading
            let _ = self.add_target_by_descriptor(&target);
        }
        Ok(())
    }

    // Create a Builder object that will then handle the build.
    pub fn builder<'a>(&self, event_handler: impl FnMut(BuildEvent) + 'a) -> Builder<'a> {
        Builder::new(event_handler)
    }

    // Builds all open modules, logging build events.
    pub fn build(&self, builder: &mut Builder) {
        // Build in alphabetical order by module name for consistency.
        let mut targets = self.targets.iter().collect::<Vec<_>>();
        targets.sort();

        builder.log_info(format!(
            "verifying modules: {}",
            targets
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));

        // The first phase is the "loading phase". We load modules and look for errors.
        // If there are errors, we won't try to do proving.
        let mut envs = vec![];
        for target in &targets {
            let module = self.get_module(target);
            match module {
                LoadState::Ok(env) => {
                    builder.module_loaded(&env);
                    envs.push(env);
                }
                LoadState::Error(e) => {
                    if e.indirect {
                        if builder.log_secondary_errors {
                            // The real problem is in a different module.
                            // So we don't want to locate the error in this module.
                            builder.log_info(e.to_string());
                        }
                    } else {
                        builder.log_loading_error(target, e);
                    }
                }
                LoadState::None => {
                    // Targets are supposed to be loaded already.
                    builder.log_info(format!("error: module {} is not loaded", target));
                }
                LoadState::Loading => {
                    // Happens if there's a circular import. A more localized error should
                    // show up elsewhere, so let's just log.
                    builder.log_info(format!("error: module {} stuck in loading", target));
                }
            }
        }

        if builder.status.is_error() {
            return;
        }

        builder.loading_phase_complete();

        // The second pass is the "proving phase".
        for (target, env) in targets.into_iter().zip(envs) {
            self.verify_module(&target, env, builder);
            if builder.status.is_error() {
                return;
            }
        }
    }

    // Turns a hash set of qualified premises into its serializable form.
    // If any premise is from an unimportable module, we return None.
    // This can happen when Acorn is running in "detached library" mode, where the current
    // file doesn't have any module name that can be used to refer to it.
    fn normalize_premises(
        &self,
        theorem_module_id: ModuleId,
        theorem_name: &str,
        premises: &HashSet<(ModuleId, String)>,
    ) -> Option<BTreeMap<String, BTreeSet<String>>> {
        let mut answer = BTreeMap::new();
        for (premise_module_id, premise_name) in premises {
            if *premise_module_id == theorem_module_id && premise_name == theorem_name {
                // We don't need to include the theorem itself as a premise.
                continue;
            }
            let module_name = match self.get_module_name_by_id(*premise_module_id) {
                Some(name) => name,
                None => return None,
            };
            answer
                .entry(module_name.to_string())
                .or_insert_with(BTreeSet::new)
                .insert(premise_name.clone());
        }
        Some(answer)
    }

    /// Construct a prover with only the facts that are included in the cached premises.
    /// Returns None if we don't have cached premises for this block.
    /// cursor points to the node we are verifying.
    pub fn make_filtered_prover(
        &self,
        env: &Environment,
        block_name: &str,
        module_cache: &Option<ModuleCache>,
    ) -> Option<Prover> {
        // Load the premises from the cache
        let normalized = module_cache.as_ref()?.blocks.get(block_name)?;
        let mut premises = HashMap::new();
        for (module_name, premise_set) in normalized.iter() {
            // A module could have been renamed, in which case the whole cache is borked.
            let module_id = self.get_module_id_by_name(module_name)?;
            premises.insert(module_id, premise_set.iter().cloned().collect());
        }
        let mut prover = Prover::new(&self, false);

        // Add facts from the dependencies
        let empty = HashSet::new();
        for module_id in self.all_dependencies(env.module_id) {
            let module_premises = match premises.get(&module_id) {
                Some(p) => p,
                None => &empty,
            };
            let module_env = self.get_env_by_id(module_id).unwrap();
            // importable_facts will always include extends and instance facts,
            // even when a filter is provided
            for fact in module_env.importable_facts(Some(module_premises)) {
                prover.add_fact(fact);
            }
        }

        // Find the index of the block with the given name
        let block_index = env.get_block_index(block_name)?;

        // Add facts from this file itself, but only up to the block we're proving
        let local_premises = premises.get(&env.module_id);
        for node in env.nodes.iter().take(block_index) {
            let Some(fact) = node.get_fact() else {
                continue;
            };

            // Always include facts that are used in normalization.
            if fact.used_in_normalization() {
                prover.add_fact(fact);
                continue;
            }

            let Some(name) = node.source_name() else {
                continue;
            };
            let Some(local_premises) = local_premises else {
                continue;
            };

            if local_premises.contains(&name) {
                prover.add_fact(fact);
            }
        }

        Some(prover)
    }

    // Verifies all goals within this module.
    // If we run into an error, we exit without verifying any more goals.
    #[cfg(test)]
    pub fn verify_module(
        &self,
        target: &ModuleDescriptor,
        env: &Environment,
        builder: &mut Builder,
    ) {
        self.verify_module_internal(target, env, builder);
    }

    #[cfg(not(test))]
    fn verify_module(&self, target: &ModuleDescriptor, env: &Environment, builder: &mut Builder) {
        self.verify_module_internal(target, env, builder);
    }

    fn verify_module_internal(
        &self,
        target: &ModuleDescriptor,
        env: &Environment,
        builder: &mut Builder,
    ) {
        if env.nodes.is_empty() {
            // Nothing to prove
            return;
        }

        let module_hash = self.get_hash(env.module_id).unwrap();
        let old_module_cache = self.build_cache.get_cloned(target);
        let mut new_module_cache = ModuleCache::new(module_hash);

        builder.module_proving_started(target.clone());

        // The full prover has access to all facts.
        let mut full_prover = Prover::new(&self, false);
        for fact in self.imported_facts(env.module_id, None) {
            full_prover.add_fact(fact);
        }
        let mut cursor = NodeCursor::new(&env, 0);

        // Loop over all the nodes that are right below the top level.
        loop {
            if cursor.requires_verification() {
                let block_name = cursor.block_name();
                // println!("{} at {} to {}", cursor.node(), cursor.node().first_line(), cursor.node().last_line());
                match cursor.node() {
                    Node::Block(b, _f) => {
                        if b.is_duplicate_theorem {
                            if cursor.node().has_goal() {
                                // println!("Is a duplicate");
                                let goalcontext = cursor.goal_context().unwrap();
                                builder.log_proving_info(&goalcontext, "Duplicate Theorem");
                            }
                        }
                    },
                    _ => {},
                }
                if self.check_hashes
                    && module_hash
                        .matches_through_line(&old_module_cache, cursor.node().last_line())
                {
                    // We don't need to verify this, we can just treat it as verified due to the hash.
                    builder.log_proving_cache_hit(&mut cursor);
                    if let Some(old_mc) = &old_module_cache {
                        // We skipped the proof of this theorem.
                        // But we still might want its premises cached.
                        // So we copy them over from the old module cache.
                        if let Some(old_block_cache) = old_mc.blocks.get(&block_name) {
                            new_module_cache
                                .blocks
                                .insert(block_name, old_block_cache.clone());
                        }
                    }
                } else {
                    // We do need to verify this.

                    // If we have a cached set of premises, we use it to create a filtered prover.
                    // The filtered prover only contains the premises that we think it needs.
                    let block_name = cursor.block_name();
                    let filtered_prover =
                        self.make_filtered_prover(env, &block_name, &old_module_cache);

                    // The premises we use while verifying this block.
                    let mut new_premises = HashSet::new();

                    // This call will recurse and verify everything within this top-level block.
                    self.verify_node(
                        &full_prover,
                        &filtered_prover,
                        &mut cursor,
                        &mut new_premises,
                        builder,
                    );
                    if builder.status.is_error() {
                        return;
                    }
                    match self.normalize_premises(env.module_id, &block_name, &new_premises) {
                        Some(normalized) => {
                            // We verified this block, so we can cache it.
                            new_module_cache
                                .blocks
                                .insert(block_name.clone(), normalized);
                        }
                        None => {
                            // We couldn't normalize the premises, so we can't cache them.
                            // This can happen if the module is unimportable.
                            builder.log_info(format!(
                                "could not normalize premises for {}",
                                block_name
                            ));
                        }
                    }
                }
            } else {
                builder.log_verified(cursor.node().first_line(), cursor.node().last_line());
            }
            if !cursor.has_next() {
                break;
            }
            if let Some(fact) = cursor.node().get_fact() {
                full_prover.add_fact(fact);
            }
            cursor.next();
        }

        if builder.module_proving_complete(target) {
            // The module was entirely verified. We can update the cache.
            if let Err(e) = self.build_cache.insert(target.clone(), new_module_cache) {
                builder.log_info(format!("error in build cache: {}", e));
            }
        }
    }

    // Verifies the goal at this node as well as at every child node.
    //
    // full_prover contains all facts that this node can use.
    // filtered_prover contains only the facts that were cached.
    // Our general strategy is to try the filtered prover, if we have it, and only fall back
    // to the full prover if the filtered prover doesn't work.
    //
    // node is a cursor, that typically we will mutate and reset to its original state.
    // new_premises is updated with the premises used in this theorem block.
    // builder tracks statistics and results for the build.
    //
    // If verify_node encounters an error, it stops, leaving node in a borked state.
    fn verify_node(
        &self,
        full_prover: &Prover,
        filtered_prover: &Option<Prover>,
        cursor: &mut NodeCursor,
        new_premises: &mut HashSet<(ModuleId, String)>,
        builder: &mut Builder,
    ) {
        if !cursor.requires_verification() {
            return;
        }

        let mut full_prover = full_prover.clone();
        let mut filtered_prover = filtered_prover.clone();
        if cursor.num_children() > 0 {
            // We need to recurse into children
            cursor.descend(0);
            loop {
                self.verify_node(
                    &full_prover,
                    &filtered_prover,
                    cursor,
                    new_premises,
                    builder,
                );
                if builder.status.is_error() {
                    return;
                }

                if let Some(fact) = cursor.node().get_fact() {
                    if let Some(ref mut filtered_prover) = filtered_prover {
                        filtered_prover.add_fact(fact.clone());
                    }
                    full_prover.add_fact(fact);
                }

                if cursor.has_next() {
                    cursor.next();
                } else {
                    break;
                }
            }
            cursor.ascend();
        }

        if cursor.node().has_goal() {
            let goal_context = cursor.goal_context().unwrap();
            let prover = self.verify_with_fallback(
                full_prover,
                filtered_prover,
                &goal_context,
                builder,
                cursor.goal_env().unwrap(),
            );
            if builder.status.is_error() {
                return;
            }

            // Gather the premises used by this proof
            prover.get_useful_source_names(new_premises);
        }
    }

    // Tries to use the filtered prover to verify this goal, but falls back to the full prover
    // if that doesn't work.
    // env should be the environment that the proof happens in.
    // Returns the prover that was used.
    fn verify_with_fallback(
        &self,
        mut full_prover: Prover,
        filtered_prover: Option<Prover>,
        goal_context: &GoalContext,
        builder: &mut Builder,
        env: &Environment,
    ) -> Prover {
        // Try the filtered prover
        if let Some(mut filtered_prover) = filtered_prover {
            builder.metrics.searches_filtered += 1;
            filtered_prover.set_goal(goal_context);
            let start = std::time::Instant::now();
            let outcome = filtered_prover.verification_search();
            if outcome == Outcome::Success {
                builder.search_finished(
                    &mut filtered_prover,
                    goal_context,
                    outcome,
                    start.elapsed(),
                    self,
                    env,
                );
                return filtered_prover;
            }
            builder.metrics.searches_fallback += 1;
        }

        // Try the full prover
        builder.metrics.searches_full += 1;
        full_prover.set_goal(goal_context);
        let start = std::time::Instant::now();
        let outcome = full_prover.verification_search();
        builder.search_finished(
            &mut full_prover,
            goal_context,
            outcome,
            start.elapsed(),
            self,
            env,
        );
        full_prover
    }

    // Does the build and returns when it's done, rather than asynchronously.
    // Returns (status, events, searches_success, cache).
    pub fn sync_build(&self) -> (BuildStatus, Vec<BuildEvent>, i32) {
        let mut events = vec![];
        let (status, searches_success) = {
            let mut builder = self.builder(|event| events.push(event));
            self.build(&mut builder);
            (builder.status, builder.metrics.searches_success)
        };
        (status, events, searches_success)
    }

    // Set the file content. This has priority over the actual filesystem.
    pub fn mock(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        let path = PathBuf::from(filename);
        let next_version = match self.get_version(&path) {
            Some(version) => version + 1,
            None => 0,
        };
        self.update_file(path, content, next_version)
            .expect("mock file update failed");
    }

    pub fn get_module_by_id(&self, module_id: ModuleId) -> &LoadState {
        match self.modules.get(module_id.get() as usize) {
            Some(module) => &module.state,
            None => &LoadState::None,
        }
    }

    pub fn get_module(&self, descriptor: &ModuleDescriptor) -> &LoadState {
        match self.module_map.get(descriptor) {
            Some(id) => self.get_module_by_id(*id),
            None => &LoadState::None,
        }
    }

    pub fn get_module_name_by_id(&self, module_id: ModuleId) -> Option<String> {
        match self.modules.get(module_id.get() as usize) {
            Some(module) => module.name(),
            None => None,
        }
    }

    pub fn get_module_id_by_name(&self, module_name: &str) -> Option<ModuleId> {
        self.module_map
            .get(&ModuleDescriptor::name(module_name))
            .copied()
    }

    pub fn get_env_by_id(&self, module_id: ModuleId) -> Option<&Environment> {
        if let LoadState::Ok(env) = self.get_module_by_id(module_id) {
            Some(env)
        } else {
            None
        }
    }

    /// You have to use the canonical descriptor, here. You can't use the path for a module
    /// that can also be referenced by name.
    pub fn get_env(&self, descriptor: &ModuleDescriptor) -> Option<&Environment> {
        if let Some(module_id) = self.module_map.get(&descriptor) {
            self.get_env_by_id(*module_id)
        } else {
            None
        }
    }

    /// Given a name in one environment, find the environment where it was originally defined.
    pub fn get_env_for_name<'a>(
        &'a self,
        env: &'a Environment,
        name: &ConstantName,
    ) -> Option<&'a Environment> {
        match name {
            ConstantName::DatatypeAttribute(datatype, attr_name) => {
                let attr_module_id = env
                    .bindings
                    .get_datatype_attribute_module(datatype, attr_name)?;
                self.get_env_by_id(attr_module_id)
            }
            ConstantName::TypeclassAttribute(typeclass, attr_name) => {
                let attr_module_id = env
                    .bindings
                    .get_typeclass_attribute_module(typeclass, attr_name)?;
                self.get_env_by_id(attr_module_id)
            }
            ConstantName::Unqualified(module_id, _name) => self.get_env_by_id(*module_id),
            ConstantName::Skolem(_) => None,
        }
    }

    /// Get doc comments for a constant, looking in the module where it was originally defined.
    pub fn get_constant_doc_comments<'a>(
        &'a self,
        env: &'a Environment,
        name: &ConstantName,
    ) -> Option<&'a Vec<String>> {
        self.get_env_for_name(env, name)?
            .bindings
            .get_constant_doc_comments(name)
    }

    /// Get definition string for a constant, looking in the module where it was originally defined.
    pub fn get_constant_definition_string<'a>(
        &'a self,
        env: &'a Environment,
        name: &ConstantName,
    ) -> Option<&'a String> {
        self.get_env_for_name(env, name)?
            .bindings
            .get_constant_definition_string(name)
    }

    /// Get doc comments for a datatype, looking in the module where it was originally defined.
    pub fn get_datatype_doc_comments(&self, datatype: &Datatype) -> Option<&Vec<String>> {
        self.get_env_by_id(datatype.module_id)?
            .bindings
            .get_datatype_doc_comments(datatype)
    }

    /// Get definition string for a datatype, looking in the module where it was originally defined.
    pub fn get_datatype_definition_string(&self, datatype: &Datatype) -> Option<&String> {
        self.get_env_by_id(datatype.module_id)?
            .bindings
            .get_datatype_definition_string(datatype)
    }

    /// Get doc comments for a typeclass, looking in the module where it was originally defined.
    pub fn get_typeclass_doc_comments(&self, typeclass: &Typeclass) -> Option<&Vec<String>> {
        self.get_env_by_id(typeclass.module_id)?
            .bindings
            .get_typeclass_doc_comments(typeclass)
    }

    /// Get definition string for a typeclass, looking in the module where it was originally defined.
    pub fn get_typeclass_definition_string(&self, typeclass: &Typeclass) -> Option<&String> {
        self.get_env_by_id(typeclass.module_id)?
            .bindings
            .get_typeclass_definition_string(typeclass)
    }

    /// Generate a GitHub link to the source code for a module.
    /// Returns None if the module doesn't have a valid path.
    pub fn github_link(&self, module_id: ModuleId) -> Option<String> {
        // Get the descriptor for this module
        let descriptor = self.get_module_descriptor(module_id)?;

        // Get the path for the module
        let path = self.path_from_descriptor(descriptor).ok()?;

        // Make it relative to the library root
        let relative_path = path.strip_prefix(&self.library_root).ok()?;

        // Convert to string with forward slashes
        let path_str = relative_path.to_str()?;
        let normalized_path = path_str.replace('\\', "/");

        // Prepend the GitHub URL
        Some(format!(
            "https://github.com/acornprover/acornlib/blob/master/src/{}",
            normalized_path
        ))
    }

    /// env should be the environment in which the token was evaluated.
    fn hover_for_info(
        &self,
        env: &Environment,
        info: &TokenInfo,
    ) -> code_generator::Result<HoverContents> {
        let mut gen = CodeGenerator::new(&env.bindings);
        let mut parts = vec![];

        // First add the main hover content
        let main_content = match &info.entity {
            NamedEntity::Value(value) => {
                // For partial applications, show the base function instead
                let base_value = value.unapply();
                gen.value_to_marked(base_value)?
            }
            NamedEntity::UnresolvedValue(unresolved) => {
                let generic = unresolved.clone().to_generic_value();
                gen.value_to_marked(&generic)?
            }

            NamedEntity::Type(t) => gen.type_to_marked(&t)?,
            NamedEntity::UnresolvedType(unresolved_type) => {
                let display = unresolved_type.to_display_type();
                gen.type_to_marked(&display)?
            }

            NamedEntity::Typeclass(typeclass) => {
                CodeGenerator::marked(format!("typeclass: {}", typeclass.name))
            }
            NamedEntity::Module(module_id) => {
                let name = self
                    .get_module_name_by_id(*module_id)
                    .unwrap_or("__module__".to_string());
                CodeGenerator::marked(name)
            }
        };
        parts.push(main_content);

        // Get definition string based on entity type
        let definition_string = match &info.entity {
            NamedEntity::Value(value) => {
                let base_value = value.unapply();
                match base_value {
                    AcornValue::Constant(ci) => self.get_constant_definition_string(env, &ci.name),
                    _ => None,
                }
            }
            NamedEntity::UnresolvedValue(unresolved) => {
                self.get_constant_definition_string(env, &unresolved.name)
            }
            NamedEntity::Type(acorn_type) => {
                if let AcornType::Data(datatype, _) = acorn_type {
                    self.get_datatype_definition_string(datatype)
                } else {
                    None
                }
            }
            NamedEntity::UnresolvedType(unresolved_type) => {
                self.get_datatype_definition_string(&unresolved_type.datatype)
            }
            NamedEntity::Typeclass(typeclass) => self.get_typeclass_definition_string(typeclass),
            NamedEntity::Module(_) => None,
        };

        // Add definition string if we have one and it's different from the main content
        if let Some(def_string) = definition_string {
            let marked = CodeGenerator::marked(def_string.clone());
            if Some(&marked) != parts.last() {
                parts.push(marked);
            }
        }

        // Get doc comments based on entity type
        let doc_comments = match &info.entity {
            NamedEntity::Value(value) => {
                // Use the unapplied value to get the base constant name for doc comments
                let base_value = value.unapply();
                match base_value {
                    AcornValue::Constant(ci) => {
                        // For constants (including those with type parameters), look up doc comments
                        self.get_constant_doc_comments(env, &ci.name)
                    }
                    _ => None,
                }
            }
            NamedEntity::UnresolvedValue(unresolved) => {
                self.get_constant_doc_comments(env, &unresolved.name)
            }

            NamedEntity::Type(acorn_type) => {
                if let AcornType::Data(datatype, _) = acorn_type {
                    self.get_datatype_doc_comments(datatype)
                } else {
                    None
                }
            }
            NamedEntity::UnresolvedType(unresolved_type) => {
                self.get_datatype_doc_comments(&unresolved_type.datatype)
            }

            NamedEntity::Typeclass(typeclass) => self.get_typeclass_doc_comments(typeclass),

            NamedEntity::Module(module_id) => {
                // Get the environment for this module to access its documentation
                if let Some(module_env) = self.get_env_by_id(*module_id) {
                    let doc_comments = module_env.get_module_doc_comments();
                    if doc_comments.is_empty() {
                        None
                    } else {
                        Some(doc_comments)
                    }
                } else {
                    None
                }
            }
        };

        // Add doc comments if we have them
        if let Some(comments) = doc_comments {
            if !comments.is_empty() {
                let doc_string = comments.join("\n");
                parts.push(MarkedString::String(doc_string));
            }
        }

        // Add "Go to definition" link if we can find the definition location
        if let Some(go_to_link) = self.create_go_to_link(&info.entity, env) {
            parts.push(MarkedString::String(go_to_link));
        }

        Ok(HoverContents::Array(parts))
    }

    /// Create a "Go to definition" link for the given entity.
    fn create_go_to_link(&self, entity: &NamedEntity, env: &Environment) -> Option<String> {
        let (name, range, module_id) = match entity {
            NamedEntity::Value(value) => {
                if let Some(constant_name) = value.as_simple_constant() {
                    let module_id = constant_name.module_id();
                    let module_env = if module_id == env.module_id {
                        env
                    } else {
                        self.get_env_by_id(module_id)?
                    };
                    let range = module_env.bindings.get_definition_range(
                        &crate::names::DefinedName::Constant(constant_name.clone()),
                    )?;
                    (constant_name.to_string(), range, module_id)
                } else {
                    return None;
                }
            }
            NamedEntity::UnresolvedValue(unresolved) => {
                let module_id = unresolved.name.module_id();
                let module_env = if module_id == env.module_id {
                    env
                } else {
                    self.get_env_by_id(module_id)?
                };
                let range = module_env.bindings.get_definition_range(
                    &crate::names::DefinedName::Constant(unresolved.name.clone()),
                )?;
                (unresolved.name.to_string(), range, module_id)
            }
            NamedEntity::Type(acorn_type) => {
                if let AcornType::Data(datatype, _) = acorn_type {
                    let module_id = datatype.module_id;
                    let module_env = if module_id == env.module_id {
                        env
                    } else {
                        self.get_env_by_id(module_id)?
                    };
                    let range = module_env.bindings.get_datatype_range(datatype)?;
                    (datatype.name.clone(), range, module_id)
                } else {
                    return None;
                }
            }
            NamedEntity::UnresolvedType(unresolved_type) => {
                let datatype = &unresolved_type.datatype;
                let module_id = datatype.module_id;
                let module_env = if module_id == env.module_id {
                    env
                } else {
                    self.get_env_by_id(module_id)?
                };
                let range = module_env.bindings.get_datatype_range(datatype)?;
                (datatype.name.clone(), range, module_id)
            }
            NamedEntity::Typeclass(typeclass) => {
                let module_id = typeclass.module_id;
                let module_env = if module_id == env.module_id {
                    env
                } else {
                    self.get_env_by_id(module_id)?
                };
                let range = module_env.bindings.get_typeclass_range(typeclass)?;
                (typeclass.name.clone(), range, module_id)
            }
            NamedEntity::Module(_) => {
                // Modules don't have a specific definition location we can link to
                return None;
            }
        };

        // Get the file path for the module
        let descriptor = self.get_module_descriptor(module_id)?;
        let file_path = self.path_from_descriptor(descriptor).ok()?;

        // Create a VSCode-style URI link
        // The format is: file:///path/to/file.ac#line,character
        let line = range.start.line + 1; // VSCode uses 1-based line numbers for links
        let character = range.start.character + 1; // VSCode uses 1-based character numbers for links
        let file_uri = format!("file://{}", file_path.to_string_lossy());
        let link = format!("[Go to {}]({}#{},{})", name, file_uri, line, character);

        Some(link)
    }

    /// Figure out the hover information to display.
    /// If we should be able to generate hover information but can't, we return an error message.
    pub fn hover(&self, env: &Environment, line_number: u32, character: u32) -> Option<Hover> {
        let (env, key, info) = env.find_token(line_number, character)?;
        let contents = match self.hover_for_info(env, info) {
            Ok(contents) => contents,
            Err(e) => {
                if cfg!(test) {
                    panic!("code generation error: {}", e);
                }

                // If we can't generate hover info, just return an error message.
                let message = format!("hover error: {} ({})", e, e.error_type());
                HoverContents::Scalar(CodeGenerator::marked(message))
            }
        };
        Some(Hover {
            contents,
            range: Some(key.range()),
        })
    }

    pub fn errors(&self) -> Vec<(ModuleId, &compilation::Error)> {
        let mut errors = vec![];
        for (module_id, module) in self.modules.iter().enumerate() {
            if let LoadState::Error(e) = &module.state {
                errors.push((ModuleId(module_id as u16), e));
            }
        }
        errors
    }

    fn read_file(&mut self, path: &PathBuf) -> Result<String, ProjectError> {
        if let Some((content, _)) = self.open_files.get(path) {
            return Ok(content.clone());
        }
        if !self.use_filesystem {
            return Err(ProjectError(format!(
                "no mocked file for: {}",
                path.display()
            )));
        }
        match std::fs::read_to_string(&path) {
            Ok(s) => Ok(s),
            Err(e) => Err(ProjectError(format!(
                "error loading {}: {}",
                path.display(),
                e
            ))),
        }
    }

    // Returns the canonical descriptor for a path.
    // Returns a load error if this isn't a valid path for an acorn file.
    pub fn descriptor_from_path(&self, path: &Path) -> Result<ModuleDescriptor, ImportError> {
        let relative = match path.strip_prefix(&self.library_root) {
            Ok(relative) => relative,
            Err(_) => return Ok(ModuleDescriptor::File(path.to_path_buf())),
        };
        let components: Vec<_> = relative
            .components()
            .map(|comp| comp.as_os_str().to_string_lossy())
            .collect();
        let mut parts = Vec::new();
        for (i, component) in components.iter().enumerate() {
            let part = if i + 1 == components.len() {
                if !component.ends_with(".ac") {
                    return Err(ImportError::NotFound(format!(
                        "path {} does not end with .ac",
                        path.display()
                    )));
                }
                // Handle the special case of default.ac
                if component == "default.ac" && i > 0 {
                    // The module name should be the parent directory
                    // We've already added it to parts, so we're done
                    break;
                }
                component[..component.len() - 3].to_string()
            } else {
                component.to_string()
            };
            let name_so_far = if parts.is_empty() {
                part.clone()
            } else {
                format!("{}.{}", parts.join("."), part)
            };
            check_valid_module_part(&part, &name_so_far)?;
            parts.push(part);
        }

        Ok(ModuleDescriptor::Name(parts))
    }

    pub fn path_from_module_name(&self, module_name: &str) -> Result<PathBuf, ImportError> {
        let mut path = self.library_root.clone();
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            check_valid_module_part(part, module_name)?;

            if i + 1 == parts.len() {
                // For the last part, check both foo.ac and foo/default.ac
                let file_path = path.join(format!("{}.ac", part));
                let dir_path = path.join(part).join("default.ac");

                let file_exists = if self.use_filesystem {
                    file_path.exists()
                } else {
                    self.open_files.contains_key(&file_path)
                };

                let dir_exists = if self.use_filesystem {
                    dir_path.exists()
                } else {
                    self.open_files.contains_key(&dir_path)
                };

                if file_exists && dir_exists {
                    return Err(ImportError::NotFound(format!(
                        "ambiguous module '{}': both {} and {} exist",
                        module_name,
                        file_path.display(),
                        dir_path.display()
                    )));
                } else if file_exists {
                    return Ok(file_path);
                } else if dir_exists {
                    return Ok(dir_path);
                } else {
                    // Default to the file path for the error message
                    return Ok(file_path);
                }
            } else {
                path.push(part.to_string());
            }
        }
        unreachable!("should have returned in the loop")
    }

    pub fn path_from_descriptor(
        &self,
        descriptor: &ModuleDescriptor,
    ) -> Result<PathBuf, ImportError> {
        let name = match descriptor {
            ModuleDescriptor::Name(parts) => parts.join("."),
            ModuleDescriptor::File(path) => return Ok(path.clone()),
            ModuleDescriptor::Anonymous => {
                return Err(ImportError::NotFound("anonymous module".to_string()))
            }
        };

        self.path_from_module_name(&name)
    }

    pub fn url_from_descriptor(&self, descriptor: &ModuleDescriptor) -> Option<Url> {
        let path = self.path_from_descriptor(descriptor).ok()?;
        Url::from_file_path(path).ok()
    }

    /// Get a display-friendly path string for a module descriptor.
    /// Returns the path relative to the library root, suitable for error messages.
    pub fn display_path(&self, descriptor: &ModuleDescriptor) -> String {
        match self.path_from_descriptor(descriptor) {
            Ok(full_path) => {
                // Try to make it relative to the library root
                match full_path.strip_prefix(&self.library_root) {
                    Ok(relative_path) => relative_path.to_string_lossy().to_string(),
                    Err(_) => {
                        // If it's not under library root, just use the full path
                        full_path.to_string_lossy().to_string()
                    }
                }
            }
            Err(_) => {
                // Fall back to the descriptor's Display implementation
                descriptor.to_string()
            }
        }
    }

    pub fn path_from_module_id(&self, module_id: ModuleId) -> Option<PathBuf> {
        self.path_from_descriptor(&self.modules[module_id.get() as usize].descriptor)
            .ok()
    }

    pub fn get_module_descriptor(&self, module_id: ModuleId) -> Option<&ModuleDescriptor> {
        self.modules
            .get(module_id.get() as usize)
            .map(|m| &m.descriptor)
    }

    pub fn get_module_cache(&self, descriptor: &ModuleDescriptor) -> Option<ModuleCache> {
        self.build_cache.get_cloned(descriptor)
    }

    /// Iterate over all module descriptors with their corresponding module IDs.
    pub fn iter_modules(&self) -> impl Iterator<Item = (&ModuleDescriptor, ModuleId)> {
        self.module_map
            .iter()
            .map(|(descriptor, &module_id)| (descriptor, module_id))
    }

    // Loads a module from cache if possible, or else from the filesystem.
    // Module names are a .-separated list where each one must be [a-z_].
    // Each component maps to a subdirectory, except the last one, which maps to a .ac file.
    // load returns an error if the module-loading process itself has an error.
    // For example, we might have an invalid name, the file might not exist, or this
    // might be a circular import.
    // If there is an error in the file, the load will return a module id, but the module
    // for the id will have an error.
    // If "open" is passed, then we cache this file's content in open files.
    fn load_module(&mut self, descriptor: &ModuleDescriptor) -> Result<ModuleId, ImportError> {
        if let Some(module_id) = self.module_map.get(&descriptor) {
            if let LoadState::Loading = self.get_module_by_id(*module_id) {
                return Err(ImportError::Circular(*module_id));
            }
            return Ok(*module_id);
        }

        let path = self.path_from_descriptor(descriptor)?;
        let mut text = String::new();
        if let Some(path_string) = path.to_str() {
            if path_string == "<stdin>" {
                if io::stdin().is_terminal() {
                    // Throws an error if it is in a terminal
                    return Err(ImportError::NotFound(String::from(
                        "cannot read stdin in an active terminal",
                    )));
                }
                let _ = io::stdin().lock();
                for line in io::stdin().lines() {
                    text.push_str(&line.unwrap());
                    text.push('\n');
                }
            } else if path_string.starts_with("-:") {
                let Some(string_path) = path.to_str() else {
                    println!("error: path cannot be empty");
                    std::process::exit(1);
                };
                if io::stdin().is_terminal() {
                    // Throws an error if it is in a terminal
                    return Err(ImportError::NotFound(String::from(
                        "cannot read stdin in an active terminal",
                    )));
                }
                let path2 = &string_path[2..];
                println!("Path: {}", path2);
                text = self
                    .read_file(&PathBuf::from(path2))
                    .map_err(|e| ImportError::NotFound(e.to_string()))?;
                let _ = io::stdin().lock();
                for line in io::stdin().lines() {
                    text.push_str(&line.unwrap());
                    text.push('\n');
                }
            } else {
                text = self
                    .read_file(&path)
                    .map_err(|e| ImportError::NotFound(e.to_string()))?;
            }
        } else {
            text = self
                .read_file(&path)
                .map_err(|e| ImportError::NotFound(e.to_string()))?;
        }

        // Give this module an id before parsing it, so that we can catch circular imports.
        let module_id = ModuleId(self.modules.len() as u16);
        self.modules.push(Module::new(descriptor.clone()));
        self.module_map.insert(descriptor.clone(), module_id);

        let mut env = Environment::new(module_id);
        let tokens = Token::scan(&text);
        if let Err(e) = env.add_tokens(self, tokens) {
            if e.circular.is_some() {
                let err = Err(ImportError::Circular(module_id));
                self.modules[module_id.get() as usize].load_error(e);
                return err;
            }
            self.modules[module_id.get() as usize].load_error(e);
            return Ok(module_id);
        }

        // Hash this module, reflecting its state on disk.
        let module_hash = ModuleHash::new(
            &text,
            env.bindings
                .direct_dependencies()
                .iter()
                .map(|dep_id| &self.modules[dep_id.get() as usize]),
        );
        self.modules[module_id.get() as usize].load_ok(env, module_hash);
        Ok(module_id)
    }

    pub fn load_module_by_name(&mut self, module_name: &str) -> Result<ModuleId, ImportError> {
        let descriptor = ModuleDescriptor::name(module_name);
        self.load_module(&descriptor)
    }

    // Appends all dependencies, including chains of direct dependencies.
    // Ie, if A imports B and B imports C, then A depends on B and C.
    // The order will be the "pop order", so that each module is added only
    // after all of its dependencies are added.
    pub fn all_dependencies(&self, original_module_id: ModuleId) -> Vec<ModuleId> {
        let mut answer = vec![];
        let mut seen = HashSet::new();
        self.append_dependencies(&mut seen, &mut answer, original_module_id);
        answer
    }

    // Helper function for all_dependencies.
    // Returns "false" if we have already seen this dependency.
    // Does not append module_id itself. If we want it, add that in last.
    fn append_dependencies(
        &self,
        seen: &mut HashSet<ModuleId>,
        output: &mut Vec<ModuleId>,
        module_id: ModuleId,
    ) -> bool {
        if !seen.insert(module_id) {
            return false;
        }
        if let LoadState::Ok(env) = self.get_module_by_id(module_id) {
            for dep in env.bindings.direct_dependencies() {
                if self.append_dependencies(seen, output, dep) {
                    output.push(dep);
                }
            }
        }
        true
    }

    pub fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        if let LoadState::Ok(env) = self.get_module_by_id(module_id) {
            Some(&env.bindings)
        } else {
            None
        }
    }

    /// All facts that the given module imports.
    /// If filter is provided, only facts that match the filter are returned.
    pub fn imported_facts(
        &self,
        module_id: ModuleId,
        filter: Option<&HashSet<String>>,
    ) -> Vec<Fact> {
        let mut facts = vec![];
        for dependency in self.all_dependencies(module_id) {
            let env = self.get_env_by_id(dependency).unwrap();
            facts.extend(env.importable_facts(filter));
        }
        facts
    }

    // path is the file we're in.
    // env_line is zero-based. It's the closest unchanged line, to use for finding the environment.
    // prefix is the entire line they've typed so far. Generally different from env_line.
    // Returns a list of completions, or None if we don't have any.
    pub fn get_completions(
        &self,
        path: Option<&Path>,
        env_line: u32,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        let re = Regex::new(r"[a-zA-Z0-9._]+").unwrap();
        let parts: Vec<&str> = re.find_iter(prefix).map(|mat| mat.as_str()).collect();
        if parts.len() == 4 && parts[0] == "from" && parts[2] == "import" {
            // We are in a "from X import Y" statement.
            let name = parts[1];
            let partial = parts[3];
            let descriptor = ModuleDescriptor::name(name);
            let env = match self.get_env(&descriptor) {
                Some(env) => env,
                None => {
                    // The module isn't loaded, so we don't know what names it has.
                    if name == "nat" && "Nat".starts_with(partial) {
                        // Cheat to optimize the tutorial.
                        // If we always loaded nat, we wouldn't need this.
                        return Some(vec![CompletionItem {
                            label: "Nat".to_string(),
                            kind: Some(tower_lsp::lsp_types::CompletionItemKind::CLASS),
                            ..Default::default()
                        }]);
                    }
                    return None;
                }
            };
            return env.bindings.get_completions(partial, true, &self);
        }

        // If we don't have a path, we can only complete imports.
        let path = path?;

        // Check if we have a completable word
        let word = match parts.last() {
            Some(word) => *word,
            None => return None,
        };

        if !word.chars().all(|c| Token::identifierish(c) || c == '.') {
            return None;
        }

        // Find the right environment
        let descriptor = self.descriptor_from_path(&path).ok()?;
        let env = match self.get_env(&descriptor) {
            Some(env) => env,
            None => return None,
        };
        let env = env.env_for_line(env_line);

        env.bindings.get_completions(word, false, &self)
    }

    // Yields (url, version) for all open files.
    pub fn open_urls(&self) -> impl Iterator<Item = (Url, i32)> + '_ {
        self.open_files.iter().filter_map(|(path, (_, version))| {
            Url::from_file_path(path.clone())
                .ok()
                .map(|url| (url, *version))
        })
    }

    // Expects the module to load successfully and for there to be no errors in the loaded module.
    // Only for testing.
    pub fn expect_ok(&mut self, module_name: &str) -> ModuleId {
        let module_id = self.load_module_by_name(module_name).expect("load failed");
        match self.get_module_by_id(module_id) {
            LoadState::Ok(_) => module_id,
            LoadState::Error(e) => panic!("error in {}: {}", module_name, e),
            _ => panic!("logic error"),
        }
    }

    // This expects there to be an error during loading itself.
    #[cfg(test)]
    pub fn expect_load_err(&mut self, module_name: &str) {
        assert!(self.load_module_by_name(module_name).is_err());
    }

    // This expects the module to load, but for there to be an error in the loaded module.
    #[cfg(test)]
    pub fn expect_module_err(&mut self, module_name: &str) {
        let module_id = self.load_module_by_name(module_name).expect("load failed");
        if let LoadState::Error(_) = self.get_module_by_id(module_id) {
            // What we expected
        } else {
            panic!("expected error");
        }
    }

    // Checks that the given expression can be parsed and turned back into code.
    #[cfg(test)]
    pub fn check_code_into(&mut self, module_name: &str, input: &str, expected: &str) {
        use crate::{code_generator::CodeGenerator, evaluator::Evaluator, expression::Expression};

        let module_id = self.expect_ok(module_name);
        let expression = Expression::expect_value(input);
        let env = self.get_env_by_id(module_id).expect("no env");
        let value =
            match Evaluator::new(self, &env.bindings, None).evaluate_value(&expression, None) {
                Ok(value) => value,
                Err(e) => panic!("evaluation error: {}", e),
            };
        CodeGenerator::expect(&env.bindings, input, &value, expected);
    }

    #[cfg(test)]
    pub fn check_code(&mut self, module_name: &str, code: &str) {
        self.check_code_into(module_name, code, code);
    }

    // Checks that generating code for the goal of the given theorem gives the expected result.
    #[cfg(test)]
    pub fn check_goal_code(&mut self, module_name: &str, theorem_name: &str, expected: &str) {
        use crate::code_generator::CodeGenerator;

        let module_id = self.expect_ok(module_name);
        let env = self.get_env_by_id(module_id).expect("no env");
        let node = env.get_node_by_description(theorem_name);
        let goal_context = node.goal_context().unwrap();
        let value = goal_context.goal.value();
        let fake_input = format!("<{}>", theorem_name);
        CodeGenerator::expect(&node.env().bindings, &fake_input, &value, expected);
    }

    // Returns num_success.
    #[cfg(test)]
    pub fn expect_build_ok(&mut self) -> i32 {
        let (status, events, searches_success) = self.sync_build();
        assert_eq!(status, BuildStatus::Good);
        assert!(events.len() > 0);
        let (done, total) = events.last().unwrap().progress.unwrap();
        assert_eq!(done, total, "expected number of build events didn't match");
        searches_success
    }

    #[cfg(test)]
    pub fn expect_build_fails(&mut self) {
        let (status, _, _) = self.sync_build();
        assert_ne!(status, BuildStatus::Good, "expected build to fail");
    }
}
