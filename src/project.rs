use core::panic;
use std::collections::{HashMap, HashSet};
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::{fmt, io};

use regex::Regex;
use tower_lsp::lsp_types::{self, CompletionItem, Hover, HoverContents, MarkedString, Url};
use walkdir::WalkDir;

use crate::build_cache::BuildCache;
use crate::certificate::{Certificate, CertificateLine};
use crate::code_generator::{self, CodeGenerator};
use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::environment::Environment;
use crate::elaborator::error;
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::ConstantName;
use crate::interfaces::{GoalInfo, Location, Step};
use crate::kernel::checker::StepReason;
use crate::module::{LoadState, Module, ModuleDescriptor, ModuleId};
use crate::processor::Processor;
use crate::syntax::statement::Statement;
use crate::syntax::token::Token;
use crate::syntax::token_map::TokenInfo;

// The Project is responsible for importing different files and assigning them module ids.
pub struct Project {
    // Flags that affect project behavior
    pub config: ProjectConfig,

    // The source directory of the library.
    // This is used to resolve all imports.
    // Note that it may be different from the editor root, which is where the user is working.
    // Set to "/mock" for mock projects.
    src_dir: PathBuf,

    // The directory where build artifacts are stored
    pub build_dir: PathBuf,

    // For "open" files, we use the content we are storing rather than the content on disk.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress whose state is "owned" by an IDE via the language server protocol.
    //
    // Maps filename -> (contents, version number).
    // The version number can mean whatever the caller wants it to mean.
    // From vscode, it'll be the vscode version number.
    open_files: HashMap<PathBuf, (String, i32)>,

    // modules[module_id] is the Module for the given module id.
    // Built-in modules have no name.
    modules: Vec<Module>,

    // module_map maps from a module's descriptor to its id
    module_map: HashMap<ModuleDescriptor, ModuleId>,

    // The module names that we want to build.
    pub targets: HashSet<ModuleDescriptor>,

    // The last known-good build cache.
    // This is different from the Builder's build cache, which is created during a build.
    pub build_cache: BuildCache,

    // A flag for whether something is using the project to build right now.
    // Only used in the parallel server code.
    pub building: bool,
}

/// Configuration options for the project.
#[derive(Clone)]
pub struct ProjectConfig {
    // Whether we permit loading files from the filesystem.
    // If false, this indicates we only want mocked files.
    pub use_filesystem: bool,

    // Whether we should read from the cache
    pub read_cache: bool,

    // Whether we should write to the cache
    pub write_cache: bool,
}

impl Default for ProjectConfig {
    fn default() -> Self {
        Self {
            use_filesystem: true,
            read_cache: true,
            write_cache: true,
        }
    }
}

// General project-level errors (file operations, setup, etc.)
#[derive(Debug)]
pub struct ProjectError(pub String);

impl From<io::Error> for ProjectError {
    fn from(error: io::Error) -> Self {
        ProjectError(format!("{}", error))
    }
}

impl From<crate::manifest::ManifestError> for ProjectError {
    fn from(error: crate::manifest::ManifestError) -> Self {
        ProjectError(format!("{}", error))
    }
}

impl fmt::Display for ProjectError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<ProjectError> for String {
    fn from(error: ProjectError) -> Self {
        error.0
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

impl From<ImportError> for String {
    fn from(error: ImportError) -> Self {
        error.to_string()
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

/// Convert a Unix-style path (like /mock/foo.ac) into a platform-specific absolute path.
/// On Windows, this converts /mock/foo to C:\mock\foo to ensure it's treated as absolute.
/// On Unix, the path is already absolute, so we just return it as-is.
pub fn localize_mock_filename(s: &str) -> String {
    if cfg!(windows) {
        // On Windows, convert Unix-style absolute paths to Windows-style
        if s.starts_with('/') {
            format!("C:{}", s.replace('/', "\\"))
        } else {
            s.to_string()
        }
    } else {
        s.to_string()
    }
}

impl Project {
    // Create a new project.
    // Returns an error if the build cache manifest version is too new.
    pub fn new(
        src_dir: PathBuf,
        build_dir: PathBuf,
        config: ProjectConfig,
    ) -> Result<Project, ProjectError> {
        // Load the build cache.
        // We need to load it when reading (to use cached certs) OR when writing (to preserve
        // manifest entries from other modules during partial builds).
        let build_cache = if config.read_cache || config.write_cache {
            BuildCache::load(build_dir.clone())?
        } else {
            BuildCache::new(build_dir.clone())
        };

        Ok(Project {
            config,
            src_dir,
            open_files: HashMap::new(),
            modules: vec![],
            module_map: HashMap::new(),
            targets: HashSet::new(),
            build_cache,
            build_dir,
            building: false,
        })
    }

    // Finds an acorn library directory, based on the provided path.
    // It can be either:
    //   - a parent directory named "acornlib" (with acorn.toml)
    //   - a parent directory containing "acorn.toml"
    //   - a directory named "acornlib" next to one named "acorn" or "acorn{n}" (with acorn.toml)
    // Returns (src_dir, build_dir) where src_dir is src/, build_dir is build/
    pub fn find_local_acorn_library(start: &Path) -> Option<(PathBuf, PathBuf)> {
        let mut current = Some(start);

        while let Some(path) = current {
            // Check if path is an acornlib directory with proper structure
            if path.ends_with("acornlib") {
                return Self::check_acornlib_layout(path);
            }

            // Check if path contains acorn.toml
            if path.join("acorn.toml").is_file() {
                return Self::check_acornlib_layout(path);
            }

            // Check if path has a sibling named acornlib (if current dir is "acorn" or "acorn{n}")
            if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                if name == "acorn"
                    || (name.starts_with("acorn") && name[5..].chars().all(|c| c.is_ascii_digit()))
                {
                    let library_path = path.with_file_name("acornlib");
                    if library_path.is_dir() {
                        return Self::check_acornlib_layout(&library_path);
                    }
                }
            }

            current = path.parent();
        }

        None
    }

    // Helper function to check if an acornlib directory has the required format
    // with acorn.toml and src directory. Returns (src_dir, build_dir).
    fn check_acornlib_layout(acornlib_path: &Path) -> Option<(PathBuf, PathBuf)> {
        let acorn_toml = acornlib_path.join("acorn.toml");
        let src_dir = acornlib_path.join("src");

        if acorn_toml.is_file() && src_dir.is_dir() {
            // Src dir is src/, build dir is build/ at same level as src/
            let build_dir = acornlib_path.join("build");
            Some((src_dir, build_dir))
        } else {
            None
        }
    }

    // A Project based on the provided starting path.
    // Returns an error if we can't find an acorn library, or if the manifest version is too new.
    pub fn new_local(start_path: &Path, config: ProjectConfig) -> Result<Project, ProjectError> {
        let (src_dir, build_dir) =
            Project::find_local_acorn_library(start_path).ok_or_else(|| {
                ProjectError(
                    "Could not find acornlib.\n\
                Please run this from within the acornlib directory.\n\
                See https://github.com/acornprover/acornlib for details."
                        .to_string(),
                )
            })?;
        Project::new(src_dir, build_dir, config)
    }

    // Create a Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mock_dir = PathBuf::from(localize_mock_filename("/mock"));
        let build_dir = mock_dir.join("build");
        let config = ProjectConfig {
            use_filesystem: false,
            read_cache: false,
            write_cache: false,
        };
        // Mock projects don't read the cache, so this can't fail
        Project::new(mock_dir, build_dir, config).expect("mock project creation failed")
    }

    /// Updates the build cache with a new one and optionally writes it to disk.
    /// If is_partial_build is true, old manifest entries are preserved for modules
    /// that weren't rebuilt. If false (full build), only newly built modules are in the manifest.
    pub fn update_build_cache(&mut self, mut new_cache: BuildCache, is_partial_build: bool) {
        if self.config.write_cache {
            // Save and merge: writes only new JSONL files, preserves manifest based on build type,
            // and merges old certificates back into memory
            // TODO: how should we handle errors here?
            let _ = new_cache.save_merging_old(&self.build_cache, is_partial_build);
        } else {
            // Even if we're not writing to disk, we need to merge the old certificates
            // into memory so they're available for future builds
            new_cache.merge_certificates_from(&self.build_cache);
        }

        self.build_cache = new_cache;
    }

    // Dropping existing modules lets you update the project for new data.
    // TODO: do this incrementally instead of dropping everything.
    fn drop_modules(&mut self) {
        self.modules = vec![];
        self.module_map = HashMap::new();
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    // Either way, it's still added as a target.
    fn add_target_by_descriptor(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> Result<(), ImportError> {
        let result = self.load_module(descriptor, false);
        self.targets.insert(descriptor.clone());
        result.map(|_| ())
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    pub fn add_target_by_name(&mut self, module_name: &str) -> Result<(), ImportError> {
        self.register_all_modules();
        self.add_target_by_descriptor(&ModuleDescriptor::name(module_name))
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    pub fn add_target_by_path(&mut self, path: &Path) -> Result<(), ImportError> {
        self.register_all_modules();
        let descriptor = self.descriptor_from_path(path)?;
        self.add_target_by_descriptor(&descriptor)
    }

    // Pre-registers all modules from the src directory with stable ModuleIds.
    // This ensures that every module always gets the same ModuleId regardless of
    // whether we're verifying one module or all modules.
    // Idempotent: does nothing if modules are already registered.
    fn register_all_modules(&mut self) {
        if !self.config.use_filesystem || !self.modules.is_empty() {
            return;
        }

        // Collect all .ac file paths
        let mut paths: Vec<PathBuf> = Vec::new();
        for entry in WalkDir::new(&self.src_dir)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if entry.file_type().is_file() {
                let path = entry.path();
                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    paths.push(path.to_path_buf());
                }
            }
        }

        // Convert to descriptors, separating prelude from the rest
        let mut prelude_descriptor = None;
        let mut descriptors: Vec<ModuleDescriptor> = Vec::new();
        for path in &paths {
            if let Ok(descriptor) = self.descriptor_from_path(path) {
                if matches!(&descriptor, ModuleDescriptor::Name(parts) if parts.len() == 1 && parts[0] == "prelude")
                {
                    prelude_descriptor = Some(descriptor);
                } else {
                    descriptors.push(descriptor);
                }
            }
        }

        // Sort non-prelude descriptors for deterministic ordering
        descriptors.sort();

        // Reserve slot 0 for prelude
        if let Some(desc) = prelude_descriptor {
            self.modules.push(Module::new_registered(desc.clone()));
            self.module_map.insert(desc, ModuleId::PRELUDE);
        } else {
            self.modules.push(Module::anonymous());
        }

        // Assign sequential IDs to remaining modules in sorted order
        for descriptor in descriptors {
            let id = ModuleId(self.modules.len() as u16);
            self.modules
                .push(Module::new_registered(descriptor.clone()));
            self.module_map.insert(descriptor, id);
        }
    }

    // Adds a target for all files in the 'src' directory.
    pub fn add_src_targets(&mut self) {
        if !self.config.use_filesystem {
            panic!("cannot add_src_targets without filesystem access")
        }
        self.register_all_modules();

        // Collect and sort paths for deterministic loading order
        let mut paths: Vec<PathBuf> = Vec::new();
        for entry in WalkDir::new(&self.src_dir)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if entry.file_type().is_file() {
                let path = entry.path();
                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    paths.push(path.to_path_buf());
                }
            }
        }
        paths.sort();

        for path in paths {
            // Ignore errors when adding all targets
            let _ = self.add_target_by_path(&path);
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

    pub fn get_module_content_hash(&self, module_id: ModuleId) -> Option<blake3::Hash> {
        self.modules[module_id.get() as usize].hash
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

        // This update might be invalidating current modules.
        // For now, we just drop everything and reload the targets.
        // TODO: figure out precisely which ones are invalidated.
        self.drop_modules();
        for target in &self.targets {
            reload_modules.push(target.clone());
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
        // Don't remove the target - we want to keep building all files
        // even when they're closed
        self.drop_modules();
        let targets = self.targets.clone();
        for target in targets {
            // Ignore errors when reloading
            let _ = self.add_target_by_descriptor(&target);
        }
        Ok(())
    }

    // Set the file content. This has priority over the actual filesystem.
    // The filename should be in Linux-style format (e.g., "/mock/foo.ac").
    // It will be converted to the platform-specific format automatically.
    pub fn mock(&mut self, filename: &str, content: &str) {
        assert!(!self.config.use_filesystem);
        // Convert Unix-style /mock/ paths to platform-specific absolute paths.
        // On Windows, this converts "/mock/foo.ac" to "C:\mock\foo.ac".
        // On Unix, the path remains "/mock/foo.ac".
        let localized = localize_mock_filename(filename);
        let path = PathBuf::from(localized);
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
            ConstantName::SpecificDatatypeAttribute(datatype, _types, attr_name) => {
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
            ConstantName::Synthetic(..) => None,
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

        // Make it relative to the src dir
        let relative_path = path.strip_prefix(&self.src_dir).ok()?;

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
                // For variables, use the token text as the name
                if let AcornValue::Variable(_, t) = value {
                    let type_expr = gen.type_to_expr(&t)?;
                    CodeGenerator::marked(format!("{}: {}", info.text, type_expr))
                } else {
                    // For partial applications, show the base function instead
                    let base_value = value.unapply();
                    gen.value_to_marked(base_value)?
                }
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

    /// Gets the location and the name of a definition if available
    fn definition_info(
        &self,
        entity: &NamedEntity,
        env: &Environment,
    ) -> Option<(String, Location)> {
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
                        &crate::elaborator::names::DefinedName::Constant(constant_name.clone()),
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
                    &crate::elaborator::names::DefinedName::Constant(unresolved.name.clone()),
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

        let uri = Url::from_file_path(file_path).ok()?;

        Some((name, Location { uri, range: *range }))
    }

    /// Create a "Go to definition" link for the given entity.
    fn create_go_to_link(&self, entity: &NamedEntity, env: &Environment) -> Option<String> {
        let (name, location) = self.definition_info(entity, env)?;

        // Create a VSCode-style URI link
        // The format is: file:///path/to/file.ac#line,character
        let line = location.range.start.line + 1; // VSCode uses 1-based line numbers for links
        let character = location.range.start.character + 1; // VSCode uses 1-based character numbers for links
        let file_uri = location.uri.as_str();
        let link = format!("[Go to {}]({}#{},{})", name, file_uri, line, character);

        Some(link)
    }

    /// Figure out the definition location of the item at the given line_number and character
    pub fn definition_location(
        &self,
        env: &Environment,
        line_number: u32,
        character: u32,
    ) -> Option<lsp_types::Location> {
        let (env, _, info) = env.find_token(line_number, character)?;
        self.definition_info(&info.entity, env)
            .map(|(_, location)| lsp_types::Location {
                uri: location.uri,
                range: location.range,
            })
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

    pub fn errors(&self) -> Vec<(ModuleId, &error::Error)> {
        let mut errors = vec![];
        for (module_id, module) in self.modules.iter().enumerate() {
            if let LoadState::Error(e) = &module.state {
                errors.push((ModuleId(module_id as u16), e));
            }
        }
        errors
    }

    pub fn read_file(&self, path: &PathBuf) -> Result<String, ProjectError> {
        if let Some((content, _)) = self.open_files.get(path) {
            return Ok(content.clone());
        }
        if !self.config.use_filesystem {
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
        let relative = match path.strip_prefix(&self.src_dir) {
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
        let mut path = self.src_dir.clone();
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            check_valid_module_part(part, module_name)?;

            if i + 1 == parts.len() {
                // For the last part, check both foo.ac and foo/default.ac
                let file_path = path.join(format!("{}.ac", part));
                let dir_path = path.join(part).join("default.ac");

                let file_exists = if self.config.use_filesystem {
                    file_path.exists()
                } else {
                    self.open_files.contains_key(&file_path)
                };

                let dir_exists = if self.config.use_filesystem {
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
    /// Returns the path relative to the src dir, suitable for error messages.
    pub fn display_path(&self, descriptor: &ModuleDescriptor) -> String {
        match self.path_from_descriptor(descriptor) {
            Ok(full_path) => {
                // Try to make it relative to the src dir
                match full_path.strip_prefix(&self.src_dir) {
                    Ok(relative_path) => relative_path.to_string_lossy().to_string(),
                    Err(_) => {
                        // If it's not under src dir, just use the full path
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
    fn load_module(
        &mut self,
        descriptor: &ModuleDescriptor,
        strict: bool,
    ) -> Result<ModuleId, ImportError> {
        // Check if this module is already known (pre-registered or loaded).
        let preassigned_id = if let Some(&module_id) = self.module_map.get(&descriptor) {
            match self.get_module_by_id(module_id) {
                LoadState::Loading => return Err(ImportError::Circular(module_id)),
                LoadState::Registered => {
                    // Pre-registered but not loaded yet. Continue loading with this ID.
                    Some(module_id)
                }
                _ => return Ok(module_id), // Already loaded (Ok, Error, None)
            }
        } else {
            None
        };

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
        // Prelude always gets ModuleId::PRELUDE. Other modules get subsequent IDs.
        let is_prelude = matches!(descriptor, ModuleDescriptor::Name(parts) if parts.len() == 1 && parts[0] == "prelude");

        let module_id = if let Some(id) = preassigned_id {
            // Use the pre-assigned ID, transition state to Loading
            self.modules[id.get() as usize] = Module::new(descriptor.clone());
            id
        } else if is_prelude {
            // Prelude always gets the reserved slot
            if self.modules.is_empty() {
                self.modules.push(Module::new(descriptor.clone()));
            } else {
                // Slot was reserved; update it
                self.modules[ModuleId::PRELUDE.get() as usize] = Module::new(descriptor.clone());
            }
            ModuleId::PRELUDE
        } else {
            // Non-prelude modules: reserve slot 0 for prelude if not already done
            if self.modules.is_empty() {
                self.modules.push(Module::anonymous());
            }
            let id = ModuleId(self.modules.len() as u16);
            self.modules.push(Module::new(descriptor.clone()));
            id
        };
        self.module_map.insert(descriptor.clone(), module_id);

        let mut env = Environment::new(module_id);
        if !is_prelude {
            let prelude_descriptor = ModuleDescriptor::name("prelude");
            // Try to load prelude, but don't fail if it doesn't exist
            if let Ok(prelude_id) = self.load_module(&prelude_descriptor, false) {
                if let Some(prelude_bindings) = self.get_bindings(prelude_id) {
                    // Silently ignore errors when importing prelude
                    let _ = env.bindings.import_prelude(prelude_bindings, self);
                }
            }
        }

        let tokens = Token::scan(&text);
        if let Err(e) = env.add_tokens(self, tokens, strict) {
            if e.circular.is_some() {
                let err = Err(ImportError::Circular(module_id));
                self.modules[module_id.get() as usize].load_error(e);
                return err;
            }
            self.modules[module_id.get() as usize].load_error(e);
            return Ok(module_id);
        }

        // Normalize all facts after elaboration.
        // We ignore errors here since some facts may intentionally fail to normalize
        // (e.g., exists over uninhabited types in test cases).
        let _ = env.run_normalization_pass(self);

        // Compute simple blake3 hash of just the file contents
        let content_hash = blake3::hash(text.as_bytes());
        self.modules[module_id.get() as usize].load_ok(env, content_hash);
        Ok(module_id)
    }

    pub fn load_module_by_name(&mut self, module_name: &str) -> Result<ModuleId, ImportError> {
        let descriptor = ModuleDescriptor::name(module_name);
        self.load_module(&descriptor, false)
    }

    #[cfg(test)]
    pub fn load_module_by_name_strict(
        &mut self,
        module_name: &str,
        strict: bool,
    ) -> Result<ModuleId, ImportError> {
        let descriptor = ModuleDescriptor::name(module_name);
        self.load_module(&descriptor, strict)
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

    /// Find a verified certificate for the given goal.
    /// Returns the first certificate that successfully verifies against the current code.
    /// Returns None if no valid certificate exists in the build cache.
    pub fn find_cert(
        &self,
        goal: &Goal,
        root_env: &Environment,
        goal_env: &Environment,
        cursor: &crate::elaborator::node::NodeCursor,
    ) -> Option<(&Certificate, Vec<CertificateLine>)> {
        let descriptor = self.get_module_descriptor(goal.module_id)?;
        let cert_store = self.build_cache.get_certificates(descriptor)?;

        let mut processor = match Processor::with_imports(None, root_env) {
            Ok(p) => p,
            Err(_) => return None,
        };
        if processor.add_module_facts(cursor).is_err() {
            return None;
        }

        // Try each certificate with a matching goal name
        for cert in &cert_store.certs {
            if cert.goal == goal.name {
                // Try to verify this certificate
                let normalized_goal = cursor.normalized_goal()?;
                if let Ok(steps) = processor.check_cert(
                    cert,
                    Some(normalized_goal),
                    &normalized_goal.normalizer,
                    self,
                    &goal_env.bindings,
                ) {
                    return Some((cert, steps));
                }
            }
        }

        None
    }

    /// Handle a selection request for a given file and line number.
    /// Returns (goal_name, goal_range, steps) or an error message.
    pub fn handle_selection(
        &self,
        path: &Path,
        selected_line: u32,
    ) -> Result<
        (
            Vec<crate::interfaces::GoalInfo>,
            Option<tower_lsp::lsp_types::Range>,
        ),
        String,
    > {
        let descriptor = self
            .descriptor_from_path(path)
            .map_err(|e| format!("descriptor_from_path failed: {:?}", e))?;

        let env = match self.get_module(&descriptor) {
            LoadState::Ok(env) => env,
            _ => return Err(format!("could not load module from {:?}", descriptor)),
        };

        let node_path = env
            .path_for_line(selected_line)
            .map_err(|e| format!("path_for_line failed: {}", e))?;

        let cursor = crate::elaborator::node::NodeCursor::from_path(env, &node_path);

        // Try to get the goal directly from this node (if it's a Claim node)
        // or find all block-level goal nodes if this is a Block node
        let mut goal_infos = vec![];
        let mut goal_range = None;

        if let Some(goal) = cursor.goal() {
            // Single goal node
            goal_range = Some(goal.proposition.source.range);
            let goal_env = cursor
                .goal_env()
                .map_err(|e| format!("goal_env failed: {}", e))?;
            let goal_info = self.create_goal_info(goal, env, goal_env, &cursor);
            goal_infos.push(goal_info);
        } else if let Some(block) = cursor.node().get_block() {
            // This is a Block node - collect ALL block-level goal children
            let goal_indices: Vec<usize> = block
                .env
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(i, node)| {
                    if node.is_block_level_goal() {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect();

            if goal_indices.is_empty() {
                return Err("no goal at this location".to_string());
            }

            // Process each goal
            for goal_index in goal_indices {
                // Create a new cursor for each goal
                let mut goal_cursor =
                    crate::elaborator::node::NodeCursor::from_path(env, &node_path);
                goal_cursor.descend(goal_index);

                let goal = goal_cursor
                    .goal()
                    .ok_or_else(|| "failed to get goal from goal node".to_string())?;

                // Use the first goal's range for the overall goal_range
                if goal_range.is_none() {
                    goal_range = Some(goal.proposition.source.range);
                }

                let goal_env = goal_cursor
                    .goal_env()
                    .map_err(|e| format!("goal_env failed: {}", e))?;

                let goal_info = self.create_goal_info(&goal, env, goal_env, &goal_cursor);
                goal_infos.push(goal_info);
            }
        } else {
            return Err("no goal at this location".to_string());
        }

        Ok((goal_infos, goal_range))
    }

    // Helper function to create a GoalInfo from a goal, its environment, and cursor
    fn create_goal_info(
        &self,
        goal: &crate::elaborator::goal::Goal,
        root_env: &crate::elaborator::environment::Environment,
        goal_env: &crate::elaborator::environment::Environment,
        cursor: &crate::elaborator::node::NodeCursor,
    ) -> GoalInfo {
        let goal_name = goal.name.clone();

        // Check if there's a verified certificate for this goal
        let (has_cached_proof, steps) = if let Some((_cert, certificate_steps)) =
            self.find_cert(goal, root_env, goal_env, cursor)
        {
            // Convert certificate lines to interface::Step objects
            let steps: Vec<Step> = certificate_steps
                .into_iter()
                .map(|cert_step| {
                    let location = match &cert_step.reason {
                        StepReason::Assumption(source) | StepReason::Skolemization(source) => self
                            .path_from_module_id(source.module_id)
                            .and_then(|path| tower_lsp::lsp_types::Url::from_file_path(path).ok())
                            .map(|uri| Location {
                                uri,
                                range: source.range,
                            }),
                        _ => None,
                    };
                    let reason = cert_step.reason.description();

                    // Pretty-print the statement by parsing and formatting it
                    let statement = Statement::parse_str_with_options(&cert_step.statement, true)
                        .map(|s| s.to_string())
                        .unwrap_or(cert_step.statement);

                    Step {
                        statement,
                        reason,
                        location,
                    }
                })
                .collect();

            (true, Some(steps))
        } else {
            (false, None)
        };

        GoalInfo {
            goal_name,
            has_cached_proof,
            steps,
        }
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
        use crate::{
            code_generator::CodeGenerator, elaborator::evaluator::Evaluator,
            syntax::expression::Expression,
        };

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
        let node = env.get_node_by_goal_name(theorem_name);
        let goal_context = node.goal().unwrap();
        let value = &goal_context.proposition.value;
        let fake_input = format!("<{}>", theorem_name);
        CodeGenerator::expect(&node.env().bindings, &fake_input, &value, expected);
    }
}
