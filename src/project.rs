use core::panic;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc};
use std::time::Duration;
use std::{fmt, io};

use regex::Regex;
use toml_edit::{value, DocumentMut};
use tower_lsp::lsp_types::{self, CompletionItem, Hover, HoverContents, MarkedString, Url};
use walkdir::WalkDir;

use crate::build_cache::BuildCache;
use crate::certificate::{Certificate, CertificateLine};
use crate::code_generator::{self, CodeGenerator};
use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::environment::Environment;
use crate::elaborator::error::{self, Error, ErrorContext};
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::lowered_module::{
    LoweredGoalEntry, LoweredGoalId, LoweredModule, ModuleExport,
};
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::interfaces::{CitationInfo, GoalInfo, Location, Step};
use crate::kernel::checker::StepReason;
use crate::loader::module_loader::elaborate_and_lower_module;
use crate::loader::parsed_module::ParsedModule;
use crate::loader::source::read_source_text;
use crate::manifest::{Manifest, ManifestError};
use crate::module::{LoadState, LoadedModule, Module, ModuleDescriptor, ModuleId};
use crate::processor::Processor;
use crate::proof_display::display_certificate_lines;
use crate::syntax::statement::StatementInfo;
use crate::syntax::token::Token;
use crate::syntax::token_map::TokenInfo;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryCitation {
    pub path: String,
    pub line: u32,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SelectionInfo {
    Goals {
        goal_infos: Vec<GoalInfo>,
        goal_range: Option<lsp_types::Range>,
    },
    Citation(CitationInfo),
}

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

    // Errors from dependency preloading, keyed by the source import name.
    // Import elaboration uses this to report the original load error at the import statement
    // without recursively loading modules during elaboration.
    dependency_load_errors: HashMap<String, ImportError>,

    // The module names that we want to build.
    pub targets: HashSet<ModuleDescriptor>,

    // Targets that should be elaborated but not proved. This is used for pending/
    // files that record intended theorem statements and proof attempts.
    surface_check_targets: HashSet<ModuleDescriptor>,

    // The last known-good build cache.
    // This is different from the Builder's build cache, which is created during a build.
    pub build_cache: Arc<BuildCache>,

    // Time spent loading the build cache during project creation.
    pub cache_load_time: Duration,

    // A flag for whether something is using the project to build right now.
    // Only used in the parallel server code.
    pub building: bool,
}

struct ParallelModuleLoadJob {
    descriptor: ModuleDescriptor,
    module_id: ModuleId,
    parsed: Option<ParsedModule>,
    is_prelude: bool,
    dependencies: Vec<ModuleId>,
    lib_dependencies: Vec<(ModuleId, Vec<String>)>,
}

struct ParallelModuleWorkerJob {
    index: usize,
    module_id: ModuleId,
    parsed: ParsedModule,
    is_prelude: bool,
    lib_dependencies: Vec<(ModuleId, Vec<String>)>,
    project: ProjectView,
    usage_mode: UsageMode,
}

struct ParallelModuleLoadResult {
    index: usize,
    module_id: ModuleId,
    loaded: Result<crate::loader::module_loader::LoadedModuleParts, error::Error>,
}

pub struct ParallelProjectLoader {
    jobs: Vec<ParallelModuleLoadJob>,
    remaining_dependencies: Vec<usize>,
    dependents: Vec<Vec<usize>>,
    ready: Vec<usize>,
    job_tx: Option<mpsc::Sender<ParallelModuleWorkerJob>>,
    result_rx: mpsc::Receiver<ParallelModuleLoadResult>,
    handles: Vec<std::thread::JoinHandle<()>>,
    active_jobs: usize,
    completed_jobs: usize,
    worker_count: usize,
}

/// Read-only project operations needed while evaluating expressions and replaying certificates.
pub trait ProjectLookup: Sync {
    fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap>;
    fn get_module_export(&self, module_id: ModuleId) -> Option<&ModuleExport>;
    fn get_module_descriptor(&self, module_id: ModuleId) -> Option<&ModuleDescriptor>;
    fn get_module_id_by_name(&self, module_name: &str) -> Option<ModuleId>;
    fn get_loaded_module_id_by_name(&self, module_name: &str) -> Result<ModuleId, ImportError>;
    fn package_role(&self, module_id: ModuleId) -> PackageRole;
    fn validate_import_visibility(
        &self,
        importer: ModuleId,
        imported: ModuleId,
    ) -> Result<(), String>;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageRole {
    Outside,
    Interface,
    Implementation,
}

const PACKAGE_INTERFACE_FILE: &str = "interface.ac";
const CERTS_DIR: &str = "certs";

fn path_has_certs_component(path: &Path) -> bool {
    path.components()
        .any(|component| component.as_os_str() == CERTS_DIR)
}

#[derive(Clone)]
struct PackageSignature {
    text: String,
    axiomatic_theorem: bool,
    first_token: Token,
    last_token: Token,
}

#[derive(Clone)]
enum ProjectViewModuleState {
    Registered,
    Loading,
    Error(Arc<error::Error>),
    Ok(Arc<ModuleExport>),
}

pub enum ProjectViewModule<'a> {
    None,
    Registered,
    Loading,
    Error(&'a error::Error),
    Ok(&'a ModuleExport),
}

/// Owned read-only snapshot of project state used while checking or proving modules.
///
/// Cloning this value is cheap: the snapshot maps and module exports are shared through `Arc`.
#[derive(Clone)]
pub struct ProjectView {
    config: ProjectConfig,
    src_dir: Arc<PathBuf>,
    build_dir: Arc<PathBuf>,
    build_cache: Arc<BuildCache>,
    targets: Arc<HashSet<ModuleDescriptor>>,
    surface_check_targets: Arc<HashSet<ModuleDescriptor>>,
    module_states: Arc<HashMap<ModuleDescriptor, ProjectViewModuleState>>,
    module_map: Arc<HashMap<ModuleDescriptor, ModuleId>>,
    module_descriptors: Arc<HashMap<ModuleId, ModuleDescriptor>>,
    module_exports: Arc<HashMap<ModuleId, Arc<ModuleExport>>>,
    lowered_modules: Arc<HashMap<ModuleDescriptor, Arc<LoweredModule>>>,
    content_hashes: Arc<HashMap<ModuleId, blake3::Hash>>,
    dependency_load_errors: Arc<HashMap<String, ImportError>>,
    open_file_paths: Arc<HashSet<PathBuf>>,
    open_file_versions: Arc<HashMap<PathBuf, i32>>,
}

impl ProjectView {
    pub fn new(project: &Project) -> Self {
        Self::new_internal(project, true)
    }

    pub fn new_for_targets(project: &Project, targets: HashSet<ModuleDescriptor>) -> Self {
        let mut view = Self::new(project);
        view.targets = Arc::new(targets);
        view
    }

    pub fn new_without_lowered(project: &Project) -> Self {
        Self::new_internal(project, false)
    }

    fn new_internal(project: &Project, include_lowered: bool) -> Self {
        let mut module_states = HashMap::new();
        let mut module_descriptors = HashMap::new();
        let mut module_exports = HashMap::new();
        let mut lowered_modules = HashMap::new();
        let mut content_hashes = HashMap::new();

        for (index, module) in project.modules.iter().enumerate() {
            let module_id = ModuleId(index as u16);
            module_descriptors.insert(module_id, module.descriptor.clone());
            let state = match &module.state {
                LoadState::None => continue,
                LoadState::Registered => ProjectViewModuleState::Registered,
                LoadState::Loading => ProjectViewModuleState::Loading,
                LoadState::Error(error) => ProjectViewModuleState::Error(Arc::new(error.clone())),
                LoadState::Ok(loaded) => {
                    module_exports.insert(module_id, Arc::clone(&loaded.export));
                    if include_lowered {
                        if let Some(lowered) = &loaded.lowered {
                            lowered_modules.insert(module.descriptor.clone(), Arc::clone(lowered));
                        }
                    }
                    ProjectViewModuleState::Ok(Arc::clone(&loaded.export))
                }
            };
            module_states.insert(module.descriptor.clone(), state);
            if let Some(hash) = module.hash {
                content_hashes.insert(module_id, hash);
            }
        }

        Self {
            config: project.config.clone(),
            src_dir: Arc::new(project.src_dir.clone()),
            build_dir: Arc::new(project.build_dir.clone()),
            build_cache: Arc::clone(&project.build_cache),
            targets: Arc::new(project.targets.clone()),
            surface_check_targets: Arc::new(project.surface_check_targets.clone()),
            module_states: Arc::new(module_states),
            module_map: Arc::new(project.module_map.clone()),
            module_descriptors: Arc::new(module_descriptors),
            module_exports: Arc::new(module_exports),
            lowered_modules: Arc::new(lowered_modules),
            content_hashes: Arc::new(content_hashes),
            dependency_load_errors: Arc::new(project.dependency_load_errors.clone()),
            open_file_paths: Arc::new(project.open_files.keys().cloned().collect()),
            open_file_versions: Arc::new(
                project
                    .open_files
                    .iter()
                    .map(|(path, (_, version))| (path.clone(), *version))
                    .collect(),
            ),
        }
    }

    pub fn config(&self) -> &ProjectConfig {
        &self.config
    }

    pub fn build_dir(&self) -> &PathBuf {
        &self.build_dir
    }

    pub fn src_dir(&self) -> &PathBuf {
        &self.src_dir
    }

    pub fn build_cache(&self) -> &BuildCache {
        &self.build_cache
    }

    pub fn targets(&self) -> &HashSet<ModuleDescriptor> {
        &self.targets
    }

    pub fn get_module(&self, descriptor: &ModuleDescriptor) -> ProjectViewModule<'_> {
        match self.module_states.get(descriptor) {
            Some(ProjectViewModuleState::Registered) => ProjectViewModule::Registered,
            Some(ProjectViewModuleState::Loading) => ProjectViewModule::Loading,
            Some(ProjectViewModuleState::Error(error)) => ProjectViewModule::Error(error),
            Some(ProjectViewModuleState::Ok(export)) => ProjectViewModule::Ok(export),
            None => ProjectViewModule::None,
        }
    }

    pub fn get_module_export(&self, module_id: ModuleId) -> Option<&ModuleExport> {
        self.module_exports
            .get(&module_id)
            .map(|export| export.as_ref())
    }

    pub fn get_lowered_module(&self, descriptor: &ModuleDescriptor) -> Option<&LoweredModule> {
        self.lowered_modules
            .get(descriptor)
            .map(|lowered| lowered.as_ref())
    }

    pub fn is_surface_check_target(&self, descriptor: &ModuleDescriptor) -> bool {
        self.surface_check_targets.contains(descriptor)
    }

    pub fn is_surface_check_module(&self, module_id: ModuleId) -> bool {
        self.get_module_descriptor(module_id)
            .is_some_and(|descriptor| self.is_surface_check_target(descriptor))
    }

    pub fn get_module_content_hash(&self, module_id: ModuleId) -> Option<blake3::Hash> {
        self.content_hashes.get(&module_id).copied()
    }

    pub fn display_path(&self, descriptor: &ModuleDescriptor) -> String {
        let normalize = |path: &Path| path.to_string_lossy().replace('\\', "/");
        match self.path_from_descriptor(descriptor) {
            Ok(full_path) => match full_path.strip_prefix(self.src_dir.as_ref()) {
                Ok(relative_path) => normalize(relative_path),
                Err(_) => normalize(&full_path),
            },
            Err(_) => descriptor.to_string(),
        }
    }

    pub fn url_from_descriptor(&self, descriptor: &ModuleDescriptor) -> Option<Url> {
        let path = self.path_from_descriptor(descriptor).ok()?;
        Url::from_file_path(path).ok()
    }

    // Yields (url, version) for all open files.
    pub fn open_urls(&self) -> impl Iterator<Item = (Url, i32)> + '_ {
        self.open_file_versions
            .iter()
            .filter_map(|(path, version)| {
                Url::from_file_path(path.clone())
                    .ok()
                    .map(|url| (url, *version))
            })
    }

    pub fn descriptor_from_path(&self, path: &Path) -> Result<ModuleDescriptor, ImportError> {
        let relative = match path.strip_prefix(self.src_dir.as_ref()) {
            Ok(relative) => relative,
            Err(_) => return Ok(ModuleDescriptor::File(path.to_path_buf())),
        };
        let components: Vec<_> = relative
            .components()
            .map(|comp| comp.as_os_str().to_string_lossy())
            .collect();
        let package_root = self.nearest_package_root_for_path(path);
        let mut parts = Vec::new();
        for (i, component) in components.iter().enumerate() {
            let part = if i + 1 == components.len() {
                if !component.ends_with(".ac") {
                    return Err(ImportError::NotFound(format!(
                        "path {} does not end with .ac",
                        path.display()
                    )));
                }
                if component == PACKAGE_INTERFACE_FILE
                    && package_root
                        .as_ref()
                        .is_some_and(|root| path == root.join(PACKAGE_INTERFACE_FILE))
                {
                    break;
                }
                if component == "default.ac" && i > 0 && package_root.is_none() {
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

    fn path_from_module_name(&self, module_name: &str) -> Result<PathBuf, ImportError> {
        let mut path = self.src_dir.as_ref().clone();
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            check_valid_module_part(part, module_name)?;

            if i + 1 == parts.len() {
                let file_path = path.join(format!("{}.ac", part));
                let dir_path = path.join(part).join("default.ac");
                let interface_path = path.join(part).join(PACKAGE_INTERFACE_FILE);

                let file_exists = self.module_path_exists(&file_path);
                let dir_exists = self.module_path_exists(&dir_path);
                let interface_exists = self.module_path_exists(&interface_path);

                if interface_exists {
                    if file_exists {
                        return Err(ImportError::NotFound(format!(
                            "ambiguous module '{}': both {} and package interface {} exist",
                            module_name,
                            file_path.display(),
                            interface_path.display()
                        )));
                    }
                    return Ok(interface_path);
                } else if file_exists && dir_exists {
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
                    return Ok(file_path);
                }
            } else {
                path.push(part.to_string());
            }
        }
        unreachable!("should have returned in the loop")
    }

    fn module_path_exists(&self, path: &Path) -> bool {
        if self.config.use_filesystem {
            path.exists()
        } else {
            self.open_file_paths.contains(path)
        }
    }

    fn nearest_package_root_for_path(&self, path: &Path) -> Option<PathBuf> {
        let mut current = path.parent()?;
        while current != self.src_dir.as_ref().as_path() {
            if self.module_path_exists(&current.join(PACKAGE_INTERFACE_FILE)) {
                return Some(current.to_path_buf());
            }
            current = current.parent()?;
        }
        None
    }

    fn package_role_for_path(&self, path: &Path) -> PackageRole {
        let Some(package_root) = self.nearest_package_root_for_path(path) else {
            return PackageRole::Outside;
        };
        if path == package_root.join(PACKAGE_INTERFACE_FILE) {
            PackageRole::Interface
        } else {
            PackageRole::Implementation
        }
    }

    fn package_root_for_module(&self, module_id: ModuleId) -> Option<PathBuf> {
        let descriptor = self.get_module_descriptor(module_id)?;
        let path = self.path_from_descriptor(descriptor).ok()?;
        self.nearest_package_root_for_path(&path)
    }

    fn package_role_for_module(&self, module_id: ModuleId) -> PackageRole {
        let Some(descriptor) = self.get_module_descriptor(module_id) else {
            return PackageRole::Outside;
        };
        self.package_role_for_descriptor(descriptor)
    }

    fn package_role_for_descriptor(&self, descriptor: &ModuleDescriptor) -> PackageRole {
        let Ok(path) = self.path_from_descriptor(descriptor) else {
            return PackageRole::Outside;
        };
        self.package_role_for_path(&path)
    }

    fn canonicalize_name_descriptor(&self, descriptor: &ModuleDescriptor) -> ModuleDescriptor {
        let ModuleDescriptor::Name(_) = descriptor else {
            return descriptor.clone();
        };

        let Ok(path) = self.path_from_descriptor(descriptor) else {
            return descriptor.clone();
        };

        if !self.module_path_exists(&path) {
            return descriptor.clone();
        }

        self.descriptor_from_path(&path)
            .unwrap_or_else(|_| descriptor.clone())
    }

    pub fn all_dependencies(&self, original_module_id: ModuleId) -> Vec<ModuleId> {
        let mut answer = vec![];
        let mut seen = HashSet::new();
        self.append_dependencies(&mut seen, &mut answer, original_module_id);
        answer
    }

    fn append_dependencies(
        &self,
        seen: &mut HashSet<ModuleId>,
        output: &mut Vec<ModuleId>,
        module_id: ModuleId,
    ) -> bool {
        if !seen.insert(module_id) {
            return false;
        }
        if let Some(bindings) = self.get_bindings(module_id) {
            for dep in bindings.direct_dependencies() {
                if self.append_dependencies(seen, output, dep) {
                    output.push(dep);
                }
            }
        }
        true
    }
}

impl ProjectLookup for ProjectView {
    fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        self.module_exports
            .get(&module_id)
            .map(|export| &export.bindings)
    }

    fn get_module_export(&self, module_id: ModuleId) -> Option<&ModuleExport> {
        ProjectView::get_module_export(self, module_id)
    }

    fn get_module_descriptor(&self, module_id: ModuleId) -> Option<&ModuleDescriptor> {
        self.module_descriptors.get(&module_id)
    }

    fn get_module_id_by_name(&self, module_name: &str) -> Option<ModuleId> {
        let descriptor = ModuleDescriptor::name(module_name);
        let canonical_descriptor = self.canonicalize_name_descriptor(&descriptor);
        self.module_map.get(&canonical_descriptor).copied()
    }

    fn get_loaded_module_id_by_name(&self, module_name: &str) -> Result<ModuleId, ImportError> {
        let descriptor = ModuleDescriptor::name(module_name);
        let canonical_descriptor = self.canonicalize_name_descriptor(&descriptor);
        let Some(&module_id) = self.module_map.get(&canonical_descriptor) else {
            if let Some(error) = self.dependency_load_errors.get(module_name) {
                return Err(error.clone());
            }
            return Err(ImportError::NotFound(format!(
                "module '{}' has not been loaded",
                module_name
            )));
        };
        match self.module_states.get(&canonical_descriptor) {
            Some(ProjectViewModuleState::Loading) => Err(ImportError::Circular(module_id)),
            Some(ProjectViewModuleState::Registered) | None => {
                if let Some(error) = self.dependency_load_errors.get(module_name) {
                    return Err(error.clone());
                }
                Err(ImportError::NotFound(format!(
                    "module '{}' has not been loaded",
                    module_name
                )))
            }
            Some(ProjectViewModuleState::Error(error)) if error.circular.is_some() => {
                Err(ImportError::Circular(module_id))
            }
            Some(ProjectViewModuleState::Error(_)) | Some(ProjectViewModuleState::Ok(_)) => {
                Ok(module_id)
            }
        }
    }

    fn package_role(&self, module_id: ModuleId) -> PackageRole {
        self.package_role_for_module(module_id)
    }

    fn validate_import_visibility(
        &self,
        importer: ModuleId,
        imported: ModuleId,
    ) -> Result<(), String> {
        if self.package_role_for_module(imported) != PackageRole::Implementation {
            return Ok(());
        }
        if self.package_role_for_module(importer) != PackageRole::Implementation {
            return Err(format!(
                "module '{}' is private to its package",
                self.get_module_descriptor(imported)
                    .map(|descriptor| descriptor.to_string())
                    .unwrap_or_else(|| imported.to_string())
            ));
        }
        if self.package_root_for_module(importer) == self.package_root_for_module(imported) {
            Ok(())
        } else {
            Err(format!(
                "module '{}' is private to its package",
                self.get_module_descriptor(imported)
                    .map(|descriptor| descriptor.to_string())
                    .unwrap_or_else(|| imported.to_string())
            ))
        }
    }
}

impl From<&Project> for ProjectView {
    fn from(project: &Project) -> Self {
        Self::new(project)
    }
}

impl From<&ProjectView> for ProjectView {
    fn from(project: &ProjectView) -> Self {
        project.clone()
    }
}

impl ProjectLookup for Project {
    fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        Project::get_bindings(self, module_id)
    }

    fn get_module_export(&self, module_id: ModuleId) -> Option<&ModuleExport> {
        Project::get_module_export(self, module_id)
    }

    fn get_module_descriptor(&self, module_id: ModuleId) -> Option<&ModuleDescriptor> {
        Project::get_module_descriptor(self, module_id)
    }

    fn get_module_id_by_name(&self, module_name: &str) -> Option<ModuleId> {
        Project::get_module_id_by_name(self, module_name)
    }

    fn get_loaded_module_id_by_name(&self, module_name: &str) -> Result<ModuleId, ImportError> {
        Project::get_loaded_module_id_by_name(self, module_name)
    }

    fn package_role(&self, module_id: ModuleId) -> PackageRole {
        self.package_role_for_module(module_id)
    }

    fn validate_import_visibility(
        &self,
        importer: ModuleId,
        imported: ModuleId,
    ) -> Result<(), String> {
        if self.package_role_for_module(imported) != PackageRole::Implementation {
            return Ok(());
        }
        if self.package_role_for_module(importer) != PackageRole::Implementation {
            return Err(format!(
                "module '{}' is private to its package",
                self.get_module_descriptor(imported)
                    .map(|descriptor| descriptor.to_string())
                    .unwrap_or_else(|| imported.to_string())
            ));
        }
        if self.package_root_for_module(importer) == self.package_root_for_module(imported) {
            Ok(())
        } else {
            Err(format!(
                "module '{}' is private to its package",
                self.get_module_descriptor(imported)
                    .map(|descriptor| descriptor.to_string())
                    .unwrap_or_else(|| imported.to_string())
            ))
        }
    }
}

impl ParallelProjectLoader {
    pub fn new(
        project: &mut Project,
        targets: &[ModuleDescriptor],
        load_order: &[ModuleDescriptor],
        worker_count: usize,
    ) -> Result<Self, ImportError> {
        project.register_all_modules();

        let target_set: HashSet<_> = targets.iter().cloned().collect();
        let mut jobs = Vec::new();
        for descriptor in load_order {
            if !target_set.contains(descriptor) {
                continue;
            }
            if let Some(job) = project.prepare_parallel_module_load_job(descriptor, false)? {
                jobs.push(job);
            }
        }

        let module_to_job: HashMap<ModuleId, usize> = jobs
            .iter()
            .enumerate()
            .map(|(index, job)| (job.module_id, index))
            .collect();
        let mut remaining_dependencies = vec![0usize; jobs.len()];
        let mut dependents = vec![Vec::new(); jobs.len()];
        for (job_index, job) in jobs.iter().enumerate() {
            for dep_id in &job.dependencies {
                if let Some(&dep_index) = module_to_job.get(dep_id) {
                    remaining_dependencies[job_index] += 1;
                    dependents[dep_index].push(job_index);
                }
            }
        }

        let ready = remaining_dependencies
            .iter()
            .enumerate()
            .filter_map(|(index, &remaining)| (remaining == 0).then_some(index))
            .collect::<Vec<_>>();
        if !jobs.is_empty() && ready.is_empty() {
            return Err(ImportError::Circular(jobs[0].module_id));
        }

        let worker_count = worker_count.min(jobs.len()).max(1);
        let (job_tx, job_rx) = mpsc::channel();
        let job_rx = Arc::new(std::sync::Mutex::new(job_rx));
        let (result_tx, result_rx) = mpsc::channel();
        let mut handles = Vec::new();

        for _ in 0..worker_count {
            let job_rx = Arc::clone(&job_rx);
            let result_tx = result_tx.clone();
            handles.push(std::thread::spawn(move || loop {
                let job: ParallelModuleWorkerJob = {
                    let receiver = job_rx.lock().expect("parallel load job receiver poisoned");
                    match receiver.recv() {
                        Ok(job) => job,
                        Err(_) => break,
                    }
                };
                let loaded = elaborate_and_lower_module(
                    &job.project,
                    job.usage_mode,
                    job.module_id,
                    job.parsed,
                    job.is_prelude,
                    job.lib_dependencies,
                );
                if result_tx
                    .send(ParallelModuleLoadResult {
                        index: job.index,
                        module_id: job.module_id,
                        loaded,
                    })
                    .is_err()
                {
                    break;
                }
            }));
        }
        drop(result_tx);

        let mut loader = Self {
            jobs,
            remaining_dependencies,
            dependents,
            ready,
            job_tx: Some(job_tx),
            result_rx,
            handles,
            active_jobs: 0,
            completed_jobs: 0,
            worker_count,
        };
        loader.enqueue_available(project);
        Ok(loader)
    }

    fn enqueue_available(&mut self, project: &Project) {
        while self.active_jobs < self.worker_count {
            let Some(job_index) = project.pop_ready_parallel_load_job(&mut self.ready, &self.jobs)
            else {
                break;
            };
            let Some(sender) = &self.job_tx else {
                break;
            };
            project.enqueue_parallel_load_job(&mut self.jobs, job_index, sender);
            self.active_jobs += 1;
        }
    }

    pub fn next_loaded_modules(
        &mut self,
        project: &mut Project,
        targets: &[ModuleDescriptor],
    ) -> Result<Option<Vec<(ModuleDescriptor, LoweredModule)>>, ImportError> {
        loop {
            if self.completed_jobs >= self.jobs.len() {
                self.finish_workers();
                return Ok(None);
            }
            if self.active_jobs == 0 && self.ready.is_empty() {
                self.finish_workers();
                let module_id = self
                    .jobs
                    .iter()
                    .find(|job| job.parsed.is_some())
                    .map(|job| job.module_id)
                    .unwrap_or(self.jobs[0].module_id);
                return Err(ImportError::Circular(module_id));
            }

            let result = self
                .result_rx
                .recv()
                .expect("parallel load workers should return all active jobs");
            self.active_jobs = self.active_jobs.saturating_sub(1);
            self.completed_jobs += 1;
            match result.loaded {
                Ok(loaded) => {
                    let descriptor = self.jobs[result.index].descriptor.clone();
                    project.modules[result.module_id.get() as usize].load_ok(
                        loaded.export,
                        Some(loaded.lowered),
                        loaded.retained_env,
                        loaded.content_hash,
                    );
                    if project
                        .path_from_descriptor(&descriptor)
                        .ok()
                        .is_some_and(|path| {
                            project.package_role_for_path(&path) == PackageRole::Interface
                        })
                    {
                        if let Err(error) = project.validate_package_implementations(&descriptor) {
                            project.modules[result.module_id.get() as usize].load_error(error);
                        }
                    }
                }
                Err(e) => {
                    project.modules[result.module_id.get() as usize].load_error(e);
                }
            }

            for dependent in &self.dependents[result.index] {
                self.remaining_dependencies[*dependent] -= 1;
                if self.remaining_dependencies[*dependent] == 0 {
                    self.ready.push(*dependent);
                }
            }
            self.enqueue_available(project);

            let work = project.take_lowered_modules_for_targets(targets);
            if !work.is_empty() {
                return Ok(Some(work));
            }
        }
    }

    fn finish_workers(&mut self) {
        self.job_tx.take();
        for handle in self.handles.drain(..) {
            let _ = handle.join();
        }
    }
}

impl Drop for ParallelProjectLoader {
    fn drop(&mut self) {
        self.finish_workers();
    }
}

/// The main workflow a project instance is serving.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UsageMode {
    /// Full-library cached certificate replay.
    Check,

    /// Command-line verification, proof search, cache updates, and diagnostics.
    Verify,

    /// Long-lived language-server state for navigation and editor features.
    Ide,
}

impl UsageMode {
    pub fn keeps_ide_metadata(self) -> bool {
        matches!(self, UsageMode::Ide)
    }

    pub fn is_batch(self) -> bool {
        matches!(self, UsageMode::Check | UsageMode::Verify)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn mock_verify_project_keeps_lowered_module_but_drops_environment() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem goal { true }\n");
        let module_id = project.load_module_by_name("main").unwrap();

        assert!(project.get_lowered_module(module_id).is_some());
        assert!(project.get_env_by_id(module_id).is_none());
    }

    #[test]
    fn mock_ide_project_retains_environment() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/main.ac", "theorem goal { true }\n");
        let module_id = project.load_module_by_name("main").unwrap();

        assert!(project.get_lowered_module(module_id).is_some());
        assert!(project.get_env_by_id(module_id).is_some());
    }

    #[test]
    fn project_error_formats_manifest_version_for_callers() {
        let too_new = ProjectError::from(ManifestError::VersionTooNew {
            found: 25,
            supported: 24,
        });

        assert_eq!(
            too_new.cli_message(),
            "This version of acornlib uses project format 25, but this version of the acorn binary only supports up to project format 24. Please run `acorn --update`."
        );
        assert_eq!(
            too_new.vscode_message(),
            "This version of acornlib uses project format 25, but this version of the Acorn VS Code extension only supports up to project format 24. Please update the Acorn VS Code extension."
        );

        let too_old = ProjectError::from(ManifestError::VersionTooOld {
            found: 22,
            supported: 24,
        });

        assert_eq!(
            too_old.cli_message(),
            "This version of acornlib uses project format 22, but this version of the acorn binary writes project format 24. Please run `acorn verify --update-version` to update acornlib's project format."
        );
        assert_eq!(
            too_old.vscode_message(),
            "This version of acornlib uses project format 22, but this version of the Acorn VS Code extension writes project format 24. Please run `acorn verify --update-version` to update acornlib's project format."
        );
    }

    #[test]
    fn older_manifest_version_is_back_compat_fallback() {
        let temp_dir = tempfile::tempdir().expect("temp directory should be created");
        let src_dir = temp_dir.path().join("src");
        let build_dir = temp_dir.path().join("build");
        fs::create_dir(&src_dir).expect("src directory should be created");
        fs::create_dir(&build_dir).expect("build directory should be created");

        let old_version = Manifest::current_version() - 1;
        fs::write(
            build_dir.join("manifest.json"),
            format!(r#"{{"version":{},"modules":{{}}}}"#, old_version),
        )
        .expect("manifest should be written");

        let error = match Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default())
        {
            Ok(_) => std::panic!("cache writes should require --update-version"),
            Err(error) => error,
        };
        assert!(matches!(
            error,
            ProjectError::Manifest(ManifestError::VersionTooOld { found, supported })
                if found == old_version && supported == Manifest::current_version()
        ));

        let read_only_config = ProjectConfig {
            write_cache: false,
            ..ProjectConfig::default()
        };
        assert!(Project::new(src_dir.clone(), build_dir.clone(), read_only_config).is_ok());

        let update_config = ProjectConfig {
            update_version: true,
            ..ProjectConfig::default()
        };
        assert!(Project::new(src_dir, build_dir, update_config).is_ok());
    }

    #[test]
    fn acorn_toml_project_format_version_is_primary() {
        let temp_dir = tempfile::tempdir().expect("temp directory should be created");
        let src_dir = temp_dir.path().join("src");
        let build_dir = temp_dir.path().join("build");
        fs::create_dir(&src_dir).expect("src directory should be created");
        fs::create_dir(&build_dir).expect("build directory should be created");
        fs::write(
            temp_dir.path().join("acorn.toml"),
            format!("project_format_version = {}\n", Manifest::current_version()),
        )
        .expect("acorn.toml should be written");

        let future_version = Manifest::current_version() + 1;
        fs::write(
            build_dir.join("manifest.json"),
            format!(r#"{{"version":{},"modules":{{}}}}"#, future_version),
        )
        .expect("manifest should be written");

        Project::new(src_dir, build_dir, ProjectConfig::default())
            .expect("acorn.toml project_format_version should override manifest fallback");
    }

    #[test]
    fn older_acorn_toml_project_format_requires_update_version_before_cache_writes() {
        let temp_dir = tempfile::tempdir().expect("temp directory should be created");
        let src_dir = temp_dir.path().join("src");
        let build_dir = temp_dir.path().join("build");
        fs::create_dir(&src_dir).expect("src directory should be created");
        fs::create_dir(&build_dir).expect("build directory should be created");
        let old_version = Manifest::current_version() - 1;
        fs::write(
            temp_dir.path().join("acorn.toml"),
            format!("project_format_version = {}\n", old_version),
        )
        .expect("acorn.toml should be written");

        let error = match Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default())
        {
            Ok(_) => std::panic!("cache writes should require --update-version"),
            Err(error) => error,
        };
        assert!(matches!(
            error,
            ProjectError::Manifest(ManifestError::VersionTooOld { found, supported })
                if found == old_version && supported == Manifest::current_version()
        ));

        let read_only_config = ProjectConfig {
            write_cache: false,
            ..ProjectConfig::default()
        };
        assert!(Project::new(src_dir.clone(), build_dir.clone(), read_only_config).is_ok());

        let update_config = ProjectConfig {
            update_version: true,
            ..ProjectConfig::default()
        };
        assert!(Project::new(src_dir, build_dir, update_config).is_ok());
    }

    #[test]
    fn update_build_cache_writes_project_format_version_to_acorn_toml() {
        let temp_dir = tempfile::tempdir().expect("temp directory should be created");
        let src_dir = temp_dir.path().join("src");
        let build_dir = temp_dir.path().join("build");
        fs::create_dir(&src_dir).expect("src directory should be created");
        fs::create_dir(&build_dir).expect("build directory should be created");
        fs::write(
            temp_dir.path().join("acorn.toml"),
            "# project config\n\n[editor]\nline_width = 100\n",
        )
        .expect("acorn.toml should be written");

        let mut project =
            Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default()).unwrap();
        project.update_build_cache(BuildCache::new(src_dir.clone(), build_dir), false);

        let acorn_toml = fs::read_to_string(temp_dir.path().join("acorn.toml"))
            .expect("acorn.toml should be readable");
        assert!(
            acorn_toml.contains(&format!(
                "project_format_version = {}",
                Manifest::current_version()
            )),
            "acorn.toml did not contain project_format_version:\n{}",
            acorn_toml
        );
        assert!(
            acorn_toml.contains("# project config"),
            "acorn.toml did not preserve comments:\n{}",
            acorn_toml
        );
        assert!(
            acorn_toml.contains("[editor]\nline_width = 100"),
            "acorn.toml did not preserve existing tables:\n{}",
            acorn_toml
        );
        let parsed = acorn_toml
            .parse::<DocumentMut>()
            .expect("updated acorn.toml should remain valid TOML");
        assert_eq!(
            parsed["project_format_version"].as_integer(),
            Some(i64::from(Manifest::current_version()))
        );
    }

    #[test]
    fn batch_drain_keeps_exports_and_drops_module_work() {
        let mut project = Project::new_mock();
        project.mock("/mock/dep.ac", "theorem dep_truth { true }\n");
        project.mock(
            "/mock/main.ac",
            "from dep import dep_truth\ntheorem goal { dep_truth }\n",
        );
        project.add_target_by_name("main").unwrap();
        let main_id = project.get_module_id_by_name("main").unwrap();
        let dep_id = project.get_module_id_by_name("dep").unwrap();

        let mut targets = project.targets.iter().cloned().collect::<Vec<_>>();
        targets.sort();
        let work = project.take_lowered_modules_for_targets(&targets);

        assert!(work
            .iter()
            .any(|(descriptor, _)| descriptor == &ModuleDescriptor::name("main")));
        assert!(project.get_module_export(main_id).is_some());
        assert!(project.get_module_export(dep_id).is_some());
        assert!(project.get_lowered_module(main_id).is_none());
        assert!(project.get_lowered_module(dep_id).is_none());
        assert!(project.get_module_export(dep_id).unwrap().fact_count() > 0);
    }

    #[test]
    fn project_view_preserves_dependency_preload_errors() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "from missing import thing\n");
        let module_id = project.load_module_by_name("main").unwrap();
        assert!(matches!(
            project.get_module_by_id(module_id),
            LoadState::Error(_)
        ));

        let view = ProjectView::new(&project);
        let error = view.get_loaded_module_id_by_name("missing").unwrap_err();
        let error = error.to_string();
        assert!(error.contains("no mocked file for:"), "{error}");
        assert!(error.contains("missing.ac"), "{error}");
    }
}

/// Configuration options for the project.
#[derive(Clone)]
pub struct ProjectConfig {
    // The main workflow this project is serving.
    pub usage_mode: UsageMode,

    // Whether we permit loading files from the filesystem.
    // If false, this indicates we only want mocked files.
    pub use_filesystem: bool,

    // Whether we should read from the cache
    pub read_cache: bool,

    // Whether we should write to the cache
    pub write_cache: bool,

    // Whether cache writes may update an older acornlib project format.
    pub update_version: bool,
}

impl Default for ProjectConfig {
    fn default() -> Self {
        Self {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: true,
            write_cache: true,
            update_version: false,
        }
    }
}

// General project-level errors (file operations, setup, etc.)
#[derive(Debug)]
pub enum ProjectError {
    Message(String),
    Manifest(ManifestError),
}

impl ProjectError {
    pub fn message(message: impl Into<String>) -> Self {
        Self::Message(message.into())
    }

    pub fn is_manifest_version_problem(&self) -> bool {
        matches!(
            self,
            Self::Manifest(
                ManifestError::VersionTooNew { .. } | ManifestError::VersionTooOld { .. }
            )
        )
    }

    pub fn cli_message(&self) -> String {
        match self {
            Self::Manifest(ManifestError::VersionTooNew { found, supported }) => format!(
                "This version of acornlib uses project format {}, but this version of the acorn binary only supports up to project format {}. Please run `acorn --update`.",
                found, supported
            ),
            Self::Manifest(ManifestError::VersionTooOld { found, supported }) => format!(
                "This version of acornlib uses project format {}, but this version of the acorn binary writes project format {}. Please run `acorn verify --update-version` to update acornlib's project format.",
                found, supported
            ),
            _ => self.to_string(),
        }
    }

    pub fn vscode_message(&self) -> String {
        match self {
            Self::Manifest(ManifestError::VersionTooNew { found, supported }) => format!(
                "This version of acornlib uses project format {}, but this version of the Acorn VS Code extension only supports up to project format {}. Please update the Acorn VS Code extension.",
                found, supported
            ),
            Self::Manifest(ManifestError::VersionTooOld { found, supported }) => format!(
                "This version of acornlib uses project format {}, but this version of the Acorn VS Code extension writes project format {}. Please run `acorn verify --update-version` to update acornlib's project format.",
                found, supported
            ),
            _ => self.to_string(),
        }
    }
}

impl From<io::Error> for ProjectError {
    fn from(error: io::Error) -> Self {
        ProjectError::message(format!("{}", error))
    }
}

impl From<ManifestError> for ProjectError {
    fn from(error: ManifestError) -> Self {
        ProjectError::Manifest(error)
    }
}

impl fmt::Display for ProjectError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProjectError::Message(message) => write!(f, "{}", message),
            ProjectError::Manifest(error) => write!(f, "{}", error),
        }
    }
}

// Errors specific to importing modules.
// Each string is a human-readable error message.
#[derive(Clone, Debug)]
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
    fn validate_package_interface_paths(
        src_dir: &Path,
        mut interface_paths: Vec<PathBuf>,
    ) -> Result<(), String> {
        interface_paths.retain(|path| path.strip_prefix(src_dir).is_ok());
        interface_paths.sort();
        interface_paths.dedup();
        interface_paths.sort_by_key(|path| path.components().count());
        let mut package_roots: Vec<PathBuf> = Vec::new();
        for path in interface_paths {
            let Some(package_root) = path.parent() else {
                continue;
            };
            if package_root == src_dir {
                return Err(format!("root {} is not supported", PACKAGE_INTERFACE_FILE));
            }
            if package_roots
                .iter()
                .any(|root| package_root.starts_with(root))
            {
                return Err(format!(
                    "nested packages are not supported: {} is inside package {}",
                    path.strip_prefix(src_dir).unwrap_or(&path).display(),
                    package_roots
                        .iter()
                        .find(|root| package_root.starts_with(root.as_path()))
                        .and_then(|root| root.strip_prefix(src_dir).ok())
                        .unwrap_or(package_root)
                        .display()
                ));
            }
            package_roots.push(package_root.to_path_buf());
            package_roots.sort();
        }
        Ok(())
    }

    fn validate_package_layout(src_dir: &Path) -> Result<(), ProjectError> {
        let mut interface_paths: Vec<PathBuf> = Vec::new();
        for entry in WalkDir::new(src_dir).into_iter().filter_map(Result::ok) {
            let path = entry.path();
            if path_has_certs_component(path) {
                continue;
            }
            if !entry.file_type().is_file()
                || path.file_name().and_then(|name| name.to_str()) != Some(PACKAGE_INTERFACE_FILE)
            {
                continue;
            }
            interface_paths.push(path.to_path_buf());
        }
        Self::validate_package_interface_paths(src_dir, interface_paths)
            .map_err(ProjectError::message)
    }

    fn acorn_toml_path_for_src_dir(src_dir: &Path) -> Option<PathBuf> {
        src_dir.parent().map(|root| root.join("acorn.toml"))
    }

    fn load_project_format_version_from_acorn_toml(
        acorn_toml: &Path,
    ) -> Result<Option<u32>, ProjectError> {
        if !acorn_toml.is_file() {
            return Ok(None);
        }

        let text = std::fs::read_to_string(acorn_toml)?;
        let doc = text.parse::<DocumentMut>().map_err(|error| {
            ProjectError::message(format!("Error parsing {}: {}", acorn_toml.display(), error))
        })?;
        let Some(value) = doc.get("project_format_version") else {
            return Ok(None);
        };
        let Some(version) = value.as_integer() else {
            return Err(ProjectError::message(format!(
                "{}: project_format_version must be a nonnegative integer",
                acorn_toml.display()
            )));
        };
        u32::try_from(version).map(Some).map_err(|_| {
            ProjectError::message(format!(
                "{}: project_format_version must be a nonnegative integer",
                acorn_toml.display()
            ))
        })
    }

    fn load_project_format_version(src_dir: &Path, build_dir: &Path) -> Result<u32, ProjectError> {
        if let Some(acorn_toml) = Self::acorn_toml_path_for_src_dir(src_dir) {
            if let Some(version) = Self::load_project_format_version_from_acorn_toml(&acorn_toml)? {
                return Ok(version);
            }
        }

        if let Ok(manifest) = Manifest::load(build_dir) {
            return Ok(manifest.version);
        }

        Ok(Manifest::current_version())
    }

    fn write_project_format_version(src_dir: &Path) -> io::Result<()> {
        let Some(acorn_toml) = Self::acorn_toml_path_for_src_dir(src_dir) else {
            return Ok(());
        };
        let existing = std::fs::read_to_string(&acorn_toml).unwrap_or_default();
        let mut doc = existing.parse::<DocumentMut>().map_err(|error| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Error parsing {}: {}", acorn_toml.display(), error),
            )
        })?;
        doc["project_format_version"] = value(i64::from(Manifest::current_version()));
        std::fs::write(acorn_toml, doc.to_string())
    }

    // Create a new project.
    // Returns an error if the project format version is incompatible.
    pub fn new(
        src_dir: PathBuf,
        build_dir: PathBuf,
        config: ProjectConfig,
    ) -> Result<Project, ProjectError> {
        if config.use_filesystem {
            Self::validate_package_layout(&src_dir)?;
        }

        let project_format_version = Self::load_project_format_version(&src_dir, &build_dir)?;
        if project_format_version > Manifest::current_version() {
            return Err(ManifestError::VersionTooNew {
                found: project_format_version,
                supported: Manifest::current_version(),
            }
            .into());
        }
        if config.write_cache
            && !config.update_version
            && project_format_version < Manifest::current_version()
        {
            return Err(ManifestError::VersionTooOld {
                found: project_format_version,
                supported: Manifest::current_version(),
            }
            .into());
        }

        // Load the build cache.
        // We need to load it when reading (to use cached certs) OR when writing (to preserve
        // manifest entries from other modules during partial builds).
        let cache_load_start = std::time::Instant::now();
        let build_cache = if config.read_cache || config.write_cache {
            let load_legacy_cache = project_format_version < Manifest::current_version();
            BuildCache::load(src_dir.clone(), build_dir.clone(), load_legacy_cache)?
        } else {
            BuildCache::new(src_dir.clone(), build_dir.clone())
        };
        let cache_load_time = cache_load_start.elapsed();

        Ok(Project {
            config,
            src_dir,
            open_files: HashMap::new(),
            modules: vec![],
            module_map: HashMap::new(),
            dependency_load_errors: HashMap::new(),
            targets: HashSet::new(),
            surface_check_targets: HashSet::new(),
            build_cache: Arc::new(build_cache),
            cache_load_time,
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

    #[cfg(test)]
    fn is_real_acornlib_src_for_unit_tests(src_dir: &Path) -> bool {
        let Some(real_src_dir) = std::fs::canonicalize(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .with_file_name("acornlib")
                .join("src"),
        )
        .ok() else {
            return false;
        };
        std::fs::canonicalize(src_dir).is_ok_and(|candidate| candidate == real_src_dir)
    }

    // A Project based on the provided starting path.
    // Returns an error if we can't find an acorn library, or if the project format version is
    // incompatible.
    pub fn new_local(start_path: &Path, config: ProjectConfig) -> Result<Project, ProjectError> {
        let (src_dir, build_dir) =
            Project::find_local_acorn_library(start_path).ok_or_else(|| {
                ProjectError::message(
                    "Could not find acornlib.\n\
                Please run this from within the acornlib directory.\n\
                See https://github.com/acornprover/acornlib for details.",
                )
            })?;
        #[cfg(test)]
        if config.use_filesystem && Self::is_real_acornlib_src_for_unit_tests(&src_dir) {
            return Err(ProjectError::message(
                "you should not use real acornlib during the unit tests",
            ));
        }
        Project::new(src_dir, build_dir, config)
    }

    // Create a Project where nothing can be imported.
    pub fn new_mock() -> Project {
        Self::new_mock_with_usage_mode(UsageMode::Verify)
    }

    #[cfg(test)]
    pub fn new_mock_ide() -> Project {
        Self::new_mock_with_usage_mode(UsageMode::Ide)
    }

    fn new_mock_with_usage_mode(usage_mode: UsageMode) -> Project {
        let mock_dir = PathBuf::from(localize_mock_filename("/mock"));
        let build_dir = mock_dir.join("build");
        let config = ProjectConfig {
            usage_mode,
            use_filesystem: false,
            read_cache: false,
            write_cache: false,
            update_version: false,
        };
        // Mock projects don't read the cache, so this can't fail
        Project::new(mock_dir, build_dir, config).expect("mock project creation failed")
    }

    /// Updates the build cache with a new one and optionally writes it to disk.
    /// If is_partial_build is true, old manifest entries are preserved for modules
    /// that weren't rebuilt. If false (full build), only newly built modules are in the manifest.
    pub fn update_build_cache(&mut self, mut new_cache: BuildCache, is_partial_build: bool) {
        if self.config.write_cache {
            let _ = Self::write_project_format_version(&self.src_dir);
            // Save and merge: writes only new JSONL files, preserves manifest based on build type,
            // and merges old certificates back into memory
            let _ = new_cache.save_merging_old(self.build_cache.as_ref(), is_partial_build);
        } else {
            // Even if we're not writing to disk, we need to merge the old certificates
            // into memory so they're available for future builds
            new_cache.merge_certificates_from(self.build_cache.as_ref());
        }

        self.build_cache = Arc::new(new_cache);
    }

    // Dropping existing modules lets you update the project for new data.
    // TODO: do this incrementally instead of dropping everything.
    fn drop_modules(&mut self) {
        self.modules = vec![];
        self.module_map = HashMap::new();
        self.dependency_load_errors = HashMap::new();
    }

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    // Either way, it's still added as a target.
    fn add_target_by_descriptor(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> Result<(), ImportError> {
        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        let build_descriptors = self.build_descriptors_for_target(&canonical_descriptor);
        let result = self.load_build_descriptors(&build_descriptors);
        self.targets.extend(build_descriptors);
        result.map(|_| ())
    }

    pub fn add_unloaded_target_by_descriptor(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> ModuleDescriptor {
        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        self.targets
            .extend(self.build_descriptors_for_target(&canonical_descriptor));
        canonical_descriptor
    }

    pub fn add_unloaded_surface_target_by_descriptor(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> ModuleDescriptor {
        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        self.targets.insert(canonical_descriptor.clone());
        self.surface_check_targets
            .insert(canonical_descriptor.clone());
        canonical_descriptor
    }

    pub fn load_target_by_descriptor(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> Result<(), ImportError> {
        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        self.load_build_descriptors(&self.build_descriptors_for_target(&canonical_descriptor))
    }

    fn load_build_descriptors(
        &mut self,
        descriptors: &[ModuleDescriptor],
    ) -> Result<(), ImportError> {
        let mut result = Ok(());
        for descriptor in descriptors {
            if let Err(error) = self.load_module(descriptor, false) {
                result = Err(error);
                break;
            }
        }
        for descriptor in descriptors {
            if self.package_role_for_descriptor(descriptor) == PackageRole::Interface {
                if let Err(error) = self.load_and_validate_package(descriptor) {
                    if let Some(module_id) = self.module_map.get(descriptor).copied() {
                        self.modules[module_id.get() as usize].load_error(error);
                    }
                }
            }
        }
        result.map(|_| ())
    }

    fn dependency_descriptors_for_target(
        &self,
        descriptor: &ModuleDescriptor,
    ) -> Vec<ModuleDescriptor> {
        let Ok(path) = self.path_from_descriptor(descriptor) else {
            return Vec::new();
        };
        let Ok(text) = read_source_text(&path, |path| self.read_file(path)) else {
            return Vec::new();
        };
        let Ok(parsed) = ParsedModule::parse(descriptor.clone(), text, false) else {
            return Vec::new();
        };

        let current_module_name = parsed.module_name();
        parsed
            .dependency_names
            .iter()
            .filter(|module_name| {
                !current_module_name
                    .as_ref()
                    .is_some_and(|current| current == *module_name)
            })
            .map(|module_name| {
                self.canonicalize_name_descriptor(&ModuleDescriptor::name(module_name))
            })
            .collect()
    }

    fn cached_dependency_descriptors_for_target(
        &self,
        descriptor: &ModuleDescriptor,
        cache: &mut HashMap<ModuleDescriptor, Vec<ModuleDescriptor>>,
    ) -> Vec<ModuleDescriptor> {
        if let Some(dependencies) = cache.get(descriptor) {
            return dependencies.clone();
        }
        let dependencies = self.dependency_descriptors_for_target(descriptor);
        cache.insert(descriptor.clone(), dependencies.clone());
        dependencies
    }

    fn dependent_target_closure(
        &self,
        roots: HashSet<ModuleDescriptor>,
        dependency_cache: &mut HashMap<ModuleDescriptor, Vec<ModuleDescriptor>>,
    ) -> HashSet<ModuleDescriptor> {
        let mut reverse_dependencies: HashMap<ModuleDescriptor, Vec<ModuleDescriptor>> =
            HashMap::new();
        let prelude = ModuleDescriptor::name("prelude");

        for target in &self.targets {
            if target != &prelude {
                reverse_dependencies
                    .entry(prelude.clone())
                    .or_default()
                    .push(target.clone());
            }
            for dependency in
                self.cached_dependency_descriptors_for_target(target, dependency_cache)
            {
                reverse_dependencies
                    .entry(dependency)
                    .or_default()
                    .push(target.clone());
            }
        }

        let mut closure = roots;
        let mut queue = closure.iter().cloned().collect::<Vec<_>>();
        while let Some(descriptor) = queue.pop() {
            let Some(dependents) = reverse_dependencies.get(&descriptor) else {
                continue;
            };
            for dependent in dependents {
                if closure.insert(dependent.clone()) {
                    queue.push(dependent.clone());
                }
            }
        }
        closure
    }

    fn target_dependency_closure(
        &self,
        roots: &HashSet<ModuleDescriptor>,
        dependency_cache: &mut HashMap<ModuleDescriptor, Vec<ModuleDescriptor>>,
    ) -> HashSet<ModuleDescriptor> {
        let mut closure = roots.clone();
        let mut queue = closure.iter().cloned().collect::<Vec<_>>();
        let prelude = ModuleDescriptor::name("prelude");

        while let Some(descriptor) = queue.pop() {
            if descriptor != prelude
                && self.module_map.contains_key(&prelude)
                && closure.insert(prelude.clone())
            {
                queue.push(prelude.clone());
            }

            for dependency in
                self.cached_dependency_descriptors_for_target(&descriptor, dependency_cache)
            {
                if !self.module_map.contains_key(&dependency) {
                    continue;
                }
                if closure.insert(dependency.clone()) {
                    queue.push(dependency);
                }
            }
        }

        closure
    }

    fn sorted_by_cached_work(
        &self,
        descriptors: &HashSet<ModuleDescriptor>,
    ) -> Vec<ModuleDescriptor> {
        let mut sorted = descriptors.iter().cloned().collect::<Vec<_>>();
        sorted.sort_by(|left, right| {
            self.cached_module_work_estimate(right)
                .cmp(&self.cached_module_work_estimate(left))
                .then_with(|| left.cmp(right))
        });
        sorted
    }

    pub fn reload_dependent_targets_by_path(
        &mut self,
        path: &Path,
        jobs: usize,
    ) -> Result<HashSet<ModuleDescriptor>, ImportError> {
        self.register_all_modules();
        let descriptor = self.descriptor_from_path(path)?;
        let canonical_descriptor = self.add_unloaded_target_by_descriptor(&descriptor);
        let roots = HashSet::from([canonical_descriptor]);
        let mut dependency_cache = HashMap::new();
        let targets = self.dependent_target_closure(roots, &mut dependency_cache);
        let load_targets = self.target_dependency_closure(&targets, &mut dependency_cache);
        let load_order = self.sorted_by_cached_work(&load_targets);
        let load_target_list = load_targets.iter().cloned().collect::<Vec<_>>();
        let loader_jobs = (jobs / 2).max(1);
        let mut loader =
            ParallelProjectLoader::new(self, &load_target_list, &load_order, loader_jobs)?;
        let no_build_targets = Vec::new();
        while loader
            .next_loaded_modules(self, &no_build_targets)?
            .is_some()
        {
            // Keep lowered modules in the project so IDE selection and citation queries can
            // inspect the fresh environments after the build.
        }
        Ok(targets)
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

    // Returns Ok(()) if the module loaded successfully, or an ImportError if not.
    // The target will be loaded during builds, but its proof goals will not be checked.
    pub fn add_surface_target_by_path(&mut self, path: &Path) -> Result<(), ImportError> {
        self.register_all_modules();
        let descriptor = self.descriptor_from_path(path)?;
        let canonical_descriptor = self.canonicalize_name_descriptor(&descriptor);
        let result = self.add_target_by_descriptor(&canonical_descriptor);
        self.surface_check_targets.insert(canonical_descriptor);
        result
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
                if path_has_certs_component(path) {
                    continue;
                }
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
        for path in self.src_target_paths() {
            // Ignore errors when adding all targets
            let _ = self.add_target_by_path(&path);
        }
    }

    // Adds all files in the 'src' directory as targets without loading them.
    // This is useful for IDE startup: the project knows what should be built,
    // but expensive parsing/elaboration is deferred until the background build.
    pub fn add_unloaded_src_targets(&mut self) {
        if !self.config.use_filesystem {
            panic!("cannot add_unloaded_src_targets without filesystem access")
        }
        self.register_all_modules();
        let mut descriptors = self.module_map.keys().cloned().collect::<Vec<_>>();
        descriptors.sort();
        for descriptor in descriptors {
            self.add_unloaded_target_by_descriptor(&descriptor);
        }
    }

    pub fn src_target_paths(&mut self) -> Vec<PathBuf> {
        self.register_all_modules();
        let mut paths: Vec<PathBuf> = Vec::new();
        for entry in WalkDir::new(&self.src_dir)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if entry.file_type().is_file() {
                let path = entry.path();
                if path_has_certs_component(path) {
                    continue;
                }
                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    paths.push(path.to_path_buf());
                }
            }
        }
        paths.sort();
        paths
    }

    pub fn src_target_descriptors(&mut self) -> Vec<ModuleDescriptor> {
        let mut descriptors = self
            .src_target_paths()
            .into_iter()
            .filter_map(|path| self.descriptor_from_path(&path).ok())
            .map(|descriptor| self.canonicalize_name_descriptor(&descriptor))
            .collect::<Vec<_>>();
        descriptors.sort();
        descriptors.dedup();
        descriptors
    }

    fn pending_dir(&self) -> Option<PathBuf> {
        self.src_dir.parent().map(|parent| parent.join("pending"))
    }

    pub fn is_pending_path(&self, path: &Path) -> bool {
        self.pending_dir()
            .is_some_and(|pending_dir| path.strip_prefix(pending_dir).is_ok())
    }

    // Adds a surface-check target for all files in the optional 'pending' directory.
    pub fn add_pending_targets(&mut self) {
        if !self.config.use_filesystem {
            panic!("cannot add_pending_targets without filesystem access")
        }

        for path in self.pending_target_paths() {
            let _ = self.add_surface_target_by_path(&path);
        }
    }

    pub fn pending_target_paths(&self) -> Vec<PathBuf> {
        let Some(pending_dir) = self.pending_dir() else {
            return Vec::new();
        };
        if !pending_dir.is_dir() {
            return Vec::new();
        }

        let mut paths: Vec<PathBuf> = Vec::new();
        for entry in WalkDir::new(&pending_dir)
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
        paths
    }

    pub fn pending_target_descriptors(&self) -> Vec<ModuleDescriptor> {
        self.pending_target_paths()
            .into_iter()
            .filter_map(|path| self.descriptor_from_path(&path).ok())
            .collect()
    }

    pub fn is_surface_check_target(&self, descriptor: &ModuleDescriptor) -> bool {
        self.surface_check_targets.contains(descriptor)
    }

    pub fn is_surface_check_module(&self, module_id: ModuleId) -> bool {
        self.get_module_descriptor(module_id)
            .is_some_and(|descriptor| self.is_surface_check_target(descriptor))
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

    fn update_file_state(
        &mut self,
        path: PathBuf,
        content: &str,
        version: i32,
    ) -> Result<bool, ImportError> {
        if self.has_version(&path, version) {
            return Ok(false);
        }
        if path.file_name().and_then(|name| name.to_str()) == Some(PACKAGE_INTERFACE_FILE) {
            self.validate_package_layout_with_open_file(&path)?;
        }
        let descriptor = self.descriptor_from_path(&path)?;

        // This update might be invalidating current modules.
        // For now, we just drop everything. The caller decides whether reloading
        // targets happens synchronously or in a background build task.
        // TODO: figure out precisely which ones are invalidated.
        self.drop_modules();
        self.open_files.insert(path, (content.to_string(), version));
        self.add_unloaded_target_by_descriptor(&descriptor);
        Ok(true)
    }

    fn validate_package_layout_with_open_file(&self, path: &Path) -> Result<(), ImportError> {
        let mut interface_paths = Vec::new();
        if self.config.use_filesystem {
            for entry in WalkDir::new(&self.src_dir)
                .into_iter()
                .filter_map(Result::ok)
            {
                let entry_path = entry.path();
                if path_has_certs_component(entry_path) {
                    continue;
                }
                if entry.file_type().is_file()
                    && entry_path.file_name().and_then(|name| name.to_str())
                        == Some(PACKAGE_INTERFACE_FILE)
                {
                    interface_paths.push(entry_path.to_path_buf());
                }
            }
        }
        for open_path in self.open_files.keys() {
            if path_has_certs_component(open_path) {
                continue;
            }
            if open_path.file_name().and_then(|name| name.to_str()) == Some(PACKAGE_INTERFACE_FILE)
            {
                interface_paths.push(open_path.clone());
            }
        }
        interface_paths.push(path.to_path_buf());
        Self::validate_package_interface_paths(&self.src_dir, interface_paths)
            .map_err(ImportError::NotFound)
    }

    // Reloads all current build targets. This is intentionally separate from
    // updating open file contents so IDE saves can enqueue the expensive reload
    // work in the background.
    pub fn reload_targets(&mut self) {
        let targets = self.targets.clone();
        for target in targets {
            let _ = self.add_target_by_descriptor(&target);
        }
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
        if self.update_file_state(path, content, version)? {
            self.reload_targets();
        }
        Ok(())
    }

    // IDE saves should update visible document state quickly. The background
    // build task calls reload_targets before verifying.
    pub fn update_file_for_ide(
        &mut self,
        path: PathBuf,
        content: &str,
        version: i32,
    ) -> Result<(), ImportError> {
        self.update_file_state(path, content, version)?;
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
        let descriptor = ModuleDescriptor::name(module_name);
        let canonical_descriptor = self.canonicalize_name_descriptor(&descriptor);
        self.module_map.get(&canonical_descriptor).copied()
    }

    pub fn get_loaded_module_id_by_name(&self, module_name: &str) -> Result<ModuleId, ImportError> {
        let descriptor = ModuleDescriptor::name(module_name);
        let canonical_descriptor = self.canonicalize_name_descriptor(&descriptor);
        let Some(&module_id) = self.module_map.get(&canonical_descriptor) else {
            if let Some(error) = self.dependency_load_errors.get(module_name) {
                return Err(error.clone());
            }
            return Err(ImportError::NotFound(format!(
                "module '{}' has not been loaded",
                module_name
            )));
        };
        match self.get_module_by_id(module_id) {
            LoadState::Loading => Err(ImportError::Circular(module_id)),
            LoadState::None | LoadState::Registered => {
                if let Some(error) = self.dependency_load_errors.get(module_name) {
                    return Err(error.clone());
                }
                Err(ImportError::NotFound(format!(
                    "module '{}' has not been loaded",
                    module_name
                )))
            }
            LoadState::Error(error) if error.circular.is_some() => {
                Err(ImportError::Circular(module_id))
            }
            LoadState::Error(_) | LoadState::Ok(_) => Ok(module_id),
        }
    }

    pub fn get_env_by_id(&self, module_id: ModuleId) -> Option<&Environment> {
        if let LoadState::Ok(module) = self.get_module_by_id(module_id) {
            module.env()
        } else {
            None
        }
    }

    pub fn get_loaded_module_by_id(&self, module_id: ModuleId) -> Option<&LoadedModule> {
        if let LoadState::Ok(module) = self.get_module_by_id(module_id) {
            Some(module)
        } else {
            None
        }
    }

    pub fn get_module_export(&self, module_id: ModuleId) -> Option<&ModuleExport> {
        Some(self.get_loaded_module_by_id(module_id)?.export.as_ref())
    }

    pub fn get_lowered_module(&self, module_id: ModuleId) -> Option<&LoweredModule> {
        self.get_loaded_module_by_id(module_id)?.lowered()
    }

    pub fn cached_module_work_estimate(&self, descriptor: &ModuleDescriptor) -> usize {
        self.build_cache
            .get_certificates(descriptor)
            .map(|store| {
                store
                    .certs
                    .iter()
                    .map(|cert| 1 + cert.proof.as_ref().map_or(0, Vec::len))
                    .sum()
            })
            .unwrap_or(0)
    }

    fn prepare_parallel_module_load_job(
        &mut self,
        descriptor: &ModuleDescriptor,
        strict: bool,
    ) -> Result<Option<ParallelModuleLoadJob>, ImportError> {
        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        let descriptor = &canonical_descriptor;

        let preassigned_id = if let Some(&module_id) = self.module_map.get(descriptor) {
            match self.get_module_by_id(module_id) {
                LoadState::Loading => return Err(ImportError::Circular(module_id)),
                LoadState::Registered => Some(module_id),
                LoadState::Ok(_) | LoadState::Error(_) | LoadState::None => return Ok(None),
            }
        } else {
            None
        };

        let path = self.path_from_descriptor(descriptor)?;
        let text =
            read_source_text(&path, |path| self.read_file(path)).map_err(ImportError::NotFound)?;
        let is_prelude = matches!(descriptor, ModuleDescriptor::Name(parts) if parts.len() == 1 && parts[0] == "prelude");

        let module_id = if let Some(id) = preassigned_id {
            self.modules[id.get() as usize] = Module::new(descriptor.clone());
            id
        } else if is_prelude {
            if self.modules.is_empty() {
                self.modules.push(Module::new(descriptor.clone()));
            } else {
                self.modules[ModuleId::PRELUDE.get() as usize] = Module::new(descriptor.clone());
            }
            ModuleId::PRELUDE
        } else {
            if self.modules.is_empty() {
                self.modules.push(Module::anonymous());
            }
            let id = ModuleId(self.modules.len() as u16);
            self.modules.push(Module::new(descriptor.clone()));
            id
        };
        self.module_map.insert(descriptor.clone(), module_id);

        let package_role = self.package_role_for_path(&path);
        let mut parsed = match ParsedModule::parse(descriptor.clone(), text, strict) {
            Ok(parsed) => parsed,
            Err(error) => {
                self.modules[module_id.get() as usize].load_error(error);
                return Ok(None);
            }
        };
        if package_role == PackageRole::Interface {
            if let Err(error) = parsed.apply_interface_mode() {
                self.modules[module_id.get() as usize].load_error(error);
                return Ok(None);
            }
        }

        let current_module_name = parsed.module_name();
        let implicit_lib_dependency_names: HashSet<_> = parsed
            .implicit_lib_dependency_names
            .iter()
            .cloned()
            .collect();
        let mut dependencies = Vec::new();
        let mut seen_dependencies = HashSet::new();
        let mut lib_dependencies = Vec::new();

        for module_name in &parsed.dependency_names {
            if current_module_name
                .as_ref()
                .is_some_and(|name| name == module_name)
            {
                continue;
            }
            match self.get_module_id_by_name(module_name) {
                Some(dep_id) => {
                    self.dependency_load_errors.remove(module_name);
                    if dep_id != module_id && seen_dependencies.insert(dep_id) {
                        dependencies.push(dep_id);
                    }
                    if implicit_lib_dependency_names.contains(module_name) {
                        let full_name = module_name
                            .split('.')
                            .map(|part| part.to_string())
                            .collect::<Vec<_>>();
                        lib_dependencies.push((dep_id, full_name));
                    }
                }
                None => {
                    let message = self
                        .path_from_descriptor(&ModuleDescriptor::name(module_name))
                        .and_then(|path| {
                            read_source_text(&path, |path| self.read_file(path))
                                .map(|_| path)
                                .map_err(ImportError::NotFound)
                        })
                        .map(|path| {
                            format!(
                                "module '{}' has not been loaded from {}",
                                module_name,
                                path.display()
                            )
                        })
                        .unwrap_or_else(|error| error.to_string());
                    self.dependency_load_errors
                        .insert(module_name.clone(), ImportError::NotFound(message));
                }
            }
        }

        if !is_prelude {
            if let Some(prelude_id) = self.get_module_id_by_name("prelude") {
                if prelude_id != module_id && seen_dependencies.insert(prelude_id) {
                    dependencies.push(prelude_id);
                }
            }
        }

        Ok(Some(ParallelModuleLoadJob {
            descriptor: descriptor.clone(),
            module_id,
            parsed: Some(parsed),
            is_prelude,
            dependencies,
            lib_dependencies,
        }))
    }

    fn pop_ready_parallel_load_job(
        &self,
        ready: &mut Vec<usize>,
        jobs: &[ParallelModuleLoadJob],
    ) -> Option<usize> {
        let (ready_index, _) = ready.iter().enumerate().max_by(|(_, left), (_, right)| {
            self.cached_module_work_estimate(&jobs[**left].descriptor)
                .cmp(&self.cached_module_work_estimate(&jobs[**right].descriptor))
                .then_with(|| jobs[**right].descriptor.cmp(&jobs[**left].descriptor))
        })?;
        Some(ready.swap_remove(ready_index))
    }

    fn enqueue_parallel_load_job(
        &self,
        jobs: &mut [ParallelModuleLoadJob],
        job_index: usize,
        sender: &mpsc::Sender<ParallelModuleWorkerJob>,
    ) {
        let project = ProjectView::new_without_lowered(self);
        let job = &mut jobs[job_index];
        let parsed = job
            .parsed
            .take()
            .expect("parallel load job should only be enqueued once");
        let worker_job = ParallelModuleWorkerJob {
            index: job_index,
            module_id: job.module_id,
            parsed,
            is_prelude: job.is_prelude,
            lib_dependencies: job.lib_dependencies.clone(),
            project,
            usage_mode: self.config.usage_mode,
        };
        sender
            .send(worker_job)
            .expect("parallel load workers should still be receiving jobs");
    }

    pub fn take_lowered_modules_for_targets(
        &mut self,
        targets: &[ModuleDescriptor],
    ) -> Vec<(ModuleDescriptor, LoweredModule)> {
        let mut target_set = HashSet::new();
        for target in targets {
            target_set.extend(self.build_descriptors_for_target(target));
        }
        let mut lowered = Vec::new();
        for module in &mut self.modules {
            if !target_set.contains(&module.descriptor) {
                continue;
            }
            let LoadState::Ok(loaded) = &mut module.state else {
                continue;
            };
            let Some(work) = loaded.lowered.take() else {
                continue;
            };
            let work = Arc::try_unwrap(work).unwrap_or_else(|work| (*work).clone());
            lowered.push((module.descriptor.clone(), work));
        }
        lowered.sort_by(|(left, _), (right, _)| left.cmp(right));
        lowered
    }

    pub fn lowered_goal_for_goal(&self, goal: &Goal) -> Option<(LoweredGoalId, &LoweredGoalEntry)> {
        self.get_lowered_module(goal.module_id)?
            .goal_for_source_goal(goal)
    }

    #[doc(hidden)]
    pub fn profile_visit_envs_mut<F>(&mut self, mut visitor: F)
    where
        F: FnMut(ModuleId, &mut Environment),
    {
        for (index, module) in self.modules.iter_mut().enumerate() {
            let LoadState::Ok(loaded) = &mut module.state else {
                continue;
            };
            let Some(env) = loaded.env_mut() else {
                continue;
            };
            visitor(ModuleId(index as u16), env);
        }
    }

    #[doc(hidden)]
    pub fn profile_visit_loaded_modules_mut<F>(&mut self, mut visitor: F)
    where
        F: FnMut(ModuleId, &mut LoadedModule),
    {
        for (index, module) in self.modules.iter_mut().enumerate() {
            let LoadState::Ok(loaded) = &mut module.state else {
                continue;
            };
            visitor(ModuleId(index as u16), loaded);
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
        _env: &'a Environment,
        name: &ConstantName,
    ) -> Option<&'a Environment> {
        match name {
            ConstantName::DatatypeAttribute(module_id, _datatype, _attr_name) => {
                self.get_env_by_id(*module_id)
            }
            ConstantName::SpecificDatatypeAttribute(module_id, _datatype, _types, _attr_name) => {
                self.get_env_by_id(*module_id)
            }
            ConstantName::TypeclassAttribute(module_id, _typeclass, _attr_name) => {
                self.get_env_by_id(*module_id)
            }
            ConstantName::InstanceAttribute(module_id, _instance_name) => {
                self.get_env_by_id(*module_id)
            }
            ConstantName::Synthetic(module_id, _) => self.get_env_by_id(*module_id),
            ConstantName::Unqualified(module_id, _name) => self.get_env_by_id(*module_id),
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

    /// Strip value-level applications while preserving explicit type applications.
    ///
    /// For hover display of partially-applied functions, we want to show the base function,
    /// but still keep `[T, U]` if it was explicitly applied.
    fn unapplied_value(value: &AcornValue) -> &AcornValue {
        match value {
            AcornValue::Application(app) => Self::unapplied_value(&app.function),
            _ => value,
        }
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
                    // For partial applications, show the base function while preserving
                    // explicit type applications like `f[T]`.
                    let base_value = Self::unapplied_value(value);
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
                let base_value = Self::unapplied_value(value);
                base_value
                    .as_name()
                    .and_then(|name| self.get_constant_definition_string(env, name))
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
            NamedEntity::UnresolvedType(unresolved_type) => unresolved_type
                .base_datatype()
                .and_then(|datatype| self.get_datatype_definition_string(datatype)),
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
                // Use the unapplied value to get the base constant name for doc comments.
                let base_value = Self::unapplied_value(value);
                base_value
                    .as_name()
                    .and_then(|name| self.get_constant_doc_comments(env, name))
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
            NamedEntity::UnresolvedType(unresolved_type) => unresolved_type
                .base_datatype()
                .and_then(|datatype| self.get_datatype_doc_comments(datatype)),

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
                let datatype = unresolved_type.base_datatype()?;
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

    pub fn citation_statements(&self) -> Vec<LibraryCitation> {
        let mut citations = Vec::new();
        let display_root = if self.src_dir.file_name().and_then(|name| name.to_str()) == Some("src")
        {
            self.src_dir.parent().unwrap_or(&self.src_dir)
        } else {
            &self.src_dir
        };

        for (index, module) in self.modules.iter().enumerate() {
            let LoadState::Ok(loaded) = &module.state else {
                continue;
            };
            let Some(env) = loaded.env() else {
                continue;
            };

            let module_id = ModuleId(index as u16);
            let path = self
                .path_from_module_id(module_id)
                .and_then(|path| {
                    path.strip_prefix(display_root)
                        .ok()
                        .map(|path| path.display().to_string())
                })
                .unwrap_or_else(|| module.descriptor.to_string());

            let mut env_citations = Vec::new();
            env.append_citation_statements(&mut env_citations);
            for citation in env_citations {
                citations.push(LibraryCitation {
                    path: path.clone(),
                    line: citation.line,
                    text: citation
                        .statement
                        .split_whitespace()
                        .collect::<Vec<_>>()
                        .join(" "),
                });
            }
        }
        citations.sort_by(|a, b| {
            a.path
                .cmp(&b.path)
                .then(a.line.cmp(&b.line))
                .then(a.text.cmp(&b.text))
        });
        citations
    }

    pub fn read_file(&self, path: &Path) -> Result<String, ProjectError> {
        if let Some((content, _)) = self.open_files.get(path) {
            return Ok(content.clone());
        }
        if !self.config.use_filesystem {
            return Err(ProjectError::message(format!(
                "no mocked file for: {}",
                path.display()
            )));
        }
        match std::fs::read_to_string(&path) {
            Ok(s) => Ok(s),
            Err(e) => Err(ProjectError::message(format!(
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
        let package_root = self.nearest_package_root_for_path(path);
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
                if component == PACKAGE_INTERFACE_FILE
                    && package_root
                        .as_ref()
                        .is_some_and(|root| path == root.join(PACKAGE_INTERFACE_FILE))
                {
                    break;
                }
                if component == "default.ac" && i > 0 && package_root.is_none() {
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
                let interface_path = path.join(part).join(PACKAGE_INTERFACE_FILE);

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

                let interface_exists = if self.config.use_filesystem {
                    interface_path.exists()
                } else {
                    self.open_files.contains_key(&interface_path)
                };

                if interface_exists {
                    if file_exists {
                        return Err(ImportError::NotFound(format!(
                            "ambiguous module '{}': both {} and package interface {} exist",
                            module_name,
                            file_path.display(),
                            interface_path.display()
                        )));
                    }
                    return Ok(interface_path);
                } else if file_exists && dir_exists {
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

    // Returns true if this path should be considered present for module resolution.
    // In mock mode, only open files are considered present.
    fn module_path_exists(&self, path: &Path) -> bool {
        if self.config.use_filesystem {
            path.exists()
        } else {
            self.open_files.contains_key(path)
        }
    }

    fn nearest_package_root_for_path(&self, path: &Path) -> Option<PathBuf> {
        let mut current = path.parent()?;
        while current != self.src_dir.as_path() {
            if self.module_path_exists(&current.join(PACKAGE_INTERFACE_FILE)) {
                return Some(current.to_path_buf());
            }
            current = current.parent()?;
        }
        None
    }

    fn package_role_for_path(&self, path: &Path) -> PackageRole {
        let Some(package_root) = self.nearest_package_root_for_path(path) else {
            return PackageRole::Outside;
        };
        if path == package_root.join(PACKAGE_INTERFACE_FILE) {
            PackageRole::Interface
        } else {
            PackageRole::Implementation
        }
    }

    fn package_root_for_module(&self, module_id: ModuleId) -> Option<PathBuf> {
        let descriptor = self.get_module_descriptor(module_id)?;
        let path = self.path_from_descriptor(descriptor).ok()?;
        self.nearest_package_root_for_path(&path)
    }

    fn package_role_for_module(&self, module_id: ModuleId) -> PackageRole {
        let Some(descriptor) = self.get_module_descriptor(module_id) else {
            return PackageRole::Outside;
        };
        self.package_role_for_descriptor(descriptor)
    }

    fn package_role_for_descriptor(&self, descriptor: &ModuleDescriptor) -> PackageRole {
        let Ok(path) = self.path_from_descriptor(descriptor) else {
            return PackageRole::Outside;
        };
        self.package_role_for_path(&path)
    }

    fn package_interface_descriptor_for_path(&self, path: &Path) -> Option<ModuleDescriptor> {
        let package_root = self.nearest_package_root_for_path(path)?;
        self.descriptor_from_path(&package_root.join(PACKAGE_INTERFACE_FILE))
            .ok()
    }

    pub fn build_descriptors_for_target(
        &self,
        descriptor: &ModuleDescriptor,
    ) -> Vec<ModuleDescriptor> {
        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        let Ok(path) = self.path_from_descriptor(&canonical_descriptor) else {
            return vec![canonical_descriptor];
        };

        let interface_descriptor = match self.package_role_for_path(&path) {
            PackageRole::Outside => return vec![canonical_descriptor],
            PackageRole::Interface => canonical_descriptor,
            PackageRole::Implementation => self
                .package_interface_descriptor_for_path(&path)
                .unwrap_or(canonical_descriptor),
        };

        let mut descriptors = vec![interface_descriptor.clone()];
        if let Ok(implementation_descriptors) =
            self.package_implementation_descriptors(&interface_descriptor)
        {
            descriptors.extend(implementation_descriptors);
        }
        descriptors.sort();
        descriptors.dedup();
        descriptors
    }

    fn package_implementation_descriptors(
        &self,
        interface_descriptor: &ModuleDescriptor,
    ) -> Result<Vec<ModuleDescriptor>, ImportError> {
        let interface_path = self.path_from_descriptor(interface_descriptor)?;
        if self.package_role_for_path(&interface_path) != PackageRole::Interface {
            return Ok(Vec::new());
        }
        let Some(package_root) = interface_path.parent() else {
            return Ok(Vec::new());
        };

        let mut paths = Vec::new();
        if self.config.use_filesystem {
            for entry in WalkDir::new(package_root)
                .into_iter()
                .filter_map(Result::ok)
            {
                let path = entry.path();
                if path_has_certs_component(path) {
                    continue;
                }
                if entry.file_type().is_file()
                    && path.extension() == Some(std::ffi::OsStr::new("ac"))
                    && path != interface_path
                {
                    paths.push(path.to_path_buf());
                }
            }
        } else {
            for path in self.open_files.keys() {
                if path_has_certs_component(path) {
                    continue;
                }
                if path.starts_with(package_root)
                    && path.extension() == Some(std::ffi::OsStr::new("ac"))
                    && path != &interface_path
                {
                    paths.push(path.clone());
                }
            }
        }

        let mut descriptors = paths
            .into_iter()
            .filter_map(|path| self.descriptor_from_path(&path).ok())
            .collect::<Vec<_>>();
        descriptors.sort();
        descriptors.dedup();
        Ok(descriptors)
    }

    fn collect_interface_signatures(
        &self,
        descriptor: &ModuleDescriptor,
    ) -> error::Result<BTreeMap<String, PackageSignature>> {
        let path = self
            .path_from_descriptor(descriptor)
            .map_err(|e| Token::empty().error(&e.to_string()))?;
        let text = read_source_text(&path, |path| self.read_file(path))
            .map_err(|e| Token::empty().error(&e))?;
        let parsed = ParsedModule::parse(descriptor.clone(), text, false)?;
        let mut signatures = BTreeMap::new();
        for statement in &parsed.statements {
            if matches!(&statement.statement, StatementInfo::Theorem(t) if t.lemma) {
                return Err(statement.error("interface.ac cannot contain lemmas"));
            }
            if matches!(&statement.statement, StatementInfo::Theorem(t) if t.body.is_some()) {
                return Err(statement.error("interface theorems cannot have proof bodies"));
            }

            let statement_signatures = statement.package_signatures();
            if statement_signatures.is_empty() {
                if matches!(
                    &statement.statement,
                    StatementInfo::Import(_)
                        | StatementInfo::Numerals(_)
                        | StatementInfo::DocComment(_)
                ) {
                    continue;
                }
                return Err(
                    statement.error("interface.ac can only contain imports and declarations")
                );
            }
            for (name, text) in statement_signatures {
                if signatures
                    .insert(
                        name.clone(),
                        PackageSignature {
                            text,
                            axiomatic_theorem: false,
                            first_token: statement.first_token.clone(),
                            last_token: statement.last_token.clone(),
                        },
                    )
                    .is_some()
                {
                    return Err(
                        statement.error(&format!("duplicate package declaration '{}'", name))
                    );
                }
            }
        }
        Ok(signatures)
    }

    fn collect_implementation_signatures(
        &self,
        descriptor: &ModuleDescriptor,
    ) -> error::Result<Vec<(String, PackageSignature)>> {
        let path = self
            .path_from_descriptor(descriptor)
            .map_err(|e| Token::empty().error(&e.to_string()))?;
        let text = read_source_text(&path, |path| self.read_file(path))
            .map_err(|e| Token::empty().error(&e))?;
        let parsed = ParsedModule::parse(descriptor.clone(), text, false)?;
        let mut signatures = Vec::new();
        for statement in &parsed.statements {
            for (name, text) in statement.package_signatures() {
                signatures.push((
                    name,
                    PackageSignature {
                        text,
                        axiomatic_theorem: matches!(
                            &statement.statement,
                            StatementInfo::Theorem(t) if t.axiomatic
                        ),
                        first_token: statement.first_token.clone(),
                        last_token: statement.last_token.clone(),
                    },
                ));
            }
        }
        Ok(signatures)
    }

    fn validate_package_implementations(
        &self,
        interface_descriptor: &ModuleDescriptor,
    ) -> error::Result<()> {
        let interface_signatures = self.collect_interface_signatures(interface_descriptor)?;
        let mut implementation_signatures: BTreeMap<String, Vec<PackageSignature>> =
            BTreeMap::new();
        for descriptor in self
            .package_implementation_descriptors(interface_descriptor)
            .map_err(|e| Token::empty().error(&e.to_string()))?
        {
            for (name, signature) in self.collect_implementation_signatures(&descriptor)? {
                implementation_signatures
                    .entry(name)
                    .or_default()
                    .push(signature);
            }
        }

        for (name, interface_signature) in &interface_signatures {
            let Some(candidates) = implementation_signatures.get(name) else {
                return Err(Error::new(
                    &interface_signature.first_token,
                    &interface_signature.last_token,
                    &format!(
                        "missing implementation for interface declaration '{}'",
                        name
                    ),
                ));
            };
            if candidates.len() > 1 {
                let signature = &candidates[0];
                return Err(Error::new(
                    &signature.first_token,
                    &signature.last_token,
                    &format!(
                        "multiple implementations found for interface declaration '{}'",
                        name
                    ),
                ));
            }
            let implementation_signature = &candidates[0];
            if implementation_signature.axiomatic_theorem {
                return Err(Error::new(
                    &implementation_signature.first_token,
                    &implementation_signature.last_token,
                    &format!("implementation theorem '{}' cannot be an axiom", name),
                ));
            }
            if implementation_signature.text != interface_signature.text {
                return Err(Error::new(
                    &implementation_signature.first_token,
                    &implementation_signature.last_token,
                    &format!(
                        "implementation '{}' does not match interface declaration\ninterface: {}\nimplementation: {}",
                        name, interface_signature.text, implementation_signature.text
                    ),
                ));
            }
        }

        Ok(())
    }

    fn load_and_validate_package(
        &mut self,
        interface_descriptor: &ModuleDescriptor,
    ) -> error::Result<()> {
        for descriptor in self
            .package_implementation_descriptors(interface_descriptor)
            .map_err(|e| Token::empty().error(&e.to_string()))?
        {
            let module_id = self
                .load_module(&descriptor, false)
                .map_err(|e| Token::empty().error(&e.to_string()))?;
            if let LoadState::Error(error) = self.get_module_by_id(module_id) {
                return Err(Error::indirect(
                    &Token::empty(),
                    &Token::empty(),
                    &format!(
                        "error in package implementation module '{}': {}",
                        descriptor, error
                    ),
                ));
            }
        }
        self.validate_package_implementations(interface_descriptor)
    }

    pub fn validate_packages_for_descriptors<I>(
        &mut self,
        descriptors: I,
    ) -> Vec<(ModuleDescriptor, Error)>
    where
        I: IntoIterator<Item = ModuleDescriptor>,
    {
        let mut interface_descriptors = BTreeSet::new();
        for descriptor in descriptors {
            let canonical_descriptor = self.canonicalize_name_descriptor(&descriptor);
            let Ok(path) = self.path_from_descriptor(&canonical_descriptor) else {
                continue;
            };
            match self.package_role_for_path(&path) {
                PackageRole::Outside => {}
                PackageRole::Interface => {
                    interface_descriptors.insert(canonical_descriptor);
                }
                PackageRole::Implementation => {
                    if let Some(interface_descriptor) =
                        self.package_interface_descriptor_for_path(&path)
                    {
                        interface_descriptors.insert(interface_descriptor);
                    }
                }
            }
        }

        let mut errors = Vec::new();
        for interface_descriptor in interface_descriptors {
            if let Err(error) = self.load_and_validate_package(&interface_descriptor) {
                if let Some(module_id) = self.module_map.get(&interface_descriptor).copied() {
                    self.modules[module_id.get() as usize].load_error(error.clone());
                }
                errors.push((interface_descriptor, error));
            }
        }
        errors
    }

    // Resolves aliases like `foo.default` to the canonical descriptor (`foo`) when
    // the named module file exists.
    fn canonicalize_name_descriptor(&self, descriptor: &ModuleDescriptor) -> ModuleDescriptor {
        let ModuleDescriptor::Name(_) = descriptor else {
            return descriptor.clone();
        };

        let Ok(path) = self.path_from_descriptor(descriptor) else {
            return descriptor.clone();
        };

        if !self.module_path_exists(&path) {
            return descriptor.clone();
        }

        self.descriptor_from_path(&path)
            .unwrap_or_else(|_| descriptor.clone())
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
        let normalize = |path: &Path| path.to_string_lossy().replace('\\', "/");
        match self.path_from_descriptor(descriptor) {
            Ok(full_path) => {
                // Try to make it relative to the src dir
                match full_path.strip_prefix(&self.src_dir) {
                    Ok(relative_path) => normalize(relative_path),
                    Err(_) => {
                        // If it's not under src dir, just use the full path
                        normalize(&full_path)
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
        // Ensure filesystem-backed projects always assign stable module IDs
        // before loading starts (including reloads after update_file/close_file).
        self.register_all_modules();

        let canonical_descriptor = self.canonicalize_name_descriptor(descriptor);
        let descriptor = &canonical_descriptor;

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
        let text =
            read_source_text(&path, |path| self.read_file(path)).map_err(ImportError::NotFound)?;

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

        let package_role = self.package_role_for_path(&path);
        let mut parsed = match ParsedModule::parse(descriptor.clone(), text, strict) {
            Ok(parsed) => parsed,
            Err(error) => {
                self.modules[module_id.get() as usize].load_error(error);
                return Ok(module_id);
            }
        };
        if package_role == PackageRole::Interface {
            if let Err(error) = parsed.apply_interface_mode() {
                self.modules[module_id.get() as usize].load_error(error);
                return Ok(module_id);
            }
        }

        let current_module_name = parsed.module_name();
        let dependency_names = parsed.dependency_names.clone();
        let implicit_lib_dependency_names: HashSet<_> = parsed
            .implicit_lib_dependency_names
            .iter()
            .cloned()
            .collect();
        let mut lib_dependencies = vec![];
        for module_name in &dependency_names {
            if current_module_name
                .as_ref()
                .is_some_and(|name| name == module_name)
            {
                continue;
            }
            match self.load_module_by_name(module_name) {
                Ok(dep_id) => {
                    self.dependency_load_errors.remove(module_name);
                    if implicit_lib_dependency_names.contains(module_name) {
                        let full_name = module_name
                            .split('.')
                            .map(|part| part.to_string())
                            .collect::<Vec<_>>();
                        lib_dependencies.push((dep_id, full_name));
                    }
                }
                Err(error) => {
                    self.dependency_load_errors
                        .insert(module_name.clone(), error);
                }
            }
        }

        if !is_prelude {
            // The prelude is an implicit dependency for ordinary modules. Load it before
            // elaboration so module processing only needs read-only project lookup.
            let _ = self.load_module_by_name("prelude");
        }
        let usage_mode = self.config.usage_mode;

        let loaded = match elaborate_and_lower_module(
            self,
            usage_mode,
            module_id,
            parsed,
            is_prelude,
            lib_dependencies,
        ) {
            Ok(loaded) => loaded,
            Err(e) => {
                if e.circular.is_some() {
                    let err = Err(ImportError::Circular(module_id));
                    self.modules[module_id.get() as usize].load_error(e);
                    return err;
                }
                self.modules[module_id.get() as usize].load_error(e);
                return Ok(module_id);
            }
        };
        self.modules[module_id.get() as usize].load_ok(
            loaded.export,
            Some(loaded.lowered),
            loaded.retained_env,
            loaded.content_hash,
        );
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
        if let Some(bindings) = self.get_bindings(module_id) {
            for dep in bindings.direct_dependencies() {
                if self.append_dependencies(seen, output, dep) {
                    output.push(dep);
                }
            }
        }
        true
    }

    pub fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        if let LoadState::Ok(module) = self.get_module_by_id(module_id) {
            Some(&module.export.bindings)
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
    pub fn find_cert(&self, goal: &Goal) -> Option<(&Certificate, Vec<CertificateLine>)> {
        let descriptor = self.get_module_descriptor(goal.module_id)?;
        let cert_store = self.build_cache.get_certificates(descriptor)?;
        let lowered = self.get_lowered_module(goal.module_id)?;
        let (goal_id, entry) = lowered.goal_for_source_goal(goal)?;

        let mut processor = match Processor::with_imports_for_checking(None, &entry.bindings, self)
        {
            Ok(p) => p,
            Err(_) => return None,
        };
        if processor
            .add_visible_module_facts(lowered, goal_id)
            .is_err()
        {
            return None;
        }

        // Try each certificate with a matching goal name
        for cert in &cert_store.certs {
            if cert.goal == goal.name {
                // Try to verify this certificate
                let normalized_goal = &entry.lowered_goal;
                if let Ok(steps) = processor.check_cert(
                    cert,
                    Some(normalized_goal),
                    &normalized_goal.kernel_context,
                    self,
                    &entry.bindings,
                ) {
                    return Some((cert, steps));
                }
            }
        }

        None
    }

    /// Handle a selection request for a given file and line number.
    /// Returns either goal information or citation information for the selected line.
    pub fn handle_selection(
        &self,
        path: &Path,
        selected_line: u32,
    ) -> Result<SelectionInfo, String> {
        let descriptor = self
            .descriptor_from_path(path)
            .map_err(|e| format!("descriptor_from_path failed: {:?}", e))?;

        let env = match self.get_module(&descriptor) {
            LoadState::Ok(module) => module
                .env()
                .ok_or_else(|| format!("environment not retained for {:?}", descriptor))?,
            _ => return Err(format!("could not load module from {:?}", descriptor)),
        };

        if let Some((cursor, citation)) = env.citation_cursor_for_line(selected_line) {
            return Ok(SelectionInfo::Citation(
                self.create_citation_info(citation, &cursor)?,
            ));
        }

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
            let goal_info = self.create_goal_info(goal, &cursor);
            goal_infos.push(goal_info);
        } else if let Some(block) = cursor.node().get_block() {
            // This is a Block node. Select its immediate block-level goals if it has any;
            // otherwise treat expression-only wrapper blocks as transparent and recurse into
            // nested blocks that cover the selected line.
            let mut goal_paths = vec![];
            let mut base_path = node_path.clone();
            crate::elaborator::environment::Environment::collect_selectable_goal_paths_in_block(
                block,
                &mut base_path,
                selected_line,
                &mut goal_paths,
            );

            if goal_paths.is_empty() {
                return Err("no goal at this location".to_string());
            }

            for goal_path in goal_paths {
                let goal_cursor = crate::elaborator::node::NodeCursor::from_path(env, &goal_path);
                let goal = goal_cursor
                    .goal()
                    .ok_or_else(|| "failed to get goal from goal node".to_string())?;

                // Use the first goal's range for the overall goal_range
                if goal_range.is_none() {
                    goal_range = Some(goal.proposition.source.range);
                }

                let goal_info = self.create_goal_info(&goal, &goal_cursor);
                goal_infos.push(goal_info);
            }
        } else {
            return Err("no goal at this location".to_string());
        }

        Ok(SelectionInfo::Goals {
            goal_infos,
            goal_range,
        })
    }

    // Helper function to create a GoalInfo from a goal, its environment, and cursor
    fn create_goal_info(
        &self,
        goal: &crate::elaborator::goal::Goal,
        cursor: &crate::elaborator::node::NodeCursor,
    ) -> GoalInfo {
        let goal_name = goal.name.clone();

        // Check if there's a verified certificate for this goal
        let (has_cached_proof, steps) = if let Some((_cert, certificate_steps)) =
            self.find_cert(goal)
        {
            let displayed_steps = display_certificate_lines(cursor.bindings(), &certificate_steps);
            let steps: Vec<Step> = displayed_steps
                .into_iter()
                .map(|displayed_step| {
                    let location = displayed_step
                        .source_index
                        .and_then(|i| certificate_steps.get(i))
                        .and_then(|cert_step| match &cert_step.reason {
                            StepReason::Assumption(source) => {
                                self.location_from_module_range(source.module_id, source.range)
                            }
                            _ => None,
                        });

                    Step {
                        statement: displayed_step.statement,
                        reason: displayed_step.reason,
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

    fn create_citation_info(
        &self,
        citation: &crate::elaborator::environment::CitationStatement,
        cursor: &crate::elaborator::node::NodeCursor,
    ) -> Result<CitationInfo, String> {
        let proposition = cursor
            .node()
            .proposition()
            .ok_or_else(|| "citation node does not contain a proposition".to_string())?;

        let mut generator = CodeGenerator::new(cursor.bindings());
        let mut rendered_clauses = Vec::new();
        let lowered_fact = self
            .get_lowered_module(cursor.env().module_id)
            .and_then(|lowered| lowered.fact_for_source_range(proposition.source.range));
        if let Some(lowered_fact) = lowered_fact {
            for step in &lowered_fact.steps {
                let quoted =
                    lowered_fact
                        .kernel_context
                        .quote_clause(&step.clause, None, None, true);
                rendered_clauses.push(
                    generator
                        .value_to_code(&quoted)
                        .map_err(|e| e.to_string())?,
                );
            }
        }
        if rendered_clauses.is_empty() {
            rendered_clauses.push(
                generator
                    .value_to_code(&proposition.value)
                    .map_err(|e| e.to_string())?,
            );
        }

        Ok(CitationInfo {
            selection_text: citation.statement.trim().to_string(),
            range: proposition.source.range,
            theorem_name: citation.cited_name.as_ref().map(|name| name.to_string()),
            theorem_location: citation
                .cited_name
                .as_ref()
                .and_then(|name| self.definition_location_for_constant(name)),
            expansion: rendered_clauses.join("\n"),
        })
    }

    fn definition_location_for_constant(&self, name: &ConstantName) -> Option<Location> {
        let module_id = name.module_id();
        let env = self.get_env_by_id(module_id)?;
        let range = *env
            .bindings
            .get_definition_range(&DefinedName::Constant(name.clone()))?;
        self.location_from_module_range(module_id, range)
    }

    fn location_from_module_range(
        &self,
        module_id: ModuleId,
        range: lsp_types::Range,
    ) -> Option<Location> {
        let uri = Url::from_file_path(self.path_from_module_id(module_id)?).ok()?;
        Some(Location { uri, range })
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
            return env.bindings.get_completions(partial, true, self);
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

        env.bindings.get_completions(word, false, self)
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
        let bindings = match self.get_module_by_id(module_id) {
            LoadState::Ok(module) => module.bindings(),
            _ => panic!("no module"),
        };
        let value = match Evaluator::new(self, bindings, None).evaluate_value(&expression, None) {
            Ok(value) => value,
            Err(e) => panic!("evaluation error: {}", e),
        };
        CodeGenerator::expect(bindings, input, &value, expected);
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
        let lowered = self
            .get_lowered_module(module_id)
            .expect("missing lowered module");
        let (_, entry) = lowered
            .goal_by_name(theorem_name)
            .expect("missing lowered goal");
        let value = &entry.lowered_goal.goal.proposition.value;
        let fake_input = format!("<{}>", theorem_name);
        CodeGenerator::expect(&entry.bindings, &fake_input, value, expected);
    }
}
