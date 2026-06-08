use std::collections::HashMap;
use std::error::Error;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use crate::certificate::{CertificateStore, CertificateWorklist};
use crate::manifest::{ManifestError, PackageManifest};
use crate::module::ModuleDescriptor;

const CERTS_DIR: &str = "certs";
const PACKAGE_INTERFACE_FILE: &str = "interface.ac";

/// Cached information about a build.
///
/// Certificates are stored next to their source files in sibling `certs/` directories:
/// `src/foo/bar.ac` has certificates at `src/foo/certs/bar.jsonl`.
/// Package manifests live at the package root's `certs/manifest.json`.
pub struct BuildCache {
    // The certificates for each module.
    cache: HashMap<ModuleDescriptor, CertificateStore>,

    // The last checked package manifests, keyed by package root.
    manifests: HashMap<PathBuf, PackageManifest>,

    // The source directory for named Acorn modules.
    src_dir: PathBuf,
}

fn normalize_relative_path(path: &Path) -> Option<String> {
    Some(
        path.components()
            .map(|component| component.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/"),
    )
}

fn path_has_certs_component(path: &Path) -> bool {
    path.components()
        .any(|component| component.as_os_str() == CERTS_DIR)
}

impl BuildCache {
    pub fn new(src_dir: PathBuf, _build_dir: PathBuf) -> Self {
        BuildCache {
            cache: HashMap::new(),
            manifests: HashMap::new(),
            src_dir,
        }
    }

    /// Load a build cache from package-local certificate and manifest files.
    /// Project checks the project format version before loading the cache.
    pub fn load(
        src_dir: PathBuf,
        build_dir: PathBuf,
        load_legacy_cache: bool,
    ) -> Result<Self, ManifestError> {
        let mut cache = HashMap::new();
        let mut manifests = HashMap::new();

        if src_dir.exists() {
            for entry in WalkDir::new(&src_dir).into_iter().filter_map(Result::ok) {
                if !entry.file_type().is_file() {
                    continue;
                }
                let path = entry.path();
                if path.file_name().and_then(|name| name.to_str()) == Some("manifest.json")
                    && path
                        .parent()
                        .and_then(|parent| parent.file_name())
                        .and_then(|name| name.to_str())
                        == Some(CERTS_DIR)
                {
                    if let Some(package_root) = path
                        .parent()
                        .and_then(|certs_dir| certs_dir.parent())
                        .map(Path::to_path_buf)
                    {
                        if let Ok(manifest) = PackageManifest::load(path) {
                            manifests.insert(package_root, manifest);
                        }
                    }
                    continue;
                }

                if path.extension().and_then(|ext| ext.to_str()) == Some("jsonl") {
                    let Some(source_path) = Self::source_path_from_cert_path(path) else {
                        continue;
                    };
                    if !source_path.is_file() {
                        continue;
                    }
                    let Some(descriptor) = Self::descriptor_for_source_path(&src_dir, &source_path)
                    else {
                        continue;
                    };
                    if let Ok(cert_store) = CertificateStore::load(path) {
                        cache.insert(descriptor, cert_store);
                    }
                }
            }
        }

        let mut build_cache = BuildCache {
            cache,
            manifests,
            src_dir,
        };

        if load_legacy_cache {
            build_cache.load_legacy_certificates(&build_dir)?;
        }

        Ok(build_cache)
    }

    fn load_legacy_certificates(&mut self, build_dir: &Path) -> Result<(), ManifestError> {
        if !build_dir.exists() {
            return Ok(());
        }

        for entry in WalkDir::new(build_dir).into_iter().filter_map(Result::ok) {
            if !entry.file_type().is_file() {
                continue;
            }
            let path = entry.path();
            if path.extension().and_then(|ext| ext.to_str()) != Some("jsonl") {
                continue;
            }
            let Some(descriptor) = Self::legacy_descriptor_for_cert_path(build_dir, path) else {
                continue;
            };
            let Some(source_path) = self.source_path_for_descriptor(&descriptor) else {
                continue;
            };
            if !source_path.is_file() || self.is_package_interface_path(&source_path) {
                continue;
            }
            if self.cache.contains_key(&descriptor) {
                continue;
            }
            if let Ok(cert_store) = CertificateStore::load(path) {
                self.cache.insert(descriptor, cert_store);
            }
        }

        Ok(())
    }

    fn legacy_descriptor_for_cert_path(
        build_dir: &Path,
        cert_path: &Path,
    ) -> Option<ModuleDescriptor> {
        let relative = cert_path.strip_prefix(build_dir).ok()?;
        let without_extension = relative.with_extension("");
        let parts = without_extension
            .components()
            .map(|component| component.as_os_str().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        if parts.is_empty() {
            None
        } else {
            Some(ModuleDescriptor::Name(parts))
        }
    }

    fn cert_path_for_source_path(source_path: &Path) -> Option<PathBuf> {
        let parent = source_path.parent()?;
        let stem = source_path.file_stem()?.to_string_lossy();
        Some(parent.join(CERTS_DIR).join(format!("{}.jsonl", stem)))
    }

    fn source_path_from_cert_path(cert_path: &Path) -> Option<PathBuf> {
        let certs_dir = cert_path.parent()?;
        if certs_dir.file_name().and_then(|name| name.to_str()) != Some(CERTS_DIR) {
            return None;
        }
        let source_dir = certs_dir.parent()?;
        let stem = cert_path.file_stem()?.to_string_lossy();
        Some(source_dir.join(format!("{}.ac", stem)))
    }

    fn package_manifest_path(package_root: &Path) -> PathBuf {
        package_root.join(CERTS_DIR).join("manifest.json")
    }

    fn descriptor_for_source_path(src_dir: &Path, source_path: &Path) -> Option<ModuleDescriptor> {
        if path_has_certs_component(source_path) {
            return None;
        }
        let relative = source_path.strip_prefix(src_dir).ok()?;
        if source_path.extension().and_then(|ext| ext.to_str()) != Some("ac") {
            return None;
        }

        let mut parts = relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        let last = parts.pop()?;
        match last.as_str() {
            PACKAGE_INTERFACE_FILE => {}
            _ => parts.push(last.strip_suffix(".ac")?.to_string()),
        }
        if parts.is_empty() {
            return None;
        }
        Some(ModuleDescriptor::Name(parts))
    }

    fn source_path_for_descriptor(&self, descriptor: &ModuleDescriptor) -> Option<PathBuf> {
        let ModuleDescriptor::Name(parts) = descriptor else {
            return None;
        };
        if parts.is_empty() {
            return None;
        }

        let mut directory = self.src_dir.clone();
        for part in &parts[..parts.len() - 1] {
            directory.push(part);
        }
        let last = parts.last()?;
        let file_path = directory.join(format!("{}.ac", last));
        let interface_path = directory.join(last).join(PACKAGE_INTERFACE_FILE);

        if interface_path.is_file() {
            Some(interface_path)
        } else if file_path.is_file() {
            Some(file_path)
        } else {
            Some(file_path)
        }
    }

    fn explicit_package_root_for_source_path(&self, source_path: &Path) -> Option<PathBuf> {
        let mut current = source_path.parent()?;
        while current != self.src_dir.as_path() {
            if current.join(PACKAGE_INTERFACE_FILE).is_file() {
                return Some(current.to_path_buf());
            }
            current = current.parent()?;
        }
        None
    }

    fn package_root_for_source_path(&self, source_path: &Path) -> Option<PathBuf> {
        if source_path.strip_prefix(&self.src_dir).is_err() {
            return None;
        }
        Some(
            self.explicit_package_root_for_source_path(source_path)
                .unwrap_or_else(|| self.src_dir.clone()),
        )
    }

    fn package_root_for_descriptor(&self, descriptor: &ModuleDescriptor) -> Option<PathBuf> {
        let source_path = self.source_path_for_descriptor(descriptor)?;
        self.package_root_for_source_path(&source_path)
    }

    fn is_package_interface_path(&self, source_path: &Path) -> bool {
        source_path.file_name().and_then(|name| name.to_str()) == Some(PACKAGE_INTERFACE_FILE)
            && self
                .explicit_package_root_for_source_path(source_path)
                .as_ref()
                .is_some_and(|root| source_path == root.join(PACKAGE_INTERFACE_FILE))
    }

    fn implementation_key_for_source_path(
        package_root: &Path,
        source_path: &Path,
    ) -> Option<String> {
        normalize_relative_path(source_path.strip_prefix(package_root).ok()?)
    }

    fn package_name_for_root(&self, package_root: &Path) -> Option<String> {
        let relative = package_root.strip_prefix(&self.src_dir).ok()?;
        if relative.as_os_str().is_empty() {
            return None;
        }
        Some(
            relative
                .components()
                .map(|component| component.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("."),
        )
    }

    fn dependency_key_for_descriptor(&self, descriptor: &ModuleDescriptor) -> Option<String> {
        let source_path = self.source_path_for_descriptor(descriptor)?;
        let package_root = self.package_root_for_source_path(&source_path)?;
        if package_root == self.src_dir {
            Some(descriptor.to_string())
        } else {
            self.package_name_for_root(&package_root)
        }
    }

    fn record_package_state(
        &mut self,
        descriptor: &ModuleDescriptor,
        hash: blake3::Hash,
        dependencies: &[(ModuleDescriptor, blake3::Hash)],
    ) {
        let Some(source_path) = self.source_path_for_descriptor(descriptor) else {
            return;
        };
        let Some(package_root) = self.package_root_for_source_path(&source_path) else {
            return;
        };
        let is_interface = self.is_package_interface_path(&source_path);
        let dependency_entries = dependencies
            .iter()
            .filter_map(|(dependency, dependency_hash)| {
                if self.package_root_for_descriptor(dependency).as_ref() == Some(&package_root) {
                    return None;
                }
                self.dependency_key_for_descriptor(dependency)
                    .map(|key| (key, *dependency_hash))
            })
            .collect::<Vec<_>>();
        let manifest = self.manifests.entry(package_root.clone()).or_default();

        if is_interface {
            manifest.record_interface(hash);
        } else if let Some(key) =
            Self::implementation_key_for_source_path(&package_root, &source_path)
        {
            manifest.record_implementation(key, hash);
        }

        for (key, dependency_hash) in dependency_entries {
            manifest.record_dependency(key, dependency_hash);
        }
    }

    pub fn insert(
        &mut self,
        module: ModuleDescriptor,
        certificates: CertificateStore,
        hash: Option<blake3::Hash>,
        dependencies: &[(ModuleDescriptor, blake3::Hash)],
    ) {
        if let Some(hash) = hash {
            self.record_package_state(&module, hash, dependencies);
        }
        self.cache.insert(module, certificates);
    }

    pub fn record_unchanged(
        &mut self,
        module: &ModuleDescriptor,
        hash: blake3::Hash,
        dependencies: &[(ModuleDescriptor, blake3::Hash)],
    ) {
        self.record_package_state(module, hash, dependencies);
    }

    pub fn make_worklist(&self, descriptor: &ModuleDescriptor) -> CertificateWorklist {
        self.cache
            .get(descriptor)
            .map(|store| CertificateWorklist::new(store.clone()))
            .unwrap_or_else(|| CertificateWorklist::new(CertificateStore { certs: vec![] }))
    }

    pub fn get_certificates(&self, descriptor: &ModuleDescriptor) -> Option<&CertificateStore> {
        self.cache.get(descriptor)
    }

    /// Returns the number of modules in the cache.
    pub fn module_count(&self) -> usize {
        self.cache.len()
    }

    /// Merge certificates and manifests from another cache into this one.
    /// Only copies certificates for modules that don't already exist in this cache.
    /// This is used when write_cache is false to preserve in-memory certificates.
    pub fn merge_certificates_from(&mut self, old_cache: &BuildCache) {
        for (descriptor, cert_store) in &old_cache.cache {
            if !self.cache.contains_key(descriptor) {
                self.cache.insert(descriptor.clone(), cert_store.clone());
            }
        }
        self.merge_missing_manifests_from(old_cache);
    }

    fn merge_missing_manifests_from(&mut self, old_cache: &BuildCache) {
        for (package_root, old_manifest) in &old_cache.manifests {
            self.manifests
                .entry(package_root.clone())
                .or_default()
                .merge_missing_from(old_manifest);
        }
    }

    /// Merge newly produced certificates and manifest entries from another cache.
    ///
    /// Parallel module workers produce independent cache fragments. The parent build
    /// merges them in module order before the usual save/merge-with-old-cache step.
    pub fn merge_updates_from(&mut self, other: BuildCache) {
        for (descriptor, cert_store) in other.cache {
            self.cache.insert(descriptor, cert_store);
        }
        for (package_root, manifest) in other.manifests {
            let entry = self.manifests.entry(package_root).or_default();
            if manifest.interface.is_some() {
                entry.interface = manifest.interface;
            }
            for (path, hash) in manifest.implementation {
                entry.implementation.insert(path, hash);
            }
            for (name, hash) in manifest.dependencies {
                entry.dependencies.insert(name, hash);
            }
        }
    }

    pub fn get_certificates_mut(
        &mut self,
        descriptor: &ModuleDescriptor,
    ) -> Option<&mut CertificateStore> {
        self.cache.get_mut(descriptor)
    }

    pub fn manifest_matches(&self, descriptor: &ModuleDescriptor, hash: blake3::Hash) -> bool {
        let Some(source_path) = self.source_path_for_descriptor(descriptor) else {
            return false;
        };
        let Some(package_root) = self.package_root_for_source_path(&source_path) else {
            return false;
        };
        let Some(manifest) = self.manifests.get(&package_root) else {
            return false;
        };

        if self.is_package_interface_path(&source_path) {
            manifest.matches_interface(hash)
        } else {
            let Some(key) = Self::implementation_key_for_source_path(&package_root, &source_path)
            else {
                return false;
            };
            manifest.matches_implementation(&key, hash)
        }
    }

    pub fn dependency_manifests_needing_update(
        &self,
        old_cache: &BuildCache,
        preserve_old_manifest_entries: bool,
    ) -> Vec<PathBuf> {
        let mut paths = Vec::new();
        for (package_root, manifest) in &self.manifests {
            let expected_dependencies = if preserve_old_manifest_entries {
                let mut dependencies = old_cache
                    .manifests
                    .get(package_root)
                    .map(|manifest| manifest.dependencies.clone())
                    .unwrap_or_default();
                for (name, hash) in &manifest.dependencies {
                    dependencies.insert(name.clone(), hash.clone());
                }
                dependencies
            } else {
                manifest.dependencies.clone()
            };

            let old_dependencies = old_cache
                .manifests
                .get(package_root)
                .map(|manifest| &manifest.dependencies);
            let dependencies_match = match old_dependencies {
                Some(old_dependencies) => old_dependencies == &expected_dependencies,
                None => expected_dependencies.is_empty(),
            };
            if !dependencies_match {
                paths.push(Self::package_manifest_path(package_root));
            }
        }
        paths.sort();
        paths.dedup();
        paths
    }

    fn cert_path_for_descriptor(&self, descriptor: &ModuleDescriptor) -> Option<PathBuf> {
        match descriptor {
            ModuleDescriptor::Name(_) => {
                let source_path = self.source_path_for_descriptor(descriptor)?;
                if self.is_package_interface_path(&source_path) {
                    return None;
                }
                Self::cert_path_for_source_path(&source_path)
            }
            ModuleDescriptor::File(ac_path) => {
                if ac_path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    Some(ac_path.with_extension("jsonl"))
                } else {
                    None
                }
            }
            ModuleDescriptor::Anonymous => None,
        }
    }

    /// Save the build cache, merging in information from an old cache.
    /// If preserve_old_manifest_entries is false (full build), only packages in the new
    /// cache will be in the manifest. If true (partial build), old manifest entries
    /// for modules not in the new cache will be preserved.
    pub fn save_merging_old(
        &mut self,
        old_cache: &BuildCache,
        preserve_old_manifest_entries: bool,
    ) -> Result<(), Box<dyn Error>> {
        if preserve_old_manifest_entries {
            self.merge_missing_manifests_from(old_cache);
        }

        for (descriptor, cert_store) in &self.cache {
            let Some(path) = self.cert_path_for_descriptor(descriptor) else {
                continue;
            };
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            cert_store.save(&path)?;
        }

        for (package_root, manifest) in &self.manifests {
            if manifest.is_empty() {
                continue;
            }
            manifest.save(&Self::package_manifest_path(package_root))?;
        }

        if !preserve_old_manifest_entries {
            for package_root in old_cache.manifests.keys() {
                if self.manifests.contains_key(package_root) {
                    continue;
                }
                let path = Self::package_manifest_path(package_root);
                if path.exists() {
                    std::fs::remove_file(path)?;
                }
            }
        }

        for (descriptor, cert_store) in &old_cache.cache {
            if !self.cache.contains_key(descriptor) {
                self.cache.insert(descriptor.clone(), cert_store.clone());
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certificate::{Certificate, CertificateStore};

    #[test]
    fn package_layout_paths_are_source_local() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir_all(src.join("pkg").join("sub")).unwrap();
        std::fs::write(src.join("pkg").join("interface.ac"), "").unwrap();
        std::fs::write(src.join("pkg").join("sub").join("foo.ac"), "").unwrap();

        let cache = BuildCache::new(src.clone(), temp.path().join("build"));
        let descriptor = ModuleDescriptor::name("pkg.sub.foo");
        let source_path = cache.source_path_for_descriptor(&descriptor).unwrap();
        assert_eq!(source_path, src.join("pkg").join("sub").join("foo.ac"));
        assert_eq!(
            cache.cert_path_for_descriptor(&descriptor).unwrap(),
            src.join("pkg")
                .join("sub")
                .join(CERTS_DIR)
                .join("foo.jsonl")
        );
        assert_eq!(
            cache
                .package_root_for_descriptor(&descriptor)
                .expect("package root should exist"),
            src.join("pkg")
        );
        assert_eq!(
            BuildCache::package_manifest_path(&src.join("pkg")),
            src.join("pkg").join(CERTS_DIR).join("manifest.json")
        );
    }

    #[test]
    fn old_style_files_use_global_package_manifest() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir_all(src.join("int")).unwrap();
        std::fs::write(src.join("int").join("gcd.ac"), "").unwrap();

        let cache = BuildCache::new(src.clone(), temp.path().join("build"));
        let descriptor = ModuleDescriptor::name("int.gcd");
        assert_eq!(
            cache
                .package_root_for_descriptor(&descriptor)
                .expect("package root should exist"),
            src
        );
    }

    #[test]
    fn legacy_build_certificates_load_for_format_migration() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        let build = temp.path().join("build");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::create_dir_all(&build).unwrap();
        std::fs::write(src.join("foo.ac"), "theorem goal { true }\n").unwrap();
        CertificateStore {
            certs: vec![Certificate::new("goal".to_string(), Vec::new())],
        }
        .save(&build.join("foo.jsonl"))
        .unwrap();

        let new_only = BuildCache::load(src.clone(), build.clone(), false).unwrap();
        assert!(new_only
            .get_certificates(&ModuleDescriptor::name("foo"))
            .is_none());

        let migrated = BuildCache::load(src, build, true).unwrap();
        assert!(migrated
            .get_certificates(&ModuleDescriptor::name("foo"))
            .is_some());
    }
}
