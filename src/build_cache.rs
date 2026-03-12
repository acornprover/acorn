use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;
use walkdir::WalkDir;

use crate::certificate::{CertificateStore, CertificateWorklist};
use crate::manifest::{Manifest, ManifestError};
use crate::module::ModuleDescriptor;

/// Cached information about a build.
/// Stored in the 'build' directory.
pub struct BuildCache {
    // The certificates for each module.
    cache: HashMap<ModuleDescriptor, CertificateStore>,

    // A hash for each module.
    pub manifest: Manifest,

    // The directory where all the files are stored.
    build_dir: PathBuf,
}

impl BuildCache {
    pub fn new(build_dir: PathBuf) -> Self {
        BuildCache {
            cache: HashMap::new(),
            manifest: Manifest::new(),
            build_dir,
        }
    }

    /// Load a build cache from a directory containing JSONL files.
    /// Returns an error if the manifest version is too new (user must update Acorn).
    pub fn load(build_dir: PathBuf) -> Result<Self, ManifestError> {
        let mut cache = HashMap::new();
        if build_dir.exists() {
            for entry in WalkDir::new(&build_dir).into_iter().filter_map(Result::ok) {
                let path = entry.path();
                if path.extension().and_then(|ext| ext.to_str()) == Some("jsonl") {
                    if let Some((desc, cert_store)) =
                        CertificateStore::load_relative(&build_dir, path)
                    {
                        cache.insert(desc, cert_store);
                    }
                }
            }
        }

        let manifest = Manifest::load_or_create(&build_dir)?;

        Ok(BuildCache {
            cache,
            manifest,
            build_dir,
        })
    }

    pub fn insert(
        &mut self,
        module: ModuleDescriptor,
        certificates: CertificateStore,
        hash: Option<blake3::Hash>,
    ) {
        // Update the certificate cache
        self.cache.insert(module.clone(), certificates);

        // Update the manifest with the module hash only if there are no warnings
        if let Some(hash) = hash {
            if let ModuleDescriptor::Name(parts) = &module {
                self.manifest.insert(parts, hash);
            }
        }
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

    /// Returns the number of modules in the cache
    pub fn module_count(&self) -> usize {
        self.cache.len()
    }

    /// Merge certificates from another cache into this one.
    /// Only copies certificates for modules that don't already exist in this cache.
    /// This is used when write_cache is false to preserve in-memory certificates.
    pub fn merge_certificates_from(&mut self, old_cache: &BuildCache) {
        for (descriptor, cert_store) in &old_cache.cache {
            if !self.cache.contains_key(descriptor) {
                self.cache.insert(descriptor.clone(), cert_store.clone());
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
        match descriptor {
            ModuleDescriptor::Name(parts) => self.manifest.matches_entry(parts, hash),
            _ => false, // Anonymous modules can't be in the manifest
        }
    }

    /// Save the build cache, merging in information from an old cache.
    /// If preserve_old_manifest_entries is false (full build), only modules in the new
    /// cache will be in the manifest. If true (partial build), old manifest entries
    /// for modules not in the new cache will be preserved.
    pub fn save_merging_old(
        &mut self,
        old_cache: &BuildCache,
        preserve_old_manifest_entries: bool,
    ) -> Result<(), Box<dyn Error>> {
        // Save only the certificate stores that are in this cache.
        // These are the ones that were actually built.
        for (descriptor, cert_store) in &self.cache {
            match descriptor {
                ModuleDescriptor::Name(parts) => {
                    if parts.is_empty() {
                        continue;
                    }
                    let mut parts = parts.clone();
                    let last = parts.pop().unwrap();
                    let mut path = self.build_dir.clone();

                    // Create directory structure for nested modules
                    for part in parts {
                        path.push(part);
                        if !path.exists() {
                            std::fs::create_dir(&path)?;
                        }
                    }

                    // Create the JSONL file for this module's certificates
                    path.push(format!("{}.jsonl", last));
                    cert_store.save(&path)?;
                }
                ModuleDescriptor::File(ac_path) => {
                    // For files outside the library, save the JSONL file alongside the .ac file
                    if ac_path.extension() == Some(std::ffi::OsStr::new("ac")) {
                        let jsonl_path = ac_path.with_extension("jsonl");
                        cert_store.save(&jsonl_path)?;
                    }
                }
                ModuleDescriptor::Anonymous => {
                    // Anonymous modules don't get saved
                }
            }
        }

        // Merge old manifest entries only if this is a partial build
        // In a full build, only modules that were actually processed should remain
        if preserve_old_manifest_entries {
            for (module_name, hex_hash) in &old_cache.manifest.modules {
                if !self.manifest.modules.contains_key(module_name) {
                    self.manifest
                        .modules
                        .insert(module_name.clone(), hex_hash.clone());
                }
            }
        }

        // Save the manifest (merged or not, depending on build type)
        self.manifest.save(&self.build_dir)?;

        // Merge the old certificates so they're available in memory.
        // These already exist on disk, so they don't need to be savced here.
        for (descriptor, cert_store) in &old_cache.cache {
            if !self.cache.contains_key(descriptor) {
                self.cache.insert(descriptor.clone(), cert_store.clone());
            }
        }

        Ok(())
    }
}
