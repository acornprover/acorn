use std::error::Error;
use std::path::PathBuf;
use std::sync::Arc;

use dashmap::mapref::entry::Entry;
use dashmap::DashMap;
use walkdir::WalkDir;

use crate::module::ModuleDescriptor;
use crate::module_cache::ModuleCache;

// The BuildCache contains information for each module, from the last time it was cleanly built.
// This enables skipping verification for modules that haven't changed.
// We read once at startup, and write whole files at a time when needed.
// Hopefully that makes it okay to not lock it. But we might need to be better about this.
#[derive(Clone)]
pub struct BuildCache {
    // A per-module hash, plus filtering information.
    module_caches: Arc<DashMap<ModuleDescriptor, ModuleCache>>,

    // A directory to persist the cache in.
    directory: Option<PathBuf>,

    // Whether it's okay to write to the cache directory.
    // If false, the cache will not be saved to disk.
    writable: bool,
}

impl BuildCache {
    // Creates a new build cache, based on data stored on disk if there is any.
    pub fn new(directory: Option<PathBuf>, writable: bool) -> BuildCache {
        let inner = DashMap::new();
        if let Some(root) = &directory {
            if root.exists() {
                for entry in WalkDir::new(root).into_iter().filter_map(Result::ok) {
                    if let Some((desc, cache)) = ModuleCache::load_relative(root, entry.path()) {
                        inner.insert(desc, cache);
                    }
                }
            }
        }
        BuildCache {
            module_caches: Arc::new(inner),
            directory,
            writable,
        }
    }

    // Gets the module cache for a module descriptor
    pub fn get_cloned_module_cache(&self, descriptor: &ModuleDescriptor) -> Option<ModuleCache> {
        self.module_caches
            .get(descriptor)
            .map(|entry| entry.value().clone())
    }

    // Inserts a module cache for a module descriptor.
    // Saves the cache if it conflicts with the old one.
    pub fn insert_module_cache(
        &self,
        descriptor: ModuleDescriptor,
        module_cache: ModuleCache,
    ) -> Result<(), Box<dyn Error>> {
        match self.module_caches.entry(descriptor) {
            Entry::Occupied(mut entry) => {
                if module_cache.requires_save(entry.get()) {
                    // Overwrite the old on-disk cache
                    self.save_module_cache(entry.key(), &module_cache)?;
                }

                *entry.get_mut() = module_cache;
            }
            Entry::Vacant(entry) => {
                // Create a new on-disk cache for this module
                self.save_module_cache(entry.key(), &module_cache)?;
                entry.insert(module_cache);
            }
        }
        Ok(())
    }

    // Returns the number of entries in the cache
    pub fn num_module_caches(&self) -> usize {
        self.module_caches.len()
    }

    // Saves the cache for one module.
    fn save_module_cache(
        &self,
        descriptor: &ModuleDescriptor,
        module_cache: &ModuleCache,
    ) -> Result<(), Box<dyn Error>> {
        if !self.writable {
            return Ok(());
        }
        let directory = match &self.directory {
            Some(directory) => directory,
            None => return Ok(()),
        };

        // Iterate over inner
        if let ModuleDescriptor::Name(parts) = descriptor {
            if parts.is_empty() {
                return Ok(());
            }
            let mut parts = parts.clone();
            let last = parts.pop().unwrap();
            let mut path = directory.clone();
            for part in parts {
                path.push(part);
                // Make the directory, if needed
                if !path.exists() {
                    std::fs::create_dir(&path)?;
                }
            }
            path.push(format!("{}.yaml", last));
            module_cache.save(&path)?;
        }

        Ok(())
    }
}
