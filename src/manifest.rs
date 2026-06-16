use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

/// Errors that can occur when loading a manifest.
#[derive(Debug)]
pub enum ManifestError {
    /// IO error (file not found, permission denied, etc.) - recoverable by starting fresh
    Io(std::io::Error),
    /// JSON parse error - recoverable by starting fresh
    Parse(serde_json::Error),
    /// Project format version is newer than this binary supports - user must update Acorn
    VersionTooNew { found: u32, supported: u32 },
    /// Project format version is older than this binary writes - user must opt in to updating
    /// acornlib
    VersionTooOld { found: u32, supported: u32 },
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ManifestError::Io(e) => write!(f, "IO error loading manifest: {}", e),
            ManifestError::Parse(e) => write!(f, "Parse error loading manifest: {}", e),
            ManifestError::VersionTooNew { found, supported } => write!(
                f,
                "The library is using project format {}, but this version of Acorn only supports up to project format {}. \
                 Please update your version of Acorn.",
                found, supported
            ),
            ManifestError::VersionTooOld { found, supported } => write!(
                f,
                "The library is using project format {}, but this version of Acorn writes project format {}. \
                 Pass --update-version to update the library project format.",
                found, supported
            ),
        }
    }
}

impl Error for ManifestError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ManifestError::Io(e) => Some(e),
            ManifestError::Parse(e) => Some(e),
            ManifestError::VersionTooNew { .. } | ManifestError::VersionTooOld { .. } => None,
        }
    }
}

impl From<std::io::Error> for ManifestError {
    fn from(e: std::io::Error) -> Self {
        ManifestError::Io(e)
    }
}

impl From<serde_json::Error> for ManifestError {
    fn from(e: serde_json::Error) -> Self {
        ManifestError::Parse(e)
    }
}

/// The current version of the project format.
/// Increment this when making breaking changes to the manifest structure, or to the structure
/// of other components of the cached build or project layout.
pub const PROJECT_FORMAT_VERSION: u32 = 25;

/// A newtype wrapper for module names, created by joining parts with "."
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ModuleName(String);

impl ModuleName {
    /// Create a ModuleName from parts by joining with "."
    pub fn new(parts: &[String]) -> Self {
        ModuleName(parts.join("."))
    }

    /// Get the underlying string
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for ModuleName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A newtype wrapper for hex-encoded hashes
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HexHash(String);

impl HexHash {
    /// Create a HexHash from a blake3::Hash
    pub fn new(hash: blake3::Hash) -> Self {
        HexHash(hash.to_hex().to_string())
    }

    /// Get the underlying hex string
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for HexHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The per-package record of the last successful checked state.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackageManifest {
    /// Hash of interface.ac for explicit packages. Omitted for the implicit global package.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface: Option<HexHash>,

    /// Hashes of package implementation files, keyed by package-relative source path.
    #[serde(default)]
    pub implementation: BTreeMap<String, HexHash>,

    /// Hashes of external public APIs this package was checked against.
    #[serde(default)]
    pub dependencies: BTreeMap<String, HexHash>,
}

impl PackageManifest {
    pub fn record_interface(&mut self, hash: blake3::Hash) {
        self.interface = Some(HexHash::new(hash));
    }

    pub fn record_implementation(&mut self, path: String, hash: blake3::Hash) {
        self.implementation.insert(path, HexHash::new(hash));
    }

    pub fn record_dependency(&mut self, name: String, hash: blake3::Hash) {
        self.dependencies.insert(name, HexHash::new(hash));
    }

    pub fn matches_interface(&self, hash: blake3::Hash) -> bool {
        self.interface.as_ref() == Some(&HexHash::new(hash))
    }

    pub fn matches_implementation(&self, path: &str, hash: blake3::Hash) -> bool {
        self.implementation
            .get(path)
            .is_some_and(|stored| stored == &HexHash::new(hash))
    }

    pub fn merge_missing_from(&mut self, old: &PackageManifest) {
        if self.interface.is_none() {
            self.interface = old.interface.clone();
        }
        for (path, hash) in &old.implementation {
            self.implementation
                .entry(path.clone())
                .or_insert_with(|| hash.clone());
        }
        for (name, hash) in &old.dependencies {
            self.dependencies
                .entry(name.clone())
                .or_insert_with(|| hash.clone());
        }
    }

    pub fn is_empty(&self) -> bool {
        self.interface.is_none() && self.implementation.is_empty() && self.dependencies.is_empty()
    }

    /// Save the package manifest atomically.
    pub fn save(&self, path: &Path) -> Result<(), Box<dyn Error>> {
        let Some(parent) = path.parent() else {
            return Err("manifest path has no parent directory".into());
        };
        std::fs::create_dir_all(parent)?;
        let json = serde_json::to_string_pretty(self)?;
        let temp_path = path.with_file_name(".manifest.json.tmp");
        let mut file = File::create(&temp_path)?;
        file.write_all(json.as_bytes())?;
        file.write_all(b"\n")?;
        file.sync_all()?;
        std::fs::rename(&temp_path, path)?;
        Ok(())
    }

    pub fn load(path: &Path) -> Result<Self, ManifestError> {
        let mut file = File::open(path)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(serde_json::from_str(&contents)?)
    }
}

/// The manifest structure that stores module hashes
/// This is the legacy root build/manifest.json format. New cache records are package-local
/// PackageManifest files; this remains for project_format_version fallback during migration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    /// Version of the manifest format
    pub version: u32,

    /// Map from module names to their content hashes.
    /// This only includes modules with "good" build status.
    pub modules: BTreeMap<ModuleName, HexHash>,
}

impl Manifest {
    /// Create a new empty manifest with the current version
    pub fn new() -> Self {
        Manifest {
            version: PROJECT_FORMAT_VERSION,
            modules: BTreeMap::new(),
        }
    }

    /// The project format version written by this binary.
    pub fn current_version() -> u32 {
        PROJECT_FORMAT_VERSION
    }

    /// Add or update a module hash in the manifest
    pub fn insert(&mut self, parts: &[String], hash: blake3::Hash) {
        let module_name = ModuleName::new(parts);
        let hex_hash = HexHash::new(hash);
        self.modules.insert(module_name, hex_hash);
    }

    /// Check if an entry matches the given module and hash
    pub fn matches_entry(&self, parts: &[String], hash: blake3::Hash) -> bool {
        if self.version != PROJECT_FORMAT_VERSION {
            return false;
        }
        let module_name = ModuleName::new(parts);
        match self.modules.get(&module_name) {
            Some(stored_hash) => stored_hash == &HexHash::new(hash),
            None => false,
        }
    }

    /// Check if a module exists in the manifest (regardless of hash)
    pub fn contains(&self, parts: &[String]) -> bool {
        let module_name = ModuleName::new(parts);
        self.modules.contains_key(&module_name)
    }

    /// Save the manifest to manifest.json in the build directory atomically
    /// Writes to a temporary file first, then renames it to avoid corruption
    pub fn save(&self, build_dir: &Path) -> Result<(), Box<dyn Error>> {
        let path = build_dir.join("manifest.json");
        let json = serde_json::to_string_pretty(&self)?;

        // Create a temporary file in the same directory as the target
        let temp_path = build_dir.join(".manifest.json.tmp");

        // Write to the temporary file
        let mut file = File::create(&temp_path)?;
        file.write_all(json.as_bytes())?;
        file.sync_all()?; // Ensure data is flushed to disk

        // Atomically rename the temp file to the target path
        std::fs::rename(&temp_path, path)?;

        Ok(())
    }

    /// Load a manifest from manifest.json in the build directory.
    pub fn load(build_dir: &Path) -> Result<Self, ManifestError> {
        let path = build_dir.join("manifest.json");
        let mut file = File::open(path)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        let manifest: Manifest = serde_json::from_str(&contents)?;

        Ok(manifest)
    }

    /// Load a manifest from the build directory, or create a new one if it doesn't exist.
    /// Recoverable errors (IO, parse) result in a fresh manifest.
    pub fn load_or_create(build_dir: &Path) -> Result<Self, ManifestError> {
        match Self::load(build_dir) {
            Ok(manifest) => Ok(manifest),
            Err(ManifestError::Io(_)) | Err(ManifestError::Parse(_)) => Ok(Self::new()),
            Err(e @ ManifestError::VersionTooNew { .. })
            | Err(e @ ManifestError::VersionTooOld { .. }) => Err(e),
        }
    }
}

impl Default for Manifest {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_manifest_save_load() {
        let temp_dir = tempdir().expect("Failed to create temp directory");
        let build_dir = temp_dir.path();

        let mut manifest = Manifest::new();

        // Add some test data
        let parts = vec!["test".to_string(), "module".to_string()];
        let hash = blake3::hash(b"test content");
        manifest.insert(&parts, hash);

        // Save the manifest
        manifest.save(build_dir).expect("Failed to save manifest");

        // Load it back
        let loaded = Manifest::load(build_dir).expect("Failed to load manifest");

        // Verify it matches
        assert_eq!(loaded.version, manifest.version);
        assert_eq!(loaded.modules.len(), 1);
        assert!(loaded.matches_entry(&parts, hash));

        // Test load_or_create with existing manifest
        let loaded2 = Manifest::load_or_create(build_dir).expect("Failed to load_or_create");
        assert_eq!(loaded2.modules.len(), 1);

        // Test load_or_create with non-existent directory
        let new_dir = temp_dir.path().join("nonexistent");
        let created = Manifest::load_or_create(&new_dir).expect("Failed to load_or_create");
        assert_eq!(created.modules.len(), 0);
    }
}
