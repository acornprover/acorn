use flate2::read::GzDecoder;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use tar::Archive;

const ARCHIVE_BYTES: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/acornlib.tar.gz"));
const ARCHIVE_HASH: &str = include_str!(concat!(env!("OUT_DIR"), "/acornlib.tar.gz.blake3"));
const CACHE_METADATA_FILE: &str = ".acornlib-cache.json";
const CACHE_METADATA_FORMAT: u32 = 1;

#[derive(Deserialize, Serialize)]
struct CacheMetadata {
    format: u32,
    archive_hash: String,
}

/// Returns a filesystem copy of the acornlib packaged in this binary.
///
/// The caller provides the cache root. This function stores each packaged acornlib
/// under a subdirectory named by the archive hash, so new binaries naturally use a
/// fresh cache entry when their packaged library changes.
pub fn get_or_extract(cache_root: &Path) -> Result<PathBuf, String> {
    let archive_hash = archive_hash();
    let target_root = cache_root.join(archive_hash);
    let acornlib_dir = target_root.join("acornlib");

    if cache_is_valid(&acornlib_dir, archive_hash) {
        return Ok(acornlib_dir);
    }

    fs::create_dir_all(cache_root).map_err(|e| {
        format!(
            "failed to create acornlib cache directory {}: {}",
            cache_root.display(),
            e
        )
    })?;

    let temp_root = cache_root.join(temp_dir_name(archive_hash));
    if temp_root.exists() {
        fs::remove_dir_all(&temp_root).map_err(|e| {
            format!(
                "failed to clear stale acornlib cache directory {}: {}",
                temp_root.display(),
                e
            )
        })?;
    }
    fs::create_dir(&temp_root).map_err(|e| {
        format!(
            "failed to create acornlib cache directory {}: {}",
            temp_root.display(),
            e
        )
    })?;

    let result = extract_to(&temp_root)
        .and_then(|_| verify_layout(&temp_root.join("acornlib")))
        .and_then(|_| write_metadata(&temp_root.join("acornlib"), archive_hash))
        .and_then(|_| install_temp_cache(&temp_root, &target_root, &acornlib_dir, archive_hash));

    if result.is_err() {
        let _ = fs::remove_dir_all(&temp_root);
    }
    result
}

fn archive_hash() -> &'static str {
    ARCHIVE_HASH.trim()
}

fn cache_is_valid(acornlib_dir: &Path, archive_hash: &str) -> bool {
    if verify_layout(acornlib_dir).is_err() {
        return false;
    }

    let metadata_path = acornlib_dir.join(CACHE_METADATA_FILE);
    let Ok(metadata) = fs::read_to_string(metadata_path) else {
        return false;
    };
    let Ok(metadata) = serde_json::from_str::<CacheMetadata>(&metadata) else {
        return false;
    };
    metadata.format == CACHE_METADATA_FORMAT && metadata.archive_hash == archive_hash
}

fn extract_to(target_root: &Path) -> Result<(), String> {
    let decoder = GzDecoder::new(Cursor::new(ARCHIVE_BYTES));
    let mut archive = Archive::new(decoder);
    archive
        .unpack(target_root)
        .map_err(|e| format!("failed to extract packaged acornlib: {}", e))
}

fn verify_layout(acornlib_dir: &Path) -> Result<(), String> {
    if !acornlib_dir.join("acorn.toml").is_file() {
        return Err(format!(
            "packaged acornlib is missing {}",
            acornlib_dir.join("acorn.toml").display()
        ));
    }
    if !acornlib_dir.join("src").is_dir() {
        return Err(format!(
            "packaged acornlib is missing {}",
            acornlib_dir.join("src").display()
        ));
    }
    if !has_package_manifest(&acornlib_dir.join("src")) {
        return Err(format!(
            "packaged acornlib is missing package manifests under {}",
            acornlib_dir.join("src").display()
        ));
    }
    Ok(())
}

fn has_package_manifest(path: &Path) -> bool {
    let Ok(entries) = fs::read_dir(path) else {
        return false;
    };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().and_then(|name| name.to_str()) == Some("certs")
                && path.join("manifest.json").is_file()
            {
                return true;
            }
            if has_package_manifest(&path) {
                return true;
            }
        }
    }
    false
}

fn write_metadata(acornlib_dir: &Path, archive_hash: &str) -> Result<(), String> {
    let metadata = CacheMetadata {
        format: CACHE_METADATA_FORMAT,
        archive_hash: archive_hash.to_string(),
    };
    let metadata = serde_json::to_string_pretty(&metadata)
        .map_err(|e| format!("failed to serialize acornlib cache metadata: {}", e))?;
    fs::write(
        acornlib_dir.join(CACHE_METADATA_FILE),
        format!("{}\n", metadata),
    )
    .map_err(|e| format!("failed to write acornlib cache metadata: {}", e))
}

fn install_temp_cache(
    temp_root: &Path,
    target_root: &Path,
    acornlib_dir: &Path,
    archive_hash: &str,
) -> Result<PathBuf, String> {
    if target_root.exists() {
        if cache_is_valid(acornlib_dir, archive_hash) {
            fs::remove_dir_all(temp_root).map_err(|e| {
                format!(
                    "failed to remove temporary acornlib cache directory {}: {}",
                    temp_root.display(),
                    e
                )
            })?;
            return Ok(acornlib_dir.to_path_buf());
        }
        fs::remove_dir_all(target_root).map_err(|e| {
            format!(
                "failed to replace invalid acornlib cache directory {}: {}",
                target_root.display(),
                e
            )
        })?;
    }

    match fs::rename(temp_root, target_root) {
        Ok(()) => Ok(acornlib_dir.to_path_buf()),
        Err(_) if target_root.exists() && cache_is_valid(acornlib_dir, archive_hash) => {
            let _ = fs::remove_dir_all(temp_root);
            Ok(acornlib_dir.to_path_buf())
        }
        Err(e) => Err(format!(
            "failed to install acornlib cache at {}: {}",
            target_root.display(),
            e
        )),
    }
}

fn temp_dir_name(archive_hash: &str) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    format!(
        ".acornlib-{}-{}-{}",
        archive_hash,
        std::process::id(),
        nanos
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_fs::TempDir;

    #[test]
    fn extracts_packaged_acornlib_once() {
        let temp = TempDir::new().unwrap();
        let first = get_or_extract(temp.path()).unwrap();
        assert!(first.join("acorn.toml").is_file());
        assert!(first.join("src").is_dir());
        assert!(has_package_manifest(&first.join("src")));
        assert!(first.join(CACHE_METADATA_FILE).is_file());

        let metadata = fs::read_to_string(first.join(CACHE_METADATA_FILE)).unwrap();
        assert!(metadata.contains(archive_hash()));

        let second = get_or_extract(temp.path()).unwrap();
        assert_eq!(first, second);
    }
}
