use flate2::write::GzEncoder;
use flate2::{Compression, GzBuilder};
use std::env;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use tar::{Builder, Header};

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let acornlib_dir = manifest_dir
        .join("vscode")
        .join("extension")
        .join("acornlib");
    if !acornlib_dir.join("acorn.toml").is_file() || !acornlib_dir.join("src").is_dir() {
        panic!("missing acornlib checkout at {}", acornlib_dir.display());
    }

    println!("cargo:rerun-if-changed={}", acornlib_dir.display());
    println!(
        "cargo:rerun-if-changed={}",
        acornlib_dir.join("acorn.toml").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        acornlib_dir.join("src").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        acornlib_dir.join("build").display()
    );

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let archive_path = out_dir.join("acornlib.tar.gz");
    write_archive(&acornlib_dir, &archive_path).unwrap();

    let archive = fs::read(&archive_path).unwrap();
    let hash = blake3::hash(&archive).to_hex().to_string();
    fs::write(out_dir.join("acornlib.tar.gz.blake3"), format!("{hash}\n")).unwrap();
}

fn write_archive(acornlib_dir: &Path, archive_path: &Path) -> io::Result<()> {
    let archive_file = File::create(archive_path)?;
    let encoder = GzBuilder::new()
        .mtime(0)
        .write(archive_file, Compression::default());
    let mut archive = Builder::new(encoder);

    let mut files = Vec::new();
    files.push(PathBuf::from("acorn.toml"));
    collect_files(&acornlib_dir.join("src"), Path::new("src"), &mut files)?;
    collect_files(&acornlib_dir.join("build"), Path::new("build"), &mut files)?;
    files.sort();

    for relative_path in files {
        append_file(&mut archive, acornlib_dir, &relative_path)?;
    }

    let encoder: GzEncoder<File> = archive.into_inner()?;
    let mut archive_file = encoder.finish()?;
    archive_file.flush()?;
    Ok(())
}

fn collect_files(path: &Path, relative_path: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    let mut entries = fs::read_dir(path)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.path());

    for entry in entries {
        let file_type = entry.file_type()?;
        let child_relative_path = relative_path.join(entry.file_name());
        if file_type.is_dir() {
            collect_files(&entry.path(), &child_relative_path, files)?;
        } else if file_type.is_file() {
            files.push(child_relative_path);
        }
    }
    Ok(())
}

fn append_file(
    archive: &mut Builder<GzEncoder<File>>,
    acornlib_dir: &Path,
    relative_path: &Path,
) -> io::Result<()> {
    let full_path = acornlib_dir.join(relative_path);
    println!("cargo:rerun-if-changed={}", full_path.display());

    let mut file = File::open(&full_path)?;
    let metadata = file.metadata()?;
    let mut header = Header::new_gnu();
    header.set_entry_type(tar::EntryType::Regular);
    header.set_size(metadata.len());
    header.set_mode(0o644);
    header.set_uid(0);
    header.set_gid(0);
    header.set_mtime(0);
    header.set_cksum();

    archive.append_data(&mut header, tar_entry_path(relative_path), &mut file)?;
    Ok(())
}

fn tar_entry_path(relative_path: &Path) -> String {
    let mut path = String::from("acornlib");
    for component in relative_path.components() {
        path.push('/');
        path.push_str(
            component
                .as_os_str()
                .to_str()
                .expect("acornlib paths must be valid UTF-8"),
        );
    }
    path
}
