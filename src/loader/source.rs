use std::io::{self, IsTerminal};
use std::path::{Path, PathBuf};

pub fn read_source_text<E>(
    path: &Path,
    mut read_file: impl FnMut(&Path) -> Result<String, E>,
) -> Result<String, String>
where
    E: ToString,
{
    let Some(path_string) = path.to_str() else {
        return read_file(path).map_err(|e| e.to_string());
    };

    if path_string == "<stdin>" {
        return read_stdin_append(String::new());
    }

    if let Some(path2) = path_string.strip_prefix("-:") {
        println!("Path: {}", path2);
        let prefix = read_file(&PathBuf::from(path2)).map_err(|e| e.to_string())?;
        return read_stdin_append(prefix);
    }

    read_file(path).map_err(|e| e.to_string())
}

fn read_stdin_append(mut text: String) -> Result<String, String> {
    if io::stdin().is_terminal() {
        return Err("cannot read stdin in an active terminal".to_string());
    }
    let _ = io::stdin().lock();
    for line in io::stdin().lines() {
        text.push_str(&line.map_err(|e| e.to_string())?);
        text.push('\n');
    }
    Ok(text)
}
