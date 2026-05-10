use crate::tests::support::verify_succeeds;
use std::env;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

const MDTEST_DIR: &str = "src/tests/prover/mdtest";
const FILTER_ENV: &str = "ACORN_MDTEST_FILTER";

#[derive(Debug, Clone, PartialEq, Eq)]
struct MdCase {
    id: String,
    start_line: usize,
    source: String,
}

fn mdtest_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(MDTEST_DIR)
}

fn discover_markdown_files(root: &Path) -> Vec<PathBuf> {
    let mut files = WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .map(|entry| entry.into_path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "md"))
        .filter(|path| path.file_name().is_none_or(|name| name != "README.md"))
        .collect::<Vec<_>>();
    files.sort();
    files
}

fn parse_heading(line: &str) -> Option<(usize, String)> {
    if !line.starts_with('#') {
        return None;
    }

    let level = line.bytes().take_while(|&b| b == b'#').count();
    let title = line[level..].trim();
    if title.is_empty() {
        return None;
    }
    Some((level, title.to_string()))
}

fn parse_fence_start(line: &str) -> Option<&str> {
    line.strip_prefix("```").map(str::trim)
}

fn is_checkable_language(language: &str) -> bool {
    matches!(language, "ac" | "acorn")
}

fn build_case_id(relative_path: &Path, headings: &[(usize, String)]) -> String {
    let relative_path = relative_path.display();
    if headings.is_empty() {
        return relative_path.to_string();
    }

    let heading_path = headings
        .iter()
        .map(|(_, title)| title.as_str())
        .collect::<Vec<_>>()
        .join(" / ");
    format!("{relative_path} :: {heading_path}")
}

fn parse_cases(relative_path: &Path, markdown: &str) -> Result<Vec<MdCase>, String> {
    let lines = markdown.lines().collect::<Vec<_>>();
    let mut headings = Vec::<(usize, String)>::new();
    let mut cases = Vec::<MdCase>::new();

    let mut index = 0usize;
    while index < lines.len() {
        let line = lines[index];

        if let Some((level, title)) = parse_heading(line) {
            while headings
                .last()
                .is_some_and(|(other_level, _)| *other_level >= level)
            {
                headings.pop();
            }
            headings.push((level, title));
            index += 1;
            continue;
        }

        if let Some(language) = parse_fence_start(line) {
            let block_start_line = index + 2;
            index += 1;
            let mut block_lines = Vec::new();
            while index < lines.len() {
                let block_line = lines[index];
                if parse_fence_start(block_line).is_some() {
                    break;
                }
                block_lines.push(block_line);
                index += 1;
            }
            if index == lines.len() {
                return Err(format!(
                    "unterminated code block starting at line {}",
                    block_start_line - 1
                ));
            }
            if is_checkable_language(language) {
                let id = build_case_id(relative_path, &headings);
                cases.push(MdCase {
                    id,
                    start_line: block_start_line,
                    source: block_lines.join("\n"),
                });
            }
            index += 1;
            continue;
        }

        index += 1;
    }
    Ok(cases)
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<String>() {
        return message.clone();
    }
    if let Some(message) = payload.downcast_ref::<&str>() {
        return message.to_string();
    }
    "non-string panic payload".to_string()
}

#[test]
fn mdtests() {
    let root = mdtest_root();
    let files = discover_markdown_files(&root);
    assert!(
        !files.is_empty(),
        "no markdown fixtures found under {}",
        root.display()
    );

    let filter = env::var(FILTER_ENV).ok();
    let mut matched_cases = 0usize;
    let mut failures = Vec::new();

    for path in files {
        let relative_path = path
            .strip_prefix(&root)
            .expect("markdown fixture should live under the mdtest root");
        let markdown = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed reading {}: {}", relative_path.display(), err));
        let cases = parse_cases(relative_path, &markdown).unwrap_or_else(|err| {
            panic!("failed parsing {}: {}", relative_path.display(), err);
        });

        for case in cases {
            if filter
                .as_ref()
                .is_some_and(|filter| !case.id.contains(filter))
            {
                continue;
            }

            matched_cases += 1;
            if let Err(payload) = catch_unwind(AssertUnwindSafe(|| verify_succeeds(&case.source))) {
                let message = panic_message(payload);
                failures.push(format!(
                    "{}:{}\n{}",
                    case.id,
                    case.start_line,
                    message.trim()
                ));
            }
        }
    }

    if let Some(filter) = filter {
        assert!(
            matched_cases > 0,
            "no mdtests matched {}={}",
            FILTER_ENV,
            filter
        );
    } else {
        assert!(matched_cases > 0, "no mdtests were discovered");
    }

    assert!(
        failures.is_empty(),
        "mdtest failures:\n\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn parses_root_case() {
    let cases = parse_cases(
        Path::new("smoke.md"),
        "```acorn\nlet a: Bool = axiom\ntheorem { a implies a }\n```",
    )
    .expect("markdown should parse");
    assert_eq!(
        cases,
        vec![MdCase {
            id: "smoke.md".to_string(),
            start_line: 2,
            source: "let a: Bool = axiom\ntheorem { a implies a }".to_string(),
        }]
    );
}

#[test]
fn splits_multiple_blocks_in_one_section() {
    let cases = parse_cases(
        Path::new("language/example.md"),
        r#"# Example

Some prose.

```ac
let a: Bool = axiom
```

More prose.

```acorn
theorem {
    a implies a
}
```
"#,
    )
    .expect("markdown should parse");
    assert_eq!(
        cases,
        vec![
            MdCase {
                id: "language/example.md :: Example".to_string(),
                start_line: 6,
                source: "let a: Bool = axiom".to_string(),
            },
            MdCase {
                id: "language/example.md :: Example".to_string(),
                start_line: 12,
                source: "theorem {\n    a implies a\n}".to_string(),
            },
        ]
    );
}

#[test]
fn uses_nested_headings_in_case_names() {
    let cases = parse_cases(
        Path::new("language/example.md"),
        r#"# Constraints

## Easy

```acorn
theorem { true }
```
"#,
    )
    .expect("markdown should parse");
    assert_eq!(
        cases,
        vec![MdCase {
            id: "language/example.md :: Constraints / Easy".to_string(),
            start_line: 6,
            source: "theorem { true }".to_string(),
        }]
    );
}
