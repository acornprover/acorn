use crate::builder::BuildStatus;
use crate::project::{ProjectConfig, UsageMode};
use crate::verifier::{Verifier, VerifierOutput};
use std::env;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

const PTEST_DIR: &str = "src/tests/project/ptest";
const FILTER_ENV: &str = "ACORN_PTEST_FILTER";
const CONFIG_FILE: &str = "ptest.toml";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PtestCommand {
    Verify,
    Check,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PtestExpectation {
    Ok,
    Warning,
    Error,
    SetupError,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PtestMetric {
    GoalsTotal,
    GoalsDone,
    GoalsSuccess,
    PendingModulesTotal,
    PendingGoalsTotal,
    SearchesTotal,
    CertChecksTotal,
    CertsCached,
    ModulesCached,
    NumVerified,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PtestMetricExpectation {
    metric: PtestMetric,
    value: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PtestConfig {
    command: PtestCommand,
    target: Option<String>,
    expectation: PtestExpectation,
    message: Option<String>,
    check_hashes: bool,
    jobs: Option<usize>,
    metrics: Vec<PtestMetricExpectation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PtestCase {
    id: String,
    fixture_dir: PathBuf,
    config: PtestConfig,
}

impl Default for PtestConfig {
    fn default() -> Self {
        Self {
            command: PtestCommand::Verify,
            target: None,
            expectation: PtestExpectation::Ok,
            message: None,
            check_hashes: false,
            jobs: None,
            metrics: Vec::new(),
        }
    }
}

fn ptest_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(PTEST_DIR)
}

fn discover_ptest_dirs(root: &Path) -> Vec<PathBuf> {
    let mut dirs = WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_dir())
        .map(|entry| entry.into_path())
        .filter(|path| path.join(CONFIG_FILE).is_file())
        .collect::<Vec<_>>();
    dirs.sort();
    dirs
}

fn parse_string(raw: &str) -> Result<String, String> {
    let raw = raw.trim();
    let Some(inner) = raw
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
    else {
        return Err(format!("expected quoted string, got '{raw}'"));
    };
    if inner.contains('"') {
        return Err("string escapes are not supported in ptest.toml".to_string());
    }
    Ok(inner.to_string())
}

fn parse_bool(raw: &str) -> Result<bool, String> {
    match raw.trim() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(format!("expected boolean, got '{other}'")),
    }
}

fn parse_command(value: &str) -> Result<PtestCommand, String> {
    match value {
        "verify" => Ok(PtestCommand::Verify),
        "check" => Ok(PtestCommand::Check),
        other => Err(format!("unknown ptest command '{other}'")),
    }
}

fn parse_expectation(value: &str) -> Result<PtestExpectation, String> {
    match value {
        "ok" | "good" | "success" => Ok(PtestExpectation::Ok),
        "warning" | "warn" => Ok(PtestExpectation::Warning),
        "error" => Ok(PtestExpectation::Error),
        "setup_error" | "setup-error" => Ok(PtestExpectation::SetupError),
        other => Err(format!("unknown ptest expectation '{other}'")),
    }
}

fn parse_metric(value: &str) -> Result<PtestMetric, String> {
    match value {
        "goals_total" => Ok(PtestMetric::GoalsTotal),
        "goals_done" => Ok(PtestMetric::GoalsDone),
        "goals_success" => Ok(PtestMetric::GoalsSuccess),
        "pending_modules_total" => Ok(PtestMetric::PendingModulesTotal),
        "pending_goals_total" => Ok(PtestMetric::PendingGoalsTotal),
        "searches_total" => Ok(PtestMetric::SearchesTotal),
        "cert_checks_total" => Ok(PtestMetric::CertChecksTotal),
        "certs_cached" => Ok(PtestMetric::CertsCached),
        "modules_cached" => Ok(PtestMetric::ModulesCached),
        "num_verified" => Ok(PtestMetric::NumVerified),
        other => Err(format!("unknown metric '{other}'")),
    }
}

fn parse_nonnegative_i32(value: &str, line: usize) -> Result<i32, String> {
    let value = value
        .parse::<i32>()
        .map_err(|_| format!("line {line}: expected nonnegative integer"))?;
    if value < 0 {
        return Err(format!("line {line}: expected nonnegative integer"));
    }
    Ok(value)
}

fn parse_ptest_config(text: &str) -> Result<PtestConfig, String> {
    let mut config = PtestConfig::default();

    for (index, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("line {}: expected key = value", index + 1));
        };
        let key = key.trim();
        let value = value.trim();
        if let Some(metric) = key.strip_prefix("metrics.") {
            config.metrics.push(PtestMetricExpectation {
                metric: parse_metric(metric)?,
                value: parse_nonnegative_i32(value, index + 1)?,
            });
            continue;
        }

        match key {
            "command" => config.command = parse_command(&parse_string(value)?)?,
            "target" => config.target = Some(parse_string(value)?),
            "expect" => config.expectation = parse_expectation(&parse_string(value)?)?,
            "message" => config.message = Some(parse_string(value)?),
            "check_hashes" => config.check_hashes = parse_bool(value)?,
            "jobs" => {
                let jobs = value
                    .parse::<usize>()
                    .map_err(|_| format!("line {}: expected positive integer", index + 1))?;
                if jobs == 0 {
                    return Err(format!("line {}: expected positive integer", index + 1));
                }
                config.jobs = Some(jobs);
            }
            other => return Err(format!("line {}: unknown key '{other}'", index + 1)),
        }
    }

    Ok(config)
}

fn load_ptest_case(root: &Path, fixture_dir: PathBuf) -> PtestCase {
    let relative = fixture_dir
        .strip_prefix(root)
        .expect("ptest fixture should live under root");
    let config_text = fs::read_to_string(fixture_dir.join(CONFIG_FILE)).unwrap_or_else(|err| {
        panic!(
            "failed reading {}/{}: {err}",
            relative.display(),
            CONFIG_FILE
        )
    });
    let config = parse_ptest_config(&config_text).unwrap_or_else(|err| {
        panic!(
            "failed parsing {}/{}: {err}",
            relative.display(),
            CONFIG_FILE
        )
    });

    PtestCase {
        id: relative.display().to_string(),
        fixture_dir,
        config,
    }
}

fn copy_project_fixture(fixture_dir: &Path, root: &Path) -> Result<(), String> {
    for entry in WalkDir::new(fixture_dir) {
        let entry = entry.map_err(|err| err.to_string())?;
        let path = entry.path();
        if path == fixture_dir {
            continue;
        }

        let relative = path
            .strip_prefix(fixture_dir)
            .expect("fixture entry should be under fixture root");
        if relative == Path::new(CONFIG_FILE) {
            continue;
        }

        let dest = root.join(relative);
        if entry.file_type().is_dir() {
            fs::create_dir_all(&dest).map_err(|err| err.to_string())?;
        } else {
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent).map_err(|err| err.to_string())?;
            }
            fs::copy(path, &dest).map_err(|err| err.to_string())?;
        }
    }

    fs::create_dir_all(root.join("build")).map_err(|err| err.to_string())?;
    Ok(())
}

fn log_text(output: &VerifierOutput) -> String {
    output
        .events
        .iter()
        .filter_map(|event| event.log_message.as_ref())
        .cloned()
        .collect::<Vec<_>>()
        .join("\n")
}

fn status_label(status: BuildStatus) -> &'static str {
    match status {
        BuildStatus::Good => "ok",
        BuildStatus::Warning => "warning",
        BuildStatus::Error => "error",
    }
}

fn expected_status(expectation: PtestExpectation) -> Option<BuildStatus> {
    match expectation {
        PtestExpectation::Ok => Some(BuildStatus::Good),
        PtestExpectation::Warning => Some(BuildStatus::Warning),
        PtestExpectation::Error => Some(BuildStatus::Error),
        PtestExpectation::SetupError => None,
    }
}

fn assert_message_contains(config: &PtestConfig, text: &str) {
    let Some(expected) = &config.message else {
        return;
    };
    assert!(
        text.contains(expected),
        "expected message containing '{expected}', got:\n{text}"
    );
}

fn metric_label(metric: PtestMetric) -> &'static str {
    match metric {
        PtestMetric::GoalsTotal => "goals_total",
        PtestMetric::GoalsDone => "goals_done",
        PtestMetric::GoalsSuccess => "goals_success",
        PtestMetric::PendingModulesTotal => "pending_modules_total",
        PtestMetric::PendingGoalsTotal => "pending_goals_total",
        PtestMetric::SearchesTotal => "searches_total",
        PtestMetric::CertChecksTotal => "cert_checks_total",
        PtestMetric::CertsCached => "certs_cached",
        PtestMetric::ModulesCached => "modules_cached",
        PtestMetric::NumVerified => "num_verified",
    }
}

fn metric_value(output: &VerifierOutput, metric: PtestMetric) -> i32 {
    match metric {
        PtestMetric::GoalsTotal => output.metrics.goals_total,
        PtestMetric::GoalsDone => output.metrics.goals_done,
        PtestMetric::GoalsSuccess => output.metrics.goals_success,
        PtestMetric::PendingModulesTotal => output.metrics.pending_modules_total,
        PtestMetric::PendingGoalsTotal => output.metrics.pending_goals_total,
        PtestMetric::SearchesTotal => output.metrics.searches_total,
        PtestMetric::CertChecksTotal => output.metrics.cert_checks_total,
        PtestMetric::CertsCached => output.metrics.certs_cached,
        PtestMetric::ModulesCached => output.metrics.modules_cached,
        PtestMetric::NumVerified => output.num_verified() as i32,
    }
}

fn assert_metrics(config: &PtestConfig, output: &VerifierOutput) {
    for expectation in &config.metrics {
        let actual = metric_value(output, expectation.metric);
        assert_eq!(
            actual,
            expectation.value,
            "expected metric {} = {}, got {}",
            metric_label(expectation.metric),
            expectation.value,
            actual
        );
    }
}

fn run_ptest_case(case: &PtestCase) {
    let temp = tempfile::TempDir::new().expect("temp ptest project should be created");
    let root = temp.path();
    copy_project_fixture(&case.fixture_dir, root).expect("ptest fixture should copy");

    let project_config = match case.config.command {
        PtestCommand::Verify => ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: false,
            write_cache: true,
            update_version: false,
        },
        PtestCommand::Check => ProjectConfig {
            usage_mode: UsageMode::Check,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
            update_version: false,
        },
    };

    let verifier = match case.config.command {
        PtestCommand::Verify => Verifier::new(
            root.to_path_buf(),
            project_config,
            case.config.target.clone(),
        ),
        PtestCommand::Check => Verifier::new_for_check(
            root.to_path_buf(),
            project_config,
            case.config.target.clone(),
        ),
    };

    let mut verifier = match verifier {
        Ok(verifier) => verifier,
        Err(error) => {
            let text = error.cli_message();
            assert_eq!(
                case.config.expectation,
                PtestExpectation::SetupError,
                "unexpected setup error:\n{text}"
            );
            assert_message_contains(&case.config, &text);
            return;
        }
    };

    assert_ne!(
        case.config.expectation,
        PtestExpectation::SetupError,
        "expected setup error, but verifier initialized"
    );

    verifier.builder.check_hashes = case.config.check_hashes;
    if case.config.command == PtestCommand::Check {
        verifier.builder.check_mode = true;
    }
    if let Some(jobs) = case.config.jobs {
        verifier.builder.check_jobs = jobs;
    }

    match verifier.run() {
        Ok(output) => {
            let Some(expected) = expected_status(case.config.expectation) else {
                unreachable!("setup error expectation was handled above");
            };
            let logs = log_text(&output);
            assert_eq!(
                output.status,
                expected,
                "expected status {}, got {}\n{}",
                status_label(expected),
                status_label(output.status),
                logs
            );
            assert_message_contains(&case.config, &logs);
            assert_metrics(&case.config, &output);
        }
        Err(error) => {
            assert_eq!(
                case.config.expectation,
                PtestExpectation::Error,
                "unexpected verifier run error:\n{error}"
            );
            assert_message_contains(&case.config, &error);
        }
    }
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
fn ptests() {
    let root = ptest_root();
    let dirs = discover_ptest_dirs(&root);
    assert!(
        !dirs.is_empty(),
        "no ptest fixtures found under {}",
        root.display()
    );

    let filter = env::var(FILTER_ENV).ok();
    let mut matched_cases = 0usize;
    let mut failures = Vec::new();

    for dir in dirs {
        let case = load_ptest_case(&root, dir);
        if filter
            .as_ref()
            .is_some_and(|filter| !case.id.contains(filter))
        {
            continue;
        }

        matched_cases += 1;
        let result = catch_unwind(AssertUnwindSafe(|| run_ptest_case(&case)));
        if let Err(payload) = result {
            failures.push(format!("{}\n{}", case.id, panic_message(payload).trim()));
        }
    }

    if let Some(filter) = filter {
        assert!(
            matched_cases > 0,
            "no ptests matched {}={}",
            FILTER_ENV,
            filter
        );
    } else {
        assert!(matched_cases > 0, "no ptests were discovered");
    }

    assert!(
        failures.is_empty(),
        "ptest failures:\n\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn parses_minimal_config() {
    assert_eq!(parse_ptest_config("").unwrap(), PtestConfig::default());
}

#[test]
fn parses_full_config() {
    assert_eq!(
        parse_ptest_config(
            r#"
            command = "check"
            target = "pkg"
            expect = "error"
            message = "missing export"
            check_hashes = true
            jobs = 2
            metrics.searches_total = 0
            "#,
        )
        .unwrap(),
        PtestConfig {
            command: PtestCommand::Check,
            target: Some("pkg".to_string()),
            expectation: PtestExpectation::Error,
            message: Some("missing export".to_string()),
            check_hashes: true,
            jobs: Some(2),
            metrics: vec![PtestMetricExpectation {
                metric: PtestMetric::SearchesTotal,
                value: 0,
            }],
        }
    );
}
