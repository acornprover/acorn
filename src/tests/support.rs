use crate::certificate::Certificate;
use crate::module::LoadState;
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::{Outcome, ProverMode};
use std::sync::Once;
use tracing_subscriber::{fmt, prelude::*, EnvFilter};

static TEST_TRACING_INIT: Once = Once::new();
const DEEP_VERIFY_TIMEOUT_SECS: f32 = 5.0;
const DEEP_VERIFY_ACTIVATION_LIMIT: i32 = 2000;

#[derive(Clone, Copy)]
struct VerifyOptions {
    verbose: bool,
    deep_followup_on_failure: bool,
}

struct VerifyFailure {
    goal_name: String,
    shallow_outcome: Outcome,
    deep_outcome: Option<Outcome>,
}

enum VerifyResult {
    Success,
    Failure(VerifyFailure),
}

fn init_test_tracing() {
    TEST_TRACING_INIT.call_once(|| {
        let _ = tracing_subscriber::registry()
            .with(fmt::layer().with_ansi(false).without_time())
            .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("warn")))
            .try_init();
    });
}

/// Expects the proof to succeed, and a valid concrete proof to be generated.
pub fn prove(project: &mut Project, module_name: &str, goal_name: &str) -> Certificate {
    init_test_tracing();
    let module_id = project
        .load_module_by_name(module_name)
        .expect("load failed");
    let load_state = project.get_module_by_id(module_id);
    let base_env = match load_state {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("no module"),
    };
    let node = base_env.get_node_by_goal_name(goal_name);
    let normalized_goal = node.lowered_goal().expect("missing lowered goal");
    let mut processor = Processor::with_imports(None, node.bindings(), project).unwrap();
    processor.add_module_facts(&node).unwrap();
    processor.set_lowered_goal(normalized_goal);
    let goal_kernel_context = &normalized_goal.kernel_context;
    let outcome = processor.search(ProverMode::Test, goal_kernel_context);

    assert_eq!(outcome, Outcome::Success);

    let cert = match processor
        .prover()
        .make_cert(node.bindings(), goal_kernel_context, true)
    {
        Ok(cert) => cert,
        Err(e) => panic!("make_cert failed: {}", e),
    };

    if let Err(e) = processor.check_cert(&cert, None, goal_kernel_context, project, node.bindings())
    {
        panic!("check_cert failed: {}", e);
    }
    cert
}

// Does one proof on the provided text for a specific goal.
pub fn prove_text(text: &str, goal_name: &str) -> Outcome {
    init_test_tracing();
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    // Find the specific goal by name
    for cursor in env.iter_goals() {
        let goal = cursor.goal().unwrap();
        if goal.name == goal_name {
            let mut processor = match Processor::with_imports(None, cursor.bindings(), &project) {
                Ok(p) => p,
                Err(_) => return Outcome::Inconsistent,
            };
            if processor.add_module_facts(&cursor).is_err() {
                return Outcome::Inconsistent;
            }
            let normalized_goal = match cursor.lowered_goal() {
                Some(n) => n,
                None => return Outcome::Inconsistent,
            };
            processor.set_lowered_goal(normalized_goal);
            let goal_kernel_context = &normalized_goal.kernel_context;
            return processor.search(ProverMode::Test, goal_kernel_context);
        }
    }
    panic!("goal '{}' not found in text", goal_name);
}

fn verify_with_options(text: &str, options: VerifyOptions) -> Result<VerifyResult, String> {
    init_test_tracing();
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    // Track the highest top-level node index that contains a goal
    let mut last_goal_top_index: Option<usize> = None;

    for cursor in env.iter_goals() {
        let goal = cursor.goal().unwrap();

        // Track the top-level index of this goal
        let path = cursor.path();
        if !path.is_empty() {
            let top_index = path[0];
            last_goal_top_index = Some(last_goal_top_index.map_or(top_index, |i| i.max(top_index)));
        }

        let mut processor = Processor::with_imports(None, cursor.bindings(), &project)?;
        processor.add_module_facts(&cursor)?;
        let normalized_goal = cursor
            .lowered_goal()
            .ok_or_else(|| "missing lowered goal".to_string())?;
        processor.set_lowered_goal(normalized_goal);
        let goal_kernel_context = &normalized_goal.kernel_context;

        if options.verbose {
            println!("verbose trace for goal `{}`:", goal.name);
        }

        // This is a key difference between our verification tests, and our real verification.
        // This helps us test that verification fails in cases where we do have an
        // infinite rabbit hole we could go down.
        let shallow_outcome = processor.search(ProverMode::Test, goal_kernel_context);
        if options.verbose {
            processor.prover().print_active_steps(
                shallow_outcome,
                cursor.bindings(),
                goal_kernel_context,
            );
        }

        if shallow_outcome != Outcome::Success {
            let deep_outcome = if options.deep_followup_on_failure
                && matches!(
                    shallow_outcome,
                    Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
                ) {
                let deep_outcome = processor.search(
                    ProverMode::Interactive {
                        timeout_secs: DEEP_VERIFY_TIMEOUT_SECS,
                        activation_limit: DEEP_VERIFY_ACTIVATION_LIMIT,
                    },
                    goal_kernel_context,
                );
                if options.verbose {
                    println!(
                        "deep follow-up trace for goal `{}` after shallow {}:",
                        goal.name, shallow_outcome
                    );
                    processor.prover().print_active_steps(
                        deep_outcome,
                        cursor.bindings(),
                        goal_kernel_context,
                    );
                }
                if deep_outcome == Outcome::Success {
                    println!(
                        "shallow verification failed for goal `{}` with {}, but deep search succeeded.\nprinting deep proof:",
                        goal.name, shallow_outcome
                    );
                    let cert = processor
                        .prover()
                        .make_cert(cursor.bindings(), goal_kernel_context, true)
                        .map_err(|e| e.to_string())?;
                    if let Err(e) = processor.check_cert(
                        &cert,
                        None,
                        goal_kernel_context,
                        &project,
                        cursor.bindings(),
                    ) {
                        panic!("check_cert failed: {}", e);
                    }
                }
                Some(deep_outcome)
            } else {
                None
            };

            return Ok(VerifyResult::Failure(VerifyFailure {
                goal_name: goal.name.to_string(),
                shallow_outcome,
                deep_outcome,
            }));
        }
        let cert = processor
            .prover()
            .make_cert(cursor.bindings(), goal_kernel_context, true)
            .map_err(|e| e.to_string())?;
        if let Err(e) = processor.check_cert(
            &cert,
            None,
            goal_kernel_context,
            &project,
            cursor.bindings(),
        ) {
            panic!("check_cert failed: {}", e);
        }
    }

    // Lower any facts after the last goal (or all facts if there are no goals).
    // This catches lowering errors in trailing definitions.
    // Note: the lowering pass already does this during module loading, but we keep
    // this check for test coverage.
    let first_unnormalized = last_goal_top_index.map_or(0, |i| i + 1);
    if first_unnormalized < env.nodes.len() {
        // Ensure all facts were lowered during the lowering pass.
        for node in &env.nodes {
            if node.get_fact().is_some() && node.lowered_fact().is_none() {
                return Err("missing lowered fact".to_string());
            }
        }
    }

    Ok(VerifyResult::Success)
}

// Verifies all the goals in the provided text, returning any non-Success outcome.
pub fn verify(text: &str) -> Result<Outcome, String> {
    match verify_with_options(
        text,
        VerifyOptions {
            verbose: false,
            deep_followup_on_failure: false,
        },
    )? {
        VerifyResult::Success => Ok(Outcome::Success),
        VerifyResult::Failure(failure) => Ok(failure.shallow_outcome),
    }
}

fn expect_verify_success(result: Result<VerifyResult, String>) {
    match result.expect("verification errored") {
        VerifyResult::Success => {}
        VerifyResult::Failure(failure) => {
            if let Some(deep_outcome) = failure.deep_outcome {
                panic!(
                    "We expected verification to return Success, but shallow search for goal '{}' returned {} and deep search returned {}.",
                    failure.goal_name, failure.shallow_outcome, deep_outcome
                );
            }
            panic!(
                "We expected verification to return Success, but we got {}.",
                failure.shallow_outcome
            );
        }
    }
}

pub fn verify_succeeds(text: &str) {
    expect_verify_success(verify_with_options(
        text,
        VerifyOptions {
            verbose: false,
            deep_followup_on_failure: true,
        },
    ));
}

pub fn verify_succeeds_verbose(text: &str) {
    expect_verify_success(verify_with_options(
        text,
        VerifyOptions {
            verbose: true,
            deep_followup_on_failure: true,
        },
    ));
}

pub fn verify_fails(text: &str) {
    let outcome = verify(text).expect("verification errored");

    if outcome != Outcome::Exhausted {
        panic!(
            "We expected verification to return Exhausted, but we got {}.",
            outcome
        );
    }
}

pub fn assert_proof_lines(actual: Vec<String>, expected: &[&str]) {
    let expected = expected
        .iter()
        .map(|line| line.to_string())
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

/// Verifies a single goal by name in the provided text.
/// Returns the outcome of the search, and panics if cert generation/checking fails.
pub const THING: &str = r#"
    type Thing: axiom
    let t: Thing = axiom
    let t2: Thing = axiom
    let f: Thing -> Bool = axiom
    let g: (Thing, Thing) -> Thing = axiom
    let h: Thing -> Thing = axiom
    "#;

// Does one proof in the "thing" environment.
pub fn prove_thing(text: &str, goal_name: &str) -> Outcome {
    let text = format!("{}\n{}", THING, text);
    prove_text(&text, goal_name)
}
