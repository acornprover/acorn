use crate::certificate::Certificate;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::lowered_module::LoweredGoalId;
use crate::elaborator::lowering::LoweredGoal;
use crate::module::{LoadState, ModuleId};
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

pub fn processor_for_lowered_goal<'a>(
    project: &'a Project,
    module_id: ModuleId,
    goal_id: LoweredGoalId,
) -> Result<(Processor, &'a BindingMap, &'a LoweredGoal), String> {
    let lowered = project
        .get_lowered_module(module_id)
        .ok_or_else(|| format!("missing lowered module {}", module_id))?;
    let entry = lowered.goal(goal_id);
    let mut processor =
        Processor::with_imports(None, &entry.bindings, project).map_err(|err| err.message)?;
    processor
        .add_visible_module_facts(lowered, goal_id)
        .map_err(|err| err.message)?;
    processor.set_lowered_goal(&entry.lowered_goal);
    Ok((processor, &entry.bindings, &entry.lowered_goal))
}

pub fn processor_for_goal_name<'a>(
    project: &'a Project,
    module_id: ModuleId,
    goal_name: &str,
) -> Result<(Processor, &'a BindingMap, &'a LoweredGoal), String> {
    let lowered = project
        .get_lowered_module(module_id)
        .ok_or_else(|| format!("missing lowered module {}", module_id))?;
    let (goal_id, _) = lowered
        .goal_by_name(goal_name)
        .ok_or_else(|| format!("goal '{}' not found", goal_name))?;
    processor_for_lowered_goal(project, module_id, goal_id)
}

/// Expects the proof to succeed, and a valid concrete proof to be generated.
pub fn prove(project: &mut Project, module_name: &str, goal_name: &str) -> Certificate {
    init_test_tracing();
    let module_id = project
        .load_module_by_name(module_name)
        .expect("load failed");
    match project.get_module_by_id(module_id) {
        LoadState::Ok(_) => {}
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("no module"),
    }
    let (mut processor, bindings, normalized_goal) =
        processor_for_goal_name(project, module_id, goal_name).expect("processor setup failed");
    let goal_kernel_context = &normalized_goal.kernel_context;
    let outcome = processor.search(ProverMode::Test, goal_kernel_context);

    assert_eq!(outcome, Outcome::Success);

    let cert = match processor
        .prover()
        .make_cert(bindings, goal_kernel_context, true)
    {
        Ok(cert) => cert,
        Err(e) => panic!("make_cert failed: {}", e),
    };

    if let Err(e) = processor.check_cert(&cert, None, goal_kernel_context, &*project, bindings) {
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
    match project.get_module_by_id(module_id) {
        LoadState::Ok(_) => {}
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    }

    let lowered = project
        .get_lowered_module(module_id)
        .expect("missing lowered module");
    if let Some((goal_id, _)) = lowered.goal_by_name(goal_name) {
        let (mut processor, _bindings, normalized_goal) =
            match processor_for_lowered_goal(&project, module_id, goal_id) {
                Ok(result) => result,
                Err(_) => return Outcome::Inconsistent,
            };
        let goal_kernel_context = &normalized_goal.kernel_context;
        return processor.search(ProverMode::Test, goal_kernel_context);
    }
    panic!("goal '{}' not found in text", goal_name);
}

fn verify_with_options(text: &str, options: VerifyOptions) -> Result<VerifyResult, String> {
    init_test_tracing();
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    match project.get_module_by_id(module_id) {
        LoadState::Ok(_) => {}
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    }

    let lowered = project
        .get_lowered_module(module_id)
        .expect("missing lowered module");
    for (goal_id, entry) in lowered.goals() {
        let goal = &entry.lowered_goal.goal;

        let (mut processor, bindings, normalized_goal) =
            processor_for_lowered_goal(&project, module_id, goal_id)?;
        let goal_kernel_context = &normalized_goal.kernel_context;

        if options.verbose {
            println!("verbose trace for goal `{}`:", goal.name);
        }

        // This is a key difference between our verification tests, and our real verification.
        // This helps us test that verification fails in cases where we do have an
        // infinite rabbit hole we could go down.
        let shallow_outcome = processor.search(ProverMode::Test, goal_kernel_context);
        if options.verbose {
            processor
                .prover()
                .print_active_steps(shallow_outcome, bindings, goal_kernel_context);
        }

        if shallow_outcome != Outcome::Success {
            let deep_outcome = if options.deep_followup_on_failure
                && matches!(
                    shallow_outcome,
                    Outcome::ShallowExhausted
                        | Outcome::ShallowExplosion
                        | Outcome::Exhausted
                        | Outcome::Timeout
                        | Outcome::ActivationCap
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
                        bindings,
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
                        .make_cert(bindings, goal_kernel_context, true)
                        .map_err(|e| e.to_string())?;
                    if let Err(e) =
                        processor.check_cert(&cert, None, goal_kernel_context, &project, bindings)
                    {
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
            .make_cert(bindings, goal_kernel_context, true)
            .map_err(|e| e.to_string())?;
        if let Err(e) = processor.check_cert(&cert, None, goal_kernel_context, &project, bindings) {
            panic!("check_cert failed: {}", e);
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

#[allow(dead_code)]
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

    if !matches!(
        outcome,
        Outcome::ShallowExhausted | Outcome::ShallowExplosion | Outcome::Timeout
    ) {
        panic!(
            "We expected verification to fail shallowly, but we got {}.",
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
