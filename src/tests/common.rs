use crate::certificate::Certificate;
use crate::module::LoadState;
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::{Outcome, ProverMode};

/// Expects the proof to succeed, and a valid concrete proof to be generated.
pub fn prove(project: &mut Project, module_name: &str, goal_name: &str) -> Certificate {
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
    let env = node.goal_env().unwrap();
    let normalized_goal = node.normalized_goal().expect("missing prenormalized goal");
    let mut processor = Processor::with_imports(None, base_env).unwrap();
    processor.add_module_facts(&node).unwrap();
    processor.set_normalized_goal(normalized_goal);
    let outcome = processor.search(ProverMode::Test);

    assert_eq!(outcome, Outcome::Success);

    let cert = match processor
        .prover()
        .make_cert(&env.bindings, processor.normalizer(), true)
    {
        Ok(cert) => cert,
        Err(e) => panic!("make_cert failed: {}", e),
    };

    if let Err(e) = processor.check_cert(&cert, None, project, &env.bindings) {
        panic!("check_cert failed: {}", e);
    }
    cert
}

// Does one proof on the provided text for a specific goal.
pub fn prove_text(text: &str, goal_name: &str) -> Outcome {
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
            let mut processor = match Processor::with_imports(None, env) {
                Ok(p) => p,
                Err(_) => return Outcome::Inconsistent,
            };
            if processor.add_module_facts(&cursor).is_err() {
                return Outcome::Inconsistent;
            }
            let normalized_goal = match cursor.normalized_goal() {
                Some(n) => n,
                None => return Outcome::Inconsistent,
            };
            processor.set_normalized_goal(normalized_goal);

            return processor.search(ProverMode::Test);
        }
    }
    panic!("goal '{}' not found in text", goal_name);
}

// Verifies all the goals in the provided text, returning any non-Success outcome.
pub fn verify(text: &str) -> Result<Outcome, String> {
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
        let _goal = cursor.goal().unwrap();
        let goal_env = cursor.goal_env().unwrap();

        // Track the top-level index of this goal
        let path = cursor.path();
        if !path.is_empty() {
            let top_index = path[0];
            last_goal_top_index = Some(last_goal_top_index.map_or(top_index, |i| i.max(top_index)));
        }

        let mut processor = Processor::with_imports(None, env)?;
        processor.add_module_facts(&cursor)?;
        let normalized_goal = cursor
            .normalized_goal()
            .ok_or_else(|| "missing prenormalized goal".to_string())?;
        processor.set_normalized_goal(normalized_goal);

        // This is a key difference between our verification tests, and our real verification.
        // This helps us test that verification fails in cases where we do have an
        // infinite rabbit hole we could go down.
        let outcome = processor.search(ProverMode::Test);
        if outcome != Outcome::Success {
            return Ok(outcome);
        }
        let cert = processor
            .prover()
            .make_cert(&goal_env.bindings, processor.normalizer(), true)
            .map_err(|e| e.to_string())?;
        if let Err(e) = processor.check_cert(&cert, None, &project, &goal_env.bindings) {
            panic!("check_cert failed: {}", e);
        }
    }

    // Normalize any facts after the last goal (or all facts if there are no goals).
    // This catches normalization errors in trailing definitions.
    // Note: prenormalize() already does this during module loading, but we keep
    // this check for test coverage.
    let first_unnormalized = last_goal_top_index.map_or(0, |i| i + 1);
    if first_unnormalized < env.nodes.len() {
        let mut processor = Processor::with_imports(None, env)?;

        // Add all facts from this module to normalize trailing ones
        for node in &env.nodes {
            if let Some(fact) = node.get_fact() {
                processor.add_fact(&fact)?;
            }
        }
    }

    Ok(Outcome::Success)
}

pub fn verify_succeeds(text: &str) {
    let outcome = verify(text).expect("verification errored");
    if outcome != Outcome::Success {
        panic!(
            "We expected verification to return Success, but we got {}.",
            outcome
        );
    }
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

/// Verifies a single goal by name in the provided text.
/// Returns the outcome of the search, and panics if cert generation/checking fails.
pub fn verify_line(text: &str, goal_name: &str) -> Result<Outcome, String> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    for cursor in env.iter_goals() {
        let goal = cursor.goal().unwrap();
        if goal.name == goal_name {
            let goal_env = cursor.goal_env().unwrap();

            let mut processor = Processor::with_imports(None, env)?;
            processor.add_module_facts(&cursor)?;
            let normalized_goal = cursor
                .normalized_goal()
                .ok_or_else(|| "missing prenormalized goal".to_string())?;
            processor.set_normalized_goal(normalized_goal);

            let outcome = processor.search(ProverMode::Test);
            if outcome != Outcome::Success {
                return Ok(outcome);
            }
            let cert = processor
                .prover()
                .make_cert(&goal_env.bindings, processor.normalizer(), true)
                .map_err(|e| e.to_string())?;
            if let Err(e) = processor.check_cert(&cert, None, &project, &goal_env.bindings) {
                panic!("check_cert failed: {}", e);
            }
            return Ok(Outcome::Success);
        }
    }
    panic!("goal '{}' not found in text", goal_name);
}

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
