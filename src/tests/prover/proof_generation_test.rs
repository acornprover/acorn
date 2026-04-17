use crate::tests::support::*;
use crate::{
    module::LoadState,
    processor::Processor,
    project::Project,
    prover::{Outcome, ProverMode},
};

#[test]
fn test_cert_generation_replays_source_let_satisfy_inside_forall() {
    let text = r#"
        type Nat: axiom
        let p: (Nat, Nat) -> Bool = axiom

        theorem goal {
            forall(big_n: Nat) {
                exists(m: Nat) {
                    p(big_n, m)
                }
            }
            implies
            forall(big_n: Nat) {
                exists(m: Nat) {
                    p(big_n, m)
                }
            }
        } by {
            forall(big_n: Nat) {
                let m: Nat satisfy {
                    p(big_n, m)
                }

                p(big_n, m)
            }
        }
    "#;

    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    let cursor = env.get_node_by_goal_name("goal");
    let mut processor = Processor::with_imports(None, cursor.bindings(), &project).unwrap();
    processor.add_module_facts(&cursor).unwrap();
    let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
    processor.set_lowered_goal(normalized_goal);
    let goal_kernel_context = &normalized_goal.kernel_context;
    let outcome = processor.search(ProverMode::Test, goal_kernel_context);
    assert_eq!(outcome, Outcome::Success);

    let cert = processor
        .prover()
        .make_cert(cursor.bindings(), goal_kernel_context, true)
        .expect("make_cert should succeed");
    let proof = cert.proof.as_ref().expect("proof should exist");
    assert!(
        !proof.is_empty(),
        "expected a non-empty generated cert proof: {proof:?}"
    );
    processor
        .check_cert(
            &cert,
            None,
            goal_kernel_context,
            &project,
            cursor.bindings(),
        )
        .expect("generated cert should replay");
}

#[test]
fn test_specializing_to_bound_variable() {
    let text = r#"
    type Elem: axiom

    define app_equal(f: Elem -> Elem, a: Elem, b: Elem) -> Bool {
        f(a) = f(b)
    }

    define is_constant(f: Elem -> Elem) -> Bool {
        forall(a: Elem, b: Elem) {
            app_equal(f, a, b)
        }
    }

    theorem const_fn_is_const(c: Elem) {
        is_constant(function(x: Elem) { c })
    }

    theorem should_fail {
        is_constant(function(x: Elem) { x })
    }
    "#;

    verify_fails(text);
}

#[test]
fn test_specializing_to_term_containing_bound_variable() {
    let text = r#"
    type Elem: axiom

    define app_equal(f: Elem -> Elem, a: Elem, b: Elem) -> Bool {
        f(a) = f(b)
    }

    define is_constant(f: Elem -> Elem) -> Bool {
        forall(a: Elem, b: Elem) {
            app_equal(f, a, b)
        }
    }

    theorem const_fn_is_const(c: Elem) {
        is_constant(function(x: Elem) { c })
    }

    let g: Elem -> Elem = axiom

    theorem should_fail {
        is_constant(function(x: Elem) { g(x) })
    }
    "#;

    verify_fails(text);
}

#[test]
fn test_cert_generation_replays_flipped_simplification_match() {
    let text = r#"
        inductive Nat {
            zero
            suc(Nat)
        }

        inductive Int {
            from_nat(Nat)
            neg_suc(Nat)
        }

        define neg_nat(n: Nat) -> Int {
            match n {
                Nat.zero {
                    Int.from_nat(Nat.zero)
                }
                Nat.suc(k) {
                    Int.neg_suc(k)
                }
            }
        }

        define neg(a: Int) -> Int {
            match a {
                Int.from_nat(n) {
                    neg_nat(n)
                }
                Int.neg_suc(n) {
                    Int.from_nat(Nat.suc(n))
                }
            }
        }

        theorem fix_neg(a: Int) {
            neg(a) = a implies a = Int.from_nat(Nat.zero)
        } by {
            if neg(a) = a {
                match a {
                    Int.from_nat(n) {
                        n = Nat.zero
                        a = Int.from_nat(Nat.zero)
                    }
                    Int.neg_suc(n) {
                    }
                }
            }
        }
    "#;

    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    let cursor = env.get_node_by_goal_name("n = Nat.zero");
    let mut processor = Processor::with_imports(None, cursor.bindings(), &project).unwrap();
    processor.add_module_facts(&cursor).unwrap();
    let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
    processor.set_lowered_goal(normalized_goal);
    let goal_kernel_context = &normalized_goal.kernel_context;
    let outcome = processor.search(
        ProverMode::Interactive {
            timeout_secs: 5.0,
            activation_limit: 2000,
        },
        goal_kernel_context,
    );
    assert_eq!(outcome, Outcome::Success);

    let cert = processor
        .prover()
        .make_cert(cursor.bindings(), goal_kernel_context, false)
        .expect("make_cert should succeed");
    processor
        .check_cert(
            &cert,
            None,
            goal_kernel_context,
            &project,
            cursor.bindings(),
        )
        .expect("generated cert should replay successfully");
}
