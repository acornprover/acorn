use crate::tests::support::*;
use crate::{
    module::LoadState,
    processor::Processor,
    project::Project,
    prover::{Outcome, ProverMode},
};

// Proof generation and condensed-certificate regressions.

#[test]
fn test_proof_generation_with_forall_goal() {
    let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg { forall(x: Nat) { f(x) implies g(x) } }
            axiom gimph { forall(x: Nat) { g(x) implies h(x) } }
            theorem goal { forall(x: Nat) { f(x) implies h(x) } }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_generation_with_intermediate_existential() {
    let text = r#"
        type Nat: axiom
        let b: Bool = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom forg(x: Nat) { f(x) or g(x) }
        axiom fgimpb { forall(x: Nat) { f(x) or g(x) } implies b }
        theorem goal { b }
        "#;
    verify_succeeds(text);
}

#[cfg(feature = "nwit")]
#[test]
fn test_nwit_cert_generation_replays_source_let_satisfy_inside_forall() {
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
        proof
            .iter()
            .any(|line| line.contains("let w0: Nat satisfy")),
        "expected witness emission in generated cert: {proof:?}"
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
fn test_assuming_lhs_of_implication() {
    verify_succeeds(
        r#"
            let a: Bool = axiom
            let b: Bool = axiom
            let c: Bool = axiom
            axiom aimpb { a implies b }
            axiom bimpc { b implies c }
            theorem goal { a implies c } by {
                b
            }
        "#,
    );
}

#[test]
fn test_templated_proof() {
    let text = r#"
            type Thing: axiom
            let t1: Thing = axiom
            let t2: Thing = axiom
            let t3: Thing = axiom

            define foo[T](x: T) -> Bool { axiom }

            axiom a12 { foo(t1) implies foo(t2) }
            axiom a23 { foo(t2) implies foo(t3) }
            theorem goal { foo(t1) implies foo(t3) }
            "#;

    verify_succeeds(text);
}

#[test]
fn test_proof_condensing_induction() {
    let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        let suc: Nat -> Nat = axiom
        axiom induction(f: Nat -> Bool) {
            f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) }
        }
        let foo: Nat -> Bool = axiom
        theorem goal { foo(zero) and forall(k: Nat) { foo(k) implies foo(suc(k)) } implies forall(n: Nat) { foo(n) } }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_condensing_false() {
    let text = r#"
        let a: Bool = axiom
        axiom a_true { a }
        if not a {
            false
        }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_condensing_combining_two_theorems() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom fimpg(x: Nat) { f(x) implies g(x) }
        axiom fa { f(a) }
        theorem goal { g(a) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_indirect_from_goal() {
    let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg(x: Nat) { f(x) implies g(x) }
            axiom gimph(x: Nat) { g(x) implies h(x) }
            axiom fimpnh(x: Nat) { f(x) implies not h(x) }
            theorem goal(x: Nat) { not f(x) }
        "#;

    verify_succeeds(text);
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
