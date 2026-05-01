use crate::tests::support::*;
use crate::{
    builder::BuildStatus,
    module::LoadState,
    processor::Processor,
    project::Project,
    project::ProjectConfig,
    prover::{Outcome, ProverMode},
    verifier::Verifier,
};
use assert_fs::prelude::*;
use assert_fs::TempDir;

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

#[test]
fn test_cert_generation_replays_inner_outer_type_parameters() {
    // Regression test for https://github.com/acornprover/acorn/issues/47.
    let text = r#"
        inductive Option[T] {
            none
            some(T)
        }

        define inner_constraint[O, M](
            a: M -> O,
            b: M -> O,
            c: O -> M,
            d: (M, M) -> M
        ) -> Bool {
            forall(x: O) { a(c(x)) = x and b(c(x)) = x }
            and forall(f: M, g: M) { a(f) = b(g) implies a(d(f, g)) = a(g) }
            and forall(f: M, g: M) { a(f) = b(g) implies b(d(f, g)) = b(f) }
            and forall(f: M, g: M, h: M) {
                a(f) = b(g) and a(g) = b(h) implies d(d(f, g), h) = d(f, d(g, h))
            }
            and forall(f: M) { d(c(b(f)), f) = f }
            and forall(f: M) { d(f, c(a(f))) = f }
        }

        structure Inner[O, M] {
            a: M -> O
            b: M -> O
            c: O -> M
            d: (M, M) -> M
        } constraint {
            inner_constraint(a, b, c, d)
        }

        define outer_constraint[O, M](inner: Inner[O, M], hom: M, inv: M) -> Bool {
            inner.a(hom) = inner.b(inv) and inner.a(inv) = inner.b(hom)
            and inner.d(inv, hom) = inner.c(inner.a(hom))
            and inner.d(hom, inv) = inner.c(inner.b(hom))
        }

        structure Outer[O, M] {
            first: Inner[O, M]
            hom: M
            inv: M
        } constraint {
            outer_constraint(first, hom, inv)
        }

        theorem outer_new_first[O, M](i: Inner[O, M], h: M, n: M, o: Outer[O, M]) {
            Outer[O, M].new(i, h, n) = Option.some(o) implies o.first = i
        }

        theorem outer_new_hom[O, M](i: Inner[O, M], h: M, n: M, o: Outer[O, M]) {
            Outer[O, M].new(i, h, n) = Option.some(o) implies o.hom = h
        }

        theorem outer_new_inv[O, M](i: Inner[O, M], h: M, n: M, o: Outer[O, M]) {
            Outer[O, M].new(i, h, n) = Option.some(o) implies o.inv = n
        }

        theorem inner_endpoints[O, M](i: Inner[O, M], x: O) {
            i.a(i.c(x)) = x and i.b(i.c(x)) = x
        } by {
            Inner[O, M].constraint(i.a, i.b, i.c, i.d)
            inner_constraint(i.a, i.b, i.c, i.d) = (
                forall(y: O) { i.a(i.c(y)) = y and i.b(i.c(y)) = y }
                and forall(f: M, g: M) { i.a(f) = i.b(g) implies i.a(i.d(f, g)) = i.a(g) }
                and forall(f: M, g: M) { i.a(f) = i.b(g) implies i.b(i.d(f, g)) = i.b(f) }
                and forall(f: M, g: M, h: M) {
                    i.a(f) = i.b(g) and i.a(g) = i.b(h) implies i.d(i.d(f, g), h) = i.d(f, i.d(g, h))
                }
                and forall(f: M) { i.d(i.c(i.b(f)), f) = f }
                and forall(f: M) { i.d(f, i.c(i.a(f))) = f }
            )
        }

        let make_outer[O, M](i: Inner[O, M], x: O) -> result: Outer[O, M] satisfy {
            result.first = i and result.hom = i.c(x) and result.inv = i.c(x)
        } by {
            inner_endpoints(i, x)
            i.a(i.c(x)) = x
            i.b(i.c(x)) = x
            Inner[O, M].constraint(i.a, i.b, i.c, i.d)
            inner_constraint(i.a, i.b, i.c, i.d) = (
                forall(y: O) { i.a(i.c(y)) = y and i.b(i.c(y)) = y }
                and forall(f: M, g: M) { i.a(f) = i.b(g) implies i.a(i.d(f, g)) = i.a(g) }
                and forall(f: M, g: M) { i.a(f) = i.b(g) implies i.b(i.d(f, g)) = i.b(f) }
                and forall(f: M, g: M, h: M) {
                    i.a(f) = i.b(g) and i.a(g) = i.b(h) implies i.d(i.d(f, g), h) = i.d(f, i.d(g, h))
                }
                and forall(f: M) { i.d(i.c(i.b(f)), f) = f }
                and forall(f: M) { i.d(f, i.c(i.a(f))) = f }
            )
            i.d(i.c(x), i.c(x)) = i.c(x)
            i.a(i.c(x)) = i.b(i.c(x))
            outer_constraint(i, i.c(x), i.c(x))
            let o: Outer[O, M] satisfy {
                Outer[O, M].new(i, i.c(x), i.c(x)) = Option.some(o)
            }
            outer_new_first(i, i.c(x), i.c(x), o)
            outer_new_hom(i, i.c(x), i.c(x), o)
            outer_new_inv(i, i.c(x), i.c(x), o)
        }

        theorem make_outer_first[O, M](i: Inner[O, M], x: O) {
            make_outer(i, x).first = i
        }
    "#;

    let project = TempDir::new().unwrap();
    project.child("acorn.toml").write_str("").unwrap();
    let src = project.child("src");
    src.create_dir_all().unwrap();
    src.child("main.ac").write_str(text).unwrap();

    let mut verifier = Verifier::new(
        project.path().to_path_buf(),
        ProjectConfig::default(),
        Some("main".to_string()),
    )
    .unwrap();
    verifier.builder.check_hashes = false;

    let output = verifier
        .run()
        .expect("issue 47 reproducer should verify without invalid generated code");
    assert_eq!(output.status, BuildStatus::Good);
}
