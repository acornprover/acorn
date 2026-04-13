use crate::module::LoadState;
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::{Outcome, ProverMode};
use crate::tests::support::*;

// Search behavior, resolution, and rewrite regressions.

#[test]
fn test_no_verify_boolean_soup() {
    // This goal is not provable.
    // I'm not sure what ever went wrong, it's a mess of nested boolean formulas.
    let text = r#"
        theorem goal(a: Bool, b: Bool, c: Bool) {
            a = b or a = not c
        }
        "#;
    let outcome = verify(text).expect("verification errored");
    assert!(
        outcome == Outcome::Exhausted || outcome == Outcome::Timeout,
        "Expected Exhausted or Timeout, got {}",
        outcome
    );
}

#[test]
fn test_resolution_trap() {
    // This is a trap for the resolution algorithm, because repeated resolution
    // against the negated goal will give longer and longer formulas.
    let text = r#"
        type Nat: axiom
        let f: Nat -> Nat = axiom
        let g: Nat -> Bool = axiom
        let a: Nat = axiom
        axiom ga { g(a) }
        theorem goal {
            not forall(x: Nat) { g(x) implies g(f(x)) }
        }
        "#;
    verify_fails(text);
}

#[test]
fn test_verify_or_contraction() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define some(x: Nat) -> Bool { f(x) or g(x) or h(x) }
        axiom somea { f(a) or g(a) or h(a) }
        theorem goal { some(a) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_fimp_expansion() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }
        axiom fimpa { fimp(a) }
        theorem thm { f(a) implies (g(a) and h(a)) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_fimp_contraction() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }
        axiom fimpa { f(a) implies (g(a) and h(a)) }
        theorem goal { fimp(a) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_definition_trap() {
    // This will infinite loop if you allow free resolutions against definition.
    let text = r#"
        type Nat: axiom
        let z: Nat = axiom
        let f: Nat -> Bool = axiom
        let suc: Nat -> Nat = axiom
        define decr(x: Nat) -> Bool { f(x) and not f(suc(x))}
        axiom fz { f(z) }
        theorem goal { exists(x: Nat) { decr(x) } }
        "#;
    verify_fails(text);
}

#[test]
fn test_verify_functional_existence() {
    // There are two tricky things about this resolution.
    // In one of the directions, you have to resolve x0(x1) against foo(a, b).
    // In the other direction, in the final literal-literal resolution, both sides
    // still have a free variable. So we don't find it via simplification.
    // Nevertheless, intuitively it is just one step.
    let text = r#"
        type Nat: axiom
        let is_min: (Nat -> Bool, Nat) -> Bool = axiom
        let foo: Nat -> (Nat -> Bool) = axiom
        axiom has_min(f: Nat -> Bool, n: Nat) {
            f(n) implies exists(m: Nat) { is_min(f, m) }
        }
        axiom foo_is_true_somewhere(a: Nat) {
            exists(b: Nat) { foo(a, b) }
        }
        let min_foo(a: Nat) -> b: Nat satisfy {
            is_min(foo(a), b)
        }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_free_simplification_trap() {
    // This will infinite loop if you let a 3-to-2 resolution plus a 2-to-1 simplification
    // be zero depth.
    let text = r#"
        type Nat: axiom
        let foo: Nat -> Nat = axiom
        let bar: Nat -> Bool = axiom
        let zap: Nat -> Bool = axiom
        axiom expander(x: Nat) {
            not zap(x) or not bar(x) or zap(foo(x))
        }
        axiom simplifier(x: Nat) {
            bar(foo(x))
        }
        theorem goal(a: Nat) {
            not zap(foo(a))
        }
        "#;
    verify_fails(text);
}

#[test]
fn test_verify_rewrite_trap() {
    // This will infinite loop if you allow complexifying rewrites.
    let text = r#"
        type Nat: axiom
        let f: (Nat, Nat) -> Nat = axiom
        let g: Nat -> Bool = axiom
        axiom fxx(x: Nat) { f(x, x) = x }
        theorem goal(a: Nat) { g(a) }
        "#;
    verify_fails(text);
}

#[test]
fn test_prove_with_imported_existential() {
    let text = r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom

        axiom exists_a_fa {
            exists(a: Nat) { f(a) }
        }

        theorem goal {
            exists(a: Nat) { f(a) }
        }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_code_gen_not_losing_conclusion() {
    // Reproducing a bug found by Dan.
    // This confused the code generator because the final step of the proof
    // uses only a single source, so when you reverse it, it has no premise.
    // (It's using equality resolution to go from "x0 != constant" to a contradiction.)
    let text = r#"
            type Foo: axiom
            let zero: Foo = axiom
            let three: Foo = axiom
            let mul: (Foo, Foo) -> Foo = axiom

            define threeven(n: Foo) -> Bool {
                exists(d: Foo) {
                    mul(three, d) = n
                }
            }

            axiom mul_zero_right(a: Foo, b: Foo) {
                b = zero implies mul(a, b) = zero
            }

            theorem goal {
                threeven(zero)
            }
            "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_identity_is_surjective() {
    // To prove this, we need to instantiate the definitions of:
    // is_surjective[V, V]
    // identity[V]
    let text = r#"
            define is_surjective[T, U](f: T -> U) -> Bool {
                forall(y: U) {
                    exists(x: T) {
                        f(x) = y
                    }
                }
            }

            define identity[T](x: T) -> T {
                x
            }

            theorem identity_is_surjective[V] {
                is_surjective(identity[V])
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_lib_keyword() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
            type Foo: axiom
            let bar: Foo = axiom
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from foo import bar

            theorem goal {
                bar = lib(foo).bar
            }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_later_import_does_not_help_earlier_goal() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/common.ac",
        r#"
            let a: Bool = axiom
        "#,
    );
    p.mock(
        "/mock/helper.ac",
        r#"
            from common import a
            axiom helper { a }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from common import a

            theorem goal {
                a
            }

            from helper import helper
        "#,
    );

    let module_id = p.load_module_by_name("main").expect("load failed");
    let env = match p.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };
    let cursor = env.get_node_by_goal_name("goal");
    let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");

    let mut processor =
        Processor::with_imports(None, cursor.bindings(), &p).expect("processor creation failed");
    processor
        .add_module_facts(&cursor)
        .expect("adding module facts failed");
    processor.set_lowered_goal(normalized_goal);

    let outcome = processor.search(ProverMode::Test, &normalized_goal.kernel_context);
    assert_eq!(outcome, Outcome::Exhausted);
}

#[test]
fn test_proving_rewrite_only() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
          bar
          baz
        }
            
        let f: Foo -> Foo = axiom

        axiom rule1 {
          f(Foo.foo) = f(Foo.bar)
        }

        axiom rule2 {
          f(Foo.bar) = f(Foo.baz)
        }
            
        theorem goal {
          f(Foo.foo) = f(Foo.baz)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_eq!(proof, vec!["f(Foo.foo) != f(Foo.bar)"]);
}

#[test]
fn test_proving_modus_ponens_only() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
          bar
          baz
        }
            
        let f: Foo -> Bool = axiom

        axiom rule1 {
          f(Foo.foo) implies f(Foo.bar)
        }

        axiom rule2 {
          f(Foo.bar) implies f(Foo.baz)
        }
            
        theorem goal {
          f(Foo.foo) implies f(Foo.baz)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), vec!["not f(Foo.bar)", "not f(Foo.foo)"]);
}

#[test]
fn test_proving_with_active_resolution() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom
            
        axiom rule(x: Foo) {
          f(x) and g(x) implies h(x)
        }
            
        theorem goal(y: Foo) {
          f(y) and g(y) implies h(y)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { not g(x0) or not f(x0) or h(x0) }(y)",
            "g(y)",
            "f(y)",
        ],
    );
}

#[test]
fn test_proving_exact_clause_match() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom
            
        axiom rule {
          f(Foo.foo) or g(Foo.foo) or h(Foo.foo)
        }
            
        theorem goal {
          f(Foo.foo) or g(Foo.foo) or h(Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(
        c.proof.unwrap(),
        vec![
            "not h(Foo.foo)",
            "g(Foo.foo) or f(Foo.foo)",
            "not f(Foo.foo) and not g(Foo.foo)",
            "not g(Foo.foo)",
            "not f(Foo.foo)",
            "f(Foo.foo)",
        ]
    );
}

#[test]
fn test_proving_an_or() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom
            
        axiom rule1 {
          f(Foo.foo) or g(Foo.foo) or h(Foo.foo)
        }

        axiom rule2 {
          not f(Foo.foo)
        }
            
        theorem goal {
          g(Foo.foo) or h(Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(
        c.proof.unwrap(),
        vec![
            "not h(Foo.foo)",
            "g(Foo.foo) or f(Foo.foo)",
            "not g(Foo.foo)",
            "f(Foo.foo)",
        ]
    );
}

#[test]
fn test_proving_removes_duplicates() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
            
        axiom rule1(x: Foo) {
          f(x) implies g(x)
        }

        axiom rule2(x: Foo) {
          f(x)
        }
            
        theorem goal(y: Foo) {
          g(y)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { not f(x0) or g(x0) }(y)",
            "function(x0: Foo) { f(x0) }(y)",
        ],
    );
}

#[test]
fn test_proving_with_passive_resolution() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            g(x)
        }

        axiom rule2(x: Foo) {
            f(x) implies not g(x)
        }

        axiom rule3(x: Foo) {
            h(x) implies f(x)
        }
            
        theorem goal(y: Foo) {
            not h(y)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { not h(x0) or f(x0) }(y)",
            "function(x0: Foo) { not g(x0) or not f(x0) }(y)",
            "function(x0: Foo) { g(x0) }(y)",
            "f(y)",
        ],
    );
}

#[test]
fn test_proving_activating_rewrite_pattern() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            f(x) = g(x)
        }
            
        theorem goal(y: Foo) {
            h(f(y)) implies h(g(y))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(proof, &["function(x0: Foo) { g(x0) = f(x0) }(y)"]);
}

#[test]
fn test_proving_with_passive_contradiction() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            h(f(Foo.foo))
        }
            
        theorem goal(y: Foo) {
            forall(x: Foo) { f(x) = g(x) } implies h(g(Foo.foo))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { g(x0) = f(x0) }(Foo.foo)",
            "not h(f(Foo.foo))",
        ],
    );
}

#[test]
fn test_proving_with_multiple_rewrite() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }

        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom

        axiom rule1(x: Foo) {
            f(x) = g(x)
        }

        theorem goal(y: Foo) {
            f(f(f(y))) = g(g(g(y)))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { g(x0) = f(x0) }(y)",
            "function(x0: Foo) { g(x0) = f(x0) }(g(y))",
            "function(x0: Foo) { g(x0) = f(x0) }(g(g(y)))",
        ],
    );
}

#[test]
fn test_proving_random_bug() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: Foo -> Foo = axiom
        let z: Foo = axiom

        axiom rule1(x: Foo) {
            f(x) = g(x) or f(x) = h(x) or f(x) = z
        }
            
        theorem goal(y: Foo) {
            g(y) = h(y) implies f(y) = h(y) or f(y) = z
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { z = f(x0) or h(x0) = f(x0) or g(x0) = f(x0) }(y)",
            "f(y) != z",
            "h(y) != f(y)",
            "g(y) != f(y)",
            "g(y) = f(y)",
        ],
    );
}

#[test]
fn test_proving_with_equality_factoring_basic() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: Foo -> Foo = axiom

        axiom rule1(x: Foo) {
            f(x) != h(x)
        }

        axiom rule2(x: Foo) {
            g(x) = h(x)
        }
            
        theorem goal(y: Foo) {
            not (f(y) = g(y) or f(y) = h(y))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { h(x0) = g(x0) }(y)",
            "function(x0: Foo) { h(x0) != f(x0) }(y)",
            "h(y) != g(y) or g(y) = f(y)",
            "g(y) = f(y)",
        ],
    );
}

#[test]
fn test_proving_with_equality_factoring_mixed_forwards() {
    // This ends up being a tiny bit different than the previous one because the atoms
    // are normalized differently.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }

        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: Foo -> Foo = axiom

        axiom rule1(x: Foo) {
            h(x) != f(x)
        }

        axiom rule2(x: Foo) {
            g(x) = h(x)
        }

        theorem goal(y: Foo) {
            not (g(y) = f(y) or h(y) = f(y))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { h(x0) = g(x0) }(y)",
            "function(x0: Foo) { h(x0) != f(x0) }(y)",
            "h(y) != g(y) or g(y) = f(y)",
            "g(y) = f(y)",
        ],
    );
}

#[test]
fn test_proving_with_equality_resolution() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: (Foo, Foo) -> Bool = axiom
        let g: Foo -> Foo = axiom

        axiom rule1(x: Foo, y: Foo) {
            g(x) = g(y) implies f(x, y)
        }

        axiom rule2(x: Foo, y: Foo) {
            f(x, y) implies f(g(x), y)
        }
            
        theorem goal(x: Foo) {
            f(g(g(x)), x) 
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo, x1: Foo) { not f(x0, x1) or f(g(x0), x1) }(x, x)",
            "function(x0: Foo, x1: Foo) { not f(x0, x1) or f(g(x0), x1) }(g(x), x)",
            "function(x0: Foo, x1: Foo) { g(x0) != g(x1) or f(x0, x1) }(x, x)",
            "function(x0: Foo) { f(x0, x0) }(x)",
            "not f(g(x), x)",
        ],
    );
}

#[test]
fn test_nested_define_expansion() {
    // Regression test for https://github.com/acornprover/acorn/issues/42
    // When an inner define has a complex exists-forall body, expanding the
    // outer define must stay shallow so the prover finds the proof within
    // the shallow activation budget.
    let text = r#"
        type Elem: axiom
        let s: Elem -> Bool = axiom
        let f: Elem -> Elem = axiom
        let close: (Elem, Elem, Elem) -> Bool = axiom
        let pos: Elem -> Bool = axiom

        define inner(x: Elem) -> Bool {
            s(x) and
            forall(eps: Elem) {
                pos(eps) implies exists(delta: Elem) {
                    pos(delta) and forall(x1: Elem) {
                        s(x1) and close(x1, x, delta) implies
                        close(f(x1), f(x), eps)
                    }
                }
            }
        }

        define outer(dummy: Elem) -> Bool {
            forall(x: Elem) {
                s(x) implies inner(x)
            }
        }

        theorem goal(x: Elem) {
            outer(x) and s(x) implies inner(x)
        }
        "#;
    verify_succeeds(text);
}
