use crate::tests::support::*;
use crate::{project::Project, prover::Outcome};

#[test]
fn test_prover_fails_on_bad_instance() {
    let text = r#"
    inductive Z2 {
        zero
        one
    }

    typeclass S: Singleton {
        value: S

        unique(x: S) {
            x = S.value
        }
    }

    instance Z2: Singleton {
        let value: Z2 = Z2.zero
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_prover_respects_typeclasses() {
    // Singleton.unique should not be misapplied to Z2.
    let text = r#"
    inductive Z2 {
        zero
        one
    }

    define is_equal[T](x: T, y: T) -> Bool {
        x = y
    }

    typeclass S: Singleton {
        element: S

        unique(x: S, y: S) {
            is_equal(x, y)
        }
    }

    theorem goal {
        is_equal(Z2.zero, Z2.one)
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_proving_with_parameterized_inductive() {
    let text = r#"
    inductive List[T] {
        nil
        cons(T, List[T])
    }

    define any(bs: List[Bool]) -> Bool {
        match bs {
            List.nil {
                false
            }
            List.cons(b, bs) {
                b or any(bs)
            }
        }
    }

    theorem goal {
        any(List.cons(true, List.nil[Bool]))
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_proving_with_mixin_instance() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
    inductive Foo {
        foo
    }
    let predicate[T]: T -> Bool = axiom

    typeclass S: Stuff {
        condition(s: S) {
            predicate(s)
        }
    }
    "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
    from foo import Foo, Stuff
    instance Foo: Stuff {}
    "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
    from foo import predicate
    from bar import Foo
    theorem goal {
        predicate(Foo.foo)
    }
    "#,
    );

    let module_id = p.load_module_by_name("main").expect("load failed");
    let env = match p.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    for cursor in env.iter_goals() {
        let mut processor =
            crate::processor::Processor::with_imports(None, cursor.bindings(), &p).unwrap();
        processor.add_module_facts(&cursor).unwrap();
        let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
        processor.set_lowered_goal(normalized_goal);
        let goal_kernel_context = &normalized_goal.kernel_context;

        let outcome = processor.search(crate::prover::ProverMode::Test, goal_kernel_context);
        assert_eq!(outcome, Outcome::Success);
        let cert = processor
            .prover()
            .make_cert(cursor.bindings(), goal_kernel_context, true)
            .expect("make_cert failed");
        processor
            .check_cert(&cert, None, goal_kernel_context, &p, cursor.bindings())
            .expect("check_cert failed");
    }
}

#[test]
fn test_proving_can_fail_with_destructuring() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }

    let Nat.suc(negative_one) = Nat.zero
    "#;
    verify_fails(text);
}

#[test]
fn test_prover_cannot_use_instance_backwards() {
    // One of two paired tests.
    // This direction should not work - we cannot use an instance relationship before it is proven.
    let text = r#"
    typeclass F: Foo {
        property: Bool
    }

    typeclass B: Bar extends Foo {
        vacuous_condition(b: B) {
            b = b
        }
    }

    type MyType: axiom

    let b: Bool = axiom

    instance MyType: Foo {
        let property: Bool = b
    }

    axiom ax[B: Bar] {
        B.property
    }

    theorem goal {
        MyType.property
    }

    instance MyType: Bar
    "#;
    verify_fails(text);
}
