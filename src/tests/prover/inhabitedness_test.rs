use crate::tests::support::*;
use crate::{project::Project, prover::Outcome};

// Prover coverage for inhabitedness reasoning and generated witnesses.

#[test]
fn test_cannot_inhabit_arbitrary_type() {
    // You should not be able to prove that every type has an element
    // just by satisfying "true".
    let text = r#"
    let inhabitant[T]: T satisfy {
        true
    }
    "#;
    // This should fail because T is not provably inhabited
    verify_fails(text);
}

#[test]
fn test_negated_exists_axiom_does_not_imply_false() {
    // Regression test for negated-existential handling:
    // from "not exists(x: T) { true }" we must NOT be able to conclude false
    // for arbitrary T.
    let text = r#"
    axiom no_elem[T] {
        not exists(x: T) {
            true
        }
    }

    theorem contradiction[T] {
        false
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_inhabit_arbitrary_type_self_equality() {
    // Self-equality is always true, so this is equivalent to "true".
    // It should still be rejected.
    let text = r#"
    let inhabitant[T]: T satisfy {
        inhabitant = inhabitant
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_inhabit_arbitrary_type_const_true() {
    // This should be rejected because T might not be inhabited.
    // Unlike the other tests, this one is NOT caught during normalization because
    // the variable is still used in const_true(inhabitant). Instead, the prover
    // correctly refuses to conclude a contradiction from foralls over uninhabited types.
    let text = r#"
    define const_true[T](x: T) -> Bool {
        true
    }

    let inhabitant[T]: T satisfy {
        const_true(inhabitant)
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_avoid_inhabitedness_through_resolution() {
    // When T is not inhabited, ax1 and ax2 do not imply goal.
    let text = r#"
    let foo[T]: Bool = axiom
    let bar[T]: T -> Bool = axiom

    axiom ax1[T](x: T) {
        bar(x) implies foo[T]
    }

    axiom ax2[T](x: T) {
        not bar(x) implies foo[T]
    }

    theorem goal[T] {
        foo[T]
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_avoid_inhabitedness_through_resolution_with_concrete_uninhabited_type() {
    // This should be rejected: FiniteSet might be empty, so we cannot derive a
    // contradiction by instantiating forall(x: FiniteSet) clauses with a witness picked only
    // from inhabitedness.
    let text = r#"
    inductive Set {
        empty
    }

    let is_finite: Set -> Bool = axiom

    type FiniteSet: axiom
    let underlying_set: FiniteSet -> Set = axiom

    axiom finite_underlying(s: FiniteSet) {
        is_finite(underlying_set(s))
    }

    axiom all_equal(x: Set, y: Set) {
        x = y
    }

    theorem goal {
        is_finite(Set.empty)
    }
    "#;

    // The correct result is Exhausted. Current behavior returns Success by deriving
    // an unsound contradiction via an arbitrary FiniteSet witness.
    assert_eq!(prove_text(text, "goal"), Outcome::Exhausted);
}

#[test]
fn test_cannot_avoid_inhabitedness_through_equality_reduction() {
    // This should be rejected because T might not be inhabited at all.
    let text = r#"
    theorem bar_or_not_bar[T](bar: T -> Bool) {
        exists(x: T) {
            bar(x) or not bar(x)
        }
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_can_inhabit_arbitrary_type_of_typeclass() {
    // This should be accepted, since any arbitrary P: Pointed is inhabited.
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed]: P satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_can_inhabit_arbitrary_type_of_extended_typeclass() {
    // This should be accepted, since any arbitrary P: Pointed is inhabited.
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    typeclass Q: Qux extends Pointed {
        foo: Q -> Bool
    }

    let inhabitant[Q: Qux]: Q satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_can_inhabit_function_type_when_codomain_inhabited() {
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed, Q]: Q -> P satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_cannot_inhabit_function_type_when_only_domain_inhabited() {
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed, Q]: P -> Q satisfy {
        true
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_can_inhabit_identity_function_type() {
    let text = r#"
    let inhabitant[T]: T -> T satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_can_inhabit_list_type() {
    let text = r#"
    inductive List[T] {
        cons(List[T])
        nil
    }
    let inhabitant[T]: List[T] satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_inhabited_const() {
    let text = r#"
    let inhabited[T]: Bool = exists(x: T) {
        true
    }
    "#;
    verify_succeeds(text);
}

/// Regression test: when a certificate uses a typeclass constraint from a function
/// defined in another module, but the current module hasn't directly imported that
/// typeclass BY NAME, the code generator should use lib(module).TypeclassName syntax.
///
/// This mirrors the real bug in binomial.ac where:
/// - a module imports a theorem that mentions `Monoid` only indirectly
/// - proof search introduces a generated witness with a `Monoid` constraint
/// - certificate replay must still print that constraint with a qualified name
///
/// The fix is for the code generator to substitute type variables that aren't valid
/// type names with concrete types that implement the required typeclass.
#[test]
fn test_generated_witness_with_unimported_typeclass_constraint() {
    let mut p = Project::new_mock();

    // Base typeclass
    p.mock(
        "/mock/monoid.ac",
        r#"
    typeclass M: Monoid {
        zero: M
        add: (M, M) -> M
    }

    // A function with Monoid constraint that has a forall (introduces a witness term)
    theorem monoid_thm[T: Monoid](f: T -> T, x: T) {
        (forall(y: T) { f(y) = y }) implies f(x) = x
    }
    "#,
    );

    // Extended typeclass
    p.mock(
        "/mock/ring.ac",
        r#"
    from monoid import Monoid

    typeclass R: Ring extends Monoid {
        one: R
        mul: (R, R) -> R
    }
    "#,
    );

    // Wrapper that exports monoid_thm but NOT Monoid by name
    p.mock(
        "/mock/wrapper.ac",
        r#"
    from monoid import monoid_thm
    "#,
    );

    // Main module:
    // - imports Ring from ring.ac (which imports Monoid, so typeclass_defs has Monoid)
    // - imports monoid_thm from wrapper (NOT from monoid.ac)
    // - does NOT directly import Monoid by name
    // So main has Monoid in typeclass_defs but NOT in name_to_typeclass
    p.mock(
        "/mock/main.ac",
        r#"
    from ring import Ring
    from wrapper import monoid_thm

    // This goal uses monoid_thm with Ring (which extends Monoid).
    // Proof search introduces a generated witness with [T: Monoid] constraint.
    // The code generator must use lib(monoid).Monoid format.
    theorem goal[R: Ring](f: R -> R, x: R) {
        (forall(y: R) { f(y) = y }) implies f(x) = x
    } by {
        monoid_thm(f, x)
    }
    "#,
    );

    let module_id = p.load_module_by_name("main").expect("load failed");
    let env = match p.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    // Check that Monoid is NOT in name_to_typeclass
    assert!(
        !env.bindings.has_typeclass_name("Monoid"),
        "Monoid should NOT be in name_to_typeclass for main module"
    );

    // Run the prover and generate a certificate
    let cursor = env.iter_goals().next().expect("expected a goal in main");
    let mut processor =
        crate::processor::Processor::with_imports(None, cursor.bindings(), &p).unwrap();
    processor.add_module_facts(&cursor).unwrap();
    let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
    processor.set_lowered_goal(normalized_goal);
    let goal_kernel_context = &normalized_goal.kernel_context;

    let outcome = processor.search(crate::prover::ProverMode::Test, goal_kernel_context);
    assert_eq!(outcome, Outcome::Success);

    // Generate the certificate
    let cert = processor
        .prover()
        .make_cert(cursor.bindings(), goal_kernel_context, true)
        .expect("make_cert failed");

    // Debug: print the certificate
    eprintln!("Certificate proof:");
    if let Some(proof) = &cert.proof {
        for (i, step) in proof.iter().enumerate() {
            eprintln!("  Step {}: {}", i, step);
        }
    }

    // The certificate should verify successfully
    // (If the code generator correctly uses lib(monoid).Monoid format)
    processor
        .check_cert(&cert, None, goal_kernel_context, &p, cursor.bindings())
        .expect("check_cert should succeed");
}

// Regression test for a bug where polymorphic structures containing functions with
// if-then-else expressions returning non-Bool types would cause a type mismatch
// during clause validation. The issue was with how normalization tracked the local
// type-parameter slots inside function definitions in `define` statements.
#[test]
fn test_polymorphic_structure_with_function_if_then_else() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }

    structure Wrapper[T] {
        func: T -> Nat
    }

    attributes Wrapper[T] {
        define modify(self, item: T) -> Wrapper[T] {
            Wrapper.new(function(x: T) {
                if x = item {
                    self.func(x).suc
                } else {
                    self.func(x)
                }
            })
        }
    }

    theorem goal[T](w: Wrapper[T], item: T) {
        w.modify(item) = w.modify(item)
    }
    "#;
    verify_succeeds(text);
}

// Reproduces a bug where the prover needs to instantiate a polymorphic axiom
// with an arbitrary type, resulting in certificate code like "let w2: x0 satisfy { true }"
// which is invalid because x0 is not a valid type name.
#[test]
fn test_polymorphic_axiom_chain_needs_arbitrary_type() {
    let text = r#"
    let foo: Bool = axiom
    let baz: Bool = axiom

    define bar[T](x: T) -> Bool {
        axiom
    }

    axiom foo_imp_bar[T](x: T) {
        foo implies bar[T](x)
    }

    axiom bar_imp_baz[T](x: T) {
        bar[T](x) implies baz
    }

    theorem goal {
        foo implies baz
    }
    "#;
    verify_succeeds(text);
}

// Regression: certificates generated while proving a polymorphic structure
// constructor definition must check with the goal's type parameters in scope.
#[test]
fn test_subgroup_identity_existence_cert_generation() {
    verify_succeeds(
        r#"
        inductive Option[T] {
            none
            some(T)
        }

        typeclass G: Group {
            1: G
        }

        define subgroup_constraint[G: Group](contains: G -> Bool) -> Bool {
            contains(G.1)
        }

        define is_identity[G: Group](g: G) -> Bool {
            g = G.1
        }

        theorem identity_subgroup_constraint[G: Group] {
            subgroup_constraint(is_identity[G])
        }

        structure Subgroup[G: Group] {
            contains: G -> Bool
        } constraint {
            subgroup_constraint(contains)
        }

        let identity_subgroup[G: Group]: Subgroup[G] satisfy {
            Subgroup.new_option(is_identity[G]) = Option.some(identity_subgroup)
        }
        "#,
    );
}

#[test]
fn test_subgroup_identity_existence_cert_keeps_outer_type_args_in_claim_with_args() {
    let text = r#"
        inductive Option[T] {
            none
            some(T)
        }

        typeclass G: Group {
            1: G
        }

        define subgroup_constraint[G: Group](contains: G -> Bool) -> Bool {
            contains(G.1)
        }

        define is_identity[G: Group](g: G) -> Bool {
            g = G.1
        }

        theorem identity_subgroup_constraint[G: Group] {
            subgroup_constraint(is_identity[G])
        }

        structure Subgroup[G: Group] {
            contains: G -> Bool
        } constraint {
            subgroup_constraint(contains)
        }

        let identity_subgroup[G: Group]: Subgroup[G] satisfy {
            Subgroup.new_option(is_identity[G]) = Option.some(identity_subgroup)
        }
    "#;

    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };
    let cursor = env
        .iter_goals()
        .find(|cursor| {
            cursor
                .goal()
                .map(|goal| goal.name.starts_with("exists(k0: Subgroup["))
                .unwrap_or(false)
        })
        .expect("expected subgroup existence goal");
    let mut processor =
        crate::processor::Processor::with_imports(None, cursor.bindings(), &project).unwrap();
    processor.add_module_facts(&cursor).unwrap();
    let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
    processor.set_lowered_goal(normalized_goal);
    let goal_kernel_context = &normalized_goal.kernel_context;

    let outcome = processor.search(crate::prover::ProverMode::Test, goal_kernel_context);
    assert_eq!(outcome, Outcome::Success);

    let cert = processor
        .prover()
        .make_cert(cursor.bindings(), goal_kernel_context, false)
        .expect("make_cert failed");
    let proof = cert.proof.expect("proof should exist");

    assert!(
        proof
            .iter()
            .any(|line| line.contains("}[G](is_identity[G])")),
        "expected claim-with-args line to keep the outer goal type argument: {proof:?}"
    );
    assert!(
        !proof.iter().any(|line| line.contains("is_identity[Bool]")),
        "claim-with-args line should not instantiate the goal type to Bool: {proof:?}"
    );
}
