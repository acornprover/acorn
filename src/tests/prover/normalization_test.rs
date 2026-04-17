use crate::tests::support::*;

#[test]
fn test_proving_avoids_infinite_monomorphization_recursion() {
    // This is a regression test to ensure we don't crash when processing
    // nested generic attribute calls with multiple type parameters.
    // The theorem is not provable, but we should handle it gracefully.
    let text = r#"

    inductive List<T> {
        nil
        cons(T, List<T>)
    }

    attributes List<T> {
        define map<U>(self, f: T -> U) -> List<U> {
            match self {
                List.nil {
                    List.nil<U>
                }
                List.cons(head, tail) {
                    List.cons(f(head), tail.map(f))
                }
            }
        }
    }

    theorem foo_1<T, U>(items: List<T>, f: T -> U, g: U -> U, items_1: List<U>) {
        items.map(f).map(g) = items_1
    }
    "#;
    // This should not crash, even though the theorem is not provable
    verify_fails(text);
}

#[test]
fn test_exists_normalization_should_not_demonstrate_inhabitedness() {
    let text = r#"

    inductive Option[T] {
        some(T)
        none
    }

    structure Foo[T] {
        item: T
    }

    let bar[T]: T -> Bool = axiom
    let baz[T]: Foo[T] -> Bool = axiom

    // This axiom doesn't mean much, for example it's trivially true if bar is always false.
    // The bug is that normalizing it can accidentally introduce a Foo[T] inhabitant.
    axiom ax1[T] {
        exists(t: T) {
            bar(t)
        } implies exists(f: Foo[T]) {
            baz(f)
        }
    }

    // This should not be provable. It is not true that a Foo[T] exists for all T.
    theorem goal[T] {
        exists(f: Foo[T]) {
            true
        }
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cross_module_eta_bridge_for_partial_application_fact() {
    let mut project = crate::project::Project::new_mock();
    project.mock(
        "/mock/helper.ac",
        r#"
        type Nat: axiom
        type Val: axiom

        define good(a: Nat -> Val) -> Bool {
            true
        }

        define good2(f: (Nat, Nat) -> Val) -> Bool {
            true
        }

        theorem right(f: (Nat, Nat) -> Val, i: Nat) {
            good2(f) implies good(function(j: Nat) { f(i, j) })
        }

        theorem distant(a: Nat -> Val, m: Nat, n: Nat) {
            good(a) and m = n implies a(m) = a(n)
        }
        "#,
    );
    project.mock(
        "/mock/main.ac",
        r#"
        from helper import Nat, Val, good, good2, right, distant

        theorem goal(f: (Nat, Nat) -> Val, i: Nat, m: Nat, n: Nat) {
            good2(f) and m = n implies f(i, m) = f(i, n)
        } by {
            if good2(f) and m = n {
                right(f, i)
                good(f(i))
                distant(f(i), m, n)
                f(i, m) = f(i, n)
            }
        }
        "#,
    );
    prove(&mut project, "main", "goal");
}

#[test]
fn test_citation_line_expands_to_instantiated_theorem_body() {
    let text = r#"
        type Ix: axiom
        type Val: axiom

        let rel: (Val, Val) -> Bool = axiom

        define good(a: Ix -> Val) -> Bool {
            true
        }

        theorem distant(a: Ix -> Val, m: Ix, n: Ix) {
            good(a) implies rel(a(m), a(n))
        }

        theorem goal(f: (Ix, Ix) -> Val, i: Ix, m: Ix, n: Ix) {
            rel(f(i, m), f(i, n))
        } by {
            good(f(i))
            distant(f(i), m, n)
            rel(f(i, m), f(i, n))
        }
        "#;

    let mut project = crate::project::Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    fn collect_props(env: &crate::elaborator::environment::Environment, out: &mut Vec<String>) {
        for node in &env.nodes {
            if let Some(crate::elaborator::fact::Fact::Proposition(prop)) = node.get_fact() {
                out.push(prop.value.to_string());
            }
            if let Some(block) = node.get_block() {
                collect_props(&block.env, out);
            }
        }
    }

    let mut proposition_values = vec![];
    collect_props(env, &mut proposition_values);

    assert!(
        proposition_values
            .iter()
            .any(|value| {
                value
                    == "function(x0: Ix -> Val, x1: Ix, x2: Ix) { (good(x0) implies rel(x0(x1), x0(x2))) }(f(i), m, n)"
            }),
        "expected expanded citation fact, got {:?}",
        proposition_values
    );
}

#[test]
fn test_type_only_theorem_citation_expands() {
    let text = r#"
        type Nat: axiom

        let constant_false[K]: K -> Bool = axiom

        theorem cite_me[K] {
            constant_false[K] = constant_false[K]
        }

        theorem goal {
            constant_false[Nat] = constant_false[Nat]
        } by {
            cite_me[Nat]
            constant_false[Nat] = constant_false[Nat]
        }
        "#;

    let mut project = crate::project::Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    fn collect_props(env: &crate::elaborator::environment::Environment, out: &mut Vec<String>) {
        for node in &env.nodes {
            if let Some(crate::elaborator::fact::Fact::Proposition(prop)) = node.get_fact() {
                out.push(prop.value.to_string());
            }
            if let Some(block) = node.get_block() {
                collect_props(&block.env, out);
            }
        }
    }

    let mut proposition_values = vec![];
    collect_props(env, &mut proposition_values);

    assert!(
        proposition_values
            .iter()
            .any(|value| value == "(constant_false[Nat] = constant_false[Nat])"),
        "expected expanded type-only citation fact, got {:?}",
        proposition_values
    );
    assert!(
        proposition_values
            .iter()
            .all(|value| value != "cite_me[Nat]"),
        "expected type-only citation to expand, got {:?}",
        proposition_values
    );
}

#[test]
#[ignore]
fn test_defined_goal_conjunction_of_forall_issue_44_repro() {
    // I made some changes from the actual issue 44. But now it works.
    verify_succeeds(
        r#"
        define compose[X, Y, Z](f: Y -> Z, g: X -> Y) -> X -> Z {
            function(x: X) {
                f(g(x))
            }
        }

        define are_two_sided_inverses[X, Y](f: X -> Y, g: Y -> X) -> Bool {
            forall(y: Y) { f(g(y)) = y } and forall(x: X) { g(f(x)) = x }
        }

        let b: Bool = axiom

        axiom fwd[X, Y, Z](
            f: X -> Y, g: Y -> Z, invf: Y -> X, invg: Z -> Y
        ) {
            b implies forall(z: Z) { compose(g, f)(compose(invf, invg)(z)) = z }
        }

        axiom bwd[X, Y, Z](
            f: X -> Y, g: Y -> Z, invf: Y -> X, invg: Z -> Y
        ) {
            b implies forall(x: X) { compose(invf, invg)(compose(g, f)(x)) = x }
        }

        theorem combined[X, Y, Z](
            f: X -> Y, g: Y -> Z, invf: Y -> X, invg: Z -> Y
        ) {
            b implies
            are_two_sided_inverses(compose(g, f), compose(invf, invg))
        } by {
            fwd(f, g, invf, invg)
            bwd(f, g, invf, invg)
        }
        "#,
    );
}
