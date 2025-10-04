#[cfg(test)]
mod tests {
    use crate::statement::*;
    use indoc::indoc;

    fn should_parse(input: &str) -> Statement {
        match Statement::parse_str(input) {
            Ok(statement) => statement,
            Err(e) => panic!("failed to parse {}: {}", input, e),
        }
    }

    fn ok(input: &str) {
        let statement = should_parse(input);
        let output = statement.to_string();
        if input != output {
            panic!(
                "when parsing input:\n{}\nwe emitted output:\n{}",
                input, output
            );
        }
        assert_eq!(input, statement.to_string());
    }

    // Expects an error parsing the input into a statement, but not a lex error
    fn fail(input: &str) {
        if Statement::parse_str(input).is_ok() {
            panic!("statement parsed okay but we expected error:\n{}\n", input);
        }
    }

    fn fail_with(input: &str, expected_error: &str) {
        match Statement::parse_str(input) {
            Ok(statement) => panic!("expected failure but got statement: {}", statement),
            Err(e) => {
                if !e.to_string().contains(expected_error) {
                    panic!("expected error '{}', got '{}'", expected_error, e);
                }
            }
        }
    }

    #[test]
    fn test_definition_statements() {
        ok("let a: int = x + 2");
        ok("let f: int -> bool = compose(g, h)");
        ok(indoc! {"
        let f: int -> int = function(x: int) {
            x + 1
        }"});
        ok("let g: (int, int, int) -> bool = swap(h)");
        ok(indoc! {"
        define orx(p: bool, q: bool) -> bool {
            (not p implies q)
        }"});
        ok(indoc! {"
        define andx(p: bool, q: bool) -> bool {
            not (p implies not q)
        }"});
        ok(indoc! {"
        define iff_func(p: bool, q: bool) -> bool {
            (p implies q) and (q implies p)
        }"});
    }

    #[test]
    fn test_theorem_statements() {
        ok(indoc! {"axiom simplification {
            p implies (q implies p)
        }"});
        ok(indoc! {"axiom distribution {
            (p implies (q implies r)) implies ((p implies q) implies (p implies r))
        }"});
        ok(indoc! {"axiom contraposition {
            (not p implies not q) implies (q implies p)
        }"});
        ok(indoc! {"theorem and_comm {
            p and q iff q and p
        }"});
        ok(indoc! {"theorem and_assoc {
            (p and q) and r iff p and (q and r)
        }"});
        ok(indoc! {"theorem or_comm {
            p or q iff q or p
        }"});
        ok(indoc! {"theorem or_assoc {
            (p or q) or r iff p or (q or r)
        }"});
        ok(indoc! {"theorem suc_gt_zero(x: nat) {
            suc(x) > 0
        }"});
    }

    #[test]
    fn test_prop_statements() {
        ok(indoc! {"
        theorem goal {
            true
        } by {
            p implies p
        }"});
    }

    #[test]
    fn test_forall_statements() {
        ok(indoc! {"
            forall(x: Nat) {
                f(x) implies f(suc(x))
            }"});
    }

    #[test]
    fn test_forall_value_in_statement() {
        ok(indoc! {"
        let p: bool = forall(b: bool) {
            b or not b
        }"});
    }

    #[test]
    fn test_nat_ac_statements() {
        ok("type Nat: axiom");
        ok("let suc: Nat -> Nat = axiom");
        ok(indoc! {"
        axiom suc_injective(x: Nat, y: Nat) {
            suc(x) = suc(y) implies x = y
        }"});
        ok(indoc! {"
        axiom suc_neq_zero(x: Nat) {
            suc(x) != 0
        }"});
        ok(indoc! {"
        axiom induction(f: Nat -> bool, n: Nat) {
            f(0) and forall(k: Nat) {
                f(k) implies f(suc(k))
            } implies f(n)
        }"});
        ok(indoc! {"
        define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat {
            axiom
        }"});
        ok(indoc! {"
        axiom recursion_base(f: Nat -> Nat, a: Nat) {
            recursion(f, a, 0) = a
        }"});
        ok(indoc! {"
            axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {
                recursion(f, a, suc(n)) = f(recursion(f, a, n))
            }"});
        ok(indoc! {"
        define add(x: Nat, y: Nat) -> Nat {
            recursion(suc, x, y)
        }"});
        ok(indoc! {"
        theorem add_zero_right(a: Nat) {
            add(a, 0) = a
        }"});
        ok(indoc! {"
        theorem add_zero_left(a: Nat) {
            add(0, a) = a
        }"});
        ok(indoc! {"
        theorem add_suc_right(a: Nat, b: Nat) {
            add(a, suc(b)) = suc(add(a, b))
        }"});
        ok(indoc! {"
        theorem add_suc_left(a: Nat, b: Nat) {
            add(suc(a), b) = suc(add(a, b))
        }"});
        ok(indoc! {"
        theorem add_comm(a: Nat, b: Nat) {
            add(a, b) = add(b, a)
        }"});
        ok(indoc! {"
            theorem add_assoc(a: Nat, b: Nat, c: Nat) {
                add(a, add(b, c)) = add(add(a, b), c)
            }"});
    }

    #[test]
    fn test_block_parsing() {
        ok(indoc! {"
            theorem foo {
                bar
            } by {
                baz
            }"});
        fail(indoc! {"
            foo {
                bar
            }"});
    }

    #[test]
    fn test_by_on_next_line() {
        let statement = should_parse(indoc! {"
            theorem foo { bar }
            by {
                baz
            }"});
        let expected = indoc! {"
        theorem foo {
            bar
        } by {
            baz
        }"};
        assert_eq!(expected, statement.to_string());
    }

    #[test]
    fn test_statement_errors() {
        fail("+ + +");
        fail("let p: Bool =");
        fail("let p: Bool = (");
        fail("let p: Bool = (x + 2");
        fail("let p: Bool = x + 2)");
    }

    #[test]
    fn test_declared_variable_names_lowercased() {
        ok("let p: Bool = true");
        fail("let P: Bool = true");
    }

    #[test]
    fn test_defined_variable_names_lowercased() {
        ok(indoc! {"
        define foo(x: Bool) -> Bool {
            true
        }"});
        fail("define Foo(x: Bool) -> Bool: true");
    }

    #[test]
    fn test_theorem_names_lowercased() {
        ok(indoc! {"
        theorem foo {
            true
        }"});
        fail("theorem Foo: true");
    }

    #[test]
    fn test_structure_names_titlecased() {
        ok(indoc! {"
        structure Foo {
            bar: Nat
        }"});
        fail(indoc! {"
        structure foo {
            bar: Nat
        }"});
    }

    #[test]
    fn test_type_names_titlecased() {
        ok("type Foo: axiom");
        fail("type foo: axiom");
    }

    #[test]
    fn test_only_declarations_in_signatures() {
        fail("theorem foo(x: int, x > 0): x + 1 > 0");
    }

    #[test]
    fn test_single_line_forall() {
        should_parse("forall(x: Nat) { f(x) implies f(suc(x)) }");
    }

    #[test]
    fn test_variable_satisfy_statement() {
        ok(indoc! {"
        let x: Nat satisfy {
            x > 0
        }"});
    }

    #[test]
    fn test_variable_satisfy_multivar_statement() {
        ok(indoc! {"
        let (x: Nat, y: Nat) satisfy {
            x > y
        }"});
    }

    #[test]
    fn test_single_line_variable_satisfy_statement() {
        should_parse("let x: Nat satisfy { x > 0 }");
    }

    #[test]
    fn test_single_line_variable_satisfy_multivar_statement() {
        should_parse("let (x: Nat, y: Nat) satisfy { x > y }");
    }

    #[test]
    fn test_function_satisfy_statement() {
        ok(indoc! {"
        let foo(a: Nat, m: Nat) -> r: Nat satisfy {
            r = a + m
        }"});
    }

    #[test]
    fn test_function_satisfy_statement_with_by_block() {
        ok(indoc! {"
        let foo(a: Nat, m: Nat) -> r: Nat satisfy {
            r > a + m
        } by {
            a + m + 1 > a + m
        }"});
    }

    #[test]
    fn test_if_statement() {
        ok(indoc! {"
        if x > 1 {
            x > 0
        }"});
    }

    #[test]
    fn test_structure_statement() {
        ok(indoc! {"
        structure NatPair {
            first: Nat
            second: Nat
        }"});
    }

    #[test]
    fn test_no_empty_structures() {
        fail("structure Foo {}");
    }

    #[test]
    fn test_structure_fields_need_newlines() {
        fail("structure Foo { bar: Nat }");
    }

    #[test]
    fn test_structure_fields_capitalized_correctly() {
        fail(indoc! {"
        structure fooBar {
            foo: Bar
        }"});
        fail(indoc! {"
        structure FooBar {
            Foo: Bar
        }"});
    }

    #[test]
    fn test_inductive_statement() {
        ok(indoc! {"
        inductive Nat {
            zero
            suc(Nat)
        }"});
    }

    #[test]
    fn test_no_empty_inductive_statements() {
        fail("inductive Nat {}");
    }

    #[test]
    fn test_inductive_fields_need_newlines() {
        fail("inductive Nat { zero }");
    }

    #[test]
    fn test_theorem_with_type_parameter() {
        ok(indoc! {"
        axiom recursion_base[T](f: T -> T, a: T) {
            recursion(f, a, 0) = a
        }"});
    }

    #[test]
    fn test_definition_with_type_parameter() {
        ok(indoc! {"
        define recursion[T](f: T -> T, a: T, n: Nat) -> Nat {
            axiom
        }"});
    }

    #[test]
    fn test_import_statement() {
        ok("import foo.bar.baz");
    }

    #[test]
    fn test_if_else_statement() {
        ok(indoc! {"
        if foo(x) {
            bar(x)
        } else {
            qux(x)
        }"});
    }

    #[test]
    fn test_no_lone_else_statement() {
        fail("else { qux(x) }");
    }

    #[test]
    fn test_attributes_statement() {
        ok(indoc! {"
        attributes Foo {
            let blorp: Foo = axiom
            let 0: Foo = axiom
        }"});
    }

    #[test]
    fn test_from_statement() {
        ok("from foo import bar");
        ok("from foo.bar import baz");
        ok("from foo.bar.qux import baz, zip");
        fail("from foo");
    }

    #[test]
    fn test_failing_early_on_bad_define_syntax() {
        fail_with(
            indoc! {"
        define foo(x: Nat) -> Nat: bar
        baz(qux)
        zip(dash)
        fo(fum)
        "},
            "unexpected token",
        );
    }

    #[test]
    fn test_parsing_match_statement() {
        ok(indoc! {"
        match x {
            Foo.bar {
                baz
            }
            Foo.qux {
                zip
            }
        }"});
    }

    #[test]
    fn test_anonymous_theorem_statement() {
        ok(indoc! {"
        theorem {
            true
        }"});
    }

    #[test]
    fn test_anonymous_theorem_statement_with_arguments() {
        ok(indoc! {"
        theorem(a: Bool, b: Bool) {
            a = b or a or b
        }"});
    }

    #[test]
    fn test_parsing_structure_with_constraint() {
        ok(indoc! {"
        structure Foo {
            bar: Nat
            baz: Nat
        } constraint {
            bar > baz
        }"});
    }

    #[test]
    fn test_parsing_structure_with_constraint_and_by() {
        ok(indoc! {"
        structure Foo {
            bar: Nat
            baz: Nat
        } constraint {
            bar > baz
        } by {
            1 > 0
        }"});
    }

    #[test]
    fn test_parsing_typeclass_statement_constants() {
        ok(indoc! {"
        typeclass F: Foo {
            bar: (F, F) -> Bool
            baz: F
            qux: Bool
        }"});
    }

    #[test]
    fn test_parsing_structure_with_type_params() {
        ok(indoc! {"
        structure Pair[T, U] {
            first: T
            second: U
        }"});
    }

    #[test]
    fn test_parsing_attributes_statement_with_type_params() {
        ok(indoc! {"
        attributes Pair[T, U] {
            define swap(self) -> Pair[U, T] {
                Pair.new(self.second, self.first)
            }
        }"});
    }

    #[test]
    fn test_parsing_typeclass_statement_theorems() {
        ok(indoc! {"
        typeclass T: MyTypeclass {
            two_nonequal {
                exists(x: T, y: T) {
                    x != y
                }
            }
            always_a_third(x: T, y: Y) {
                exists(z: T) {
                    x != z and y != z
                }
            }
        }"});
    }

    #[test]
    fn test_parsing_typeclass_statement_general() {
        ok(indoc! {"
        typeclass F: Foo {
            bar: (F, F) -> Bool
            some_bar(x: F) {
                exists(y: F) {
                    x.bar(y)
                }
            }
        }"});
    }

    #[test]
    fn test_parsing_instance_statement() {
        ok(indoc! {"
        instance State: Magma {
            define mul(self, other: State) -> State {
                State.dirty
            }
        }"});
    }

    #[test]
    fn test_parsing_parametrized_let_statements() {
        ok("let foo[T]: T = bar[T]");
        ok("let foo[T: Thing]: T = bar[T]");
    }

    #[test]
    fn test_parsing_parametrized_inductive_statement() {
        ok(indoc! {"
        inductive List[T] {
            nil
            cons(T, List[T])
        }"});
    }

    #[test]
    fn test_parsing_typeclass_statement_with_extends() {
        ok(indoc! {"
        typeclass F: Foo extends Bar {
            b: Bool
        }"});
    }

    #[test]
    fn test_parsing_typeclass_statement_with_multiple_extends() {
        ok(indoc! {"
        typeclass F: Foo extends Bar, Baz {
            b: Bool
        }"});
    }

    #[test]
    fn test_parsing_typeclass_statement_no_block_syntax() {
        ok("typeclass Qux extends Foo, Bar");
        ok("typeclass Simple extends Base");
    }

    #[test]
    fn test_parsing_instance_statement_no_block_syntax() {
        ok("instance Nat: Trivial");
        ok("instance String: Show");
    }

    #[test]
    fn test_parsing_doc_comment_pseudo_statement() {
        ok("/// This is a doc comment");
    }

    #[test]
    fn test_parsing_todo_statement() {
        ok(indoc! {"
        todo {
            theorem foo(a: Bool, b: Bool) {
                a = b or a or b
            }
        }"});
    }

    #[test]
    fn test_parsing_match_in_define_statement() {
        ok(indoc! {"
        define foo(x: Nat) -> Nat {
            match x {
                Nat.zero {
                    0
                }
                Nat.suc(n) {
                    n + 1
                }
            }
        }"});
    }

    #[test]
    fn test_function_must_have_arguments() {
        fail_with(
            indoc! {"
            define foo[T] -> Bool {
                true
            }"},
            "must have at least one argument",
        );
    }
}
