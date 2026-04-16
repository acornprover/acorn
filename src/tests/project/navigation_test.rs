use im::HashMap;
use tower_lsp::lsp_types::{HoverContents, Location, MarkedString, Position, Range, Url};

use crate::elaborator::names::ConstantName;
use crate::module::ModuleDescriptor;
use crate::project::{localize_mock_filename, Project, ProjectConfig, SelectionInfo};
use indoc::indoc;

use super::support::expect_build_ok;

// Hover, go-to-definition, docs, and selection behavior across a project.

#[test]
fn test_hover_basic() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
    /// Nat_doc_comment
    inductive Nat {                           // line 1
        0                                     // line 2
        suc(Nat)                              // line 3
    }
    // 3456789012345678901234567890
    let one: Nat = Nat.suc(Nat.0)             // line 6
    define make_nat(odd: Bool) -> Nat {       // line 7
        if odd {                              // line 8
            one                               // line 9
        } else {
            Nat.suc(one)                      // line 11
        }
    }
    /// HasZero_doc_comment                   // line 14
    typeclass Z: HasZero {
        0: Z
    }
    // 34567890123456789012345678901
    instance Nat: HasZero {                   // line 19
        let 0 = Nat.0                         // line 20
    }
    theorem eq_zero[Z: HasZero](a: Z) {       // line 22
        a = Z.0                               // line 23
    } by {
        let b: Z = a                          // line 25
    }
    /// equals_doc_comment
    define equals[T](x: T, y: T) -> Bool {    // line 28
        x = y                             
    }
    let z_eq_z = equals(Nat.0, Nat.0)         // line 31
    /// num_doc_comment
    let num: Nat = make_nat(true)             // line 33
    /// List_doc_comment
    inductive List[T] {                       // line 35
        nil
        cons(T, List[T])
    }
    let l = List.cons(num, List.nil[Nat])     // line 39
    // 34567890123456789012345678901
    let m: Nat satisfy {                      // line 41
        m = m
    }
    "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");
    assert!(p.hover(&env, 6, 9).is_some()); // Nat
    assert!(p.hover(&env, 6, 19).is_some()); // suc
    assert!(p.hover(&env, 6, 24).is_some()); // Nat
    assert!(p.hover(&env, 6, 26).is_none()); // .
    assert!(p.hover(&env, 6, 27).is_some()); // 0
    assert!(p.hover(&env, 6, 30).is_none()); // past end of line
    assert!(p.hover(&env, 7, 22).is_some()); // Bool
    assert!(p.hover(&env, 7, 30).is_some()); // Nat
    assert!(p.hover(&env, 8, 9).is_some()); // odd
    assert!(p.hover(&env, 9, 9).is_some()); // one
    assert!(p.hover(&env, 11, 9).is_some()); // Nat
    assert!(p.hover(&env, 11, 13).is_some()); // suc
    assert!(p.hover(&env, 11, 17).is_some()); // one
    assert!(p.hover(&env, 19, 9).is_some()); // Nat
    assert!(p.hover(&env, 19, 14).is_some()); // HasZero
    assert!(p.hover(&env, 20, 12).is_some()); // Nat
    assert!(p.hover(&env, 20, 16).is_some()); // 0
    assert!(p.hover(&env, 22, 19).is_some()); // HasZero
    assert!(p.hover(&env, 22, 31).is_some()); // Z
    assert!(p.hover(&env, 23, 4).is_some()); // a
    assert!(p.hover(&env, 23, 8).is_some()); // Z
    assert!(p.hover(&env, 23, 10).is_some()); // 0
    assert!(p.hover(&env, 25, 11).is_some()); // Z
    assert!(p.hover(&env, 25, 15).is_some()); // a
    assert!(p.hover(&env, 28, 20).is_some()); // T
    assert!(p.hover(&env, 31, 20).is_some()); // Nat
    assert!(p.hover(&env, 41, 8).is_some()); // Nat

    // Check hovers

    let nat_hover = format!("{:?}", p.hover(&env, 6, 11));
    assert!(nat_hover.contains("Nat_doc_comment"));

    let has_zero_hover = format!("{:?}", p.hover(&env, 19, 19));
    assert!(has_zero_hover.contains("HasZero_doc_comment"));

    let equals_hover = format!("{:?}", p.hover(&env, 31, 14));
    assert!(equals_hover.contains("equals_doc_comment"));

    let num_hover = format!("{:?}", p.hover(&env, 39, 18));
    assert!(num_hover.contains("num_doc_comment"));

    let list_hover = format!("{:?}", p.hover(&env, 39, 23));
    assert!(list_hover.contains("List_doc_comment"));

    // Check that "Go to" links are present
    let nat_hover_str = format!("{:?}", p.hover(&env, 6, 11));
    assert!(nat_hover_str.contains("Go to Nat"));

    let has_zero_hover_str = format!("{:?}", p.hover(&env, 19, 19));
    assert!(has_zero_hover_str.contains("Go to HasZero"));
}

#[test]
fn test_hover_with_imports() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        indoc! {r"
        /// module_doc_comment
        
        /// type_doc_comment
        inductive Foo {               // line 3
            foo
        }

        /// val_doc_comment
        let bar = (Foo.foo = Foo.foo)
        "},
    );
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
        // 3456789012345678901234567890  
        from foo import Foo, bar         // line 1
        "#},
    );
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");
    assert!(p.hover(&env, 1, 2).is_none()); // from
    assert!(p.hover(&env, 1, 7).is_some()); // foo
    assert!(p.hover(&env, 1, 10).is_none()); // import
    assert!(p.hover(&env, 1, 17).is_some()); // Foo
    assert!(p.hover(&env, 1, 21).is_some()); // bar

    // Check hovers

    let module_hover = format!("{:?}", p.hover(&env, 1, 7));
    assert!(module_hover.contains("module_doc_comment"));
    assert!(!module_hover.contains("type_doc_comment"));

    let type_hover = format!("{:?}", p.hover(&env, 1, 17));
    assert!(!type_hover.contains("module_doc_comment"));
    assert!(type_hover.contains("type_doc_comment"));

    let val_hover = format!("{:?}", p.hover(&env, 1, 21));
    assert!(val_hover.contains("val_doc_comment"));
}

#[test]
fn test_theorem_hover_and_definition_omit_proof_body() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
        theorem helper {                 // line 1
            true                         // line 2
        } by {                           // line 3
            let hidden: Bool = true      // line 4
        }
        // 3456789012345678901234567890
        theorem uses_helper {            // line 7
            helper                       // line 8
        }
        "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");

    let helper_name = ConstantName::Unqualified(env.module_id, "helper".to_string());
    let definition = p
        .get_constant_definition_string(&env, &helper_name)
        .expect("helper should have a definition string");
    assert!(definition.contains("theorem helper"));
    assert!(definition.contains("true"));
    assert!(!definition.contains("} by {"));
    assert!(!definition.contains("let hidden: Bool = true"));

    let mut hover = None;
    for line in 7..=9 {
        for character in 0..20 {
            let Some(candidate) = p.hover(&env, line, character) else {
                continue;
            };
            let candidate = format!("{:?}", candidate);
            if candidate.contains("theorem helper") {
                hover = Some(candidate);
                break;
            }
        }
        if hover.is_some() {
            break;
        }
    }
    let hover = hover.expect("hover should exist");
    assert!(hover.contains("theorem helper"));
    assert!(hover.contains("true"));
    assert!(!hover.contains("} by {"));
    assert!(!hover.contains("let hidden: Bool = true"));
}

#[test]
fn test_definition_location_basic() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
    /// Nat_doc_comment
    inductive Nat {                           // line 1
        0
        suc(Nat)                              // line 3
    }
    // 3456789012345678901234567890
    let one: Nat = Nat.suc(Nat.0)             // line 6
    define make_nat(odd: Bool) -> Nat {       // line 7
        if odd {
            one                               // line 9
        } else {
            Nat.suc(one)                      // line 11
        }
    }
    /// HasZero_doc_comment
    typeclass Z: HasZero {                    // line 15
        0: Z
    }
    typeclass O: HasOne extends HasZero {     // line 18
        1: O
    }
    // 34567890123456789012345678901
    instance Nat: HasZero {                   // line 22
        let 0 = Nat.0                         // line 23
    }
    theorem eq_zero[Z: HasZero](a: Z) {       // line 25
        a = Z.0
    } by {
        let b: Z = a
    }
    /// equals_doc_comment
    define equals[T](x: T, y: T) -> Bool {    // line 31
        x = y
    }
    let z_eq_z = equals(Nat.0, Nat.0)         // line 34
    /// num_doc_comment
    let num: Nat = make_nat(true)             // line 36
    /// List_doc_comment
    inductive List[T] {                       // line 38
        nil
        cons(T, List[T])                      // line 40
    }
    let l = List.cons(num, List.nil[Nat])     // line 42
    // 34567890123456789012345678901
    let m: Nat satisfy {                      // line 44
        m = m
    }
    "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");

    let location = |line, start_character, end_character| Location {
        uri: Url::from_file_path(localize_mock_filename("/mock/main.ac"))
            .expect("Failed to create URL from /mock/main.ac - this path should be valid"),
        range: Range {
            start: Position {
                line,
                character: start_character,
            },
            end: Position {
                line,
                character: end_character,
            },
        },
    };

    // expected locations
    let nat = Some(location(1, 10, 13));
    let one = Some(location(6, 4, 7));
    let make_nat = Some(location(7, 7, 15));
    let has_zero = Some(location(15, 13, 20));
    let equals = Some(location(31, 7, 13));
    let list = Some(location(38, 10, 14));

    // expected definition-linkable references,
    // first value is the expected definition location,
    // second value is the line of the reference,
    // third value is the start character of the reference, and
    // fourth value is the end character of the reference (exclusive)
    let expected_definition_links = [
        (&nat, 3, 8, 11),        // recursive reference
        (&nat, 6, 9, 12),        // type of let variable
        (&nat, 6, 15, 18),       // suc inductive function call
        (&nat, 6, 23, 26),       // 0 inductive constant
        (&nat, 7, 30, 33),       // return type
        (&nat, 11, 8, 11),       // suc inductive function call
        (&nat, 22, 9, 12),       // instance Nat
        (&nat, 23, 12, 15),      // 0 inductive constant
        (&nat, 34, 20, 23),      // 0 inductive constant
        (&nat, 34, 27, 30),      // 0 inductive constant
        (&nat, 42, 32, 35),      // generic argument
        (&nat, 44, 7, 10),       // type of let satisfy variable
        (&nat, 36, 9, 12),       // type of let variable
        (&one, 9, 8, 11),        // constant expression
        (&one, 11, 16, 19),      // function parameter
        (&make_nat, 36, 15, 23), // function call
        (&has_zero, 18, 28, 35), // extends typeclass HasZero
        (&has_zero, 22, 14, 21), // instance typeclass HasZero
        (&has_zero, 25, 19, 26), // generic bound HasZero
        (&equals, 34, 13, 19),   // function call
        (&list, 40, 12, 16),     // recursive reference
        (&list, 42, 8, 12),      // cons inductive function call
        (&list, 42, 23, 27),     // nil inductive constant
    ];
    // turns the above into a hashmap that maps pairs (line, char) to expected definition location,
    // non-existing pairs are expected to not reference any definition
    let mut expected_definition_links: HashMap<(u32, u32), _> = expected_definition_links
        .into_iter()
        .flat_map(|(loc, line, start, end)| (start..end).map(move |char| ((line, char), loc)))
        .collect();

    // iterate over all cells in input file,
    // we iterate more lines than there exists and more characters than there exists in one line to
    // test those cases too
    for line in 0..=38 {
        for char in 0..=54 {
            assert_eq!(
                p.definition_location(&env, line, char),
                *expected_definition_links
                    .remove(&(line, char))
                    .unwrap_or(&None),
                "Mismatching definition location for line {} and char {}",
                line,
                char
            );
        }
    }
}

#[test]
fn test_definition_location_with_imports() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        indoc! {r"
        /// module_doc_comment
        
        /// type_doc_comment
        inductive Foo {               // line 3
            foo
        }

        /// val_doc_comment
        let bar = (Foo.foo = Foo.foo) // line 8
        "},
    );
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
        // 3456789012345678901234567890  
        from foo import Foo, bar         // line 1
        "#},
    );
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");

    let location = |file, line, start_character, end_character| Location {
        uri: Url::from_file_path(localize_mock_filename(file))
            .unwrap_or_else(|_| panic!("Failed to create URL from mock file path: {}", file)),
        range: Range {
            start: Position {
                line,
                character: start_character,
            },
            end: Position {
                line,
                character: end_character,
            },
        },
    };

    // expected locations
    let foo_location = Some(location("/mock/foo.ac", 3, 10, 13));
    let bar_location = Some(location("/mock/foo.ac", 8, 4, 7));

    // expected definition-linkable references,
    // first value is the expected definition location,
    // second value is the line of the reference,
    // third value is the start character of the reference, and
    // fourth value is the end character of the reference (exclusive)
    let expected_definition_links = [
        (&foo_location, 1, 16, 19), // type import
        (&bar_location, 1, 21, 24), // function import
    ];
    // turns the above into a hashmap that maps pairs (line, char) to expected definition location,
    // non-existing pairs are expected to not reference any definition
    let mut expected_definition_links: HashMap<(u32, u32), _> = expected_definition_links
        .into_iter()
        .flat_map(|(loc, line, start, end)| (start..end).map(move |char| ((line, char), loc)))
        .collect();

    // iterate over all cells in main file,
    // we iterate more lines than there exists and more characters than there exists in one line to
    // test those cases too
    for line in 0..=3 {
        for char in 0..=54 {
            assert_eq!(
                p.definition_location(&env, line, char),
                *expected_definition_links
                    .remove(&(line, char))
                    .unwrap_or(&None),
                "Mismatching definition location for line {} and char {}",
                line,
                char
            );
        }
    }
}

#[test]
fn test_import_default_ac() {
    let mut p = Project::new_mock();

    // Create a module in foo/default.ac
    p.mock(
        "/mock/foo/default.ac",
        r#"
        type Foo: axiom
        let foo_value: Foo = axiom
        "#,
    );

    // Import from foo should find foo/default.ac
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo, foo_value
        let x: Foo = foo_value
        "#,
    );

    p.expect_ok("main");
}

#[test]
fn test_import_from_default_ac() {
    let mut p = Project::new_mock();

    // Create a module in bar/default.ac
    p.mock(
        "/mock/bar/default.ac",
        r#"
        inductive Bar {
            bar1
            bar2
        }
        let bar_constant: Bar = Bar.bar1
        "#,
    );

    // Test various import styles
    p.mock(
        "/mock/main.ac",
        r#"
        from bar import Bar, bar_constant
        let b1: Bar = Bar.bar1
        let b2: Bar = bar_constant
        "#,
    );

    p.expect_ok("main");
}

#[test]
fn test_typeclass_attributes_across_files() {
    let mut p = Project::new_mock();
    // Define the typeclass
    p.mock(
        "/mock/addable.ac",
        r#"
        typeclass A: Addable {
            zero: A
        }
        "#,
    );
    // Add attributes to the typeclass
    p.mock(
        "/mock/addable_attrs.ac",
        r#"
        from addable import Addable

        attributes A: Addable {
            define is_zero(self) -> Bool {
                self = A.zero
            }
        }
        "#,
    );
    // Import both and use the attribute
    p.mock(
        "/mock/main.ac",
        r#"
        from addable_attrs import Addable

        inductive MyType {
            value
        }

        instance MyType: Addable {
            let zero = MyType.value
        }

        theorem test_use_attribute {
            MyType.value.is_zero
        }
        "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_import_normalization_handles_conflicting_typeclass_attribute_ids() {
    let mut p = Project::new_mock();

    p.mock(
        "/mock/thing/base.ac",
        indoc! {"
            typeclass T: Thing {
                unit: T
            }
        "},
    );

    p.mock(
        "/mock/thing/left.ac",
        indoc! {"
            from thing.base import Thing

            attributes T: Thing {
                define left(self, other: T) -> T {
                    self
                }
            }
        "},
    );

    p.mock(
        "/mock/thing/right.ac",
        indoc! {"
            from thing.base import Thing

            attributes T: Thing {
                define is_unit(self) -> Bool {
                    self = T.unit
                }
            }

            define check_unit[T: Thing](x: T) -> Bool {
                x.is_unit
            }
        "},
    );

    p.mock(
        "/mock/main.ac",
        indoc! {"
            from thing.left import Thing
            from thing.right import check_unit

            inductive Item {
                mk
            }

            instance Item: Thing {
                let unit: Item = Item.mk
            }

            define use_left(x: Item, y: Item) -> Item {
                x.left(y)
            }

            define use_is_unit(x: Item) -> Bool {
                check_unit(x)
            }

            let mixed_attribute_use: Bool = use_is_unit(use_left(Item.mk, Item.mk))
        "},
    );

    // This should load successfully: we import two different typeclass attributes and use both.
    // The original regression was in import normalization during module loading.
    p.expect_ok("main");
}

#[test]
fn test_diamond_typeclass_attribute_conflict() {
    // Similar to test_diamond_attribute_conflict but for typeclass attributes
    let mut p = Project::new_mock();
    // Define the typeclass
    p.mock(
        "/mock/addable.ac",
        r#"
        typeclass A: Addable {
            zero: A
        }
        "#,
    );
    // First module defines an attribute
    p.mock(
        "/mock/addable_attrs1.ac",
        r#"
        from addable import Addable
        
        attributes A: Addable {
            define helper(self) -> Bool {
                true
            }
        }
        "#,
    );
    // Second module defines the same attribute differently
    p.mock(
        "/mock/addable_attrs2.ac",
        r#"
        from addable import Addable
        
        attributes A: Addable {
            define helper(self) -> Bool {
                false
            }
        }
        "#,
    );
    // Main tries to import both - should fail
    p.mock(
        "/mock/main.ac",
        r#"
        import addable_attrs1
        import addable_attrs2
        "#,
    );
    p.expect_ok("addable_attrs1");
    p.expect_ok("addable_attrs2");
    p.expect_module_err("main");
}

#[test]
fn test_deep_required_attribute_lookup() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/semigroup.ac",
        r#"
        typeclass S: Semigroup {
            // The semigroup operation
            mul: (S, S) -> S
        }
        "#,
    );
    p.mock(
        "/mock/group.ac",
        r#"
        from semigroup import Semigroup
        typeclass G: Group extends Semigroup {
            item: G
        }
        "#,
    );
    p.mock(
        "/mock/subgroup.ac",
        r#"
        from group import Group

        define closure_constraint[G: Group](contains: G -> Bool) -> Bool {
            forall(a: G, b: G) {
                contains(a) and contains(b) implies contains(a * b)
            }
        }
        "#,
    );
    p.expect_ok("subgroup");
}

#[test]
fn test_deep_lib() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo/bar.ac",
        r#"
        let baz: Bool = false
    "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo.bar import baz

        theorem goal {
            baz = lib(foo.bar).baz
        }
        "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_complex_attribute_reference() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/base.ac",
        r#"
        structure Set[T] {
            contains: T -> Bool
        }

        inductive Real {
            zero
            one
        }

        attributes Real {
            define lte(self, other: Real) -> Bool {
                self != Real.one or other != Real.zero
            }
        }


        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from base import Set, Real

        attributes Set[Real] {
            define is_upper_bound(self, b: Real) -> Bool {
                forall(x: Real) {
                    self.contains(x) implies x <= b
                }        
            }

            define has_upper_bound(self) -> Bool {
                exists(b: Real) {
                    self.is_upper_bound(b)
                }
            }
        }
        "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_hover_method_call() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
    inductive Foo {
        foo
    }

    attributes Foo {
        /// bar_doc_comment
        define bar(self, x: Bool) -> Bool {
            x
        }
    }

    let foo_instance: Foo = Foo.foo
    let result = foo_instance.bar(true)             // line 12
    // 34567890123456789012345678901234567890
    "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");

    // Test hovering over the method name in method call
    // Line 11: let result = foo_instance.bar(true)
    //                                    ^^^
    // Hovering over "bar" at columns 26-28

    let method_hover = p.hover(&env, 12, 27); // over "bar"
    assert!(
        method_hover.is_some(),
        "should be able to hover over method name"
    );

    let hover_str = format!("{:?}", method_hover.unwrap());
    println!("Method hover result: {}", hover_str);

    // After the fix, hover should show the general method definition "Foo.bar"
    // instead of the partial application "Foo.foo.bar"
    assert!(
        hover_str.contains("Foo.bar"),
        "Hover should show general method definition"
    );
    assert!(
        !hover_str.contains("Foo.foo.bar"),
        "Hover should NOT show method bound to instance"
    );
    assert!(
        hover_str.contains("bar_doc_comment"),
        "Hover should include the doc comment for the method"
    );
}

#[test]
fn test_hover_typeclass_method_with_doc_comment() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
    typeclass T: Thing {
        thing: T
    }
    
    attributes T: Thing {
        /// do_something_doc_comment
        define do_something(self) -> Bool {
            self = T.thing
        }
    }
    
    inductive Foo {
        foo
    }
    
    instance Foo: Thing {
        let thing = Foo.foo
    }
    
    let foo_instance: Foo = Foo.foo
    let result = foo_instance.do_something              // line 20
    // 34567890123456789012345678901234567890

    theorem goal[T: Thing](t: T) {
        t.do_something
    }
    "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");

    // Test hovering over the typeclass method name in method call
    let method_hover = p.hover(&env, 20, 30); // over "do_something"
    assert!(
        method_hover.is_some(),
        "should be able to hover over typeclass method name"
    );

    let hover_str = format!("{:?}", method_hover.unwrap());
    println!("Typeclass method hover result: {}", hover_str);

    assert!(
        hover_str.contains("Foo.do_something"),
        "Hover should show the instantiated method"
    );
    assert!(
        hover_str.contains("do_something_doc_comment"),
        "Hover should include the doc comment for the typeclass method"
    );

    // Test hovering over the typeclass method in a generic context
    // Line 24: t.do_something
    let generic_method_hover = p.hover(&env, 24, 10); // over "do_something" in t.do_something
    assert!(
        generic_method_hover.is_some(),
        "should be able to hover over typeclass method in generic context"
    );

    let generic_hover_str = format!("{:?}", generic_method_hover.unwrap());
    println!(
        "Generic typeclass method hover result: {}",
        generic_hover_str
    );

    assert!(
        generic_hover_str.contains("T.do_something"),
        "Hover should show the typeclass method with type parameter"
    );
    assert!(
        generic_hover_str.contains("do_something_doc_comment"),
        "Hover should include the doc comment for the typeclass method in generic context"
    );
}

#[test]
fn test_hover_preserves_explicit_type_args_on_partial_application() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        indoc! {r#"
    define constant[T, U](u: U, t: T) -> U {
        u
    }

    define uses_constant[T, U](u: U, t: T) -> U {
        constant[T, U](u, t)                           // line 6
    }
    // 345678901234567890123456789012345678901234567890
    "#},
    );
    p.expect_ok("main");
    let desc = ModuleDescriptor::name("main");
    let env = p.get_env(&desc).expect("no env for main");

    let hover = p.hover(&env, 5, 6).expect("hover on constant should exist");
    let HoverContents::Array(parts) = hover.contents else {
        panic!("expected array hover contents");
    };
    let first = match &parts[0] {
        MarkedString::LanguageString(s) => s.value.clone(),
        MarkedString::String(s) => s.clone(),
    };
    assert!(
        first.contains("constant["),
        "hover should preserve explicit type arguments, got: {}",
        first
    );
}

#[test]
fn test_doc_comment_lookup() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
    /// Foo_doc_comment
    inductive Foo {
        /// foo_doc_comment
        foo
    }
    "#,
    );

    p.mock(
        "/mock/bar.ac",
        r#"
    from foo import Foo

    attributes Foo {
        /// bar_doc_comment
        define bar(self, x: Bool) -> Bool {
            x
        }
    }

    /// Baz_doc_comment
    structure Baz {
        /// baz_doc_comment
        baz: Bool
    }

    /// Qux_doc_comment
    typeclass Q: Qux {
        /// qux_doc_comment
        qux: Q

        /// quux_doc_comment
        quux {
            true
        }
    }
    "#,
    );

    p.mock(
        "/mock/main.ac",
        r#"
    from bar import Foo, Baz, Qux
    "#,
    );

    p.expect_ok("foo");
    p.expect_ok("bar");
    p.expect_ok("main");

    // Get the main environment
    let main_descriptor = crate::module::ModuleDescriptor::name("main");
    let main_env = p.get_env(&main_descriptor).unwrap();

    // Check Foo
    let foo_potential_type = main_env.bindings.get_type_for_typename("Foo").unwrap();
    let foo_datatype = foo_potential_type.as_base_datatype().unwrap();
    let comments = p.get_datatype_doc_comments(&foo_datatype);
    assert_eq!(comments.unwrap(), &vec!["Foo_doc_comment".to_string()]);

    // Check Foo.bar
    let bar_module = main_env
        .bindings
        .get_datatype_attribute_module(&foo_datatype, "bar")
        .expect("Foo.bar module");
    let bar_constant_name = ConstantName::datatype_attr(bar_module, foo_datatype.clone(), "bar");
    let comments = p.get_constant_doc_comments(main_env, &bar_constant_name);
    assert_eq!(comments.unwrap(), &vec!["bar_doc_comment".to_string()]);

    // Check Foo.foo
    let foo_module = main_env
        .bindings
        .get_datatype_attribute_module(&foo_datatype, "foo")
        .expect("Foo.foo module");
    let foo_constant_name = ConstantName::datatype_attr(foo_module, foo_datatype.clone(), "foo");
    let comments = p.get_constant_doc_comments(main_env, &foo_constant_name);
    assert_eq!(comments.unwrap(), &vec!["foo_doc_comment".to_string()]);

    // Check Baz
    let baz_potential_type = main_env.bindings.get_type_for_typename("Baz").unwrap();
    let baz_datatype = baz_potential_type.as_base_datatype().unwrap();
    let comments = p.get_datatype_doc_comments(&baz_datatype);
    assert_eq!(comments.unwrap(), &vec!["Baz_doc_comment".to_string()]);

    // Check Baz.baz
    let baz_module = main_env
        .bindings
        .get_datatype_attribute_module(&baz_datatype, "baz")
        .expect("Baz.baz module");
    let baz_constant_name = ConstantName::datatype_attr(baz_module, baz_datatype.clone(), "baz");
    let comments = p.get_constant_doc_comments(main_env, &baz_constant_name);
    assert_eq!(comments.unwrap(), &vec!["baz_doc_comment".to_string()]);

    // Check Qux typeclass
    let qux_typeclass = main_env.bindings.get_typeclass_for_name("Qux").unwrap();
    let comments = p.get_typeclass_doc_comments(&qux_typeclass);
    assert_eq!(comments.unwrap(), &vec!["Qux_doc_comment".to_string()]);

    // Check Qux.qux
    let qux_constant_name =
        ConstantName::typeclass_attr(qux_typeclass.module_id, qux_typeclass.clone(), "qux");
    let comments = p.get_constant_doc_comments(main_env, &qux_constant_name);
    assert_eq!(comments.unwrap(), &vec!["qux_doc_comment".to_string()]);

    // Check Qux.quux
    let quux_constant_name =
        ConstantName::typeclass_attr(qux_typeclass.module_id, qux_typeclass.clone(), "quux");
    let comments = p.get_constant_doc_comments(main_env, &quux_constant_name);
    assert_eq!(comments.unwrap(), &vec!["quux_doc_comment".to_string()]);
}

#[test]
fn test_handle_selection_typeclass_attribute() {
    use std::fs;
    use tempfile::TempDir;

    // Create a temp directory for our test
    let temp_dir = TempDir::new().unwrap();
    let src_dir = temp_dir.path().join("src");
    let build_dir = temp_dir.path().join("build");
    fs::create_dir(&src_dir).unwrap();
    fs::create_dir(&build_dir).unwrap();

    // Create test file
    let test_file = src_dir.join("test.ac");
    let content = indoc! {r#"
        type Nat: axiom

        typeclass T: Thing {
            condition {
                true
            }
        }

        instance Nat: Thing

        attributes T: Thing {
            let foo: T -> Bool = axiom
        }

        axiom foo_general[T: Thing](x: T) {
            x.foo
        }

        theorem foo_specific(x: Nat) {
            x.foo
        }
    "#};
    fs::write(&test_file, content).unwrap();

    // Create project and build
    let mut p = Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default()).unwrap();
    p.add_target_by_path(&test_file).unwrap();
    expect_build_ok(&mut p);

    // Handle selection on the foo_specific theorem line (line 18)
    let result = p.handle_selection(&test_file, 18);

    assert!(
        result.is_ok(),
        "handle_selection should succeed: {:?}",
        result.err()
    );
    let (goal_infos, goal_range) = match result.unwrap() {
        SelectionInfo::Goals {
            goal_infos,
            goal_range,
        } => (goal_infos, goal_range),
        SelectionInfo::Citation(_) => panic!("expected goal selection"),
    };

    // Verify we got exactly one goal
    assert_eq!(goal_infos.len(), 1, "Expected exactly one goal");
    let goal_info = &goal_infos[0];

    // Verify we got the right goal
    assert_eq!(goal_info.goal_name, "foo_specific".to_string());
    assert!(goal_range.is_some());

    // Verify we got steps
    assert!(
        goal_info.steps.is_some(),
        "Expected proof steps to be returned"
    );
    let steps = goal_info.steps.as_ref().unwrap();

    // Find the step with the proof
    assert!(!steps.is_empty(), "Expected at least one step");

    for step in steps {
        println!("Step: {}, Reason: {}", step.statement, step.reason);
    }

    // The main step should contain "x.foo" in the statement
    let main_step = steps
        .iter()
        .find(|s| s.statement.contains("x.foo"))
        .expect("Expected to find a step containing 'x.foo'");

    assert!(
        main_step.reason.contains("foo_general"),
        "Reason should refer to 'foo_general', not 'foo_specific'. Got: {}",
        main_step.reason
    );
}

#[test]
fn test_handle_selection_citation_returns_expansion() {
    let temp = tempfile::tempdir().unwrap();
    let src_dir = temp.path().join("src");
    let build_dir = temp.path().join("build");
    std::fs::create_dir_all(&src_dir).unwrap();
    std::fs::create_dir_all(&build_dir).unwrap();

    let test_file = src_dir.join("main.ac");
    let content = indoc! {r#"
        type Nat: axiom

        let foo: Nat -> Bool = axiom
        let bar: Nat -> Bool = axiom
        let baz: Nat -> Bool = axiom
        let a: Nat = axiom

        axiom base_helper(x: Nat) {
            foo(x) and bar(x) implies baz(x)
        }

        theorem helper(x: Nat) {
            foo(x) and bar(x) implies baz(x)
        } by {
            if foo(x) and bar(x) {
                base_helper(x)
                baz(x)
            }
        }

        theorem goal {
            foo(a) and bar(a) implies baz(a)
        } by {
            if foo(a) and bar(a) {
                helper(a)
                baz(a)
            }
        }
    "#};
    std::fs::write(&test_file, content).unwrap();

    let mut project =
        Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default()).unwrap();
    project.add_target_by_path(&test_file).unwrap();
    expect_build_ok(&mut project);

    let selection = project
        .handle_selection(&test_file, 24)
        .expect("citation selection should succeed");
    let citation = match selection {
        SelectionInfo::Citation(citation) => citation,
        SelectionInfo::Goals { .. } => panic!("expected citation selection"),
    };

    assert_eq!(citation.selection_text, "helper(a)");
    assert_eq!(citation.theorem_name.as_deref(), Some("helper"));
    assert!(citation.theorem_location.is_some());
    assert!(
        citation.expansion.contains("foo(a)")
            && citation.expansion.contains("bar(a)")
            && citation.expansion.contains("baz(a)"),
        "expected instantiated normalized expansion, got {}",
        citation.expansion
    );
}
