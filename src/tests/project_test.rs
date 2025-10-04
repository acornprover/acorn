use std::path::PathBuf;

use tokio_util::sync::CancellationToken;

use crate::builder::{BuildEvent, BuildStatus, Builder};
use crate::environment::LineType;
use crate::module::ModuleDescriptor;
use crate::names::ConstantName;
use crate::project::{Project, ProjectConfig};
use indoc::indoc;

fn expect_build_ok(project: &Project) -> i32 {
    let mut events: Vec<BuildEvent> = vec![];
    let (status, searches_success) = {
        let mut builder = Builder::new(&project, CancellationToken::new(), |event| {
            events.push(event)
        });
        builder.build();
        (builder.status, builder.metrics.searches_success)
    };
    assert_eq!(status, BuildStatus::Good);
    assert!(events.len() > 0);
    let (done, total) = events.last().unwrap().progress.unwrap();
    assert_eq!(done, total, "expected number of build events didn't match");
    searches_success
}

const FOO_AC: &str = r#"
// Imported by other tests
type Foo: axiom
type AlsoFoo: Foo
type NotFoo: axiom
let foo: Foo = axiom
define fooify(x: Foo) -> Foo { foo }
"#;

#[test]
fn test_update_file_first_call_drops_modules() {
    use std::fs;
    use tempfile::TempDir;

    // Create a temp directory for our test
    let temp_dir = TempDir::new().unwrap();
    let src_dir = temp_dir.path().join("src");
    let build_dir = temp_dir.path().join("build");
    fs::create_dir(&src_dir).unwrap();
    fs::create_dir(&build_dir).unwrap();

    // Create initial file on disk
    let test_file = src_dir.join("test.ac");
    let initial_content = "type Nat: axiom\nlet zero: Nat = axiom";
    fs::write(&test_file, initial_content).unwrap();

    // Step 1: Create first project and build to get baseline
    let mut p1 = Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default());
    p1.add_target_by_path(&test_file).unwrap();
    let initial_searches = expect_build_ok(&p1);

    // Step 2: Create a fresh project (simulating server restart)
    // The file exists on disk with the initial content
    let mut p2 = Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default());

    // Load and build once - this caches the module from disk
    p2.add_target_by_path(&test_file).unwrap();
    expect_build_ok(&p2);

    // Step 3: Now call update_file with new content that adds a theorem
    // This simulates VS Code opening the file and making the first edit+save
    let content_with_theorem =
        "type Nat: axiom\nlet zero: Nat = axiom\n\ntheorem test_theorem { true }";

    // This is the FIRST update_file call for this path
    // The bug: it won't drop modules because the file isn't in open_files yet
    p2.update_file(test_file.clone(), content_with_theorem, 1)
        .expect("update should succeed");

    // Step 4: Build and check that the theorem was actually processed
    let searches_after_update = expect_build_ok(&p2);

    // The bug would manifest as: searches don't increase because the theorem wasn't picked up
    assert!(
        searches_after_update > initial_searches,
        "BUG: First update_file didn't invalidate cache. Initial searches: {}, after update: {}",
        initial_searches,
        searches_after_update
    );
}

#[test]
fn test_basic_import() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock("/mock/main.ac", "import foo");
    p.expect_ok("main");
}

#[test]
fn test_direct_import_nonexistent() {
    let mut p = Project::new_mock();
    p.expect_load_err("main");
}

#[test]
fn test_indirect_import_nonexistent() {
    let mut p = Project::new_mock();
    p.mock("/mock/main.ac", "import nonexistent");
    p.expect_module_err("main");
}

#[test]
fn test_nonexistent_property() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let bar: foo.nonexistent = axiom
    "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_circular_imports() {
    let mut p = Project::new_mock();
    p.mock("/mock/a.ac", "import b");
    p.mock("/mock/b.ac", "import c");
    p.mock("/mock/c.ac", "import a");
    p.expect_module_err("a");
    // The error should show up in c.ac, not in a.ac
    assert!(p.errors().len() > 0);
}

#[test]
fn test_self_import() {
    let mut p = Project::new_mock();
    p.mock("/mock/a.ac", "import a");
    p.expect_module_err("a");
}

#[test]
fn test_import_from_subdir() {
    let mut p = Project::new_mock();
    p.mock("/mock/stuff/foo.ac", FOO_AC);
    p.mock("/mock/main.ac", "import stuff.foo");
    p.expect_ok("main");
}

#[test]
fn test_good_imported_types() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        type MyFoo: foo.AlsoFoo
        let x: foo.Foo = axiom
        let y: MyFoo = axiom
        let z: Bool = (x = y)
    "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_bad_imported_types() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        type MyFoo: foo.NotFoo
        let x: foo.Foo = axiom
        let y: MyFoo = axiom
        let z: Bool = (x = y)
    "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_imported_constants() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let x: foo.Foo = axiom
        let y: foo.Foo = foo.foo
        let z: Bool = (x = y)
    "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_building_project() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        import foo
        let new_foo: foo.Foo = axiom
        theorem goal { foo.fooify(new_foo) = foo.foo }
    "#,
    );
    p.load_module_by_name("foo").expect("loading foo failed");
    p.load_module_by_name("main").expect("loading main failed");
    p.add_target_by_name("foo")
        .expect("adding foo target failed");
    p.add_target_by_name("main")
        .expect("adding main target failed");
    expect_build_ok(&p);
}

#[test]
fn test_target_outside_library() {
    let mut p = Project::new_mock();
    let outside_path = "/outside/foo.ac";
    p.mock(outside_path, FOO_AC);
    p.add_target_by_path(&PathBuf::from(outside_path))
        .expect("adding outside target failed");
    expect_build_ok(&p);
}

#[test]
fn test_completions() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/nat.ac",
        r#"
        inductive Nat {
            0
            suc(Nat)
        }

        theorem ugly {
            true = true
        }
        "#,
    );
    let main = PathBuf::from("/mock/main.ac");
    p.mock(
        main.to_str().unwrap(),
        r#"
        from nat import Nat
        let foo: Nat = axiom
        let bar: Nat = axiom
        theorem goal(bop: Nat) {
            bop != foo or bop != bar or foo = bar
        } by {
            // This should be line 7. Let's test completions here.
        }
        "#,
    );
    let env = p.get_env(&ModuleDescriptor::name("main")).unwrap();

    // Make sure the indexes are what we expect
    assert_eq!(env.get_line_type(0), Some(LineType::Empty));
    assert_eq!(env.get_line_type(1), Some(LineType::Other));
    assert_eq!(env.get_line_type(2), Some(LineType::Other));
    assert_eq!(env.get_line_type(3), Some(LineType::Other));
    assert_eq!(env.get_line_type(4), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(5), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(6), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(7), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(8), Some(LineType::Node(0)));
    assert_eq!(env.get_line_type(9), None);

    let check = |prefix: &str, line: u32, expected: &[&str]| {
        let completions = match p.get_completions(Some(&main), line, prefix) {
            Some(c) => c,
            None => {
                assert!(expected.is_empty(), "no completions found for '{}'", prefix);
                return;
            }
        };
        let labels: Vec<_> = completions.iter().map(|c| &c.label).collect();
        assert_eq!(labels, expected, "completions for '{}'", prefix);
    };

    // Test completions
    check("from nat import N", 0, &["Nat"]);
    check("ba", 7, &["bar"]);
    check("fo", 7, &["forall", "foo"]);
    check("b", 7, &["by", "bar", "bop"]);
    check("Nat.s", 7, &["suc"]);
    check("foo.s", 7, &["suc"]);
    check("nat.N", 7, &["Nat"]);
    check("(ba", 7, &["bar"]);
    check("nat.u", 7, &[]);
    check("nat.", 7, &["Nat"]);
    check("foo.", 7, &["0", "induction", "suc"]);
}

#[test]
fn test_build_cache() {
    let mut p = Project::new_mock();
    let foo_text = r#"
    let thing1: Bool = axiom
    let thing2: Bool = thing1

    theorem one {
        thing1 = thing2
    }
    "#;
    let main_text = r#"
    import foo
    theorem two {
        foo.thing1 = foo.thing2
    }
    "#;
    p.mock("/mock/foo.ac", foo_text);
    p.mock("/mock/main.ac", main_text);
    let num_success = expect_build_ok(&p);
    assert_eq!(num_success, 2);

    // Just rebuilding a second time - with mock projects using certificates,
    // caching doesn't work the same way since read_cache/write_cache are false
    let num_success = expect_build_ok(&p);
    // Mock projects don't cache, so everything gets re-proven
    assert_eq!(num_success, 2);

    // If we change main, we rebuild both modules
    let touched_main = format!("// Touch\n{}", main_text);
    p.update_file(PathBuf::from("/mock/main.ac"), &touched_main, 1)
        .expect("update failed");
    let num_success = expect_build_ok(&p);
    assert_eq!(num_success, 2);

    // If we change foo, we should have to rebuild both
    let touched_foo = format!("// Touch\n{}", foo_text);
    p.update_file(PathBuf::from("/mock/foo.ac"), &touched_foo, 1)
        .expect("update failed");
    let num_success = expect_build_ok(&p);
    assert_eq!(num_success, 2);
}

#[test]
fn test_build_cache_partial_rebuild() {
    let mut p = Project::new_mock();
    let mut lines = vec![
        "theorem one {",
        "    true = true",
        "}",
        "theorem two {",
        "    true = true",
        "}",
        "theorem three {",
        "    true = true",
        "}",
    ];
    let filename = "/mock/main.ac";
    p.mock(filename, &lines.join("\n"));
    let num_success = expect_build_ok(&p);
    assert_eq!(num_success, 3);

    // Change the middle theorem
    lines[4] = "    false = false";
    p.update_file(PathBuf::from(filename), &lines.join("\n"), 1)
        .expect("update failed");
    let num_success = expect_build_ok(&p);
    // With certificates, all theorems in the module are re-proven when any part changes
    assert_eq!(num_success, 3);
}

#[test]
fn test_module_name_forbidden_as_function_arg() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        let foobool: Bool = true
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import foo

        let bar: Bool -> Bool = function(foo: Bool) {
            true
        }
        "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_module_name_forbidden_as_define_arg() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        let foobool: Bool = true
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import foo

        define bar(foo: Bool) -> Bool {
            true
        }
        "#,
    );
    p.expect_module_err("main");
}

#[test]
fn test_instance_of_imported_typeclass() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/semigroup.ac",
        r#"
        typeclass S: Semigroup {
            // Semigroups have a binary operation
            mul: (S, S) -> S

            // The operation must be associative
            associative(x: S, y: S, z: S) {
                (x * y) * z = x * (y * z)
            }
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from semigroup import Semigroup

        inductive Foo {
            foo
        }

        attributes Foo {
            define mul(self, f: Foo) -> Foo {
                Foo.foo
            }
        }

        instance Foo: Semigroup {
            let mul: (Foo, Foo) -> Foo = Foo.mul
        }
        "#,
    );
    p.expect_ok("semigroup");
    p.expect_ok("main");
}

#[test]
fn test_indirect_importing() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }

        attributes Foo {
            let a: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let b: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from bar import Foo

        let a: Bool = Foo.a
        let b: Bool = Foo.b
        "#,
    );
    p.expect_ok("bar");
    p.expect_ok("main");
}

#[test]
fn test_importing_let_attr_conflict() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }

        attributes Foo {
            let a: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let a: Bool = false
        }
        "#,
    );
    p.expect_ok("foo");
    p.expect_module_err("main");
}

#[test]
fn test_importing_define_attr_conflict() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }

        attributes Foo {
            define a(self) -> Bool { true }
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo

        attributes Foo {
            define a(self) -> Bool { true }
        }
        "#,
    );
    p.expect_ok("foo");
    p.expect_module_err("main");
}

#[test]
fn test_diamond_attribute_conflict() {
    // bar and baz are both all right on their own, but they conflict with each other.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let a: Bool = false
        }
        "#,
    );
    p.mock(
        "/mock/baz.ac",
        r#"
        from foo import Foo

        attributes Foo {
            let a: Bool = true
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import bar
        import baz
        "#,
    );
    p.expect_ok("bar");
    p.expect_ok("baz");
    p.expect_module_err("main");
}

#[test]
fn test_instance_separate_from_class_and_typeclass() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }
        "#,
    );
    p.mock(
        "/mock/pointed.ac",
        r#"
        typeclass P: Pointed {
            origin: P
        }
        "#,
    );
    p.mock(
        "/mock/relate.ac",
        r#"
        from foo import Foo
        from pointed import Pointed

        instance Foo: Pointed {
            let origin: Foo = Foo.foo
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo
        from pointed import Pointed
        import relate

        define get_point[P: Pointed](p: P) -> P {
            P.origin
        }

        let p: Foo = get_point(Foo.foo)
        "#,
    );
    p.expect_ok("relate");
    p.expect_ok("main");
}

#[test]
fn test_diamond_instance_conflict() {
    // bar and baz are both all right on their own, but they conflict with each other.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        typeclass P: Pointed {
            origin: P
        }

        inductive Foo {
            foo1
            foo2
        }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo, Pointed

        instance Foo: Pointed {
            let origin: Foo = Foo.foo1
        }
        "#,
    );
    p.mock(
        "/mock/baz.ac",
        r#"
        from foo import Foo, Pointed

        instance Foo: Pointed {
            let origin: Foo = Foo.foo2
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        import bar
        import baz
        "#,
    );
    p.expect_ok("bar");
    p.expect_ok("baz");
    p.expect_module_err("main");
}

#[test]
fn test_mixed_in_attribute() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo

        attributes Foo {
            define a(self) -> Bool { true }
        }

        theorem goal {
            Foo.foo.a
        }
        "#,
    );
    p.expect_ok("foo");
    p.expect_ok("main");
}

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
        import foo
        let x: foo.Foo = foo.foo_value
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
        from addable import Addable
        import addable_attrs
        
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
    let bar_constant_name = ConstantName::datatype_attr(foo_datatype.clone(), "bar");
    let comments = p.get_constant_doc_comments(main_env, &bar_constant_name);
    assert_eq!(comments.unwrap(), &vec!["bar_doc_comment".to_string()]);

    // Check Foo.foo
    let foo_constant_name = ConstantName::datatype_attr(foo_datatype.clone(), "foo");
    let comments = p.get_constant_doc_comments(main_env, &foo_constant_name);
    assert_eq!(comments.unwrap(), &vec!["foo_doc_comment".to_string()]);

    // Check Baz
    let baz_potential_type = main_env.bindings.get_type_for_typename("Baz").unwrap();
    let baz_datatype = baz_potential_type.as_base_datatype().unwrap();
    let comments = p.get_datatype_doc_comments(&baz_datatype);
    assert_eq!(comments.unwrap(), &vec!["Baz_doc_comment".to_string()]);

    // Check Baz.baz
    let baz_constant_name = ConstantName::datatype_attr(baz_datatype.clone(), "baz");
    let comments = p.get_constant_doc_comments(main_env, &baz_constant_name);
    assert_eq!(comments.unwrap(), &vec!["baz_doc_comment".to_string()]);

    // Check Qux typeclass
    let qux_typeclass = main_env.bindings.get_typeclass_for_name("Qux").unwrap();
    let comments = p.get_typeclass_doc_comments(&qux_typeclass);
    assert_eq!(comments.unwrap(), &vec!["Qux_doc_comment".to_string()]);

    // Check Qux.qux
    let qux_constant_name = ConstantName::typeclass_attr(qux_typeclass.clone(), "qux");
    let comments = p.get_constant_doc_comments(main_env, &qux_constant_name);
    assert_eq!(comments.unwrap(), &vec!["qux_doc_comment".to_string()]);

    // Check Qux.quux
    let quux_constant_name = ConstantName::typeclass_attr(qux_typeclass.clone(), "quux");
    let comments = p.get_constant_doc_comments(main_env, &quux_constant_name);
    assert_eq!(comments.unwrap(), &vec!["quux_doc_comment".to_string()]);
}
