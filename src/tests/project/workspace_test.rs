use std::path::PathBuf;

use tokio_util::sync::CancellationToken;

use crate::builder::{BuildStatus, Builder};
use crate::elaborator::environment::LineType;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::project::{localize_mock_filename, LibraryCitation, Project, ProjectConfig};
use indoc::indoc;

use super::support::{expect_build_ok, FOO_AC};

// Multi-file project and workspace behavior.

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
    let mut p1 =
        Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default()).unwrap();
    p1.add_target_by_path(&test_file).unwrap();
    let initial_searches = expect_build_ok(&mut p1);

    // Step 2: Create a fresh project (simulating server restart)
    // The file exists on disk with the initial content
    let mut p2 =
        Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default()).unwrap();

    // Load and build once - this caches the module from disk
    p2.add_target_by_path(&test_file).unwrap();
    expect_build_ok(&mut p2);

    // Step 3: Now call update_file with new content that adds a theorem
    // This simulates VS Code opening the file and making the first edit+save
    let content_with_theorem =
        "type Nat: axiom\nlet zero: Nat = axiom\n\ntheorem test_theorem { true }";

    // This is the FIRST update_file call for this path
    // The bug: it won't drop modules because the file isn't in open_files yet
    p2.update_file(test_file.clone(), content_with_theorem, 1)
        .expect("update should succeed");

    // Step 4: Build and check that the theorem was actually processed
    let searches_after_update = expect_build_ok(&mut p2);

    // The bug would manifest as: searches don't increase because the theorem wasn't picked up
    assert!(
        searches_after_update > initial_searches,
        "BUG: First update_file didn't invalidate cache. Initial searches: {}, after update: {}",
        initial_searches,
        searches_after_update
    );
}

#[test]
fn test_update_file_preserves_module_ids() {
    use std::fs;
    use tempfile::TempDir;

    let temp_dir = TempDir::new().unwrap();
    let src_dir = temp_dir.path().join("src");
    let build_dir = temp_dir.path().join("build");
    fs::create_dir(&src_dir).unwrap();
    fs::create_dir(&build_dir).unwrap();

    fs::write(
        src_dir.join("prelude.ac"),
        "let prelude_true: Bool = true\n",
    )
    .unwrap();
    fs::write(src_dir.join("a.ac"), "theorem a_goal { true }\n").unwrap();
    fs::write(src_dir.join("z.ac"), "theorem z_goal { true }\n").unwrap();
    let main_file = src_dir.join("main.ac");
    let main_content = "import z\nimport a\n\ntheorem main_goal { true }\n";
    fs::write(&main_file, main_content).unwrap();

    let mut p = Project::new(src_dir.clone(), build_dir.clone(), ProjectConfig::default()).unwrap();
    p.add_target_by_path(&main_file).unwrap();

    let initial_ids = (
        p.get_module_id_by_name("prelude").unwrap(),
        p.get_module_id_by_name("a").unwrap(),
        p.get_module_id_by_name("main").unwrap(),
        p.get_module_id_by_name("z").unwrap(),
    );
    assert_eq!(
        initial_ids,
        (ModuleId::PRELUDE, ModuleId(1), ModuleId(2), ModuleId(3))
    );

    let touched_main = format!("// touch\n{}", main_content);
    p.update_file(main_file, &touched_main, 1)
        .expect("update should succeed");

    let updated_ids = (
        p.get_module_id_by_name("prelude").unwrap(),
        p.get_module_id_by_name("a").unwrap(),
        p.get_module_id_by_name("main").unwrap(),
        p.get_module_id_by_name("z").unwrap(),
    );
    assert_eq!(updated_ids, initial_ids);
}

#[test]
fn test_basic_import() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock("/mock/main.ac", "from foo import Foo");
    p.expect_ok("main");
}

#[test]
fn test_citation_statements_collect_nested_citations() {
    let mut p = Project::new_mock();
    p.mock("/mock/base.ac", "theorem helper { true }\n");
    p.mock(
        "/mock/main.ac",
        indoc! {"
            from base import helper

            theorem top_level {
                helper
            }

            theorem outer {
                true
            } by {
                helper
            }
        "},
    );
    p.expect_ok("main");

    assert_eq!(
        p.citation_statements(),
        vec![
            LibraryCitation {
                path: "main.ac".to_string(),
                line: 3,
                text: "theorem top_level { helper }".to_string(),
            },
            LibraryCitation {
                path: "main.ac".to_string(),
                line: 10,
                text: "helper".to_string(),
            },
        ]
    );
}

#[test]
fn test_from_import_does_not_bind_module_name() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo
        let foo: Bool = true
    "#,
    );
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
    p.mock("/mock/main.ac", "from stuff.foo import Foo");
    p.expect_ok("main");
}

#[test]
fn test_good_imported_types() {
    let mut p = Project::new_mock();
    p.mock("/mock/foo.ac", FOO_AC);
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Foo, AlsoFoo
        type MyFoo: AlsoFoo
        let x: Foo = axiom
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
        from foo import Foo
        let x: Foo = axiom
        let y: Foo = lib(foo).foo
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
        from foo import Foo, fooify
        let new_foo: Foo = axiom
        theorem goal { fooify(new_foo) = lib(foo).foo }
    "#,
    );
    p.load_module_by_name("foo").expect("loading foo failed");
    p.load_module_by_name("main").expect("loading main failed");
    p.add_target_by_name("foo")
        .expect("adding foo target failed");
    p.add_target_by_name("main")
        .expect("adding main target failed");
    expect_build_ok(&mut p);
}

#[test]
fn test_filesystem_project_supports_global_lib_module_lookup() {
    use std::fs;
    use tempfile::TempDir;

    let temp_dir = TempDir::new().unwrap();
    let src_dir = temp_dir.path().join("src");
    let build_dir = temp_dir.path().join("build");
    fs::create_dir(&src_dir).unwrap();
    fs::create_dir(&build_dir).unwrap();
    fs::write(temp_dir.path().join("acorn.toml"), "").unwrap();

    fs::write(
        src_dir.join("util.ac"),
        indoc! {r#"
            type Foo: axiom
            let foo: Foo = axiom
        "#},
    )
    .unwrap();
    fs::write(
        src_dir.join("main.ac"),
        indoc! {r#"
            theorem goal {
                lib(util).foo = lib(util).foo
            }
        "#},
    )
    .unwrap();

    let mut p = Project::new(src_dir, build_dir, ProjectConfig::default()).unwrap();
    p.expect_ok("main");
    let main_id = p.get_module_id_by_name("main").unwrap();
    let util_id = p.get_module_id_by_name("util").unwrap();
    assert!(
        p.all_dependencies(main_id).contains(&util_id),
        "lib(util) should register util as a source dependency",
    );
    p.add_target_by_name("main").unwrap();
    expect_build_ok(&mut p);
}

#[test]
fn test_target_outside_library() {
    let mut p = Project::new_mock();
    let outside_path = "/outside/foo.ac";
    p.mock(outside_path, FOO_AC);
    p.add_target_by_path(&PathBuf::from(localize_mock_filename(outside_path)))
        .expect("adding outside target failed");
    expect_build_ok(&mut p);
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
    let main = PathBuf::from(localize_mock_filename("/mock/main.ac"));
    p.mock(
        "/mock/main.ac",
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
    // Let statements (including axiom constants) now create nodes with proper line types
    assert_eq!(env.get_line_type(0), Some(LineType::Empty));
    assert_eq!(env.get_line_type(1), Some(LineType::Other)); // import
    assert_eq!(env.get_line_type(2), Some(LineType::Node(0))); // foo axiom
    assert_eq!(env.get_line_type(3), Some(LineType::Node(1))); // bar axiom
    assert_eq!(env.get_line_type(4), Some(LineType::Node(2))); // theorem goal
    assert_eq!(env.get_line_type(5), Some(LineType::Node(2)));
    assert_eq!(env.get_line_type(6), Some(LineType::Node(2)));
    assert_eq!(env.get_line_type(7), Some(LineType::Node(2)));
    assert_eq!(env.get_line_type(8), Some(LineType::Node(2)));
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
    check("(ba", 7, &["bar"]);
    check("foo.", 7, &["0", "induction", "match", "suc"]);
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
    from foo import thing1, thing2
    theorem two {
        thing1 = thing2
    }
    "#;
    p.mock("/mock/foo.ac", foo_text);
    p.mock("/mock/main.ac", main_text);
    let num_success = expect_build_ok(&mut p);
    assert_eq!(num_success, 2);

    // Just rebuilding a second time - with mock projects using certificates,
    // caching doesn't work the same way since read_cache/write_cache are false
    let num_success = expect_build_ok(&mut p);
    // Mock projects don't cache, so everything gets re-proven
    assert_eq!(num_success, 2);

    // If we change main, we rebuild both modules
    let touched_main = format!("// Touch\n{}", main_text);
    p.update_file(
        PathBuf::from(localize_mock_filename("/mock/main.ac")),
        &touched_main,
        1,
    )
    .expect("update failed");
    let num_success = expect_build_ok(&mut p);
    assert_eq!(num_success, 2);

    // If we change foo, we should have to rebuild both
    let touched_foo = format!("// Touch\n{}", foo_text);
    p.update_file(
        PathBuf::from(localize_mock_filename("/mock/foo.ac")),
        &touched_foo,
        1,
    )
    .expect("update failed");
    let num_success = expect_build_ok(&mut p);
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
    let num_success = expect_build_ok(&mut p);
    assert_eq!(num_success, 3);

    // Change the middle theorem
    lines[4] = "    false = false";
    p.update_file(
        PathBuf::from(localize_mock_filename(filename)),
        &lines.join("\n"),
        1,
    )
    .expect("update failed");
    let num_success = expect_build_ok(&mut p);
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
fn test_double_import_value() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        let bar: Bool = true
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import bar
        from foo import bar
        "#,
    );
    p.expect_ok("foo");
    p.expect_module_err("main");
}

#[test]
fn test_double_import_type() {
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
        from foo import Foo
        "#,
    );
    p.expect_ok("foo");
    p.expect_module_err("main");
}

#[test]
fn test_double_import_typeclass() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        typeclass M: Magma {
            mul: (M, M) -> M
        }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
        from foo import Magma
        from foo import Magma
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
        from relate import Foo
        from pointed import Pointed

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
fn test_strict_mode_rejects_axiom_statements() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        axiom test_axiom { true }
        "#,
    );

    // First, verify it works without strict mode
    p.expect_ok("main");

    // Now test with strict mode enabled
    let mut builder = Builder::new(&p, CancellationToken::new(), |_| {});
    builder.strict = true;
    builder.build();

    // Should fail with an error - axiom statements are not allowed
    assert_eq!(builder.status, BuildStatus::Error);
}

#[test]
fn test_strict_mode_allows_theorems() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        theorem test_theorem { true }
        "#,
    );

    // Should work with strict mode since there's only a theorem, no axioms
    let mut builder = Builder::new(&p, CancellationToken::new(), |_| {});
    builder.strict = true;
    builder.build();

    // The build will have warnings because the theorem can't be proven,
    // but it shouldn't error from strict mode
    assert_ne!(builder.status, BuildStatus::Error);
}

#[test]
fn test_strict_mode_allows_inductive_types() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Nat {
            zero
            suc(Nat)
        }

        theorem test_induction(n: Nat) {
            n = n
        } by {
            Nat.induction(function(x: Nat) { x = x })
        }
        "#,
    );

    // Should work with strict mode since inductive types generate structural axioms,
    // not explicit axioms from the axiom keyword
    let mut builder = Builder::new(&p, CancellationToken::new(), |_| {});
    builder.strict = true;
    builder.build();

    // Should succeed
    assert_eq!(builder.status, BuildStatus::Good);
}

#[test]
fn test_strict_mode_rejects_axiomatic_types() {
    use crate::syntax::statement::Statement;
    use crate::syntax::token::{Token, TokenIter};

    let input = "type Nat: axiom\n";
    let tokens = Token::scan(input);
    let mut tokens = TokenIter::new(tokens);

    // Should error in strict mode
    let result = Statement::parse(&mut tokens, false, true);
    match result {
        Ok(_) => panic!("Expected error in strict mode for 'type Nat: axiom'"),
        Err(e) => assert!(
            e.to_string().contains("axiom keyword is not allowed"),
            "Error should mention axiom keyword: {}",
            e
        ),
    }
}

#[test]
fn test_strict_mode_rejects_axiomatic_constants() {
    use crate::syntax::statement::Statement;
    use crate::syntax::token::{Token, TokenIter};

    let input = "let zero: Nat = axiom\n";
    let tokens = Token::scan(input);
    let mut tokens = TokenIter::new(tokens);

    // Should error in strict mode
    let result = Statement::parse(&mut tokens, false, true);
    match result {
        Ok(_) => panic!("Expected error in strict mode for 'let zero: Nat = axiom'"),
        Err(e) => assert!(
            e.to_string().contains("axiom keyword is not allowed"),
            "Error should mention axiom keyword: {}",
            e
        ),
    }
}

#[test]
fn test_prelude_auto_import() {
    let mut p = Project::new_mock();

    // Create a prelude.ac file with a constant
    p.mock("/mock/prelude.ac", "let foo: Bool = true");

    // Create a module that uses the prelude constant without importing
    p.mock("/mock/main.ac", "let bar: Bool = not(foo)");

    // This should work because prelude is auto-imported
    p.expect_ok("main");
}

#[test]
fn test_polymorphic_variable_satisfy() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive List[T] {
            nil
            cons(T, List[T])
        }
        // Define a polymorphic witness using variable satisfy
        let witness[T]: List[T] satisfy {
            witness = List.nil[T]
        }
        // Use the polymorphic witness at a concrete type
        let bool_witness: List[Bool] = witness[Bool]
        theorem test_witness {
            bool_witness = List.nil[Bool]
        }
    "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_polymorphic_function_satisfy() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        // Define a polymorphic identity function using function satisfy
        let identity[T](x: T) -> r: T satisfy {
            r = x
        }
        // Use the polymorphic function at a concrete type
        let bool_id: Bool = identity[Bool](true)
        theorem test_identity {
            bool_id = true
        }
    "#,
    );
    p.expect_ok("main");
}

#[test]
fn test_import_normalization_handles_conflicting_attribute_ids() {
    let mut p = Project::new_mock();

    p.mock(
        "/mock/nat/base.ac",
        indoc! {"
            inductive Nat {
                0
                suc(Nat)
            }

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    self
                }

                define mul(self, other: Nat) -> Nat {
                    self
                }
            }
        "},
    );

    p.mock(
        "/mock/nat/divide.ac",
        indoc! {"
            from nat.base import Nat

            attributes Nat {
                define divides(self, other: Nat) -> Bool {
                    exists(x: Nat) { self * x = other }
                }
            }
        "},
    );

    p.mock(
        "/mock/list/base.ac",
        indoc! {"
            from nat.base import Nat

            inductive List[T] {
                nil
                cons(T, List[T])
            }

            attributes Nat {
                define range(self) -> List[Nat] {
                    List.nil[Nat]
                }
            }
        "},
    );

    p.mock(
        "/mock/int/base.ac",
        indoc! {"
            from nat.base import Nat

            inductive Int {
                0
                wrap(Nat)
            }

            attributes Int {
                define mul(self, other: Int) -> Int {
                    self
                }
            }

            define abs(a: Int) -> Nat {
                Nat.0
            }
        "},
    );

    p.mock(
        "/mock/int/default.ac",
        indoc! {"
            from nat.divide import Nat
            from int.base import Int, abs
            from list.base import List

            attributes Int {
                define divides(self, other: Int) -> Bool {
                    exists(d: Int) { d * self = other }
                }
            }

            theorem div_imp_div_abs(a: Int, b: Int) {
                a.divides(b) implies abs(a).divides(abs(b))
            } by {
                if a.divides(b) {
                    abs(a).divides(abs(b))
                }
            }
        "},
    );

    // This used to panic in normalization import merge with:
    // "Function type expected but not found during type application".
    p.expect_ok("int.default");
}
