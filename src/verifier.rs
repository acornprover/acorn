use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use tokio_util::sync::CancellationToken;

use crate::builder::{BuildEvent, BuildMetrics, BuildStatus, Builder};
use crate::project::{Project, ProjectConfig};

/// Output from running the verifier
#[derive(Debug)]
pub struct VerifierOutput {
    /// The overall build status
    pub status: BuildStatus,

    /// Build metrics collected during verification
    pub metrics: BuildMetrics,

    /// All build events collected during verification
    pub events: Vec<BuildEvent>,
}

impl VerifierOutput {
    /// How many verification events were collected.
    pub fn num_verified(&self) -> usize {
        self.events.iter().filter(|e| e.verified.is_some()).count()
    }

    pub fn is_success(&self) -> bool {
        self.status == BuildStatus::Good
    }
}

/// The Verifier manages the run of a single build.
pub struct Verifier {
    /// Pointer to the manually managed project for cleanup
    project_ptr: *mut Project,

    /// The target module to verify.
    /// If None, all modules are verified.
    target: Option<String>,

    /// Optional external line number (1-based) to verify a single goal.
    /// If this is set, target must be as well.
    pub line: Option<u32>,

    /// Events collected during verification
    events: Rc<RefCell<Vec<BuildEvent>>>,

    /// The builder for verification
    pub builder: Builder<'static>,
}

impl Verifier {
    pub fn new(
        start_path: PathBuf,
        config: ProjectConfig,
        target: Option<String>,
    ) -> Result<Self, String> {
        let mut project = Project::new_local(&start_path, config.clone())?;

        // Add targets to the project
        if let Some(ref target) = target {
            if target == "-" {
                let path = PathBuf::from("<stdin>");
                project.add_target_by_path(&path)?;
            } else if target.starts_with("-:") {
                let path = PathBuf::from(target);
                project.add_target_by_path(&path)?;
            } else if target.ends_with(".ac") {
                // Looks like a filename
                let path = PathBuf::from(target);
                project.add_target_by_path(&path)?;
            } else {
                project.add_target_by_name(target)?;
            }
        } else {
            project.add_src_targets();
        }

        // Unsafe is to make this self-referential
        let project_box = Box::new(project);
        let project_ptr = Box::into_raw(project_box);
        let project: &'static Project = unsafe { &*project_ptr };
        let events = Rc::new(RefCell::new(Vec::new()));
        let events_clone = events.clone();

        // Set up the builder with event handler
        let mut builder = Builder::new(project, CancellationToken::new(), move |event| {
            if let Some(m) = &event.log_message {
                println!("{}", m);
            }

            // Store the event
            events_clone.borrow_mut().push(event);
        });

        if target.is_none() {
            builder.log_secondary_errors = false;
        }

        Ok(Self {
            project_ptr,
            target: target.clone(),
            line: None,
            events,
            builder,
        })
    }

    /// Returns VerifierOutput on success or clean failure.
    /// Returns an error string if verification fails during setup.
    pub fn run(mut self) -> Result<VerifierOutput, String> {
        // If a specific line is provided along with a target, set up single goal verification
        if let Some(line) = self.line {
            let Some(target) = &self.target else {
                panic!("line set without target");
            };
            // line is the external line number (1-based)
            if let Err(e) = self.builder.set_single_goal(target, line) {
                return Err(format!("Failed to set single goal: {}", e));
            }
        }

        // Build
        self.builder.build();
        self.builder.metrics.print(self.builder.status);

        // Create the output
        let status = self.builder.status;
        let metrics = self.builder.metrics.clone();
        let events = self.events.take();
        let output = VerifierOutput {
            status,
            metrics,
            events,
        };

        // Update the build cache if the build was successful
        if let Some(build_cache) = self.builder.into_build_cache() {
            unsafe {
                (*self.project_ptr).update_build_cache(build_cache);
            }
        }

        // Clean up the project
        unsafe {
            drop(Box::from_raw(self.project_ptr));
        }

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_fs::fixture::ChildPath;
    use assert_fs::prelude::*;
    use assert_fs::TempDir;

    /// Creates a standard Acorn project layout with acorn.toml, src/, and build/ directories.
    /// Returns (project dir, src_dir, build_dir) for use in tests.
    /// Close the project directory after use to clean up.
    fn setup() -> (TempDir, ChildPath, ChildPath) {
        let temp = TempDir::new().unwrap();
        temp.child("acorn.toml").write_str("").unwrap();
        let src = temp.child("src");
        src.create_dir_all().unwrap();
        let build = temp.child("build");
        build.create_dir_all().unwrap();
        (temp, src, build)
    }

    #[test]
    fn test_verifier_basic() {
        let (acornlib, src, build) = setup();

        // Create foo.ac inside the src directory
        let foo_ac = src.child("foo.ac");
        foo_ac
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier starting from the acornlib directory
        // The verifier should find the src directory and use it as the root
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;

        // Test that the verifier can run successfully on our theorem in the src directory
        let result = verifier1.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify the theorem in src directory: {:?}",
            result
        );

        // Check that we proved one goal, via search
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1);
        assert_eq!(output.metrics.goals_success, 1);
        assert_eq!(output.metrics.certs_cached, 0);
        assert_eq!(output.metrics.certs_unused, 0);
        assert_eq!(output.metrics.searches_total, 1);

        // With certificates enabled, we should NOT create YAML files
        let build_file = build.child("foo.yaml");
        assert!(
            !build_file.exists(),
            "Module cache YAML file should NOT exist when using certificates"
        );

        // Check that the cert file has one line
        let cert_file = build.child("foo.jsonl");
        assert!(cert_file.exists(), "build/foo.jsonl should exist");
        let jsonl_content = std::fs::read_to_string(cert_file.path()).unwrap();
        let line_count = jsonl_content.lines().count();
        assert_eq!(line_count, 1,);

        assert!(build.child("manifest.json").exists());

        // Verify again
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let result2 = verifier2.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        // Check that we proved one goal, via cached cert
        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(output2.metrics.goals_total, 1);
        assert_eq!(output2.metrics.goals_success, 1);
        assert_eq!(output2.metrics.certs_cached, 1);
        assert_eq!(output2.metrics.certs_unused, 0);
        assert_eq!(output2.metrics.searches_total, 0);

        // Check that the cert file still has one line
        assert!(cert_file.exists(), "build/foo.jsonl should exist");
        let jsonl_content = std::fs::read_to_string(cert_file.path()).unwrap();
        let line_count = jsonl_content.lines().count();
        assert_eq!(line_count, 1,);

        // Now test reverify mode with verifier3
        let mut verifier3 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo".to_string()),
        )
        .unwrap();
        verifier3.builder.check_hashes = false;
        verifier3.builder.reverify = true;
        let result3 = verifier3.run();
        assert!(
            result3.is_ok(),
            "Third verifier in reverify mode should successfully run: {:?}",
            result3
        );

        // Check that we proved one goal in reverify mode, via cached cert
        let output3 = result3.unwrap();
        assert_eq!(output3.status, BuildStatus::Good);
        assert_eq!(output3.metrics.goals_total, 1);
        assert_eq!(output3.metrics.goals_success, 1);
        assert_eq!(output3.metrics.certs_cached, 1);
        assert_eq!(output3.metrics.certs_unused, 0);
        // In reverify mode, we should never reach the search phase
        assert_eq!(output3.metrics.searches_total, 0);
    }

    #[test]
    fn test_verifier_uses_nested_cache() {
        let (acornlib, src, build) = setup();

        // Create a nested directory structure
        let foo_dir = src.child("foo");
        foo_dir.create_dir_all().unwrap();

        // Create a file at foo/bar.ac with one theorem
        let bar_ac = foo_dir.child("bar.ac");
        bar_ac
            .write_str(
                r#"
                theorem nested_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier targeting the nested module
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo.bar".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;

        // Run the verifier the first time
        let result = verifier1.run();
        assert!(
            result.is_ok(),
            "First verifier run should succeed: {:?}",
            result
        );

        // Check that we actually proved something
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(output.metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(output.metrics.searches_total > 0); // Should have performed at least one search

        // With certificates enabled, we should NOT create YAML files
        let build_foo_dir = build.child("foo");
        let build_file = build_foo_dir.child("bar.yaml");
        assert!(
            !build_file.exists(),
            "YAML cache file should NOT exist when using certificates"
        );

        // Check that we created a JSONL file for certificates in the nested directory
        let cert_file = build_foo_dir.child("bar.jsonl");
        assert!(
            cert_file.exists(),
            "Certificate file should exist at build/foo/bar.jsonl"
        );

        assert!(build.child("manifest.json").exists());

        // Verify again
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo.bar".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let result2 = verifier2.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
    }

    #[test]
    fn test_verifier_filter_picks_up_imported_extends() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property[B: Bar] {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }
        "#,
            )
            .unwrap();

        src.child("main.ac")
            .write_str(
                r#"
            from foo import Baz

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property[B: Baz] {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output = verifier1.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
    }

    #[test]
    fn test_verifier_filter_picks_up_local_extends() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property[B: Bar] {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property[B: Baz] {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output = verifier1.run().unwrap();
        assert_eq!(output.num_verified(), 5);

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good,);
        assert_eq!(output.num_verified(), 5);
    }

    #[test]
    fn test_verifier_fails_on_circular_import() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac").write_str("import bar").unwrap();
        src.child("bar.ac").write_str("import foo").unwrap();

        let result = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("foo".to_string()),
        );

        let Err(err) = result else {
            panic!("Verifier::new should fail on circular import");
        };

        assert!(
            err.contains("circular"),
            "Expected circular import error, got: {}",
            err
        );

        if err.lines().map(|l| l.contains("^^^^^")).count() != 1 {
            panic!(
                "Expected exactly one ^^^^^^ line in the error message, got:\n{}",
                err
            );
        }
    }

    #[test]
    fn test_verifier_fails_on_ambiguous_import() {
        let (acornlib, src, _) = setup();

        // Create both foo.ac and foo/default.ac
        src.child("foo.ac").write_str("type Foo: axiom").unwrap();
        std::fs::create_dir_all(src.child("foo").path()).unwrap();
        src.child("foo")
            .child("default.ac")
            .write_str("type Bar: axiom")
            .unwrap();

        // Try to import the ambiguous module
        src.child("main.ac").write_str("import foo").unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        let output = verifier.run().unwrap();

        // The verifier should report a compilation error
        assert_eq!(output.status, BuildStatus::Error);

        // Check that the error message contains "ambiguous"
        let error_messages: Vec<String> = output
            .events
            .iter()
            .filter_map(|e| e.log_message.as_ref())
            .cloned()
            .collect();
        let error_text = error_messages.join("\n");
        assert!(
            error_text.contains("ambiguous"),
            "Expected ambiguous import error, got: {}",
            error_text
        );
    }

    #[test]
    fn test_module_skipping() {
        let (acornlib, src, build) = setup();

        // Create foo.ac with a theorem
        src.child("foo.ac")
            .write_str(
                r#"
                let thing: Bool = axiom
                theorem foo_goal {
                    thing = thing
                }
                "#,
            )
            .unwrap();

        let config = ProjectConfig::default();

        // First build with just foo.ac
        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            Some("foo".to_string()),
        )
        .unwrap();
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);
        assert_eq!(output1.metrics.modules_total, 1);
        assert_eq!(output1.metrics.modules_cached, 0);

        // Check that manifest was created after first run
        let manifest = build.child("manifest.json");
        assert!(
            manifest.exists(),
            "manifest.json should exist after first build"
        );

        src.child("bar.ac")
            .write_str(
                r#"
                import foo
                theorem bar_goal {
                    foo.thing = foo.thing
                }
                "#,
            )
            .unwrap();

        // Second build with both modules - foo should be cached
        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            None, // Build all modules
        )
        .unwrap();
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(output2.metrics.modules_total, 2);

        assert_eq!(
            output2.metrics.modules_cached, 1,
            "foo module should have been cached"
        );
    }

    #[test]
    fn test_unchanged_jsonl_not_rewritten() {
        let (acornlib, src, build) = setup();

        // Create foo.ac with a theorem
        src.child("foo.ac")
            .write_str(
                r#"
                let thing: Bool = axiom
                theorem foo_goal {
                    thing = thing
                }
                "#,
            )
            .unwrap();

        let config = ProjectConfig::default();

        // First build with just foo.ac
        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            Some("foo".to_string()),
        )
        .unwrap();
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Get the modification time of the foo.jsonl file
        let foo_jsonl = build.child("foo.jsonl");
        assert!(
            foo_jsonl.exists(),
            "foo.jsonl should exist after first build"
        );
        let metadata1 = std::fs::metadata(foo_jsonl.path()).unwrap();
        let modified1 = metadata1.modified().unwrap();

        // Sleep briefly to ensure filesystem timestamp granularity
        std::thread::sleep(std::time::Duration::from_millis(10));

        // Now add bar.ac that depends on foo.ac
        src.child("bar.ac")
            .write_str(
                r#"
                import foo
                theorem bar_goal {
                    foo.thing = foo.thing
                }
                "#,
            )
            .unwrap();

        // Second build with both modules - foo should be cached
        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            None, // Build all modules
        )
        .unwrap();
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(
            output2.metrics.modules_cached, 1,
            "foo module should have been cached"
        );

        // Check that foo.jsonl was NOT rewritten (modification time unchanged)
        let metadata2 = std::fs::metadata(foo_jsonl.path()).unwrap();
        let modified2 = metadata2.modified().unwrap();
        assert_eq!(
            modified1, modified2,
            "foo.jsonl should not have been rewritten for unchanged module"
        );

        // Check that bar.jsonl was created
        let bar_jsonl = build.child("bar.jsonl");
        assert!(
            bar_jsonl.exists(),
            "bar.jsonl should exist after second build"
        );
    }

    #[test]
    fn test_verifier_concrete_local_constants() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
        inductive Nat {
            0
            suc(Nat)
        }
        attributes Nat {
            define add(self, other: Nat) -> Nat {
                match other {
                    Nat.0 {
                        self
                    }
                    Nat.suc(pred) {
                        self.add(pred).suc
                    }
                }
            }
        }

        numerals Nat

        theorem goal(a: Nat) {
            a + 0 = a
        }
        "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output = verifier1.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
    }
}
