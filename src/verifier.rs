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

/// Represents a line selection for verification: either a single line or a range.
#[derive(Clone, Debug)]
pub enum LineSelection {
    /// A single line number (1-based, external)
    Single(u32),
    /// A range of lines, inclusive (1-based, external)
    Range(u32, u32),
}

/// The Verifier manages the run of a single build.
/// It creates its own project.
pub struct Verifier {
    /// Pointer to the manually managed project for cleanup
    project_ptr: *mut Project,

    /// The target module to verify.
    /// If None, all modules are verified.
    target: Option<String>,

    /// Optional line selection (1-based, external) to verify specific goal(s).
    /// If this is set, target must be as well.
    pub line_selection: Option<LineSelection>,

    /// When this flag is set, verification exits immediately upon encountering any warning.
    /// This is useful for operations like the cleaner where any warning means the change
    /// should be reverted, so there's no point continuing verification.
    pub exit_on_warning: bool,

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
            line_selection: None,
            exit_on_warning: false,
            events,
            builder,
        })
    }

    /// Returns VerifierOutput on success or clean failure.
    /// Returns an error string if verification fails during setup.
    pub fn run(mut self) -> Result<VerifierOutput, String> {
        // If a specific line selection is provided along with a target, set up goal filtering
        if let Some(ref line_sel) = self.line_selection {
            let Some(target) = &self.target else {
                panic!("line_selection set without target");
            };
            // line values are external line numbers (1-based)
            match line_sel {
                LineSelection::Single(line) => {
                    if let Err(e) = self.builder.set_single_goal(target, *line) {
                        return Err(format!("Failed to set single goal: {}", e));
                    }
                }
                LineSelection::Range(start, end) => {
                    if let Err(e) = self.builder.set_goal_range(target, *start, *end) {
                        return Err(format!("Failed to set goal range: {}", e));
                    }
                }
            }
        }

        // Pass the exit_on_warning flag to the builder
        self.builder.exit_on_warning = self.exit_on_warning;

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
        // Pass is_partial_build flag: true if we have a specific target, false for full build
        if let Some(build_cache) = self.builder.into_build_cache() {
            let is_partial_build = self.target.is_some();
            unsafe {
                (*self.project_ptr).update_build_cache(build_cache, is_partial_build);
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
        // Verify all modules (None) to test certificate caching
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
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

        // Verify again (all modules)
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
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

        // Now test reverify mode with verifier3 (all modules)
        let mut verifier3 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
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

        // Create a verifier for all modules to test certificate caching
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
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

        // Verify again (all modules)
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
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

        src.child("foo.ac")
            .write_str("from bar import Bar")
            .unwrap();
        src.child("bar.ac")
            .write_str("from foo import Foo")
            .unwrap();

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
        src.child("main.ac")
            .write_str("from foo import Foo")
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("main".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        let output = verifier.run().unwrap();

        // The verifier should report an elaboration error
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

        // First build with all modules (just foo.ac for now)
        let verifier1 = Verifier::new(acornlib.path().to_path_buf(), config.clone(), None).unwrap();
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
                from foo import thing
                theorem bar_goal {
                    thing = thing
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

        // First build with all modules (just foo.ac for now)
        let verifier1 = Verifier::new(acornlib.path().to_path_buf(), config.clone(), None).unwrap();
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
                from foo import thing
                theorem bar_goal {
                    thing = thing
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
    fn test_verifier_concrete_scoped_constants() {
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

    #[test]
    fn test_manifest_preserved_when_verifying_single_module() {
        let (acornlib, src, build) = setup();

        // Create two modules
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem a_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem b_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        // Phase 1: Verify all modules - manifest should have two entries
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check manifest has two entries
        let manifest_file = build.child("manifest.json");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::Manifest = serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.modules.len(),
            2,
            "manifest should have 2 entries after verifying both modules"
        );

        // Phase 2: Verify only module_a - manifest should STILL have two entries
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            Some("module_a".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        // Check manifest STILL has two entries (this is the bug - it will only have one)
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::Manifest = serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.modules.len(),
            2,
            "BUG: manifest should still have 2 entries after verifying only module_a, but other entries were deleted"
        );
    }

    #[test]
    fn test_manifest_preserved_when_reproving_single_module() {
        // This test mimics the `reprove <module> --write-cache` command behavior.
        // The key difference from verify is: read_cache: false, write_cache: true
        let (acornlib, src, build) = setup();

        // Create two modules
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem a_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom
                theorem b_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        // Phase 1: Verify all modules normally - manifest should have two entries
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check manifest has two entries
        let manifest_file = build.child("manifest.json");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::Manifest = serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.modules.len(),
            2,
            "manifest should have 2 entries after verifying both modules"
        );

        // Phase 2: Reprove only module_a with reprove-style config (read_cache: false, write_cache: true)
        // This is what `reprove module_a --write-cache` does
        let reprove_config = ProjectConfig {
            use_filesystem: true,
            read_cache: false,
            write_cache: true,
        };
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("module_a".to_string()),
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        // Check manifest STILL has two entries
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::Manifest = serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.modules.len(),
            2,
            "manifest should still have 2 entries after reproving only module_a"
        );
    }

    #[test]
    fn test_reprove_default_alias_writes_canonical_cache_path() {
        let (acornlib, src, build) = setup();

        src.child("rat").create_dir_all().unwrap();
        src.child("rat")
            .child("default.ac")
            .write_str(
                r#"
                theorem t {
                    true
                }
                "#,
            )
            .unwrap();

        let reprove_config = ProjectConfig {
            use_filesystem: true,
            read_cache: false,
            write_cache: true,
        };
        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            reprove_config,
            Some("rat.default".to_string()),
        )
        .unwrap();
        verifier.builder.check_hashes = false;
        verifier.builder.reverify = false;
        verifier.builder.operation_verb = "reproved";
        let output = verifier.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);

        assert!(
            build.child("rat.jsonl").exists(),
            "canonical cache file should be written for rat/default.ac"
        );
        assert!(
            !build.child("rat").child("default.jsonl").exists(),
            "default.jsonl should never be written for default.ac modules"
        );

        let mut reverify = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        reverify.builder.reverify = true;
        reverify.builder.check_hashes = false;
        let reverify_output = reverify.run().unwrap();
        assert_eq!(reverify_output.status, BuildStatus::Good);
    }

    #[test]
    fn test_deleted_module_removed_from_manifest_on_full_verify() {
        let (acornlib, src, build) = setup();

        // Create two modules
        let module_a = src.child("module_a.ac");
        module_a
            .write_str(
                r#"
                type Nat: axiom
                theorem a_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        let module_b = src.child("module_b.ac");
        module_b
            .write_str(
                r#"
                type Nat: axiom
                theorem b_theorem(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        // Phase 1: Verify all modules - manifest should have two entries
        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check manifest has two entries
        let manifest_file = build.child("manifest.json");
        assert!(manifest_file.exists(), "manifest.json should exist");
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::Manifest = serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.modules.len(),
            2,
            "manifest should have 2 entries after verifying both modules"
        );

        // Phase 2: Delete module_b
        std::fs::remove_file(module_b.path()).unwrap();

        // Phase 3: Run full verify again - manifest should now only have one entry
        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        // Check manifest now only has one entry (module_b should be removed)
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        let manifest: crate::manifest::Manifest = serde_json::from_str(&manifest_content).unwrap();
        assert_eq!(
            manifest.modules.len(),
            1,
            "manifest should have only 1 entry after deleting module_b and running full verify"
        );

        // Verify the remaining entry is module_a
        let module_a_name = crate::manifest::ModuleName::new(&vec!["module_a".to_string()]);
        assert!(
            manifest.modules.contains_key(&module_a_name),
            "manifest should still contain module_a"
        );
    }

    #[test]
    fn test_global_certificate_preservation_across_modules() {
        let (acornlib, src, build) = setup();

        // Phase 1: Initial build - both modules verify successfully
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem a_theorem_1(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem b_theorem_1(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        let mut verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier1.builder.check_hashes = false;
        let output1 = verifier1.run().unwrap();
        assert_eq!(output1.status, BuildStatus::Good);

        // Check initial certificates: both modules should have 1 cert each
        let cert_a = build.child("module_a.jsonl");
        let cert_b = build.child("module_b.jsonl");
        assert!(cert_a.exists(), "module_a.jsonl should exist");
        assert!(cert_b.exists(), "module_b.jsonl should exist");

        let cert_a_content = std::fs::read_to_string(cert_a.path()).unwrap();
        let cert_b_content = std::fs::read_to_string(cert_b.path()).unwrap();
        assert_eq!(
            cert_a_content.lines().count(),
            1,
            "module_a should have 1 cert"
        );
        assert_eq!(
            cert_b_content.lines().count(),
            1,
            "module_b should have 1 cert"
        );

        // Phase 2: Mixed build - module A renames its theorem, module B adds bad theorem
        src.child("module_a.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem a_theorem_renamed(x: Nat) {
                    x = x
                }
                "#,
            )
            .unwrap();

        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem b_theorem_1(x: Nat) {
                    x = x
                }

                theorem b_bad_theorem(x: Nat, y: Nat) {
                    x = y
                }
                "#,
            )
            .unwrap();

        let mut verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier2.builder.check_hashes = false;
        let output2 = verifier2.run().unwrap();
        // Build should have warnings (module_b has unverified theorem)
        assert_eq!(output2.status, BuildStatus::Warning);

        // Check certificates after mixed build:
        // Module A should have 2 certs (new cert for a_theorem_renamed + old cert for a_theorem_1 preserved due to global warning)
        // Module B should have 1 cert (only the old cert, new theorem didn't verify)
        let cert_a_content = std::fs::read_to_string(cert_a.path()).unwrap();
        let cert_b_content = std::fs::read_to_string(cert_b.path()).unwrap();
        assert_eq!(
            cert_a_content.lines().count(),
            2,
            "module_a should have 2 certs (a_theorem_renamed + old a_theorem_1 preserved due to global warning)"
        );
        assert_eq!(
            cert_b_content.lines().count(),
            1,
            "module_b should still have 1 cert (only the old one)"
        );

        // Phase 3: Clean build - fix module B so it verifies
        src.child("module_b.ac")
            .write_str(
                r#"
                type Nat: axiom

                theorem b_theorem_1(x: Nat) {
                    x = x
                }

                theorem b_theorem_2(x: Nat, y: Nat) {
                    y = y
                }
                "#,
            )
            .unwrap();

        let mut verifier3 = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier3.builder.check_hashes = false;
        let output3 = verifier3.run().unwrap();
        // Build should be good now
        assert_eq!(output3.status, BuildStatus::Good);

        // Check certificates after clean build:
        // Module A should have only its current cert (old a_theorem_1 cert flushed)
        // Module B should have both its certs
        let cert_a_content = std::fs::read_to_string(cert_a.path()).unwrap();
        let cert_b_content = std::fs::read_to_string(cert_b.path()).unwrap();
        assert_eq!(
            cert_a_content.lines().count(),
            1,
            "module_a should have 1 cert (only a_theorem_renamed, old a_theorem_1 flushed)"
        );
        assert_eq!(
            cert_b_content.lines().count(),
            2,
            "module_b should have 2 certs (b_theorem_1 and b_theorem_2)"
        );
    }

    #[test]
    fn test_verifier_function_satisfy() {
        let (acornlib, src, _) = setup();

        // Create a file with a function satisfy and prove it works correctly
        src.child("main.ac")
            .write_str(
                r#"
                // Define an identity function using function satisfy
                let identity(x: Bool) -> r: Bool satisfy {
                    r = x
                }

                // Prove that identity returns its input
                theorem identity_true {
                    identity(true) = true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify function satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(output.metrics.goals_success >= 1);
    }

    #[test]
    fn test_verifier_polymorphic_variable_satisfy() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
                typeclass Z: Zero {
                    0: Z
                }

                let zero1[Z: Zero]: Z satisfy {
                    zero1 = Z.0
                }

                let zero2[Z: Zero]: Z satisfy {
                    zero2 = Z.0
                }

                theorem goal[Z: Zero] {
                    zero1[Z] = zero2[Z]
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully elaborate polymorphic variable satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert!(
            output.status == BuildStatus::Good,
            "Expected Good status, got {:?}",
            output.status
        );
    }

    #[test]
    fn test_verifier_polymorphic_function_satisfy() {
        let (acornlib, src, _) = setup();

        // Test polymorphic function satisfy with a theorem proving it works
        src.child("main.ac")
            .write_str(
                r#"
                // Define a polymorphic identity function using function satisfy
                let identity[T](x: T) -> r: T satisfy {
                    r = x
                }

                // Prove that identity returns its input
                theorem identity_true {
                    identity[Bool](true) = true
                }
                "#,
            )
            .unwrap();

        let mut verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            ProjectConfig::default(),
            None,
        )
        .unwrap();
        verifier.builder.check_hashes = false;

        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify polymorphic function satisfy: {:?}",
            result
        );

        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert!(output.metrics.goals_success >= 1);
    }
}
