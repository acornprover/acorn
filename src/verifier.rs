use std::path::PathBuf;

use crate::builder::{BuildStatus, BuildMetrics};
use crate::project::Project;

#[derive(Debug, PartialEq, Eq)]
pub enum VerifierMode {
    Standard,
    Full,
    Filtered,
}

pub struct Verifier {
    mode: VerifierMode,

    /// The target module to verify.
    /// If None, all modules are verified.
    target: Option<String>,

    /// If true, a dataset is created, for training.
    create_dataset: bool,

    /// The starting path to find the acorn library from.
    start_path: PathBuf,
}

impl Verifier {
    pub fn new(start_path: PathBuf, mode: VerifierMode, target: Option<String>, create_dataset: bool) -> Self {
        Self {
            mode,
            target,
            create_dataset,
            start_path,
        }
    }

    /// Returns (BuildStatus, BuildMetrics) on success, or an error string if verification fails.
    pub fn run(&self) -> Result<(BuildStatus, BuildMetrics), String> {
        let use_cache = self.mode != VerifierMode::Full;

        let mut project = match Project::new_local(&self.start_path, use_cache) {
            Ok(p) => p,
            Err(e) => return Err(format!("Error: {}", e)),
        };
        if self.mode == VerifierMode::Filtered {
            project.check_hashes = false;
        }

        if let Some(target) = &self.target {
            if target.ends_with(".ac") {
                // Looks like a filename
                let path = PathBuf::from(&target);
                if !project.add_target_by_path(&path) {
                    return Err(format!("File not found: {}", target));
                }
            } else {
                if !project.add_target_by_name(&target) {
                    return Err(format!("Module not found: {}", target));
                }
            }
        } else {
            project.add_all_targets();
        }

        // Set up the builder
        let mut builder = project.builder(|event| {
            if let Some(m) = event.log_message {
                if let Some(diagnostic) = event.diagnostic {
                    println!(
                        "{}, line {}: {}",
                        event.module,
                        diagnostic.range.start.line + 1,
                        m
                    );
                } else {
                    println!("{}", m);
                }
            }
        });
        if self.mode == VerifierMode::Filtered {
            builder.log_when_slow = true;
        }
        if self.create_dataset {
            builder.create_dataset();
        }
        if self.target.is_none() {
            builder.log_secondary_errors = false;
        }

        // Build
        project.build(&mut builder);
        builder.metrics.print(builder.status);
        if let Some(dataset) = builder.dataset {
            dataset.save();
        }

        if self.mode == VerifierMode::Filtered && builder.metrics.searches_fallback > 0 {
            return Err("Warning: the filtered prover was not able to handle all goals.".to_string());
        }
        
        Ok((builder.status, builder.metrics))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_fs::prelude::*;
    use assert_fs::TempDir;

    #[test]
    fn test_verifier_with_simple_acornlib() {
        // Create a temporary directory with acornlib structure
        let temp = TempDir::new().unwrap();
        let acornlib = temp.child("acornlib");
        acornlib.create_dir_all().unwrap();
        
        // Create foo.ac with a simple theorem
        let foo_ac = acornlib.child("foo.ac");
        foo_ac.write_str(r#"
theorem simple_truth {
    true
}
"#).unwrap();

        // Create a verifier and test that it can run successfully
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            VerifierMode::Standard,
            Some("foo".to_string()),
            false
        );
        
        // Test that the verifier was created successfully with the right parameters
        assert_eq!(verifier.start_path, acornlib.path());
        assert_eq!(verifier.mode, VerifierMode::Standard);
        assert_eq!(verifier.target, Some("foo".to_string()));
        assert_eq!(verifier.create_dataset, false);
        
        // Test that the verifier can run successfully on our simple theorem
        let result = verifier.run();
        assert!(result.is_ok(), "Verifier should successfully verify the simple theorem: {:?}", result);
        
        // Check that we actually proved something
        let (status, metrics) = result.unwrap();
        assert_eq!(status, BuildStatus::Good);
        assert_eq!(metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(metrics.searches_total > 0); // Should have performed at least one search
        
        temp.close().unwrap();
    }

    #[test]
    fn test_verifier_with_acorn_toml_layout() {
        // Create a temporary directory with the new acorn.toml + src layout
        let temp = TempDir::new().unwrap();
        let acornlib = temp.child("acornlib");
        acornlib.create_dir_all().unwrap();
        
        // Create acorn.toml file
        let acorn_toml = acornlib.child("acorn.toml");
        acorn_toml.write_str("").unwrap();
        
        // Create src directory
        let src = acornlib.child("src");
        src.create_dir_all().unwrap();
        
        // Create foo.ac inside the src directory
        let foo_ac = src.child("foo.ac");
        foo_ac.write_str(r#"
theorem simple_truth {
    true
}
"#).unwrap();

        // Create a verifier starting from the acornlib directory
        // The verifier should find the src directory and use it as the root
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            VerifierMode::Standard,
            Some("foo".to_string()),
            false
        );
        
        // Test that the verifier can run successfully on our theorem in the src directory
        let result = verifier.run();
        assert!(result.is_ok(), "Verifier should successfully verify the theorem in src directory: {:?}", result);
        
        // Check that we actually proved something
        let (status, metrics) = result.unwrap();
        assert_eq!(status, BuildStatus::Good);
        assert_eq!(metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(metrics.searches_total > 0); // Should have performed at least one search
        
        temp.close().unwrap();
    }
}
