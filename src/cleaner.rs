use std::io;
use std::path::PathBuf;

use tower_lsp::lsp_types::Range;

use crate::elaborator::environment::Environment;
use crate::elaborator::node::Node;
use crate::module::{LoadState, ModuleDescriptor};
use crate::project::{ImportError, Project, ProjectConfig, ProjectError};
use crate::verifier::Verifier;

/// A ModuleCleaner analyzes loaded modules to extract information about claims and proofs.
/// It stores the project root and module spec, but loads fresh Projects for each operation.
pub struct ModuleCleaner {
    project_root: PathBuf,
    module_spec: ModuleDescriptor,
}

/// Statistics from a cleaning operation.
#[derive(Debug)]
pub struct CleanStats {
    pub claims_deleted: usize,
    pub claims_kept: usize,
    pub original_lines: usize,
    pub final_lines: usize,
}

/// Errors that can occur when using the ModuleCleaner.
#[derive(Debug)]
pub enum CleanerError {
    Project(ProjectError),
    Import(ImportError),
    ModuleNotLoaded,
    ModuleLoading,
    Io(io::Error),
}

impl From<ProjectError> for CleanerError {
    fn from(error: ProjectError) -> Self {
        CleanerError::Project(error)
    }
}

impl From<ImportError> for CleanerError {
    fn from(error: ImportError) -> Self {
        CleanerError::Import(error)
    }
}

impl From<io::Error> for CleanerError {
    fn from(error: io::Error) -> Self {
        CleanerError::Io(error)
    }
}

impl ModuleCleaner {
    /// Creates a new ModuleCleaner for the specified project and module.
    pub fn new(project_root: PathBuf, module_spec: ModuleDescriptor) -> Self {
        ModuleCleaner {
            project_root,
            module_spec,
        }
    }

    /// Returns the ranges of all cleanable nodes in the specified module,
    /// including both Node::Claim nodes and Node::Block nodes with source ranges.
    /// Returns ranges in preorder traversal order.
    ///
    /// Loads a fresh Project each time to ensure it picks up any changes.
    pub fn ranges(&self) -> Result<Vec<Range>, CleanerError> {
        // Load a fresh project
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let mut project = Project::new_local(self.project_root.as_path(), config)?;

        // Load the module
        let module_id = project.load_module_by_name(&self.module_spec.to_string())?;
        let module_state = project.get_module_by_id(module_id);

        // Get the environment from the loaded module
        let env = match module_state {
            LoadState::Ok(env) => env,
            LoadState::Error(_) => {
                // If there's an elaboration error, we still want to extract what we can
                // Return empty ranges for now
                return Ok(Vec::new());
            }
            LoadState::Loading => return Err(CleanerError::ModuleLoading),
            LoadState::None => return Err(CleanerError::ModuleNotLoaded),
        };

        // Collect ranges from the module environment (depth 0)
        let mut ranges = Vec::new();
        Self::collect_ranges(env, &mut ranges);
        Ok(ranges)
    }

    /// Recursively collects cleanable ranges from an environment.
    /// This includes both Claim nodes and Block nodes with source ranges.
    /// Only collects items inside proofs (env.depth >= 1), never top-level items.
    /// - depth 0: top-level module (not cleanable - might be imported)
    /// - depth 1+: inside theorem/axiom proof blocks (cleanable - local to proof)
    fn collect_ranges(env: &Environment, ranges: &mut Vec<Range>) {
        // Only collect ranges when we're inside a proof (depth >= 1)
        let inside_proof = env.depth >= 1;

        for node in &env.nodes {
            match node {
                Node::Claim(goal, _, _, _) => {
                    // Only collect claims when inside proofs, but skip block-level goals
                    if inside_proof && !node.is_block_level_goal() {
                        // This is an internal claim in a proof, it's cleanable
                        ranges.push(goal.proposition.source.range);
                    }
                }
                Node::Block(block, _, _) => {
                    // Only collect blocks when inside proofs
                    // This means forall/if/by blocks inside theorems are cleanable,
                    // but top-level theorem blocks themselves are not
                    if inside_proof {
                        if let Some(range) = block.source_range {
                            ranges.push(range);
                        }
                    }
                    // Always recurse into the block to find nested cleanable items
                    Self::collect_ranges(&block.env, ranges);
                }
                Node::Structural(_, _) => {
                    // Skip structural nodes
                }
            }
        }
    }

    /// Attempts to delete the given range from the module file.
    /// Handles both full-line and partial-line deletions based on character positions in the range.
    /// If the module still verifies after deletion, returns Ok(true) and keeps the deletion.
    /// If verification fails (including parse errors), restores the original file and returns Ok(false).
    /// Returns Err only for unexpected errors (file not found, permission issues, etc.).
    ///
    /// # Panics
    /// Panics if the range is invalid (start line beyond file bounds), which indicates a bug in the caller.
    pub fn try_delete(&self, range: Range) -> Result<bool, CleanerError> {
        // Get the file path
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let project = Project::new_local(self.project_root.as_path(), config)?;
        let file_path = project.path_from_descriptor(&self.module_spec)?;

        // Read the original file content
        let original_content = std::fs::read_to_string(&file_path)?;

        // Delete the range (handles both full-line and partial-line deletions)
        let lines: Vec<&str> = original_content.lines().collect();
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;
        let start_char = range.start.character as usize;
        let end_char = range.end.character as usize;

        // Validate range - panic if invalid since this indicates a bug
        assert!(
            start_line < lines.len(),
            "Range start line {} is beyond file bounds (file has {} lines)",
            start_line,
            lines.len()
        );

        // Build new content with the range deleted
        let mut new_lines = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            if i < start_line || i > end_line {
                // Line is outside the range, keep it as-is
                new_lines.push(line.to_string());
            } else if i == start_line && i == end_line {
                // Deletion is within a single line - keep the part before start and after end
                let before = &line[..start_char.min(line.len())];
                let after = &line[end_char.min(line.len())..];
                let combined = format!("{}{}", before, after);
                // Only add the line if there's content left after deletion
                if !combined.trim().is_empty() || i == 0 || i == lines.len() - 1 {
                    new_lines.push(combined);
                }
            } else if i == start_line {
                // First line of multi-line deletion - keep the part before start_char
                let before = &line[..start_char.min(line.len())];
                if !before.trim().is_empty() || i == 0 {
                    new_lines.push(before.to_string());
                }
            } else if i == end_line {
                // Last line of multi-line deletion - keep the part after end_char
                let after = &line[end_char.min(line.len())..];
                if !after.trim().is_empty() || i == lines.len() - 1 {
                    new_lines.push(after.to_string());
                }
            }
            // else: middle lines of multi-line deletion are completely skipped
        }

        let new_content = new_lines.join("\n");
        // Add trailing newline if original had one
        let mut new_content = if original_content.ends_with('\n') {
            format!("{}\n", new_content)
        } else {
            new_content
        };

        // Consolidate whitespace
        while new_content.contains(" \n") {
            new_content = new_content.replace(" \n", "\n");
        }
        while new_content.contains("\n\n\n") {
            new_content = new_content.replace("\n\n\n", "\n\n");
        }

        // Write the modified content to disk
        std::fs::write(&file_path, &new_content)?;

        // Try to verify the module
        let verification_result = match Verifier::new(
            self.project_root.clone(),
            ProjectConfig::default(),
            Some(self.module_spec.to_string()),
        ) {
            Ok(mut verifier) => {
                // Enable early exit on warning - no need to continue verifying once we hit any issue
                verifier.exit_on_warning = true;
                // Run verification
                match verifier.run() {
                    Ok(output) => output.is_success(),
                    Err(_) => false, // Treat verification errors as failure
                }
            }
            Err(_) => false, // Treat initialization errors as failure (e.g., parse errors)
        };

        // If verification failed, restore the original file
        if !verification_result {
            std::fs::write(&file_path, original_content)?;
            return Ok(false);
        }

        // Verification succeeded - keep the deletion
        Ok(true)
    }

    /// Iteratively removes redundant claims from the module.
    /// Returns statistics about the cleaning operation.
    pub fn clean(&self) -> Result<CleanStats, CleanerError> {
        // Count original lines
        let original_lines = self.count_lines()?;

        let mut claims_deleted = 0;
        let mut claims_kept = 0;
        let mut last_required_range: Option<Range> = None;

        // Get the initial total number of cleanable goals
        let initial_ranges = self.ranges()?;
        let total_goals = initial_ranges.len();

        loop {
            // Get current cleanable ranges
            let ranges = self.ranges()?;

            // Find the first claim range that comes after last_required_range
            let next_range = ranges.iter().find(|range| {
                if let Some(ref last_req) = last_required_range {
                    range.start.line > last_req.start.line
                } else {
                    true // No last required, so first range is next
                }
            });

            // If no more claims to try, we're done
            let Some(&range_to_try) = next_range else {
                break;
            };

            // Calculate how many goals have been processed
            let goals_cleaned = claims_deleted + claims_kept;
            println!("{}/{} goals cleaned", goals_cleaned, total_goals);

            // Try to delete this claim
            if self.try_delete(range_to_try)? {
                // Deletion succeeded
                claims_deleted += 1;
                // Continue loop - ranges will be recalculated
            } else {
                // Deletion failed - this claim is required
                last_required_range = Some(range_to_try);
                claims_kept += 1;
                // Continue to next claim
            }
        }

        // Clean certificates: run verification with clean_certs enabled to minimize all certificates
        println!("Cleaning certificates...");
        let cert_cleaning_result = match Verifier::new(
            self.project_root.clone(),
            ProjectConfig::default(),
            Some(self.module_spec.to_string()), // Only clean this module
        ) {
            Ok(mut verifier) => {
                verifier.builder.clean_certs = true;
                match verifier.run() {
                    Ok(output) => output.is_success(),
                    Err(e) => {
                        println!("Certificate cleaning failed with error: {}", e);
                        false
                    }
                }
            }
            Err(e) => {
                println!("Failed to initialize certificate cleaning: {}", e);
                false
            }
        };

        if !cert_cleaning_result {
            return Err(CleanerError::Project(crate::project::ProjectError(
                "BUG: Certificate cleaning failed. This indicates a bug in the cleaning algorithm."
                    .to_string(),
            )));
        }

        // Final verification: verify the entire project (not just the module)
        // If this fails, there's a bug in the cleaning algorithm
        println!("Running final verification on entire project...");
        let final_verification_result = match Verifier::new(
            self.project_root.clone(),
            ProjectConfig::default(),
            None, // Verify all modules, not just this one
        ) {
            Ok(verifier) => {
                // Don't enable early exit here - we want to see all issues if there are any
                match verifier.run() {
                    Ok(output) => output.is_success(),
                    Err(e) => {
                        println!("Final verification failed with error: {}", e);
                        false
                    }
                }
            }
            Err(e) => {
                println!("Failed to initialize final verification: {}", e);
                false
            }
        };

        if !final_verification_result {
            return Err(CleanerError::Project(crate::project::ProjectError(
                "BUG: Final verification failed after cleaning. This indicates a bug in the cleaning algorithm.".to_string(),
            )));
        }

        // Post-process: remove empty blocks
        self.remove_empty_blocks()?;

        // Recount lines after post-processing
        let final_lines = self.count_lines()?;

        let stats = CleanStats {
            claims_deleted,
            claims_kept,
            original_lines,
            final_lines,
        };

        // Print stats
        println!("Cleaning complete!");
        println!("  Claims deleted: {}", stats.claims_deleted);
        println!("  Claims kept: {}", stats.claims_kept);
        println!(
            "  Lines: {} -> {} (removed {} lines)",
            stats.original_lines,
            stats.final_lines,
            stats.original_lines - stats.final_lines
        );

        Ok(stats)
    }

    /// Removes empty blocks from the module file.
    /// This is a post-processing step after cleaning to remove unnecessary syntax.
    /// We do this textually by looking for patterns like "} by {\n}" or "forall(...) {\n}" and removing them.
    fn remove_empty_blocks(&self) -> Result<(), CleanerError> {
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let project = Project::new_local(self.project_root.as_path(), config)?;
        let file_path = project.path_from_descriptor(&self.module_spec)?;

        // Read the file
        let content = std::fs::read_to_string(&file_path)?;

        // Look for empty blocks
        let mut new_content = content.clone();
        let mut changed = true;

        // Keep replacing until no more changes (handles nested cases)
        while changed {
            let before = new_content.clone();

            let lines: Vec<&str> = new_content.lines().collect();
            let mut result_lines = Vec::new();
            let mut i = 0;

            while i < lines.len() {
                let line = lines[i];

                // Check for "} by {" pattern (empty by blocks)
                if line.trim_end().ends_with("} by {") {
                    // Look ahead to see if the next line is just "}"
                    if i + 1 < lines.len() && lines[i + 1].trim() == "}" {
                        // Found an empty by block! Replace these two lines with just the closing brace
                        let before_by = &line[..line.rfind("} by {").unwrap()];
                        result_lines.push(format!("{}}}", before_by));
                        i += 2; // Skip both lines
                        continue;
                    }
                }

                // Check for empty forall blocks: "forall(...) {" followed by "}"
                // Look for lines ending with ") {" that start with forall
                if line.trim_end().ends_with(") {") {
                    let trimmed = line.trim();
                    // Check if this starts with forall
                    if trimmed.starts_with("forall(") {
                        // Look ahead to see if the next line is just "}"
                        if i + 1 < lines.len() && lines[i + 1].trim() == "}" {
                            // Found an empty forall block! Skip both lines entirely
                            i += 2;
                            continue;
                        }
                    }
                }

                result_lines.push(line.to_string());
                i += 1;
            }

            new_content = result_lines.join("\n");
            if content.ends_with('\n') && !new_content.ends_with('\n') {
                new_content.push('\n');
            }

            changed = new_content != before;
        }

        // Consolidate whitespace after removing blocks
        while new_content.contains(" \n") {
            new_content = new_content.replace(" \n", "\n");
        }
        while new_content.contains("\n\n\n") {
            new_content = new_content.replace("\n\n\n", "\n\n");
        }

        // Write back if changed
        if new_content != content {
            std::fs::write(&file_path, &new_content)?;
        }

        Ok(())
    }

    /// Counts the number of lines in the module file.
    fn count_lines(&self) -> Result<usize, CleanerError> {
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let project = Project::new_local(self.project_root.as_path(), config)?;
        let file_path = project.path_from_descriptor(&self.module_spec)?;
        let content = std::fs::read_to_string(&file_path)?;
        Ok(content.lines().count())
    }
}

/// A ProjectCleaner cleans all modules in a project.
/// It finds all modules in the project and runs a ModuleCleaner on each one.
pub struct ProjectCleaner {
    project_root: PathBuf,
}

impl ProjectCleaner {
    /// Creates a new ProjectCleaner for the specified project.
    pub fn new(project_root: PathBuf) -> Self {
        ProjectCleaner { project_root }
    }

    /// Cleans all modules in the project.
    /// Returns the total statistics across all modules.
    pub fn clean(&self) -> Result<CleanStats, CleanerError> {
        // Load the project to discover all modules
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let mut project = Project::new_local(self.project_root.as_path(), config)?;

        // Add all source files as targets
        project.add_src_targets();

        // Collect all module descriptors
        let modules: Vec<ModuleDescriptor> = project
            .iter_modules()
            .map(|(descriptor, _)| descriptor.clone())
            .collect();

        println!("Found {} modules to clean", modules.len());

        // Clean each module and accumulate stats
        let mut total_claims_deleted = 0;
        let mut total_claims_kept = 0;
        let mut total_original_lines = 0;
        let mut total_final_lines = 0;

        for (i, module_spec) in modules.iter().enumerate() {
            println!(
                "\n[{}/{}] Cleaning module: {}",
                i + 1,
                modules.len(),
                module_spec
            );

            let cleaner = ModuleCleaner::new(self.project_root.clone(), module_spec.clone());

            let stats = cleaner.clean()?;
            total_claims_deleted += stats.claims_deleted;
            total_claims_kept += stats.claims_kept;
            total_original_lines += stats.original_lines;
            total_final_lines += stats.final_lines;
        }

        let total_stats = CleanStats {
            claims_deleted: total_claims_deleted,
            claims_kept: total_claims_kept,
            original_lines: total_original_lines,
            final_lines: total_final_lines,
        };

        // Print summary
        println!("\n=== Project Cleaning Summary ===");
        println!("  Total claims deleted: {}", total_stats.claims_deleted);
        println!("  Total claims kept: {}", total_stats.claims_kept);
        println!(
            "  Total lines: {} -> {} (removed {} lines)",
            total_stats.original_lines,
            total_stats.final_lines,
            total_stats.original_lines - total_stats.final_lines
        );

        Ok(total_stats)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;
    use std::fs;
    use tempfile::TempDir;

    /// Helper function to clean Acorn code and return the result.
    /// Creates a temporary project, writes the input code, runs the cleaner, and returns the cleaned code.
    fn clean(input: &str) -> String {
        // Create a test project
        let temp_dir = TempDir::new().unwrap();
        let src_dir = temp_dir.path().join("src");
        fs::create_dir(&src_dir).unwrap();
        let toml_file = temp_dir.path().join("acorn.toml");
        fs::write(&toml_file, "").unwrap();

        // Create the test file
        let test_file = src_dir.join("test.ac");
        fs::write(&test_file, input).unwrap();

        // Create a cleaner for this module
        let cleaner = ModuleCleaner::new(
            temp_dir.path().to_path_buf(),
            ModuleDescriptor::name("test"),
        );

        // Run the cleaning operation
        cleaner.clean().expect("cleaning should succeed");

        // Read and return the cleaned file
        let output = fs::read_to_string(&test_file).unwrap();
        println!("Cleaned content:\n{}", output);
        output
    }

    #[test]
    fn test_cleaning_partial() {
        let input = indoc! {r#"
            inductive Color {
                red
                blue
            }

            axiom foo(f: Color -> Bool, c: Color) {
                f(c)
            }

            theorem cheat(c: Color) {
                c = Color.red
            } by {
                Color.red != Color.blue
                define f(d: Color) -> Bool {
                    d = Color.red
                }

                Color.red != Color.blue
                Color.red != Color.blue
                Color.red != Color.blue

                forall(k: Color) {
                }

                foo(f, c)
                Color.red != Color.blue
            }
        "#};

        let output = clean(input);

        // The core theorem structure should be preserved
        assert!(output.contains("theorem cheat"));
        assert!(output.contains(indoc! {r#"
            theorem cheat(c: Color) {
                c = Color.red
            } by {
                define f(d: Color) -> Bool {
                    d = Color.red
                }

                foo(f, c)
            }"#}));
    }

    #[test]
    fn test_cleaning_full() {
        let input = indoc! {r#"
            inductive Color {
                red
                blue
            }

            let fav: Color = Color.red

            theorem possibilities(c: Color) {
                c = Color.red or c = Color.blue
            } by {
                forall(d: Color) {
                    true
                }
                Color.red != Color.blue
            }
        "#};

        let output = clean(input);

        // Most stuff should be preserved
        assert!(output.contains("theorem possibilities"));
        assert!(output.contains("let fav"));
        assert!(output.contains("inductive Color"));

        // All the "by" blocks should be cleaned
        assert!(!output.contains("by"));
    }
}
