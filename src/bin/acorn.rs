// The Acorn CLI.
// You can run a language server, verify a file, or check the whole project.

use acorn::cleaner::{ModuleCleaner, ProjectCleaner};
use acorn::doc_generator::DocGenerator;
use acorn::interfaces::GoalInfo;
use acorn::module::ModuleDescriptor;
use acorn::project::{Project, ProjectConfig};
use acorn::server::{run_server, ServerArgs};
use acorn::verifier::{LineSelection as VerifierLineSelection, Verifier};
use clap::{Parser, Subcommand};
use mimalloc::MiMalloc;
use std::io::{self, Write};
use tracing_subscriber::{fmt, prelude::*, EnvFilter};
use walkdir::WalkDir;

/// Represents a line selection: either a single line or a range.
#[derive(Clone, Debug)]
pub enum LineSelection {
    /// A single line number (1-based, external)
    Single(u32),
    /// A range of lines, inclusive (1-based, external)
    Range(u32, u32),
}

/// Parse target and line from various syntaxes:
/// - MODULE:LINE (colon-separated, single line)
/// - MODULE:START-END (colon-separated, line range)
/// - MODULE LINE (positional)
/// - MODULE --line LINE (flag-based)
///
/// Returns (target, line_selection) where line_selection is Some if specified by any method.
fn parse_target_and_line(
    target: Option<String>,
    line_positional: Option<u32>,
    line_flag: Option<u32>,
) -> Result<(Option<String>, Option<LineSelection>), String> {
    // Check for colon syntax in target
    if let Some(ref t) = target {
        if let Some(colon_pos) = t.rfind(':') {
            let module_part = &t[..colon_pos];
            let line_part = &t[colon_pos + 1..];

            // Check for conflicts first
            if line_positional.is_some() || line_flag.is_some() {
                // Only error if the colon syntax actually has a valid line/range
                if line_part.parse::<u32>().is_ok() || line_part.contains('-') {
                    return Err(
                        "cannot specify line both in target (MODULE:LINE) and separately"
                            .to_string(),
                    );
                }
            }

            // Try to parse as a range (START-END)
            if let Some(dash_pos) = line_part.find('-') {
                let start_part = &line_part[..dash_pos];
                let end_part = &line_part[dash_pos + 1..];

                if let (Ok(start), Ok(end)) = (start_part.parse::<u32>(), end_part.parse::<u32>()) {
                    if start > end {
                        return Err(format!(
                            "invalid line range: start ({}) must be <= end ({})",
                            start, end
                        ));
                    }
                    return Ok((
                        Some(module_part.to_string()),
                        Some(LineSelection::Range(start, end)),
                    ));
                }
            }

            // Try to parse as a single line number
            if let Ok(line) = line_part.parse::<u32>() {
                return Ok((
                    Some(module_part.to_string()),
                    Some(LineSelection::Single(line)),
                ));
            }
        }
    }

    // Check for conflicts between positional and flag
    if line_positional.is_some() && line_flag.is_some() {
        return Err(
            "cannot specify line both as positional argument and with --line flag".to_string(),
        );
    }

    // Use positional if provided, otherwise flag
    let line = line_positional.or(line_flag).map(LineSelection::Single);
    Ok((target, line))
}

fn validate_verbose_flag(
    verbose: bool,
    line_selection: &Option<LineSelection>,
) -> Result<(), String> {
    if verbose && !matches!(line_selection, Some(LineSelection::Single(_))) {
        return Err(
            "--verbose requires a single line selection via TARGET:LINE or --line LINE".to_string(),
        );
    }
    Ok(())
}

fn validate_activations_flag(activations: Option<u32>) -> Result<(), String> {
    if matches!(activations, Some(0)) {
        return Err("--activations must be at least 1".to_string());
    }
    Ok(())
}

fn validate_goal_flag(goal: Option<usize>) -> Result<(), String> {
    if matches!(goal, Some(0)) {
        return Err("--goal must be at least 1".to_string());
    }
    Ok(())
}

fn validate_goal_requires_single_line(
    goal: Option<usize>,
    line_selection: &Option<LineSelection>,
) -> Result<(), String> {
    if goal.is_some() && !matches!(line_selection, Some(LineSelection::Single(_))) {
        return Err(
            "--goal requires a single line selection via TARGET:LINE or --line LINE".to_string(),
        );
    }
    Ok(())
}

fn filter_selected_goals(
    goal_infos: Vec<GoalInfo>,
    goal_index: Option<usize>,
) -> Result<(Vec<GoalInfo>, Option<usize>), String> {
    match goal_index {
        None => Ok((goal_infos, None)),
        Some(goal_number) => {
            if goal_number > goal_infos.len() {
                return Err(format!(
                    "goal {} is out of range for this location (found {} goal{})",
                    goal_number,
                    goal_infos.len(),
                    if goal_infos.len() == 1 { "" } else { "s" }
                ));
            }
            Ok((
                vec![goal_infos.into_iter().nth(goal_number - 1).unwrap()],
                Some(goal_number),
            ))
        }
    }
}

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Debug, Parser)]
#[clap(
    name = "acorn",
    about = "A theorem prover and programming language",
    long_about = "Acorn is a theorem prover and programming language.\n\nYou can:\n- Run a language server for IDE integration\n- Verify theorems and proofs\n- Generate documentation\n- Generate training data",
    version = env!("CARGO_PKG_VERSION")
)]
struct Args {
    /// Set the directory to look for acornlib
    #[clap(
        long,
        global = true,
        help = "Set the directory to look for acornlib.",
        value_name = "DIR"
    )]
    lib: Option<String>,

    #[clap(subcommand)]
    command: Option<Command>,
}

// Note that we cannot use flags named "--update" or "--clean" because those get intercepted by the JS wrapper.
#[derive(Debug, Subcommand)]
enum Command {
    /// Run the language server for IDE integration
    Serve {
        /// The root folder the user has open
        #[clap(long)]
        workspace_root: Option<String>,

        /// The root folder of the extension
        #[clap(long)]
        extension_root: String,
    },

    /// Generate documentation
    Docs {
        /// Directory to generate documentation in
        #[clap(value_name = "DIR")]
        dir: String,
    },

    /// Verify theorems and proofs (default)
    Verify {
        /// Target module or file to verify (can be a filename, module name, or module:line)
        #[clap(
            value_name = "TARGET",
            help = "Module or filename to verify. Supports TARGET:LINE syntax. If not provided, verifies all files in the library. If \"-\" is provided, it reads from stdin."
        )]
        target: Option<String>,

        /// Line number as positional argument (alternative to --line)
        #[clap(value_name = "LINE")]
        line_positional: Option<u32>,

        /// Ignore manifest hash checks and reprocess unchanged modules
        #[clap(
            long = "ignore-hash",
            alias = "nohash",
            help = "Ignore manifest hash checks and reprocess unchanged modules."
        )]
        ignore_hash: bool,

        /// Verify without writing results to the cache
        #[clap(
            long = "read-only",
            help = "Verify without writing results to the cache."
        )]
        read_only: bool,

        /// Search for a proof at a specific line number (requires target)
        #[clap(
            long = "line",
            help = "Search for a proof at a specific line number.",
            value_name = "LINE"
        )]
        line_flag: Option<u32>,

        /// Exit immediately on the first verification failure
        #[clap(long, help = "Exit immediately on the first verification failure.")]
        fail_fast: bool,

        /// Reject any use of the axiom keyword
        #[clap(
            long,
            default_value = "false",
            help = "Reject any use of the axiom keyword."
        )]
        strict: bool,

        /// Timeout in seconds for proof search (default: 5)
        #[clap(
            long,
            help = "Timeout in seconds for proof search.",
            value_name = "SECONDS"
        )]
        timeout: Option<f32>,

        /// Maximum number of non-factual activations before stopping the search
        #[clap(
            long,
            help = "Maximum number of non-factual activations before stopping the search.",
            value_name = "COUNT"
        )]
        activations: Option<u32>,

        /// Print the activated proof steps and final contradiction details for a single selected goal
        #[clap(
            long,
            help = "Print the activated proof steps and final contradiction details for a single selected goal."
        )]
        verbose: bool,
    },

    /// Check all goals, erroring if any goal requires a search
    #[clap(alias = "reverify")]
    Check {
        /// Target module or file to check (can be a filename, module name, or module:line)
        #[clap(
            value_name = "TARGET",
            help = "Module or filename to check. Supports TARGET:LINE syntax. If not provided, checks all files in the library."
        )]
        target: Option<String>,

        /// Line number as positional argument (alternative to --line)
        #[clap(value_name = "LINE")]
        line_positional: Option<u32>,

        /// Search for a proof at a specific line number (requires target)
        #[clap(
            long = "line",
            help = "Search for a proof at a specific line number.",
            value_name = "LINE"
        )]
        line_flag: Option<u32>,

        /// Use a specific certificate instead of the cached one (requires line)
        #[clap(
            long,
            help = "Use a specific certificate (JSON format) instead of the cached one.",
            value_name = "CERT"
        )]
        cert: Option<String>,
    },

    /// Re-prove goals without using the cache
    Reprove {
        /// Target module or file to reprove (can be a filename, module name, module:line, or module:start-end)
        #[clap(
            value_name = "TARGET",
            help = "Module or filename to reprove. Supports TARGET:LINE and TARGET:START-END syntax for single line or line range. If not provided, reproves all files in the library."
        )]
        target: Option<String>,

        /// Line number as positional argument (alternative to --line)
        #[clap(value_name = "LINE")]
        line_positional: Option<u32>,

        /// Search for a proof at a specific line number (requires target)
        #[clap(
            long = "line",
            help = "Search for a proof at a specific line number.",
            value_name = "LINE"
        )]
        line_flag: Option<u32>,

        /// 1-based goal index when the selected line has multiple goals
        #[clap(
            long = "goal",
            help = "1-based goal index when the selected line has multiple goals.",
            value_name = "INDEX"
        )]
        goal: Option<usize>,

        /// Exit immediately on the first verification failure
        #[clap(long, help = "Exit immediately on the first verification failure.")]
        fail_fast: bool,

        /// Timeout in seconds for proof search (default: 5)
        #[clap(
            long,
            help = "Timeout in seconds for proof search.",
            value_name = "SECONDS"
        )]
        timeout: Option<f32>,

        /// Maximum number of non-factual activations before stopping the search
        #[clap(
            long,
            help = "Maximum number of non-factual activations before stopping the search.",
            value_name = "COUNT"
        )]
        activations: Option<u32>,

        /// Save reproved results to the cache
        #[clap(long = "save-results", help = "Save reproved results to the cache.")]
        save_results: bool,

        /// Visit modules in reverse alphabetical order during a whole-project reprove
        #[clap(
            long,
            help = "Visit modules in reverse alphabetical order during a whole-project reprove."
        )]
        reverse: bool,

        /// Print the activated proof steps and final contradiction details for a single selected goal
        #[clap(
            long,
            help = "Print the activated proof steps and final contradiction details for a single selected goal."
        )]
        verbose: bool,
    },

    /// Display proof details for a specific line
    Select {
        /// Module or file to select from (can be module name, filename, or module:line)
        #[clap(value_name = "MODULE")]
        module: String,

        /// Line number as positional argument (alternative to --line or :LINE suffix)
        #[clap(value_name = "LINE")]
        line_positional: Option<u32>,

        /// Line number to select
        #[clap(long = "line", help = "Line number to select.", value_name = "LINE")]
        line_flag: Option<u32>,

        /// 1-based goal index when the selected line has multiple goals
        #[clap(
            long = "goal",
            help = "1-based goal index when the selected line has multiple goals.",
            value_name = "INDEX"
        )]
        goal: Option<usize>,
    },

    /// Remove redundant claims from a module or entire project
    Clean {
        /// Module name to clean (if not provided, cleans all modules in the project)
        #[clap(value_name = "MODULE")]
        module: Option<String>,
    },

    /// Print every citation statement in the library
    Citations,

    /// List all module names in the library
    List,

    /// Export all definitions, theorems, and types to JSONL
    Export {
        /// Output directory for exported files
        #[clap(long, default_value = "export")]
        output_dir: String,

        /// Only export a specific module
        #[clap(long)]
        module: Option<String>,

        /// Pretty-print JSON output
        #[clap(long)]
        pretty: bool,

        /// Include type annotations for identifiers in statements and proofs
        #[clap(long)]
        type_annotations: bool,

        /// Include proof-level dependencies (which lemmas are used in proofs)
        #[clap(long)]
        proof_deps: bool,

        /// Include elaborated proof lines (explicit numerals, resolved types)
        #[clap(long)]
        elaborated: bool,

        /// Enable all optional export fields
        #[clap(long)]
        full: bool,
    },
}

#[tokio::main]
async fn main() {
    // Initialize tracing subscriber with env filter
    // Use RUST_LOG env var to control log levels, e.g.:
    //   RUST_LOG=acorn::processor=debug cargo run -- verify
    //   RUST_LOG=acorn::processor=trace cargo run -- verify
    tracing_subscriber::registry()
        .with(fmt::layer().with_ansi(false).without_time())
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("warn")))
        .init();

    let args = Args::parse();

    let current_dir = if let Some(lib_dir) = &args.lib {
        std::path::PathBuf::from(lib_dir)
    } else {
        match std::env::current_dir() {
            Ok(dir) => dir,
            Err(e) => {
                println!("Error getting current directory: {}", e);
                std::process::exit(1);
            }
        }
    };

    match args.command {
        Some(Command::Serve {
            workspace_root,
            extension_root,
        }) => {
            let server_args = ServerArgs {
                workspace_root,
                extension_root,
            };
            run_server(&server_args).await;
        }

        Some(Command::Docs { dir }) => {
            let mut project = Project::new_local(&current_dir, ProjectConfig::default())
                .unwrap_or_else(|e| {
                    println!("Error loading project: {}", e);
                    std::process::exit(1);
                });
            project.add_src_targets();
            match DocGenerator::new(&project).generate(&dir) {
                Ok(count) => {
                    println!("{} files generated in {}", count, dir);
                }
                Err(e) => {
                    println!("Error generating documentation: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Some(Command::Verify {
            target,
            line_positional,
            ignore_hash,
            read_only,
            line_flag,
            fail_fast,
            strict,
            timeout,
            activations,
            verbose,
        }) => {
            let (target, line_sel) = match parse_target_and_line(target, line_positional, line_flag)
            {
                Ok(result) => result,
                Err(e) => {
                    println!("Error: {}", e);
                    std::process::exit(1);
                }
            };

            if let Err(e) = validate_verbose_flag(verbose, &line_sel) {
                println!("Error: {}", e);
                std::process::exit(1);
            }
            if let Err(e) = validate_activations_flag(activations) {
                println!("Error: {}", e);
                std::process::exit(1);
            }

            // Verify command doesn't support line ranges
            let line_selection = match line_sel {
                Some(LineSelection::Single(line)) => Some(VerifierLineSelection::Single(line)),
                Some(LineSelection::Range(_, _)) => {
                    println!("Error: verify command does not support line ranges");
                    std::process::exit(1);
                }
                None => None,
            };

            let config = ProjectConfig {
                use_filesystem: true,
                read_cache: true,
                write_cache: !read_only,
            };

            let mut verifier = match Verifier::new(current_dir, config, target) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.print_proof = line_selection.is_some();
            verifier.builder.verbose = verbose;
            verifier.line_selection = line_selection;
            verifier.builder.check_mode = false;
            verifier.builder.strict = strict;
            verifier.builder.check_hashes = !ignore_hash && !strict;
            verifier.exit_on_warning = fail_fast;
            if let Some(t) = timeout {
                verifier.builder.timeout_secs = t;
            }
            if let Some(limit) = activations {
                verifier.builder.activation_limit = limit as i32;
            }

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Check {
            target,
            line_positional,
            line_flag,
            cert,
        }) => {
            let (target, line_sel) = match parse_target_and_line(target, line_positional, line_flag)
            {
                Ok(result) => result,
                Err(e) => {
                    println!("Error: {}", e);
                    std::process::exit(1);
                }
            };

            // Check command doesn't support line ranges
            let line_selection = match line_sel {
                Some(LineSelection::Single(line)) => Some(VerifierLineSelection::Single(line)),
                Some(LineSelection::Range(_, _)) => {
                    println!("Error: check command does not support line ranges");
                    std::process::exit(1);
                }
                None => None,
            };

            // Validate that cert requires line
            if cert.is_some() && line_selection.is_none() {
                println!("Error: --cert requires a line number to be set");
                std::process::exit(1);
            }

            let config = ProjectConfig {
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
            };

            let mut verifier = match Verifier::new(current_dir, config, target) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.print_proof = false;
            verifier.line_selection = line_selection;
            verifier.builder.check_mode = true;
            verifier.builder.check_hashes = false;
            verifier.builder.operation_verb = "checked";

            // Parse and set the certificate override if provided
            if let Some(cert_json) = cert {
                match serde_json::from_str::<acorn::certificate::Certificate>(&cert_json) {
                    Ok(certificate) => {
                        verifier.builder.cert_override = Some(certificate);
                    }
                    Err(e) => {
                        println!("Error parsing certificate JSON: {}", e);
                        std::process::exit(1);
                    }
                }
            }

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Reprove {
            target,
            line_positional,
            line_flag,
            goal,
            fail_fast,
            timeout,
            activations,
            save_results,
            reverse,
            verbose,
        }) => {
            let (target, line_sel) = match parse_target_and_line(target, line_positional, line_flag)
            {
                Ok(result) => result,
                Err(e) => {
                    println!("Error: {}", e);
                    std::process::exit(1);
                }
            };

            if let Err(e) = validate_verbose_flag(verbose, &line_sel) {
                println!("Error: {}", e);
                std::process::exit(1);
            }
            if let Err(e) = validate_activations_flag(activations) {
                println!("Error: {}", e);
                std::process::exit(1);
            }
            if let Err(e) = validate_goal_flag(goal) {
                println!("Error: {}", e);
                std::process::exit(1);
            }
            if let Err(e) = validate_goal_requires_single_line(goal, &line_sel) {
                println!("Error: {}", e);
                std::process::exit(1);
            }

            // Convert to verifier's LineSelection type - reprove supports both single lines and ranges
            let line_selection = match line_sel {
                Some(LineSelection::Single(line)) => Some(VerifierLineSelection::Single(line)),
                Some(LineSelection::Range(start, end)) => {
                    Some(VerifierLineSelection::Range(start, end))
                }
                None => None,
            };

            // --save-results with a line selection doesn't make sense:
            // it would overwrite the full module cache with only the selected lines.
            if save_results && line_selection.is_some() {
                println!("Error: --save-results cannot be used with a line number selection");
                std::process::exit(1);
            }

            // Reprove doesn't read from cache; optionally writes with --save-results
            let config = ProjectConfig {
                use_filesystem: true,
                read_cache: false,
                write_cache: save_results,
            };

            let mut verifier = match Verifier::new(current_dir, config, target) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.print_proof = line_selection.is_some();
            verifier.builder.verbose = verbose;
            verifier.line_selection = line_selection;
            verifier.goal_index = goal;
            verifier.builder.check_mode = false; // Run search like verify does
            verifier.builder.check_hashes = false; // Don't skip based on hashes
            verifier.builder.reverse_targets = reverse;
            verifier.builder.operation_verb = "reproved";
            verifier.exit_on_warning = fail_fast;
            if let Some(t) = timeout {
                verifier.builder.timeout_secs = t;
            }
            if let Some(limit) = activations {
                verifier.builder.activation_limit = limit as i32;
            }

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Select {
            module,
            line_positional,
            line_flag,
            goal,
        }) => {
            let (module, line_sel) =
                match parse_target_and_line(Some(module), line_positional, line_flag) {
                    Ok((Some(m), l)) => (m, l),
                    Ok((None, _)) => {
                        println!("Error: module is required");
                        std::process::exit(1);
                    }
                    Err(e) => {
                        println!("Error: {}", e);
                        std::process::exit(1);
                    }
                };
            if let Err(e) = validate_goal_flag(goal) {
                println!("Error: {}", e);
                std::process::exit(1);
            }

            // Select command doesn't support line ranges
            let line = match line_sel {
                Some(LineSelection::Single(l)) => l,
                Some(LineSelection::Range(_, _)) => {
                    println!("Error: select command does not support line ranges");
                    std::process::exit(1);
                }
                None => {
                    println!("Error: line number is required for select command");
                    std::process::exit(1);
                }
            };

            let mut project = Project::new_local(&current_dir, ProjectConfig::default())
                .unwrap_or_else(|e| {
                    println!("Error loading project: {}", e);
                    std::process::exit(1);
                });

            // Add target and resolve path, same way as verify does
            let path = if module.ends_with(".ac") {
                // Treat as a filename
                let path = std::path::PathBuf::from(&module);
                if let Err(e) = project.add_target_by_path(&path) {
                    println!("Error loading module: {}", e);
                    std::process::exit(1);
                }
                path
            } else {
                // Treat as a module name
                if let Err(e) = project.add_target_by_name(&module) {
                    println!("Error loading module '{}': {}", module, e);
                    std::process::exit(1);
                }
                match project.path_from_module_name(&module) {
                    Ok(path) => path,
                    Err(e) => {
                        println!("Error resolving module '{}': {}", module, e);
                        std::process::exit(1);
                    }
                }
            };

            match project.handle_selection(&path, line - 1) {
                Ok((goal_infos, _range)) => {
                    let (goal_infos, selected_goal_number) =
                        match filter_selected_goals(goal_infos, goal) {
                            Ok(result) => result,
                            Err(e) => {
                                println!("Error: {}", e);
                                std::process::exit(1);
                            }
                        };
                    if goal_infos.is_empty() {
                        println!("No goals found at this location.");
                    } else {
                        for (i, goal_info) in goal_infos.iter().enumerate() {
                            if let Some(goal_number) = selected_goal_number {
                                println!("Goal {}: {}", goal_number, goal_info.goal_name);
                            } else if goal_infos.len() > 1 {
                                println!("Goal {}: {}", i + 1, goal_info.goal_name);
                            } else {
                                println!("{}", goal_info.goal_name);
                            }
                            println!();

                            if let Some(ref steps) = goal_info.steps {
                                if steps.is_empty() {
                                    println!("Trivial.");
                                } else {
                                    let step_word = if steps.len() == 1 { "step" } else { "steps" };
                                    println!(
                                        "The detailed proof has {} {}:\n",
                                        steps.len(),
                                        step_word
                                    );

                                    // Find the maximum width for statement column
                                    let max_statement_width = steps
                                        .iter()
                                        .map(|s| s.statement.len())
                                        .max()
                                        .unwrap_or(20)
                                        .max(20); // Minimum width of 20

                                    // Print header
                                    println!(
                                        "{:<width$}    Reason",
                                        "Statement",
                                        width = max_statement_width
                                    );

                                    // Print each step
                                    for step in steps {
                                        println!(
                                            "{:<width$}    {}",
                                            step.statement,
                                            step.reason,
                                            width = max_statement_width
                                        );
                                    }
                                }
                            } else {
                                println!("No proof available.");
                            }

                            if i < goal_infos.len() - 1 {
                                println!();
                                println!("---");
                                println!();
                            }
                        }
                    }
                }
                Err(e) => {
                    println!("Error: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Some(Command::Clean { module }) => {
            match module {
                Some(module_name) => {
                    // Clean a specific module
                    let module_spec = ModuleDescriptor::name(&module_name);
                    let cleaner = ModuleCleaner::new(current_dir, module_spec);

                    match cleaner.clean() {
                        Ok(_stats) => {
                            // Stats are already printed by clean()
                        }
                        Err(e) => {
                            println!("Error cleaning module: {:?}", e);
                            std::process::exit(1);
                        }
                    }
                }
                None => {
                    // Clean the entire project
                    let cleaner = ProjectCleaner::new(current_dir);

                    match cleaner.clean() {
                        Ok(_stats) => {
                            // Stats are already printed by clean()
                        }
                        Err(e) => {
                            println!("Error cleaning project: {:?}", e);
                            std::process::exit(1);
                        }
                    }
                }
            }
        }

        Some(Command::Citations) => {
            let mut project = Project::new_local(
                &current_dir,
                ProjectConfig {
                    use_filesystem: true,
                    read_cache: false,
                    write_cache: false,
                },
            )
            .unwrap_or_else(|e| {
                println!("Error loading project: {}", e);
                std::process::exit(1);
            });

            project.add_src_targets();
            let errors = project.errors();
            if !errors.is_empty() {
                for (module_id, error) in errors {
                    let module_name = project
                        .get_module_name_by_id(module_id)
                        .or_else(|| {
                            project
                                .get_module_descriptor(module_id)
                                .map(|descriptor| descriptor.to_string())
                        })
                        .unwrap_or_else(|| module_id.to_string());
                    println!("Error loading {}: {}", module_name, error);
                }
                std::process::exit(1);
            }

            let stdout = io::stdout();
            let mut stdout = stdout.lock();
            for citation in project.citation_statements() {
                if let Err(err) = writeln!(
                    stdout,
                    "{}:{}: {}",
                    citation.path, citation.line, citation.text
                ) {
                    if err.kind() == io::ErrorKind::BrokenPipe {
                        return;
                    }
                    println!("Error writing output: {}", err);
                    std::process::exit(1);
                }
            }
        }

        Some(Command::List) => {
            let (src_dir, build_dir) = Project::find_local_acorn_library(&current_dir)
                .unwrap_or_else(|| {
                    println!(
                        "Could not find acornlib.\n\
                        Please run this from within the acornlib directory.\n\
                        See https://github.com/acornprover/acornlib for details."
                    );
                    std::process::exit(1);
                });

            let project = Project::new(src_dir.clone(), build_dir, ProjectConfig::default())
                .unwrap_or_else(|e| {
                    println!("Error loading project: {}", e);
                    std::process::exit(1);
                });

            let mut module_names = Vec::new();
            for entry in WalkDir::new(&src_dir).into_iter().filter_map(|e| e.ok()) {
                if !entry.file_type().is_file() {
                    continue;
                }

                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) != Some("ac") {
                    continue;
                }

                let descriptor = project.descriptor_from_path(path).unwrap_or_else(|e| {
                    println!("Error reading module '{}': {}", path.display(), e);
                    std::process::exit(1);
                });

                if let ModuleDescriptor::Name(parts) = descriptor {
                    module_names.push(parts.join("."));
                }
            }

            module_names.sort();
            module_names.dedup();

            for module_name in module_names {
                println!("{}", module_name);
            }
        }

        Some(Command::Export {
            output_dir,
            module,
            pretty,
            type_annotations,
            proof_deps,
            elaborated,
            full,
        }) => {
            let mut project = Project::new_local(
                &current_dir,
                ProjectConfig {
                    use_filesystem: true,
                    read_cache: true,
                    write_cache: false,
                },
            )
            .unwrap_or_else(|e| {
                println!("Error loading project: {}", e);
                std::process::exit(1);
            });

            project.add_src_targets();
            let errors = project.errors();
            if !errors.is_empty() {
                for (module_id, error) in errors {
                    let module_name = project
                        .get_module_name_by_id(module_id)
                        .or_else(|| {
                            project
                                .get_module_descriptor(module_id)
                                .map(|descriptor| descriptor.to_string())
                        })
                        .unwrap_or_else(|| module_id.to_string());
                    println!("Error loading {}: {}", module_name, error);
                }
                std::process::exit(1);
            }

            let options = acorn::exporter::ExportOptions {
                pretty,
                type_annotations: type_annotations || full,
                proof_deps: proof_deps || full,
                elaborated: elaborated || full,
            };

            let output_path = std::path::Path::new(&output_dir);
            if let Err(e) =
                acorn::exporter::export_project(&project, output_path, module.as_deref(), &options)
            {
                println!("Export failed: {}", e);
                std::process::exit(1);
            }
        }

        // Default to do a global verify if no subcommand is provided
        None => {
            let mut verifier = match Verifier::new(current_dir, ProjectConfig::default(), None) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.check_mode = false;
            verifier.builder.check_hashes = true;

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use acorn::interfaces::GoalInfo;
    use clap::{error::ErrorKind, Parser};

    use super::{
        filter_selected_goals, validate_activations_flag, validate_goal_flag,
        validate_goal_requires_single_line, validate_verbose_flag, Args, Command, LineSelection,
    };

    #[test]
    fn test_verbose_flag_requires_single_line() {
        assert!(validate_verbose_flag(true, &None).is_err());
        assert!(validate_verbose_flag(true, &Some(LineSelection::Range(10, 12))).is_err());
        assert!(validate_verbose_flag(true, &Some(LineSelection::Single(10))).is_ok());
        assert!(validate_verbose_flag(false, &None).is_ok());
    }

    #[test]
    fn test_activations_flag_requires_positive_count() {
        assert!(validate_activations_flag(Some(0)).is_err());
        assert!(validate_activations_flag(Some(1)).is_ok());
        assert!(validate_activations_flag(None).is_ok());
    }

    #[test]
    fn test_goal_flag_requires_positive_count() {
        assert!(validate_goal_flag(Some(0)).is_err());
        assert!(validate_goal_flag(Some(1)).is_ok());
        assert!(validate_goal_flag(None).is_ok());
    }

    #[test]
    fn test_goal_requires_single_line() {
        assert!(validate_goal_requires_single_line(Some(1), &None).is_err());
        assert!(
            validate_goal_requires_single_line(Some(1), &Some(LineSelection::Range(10, 12)))
                .is_err()
        );
        assert!(
            validate_goal_requires_single_line(Some(1), &Some(LineSelection::Single(10))).is_ok()
        );
        assert!(validate_goal_requires_single_line(None, &None).is_ok());
    }

    #[test]
    fn test_filter_selected_goals_returns_requested_goal() {
        let goals = vec![
            GoalInfo {
                goal_name: "g1".to_string(),
                has_cached_proof: false,
                steps: None,
            },
            GoalInfo {
                goal_name: "g2".to_string(),
                has_cached_proof: false,
                steps: None,
            },
        ];

        let (filtered, selected_goal) = filter_selected_goals(goals, Some(2)).unwrap();
        assert_eq!(selected_goal, Some(2));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].goal_name, "g2");
    }

    #[test]
    fn test_filter_selected_goals_rejects_out_of_range() {
        let goals = vec![GoalInfo {
            goal_name: "g1".to_string(),
            has_cached_proof: false,
            steps: None,
        }];

        let error = filter_selected_goals(goals, Some(2)).unwrap_err();
        assert!(error.contains("out of range"));
    }

    #[test]
    fn test_verify_accepts_renamed_flags() {
        let args = Args::try_parse_from(["acorn", "verify", "--ignore-hash", "--read-only"])
            .expect("verify flags should parse");

        match args.command {
            Some(Command::Verify {
                ignore_hash,
                read_only,
                ..
            }) => {
                assert!(ignore_hash);
                assert!(read_only);
            }
            _ => panic!("unexpected command"),
        }
    }

    #[test]
    fn test_verify_rejects_legacy_flag_aliases() {
        let error = Args::try_parse_from(["acorn", "verify", "--no-cache-skip"]).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::UnknownArgument);

        let error = Args::try_parse_from(["acorn", "verify", "--no-write-cache"]).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::UnknownArgument);
    }

    #[test]
    fn test_reprove_accepts_renamed_save_flag() {
        let args = Args::try_parse_from(["acorn", "reprove", "--save-results"])
            .expect("renamed reprove flag should parse");
        match args.command {
            Some(Command::Reprove { save_results, .. }) => assert!(save_results),
            _ => panic!("unexpected command"),
        }
    }

    #[test]
    fn test_reprove_accepts_reverse_flag() {
        let args =
            Args::try_parse_from(["acorn", "reprove", "--reverse"]).expect("flag should parse");
        match args.command {
            Some(Command::Reprove { reverse, .. }) => assert!(reverse),
            _ => panic!("unexpected command"),
        }
    }

    #[test]
    fn test_reprove_rejects_legacy_save_flag() {
        let error = Args::try_parse_from(["acorn", "reprove", "--write-cache"]).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::UnknownArgument);
    }

    #[test]
    fn test_citations_command_parses() {
        let args =
            Args::try_parse_from(["acorn", "citations"]).expect("citations command should parse");
        assert!(matches!(args.command, Some(Command::Citations)));
    }
}
