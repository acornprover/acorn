// The Acorn CLI.
// You can run a language server, verify a file, or verify the whole project.

use acorn::doc_generator::DocGenerator;
use acorn::project::Project;
use acorn::searcher::Searcher;
use acorn::server::{run_server, ServerArgs};
use acorn::verifier::{ProverMode, Verifier};
use clap::Parser;

#[derive(Parser)]
#[clap(
    name = "acorn",
    about = "A theorem prover and programming language",
    long_about = "Acorn is a theorem prover and programming language.\n\nYou can:\n- Run a language server for IDE integration\n- Verify theorems and proofs\n- Search for proofs at specific locations",
    version = env!("CARGO_PKG_VERSION")
)]
struct Args {
    /// The root folder the user has open (language server mode only)
    #[clap(long, hide = true)]
    workspace_root: Option<String>,

    /// The root folder of the extension (enables language server mode)
    #[clap(long, hide = true)]
    extension_root: Option<String>,

    /// Target module or file to verify (can be a filename or module name)
    #[clap(
        value_name = "TARGET",
        help = "Module or filename to verify. If not provided, verifies all files in the library. If \"-\" is provided, it reads from stdin."
    )]
    target: Option<String>,

    /// Create a dataset from the prover logs
    #[clap(long, help = "Create a dataset from the prover logs.")]
    dataset: bool,

    /// Use proof certificates
    #[clap(long, help = "Use proof certificates.")]
    certs: bool,

    /// Ignore the cache and do a full reverify
    #[clap(long, help = "Ignore the cache and do a full reverify.")]
    full: bool,

    /// Use the cache only for the filtered prover, not for hash checking
    #[clap(
        long,
        help = "Use the cache only for the filtered prover, not for hash checking.",
        conflicts_with = "full"
    )]
    filtered: bool,

    /// Search for a proof at a specific line number (requires target)
    #[clap(
        long,
        help = "Search for a proof at a specific line number.",
        value_name = "LINE"
    )]
    line: Option<u32>,

    /// Generate documentation in the given directory
    #[clap(
        long,
        help = "Generate documentation in the given directory.",
        value_name = "DIR"
    )]
    doc_root: Option<String>,

    // Appends input to a file (can only be used if target is \"-\")
    #[clap(
        long,
        help = "Appends input to a file (can only be used if target is \"-\")"
    )]
    append_to: Option<String>,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();

    // Check for language server mode.
    if let Some(extension_root) = args.extension_root {
        let server_args = ServerArgs {
            workspace_root: args.workspace_root,
            extension_root,
        };
        run_server(&server_args).await;
        return;
    }

    if args.workspace_root.is_some() {
        println!("--workspace-root is only relevant in language server mode.");
        std::process::exit(1);
    }

    let mode = if args.full {
        if args.filtered {
            println!("--full and --filtered are incompatible.");
            std::process::exit(1);
        }
        ProverMode::Full
    } else if args.filtered {
        ProverMode::Filtered
    } else {
        ProverMode::Standard
    };

    let current_dir = match std::env::current_dir() {
        Ok(dir) => dir,
        Err(e) => {
            println!("Error getting current directory: {}", e);
            std::process::exit(1);
        }
    };

    // Check if we should generate documentation.
    if let Some(doc_root) = args.doc_root {
        let mut project =
            Project::new_local(&current_dir, ProverMode::Standard).unwrap_or_else(|e| {
                println!("Error loading project: {}", e);
                std::process::exit(1);
            });
        project.add_all_targets();
        match DocGenerator::new(&project).generate(&doc_root) {
            Ok(count) => {
                println!("{} files generated in {}", count, doc_root);
                return;
            }
            Err(e) => {
                println!("Error generating documentation: {}", e);
                std::process::exit(1);
            }
        }
    }

    // Check if we should run the searcher.
    if let Some(line) = args.line {
        let Some(target) = args.target else {
            println!("Error: --line requires a target module or file to be specified.");
            std::process::exit(1);
        };
        let searcher = Searcher::new(current_dir, mode, target, line);
        if let Err(e) = searcher.run() {
            println!("{}", e);
            std::process::exit(1);
        }
        return;
    }

    // Run the verifier with input appended to a file.
    if let Some(append) = args.append_to {
        let Some(target) = args.target else {
            println!("Error: --append_to requires a target file to be specified.");
            std::process::exit(1);
        };
        if target != "-" {
            println!("Error: target is required to be \"-\".");
            std::process::exit(1);
        }
        let new_target = target + ":" + &append;
        let verifier = Verifier::new(
            current_dir,
            mode,
            Some(new_target),
            args.dataset,
            args.certs,
        );
        match verifier.run() {
            Err(e) => {
                println!("{}", e);
                std::process::exit(1);
            }
            Ok(output) => {
                if !output.is_success() {
                    // Make sure CI-type environments fail.
                    std::process::exit(1);
                }
            }
        }
        return;
    }

    // Run the verifier.
    let verifier = Verifier::new(current_dir, mode, args.target, args.dataset, args.certs);
    match verifier.run() {
        Err(e) => {
            println!("{}", e);
            std::process::exit(1);
        }
        Ok(output) => {
            if !output.is_success() {
                // Make sure CI-type environments fail.
                std::process::exit(1);
            }
        }
    }
}
