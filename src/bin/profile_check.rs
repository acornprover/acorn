// A representative run of the verifier, to use for profiling.
// This does a check run, so you should run it once first to populate the cache.
//
// To profile using samply:
//
//   cargo build --bin=profile_check --profile=fastdev
//   samply record target/fastdev/profile_check

use acorn::{project::ProjectConfig, verifier::Verifier};
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..1 {
        let mut verifier = Verifier::new(current_dir.clone(), ProjectConfig::default(), None)
            .expect("Failed to create verifier");
        verifier.builder.check_mode = true;
        verifier.builder.check_hashes = false;
        verifier.builder.check_jobs = std::thread::available_parallelism()
            .map(|threads| threads.get())
            .unwrap_or(1);

        let output = verifier.run().unwrap();
        if !output.status.is_good() {
            println!("unexpected non-good status. exiting.");
            std::process::exit(1);
        }
    }
}
