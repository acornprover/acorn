// A representative cached-proof verify run, to use for profiling.
// This mirrors `acorn verify --ignore-hash --read-only`: read certificates
// from the cache, reprocess every module, and avoid writing cache updates.
//
// To profile using samply:
//
//   cargo build --bin=profile_verify --profile=fastdev
//   samply record target/fastdev/profile_verify

use acorn::{
    project::{ProjectConfig, UsageMode},
    verifier::Verifier,
};
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..1 {
        let config = ProjectConfig {
            usage_mode: UsageMode::Verify,
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let mut verifier =
            Verifier::new(current_dir.clone(), config, None).expect("Failed to create verifier");
        verifier.builder.check_mode = false;
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
