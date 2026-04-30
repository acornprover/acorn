// A representative target-module load, to use for profiling verifier setup.
// This loads real.double_sum and its dependencies, then exits before build/check/search.
//
// To profile using samply:
//
//   cargo build --bin=profile_load --profile=fastdev
//   samply record target/fastdev/profile_load

use acorn::project::{Project, ProjectConfig};
use mimalloc::MiMalloc;
use std::hint::black_box;
use std::time::{Duration, Instant};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

// The module to test on.
const MODULE: &str = "real.double_sum";

fn format_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 1.0 {
        format!("{:.3}s", seconds)
    } else {
        format!("{:.1}ms", seconds * 1000.0)
    }
}

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    let total_start = Instant::now();

    let project_start = Instant::now();
    let mut project = Project::new_local(&current_dir, ProjectConfig::default())
        .expect("failed to create project");
    let project_time = project_start.elapsed();

    let target_start = Instant::now();
    project
        .add_target_by_name(MODULE)
        .expect("failed to load target module");
    let target_time = target_start.elapsed();

    let module_count = project.iter_modules().count();
    let target_count = project.targets.len();
    black_box(&project);

    println!("profile_load target: {}", MODULE);
    println!("project setup: {}", format_duration(project_time));
    println!("  cache load: {}", format_duration(project.cache_load_time));
    println!("target/dependency load: {}", format_duration(target_time));
    println!("total measured: {}", format_duration(total_start.elapsed()));
    println!("modules loaded: {}", module_count);
    println!("targets: {}", target_count);
}
