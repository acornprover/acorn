## Instructions

- When writing Rust code, before telling the user you're finished, you should run the tests, check, and autoformat:
  `cargo test`
  `cargo check`
  `cargo fmt`

- If we make changes to the normalizer or the kernel, we should run a full reverify to ensure we didn't
  break anything.
  `cargo run --profile release --features validate -- reverify`

  This verifies the code in `~/acornlib`, which you can inspect to figure out verification failures.

- If a unit test breaks, but just in the verifier or prover, we should try to add another,
  narrower unit test, that catches the problem in the underlying data structure.

- If we run into an error during reverification, to debug it, it can help to
  run the reverification just on the module that failed at a higher log level. For example:
  `RUST_LOG=acorn=trace cargo run --profile release -- reverify list.list_base`

- To evaluate performance, we should do a release build:

  `cargo build --profile release`

  and then see how long it takes to run the commands:

  `time cargo run --profile release -- reverify`
  `time cargo run --profile release -- reprove real.double_sum`

  This is important to do if we are doing something performance-sensitive, like altering the basic Term
  structure, or changing how one of the key EqualityGraph / Pdt / FingerprintX data structures work.

- A "full reprove" is slow, but sometimes finds obscure bugs that nothing else finds. We generally
  only want to do this when the user asks for it:

  `cargo run --profile release --features validate -- reprove`

  When you do a full reprove, it's okay if some propositions can't be verified. What indicates a real problem is if the prover crashes.

- If we find errors during a "reverify" or "reprove" operation, we should add a unit test that catches
  this case.

## Project Structure

- `/src` - Core Rust implementation
- `/vscode` - VS Code extension and assistant interface
- `/python` - Training scripts for the scoring model

## Versioning

- The "acornlib manifest version" is defined by `MANIFEST_VERSION` in `src/manifest.rs`. Bump this when making breaking changes to the build format.
