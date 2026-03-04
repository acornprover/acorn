---
name: migrate
description: Migrate acornlib certificate/build-cache formats across breaking verifier or proof-format changes. Use when introducing a feature-flagged format change (for example clausification, normalization, or certificate encoding changes) and you need a safe rollout plan with manifest-version gating.
---

# Migrate

## Goal
Perform a safe rollout for breaking acornlib/certificate format changes.

## Workspace Assumptions
- Run these `cargo run ...` commands from the `acorn` repo.
- Edit theorem/proof source files under `~/acornlib/src`.
- Do not run git commands as part of this workflow.
- The human handles commit/push/upstream actions.

## Workflow
1. Gate new behavior behind a feature flag.
- Implement new behavior under a dedicated Cargo feature (example: `ndc`).
- Keep default behavior unchanged.
- Add tests for both modes where behavior is intentionally different.

2. Check whether migration is needed.
- Run:
  `cargo run --profile release --features <feature> -- reverify`
- If this succeeds end-to-end, stop. Do not migrate.

3. If feature-mode reverify fails, start migration mode.
- Bump manifest version by +1 under the feature:
```rust
#[cfg(feature = "<feature>")]
const MANIFEST_VERSION: u32 = N + 1;
#[cfg(not(feature = "<feature>"))]
const MANIFEST_VERSION: u32 = N;
```
- Keep checked-in certificate files (`jsonl`) in the old format during this phase.

4. Run the migration loop until feature-mode prover can regenerate everything.
- Find any proofs the feature-mode automatic prover cannot handle (whole project).
  Run a fail-fast whole-project probe that:
  - does not skip by hashes
  - tries existing certs first
  - falls back to search when needed
  - does not write cache
  Command:
  `cargo run --profile release --features <feature> -- verify --no-cache-skip --no-write-cache --fail-fast`
- Add more detail to the corresponding acornlib theorem proofs.
- Iterate on a single module while fixing:
  - old/default mode, single module, writes cache:
    `cargo run --profile release -- verify <module> --no-cache-skip --fail-fast`
  - feature mode, single module, does not write cache:
    `cargo run --profile release --features <feature> -- verify <module> --no-cache-skip --no-write-cache --fail-fast`
- Keep cert files in old format while iterating.
- Repeat until whole-project feature-mode probe succeeds.
- Then run full feature-mode reverify:
  `cargo run --profile release --features <feature> -- reverify`

5. Freeze proof-content changes and stop for review.
- Stop for user review before flipping defaults.
- Hand off local changes to the human for commit/push.

6. After review, flip default behavior to the new feature.
- Adopt the feature behavior as default in `acorn`.
- Regenerate certs in the new format:
  `verify --no-cache-skip`
- Run final safety check with full cert validation:
  `cargo run --profile release --features validate -- reverify`

7. Perform tied deployment.
- User-only step: the human handles deployment, public communication, and rollout messaging.

8. Cleanup (final).
- Remove obsolete feature-flag paths after deployment stabilizes.
