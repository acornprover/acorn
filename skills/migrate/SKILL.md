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
- Use the edit tool for proof-file changes (do not use ad-hoc shell text mutation commands).
- Do not run git commands as part of this workflow.
- The human handles commit/push/upstream actions.

## Workflow (Strict State Machine)
Treat migration as a state machine. Do not skip states. Do not run commands from later states early.

### State S0: Feature Prepared
Preconditions:
- New behavior is behind `--features <feature>`.
- Default behavior is unchanged.
- Local tests for feature and default modes exist where needed.

Transition command:
- `cargo run --profile release --features <feature> -- reverify`

Outcomes:
- If success: go to `S_done_no_migration`.
- If failure: go to `S1_enable_manifest_gate`.

### State S1: Enable Manifest Gate
When entered:
- Any time `S0` feature-mode `reverify` fails.

Required change:
```rust
#[cfg(feature = "<feature>")]
const MANIFEST_VERSION: u32 = N + 1;
#[cfg(not(feature = "<feature>"))]
const MANIFEST_VERSION: u32 = N;
```

Rule:
- Keep checked-in certificate files (`jsonl`) in old format during migration loop.

Next state:
- `S2_probe`.

### State S2: Whole-Project Prover Probe
Purpose:
- Check whether feature-mode prover can regenerate proofs without touching cache.

Required command:
- `cargo run --profile release --features <feature> -- verify --no-cache-skip --no-write-cache --fail-fast`

Outcomes:
- If success: go to `S4` (ready for review, then flag flip).
- If failure: go to `S3_fix_loop`.

Hard guard:
- Do **not** inspect/edit theorem proofs before this probe fails.

### State S3: Module-Level Fix Loop
Loop until whole-project probe succeeds.

For each failing theorem/module:
- Inspect proof detail in default mode only:
  - `cargo run --profile release -- select MODULENAME LINENUMBER`
- Edit files under `~/acornlib/src` using the edit tool.
- Add statements only; do not delete existing statements.
- Good explication sources:
  - definitions
  - theorems
  - boolean reduction
  - simplification
- Placement rule:
  - before target line, or at end of `by` block if target line has one.

Per-iteration checks:
- Default mode module check (writes cache):
  - `cargo run --profile release -- verify <module> --no-cache-skip --fail-fast`
- Feature mode module check (no cache writes):
  - `cargo run --profile release --features <feature> -- verify <module> --no-cache-skip --no-write-cache --fail-fast`

Exit condition:
- Whole-project feature probe succeeds:
  - `cargo run --profile release --features <feature> -- verify --no-cache-skip --no-write-cache --fail-fast`

Hard guard:
- During this phase, feature-mode `reverify` may fail on old cert format. Do not use it as pass/fail.

Blocked-condition exit:
- If a module/theorem cannot be made to pass in feature mode after reasonable proof-explication attempts, treat this as a likely feature bug (not a proof-gap-only issue).
- Do not keep looping blindly. Exit the fix loop and report to the user with diagnostics.
- Gather and report:
  - failing module and line/theorem
  - exact failing command used
  - error output
  - whether default-mode module verify passes for the same target
  - any minimal reduced repro you can extract
  - likely subsystem suspects (parser/elaboration/clausification/reduction/checker/prover)
- Next state on this path:
  - `S_blocked_feature_bug`

### State S4: Review Checkpoint
Entry conditions:
- Arrived from `S2` success after:
  - feature-mode `reverify` failed
  - manifest gate was enabled
  - feature-mode prover probe succeeded
- No proof edits are required in this path; migration is ready for review and potential flag flip.

Required:
- Stop and hand off for human review before any default flip.
- If there are `~/acornlib/src` proof changes, human reviews them and then merges/pushes upstream first.
- Human handles all commit/push/upstream communication.

Next state:
- `S5_flip_default` only after review approval and upstream `acornlib` updates are in.

### State S5: Flip Default + Regenerate
Preconditions:
- `acorn` is up to date with `master`.
- `acornlib` is up to date with `master` (including any reviewed migration proof edits from `S4`).

Actions:
- Adopt feature behavior as default in `acorn`.
- Remove obsolete feature-flag code paths for this migration.
- Regenerate certs in new format:
  - `cargo run --profile release -- verify --no-cache-skip`
- Final validation:
  - `cargo run --profile release --features validate -- reverify`

Next state:
- `S6_deploy_ready`

### Terminal State: S6_deploy_ready
Meaning:
- Flip/default regeneration/validation work is complete and ready for user-led deployment.

Actions:
- User handles tied deploy/public rollout messaging.

Required report:
- current state = `S6_deploy_ready`
- result = migration implementation complete; waiting for user deployment steps
- next state = none (stop)

### Terminal State: S_blocked_feature_bug
Meaning:
- Migration loop (`S3`) is blocked by a likely feature bug.

Required report:
- current state = `S_blocked_feature_bug`
- include diagnostics gathered in `S3` blocked-condition exit
- next state = wait for user direction / bugfix work

### Terminal State: S_done_no_migration
Meaning:
- Feature-mode `reverify` succeeded in `S0`.
- No migration work is required.

Required report:
- current state = `S_done_no_migration`
- command run = `cargo run --profile release --features <feature> -- reverify`
- result = success
- next state = none (stop)

### Reporting Contract (Mandatory)
After each state transition, report:
- current state
- command run
- pass/fail result
- next state

Never report progress without naming the current state.
