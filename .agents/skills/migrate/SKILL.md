---
name: migrate
description: Use when asked to migrate to a feature flag or roll out a manifest-gated acornlib certificate/build-cache or proof-format change. This skill covers feature-flag migrations, including the state-machine workflow for verifier, proof, and cache migrations.
---

# Migrate

## Goal
Perform a safe rollout for feature-flag migrations and other breaking acornlib/certificate format changes.

## Workspace Assumptions
- Run these `cargo run ...` commands from the `acorn` repo.
- Treat the sibling `acornlib` repo as `../acornlib` relative to the `acorn` repo root.
- Edit theorem/proof source files under `../acornlib/src`.
- Use the edit tool for proof-file changes (do not use ad-hoc shell text mutation commands).
- Read-only git commands are allowed (`status`, `log`, `show`, `diff`, etc.).
- Do not run mutating git commands as part of this workflow (`add`, `commit`, `push`, `pull`, `merge`, `rebase`, `cherry-pick`, `reset`, `checkout`).
- The human handles commit/push/upstream actions.
- In sandboxed Codex runs, any command expected to write `../acornlib/build/*` must be run with escalated permissions.
- After every cache-writing command, confirm writes actually happened with `git -C ../acornlib status --short`.

## Write Verification Protocol (Mandatory)
For any step that is expected to update `../acornlib/build`:
1. Run the command (with escalated permissions in sandboxed runs).
2. Immediately run `git -C ../acornlib status --short`.
3. If no expected write evidence appears, treat it as a failed step (usually permissions) and rerun with escalated permissions.
4. Do not advance state until write evidence is confirmed.

## Preflight (Mandatory Before S0)
Before running the migration state machine:
- Confirm tests pass in default mode:
  - `cargo test`
- Confirm tests pass in feature mode:
  - `cargo test --features <feature>`
- If either test run fails, stop and fix that baseline issue before starting migration.

## Workflow (Strict State Machine)
Treat migration as a state machine. Do not skip states. Do not run commands from later states early.

## Panic Rule (Critical)
- Any panic from feature-mode `verify` is an immediate transition to `S_blocked_feature_bug`.
- On such a panic, stop proof migration immediately.
- Do **not** continue theorem/proof edits, proof reshaping, or module-loop retries after the panic.
- Do **not** treat the panic as a normal proof failure even if it appears proof-shape-dependent or disappears after a rewrite.
- First collect the blocked-condition diagnostics, then debug the prover/feature implementation.

### State S0: Feature Prepared
Preconditions:
- New behavior is behind `--features <feature>`.
- Default behavior is unchanged.
- Local tests for feature and default modes exist where needed.

Transition command:
- `cargo run --profile release --features <feature> -- check`

Outcomes:
- If success: go to `S_done_no_migration`.
- If failure: go to `S1_enable_manifest_gate`.

### State S1: Enable Manifest Gate
When entered:
- Any time `S0` feature-mode `check` fails.

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
- Ensure newly generated feature-mode certs are immediately checkable.

Required command:
- `cargo run --profile release --features <feature>,validate -- verify --ignore-hash --read-only --fail-fast`

Outcomes:
- If success: go to `S4` (ready for review, then flag flip).
- If failure: go to `S3_probe`.
- If this command panics (for example, "newly generated cert should be checkable"), stop immediately and go to `S_blocked_feature_bug`. Do **not** inspect/edit proofs after the panic.

Hard guard:
- Do **not** inspect/edit theorem proofs before this probe fails.

### State S3_probe: Identify Failing Module/Theorem
Purpose:
- Start one fix-loop iteration from an `S2` failure.

Actions:
- Extract failing module/theorem/line from the failing output.
- Reproduce quickly with no-write checks:
  - `cargo run --profile release -- verify <module> --ignore-hash --read-only --fail-fast`
  - `cargo run --profile release --features <feature>,validate -- verify <module> --ignore-hash --read-only --fail-fast`

Outcomes:
- If failure is reproduced in feature mode: go to `S3_edit`.
- If not reproducible (flaky/stale): go back to `S2_probe`.
- If feature-mode verify panics, stop immediately and go to `S_blocked_feature_bug`. Do **not** continue the migration loop.

### State S3_edit: Edit Proofs
Purpose:
- Make minimal source edits for the currently failing target.

Actions:
- Inspect proof detail in default mode only:
  - `cargo run --profile release -- select MODULENAME LINENUMBER`
- Edit files under `../acornlib/src` using the edit tool.
- Add statements only; do not delete existing statements.
- Good explication sources:
  - definitions
  - theorems
  - boolean reduction
  - simplification
- Placement rule:
  - before target line, or at end of `by` block if target line has one.

Next state:
- `S3_check`.

### State S3_check: Validate Edited Module
Purpose:
- Validate the current module in both modes before looping.

Required commands:
- Default mode module check (no-write):
  - `cargo run --profile release -- verify <module> --ignore-hash --read-only --fail-fast`
- Feature mode module check (no-write):
  - `cargo run --profile release --features <feature>,validate -- verify <module> --ignore-hash --read-only --fail-fast`

Conditional command:
- If and only if this iteration included explicit edits under `../acornlib/src` for this module:
  - `cargo run --profile release -- verify <module> --ignore-hash --fail-fast`
  - then confirm write evidence with `git -C ../acornlib status --short`.

Permission note:
- In sandboxed Codex runs, run the conditional cache-writing check with escalated permissions.
- If a cache-writing check is expected to update `../acornlib/build` but no files change, do not continue; rerun with escalated permissions and re-check write evidence.

Outcomes:
- If both no-write module checks pass: go to `S3_decide`.
- If feature-mode module check fails: go back to `S3_edit`.
- If default-mode module check fails after edits: go back to `S3_edit`.
- If feature-mode verify panics, stop immediately and go to `S_blocked_feature_bug`. Do **not** continue proof edits for that target.

### State S3_decide: Loop Decision
Purpose:
- Decide whether to continue module loop or exit to review.

Required command:
- `cargo run --profile release --features <feature>,validate -- verify --ignore-hash --read-only --fail-fast`

Outcomes:
- If success: go to `S4`.
- If failure on another target: go to `S3_probe`.
- If repeated attempts on same target are not converging: go to `S_blocked_feature_bug`.
- If feature-mode verify panics, stop immediately and go to `S_blocked_feature_bug`. Do **not** continue migration work in `S3_*`.

Hard guard:
- During all `S3_*` states, feature-mode `check` may fail on old cert format. Do not use it as pass/fail.

Blocked-condition diagnostics (required when entering `S_blocked_feature_bug`):
- collect these before any further proof edits
- failing module and line/theorem
- exact failing command used
- error output
- whether failure was a panic in feature+validate verify
- whether default-mode module verify passes for the same target
- any minimal reduced repro you can extract
- likely subsystem suspects (parser/elaboration/clausification/reduction/checker/prover)

### State S4: Review Checkpoint
Entry conditions:
- Arrived from `S2` success after:
  - feature-mode `check` failed
  - manifest gate was enabled
  - feature-mode prover probe succeeded
- No proof edits are required in this path; migration is ready for review and potential flag flip.

Required:
- Stop and hand off for human review before any default flip.
- Confirm default-mode whole-project verifiability (without writing cache):
  - `cargo run --profile release -- verify --ignore-hash --read-only --fail-fast`
- If there are `../acornlib/src` proof changes, human reviews them and then merges/pushes upstream first.
- Human handles all commit/push/upstream communication.
- In the S4 report, state explicitly:
  - "acornlib is verifiable both with and without the flag"
  - "we're ready for the flip"
  - "this is the final pre-flip review checkpoint"

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
  - `cargo run --profile release -- verify --ignore-hash`
- Final validation:
  - `cargo run --profile release --features validate -- check`

Permission note:
- In sandboxed Codex runs, run regeneration with escalated permissions.
- After regeneration, verify expected cache updates with `git -C ../acornlib status --short`.
- If regeneration reports success but write evidence is missing, treat it as failed and rerun regeneration with escalated permissions.

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
- Migration loop (`S3_probe`/`S3_edit`/`S3_check`/`S3_decide`) is blocked by a likely feature bug.
- No further proof migration should be attempted until the panic/feature bug is understood.

Required report:
- current state = `S_blocked_feature_bug`
- include diagnostics gathered in `S3` blocked-condition exit
- next state = wait for user direction / bugfix work

### Terminal State: S_done_no_migration
Meaning:
- Feature-mode `check` succeeded in `S0`.
- No migration work is required.

Required report:
- current state = `S_done_no_migration`
- command run = `cargo run --profile release --features <feature> -- check`
- result = success
- next state = none (stop)

### Reporting Contract (Mandatory)
After each state transition, report:
- current state
- command run
- pass/fail result
- next state

Never report progress without naming the current state.
