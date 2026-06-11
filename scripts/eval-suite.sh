#!/bin/bash
#
# Runs the traced scoring eval suite sequentially.
#
# Examples:
#   ./scripts/eval-suite.sh
#   ./scripts/eval-suite.sh --out tmp/my-eval --skip-build
#   ./scripts/eval-suite.sh --policy depth-first --policy legacy
#   ./scripts/eval-suite.sh --case candidate=model:tmp/models/scorer.onnx

set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }
original_args=("$@")

usage() {
    cat <<EOF
Usage: ./scripts/eval-suite.sh [options]

Runs traced evals sequentially and writes sharded zstd-compressed JSONL
traces under OUT/traces/*.jsonl.zst.

Each run also writes OUT/manifest.txt, git state files, and updates
tmp/acorn-eval-latest to point at the newest run directory.

Options:
  --out DIR        Output directory. Default: tmp/acorn-eval-YYYYMMDD-HHMMSS
  --case SPEC      Case to run. Can be repeated. SPEC is NAME=POLICY[:MODEL].
                   Default: all standard cases.
  --policy NAME    Built-in policy case to run. Can be repeated.
                   Shorthand for --case NAME=NAME.
  --skip-build     Use the existing target/release/acorn binary.
  --trace-shard-rows N
                   Rotate trace files after N JSONL rows.
                   Default: 1000000
  --min-free-gb N  Stop before the next run if less than N GiB is free.
                   Default: 20
  -h, --help       Show this help.

Environment:
  ACORN_BIN        Acorn binary to run. Default: target/release/acorn
EOF
}

timestamp="$(date +%Y%m%d-%H%M%S)"
default_out_dir="tmp/acorn-eval-$timestamp"
out_dir=""
min_free_gb=20
skip_build=""
trace_shard_rows=1000000
case_names=()
case_policies=()
case_models=()
case_specs=()
standard_model="tmp/models/model-20260610a.onnx"

add_case() {
    local name="$1"
    local policy="$2"
    local model="${3:-}"

    [[ -n "$name" ]] || { echo "Error: case name must not be empty"; exit 1; }
    [[ -n "$policy" ]] || { echo "Error: case policy must not be empty"; exit 1; }
    [[ "$name" =~ ^[A-Za-z0-9._-]+$ ]] || {
        echo "Error: invalid case name '$name'. Use letters, numbers, dot, underscore, or dash."
        exit 1
    }

    case_names+=("$name")
    case_policies+=("$policy")
    case_models+=("$model")
    if [[ -n "$model" ]]; then
        case_specs+=("$name=$policy:$model")
    else
        case_specs+=("$name=$policy")
    fi
}

add_case_spec() {
    local spec="$1"
    [[ "$spec" == *=* ]] || { echo "Error: --case requires NAME=POLICY[:MODEL]"; exit 1; }
    local name="${spec%%=*}"
    local rest="${spec#*=}"
    local policy="$rest"
    local model=""
    if [[ "$rest" == *:* ]]; then
        policy="${rest%%:*}"
        model="${rest#*:}"
    fi
    add_case "$name" "$policy" "$model"
}

add_standard_cases() {
    add_case "legacy" "legacy"
    add_case "depth-first" "depth-first"
    add_case "handcrafted" "handcrafted"
    add_case "legacy-no-shallow" "legacy-no-shallow"
    add_case "model-20260610a" "model" "$standard_model"
    add_case "model-20260610a-no-shallow" "model-no-shallow" "$standard_model"
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --out)
            [[ $# -ge 2 ]] || { echo "Error: --out requires a directory"; exit 1; }
            out_dir="$2"
            shift 2
            ;;
        --case)
            [[ $# -ge 2 ]] || { echo "Error: --case requires NAME=POLICY[:MODEL]"; exit 1; }
            add_case_spec "$2"
            shift 2
            ;;
        --policy)
            [[ $# -ge 2 ]] || { echo "Error: --policy requires a policy name"; exit 1; }
            add_case "$2" "$2"
            shift 2
            ;;
        --skip-build)
            skip_build="1"
            shift
            ;;
        --trace-shard-rows)
            [[ $# -ge 2 ]] || { echo "Error: --trace-shard-rows requires a number"; exit 1; }
            [[ "$2" =~ ^[1-9][0-9]*$ ]] || { echo "Error: --trace-shard-rows must be a positive integer"; exit 1; }
            trace_shard_rows="$2"
            shift 2
            ;;
        --min-free-gb)
            [[ $# -ge 2 ]] || { echo "Error: --min-free-gb requires a number"; exit 1; }
            [[ "$2" =~ ^[0-9]+$ ]] || { echo "Error: --min-free-gb must be an integer"; exit 1; }
            min_free_gb="$2"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "Error: unknown argument: $1"
            usage
            exit 1
            ;;
    esac
done

if [[ ${#case_names[@]} -eq 0 ]]; then
    add_standard_cases
fi

for i in "${!case_names[@]}"; do
    model="${case_models[$i]}"
    if [[ -n "$model" && ! -f "$model" ]]; then
        echo "Error: model for case '${case_names[$i]}' does not exist: $model"
        exit 1
    fi
done

if [[ -z "$out_dir" ]]; then
    out_dir="$default_out_dir"
    suffix=1
    while [[ -e "$out_dir" ]]; do
        out_dir="$default_out_dir-$suffix"
        suffix=$((suffix + 1))
    done
elif [[ -e "$out_dir" ]] && [[ -n "$(find "$out_dir" -mindepth 1 -print -quit)" ]]; then
    echo "Error: output directory already exists and is not empty: $out_dir"
    exit 1
fi

acorn_bin="${ACORN_BIN:-target/release/acorn}"

mkdir -p "$out_dir/logs" "$out_dir/status" "$out_dir/traces"

out_abs="$out_dir"
if [[ "$out_abs" != /* ]]; then
    out_abs="$project_root/$out_abs"
fi

latest_link="$project_root/tmp/acorn-eval-latest"
mkdir -p "$project_root/tmp"
if [[ -e "$latest_link" && ! -L "$latest_link" ]]; then
    echo "Not updating latest link because it exists and is not a symlink: $latest_link"
else
    ln -sfn "$out_abs" "$latest_link"
fi

write_run_metadata() {
    local phase="$1"
    local manifest_file="$out_dir/manifest.txt"

    {
        printf "phase=%s\n" "$phase"
        printf "created_at=%s\n" "$(date -Is)"
        printf "project_root=%s\n" "$project_root"
        printf "output_directory=%s\n" "$out_abs"
        printf "latest_link=%s\n" "$latest_link"
        printf "command="
        printf "%q " "$0" "${original_args[@]}"
        printf "\n"
        printf "cases="
        printf "%s " "${case_specs[@]}"
        printf "\n"
        printf "standard_model=%s\n" "$standard_model"
        printf "acorn_bin=%s\n" "$acorn_bin"
        printf "skip_build=%s\n" "${skip_build:-0}"
        printf "trace_shard_rows=%s\n" "$trace_shard_rows"
        printf "min_free_gb=%s\n" "$min_free_gb"
        printf "hostname=%s\n" "$(hostname 2>/dev/null || true)"
        printf "uname=%s\n" "$(uname -a 2>/dev/null || true)"
        printf "cargo_version=%s\n" "$(cargo --version 2>/dev/null || true)"
        printf "rustc_version=%s\n" "$(rustc --version 2>/dev/null || true)"
        printf "ACORN_BIN_ENV=%s\n" "${ACORN_BIN-}"
        printf "ACORNLIB_ENV=%s\n" "${ACORNLIB-}"
        printf "ACORN_LIB_ENV=%s\n" "${ACORN_LIB-}"
        printf "RUST_LOG_ENV=%s\n" "${RUST_LOG-}"
        if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
            printf "git_branch=%s\n" "$(git rev-parse --abbrev-ref HEAD 2>/dev/null || true)"
            printf "git_commit=%s\n" "$(git rev-parse HEAD 2>/dev/null || true)"
            if [[ -n "$(git status --porcelain 2>/dev/null)" ]]; then
                printf "git_dirty=1\n"
            else
                printf "git_dirty=0\n"
            fi
        fi
        if [[ -x "$acorn_bin" ]]; then
            printf "acorn_binary_sha256=%s\n" "$(sha256sum "$acorn_bin" 2>/dev/null | awk '{ print $1 }')"
        fi
        for i in "${!case_names[@]}"; do
            case_name="${case_names[$i]}"
            safe_case_name="$(printf "%s" "$case_name" | tr -c 'A-Za-z0-9_' '_')"
            printf "case_%s_policy=%s\n" "$safe_case_name" "${case_policies[$i]}"
            if [[ -n "${case_models[$i]}" ]]; then
                printf "case_%s_model=%s\n" "$safe_case_name" "${case_models[$i]}"
                printf "case_%s_model_sha256=%s\n" "$safe_case_name" "$(sha256sum "${case_models[$i]}" 2>/dev/null | awk '{ print $1 }')"
            fi
        done
    } > "$manifest_file"

    git status --short > "$out_dir/git-status.txt" 2>&1 || true
    git diff > "$out_dir/git-diff.patch" 2>/dev/null || true
    git diff --cached > "$out_dir/git-diff-staged.patch" 2>/dev/null || true
    git submodule status > "$out_dir/git-submodule-status.txt" 2>&1 || true
}

write_run_metadata "starting"

if [[ -z "$skip_build" ]]; then
    build_log="$out_dir/logs/build.log"
    echo "Building release binary..."
    if ! cargo build --profile release > "$build_log" 2>&1; then
        write_run_metadata "build-failed"
        echo "Build failed. See $build_log"
        exit 1
    fi
fi

[[ -x "$acorn_bin" ]] || { write_run_metadata "missing-binary"; echo "Error: missing executable: $acorn_bin"; exit 1; }
write_run_metadata "running"

free_gb() {
    df -Pk "$out_dir" | awk 'NR == 2 { print int($4 / 1024 / 1024) }'
}

print_run_summary() {
    local log_file="$1"
    grep -E "benchmark searches succeeded|search success rate|average search time|searches found inconsistent assumptions|Build failed|Evaluation completed|Evaluation succeeded" "$log_file" || true
}

trace_file_bytes() {
    local pattern="$1"
    local bytes=0
    local file
    shopt -s nullglob
    for file in $pattern; do
        bytes=$((bytes + $(stat -c '%s' "$file")))
    done
    shopt -u nullglob
    printf "%s\n" "$bytes"
}

any_failed=0
stopped_early=0

echo "Output directory: $out_dir"
echo "Cases: ${case_specs[*]}"
echo "Minimum free space: ${min_free_gb}GiB"
echo

for i in "${!case_names[@]}"; do
    case_name="${case_names[$i]}"
    policy="${case_policies[$i]}"
    model="${case_models[$i]}"
    free_before="$(free_gb)"
    if [[ "$free_before" -lt "$min_free_gb" ]]; then
        echo "Stopping before $case_name: only ${free_before}GiB free."
        stopped_early=1
        break
    fi

    log_file="$out_dir/logs/trace-$case_name.log"
    status_file="$out_dir/status/trace-$case_name.status"
    trace_file="$out_dir/traces/$case_name.jsonl.zst"
    trace_pattern="$out_dir/traces/$case_name-[0-9][0-9][0-9][0-9][0-9][0-9].jsonl.zst"

    echo "[$(date -Is)] Starting case: $case_name ($policy)"
    start="$(date -Is)"
    cmd=("$acorn_bin" eval --policy "$policy" --policy-label "$case_name" --trace-out "$trace_file" --trace-shard-rows "$trace_shard_rows" --timing)
    if [[ -n "$model" ]]; then
        cmd+=(--model "$model")
    fi
    "${cmd[@]}" > "$log_file" 2>&1
    status=$?
    end="$(date -Is)"

    trace_bytes="$(trace_file_bytes "$trace_pattern")"

    {
        printf "case=%s\n" "$case_name"
        printf "policy=%s\n" "$policy"
        printf "model=%s\n" "$model"
        printf "start=%s\n" "$start"
        printf "end=%s\n" "$end"
        printf "exit_status=%s\n" "$status"
        printf "log=%s\n" "$log_file"
        printf "trace_pattern=%s\n" "$trace_pattern"
        printf "trace_bytes=%s\n" "$trace_bytes"
    } > "$status_file"

    echo "[$end] Finished case: $case_name (exit $status, trace ${trace_bytes} bytes)"
    print_run_summary "$log_file"
    df -h "$out_dir"
    echo

    if [[ "$status" -ne 0 ]]; then
        any_failed=1
        if grep -Eiq "No space left on device|ENOSPC|could not flush trace file|could not create trace file" "$log_file"; then
            echo "Stopping after $case_name because the log indicates a trace/disk write failure."
            stopped_early=1
            break
        fi
    fi
done

echo "Run directory:"
du -sh "$out_dir"
echo
echo "Trace files:"
du -h "$out_dir"/traces/*.jsonl.zst 2>/dev/null || true
echo
echo "Status files:"
for status_file in "$out_dir"/status/*.status; do
    [[ -f "$status_file" ]] || continue
    echo "--- $status_file"
    cat "$status_file"
done

if [[ "$stopped_early" -ne 0 ]]; then
    write_run_metadata "stopped-early"
    exit 2
fi

if [[ "$any_failed" -ne 0 ]]; then
    write_run_metadata "completed-with-failures"
    exit 1
fi

write_run_metadata "completed"
exit 0
