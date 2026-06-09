#!/bin/bash
#
# Runs the traced scoring eval suite sequentially.
#
# Examples:
#   ./scripts/eval-suite.sh
#   ./scripts/eval-suite.sh --out tmp/my-eval --skip-build
#   ./scripts/eval-suite.sh --policy depth-first --policy onnx

set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }

usage() {
    cat <<EOF
Usage: ./scripts/eval-suite.sh [options]

Runs traced evals sequentially and writes gzip-compressed JSONL traces
under OUT/traces/*.jsonl.gz.

Options:
  --out DIR        Output directory. Default: tmp/acorn-eval-YYYYMMDD-HHMMSS
  --policy NAME    Policy to run. Can be repeated.
                   Default: onnx depth-first handcrafted onnx-no-shallow
  --skip-build     Use the existing target/release/acorn binary.
  --min-free-gb N  Stop before the next run if less than N GiB is free.
                   Default: 20
  -h, --help       Show this help.

Environment:
  ACORN_BIN        Acorn binary to run. Default: target/release/acorn
EOF
}

timestamp="$(date +%Y%m%d-%H%M%S)"
out_dir="tmp/acorn-eval-$timestamp"
min_free_gb=20
skip_build=""
policies=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --out)
            [[ $# -ge 2 ]] || { echo "Error: --out requires a directory"; exit 1; }
            out_dir="$2"
            shift 2
            ;;
        --policy)
            [[ $# -ge 2 ]] || { echo "Error: --policy requires a policy name"; exit 1; }
            policies+=("$2")
            shift 2
            ;;
        --skip-build)
            skip_build="1"
            shift
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

if [[ ${#policies[@]} -eq 0 ]]; then
    policies=(onnx depth-first handcrafted onnx-no-shallow)
fi

acorn_bin="${ACORN_BIN:-target/release/acorn}"

if [[ -z "$skip_build" ]]; then
    cargo build --profile release || exit 1
fi

[[ -x "$acorn_bin" ]] || { echo "Error: missing executable: $acorn_bin"; exit 1; }

mkdir -p "$out_dir/logs" "$out_dir/status" "$out_dir/traces"

free_gb() {
    df -Pk "$out_dir" | awk 'NR == 2 { print int($4 / 1024 / 1024) }'
}

print_run_summary() {
    local log_file="$1"
    grep -E "benchmark searches succeeded|search success rate|average search time|searches found inconsistent assumptions|Build failed|Evaluation completed|Evaluation succeeded" "$log_file" || true
}

any_failed=0
stopped_early=0

echo "Output directory: $out_dir"
echo "Policies: ${policies[*]}"
echo "Minimum free space: ${min_free_gb}GiB"
echo

for policy in "${policies[@]}"; do
    free_before="$(free_gb)"
    if [[ "$free_before" -lt "$min_free_gb" ]]; then
        echo "Stopping before $policy: only ${free_before}GiB free."
        stopped_early=1
        break
    fi

    log_file="$out_dir/logs/trace-$policy.log"
    status_file="$out_dir/status/trace-$policy.status"
    trace_file="$out_dir/traces/$policy.jsonl.gz"

    echo "[$(date -Is)] Starting policy: $policy"
    start="$(date -Is)"
    "$acorn_bin" eval --policy "$policy" --trace-out "$trace_file" --timing > "$log_file" 2>&1
    status=$?
    end="$(date -Is)"

    trace_bytes=0
    if [[ -f "$trace_file" ]]; then
        trace_bytes="$(stat -c '%s' "$trace_file")"
    fi

    {
        printf "policy=%s\n" "$policy"
        printf "start=%s\n" "$start"
        printf "end=%s\n" "$end"
        printf "exit_status=%s\n" "$status"
        printf "log=%s\n" "$log_file"
        printf "trace=%s\n" "$trace_file"
        printf "trace_bytes=%s\n" "$trace_bytes"
    } > "$status_file"

    echo "[$end] Finished policy: $policy (exit $status, trace ${trace_bytes} bytes)"
    print_run_summary "$log_file"
    df -h "$out_dir"
    echo

    if [[ "$status" -ne 0 ]]; then
        any_failed=1
        if grep -Eiq "No space left on device|ENOSPC|could not flush trace file|could not create trace file" "$log_file"; then
            echo "Stopping after $policy because the log indicates a trace/disk write failure."
            stopped_early=1
            break
        fi
    fi
done

echo "Run directory:"
du -sh "$out_dir"
echo
echo "Trace files:"
du -h "$out_dir"/traces/*.jsonl "$out_dir"/traces/*.jsonl.gz 2>/dev/null || true
echo
echo "Status files:"
for status_file in "$out_dir"/status/*.status; do
    [[ -f "$status_file" ]] || continue
    echo "--- $status_file"
    cat "$status_file"
done

if [[ "$stopped_early" -ne 0 ]]; then
    exit 2
fi

if [[ "$any_failed" -ne 0 ]]; then
    exit 1
fi

exit 0
