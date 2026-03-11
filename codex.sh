#!/bin/bash
set -euo pipefail

# Run Codex from this repo's root and grant writable access to the sibling
# ../acornlib checkout so the agent can inspect and edit both trees.
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$script_dir" rev-parse --show-toplevel)"
acornlib_dir="$(cd -- "$repo_root/.." && pwd)/acornlib"

exec codex -C "$repo_root" --add-dir "$acornlib_dir" "$@"
