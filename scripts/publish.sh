#!/bin/bash
# Publish the VS Code extension

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }

# Exit immediately if any command fails
set -e

if [ -n "$(git status --porcelain)" ]; then
  echo "Error: working tree has uncommitted changes"
  git status --short
  exit 1
fi

# Get local version from VERSION file
local_version=$(cat VERSION)

# Get latest GitHub release version
latest_github_version=$(curl -s https://api.github.com/repos/acornprover/acorn/releases/latest | grep '"tag_name":' | sed -E 's/.*"([^"]+)".*/\1/')

# Check that versions match
if [ "v$local_version" != "$latest_github_version" ]; then
  echo "Error: Version mismatch"
  echo "VERSION file has: $local_version"
  echo "Latest GitHub release is: $latest_github_version"
  exit 1
fi

# Proceed with publishing
set -x
cd vscode/extension
# Delete all existing .vsix files before publishing
rm -f *.vsix
vsce publish
