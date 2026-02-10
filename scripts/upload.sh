#!/bin/bash
# Creates a draft release and uploads the language server binaries and extension.
# Add the --clobber flag to overwrite any existing files.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }

# Exit immediately if any command fails
set -ex

# We always want an up-to-date build, and it's cached so it won't slow us down to redo this.
./scripts/crossbuild.sh

# Default value: empty
CLOBBER=""

# Parse CLI arguments
for arg in "$@"; do
  if [ "$arg" == "--clobber" ]; then
    echo "clobbering."
    CLOBBER="--clobber"
    break
  fi
done

VERSION=`cat VERSION`
[[ $VERSION =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo "bad version"; exit 1; }
TAG="v$VERSION"

# Map between the Node and Rust ways of describing platforms
declare -A MAP=(
  ["linux-x64"]="x86_64-unknown-linux-gnu"
  ["darwin-arm64"]="aarch64-apple-darwin"
)

# Create the draft release
gh release create $TAG --draft --title "$TAG" --notes "Automated release for version $VERSION"
# Wait a little bit for the release to actually be created.
sleep 5

# Use files/release for renaming
[[ -d files ]] || { echo "missing files directory"; exit 1; }
mkdir -p files/release
rm -f files/release/*

for key in "${!MAP[@]}"; do
    if [[ $key == *"win32"* ]]; then
        suffix=".exe"
    fi
    node=$key
    remote_name="acorn-$VERSION-$node$suffix"
    rust=${MAP[$node]}
    local_name="target/$rust/release/acorn$suffix"
    [[ -f $local_name ]] || { echo "missing $local_name"; exit 1; }
    cp $local_name files/release/$remote_name
    gh release upload $TAG files/release/$remote_name $CLOBBER
done

# Be sure to rebuild the assistant
cd vscode/assistant
npm install
npm run build
cd ../..

# Rebuild the extension and release the vsix
cd vscode/extension
npm install
npm run build
vsce package
gh release upload $TAG acornprover-$VERSION.vsix $CLOBBER
cd ../..