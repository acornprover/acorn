#!/bin/bash
#
# Does the whole release process.
# By default, picks a version number that just bumps the last number by one.
#
# You can also set a version with:
#   ./scripts/release.sh <version>
#
# but be careful since that flow is rarely exercised.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
current_dir="$(pwd)"
[[ $current_dir == $project_root ]] || { echo "Run this script from the repository root."; exit 1; }

# Exit immediately if any command fails
set -ex

# Handle version update
if [ $# -eq 1 ]; then
    # Use provided version
    VERSION=$1
    ./python/version.py "$VERSION"
else
    # Bump version and capture the new version
    VERSION_OUTPUT=$(./python/version.py bump)
    VERSION=$(echo "$VERSION_OUTPUT" | grep "changed to:" | awk '{print $3}')
fi

# Verify version format (number.number.number)
if ! [[ $VERSION =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "Error: Invalid version format: $VERSION"
    exit 1
fi

echo "New version: $VERSION"

./scripts/crossbuild.sh

# Make sure the uploaded Linux release binary can check the embedded acornlib.
./target/x86_64-unknown-linux-gnu/release/acorn check --lib ./vscode/extension/acornlib

git add .
git commit -m "Releasing version $VERSION"
git push
git push upstream master

# Making the tag will kick off the Windows build.
./python/tag.py

# This creates the release, and hopefully finishes before the Windows build.
./scripts/upload.sh --skip-build

set +x
echo Check the Windows build here:      https://github.com/acornprover/acorn/actions
echo Edit the release description here: https://github.com/acornprover/acorn/releases
echo Publish the extension with:        ./scripts/publish.sh
