#!/usr/bin/env python3

# Script to tag the current version and push it upstream.
#
# To do it step by step:
#   git tag v0.0.1
#   git push upstream v0.0.1

import os
import subprocess
import sys


def get_version():
    # Find VERSION file
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.dirname(script_dir)
    version_file_path = os.path.join(project_root, "VERSION")

    # Read current version
    with open(version_file_path) as f:
        version = f.read().strip()

    return version


def check_uncommitted_changes():
    # Check if there are any uncommitted changes
    result = subprocess.run(
        ["git", "status", "--porcelain"],
        check=True,
        capture_output=True,
        text=True,
    )
    return len(result.stdout.strip()) == 0


def check_upstream_push():
    # Check if there are unpushed commits to upstream master
    try:
        result = subprocess.run(
            ["git", "rev-list", "--count", "upstream/master..HEAD"],
            check=True,
            capture_output=True,
            text=True,
        )
        unpushed_commits = int(result.stdout.strip())
        return unpushed_commits == 0
    except subprocess.CalledProcessError:
        print(
            "Error: Unable to check unpushed commits. Is 'upstream' remote configured?"
        )
        return False


def check_tag_exists(tag):
    # Check if tag already exists
    result = subprocess.run(
        ["git", "tag", "-l", tag],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip() == tag


def main():
    version = get_version()
    tag_name = f"v{version}"
    print(f"Current version: {version}")

    # Check if tag already exists
    if check_tag_exists(tag_name):
        print(f"ERROR: Tag {tag_name} already exists.")
        sys.exit(1)

    # Check if there are uncommitted changes
    if not check_uncommitted_changes():
        print("ERROR: You have uncommitted changes.")
        print("Please commit or stash your changes before creating a tag.")
        sys.exit(1)

    # Check if all commits are pushed to upstream/master
    if not check_upstream_push():
        print("WARNING: You have unpushed commits to upstream/master.")
        print("Please run 'git push upstream master' before creating a tag.")
        sys.exit(1)

    # Create git tag
    try:
        subprocess.run(["git", "tag", tag_name], check=True)
        print(f"Created tag: {tag_name}")
    except subprocess.CalledProcessError as e:
        print(f"Error creating tag: {e}")
        sys.exit(1)

    # Push tag to upstream
    try:
        subprocess.run(["git", "push", "upstream", tag_name], check=True)
        print(f"Pushed tag {tag_name} to upstream")
    except subprocess.CalledProcessError as e:
        print(f"Error pushing tag: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
