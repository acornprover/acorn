# The release process

To do a full release, you need a Linux machine. The Linux and Mac builds happen locally, and then
GitHub Actions will handle the Windows build.

## Linux/Mac release builds

You can build for both Linux and Mac, from Linux.
You will need these dependencies.

All commands are run from `~/acorn`.

Mac support:

Download a [Mac OS X SDK](https://github.com/joseluisq/macosx-sdks)
somewhere, then symlink to it from `~/macsdk`.

```bash
rustup target add aarch64-apple-darwin
snap install zig --classic --beta
cargo install --locked cargo-zigbuild
```

## The typical release process

When we create a new release, we release a new language server, and then a new VSCode extension.

All commands are run from `~/acorn`.

1. Before you release, consider whether you also want to update the built-in copy of acornlib. If you do:

   ```
   cd vscode/extension/acornlib
   git pull origin master
   cd ../../..
   ```

   Then check in the updated submodule reference and merge it upstream.

2. Release to GitHub.

   ```
   ./scripts/release.sh
   ```

   This should locally build Linux and Mac, create a draft release, upload some files, and trigger a Windows release build. It pushes a new version file to GitHub, so if something goes wrong, you
   will need to muck around to fix it.

   Check that the [GitHub Actions](https://github.com/acornprover/acorn/actions) succeed.
   They might take 7-8 minutes. At the end of it, the GitHub release should be moved out of "draft".

   Once the release moves out of "draft", the CLI will pick it up.

   Meanwhile, you can edit the release description [here](https://github.com/acornprover/acorn/releases).

3. If the tests fail

   Figure out the tag, something like `v0.1.2`.

   Delete the draft release at https://github.com/acornprover/acorn/releases .

   ```
   # Delete the old tag
   TAG=v...
   git tag -d $TAG
   git push --delete upstream $TAG

   # Rebuild
   ./scripts/crossbuild.sh
   ./python/tag.py
   ./scripts/upload.sh
   ```

   Then check the build: https://github.com/acornprover/acorn/actions
   Edit the new release description: https://github.com/acornprover/acorn/releases

4. Publish the extension to the Visual Studio Marketplace.

   ```bash
   ./scripts/publish.sh
   ```

   This makes the VS Code extension pick up the release.
