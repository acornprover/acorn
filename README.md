# acorn

The core implementation of the Acorn language.

## Who should use this repository?

There are several ways to use Acorn.

If you are using Acorn for your own project, all you need is the Acorn extension for VS Code. You don't need this repository.

If you are contributing mathematics to the Acorn Library, you only need the
[acornlib repository](https://github.com/acornprover/acornlib). You don't need this repository.

If you are making changes to the Acorn language, its theorem prover, or to the UI of the VS Code extension, then keep reading.

## Installing acorn from source

Fork this repository, then clone the fork to your local machine with submodules. These instructions
will assume you have this repository cloned in `~/acorn`.

Install rust and node, then verify tests pass locally:

```bash
cd ~/acorn
git submodule update --init
cargo test -q
```

If there are any errors, submit an issue.

Then, install dependencies for the VS Code extension.

```bash
cd ~/acorn/vscode/extension
npm install
cd ~/acorn/vscode/assistant
npm install
```

## Running the prover

Open up this repository in VS Code. You can open this exact file, if you like, and keep reading from within VS Code. You'll use this instance of VS Code to make changes to the prover or the extension.

Hit F5. This will open up a new VS Code window. This new window is called the "extension development host". Use it to open `~/acorn/acornlib`, or another acornlib checkout. This is where you'll test out your local changes.

## Code Overview

The guts of Acorn are written in Rust. Those files are mostly [here](./src).

If you'd like to add something new to the language, the best way to start might be to make sure it parses, by adding a new [environment test](./src/tests/env_parsing_test.rs). Then run the tests with `cargo test -q`, you'll see where it fails, and you can proceed from there. The next step is to make sure it behaves like you want, by adding a new [prover test](./src/tests/prover_language_test.rs).

Other interesting parts of the code:

- The [Acorn binary](./src/bin/acorn.rs) is the entry point to Rust logic from the command line.

- The [Acorn language server](./src/bin/server.rs) handles asynchronous proving in VS Code.

- The [VS Code extension](./vscode/extension) runs within VS Code, and handles communication between the user and the language server.

- The [Acorn Assistant](./vscode/assistant) is a small webapp that runs as its own virtual document within VS Code.

- The [model training process](./python) uses PyTorch and outputs an ONNX model that the Rust code can import to use at runtime.

- The [release process document](./RELEASE.md) explains how to release a new version of all this.
