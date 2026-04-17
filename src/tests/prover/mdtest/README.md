# Markdown Prover Tests

These fixtures are prover smoke tests written as readable Markdown.

- Headings define test case names.
- Each fenced `acorn` or `ac` code block is a separate test case.
- Each case is checked with `verify_succeeds`.
- Keep prose in the file when it helps explain what the proof is exercising.

Run the full suite with:

```sh
cargo test mdtests
```

Narrow to one fixture or heading with:

```sh
ACORN_MDTEST_FILTER=constraints cargo test mdtests -- --nocapture
```
