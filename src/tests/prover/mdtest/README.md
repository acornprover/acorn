# Markdown Prover Tests

These fixtures are prover smoke tests written as readable Markdown.

- Headings define test case names.
- Each fenced `acorn` or `ac` code block is a separate test case.
- Each case is checked with `verify_succeeds`.
- Keep prose in the file when it helps explain what the proof is exercising.
- Group cases by semantic topic, not by whether they were found as regressions.
- Prefer existing topical files. If you need a new file, name it for the behavior under test.

Run the full suite with:

```sh
cargo test mdtests
```

Narrow to one fixture or heading with:

```sh
ACORN_MDTEST_FILTER=constraints cargo test mdtests -- --nocapture
```
