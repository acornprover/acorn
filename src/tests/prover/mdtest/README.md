# Markdown Prover Tests

These fixtures are prover smoke tests written as readable Markdown.

- Headings define test case names.
- Each fenced `acorn` or `ac` code block is a separate test case.
- By default, success cases run `verify`, write certificate cache files, and
  then run `check` against that cache.
- Use `acorn success` or `ac success` when you want to mark success explicitly.
- Use `acorn fail` or `ac fail` for cases that should not verify.
- Use `acorn eval-handcrafted` for cases that should verify, seed a cache, and
  then succeed under eval replay with the handcrafted scoring policy and skip=0.
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
