# Certificate Format

Certificates are stored as JSONL. Each line proves one goal and contains a compact
proof trace under `p`:

```json
{"goal":"goal","p":[{"c":"p and q"},{"r":"br","c":"p","f":[0],"k":"pos_and_left","i":0}]}
```

Top-level fields:

- `goal`: the normalized goal text.
- `p`: the proof trace. This field is omitted only for placeholder records.

Each proof trace step has:

- `r`: the checker rule. Omitted means `claim`.
- `c`: the Acorn-readable claim or witness declaration, when the rule needs one.
- `f`: premise step indexes, when the rule needs explicit premises.
- `g`: when present on a step, the step targets the generic clause parsed from
  `c`; otherwise it targets the specialized clause.
- `k`: exact boolean-reduction kind for `br` steps.
- `i`: exact literal index for `br` steps.

Current rules:

- `fact`: direct source/environment fact lookup.
- `claim`: direct exact/egraph lookup.
- `br`: one explicit boolean reduction from a previous step.
- `br_intro`: a claim accepted because the current checker state already
  contains the needed boolean-reduction closure.
- `eq`: local equality-graph check from listed premises.
- `er`: one equality-resolution step from a previous step.
- `ef`: one equality-factoring step from a previous step.
- `ext`: one extensionality step from a previous step.
- `inj`: one injectivity step from a previous step.
- `inst`: instantiate a generic claim from a previous step.
- `wit`: certificate-local witness declaration.
- `contra`: final contradiction marker.

Certificate generation first converts the prover proof into concrete checker
steps, then serializes that trace. If trace construction fails, generation fails;
there is no fallback proof payload.
