# Prover Scoring

This document records what we learned from the June 2026 eval instrumentation and
policy-ablation pass, plus the current shape of the prover scoring code. It is meant as
context for future work on proof-search heuristics.

## Summary

There are two broad levers for making the prover scale:

- retrieval, or premise selection: put fewer initial facts into the passive set
- scoring, or activation policy: choose better passive clauses to activate first

Both are worth improving eventually. The current data points to scoring first, because the
largest measured cost is active inference after activation, not the mechanical cost of inserting
facts into the passive set. A better activation policy can find proofs with fewer activations,
especially fewer irrelevant factual assumption activations. That directly attacks the dominant
runtime bucket while keeping the proof search more complete than an early retrieval filter.

This should not be interpreted as "the ONNX file is the whole policy." The current ONNX model is
only one part of the activation policy. The policy also has hardcoded ordering in the default
configuration, no ability to reject or budget facts, and training infrastructure that is only
indirectly connected to the live eval metric.

The first configurability step has now landed: `acorn eval --policy` can run several activation
policies without code edits, and `--policy model --model PATH` can evaluate a trained ONNX scorer
with its exported `*.features.json` contract. That immediately exposed two important facts:

- the trained `model-20260611-e50-h512-l3` checkpoint narrowly beats `depth-first` on the full
  eval, and is now the embedded default policy.
- alternate policies exercised proof and certificate paths the default policy rarely reached.
  The initially reduced certificate and stack-growth bugs have now been fixed.

## Current Eval Harness

`acorn eval` is a useful outer benchmark for scoring work. In eval mode, `Builder`:

- forces prover search instead of trusting cached proofs
- disables module hash skipping
- runs configured skip modes, defaulting to `0` and `1`
- accepts `--policy` to select the activation queue policy
- accepts `--model` for external ONNX scorer policies and `--policy-label` for stable trace case
  names
- accepts `--trace-out` to write search traces as `.jsonl.zst`
- accepts `--trace-shard-rows` to rotate trace output into independent `.jsonl.zst` shards for
  later parallel conversion
- compares current source goals against cached proof targets
- records per-search `SearchStats`

Eval success counts successful prover outcomes. That includes `Outcome::Success` and
`Outcome::Inconsistent`; finding an inconsistency is useful evidence that the prover reached a
decisive result. Regular verify/search behavior still treats unexpected inconsistencies as warnings.

The trace exporter is intentionally eval-shaped:

- `--trace-out PATH` writes one `acorn-activated-step-trace-v2` JSON object per activated step
  from eval searches; paths must end in `.jsonl.zst`
- a sidecar metadata file next to the trace, for example
  `model-20260611-e50-h512-l3.meta.json` for
  `model-20260611-e50-h512-l3.jsonl.zst`,
  records the numeric feature-vector names once
- each record includes module/goal/skip/policy/outcome metadata, stable `goal_bucket`, activation
  index, passive id, active id, queue score/order fields, rule, truthiness, the current numeric
  `feature_vector`, and a `used_in_final_proof` label derived from the final proof dependency
  closure
- failed-search rows have their real `outcome` and `used_in_final_proof=false`, because there is no
  final proof dependency closure
- records do not currently include a named per-row `features` object; feature names live only in
  the sidecar metadata file
- unactivated passive candidates are not labeled, because we do not know whether they would have
  been useful if selected later
This trace format is intentionally closer to an activated-step feature/label export than a stable
raw event log. `feature_vector` is a wide, versioned feature catalog: Rust computes many candidate
features, traces store all of them with names in metadata, Python chooses model-specific feature
subsets by name, and exported models record the exact feature names/order they expect.

The skip modes give two related benchmark shapes:

- `skip=0` searches at the current point in the file
- nonzero skip modes use an `EvalSkipTail` checkpoint before recent plain anonymous claims

Empty cached proofs are omitted for `skip=0`. They can still matter for nonzero skip modes,
where a later claim may be used as the benchmark target while the search context comes from an
earlier checkpoint.

This makes eval a better metric than offline training loss. A scoring change should be judged by
eval success rate, average search time, activation counts, generated candidates, and the timing
buckets above.

The current policy options are:

- `model-20260611-e50-h512-l3`: the default embedded ONNX scorer, with shallow-first ordering
- `handcrafted`: the old hand-written scorer, with shallow-first ordering
- `depth-first`: constant scorer, so queue ties fall back to insertion/order structure, with
  shallow-first ordering
- `model`: an external ONNX scorer loaded from `--model`, with shallow-first ordering
- `model-no-shallow`: an external ONNX scorer loaded from `--model`, with shallow status removed
  from the ordinary ordering key

The scoring config is threaded through `Builder`, `Processor`, `Prover`, and `PassiveSet`, so eval
workers can carry both a policy and an optional external model path. `scripts/eval-suite.sh` runs
the standard traced cases by default:

- `model-20260611-e50-h512-l3`
- `depth-first`
- `model-20260610a`
- `model-20260610a-no-shallow`
- `model-20260611-e20-h256-l3`

The current external comparison model cases point at:

- `model-20260610a`: `tmp/models/model-20260610a.onnx`
- `model-20260611-e20-h256-l3`: `tmp/models/model-20260611-e20-h256-l3.onnx`

For quick iteration, `./scripts/eval-suite.sh --fast` passes
`acorn eval --eval-sample 0-4,90-94` to every case. The sample uses the same stable goal buckets as
training validation: buckets `0-4` are trainable-bucket goals, while buckets `90-94` are
validation-bucket goals.

## Current Scoring Architecture

The activation queue lives in `PassiveSet`. New proof steps are scored in batches:

1. `PassiveSet::push_batch` builds `Features` for each `ProofStep`.
2. `Score::batch` asks the configured `Scorer` for a float score and applies the configured
   `ScoringPolicy`.
3. `PassiveSet` stores `(Score, clause_id)` in a `BTreeSet`.
4. `PassiveSet::pop_with_shallow` pops the highest ordered score for normal activation.
5. `PassiveSet::pop_shallow` is used by shallow proof mode to find shallow work even when the
   ordinary policy does not prioritize it.

The default scorer is the embedded ONNX model:

```rust
pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    Box::new(ScoringModel::load().unwrap())
}
```

`ScoringModel::load()` embeds one ONNX model and its feature contract:

```rust
include_bytes!("../../files/models/model-20260611-e50-h512-l3.onnx")
include_str!("../../files/models/model-20260611-e50-h512-l3.features.json")
```

`ScoringPolicy` now exposes these choices:

- `Model20260611E50H512L3`
- `Handcrafted`
- `DepthFirst`
- `Model`
- `ModelNoShallow`

The eval CLI exposes them as `model-20260611-e50-h512-l3`, `handcrafted`, `depth-first`, `model`,
and `model-no-shallow`. The `model` policies require `--model PATH`; Rust loads the adjacent
`PATH.with_extension("features.json")` contract and feeds the model exactly those feature columns.

## Policy Around The Model

The model score is not the whole ordering. Under the default `model-20260611-e50-h512-l3` policy,
`Score` orders proof steps lexicographically by:

1. whether the step is a contradiction
2. `ShallowStatus`
3. the float returned by the scorer

So the current policy hardcodes:

- contradictions first
- shallow work before deep work
- ONNX score only after those decisions

This matters because an ONNX replacement cannot learn to activate a useful deep step before an
unhelpful shallow step. That choice is made outside the model. The shallow heuristic is useful for
some proof-validation behavior, but it is also acting as a global search policy.

`model-no-shallow` can be used with an external checkpoint to ablate this ordering. It preserves
whether a step is shallow for shallow proof mode, but neutralizes shallow status in the ordinary
queue ordering.

Future work should separate:

- proof modes that intentionally stop at the shallow frontier
- heuristic ordering that happens to prefer shallow clauses

Those are related but not the same policy decision.

## Current Features

`Features` exposes the wide feature catalog exported in eval traces via
`Features::to_catalog_floats`.

The catalog is intended for serious training data. It includes the original nine model inputs plus
refactor-resistant shape/count/category features:

- shallow-status one-hots
- literal counts by polarity and signed/equality shape
- context variable, type-sort, and typeclass counts
- free/bound variable atom counts and distinct free-variable count
- scoped/global constant atom counts without preserving names
- type, typeclass, boolean-value, and logical-symbol atom counts
- generated-vs-assumption and rule-category one-hots
- source-category one-hots, source importability, and source depth for direct assumptions

The current embedded ONNX model records its exact 60-feature input order in
`files/models/model-20260611-e50-h512-l3.features.json`.

`is_shallow` and `shallow_status` are still used outside the model by `Score` for policies that
keep shallow-first ordering. They are now also present in the trace catalog so future models can
learn from them directly.

The catalog still does not include:

- goal/fact symbol overlap
- dependency-distance or scope-distance features
- source position or recency
- whether a fact came from a direct dependency, transitive dependency, or local context
- parent rule details
- active/passive queue context
- age or activation order
- generated-candidate competition at decision time

These feature limits are probably more important than the specific neural-network architecture.

## Passive Set Versus Activation

Adding everything to the passive set is cheaper than activating everything, but it is not free.
Insertion requires scoring and indexing, and passive clauses can later be simplified when a
single-literal clause is activated.

The June 2026 eval instrumentation showed that active inference was much more expensive than the
ONNX call or passive insertion. So it is plausible that premise selection would help, especially as
the library grows. However, the first bottleneck to attack is the work triggered by activation.

This distinction is important:

- Retrieval decides which initial facts are even available.
- Scoring decides which available passive clauses become active and when.

Retrieval has a recall failure mode: if it removes a needed fact, search cannot recover. Scoring
can initially be tested in a less destructive way: keep all facts available, but activate more
useful ones earlier. Later, the same policy machinery can grow thresholds, beams, or factual
activation budgets that approximate retrieval without making premise availability an all-or-nothing
upfront choice.

## Current Fact Loading

The processor currently adds broad fact context to the prover:

- `Processor::add_imports_from_bindings` walks direct dependencies and their transitive
  dependencies.
- `Processor::add_imported_module` adds every lowered module fact from each imported module.
- `Processor::add_module_facts` adds module-local facts visible at the cursor.
- `Processor::add_lowered_fact` pushes the lowered proof steps into the prover with
  `prover.add_steps`.

This means many library facts enter the passive set as assumptions. They are not all used
immediately for inference, but they are all candidates for later activation under the passive
queue ordering.

The activation cap currently counts non-factual activations. Factual activations can therefore
be very large in a timeout search. An earlier default ONNX eval run had about 108 factual
activations for every non-factual activation.

## Current Activation Cost

When a step is activated, `Prover::activate`:

- may simplify existing passive clauses if the activated clause has one literal
- sends the step to `ActiveSet::activate`
- generates new candidate steps through the active inference machinery
- simplifies generated steps against the active set
- rejects some generated steps with `ProofStep::automatic_reject`
- pushes accepted generated steps back into the passive set

`ProofStep::automatic_reject` currently rejects:

- factual generated steps with `proof_size > 2`
- any step with `depth >= 30`

The active inference machinery includes equality resolution, equality factoring, injectivity,
boolean reduction, extensionality, resolution, and rewrite handling. The eval generated-rule
counts show that rewrite, resolution, and boolean reduction dominate candidate generation.

This is why better activation ordering can be valuable even though scoring itself is cheap. A
better scorer is not saving 8 ms of scoring time; it is trying to avoid hundreds of milliseconds
of unnecessary active inference.

## Current Training Code

The current Python code under `python/` is a uv package named `acorn_training`. Its CLIs build
tensor shards from traces and train from either raw traces or shard directories. The trainer:

- loads schema-v2 eval trace `.jsonl.zst` files from `acorn eval --trace-out`, or prebuilt shard
  directories
- trains on selected columns from each activated step's numeric `feature_vector`
- uses `used_in_final_proof` as the binary label
- groups train/validation splits by search key `(module, goal)`, so alternate policies and skip
  modes for the same goal cannot leak across the split
- for new traces with stamped `goal_bucket`, uses buckets `90-99` as validation and `0-89` as
  trainable data
- trains a small configurable PyTorch MLP with feature normalization, positive-class weighting, and
  AdamW
- exports an ONNX probability scorer with input `input`, output `output`, and a sidecar
  `*.features.json` file that records the exact input feature names/order

The Python loader reads trace feature names from the sidecar `*.meta.json` file. By default it
uses all catalog features; `--features legacy` selects the old nine-feature contract, and repeated
`--feature NAME` arguments can choose an explicit subset. The embedded production model in
`src/prover/scoring_model.rs` is `model-20260611-e50-h512-l3`; new ONNX files can still be
evaluated without embedding them by running `acorn eval --policy model --model PATH`.

This setup is useful historical context, but it should not drive the next iteration by itself.
The training objective is weakly connected to the actual metric we care about: proving more eval
goals faster under the live search policy. A model can improve offline classification loss while
making activation order worse.

## Why Work On Scoring First

Scoring first makes sense for four reasons.

First, active inference dominates measured runtime. The largest win is probably not making the
scorer cheaper; it is activating fewer bad clauses before finding the goal.

Second, factual activations dominate. Most activations in the measured eval were assumptions. A
policy that delays or limits irrelevant factual assumptions could reduce the amount of active
inference substantially.

Third, scoring experiments can be incremental. We can keep all existing facts in the passive set,
preserving recall, while testing alternative activation orderings under `acorn eval`. Retrieval
is riskier as a first move because it can make necessary facts unavailable.

Fourth, the current code already has a narrow abstraction point. `Scorer` and `Score` are small,
and `PassiveSet` already batch-scores steps. It should be feasible to add configurable policies
and richer instrumentation before making larger premise-selection changes.

The policy ablation made this more concrete: changing activation order alone, without changing
retrieval, was enough to move both success rate and runtime substantially.

## Why The Model Is Not The Whole Policy

Updating the embedded ONNX model is useful, but it is not the whole search policy.

The default model is boxed in by policy. The default ordering is contradiction, then shallow
status, then model score. A better model cannot override shallow-first behavior unless we choose
a policy that lets it do so.

The current catalog is still missing features that a premise selector or activation policy likely
needs, such as goal relevance, symbol overlap, dependency distance, and richer search context.

The scorer cannot express policy decisions beyond a float rank. It cannot say "do not activate
this yet", "never activate this fact in this search", "spend only N factual activations", or
"prefer this generated step because the current queue is saturated with assumptions."

The current training data is closer to eval-shaped than the old dataset, but it still does not
directly encode decision-time ranking among candidates or counterfactual choices the prover did not
activate.

Eval policy selection now supports both built-in scorers and external model contracts. It is enough
for ranking ablations, but not enough for richer search policies that defer, reject, threshold, or
budget activations.

For these reasons, the useful "scoring" work is really policy, training, and measurement work:
keep policies configurable, make shallow ordering optional or learnable, train from eval traces,
and evaluate with `acorn eval`. The immediate next step is to rerun the standard eval suite with
the embedded `model-20260611-e50-h512-l3` checkpoint as the default baseline.

## Recommended Next Work

1. Rerun the traced standard eval suite.

./scripts/eval-suite.sh

The policy flag did its job: it found real failures outside the default proof paths. The reduced
bugs from the first ablation pass are now fixed:

- no-shallow stack growth from cyclic named-witness placement
- `handcrafted` certificate generation for the `number_theory/arithmetic_functions.ac` line 154
  proof path
- `handcrafted` certificate generation for the `fin_matrix_det.ac` line 225 proof path
- claim context capture when a claim-map term refers to a surviving replacement-context type local

The next useful data is a fresh traced run of all standard cases under the same timeout/skip
settings. The eval suite now exports traces, including failed searches, for every standard case by
default, so there is no separate trace-export implementation step. If the rerun exposes new crashes
or certificate failures, reduce those next; otherwise, use the updated success, timing, and trace
data as the new baseline for scorer work.

2. Inspect policy value and failure modes.

The existing policies and trained models are useful both as baselines and as trace generators.
After the rerun, compare which goals are solved uniquely by each case and which cases are mostly
subsumed by the others. This should tell us which built-ins and model variants are worth keeping in
the experiment suite while we train replacements.
`scripts/eval-policy-wins.py` computes these unique-win counts from the eval-suite logs without
reading the much larger trace files.

3. Iterate on the trained scorer.

The trace exporter, shard converter, Python training path, ONNX export, and Rust external-model
loader now exist. The current embedded catalog-feature model is a useful baseline, not a final
answer. The next iteration should be guided by activation traces and live eval behavior, not just
offline loss.

4. Add the next feature batch only after looking at the new traces.

The wide catalog already includes the obvious cheap shape/count/category features. The likely next
feature work is goal-aware, source-aware, and cost-aware, but it should be guided by the traced eval
data rather than added blindly. Refactor-resistant candidates include dependency distance, local
versus imported scope category, source recency buckets, goal/candidate shape overlap, parent-rule
summaries, activation age, and generated-candidate cost summaries.

5. Evaluate by live prover behavior.

Use `acorn eval` as the main metric. Track at least:

- success rate
- average search time
- timeout count
- factual activations/search
- non-factual activations/search
- generated candidates/search
- active inference time/search
- passive size metrics

Offline loss can be a development signal, but it should not decide whether a policy is better.

6. Use stable goal-bucket train/test splits.

Avoid training and evaluating on nearly identical local proof contexts. New traces stamp
`goal_bucket = first_8_bytes_be(SHA-256("{module}\t{goal}")) % 100`; Python uses buckets `90-99`
for validation and `0-89` for trainable data. Rows should not differ only by policy or skip mode
across the split.

7. Consider factual activation budgets.

The current activation cap counts non-factual activations. Since factual activations dominate,
future policy experiments should consider a separate factual budget, a per-source budget, or a
threshold that delays low-value factual assumptions. This is a natural bridge between scoring and
retrieval.

8. Return to retrieval after scoring baselines are understood.

Retrieval is still important, especially as the library grows. But it should come after we know
how much can be gained from better activation order with all facts still available. The scoring
trace data should also make retrieval easier, because it will identify which facts were actually
useful under successful searches.

## Open Questions

- Does the embedded `model-20260611-e50-h512-l3` checkpoint keep beating `depth-first` after the
  next full eval rerun?
- Does removing shallow-first ordering help or hurt the embedded checkpoint if we add a built-in
  no-shallow variant?
- Can normal search drop shallow-first ordering and let the model rank shallow and deep candidates
  together, while keeping `ProverMode::Shallow` as a separate bounded mode?
- Should all initial facts continue to enter the passive set, or should a learned/source-aware
  admission policy decide which facts are available?
- Are the current automatic reject rules discarding useful generated steps, and should they become
  learned, feature-driven, or policy-configurable decisions?
- Would factual activation budgets, per-source budgets, or activation thresholds improve average
  behavior, or would they create brittle near-misses?
- Which source metadata is cheap to preserve from elaboration/lowering into `ProofStep` features?
- How often does the final proof use a fact that looked irrelevant by simple symbol overlap?
- Should the scorer own only ranking, or should the abstraction become a broader search policy
  that can defer, reject, or budget activations?

The next concrete milestone should be to rerun the traced standard eval suite after the current
fixes and model-loader changes. Once the standard cases complete cleanly, the ablations can tell us
which policy constraints are costing searches and whether the embedded catalog-feature model keeps
helping under live prover behavior.
