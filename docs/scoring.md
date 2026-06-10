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

This should not be interpreted as "replace the ONNX file and call it done." The current ONNX
model is only one small part of the activation policy. The policy also has hardcoded ordering in
the default configuration, very limited features, no ability to reject or budget facts, and old
training infrastructure that is not eval-driven.

The first configurability step has now landed: `acorn eval --policy` can run several activation
policies without code edits, and `--policy model --model PATH` can evaluate a trained ONNX scorer
with its exported `*.features.json` contract. That immediately exposed two important facts:

- `depth-first` currently beats the default ONNX policy by a large margin on the full eval.
- alternate policies exercised proof and certificate paths the default policy rarely reached.
  The initially reduced certificate and stack-growth bugs have now been fixed, but the full
  standard eval suite has not yet been rerun after those fixes and the first trained model.

## Current Eval Harness

`acorn eval` is a useful outer benchmark for scoring work. In eval mode, `Builder`:

- forces prover search instead of trusting cached proofs
- disables module hash skipping
- runs configured skip modes, defaulting to `0` and `1`
- accepts `--policy` to select the activation queue policy
- accepts `--model` for external ONNX scorer policies and `--policy-label` for stable trace case
  names
- accepts `--trace-out` to write successful search traces as JSONL, zstd-compressed when the
  path ends in `.zst` and gzip-compressed when the path ends in `.gz`
- compares current source goals against cached proof targets
- records per-search `SearchStats`

Eval success counts successful prover outcomes. That includes `Outcome::Success` and
`Outcome::Inconsistent`; finding an inconsistency is useful evidence that the prover reached a
decisive result. Regular verify/search behavior still treats unexpected inconsistencies as warnings.

The first trace exporter is intentionally eval-shaped:

- `--trace-out PATH` writes one `acorn-activated-step-trace-v2` JSON object per activated step
  from successful eval searches
- a sidecar metadata file next to the trace, for example `onnx.meta.json` for `onnx.jsonl.zst`,
  records the numeric feature-vector names once
- each record includes module/goal/skip/policy/outcome metadata, activation index, passive id,
  active id, queue score/order fields, rule, truthiness, the current numeric `feature_vector`, and
  a `used_in_final_proof` label derived from the final proof dependency closure
- records do not currently include a named per-row `features` object; feature names live only in
  the sidecar metadata file
- unactivated passive candidates are not labeled, because we do not know whether they would have
  been useful if selected later
- `Outcome::Inconsistent` traces are exported when eval counts them as successful prover outcomes

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

- `onnx`: the default embedded ONNX scorer, with shallow-first ordering
- `handcrafted`: the old hand-written scorer, with shallow-first ordering
- `depth-first`: constant scorer, so queue ties fall back to insertion/order structure, with
  shallow-first ordering
- `onnx-no-shallow`: the embedded ONNX scorer with shallow status removed from the ordinary
  ordering key
- `model`: an external ONNX scorer loaded from `--model`, with shallow-first ordering
- `model-no-shallow`: an external ONNX scorer loaded from `--model`, with shallow status removed
  from the ordinary ordering key

The scoring config is threaded through `Builder`, `Processor`, `Prover`, and `PassiveSet`, so eval
workers can carry both a policy and an optional external model path. `scripts/eval-suite.sh` runs
the standard traced cases by default:

- `onnx`
- `depth-first`
- `handcrafted`
- `onnx-no-shallow`
- `trained-5m`
- `trained-5m-no-shallow`

The trained cases currently point at
`tmp/models/scorer-catalog-5m-h128-l3-e20-best.onnx`.

## Current Scoring Architecture

The activation queue lives in `PassiveSet`. New proof steps are scored in batches:

1. `PassiveSet::push_batch` builds `Features` for each `ProofStep`.
2. `Score::batch` asks the configured `Scorer` for a float score and applies the configured
   `ScoringPolicy`.
3. `PassiveSet` stores `(Score, clause_id)` in a `BTreeSet`.
4. `PassiveSet::pop_with_shallow` pops the highest ordered score for normal activation.
5. `PassiveSet::pop_shallow` is used by shallow proof mode to find shallow work even when the
   ordinary policy does not prioritize it.

The default scorer is still the embedded ONNX model:

```rust
pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    Box::new(ScoringModel::load().unwrap())
}
```

`ScoringModel::load()` embeds one ONNX model:

```rust
include_bytes!("../../files/models/model-2024-09-25-15-33-10.onnx")
```

`ScoringPolicy` now exposes these choices:

- `Onnx`
- `Handcrafted`
- `DepthFirst`
- `OnnxNoShallow`
- `Model`
- `ModelNoShallow`

The eval CLI exposes them as `onnx`, `handcrafted`, `depth-first`, `onnx-no-shallow`, `model`, and
`model-no-shallow`. `model` policies require `--model PATH`; Rust loads the adjacent
`PATH.with_extension("features.json")` contract and feeds the model exactly those feature columns.

## Policy Around The Model

The model score is not the whole ordering. Under the default `onnx` policy, `Score` orders proof
steps lexicographically by:

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

`onnx-no-shallow` was added to ablate this ordering. It preserves whether a step is shallow for
shallow proof mode, but neutralizes shallow status in the ordinary queue ordering. The first full
eval attempt hit a stack-growth bug that is now fixed in reduced form, so this ablation should be
rerun.

Future work should separate:

- proof modes that intentionally stop at the shallow frontier
- heuristic ordering that happens to prefer shallow clauses

Those are related but not the same policy decision.

## Current Features

`Features` now has two distinct vector views:

- the wide feature catalog, exported in eval traces via `Features::to_catalog_floats`
- the legacy embedded-model input, selected by `Features::legacy_model_feature_names`

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

The current embedded ONNX model still sees only the legacy nine inputs:

- contradiction bit
- atom count
- counterfactual bit
- hypothetical bit
- factual bit
- assumption bit
- negated-goal bit
- proof size
- depth

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
be very large in a timeout search. The default ONNX eval run had about 108 factual activations
for every non-factual activation.

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

There are two training paths in the tree.

The older Rust dataset type in `src/prover/dataset.rs` is still present. It was designed around
activated proof steps:

- `features`: the feature vector for a proof step
- `label`: whether the activated step was used in the final proof

It writes `.npz` files under `files/datasets`. This is legacy infrastructure; the newer trace
exporter is the path we are using for eval-shaped training.

The current Python code under `python/` is a uv package named `acorn_training`. Its CLIs build
tensor shards from traces and train from either raw traces or shard directories. The trainer:

- loads schema-v2 eval trace JSONL, JSONL.ZST, or JSONL.GZ files from `acorn eval --trace-out`,
  or prebuilt shard directories
- trains on selected columns from each activated step's numeric `feature_vector`
- uses `used_in_final_proof` as the binary label
- groups train/validation splits by search key `(module, goal, skip, policy)`
- trains a small configurable PyTorch MLP with feature normalization, positive-class weighting, and
  AdamW
- exports an ONNX probability scorer with input `input`, output `output`, and a sidecar
  `*.features.json` file that records the exact input feature names/order

The Python loader reads trace feature names from the sidecar `*.meta.json` file. By default it
uses all catalog features; `--features legacy` selects the old nine-feature contract, and repeated
`--feature NAME` arguments can choose an explicit subset. The embedded production model in
`src/prover/scoring_model.rs` is still the checked-in `model-2024-09-25-15-33-10.onnx`, but a
new ONNX file can now be evaluated without embedding it by running
`acorn eval --policy model --model PATH`.

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

## Why Not Just Swap The ONNX Model

Swapping the ONNX file alone is unlikely to be enough.

The default model is boxed in by policy. The default ordering is contradiction, then shallow
status, then model score. A better model cannot override shallow-first behavior unless we choose
a policy that lets it do so.

The embedded model input is too sparse. Nine scalar features cannot express most of what a premise
selector or activation policy needs to know, such as goal relevance, symbol overlap, dependency
distance, term shape, rule type, or search context.

The scorer cannot express policy decisions beyond a float rank. It cannot say "do not activate
this yet", "never activate this fact in this search", "spend only N factual activations", or
"prefer this generated step because the current queue is saturated with assumptions."

The legacy training data was not eval-shaped. The old dataset labels whether activated steps
appeared in the final proof. The new trace path fixes the most important part of that by exporting
successful eval searches, but it still does not directly encode decision-time ranking among
candidates or counterfactual choices the prover did not activate.

Eval policy selection now supports both built-in scorers and external model contracts. It is enough
for ranking ablations, but not enough for richer search policies that defer, reject, threshold, or
budget activations.

For these reasons, the useful "scoring" work is really policy, training, and measurement work:
keep policies configurable, make shallow ordering optional or learnable, train from eval traces,
and evaluate with `acorn eval`. The immediate next step is to rerun the standard eval suite now
that the first wave of alternate-policy bugs has been fixed and the first trained model is wired in.

## Recommended Next Work

1. Rerun the traced standard eval suite.

./scripts/eval-suite.sh

The policy flag did its job: it found real failures outside the default proof paths. The reduced
bugs from the first ablation pass are now fixed:

- `onnx-no-shallow` stack growth from cyclic named-witness placement
- `handcrafted` certificate generation for the `number_theory/arithmetic_functions.ac` line 154
  proof path
- `handcrafted` certificate generation for the `fin_matrix_det.ac` line 225 proof path
- claim context capture when a claim-map term refers to a surviving replacement-context type local

The next useful data is a fresh traced run of all standard cases under the same timeout/skip
settings. The eval suite now exports traces for every case by default, so there is no separate
trace-export implementation step. If the rerun exposes new crashes or certificate failures, reduce
those next; otherwise, use the updated success, timing, and trace data as the new baseline for
scorer work.

2. Inspect policy value and failure modes.

The existing policies and the first trained model are useful both as baselines and as trace
generators. After the rerun, compare which goals are solved uniquely by each case and which cases
are mostly subsumed by the others. This should tell us whether the built-ins and the first trained
model variants are all worth keeping in the experiment suite while we train replacements.
`scripts/eval-policy-wins.py` computes these unique-win counts from the eval-suite logs without
reading the much larger trace files.

3. Iterate on the trained scorer.

The trace exporter, shard converter, Python training path, ONNX export, and Rust external-model
loader now exist. The first catalog-feature model should be treated as an eval candidate, not as a
final replacement. If it beats useful baselines, the next iteration is larger or cleaner training.
If it underperforms, inspect activation traces and offline errors before changing architecture.

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

6. Use module-based train/test splits.

Avoid training and evaluating on nearly identical local proof contexts. Module-level or
dependency-aware splits should give a better signal about whether the policy generalizes.

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

- Does `depth-first` still outperform the default ONNX policy after the next full eval rerun?
- Will the fixed `handcrafted` run now complete the full corpus, and how does it compare to
  `depth-first`?
- Does the first catalog-feature trained model beat the embedded ONNX model, and does removing
  shallow-first ordering help or hurt it?
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
which policy constraints are costing searches and whether the first catalog-feature model is already
useful under live prover behavior.
