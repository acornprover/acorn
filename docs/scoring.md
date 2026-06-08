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
policies without code edits. That immediately exposed two important facts:

- `depth-first` currently beats the default ONNX policy by a large margin on the full eval.
- alternate policies exercised proof and certificate paths the default policy rarely reached.
  The initially reduced certificate and stack-growth bugs have now been fixed, but the full
  four-policy eval has not yet been rerun after those fixes.

## Eval Baseline

The regular eval run on June 6, 2026 used the default `acorn eval` settings:

- force-search eval mode
- default timeout of 1 second per search
- default skip modes `0` and `1`
- goals drawn from eligible cached proofs
- default scoring policy `onnx`

The run produced this aggregate summary:

- 74,671 benchmark proofs with eligible cached proofs
- 38,622 benchmark proofs with empty cached proofs, omitted for `skip=0`
- 74,671 benchmark goals matched current source
- 69,726 searches performed
- 39,920 searches succeeded
- 57.25% search success rate
- 598.9 ms average search time
- 29,799 timeouts and 7 inconsistent searches
- `skip=0`: 20,745 / 36,049 searches succeeded, 611.6 ms average
- `skip=1`: 19,175 / 33,677 searches succeeded, 40,994 ineligible, 585.3 ms average

The new search instrumentation reported:

- 2,967.0 initial passive clauses per search on average
- 9,707.0 max passive clauses per search on average
- 44,350 peak passive clauses in one search
- 9,632.8 final passive clauses per search on average
- 128,097,294 factual activations, or 1,837.2 per search
- 1,190,376 non-factual activations, or 17.1 per search
- 660,394,684 generated candidates, or 9,471.3 per search
- 595,273,049 accepted generated steps
- 488,361 auto-rejected generated steps
- 63,833,238 simplified-away generated steps
- 165,898 passive simplifications

The timing split was:

- 490.8 ms active inference per search
- 37.2 ms active simplification per search
- 26.9 ms passive simplification per search
- 8.3 ms scoring per search
- 32.0 ms passive indexing per search

The activated rule counts were heavily dominated by facts:

- 109,918,354 `Assumption`
- 17,520,061 `Boolean Reduction`
- 846,282 `Extensionality`
- 700,534 `Equality Resolution`
- 158,008 `Rewrite`
- 46,601 `Simplification`
- 97,830 other

Generated candidates were dominated by:

- 532,748,487 `Boolean Reduction`
- 73,385,930 `Rewrite`
- 38,782,142 `Resolution`
- 7,848,062 `Extensionality`
- 5,388,655 `Equality Resolution`
- 1,678,238 `Injectivity`
- 563,170 other

The important interpretation is that passive-set operations are not free, but they are not
currently the main measured cost. The expensive event is activating a clause, because activation
runs the active inference machinery and can generate thousands of new candidates. The eval data
shows many more factual activations than non-factual activations, and most activations are
assumption steps. That makes activation ordering a high-leverage target.

The default full eval took about 47 minutes wall time on this machine. Most of that was proof
search: 2,814.670 seconds measured wall time, with 41,756.640 seconds of summed per-search proof
time across worker threads.

## Policy Ablation Results

After adding `--policy`, the standard eval was run across four policies:

| policy | result | success | average search | measured wall time |
| --- | --- | ---: | ---: | ---: |
| `onnx` | completed with failed searches | 39,920 / 69,726 = 57.25% | 598.9 ms | 2,815.059s |
| `depth-first` | completed with failed searches | 54,377 / 69,726 = 77.99% | 278.1 ms | 1,155.152s |
| `handcrafted` | build failed during eval | partial: 27,018 / 43,722 = 61.79% | 678.0 ms | 2,235.264s |
| `onnx-no-shallow` | crashed during full eval | no aggregate | n/a | immediate stack overflow |

The `depth-first` result is the most important clean ablation. It proves 14,457 more searches
than the default ONNX policy and finishes about 2.4x faster. It also does much less search work:

- 311.5M generated candidates versus 660.4M for `onnx`
- 3,944.9 average max passive clauses versus 9,707.0 for `onnx`
- 243.4 ms active inference per search versus 490.8 ms for `onnx`
- 10.1 ms passive indexing per search versus 32.0 ms for `onnx`

The `handcrafted` run is not directly comparable because it hit certificate-generation failures
before completing the full corpus. The logged failures were:

- `number_theory/arithmetic_functions.ac`, line 154: certificate claim map type mismatch
- `fin_matrix_det.ac`, line 225: generated certificate code expected a type but found a value

Those failures are still useful: alternate search paths are finding proofs that expose
certificate-generation bugs.

The `onnx-no-shallow` run currently cannot answer whether shallow-first is hurting ONNX. Full
eval stack-overflowed immediately, including a retry with `RUST_MIN_STACK=67108864`. A narrow
`acorn eval category --policy onnx-no-shallow --timing -j1` run completed, so the policy is not
trivially broken, but some full-library search path is triggering unbounded recursion or stack
growth.

Status after the follow-up fixes: the reduced bugs found from these failures are fixed and have
regression coverage. Specifically:

- the `onnx-no-shallow` stack-growth path was reduced to certificate witness placement cycling
  around a claim that mentioned the witness being placed
- the `fin_matrix_det.ac` certificate failure was reduced to closed generic typeclass-attribute
  claim serialization
- the `number_theory/arithmetic_functions.ac` failure was reduced to reversed passive
  simplification/PDT variable-map IDs escaping in the wrong variable numbering
- a later cleanup of that path removed a direct-claim fallback and fixed claim context capture
  for surviving replacement-context type locals

Those fixes have passed the focused mdtests, `cargo test`, `cargo check`, and full cached
certificate replay. The historical table above should not be reinterpreted as current policy
performance; rerun the same policy ablation before drawing new conclusions.

## Current Eval Harness

`acorn eval` is a useful outer benchmark for scoring work. In eval mode, `Builder`:

- forces prover search instead of trusting cached proofs
- disables module hash skipping
- runs configured skip modes, defaulting to `0` and `1`
- accepts `--policy` to select the activation queue policy
- compares current source goals against cached proof targets
- records per-search `SearchStats`

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

The policy is threaded through `Builder`, `Processor`, `Prover`, and `PassiveSet`. This is enough
for eval ablations. The alternate policies should still be treated as experimental until the full
policy ablation is rerun on top of the bug fixes above.

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

The eval CLI exposes them as `onnx`, `handcrafted`, `depth-first`, and `onnx-no-shallow`.

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

`Features` currently stores:

- `is_contradiction`
- `is_shallow`
- `shallow_status`
- `atom_count`
- `is_counterfactual`
- `is_hypothetical`
- `is_factual`
- `is_assumption`
- `is_negated_goal`
- `proof_size`
- `depth`

But `Features::to_floats` sends only nine values to ONNX:

- contradiction bit
- atom count
- counterfactual bit
- hypothetical bit
- factual bit
- assumption bit
- negated-goal bit
- proof size
- depth

Notably, `is_shallow` and `shallow_status` are not model inputs. They are used outside the model
by `Score`.

The model does not see:

- goal/fact symbol overlap
- source module or import distance
- source position or recency
- whether a fact came from a direct dependency, transitive dependency, or local context
- term structure beyond atom count
- literal count by polarity
- variable count, type information, or quantifier-like shape
- rule type beyond assumption and negated goal bits
- whether a step is an initial fact or generated during search
- parent rule details
- active/passive queue context
- age or activation order
- generated-candidate competition at decision time

These feature limits are probably more important than the specific neural-network architecture.

## Passive Set Versus Activation

Adding everything to the passive set is cheaper than activating everything, but it is not free.
Insertion requires scoring and indexing, and passive clauses can later be simplified when a
single-literal clause is activated.

The June 2026 default ONNX eval numbers suggest this rough split per search:

- scoring plus passive indexing: 40.3 ms
- passive simplification: 26.9 ms
- active inference: 490.8 ms

So it is plausible that premise selection would help, especially as the library grows. However,
the current bottleneck is not the ONNX call or passive insertion. The current bottleneck is the
work triggered by activation.

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

The Rust dataset type in `src/prover/dataset.rs` was designed around activated proof steps:

- `features`: the feature vector for a proof step
- `label`: whether the activated step was used in the final proof

It writes `.npz` files under `files/datasets`.

The Python code under `python/` is old notebook-era training code:

- `python/config.py` hardcodes CUDA.
- `python/config.py` hardcodes one dataset filename.
- `python/config.py` hardcodes `num_features = 9`.
- `python/model.py` defines a simple two-hidden-layer network with 16 units per layer.
- The model trains with binary cross entropy on used-vs-unused labels.
- The exporter writes an ONNX file under `files/models`.

The current embedded ONNX model appears to come from this pipeline. The old notebook showed a
highly imbalanced dataset, roughly 413k examples with about 8.5k positives. That is around 2%
positive examples.

This setup is useful historical context, but it should not drive the next iteration by itself.
The training objective is weakly connected to the actual metric we care about: proving more eval
goals faster under the live search policy. A model can improve offline classification loss while
making activation order worse.

## Why Work On Scoring First

Scoring first makes sense for four reasons.

First, active inference dominates measured runtime. The default ONNX eval run spent 490.8
ms/search in active inference, versus 8.3 ms/search scoring and 32.0 ms/search passive indexing.
The largest win is probably not making the scorer cheaper; it is activating fewer bad clauses
before finding the goal.

Second, factual activations dominate. The prover activated about 128.1M factual steps and 1.2M
non-factual steps in the default ONNX eval run. Most activations were assumptions. A policy that
delays or limits irrelevant factual assumptions could reduce the amount of active inference
substantially.

Third, scoring experiments can be incremental. We can keep all existing facts in the passive set,
preserving recall, while testing alternative activation orderings under `acorn eval`. Retrieval
is riskier as a first move because it can make necessary facts unavailable.

Fourth, the current code already has a narrow abstraction point. `Scorer` and `Score` are small,
and `PassiveSet` already batch-scores steps. It should be feasible to add configurable policies
and richer instrumentation before making larger premise-selection changes.

The `depth-first` result makes this more concrete. It changed activation order without changing
retrieval, proved 14,457 more searches than the default ONNX policy, and cut measured wall time
from about 47 minutes to about 19 minutes.

## Why Not Just Swap The ONNX Model

Swapping the ONNX file alone is unlikely to be enough.

The default model is boxed in by policy. The default ordering is contradiction, then shallow
status, then model score. A better model cannot override shallow-first behavior unless we choose
a policy that lets it do so.

The model input is too sparse. Nine scalar features cannot express most of what a premise
selector or activation policy needs to know, such as goal relevance, symbol overlap, module
distance, term shape, rule type, or search context.

The scorer cannot express policy decisions beyond a float rank. It cannot say "do not activate
this yet", "never activate this fact in this search", "spend only N factual activations", or
"prefer this generated step because the current queue is saturated with assumptions."

The training data is not eval-shaped. The old dataset labels whether activated steps appeared in
the final proof. It does not directly encode decision-time ranking among candidates, counterfactual
choices the prover did not activate, success under timeout, or activation counts.

Eval policy selection now exists, but only for a small set of hardcoded choices. It is enough for
basic ablations, not enough for richer search policies that defer, reject, threshold, or budget
activations.

For these reasons, the useful "scoring" work is really policy and measurement work: keep policies
configurable, make shallow ordering optional or learnable, export better data, and evaluate with
`acorn eval`. The immediate next step is to rerun the policy ablations now that the first wave of
alternate-policy bugs has been fixed.

## Recommended Next Work

1. Rerun the four-policy eval after the bug fixes.

The policy flag did its job: it found real failures outside the default proof paths. The reduced
bugs from the first ablation pass are now fixed:

- `onnx-no-shallow` stack growth from cyclic named-witness placement
- `handcrafted` certificate generation for the `number_theory/arithmetic_functions.ac` line 154
  proof path
- `handcrafted` certificate generation for the `fin_matrix_det.ac` line 225 proof path
- claim context capture when a claim-map term refers to a surviving replacement-context type local

The next useful data is a fresh run of the same four policies (`onnx`, `depth-first`,
`handcrafted`, `onnx-no-shallow`) under the same timeout/skip settings. If the rerun exposes new
crashes or certificate failures, reduce those next; otherwise, use the updated success and timing
numbers as the new baseline for scorer work.

2. Finish activation-policy configurability.

The first slice is done for eval:

- `onnx`
- `handcrafted`
- `depth-first`
- `onnx-no-shallow`

Next, decide how broadly this should apply outside eval. It may be enough for now to keep
alternate policies eval-only, but the plumbing should remain clean enough that targeted verify
repros can select a policy when debugging scorer-specific behavior.

3. Separate shallow proof mode from shallow ordering.

`ProverMode::Shallow` still needs to stop at the shallow frontier. That does not require every
normal search policy to rank all shallow clauses above all deep clauses. Make this distinction
explicit in the code.

`onnx-no-shallow` is the first attempt at this separation. The known stack-growth repro has been
fixed, but the full-eval ablation needs to be rerun before trusting the result.

4. Add richer features.

Useful candidates include:

- rule type one-hot
- initial fact versus generated step
- source kind: local, direct dependency, transitive dependency, generated
- module distance from the goal
- source position or recency
- clause literal count by polarity
- variable count
- term-size features
- type-parameter or higher-order shape features
- goal symbol overlap
- active/passive age
- parent rule and parent truthiness
- shallow status as an ordinary feature

Goal-aware and source-aware features are especially important if we want the scorer to behave
partly like soft premise selection.

5. Export eval-shaped training traces.

For each search, record enough information to reconstruct ranking decisions:

- goal identity
- search outcome
- timeout and activation limit
- passive queue candidates at selected decision points
- activated step features
- score and final ordered key
- activation order
- rule and truthiness
- source/module metadata for assumptions
- whether the step appeared in the final proof
- generated-candidate counts caused by the activation

A lightweight first version can log only activated steps plus their features and outcome. A better
version should include candidate snapshots, because scoring is a ranking problem, not just a
used-vs-unused classification problem.

6. Evaluate by live prover behavior.

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

7. Use module-based train/test splits.

Avoid training and evaluating on nearly identical local proof contexts. Module-level or
dependency-aware splits should give a better signal about whether the policy generalizes.

8. Consider factual activation budgets.

The current activation cap counts non-factual activations. Since factual activations dominate,
future policy experiments should consider a separate factual budget, a per-source budget, or a
threshold that delays low-value factual assumptions. This is a natural bridge between scoring and
retrieval.

9. Return to retrieval after scoring baselines are understood.

Retrieval is still important, especially as the library grows. But it should come after we know
how much can be gained from better activation order with all facts still available. The scoring
trace data should also make retrieval easier, because it will identify which facts were actually
useful under successful searches.

## Open Questions

- Why does `depth-first` outperform the default ONNX policy so strongly on the current eval?
- After rerunning `onnx-no-shallow`, how much of the timeout set is caused by shallow-first
  ordering specifically?
- Will the fixed `handcrafted` run now complete the full corpus, and how does it compare to
  `depth-first`?
- Are successful proofs usually found after activating a small number of relevant facts, or do
  they genuinely need broad factual saturation?
- Would a factual activation budget improve average behavior, or would it create many brittle
  near-misses?
- Which source metadata is cheap to preserve from elaboration/lowering into `ProofStep` features?
- How often does the final proof use a fact that looked irrelevant by simple symbol overlap?
- Should the scorer own only ranking, or should the abstraction become a broader search policy
  that can defer, reject, or budget activations?

The next concrete milestone should be to rerun the same four-policy eval after the current fixes.
Once the alternate policies complete cleanly, the ablations can tell us which policy constraints
are costing searches before we invest in larger training and retrieval systems.
