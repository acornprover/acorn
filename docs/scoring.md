# Prover Scoring

This document records what we learned from the May 2026 eval instrumentation pass and
the current shape of the prover scoring code. It is meant as context for future work on
proof-search heuristics.

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
model is only one small part of the activation policy. The policy also has hardcoded ordering,
very limited features, no runtime configurability, no ability to reject or budget facts, and old
training infrastructure that is not eval-driven.

## Eval Baseline

The regular eval run on May 7, 2026 used the default `acorn eval` settings:

- force-search eval mode
- default timeout of 1 second per search
- default skip modes `0` and `1`
- goals drawn from eligible cached proofs

The run produced this aggregate summary:

- 43,870 benchmark proofs with eligible cached proofs
- 21,590 benchmark proofs with empty cached proofs, omitted for `skip=0`
- 43,870 benchmark goals matched current source
- 41,487 searches performed
- 32,251 searches succeeded
- 77.74% search success rate
- 414.2 ms average search time
- 9,229 timeouts and 7 inconsistent searches
- `skip=0`: 17,589 / 22,280 searches succeeded, 411.5 ms average
- `skip=1`: 14,662 / 19,207 searches succeeded, 24,663 ineligible, 417.3 ms average

The new search instrumentation reported:

- 2,918.2 initial passive clauses per search on average
- 5,230.3 max passive clauses per search on average
- 33,623 peak passive clauses in one search
- 5,090.6 final passive clauses per search on average
- 94,483,115 factual activations, or 2,277.4 per search
- 806,785 non-factual activations, or 19.4 per search
- 192,231,357 generated candidates, or 4,633.5 per search
- 186,253,845 accepted generated steps
- 491,698 auto-rejected generated steps
- 4,829,145 simplified-away generated steps
- 159,086 passive simplifications

The timing split was:

- 316.2 ms active inference per search
- 16.3 ms active simplification per search
- 37.2 ms passive simplification per search
- 10.1 ms scoring per search
- 26.4 ms passive indexing per search

The activated rule counts were heavily dominated by facts:

- 81,880,708 `Assumption`
- 10,075,740 `Boolean Reduction`
- 1,833,384 `Extensionality`
- 909,799 `Equality Resolution`
- 276,817 `Rewrite`
- 112,544 `Equality Factoring`
- 200,908 other

Generated candidates were dominated by:

- 92,674,669 `Rewrite`
- 45,662,411 `Resolution`
- 43,667,771 `Boolean Reduction`
- 5,698,699 `Extensionality`
- 2,891,293 `Equality Resolution`
- 1,225,128 `Injectivity`
- 411,386 other

The important interpretation is that passive-set operations are not free, but they are not
currently the main measured cost. The expensive event is activating a clause, because activation
runs the active inference machinery and can generate thousands of new candidates. The eval data
shows many more factual activations than non-factual activations, and most activations are
assumption steps. That makes activation ordering a high-leverage target.

## Current Eval Harness

`acorn eval` is a useful outer benchmark for scoring work. In eval mode, `Builder`:

- forces prover search instead of trusting cached proofs
- disables module hash skipping
- runs configured skip modes, defaulting to `0` and `1`
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

## Current Scoring Architecture

The activation queue lives in `PassiveSet`. New proof steps are scored in batches:

1. `PassiveSet::push_batch` builds `Features` for each `ProofStep`.
2. `Score::batch` asks the configured `Scorer` for a float score.
3. `PassiveSet` stores `(Score, clause_id)` in a `BTreeSet`.
4. `PassiveSet::pop_with_shallow` pops the highest ordered score for activation.

The default scorer is hardcoded:

```rust
pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    Box::new(ScoringModel::load().unwrap())
}
```

`ScoringModel::load()` embeds one ONNX model:

```rust
include_bytes!("../../files/models/model-2024-09-25-15-33-10.onnx")
```

There are also old alternative scorers in `src/prover/scorer.rs`:

- `HandcraftedScorer`
- `DepthFirstScorer`

They are not exposed as normal eval/runtime options.

## Hardcoded Policy Around The Model

The model score is not the whole ordering. `Score` orders proof steps lexicographically by:

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

The May 2026 eval numbers suggest this rough split per search:

- scoring plus passive indexing: 36.5 ms
- passive simplification: 37.2 ms
- active inference: 316.2 ms

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
be very large in a timeout search. The eval run had about 117 factual activations for every
non-factual activation.

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
better scorer is not saving 10 ms of scoring time; it is trying to avoid hundreds of milliseconds
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

First, active inference dominates measured runtime. The eval run spent 316.2 ms/search in active
inference, versus 10.1 ms/search scoring and 26.4 ms/search passive indexing. The largest win is
probably not making the scorer cheaper; it is activating fewer bad clauses before finding the
goal.

Second, factual activations dominate. The prover activated about 94.5M factual steps and 0.8M
non-factual steps in the eval run. Most activations were assumptions. A policy that delays or
limits irrelevant factual assumptions could reduce the amount of active inference substantially.

Third, scoring experiments can be incremental. We can keep all existing facts in the passive set,
preserving recall, while testing alternative activation orderings under `acorn eval`. Retrieval
is riskier as a first move because it can make necessary facts unavailable.

Fourth, the current code already has a narrow abstraction point. `Scorer` and `Score` are small,
and `PassiveSet` already batch-scores steps. It should be feasible to add configurable policies
and richer instrumentation before making larger premise-selection changes.

## Why Not Just Swap The ONNX Model

Swapping the ONNX file alone is unlikely to be enough.

The model is boxed in by hardcoded policy. The final ordering is contradiction, then shallow
status, then model score. A better model cannot override shallow-first behavior.

The model input is too sparse. Nine scalar features cannot express most of what a premise
selector or activation policy needs to know, such as goal relevance, symbol overlap, module
distance, term shape, rule type, or search context.

The scorer cannot express policy decisions beyond a float rank. It cannot say "do not activate
this yet", "never activate this fact in this search", "spend only N factual activations", or
"prefer this generated step because the current queue is saturated with assumptions."

The training data is not eval-shaped. The old dataset labels whether activated steps appeared in
the final proof. It does not directly encode decision-time ranking among candidates, counterfactual
choices the prover did not activate, success under timeout, or activation counts.

The model is not runtime-configurable. The default scorer always loads the embedded model, so
comparing policies requires code changes rather than clean eval runs.

For these reasons, the first useful "scoring" work is really policy and measurement work:
make policies configurable, make shallow ordering optional or learnable, export better data, and
evaluate with `acorn eval`.

## Recommended Next Work

1. Make activation policy configurable.

Add a way for eval to select among at least:

- current ONNX baseline
- handcrafted scorer
- depth-first scorer
- ONNX without shallow-first priority
- shallow status as a model feature rather than an outer ordering key

This gives quick ablations for how much the hardcoded shallow ordering matters.

2. Separate shallow proof mode from shallow ordering.

`ProverMode::Shallow` still needs to stop at the shallow frontier. That does not require every
normal search policy to rank all shallow clauses above all deep clauses. Make this distinction
explicit in the code.

3. Add richer features.

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

4. Export eval-shaped training traces.

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

- How much of the timeout set is caused by shallow-first ordering specifically?
- Are successful proofs usually found after activating a small number of relevant facts, or do
  they genuinely need broad factual saturation?
- Would a factual activation budget improve average behavior, or would it create many brittle
  near-misses?
- Which source metadata is cheap to preserve from elaboration/lowering into `ProofStep` features?
- How often does the final proof use a fact that looked irrelevant by simple symbol overlap?
- Should the scorer own only ranking, or should the abstraction become a broader search policy
  that can defer, reject, or budget activations?

The next concrete milestone should be a configurable eval policy framework plus ablations of the
current shallow-first behavior. That will tell us whether the obvious policy constraints are
already costing many searches before we invest in larger training and retrieval systems.
