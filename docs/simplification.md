# Simplification

The `simplify` command removes proof-local propositions that are very likely redundant.
It is deliberately conservative: when the command is not sure a proposition is removable, it keeps
the source unchanged.

## Scope

Simplification only edits proof-local, anonymous propositions. It does not remove:

- top-level propositions
- theorem, lemma, or axiom statements
- block goals or propositions exported from blocks
- imported facts

The first implementation removes individual claim statements. Removing whole blocks is a future
extension; it should use the same dependency and reproving rules.

## Dependency Model

Lowering turns source into a tree of items:

- facts, which become available to later items
- claims, which have a goal to prove and then become facts
- blocks, which have local items and may export an external fact

A removable claim has a post-fact. Any later goal whose visible facts include that post-fact is an
affected goal. This is a conservative dependency graph: it may include goals that did not actually
use the candidate in their final proof, but it will not miss a goal that could depend on it through
source visibility.

Future work can replace the visibility-based affected set with a proof-DAG set extracted from
checked certificates or generated proof dependencies. The source-editing rule should stay the same:
only edit after all affected goals reprove without the candidate.

## Weak Reproving

To test candidate claim `A`:

1. Collect affected goals whose visible facts include `A`.
2. For each affected goal `B`, build a processor with every visible fact except `A`.
3. Run a weak prover on `B`.
4. If all affected goals succeed, `A` is accepted for deletion.

The default weak prover timeout is `0.1` seconds. It uses the normal prover search with a small time
budget, so simplification should remove only facts that are easy to rediscover.

Passing weak reproving is not enough to edit the source. Before writing, the command reloads the
edited source in memory and runs normal verification on the edited target. Existing certificates may
be reused when they still check, but the edited target must verify successfully. If weak reproving
accepts a candidate and the edited target does not load or verify, the command treats that as a
`simplify bug` and leaves the file unchanged.

## Editing Loop

The command tests one candidate at a time:

1. Load and lower the target file.
2. Find the next removable candidate at or after the current source line.
3. Test the candidate by masking it in memory.
4. If accepted, verify the edited target in memory, then delete the source range.
5. Reload the edited file and continue from the deletion point.
6. If rejected, continue after the candidate range.

This avoids batching decisions from a stale graph. Once a line is removed, downstream lowered facts,
goal ranges, and dependencies can all change, so the graph is rebuilt before continuing.
