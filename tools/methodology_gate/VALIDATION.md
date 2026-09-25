# Structural reasoning workflow validation

The shared workflow is unversioned. New task queues use Phase 0 followed by
Phases 1–8 from `policy/workflow.json`. `test_taskflow.py` covers exact branch
snapshots, one-task dispatch, two cited reviews, conditional payoff and outcome
coverage, integration priority, transport and account checks, finite-table
survivors, sibling branches, stale evidence invalidation, and the CLI templates.
The queue checks the shape, freshness, dependency, and review records; it does
not decide arbitrary mathematical implications. Accepted proof artifacts and
required Lean checks supply that evidence.

The existing isolated EG stage runner uses `1 → 2 → 3 → 3b →
4 → 5 → 6 → 7 → 8`. Stage 3b proves the selected structure for the exact
incoming residual in Lean and publishes one reviewed fact in the canonical
`ExactLedger`. Stage 4 must consume that fact on the same bound witness.

The controller rejects any record that skips Stage 3b. It does not import
closure attempts made under an earlier stage order. Accepted stages remain
locked and are carried forward exactly.

Stage 3b's assignment now carries only the exact incoming residual, retained
fact IDs and selected Stage 3 structural opportunity as its mathematical
focus. Its artifact must name the incoming residual key, owner-local ledger
row, exact bound witness and same-witness projection for each selected claim.
The independent reviewers check these against the Lean statement and locked
kernel result.

Node 20's current controller record is
`/tmp/hypostructure-methodology/node20-current`. It contains only the accepted
Stage 1, 2, and 3 events. Its next obligation is Stage 3b. No Stage 3b fact or
Node 20 closure has been accepted yet.
