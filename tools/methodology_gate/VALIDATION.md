# Structural reasoning workflow validation

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the retained objects, match the hypotheses of the relevant textbook result, execute the deduction, and check the requested output. Give routine steps concise, sufficient justification. Reuse accepted prerequisites at their stated types and domains. A review objection identifies a concrete missing hypothesis, invalid inference, domain mismatch, or unmet task contract and its local repair. Preserve the assigned objectives, stage boundaries, mathematical statements, and required checks.

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

Inspect the selected run for its accepted prefix and next assignment. Validation
results describe their exact run and source revision.
