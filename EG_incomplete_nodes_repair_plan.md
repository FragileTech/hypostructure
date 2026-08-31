# Erdős–Gyárfás incomplete nodes and repair plan

Status date: 2026-08-31

This plan lists only work that remains after reconciling the manuscript, live Lean declarations,
literal call sites, and [`Assembly_node_audit.md`](Assembly_node_audit.md).

## Non-negotiable repair rule

The manuscript determines the proposition, branch order, and destination. Every repair must:

- consume the literal incoming residual and its accumulated `ExactLedger`;
- retrieve required facts through the canonical input API rather than re-proving them;
- publish every reusable conclusion under the canonical key;
- preserve all incoming keys monotonically;
- avoid callbacks, detached theorem parameters, compatibility routes, synthetic residuals, or
  a stronger/weaker substitute for the paper's statement.

## Current boundary

Node `[85]` is closed. Its degree-four Type-B route now executes the complete triangular
shoulder/port prefix, the fan-closed and triangular routing corollaries, the certificate/B1/B2
split, the five-clause global/local bridge on the obstruction arm, and the fan-mass/sublinear
tail on one monotone `ExactLedger`. The full `Assembly.lean` file kernel-checks with one Lean
worker under the 16 GiB ceiling. None of the remaining repairs below is a missing premise of
Node `[85]`.

The live root is not reduced to `[172a]`, `[181]`, and `[182]`. It also exposes the enclosing
`[20]` sparse target-defect handoff, routed pair-system and strict-surplus Type-B entries,
route-8 sublinear/quotient/rate residuals, cold-closure facts, and blocked-overlap facts. The exact expansion is recorded in
[`EG_LEAN_COMPLIANCE_REMAINING.md`](EG_LEAN_COMPLIANCE_REMAINING.md).

The repair frontier is:

1. the graph-derived overlap/serial chain `[172a]`–`[172c]`;
2. exact open residual `[181]`;
3. exact open residual `[182]`;
4. the missing final topology endpoint in `StrategyDag.lean`.

## Repair 1 — implement `[172a]`–`[172c]`

`[170]` already supplies the exact least failed scale, prefix, outside record, graph multiplicity,
state-fibre bound, and reverse ratio. On that ledger:

1. `[172a]`: construct the cardinality-minimal connected overlap support and prove the
   manuscript's exhaustive uncrossing alternatives;
2. route alternatives (i)–(iv) only after producing their concrete G1/G2/G3 or declared-handoff
   witnesses;
3. publish the graph-realized serial system for alternative (v);
4. `[172b]`: perform the exact compatible central-lift test on that system;
5. `[172c]`: on the literal complement, retain the full residue, cold cut state, degree profile,
   truncated distances, rare choices, and trace incidences until an existing destination witness
   is produced.

The reusable arithmetic library is not a substitute for the missing graph-derived producer.

## Repair 2 — close `[181]`

Node `[123]` is complete and must remain unchanged: it retains the full prefix, closes the true
route-8 arm at `[124]`, and publishes `route8PeeledDemandResidual` on failed rate. New mathematics
belongs to a consumer of that exact node-`[181]` ledger. The consumer must read the stage
accounting, demand ledger, absorption, blockers, and all upstream facts from the ledger and prove
the manuscript's prescribed conclusion without assuming a sublinear pressure or zero-shadow cap
that the residual does not contain.

## Repair 3 — close `[182]`

`PairUncoveredResidual` has three exact constructors:

1. the pair-response model with failed conditional factorization;
2. the retained return package with no `[179]` uncrossing outcome;
3. the graph-realized serial system with no `[180]` arithmetic/periodic outcome.

Prove the corresponding manuscript implication on each constructor's retained data. Do not merge
the constructors, rename a failure as a closed alternative, or route an abstract arithmetic
system as though it were already a cycle in the selected graph.

## Repair 4 — close the root and author topology

Only after all semantic outputs of `SelectedLedgerBoundaryResult` are consumed may Assembly expose
a closed target. `StrategyDag.lean` should then contain the sealed root topology that consumes that
closed result. Its present two `example`s prove only definitional agreement of the problem and
target presentations.

## Validation gates

After each repair:

```bash
python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check --repo-root .
LEAN_NUM_THREADS=1 lake env lean HypostructureErdos64EG/Assembly.lean
git diff --check
```

Use the 16 GiB ceiling if the aggregate Lean command requires it. Regenerate the web node and axiom audit
data after the aggregate module succeeds. Until then the axiom audit must remain explicitly
unavailable rather than present unverified classifications as kernel evidence.
