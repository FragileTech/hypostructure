# Erdős–Gyárfás Lean port: current compliance boundary

Status date: 2026-08-30

This file is a compact view of the remaining compliance work.
[`Assembly_node_audit.md`](Assembly_node_audit.md) is the per-label and per-node
authority; `to_formalize/erdos_64_proof.tex` is the mathematical authority.

## Compliance standard

A node is complete only when its literal incoming `ExactLedger` reaches a sealed owner,
every prerequisite is obtained through `FactInputs.get` or `ExactLedger.get`, every reusable
conclusion is registered under its canonical key, the outgoing residual matches the manuscript,
and the composed term kernel-checks. A successful local build does not prove manuscript fidelity,
and an implemented residual is not the same thing as a closed branch.

## What is implemented

The current audit records the following segments as implemented on their literal residuals:

- `[49]`–`[52]`: the low-entropy branch now proves the dominant rooted type, splits on the
  rooted wedge, and runs the independent-translate row only on the wedge arm;
- `[64]`, `[70]`, and `[79]`–`[85]`: the common Type-B local geometry, shoulder completion,
  port return, first landing, cross-shoulder routing, global/local bridge, and branch-specific
  mass rows exist;
- `[123]`: the exact unified census is required at the type boundary, the full incoming key
  list is retained, true route-8 entries close only at `[124]`, and failed reduced rate publishes
  the exact node-`[181]` residual;
- `[125]`: a routing-only identity accepting only `K .sparseSurplusSurvivor`; the enclosing
  `[20]` decision owns the sparse target-defect exit;
- `[153]`, `[157]`, `[168]`, `[170]`, and `[171]`: the current table records the prescribed
  source-local facts and covered continuations;
- `[173]`–`[180]`: the covered collision, absorbed-germ, pair-system, and increment-arithmetic
  arms are represented, while exact negative complements are retained rather than renamed.

## Remaining node obligations

| Boundary | Current implementation | What remains |
| --- | --- | --- |
| `[75]`–`[77]` | Complete on the prescribed low-surplus Type-B residuals from `[64]` and `[177]`: every accounting ledger enters branch-kill and Part IX on the same ExactLedger. | No local work remains. The resulting honest sublinear, quotient, and peeled-demand residuals are governed by their own downstream nodes. |
| `[64]`, `[144]`, `[177]` call sites | Ancestry and freshness are repaired. `[64]` and `[177]` consume `[75]`–`[77]`; strict-surplus `[144]` returns the manuscript's exact `typeBFanEntry` handoff and does not import the incompatible low-surplus estimate. | No local work remains. |
| `[172a]` | `[170]` publishes the exact least failed fixed-scale fibre. | Construct the manuscript's cardinality-minimal connected overlap support and execute its uncrossing alternatives. No live producer currently does this. |
| `[172b]`–`[172c]` | The arithmetic library contains reusable results. | These nodes are unreachable until `[172a]` produces the graph-derived serial system; then perform the exact compatible central lift and full-state routing on that system. |
| `[181]` | `route8PeeledDemandResidualRow` publishes the exact peeled target-defect demand residual and retains all pre-`[123]` facts. | Prove the manuscript-prescribed consumer on this residual. No current consumer closes it. Do not move this mathematics into `[123]`. |
| `[182]` | `PairUncoveredResidual` retains exactly the failed implication from `[178]`, `[179]`, or `[180]`. | Prove the corresponding implication or extend the manuscript with an explicit faithful continuation. It is an honest open endpoint, not a closed theorem. |

## Literal selected-root boundary

`selectedLedgerBoundary` currently returns `SelectedLedgerBoundaryResult`, whose four top-level
alternatives are:

1. `sparseTargetDefectResidual` from the enclosing `[20]` sparse-exit classification;
2. a routed `typeBFanEntry` from strict-surplus `[144]` or early pair-system outcomes;
3. `pairConditionalFactorizationResidual`, the shared node-`[182]` key;
4. `SelectedNearCubicSurvivorBoundary`.

The fourth alternative expands to route-8 sublinear, quotient, and peeled-demand residuals;
cold-closure and blocked-overlap residuals; a failed route-8 rate; and the same
blocked-overlap/cold-closure facts returned by the dense path. None is definitionally
`False`. Therefore the selected root is not a proof of the target theorem.

## Aggregate validation

The synchronized table check passes:

```bash
python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check --repo-root .
```

A fresh one-worker check of `Assembly.lean` elaborates the repaired `[64]`, `[144]`,
`[177]`, and `[75]`–`[77]` regions. It next stops around lines 7551–7552, where the
generic cold-route callback quantifies over an abstract `known'` without transporting
`contractionCritical` and the freshness proofs required by
`selectedNetChargeContinuation`. Consequently:

- local owner/module checks may be cited only where the audit row names them;
- claims that the complete current `Assembly.lean` or package root kernel-check are stale;
- the checked-in axiom audit cannot be regenerated from the current aggregate module;
- `StrategyDag.lean` has no final `strategyDag` declaration, only two definitional-equality
  examples.

## Completion order

1. Implement `[172a]`, then `[172b]`–`[172c]` on the graph-derived serial system it publishes.
2. Close `[181]` and `[182]` from their exact incoming ledgers.
3. Reduce `SelectedLedgerBoundaryResult` to a closed target and only then author the final sealed
   topology endpoint in `StrategyDag.lean`.
