# Exact current selected-ledger boundary

The public finite-graph entry is
`officialCounterexample_reaches_selectedLedgerBoundary` in
`Assembly/Final.lean`. Its selected continuation is
`selectedLedgerBoundary`. Both use the canonical `ExactLedger` producers;
neither excludes an endpoint.

`SelectedLedgerBoundaryResult` has nine top-level outcomes. Its sixth outcome,
`OtherReturnedOutcome` ([187]), is itself a disjunction of six residuals, so
the boundary consists of 14 returned residuals. Each residual is stated in
`Assembly/Residuals.lean` as the explicit conjunction of every fact on its
maximal ledger (the facts common to every path that reaches it). Every return
site calls that residual's return theorem, which reads each fact with one
`ExactLedger.get`. The fact lists are in `Residuals.lean`. The counts below are
the number of conjuncts, including the arm-specific facts of residuals that
have their own decision.

| # | Top-level outcome | Residual (`Residuals.lean`) | Return theorem(s) | Facts |
| --- | --- | --- | --- | ---: |
| 1 | [20a] | `Node20aOutcome` | `node20aReturn` | 18 |
| 2 | [144a] | `Node144aOutcome` | `node144aHandoffReturn`, `node144aFailsReturn` | 44 + (2 / 3) |
| 3 | [172a] | `BlockedBarrierOverlapOutcome` | `blockedBarrierOverlapReturn` | 71 |
| 4 | [182] | `PairConditionalFactorizationOutcome` | `pairConditionalFactorizationReturn` | 33 |
| 5 | [186] | `Route8JointBalanceOutcome` | `route8JointBalanceReturn` | 79 |
| 6 | [187] `OtherReturnedOutcome` | `NearCubicTargetDefectOutcome` | `nearCubicTargetDefectReturn` | 18 |
| | | `PairTypeBOutcome` ([179]/[180] Type B entry) | `pairTypeBSystemReturn`, `pairTypeBIncrementReturn` | 37 + (1 / 4) |
| | | `TypeBSublinearOutcome` | `typeBSublinearReturn` | 62 |
| | | `Route8QuotientOutcome` ([348]) | `route8QuotientReturn` | 64 |
| | | `Route8RateFailsOutcome` | `route8RateFailsReturn` | 42 |
| | | `ColdBranchClosedOutcome` | `coldBranchClosedReturn` | 57 |
| 7 | [153] | `Node153ResidualOutcome` | `node153Return` | 42 |
| 8 | [162] | `Node162ResidualOutcome` | `node162Return` | 46 |
| 9 | [54] | `Node54ResidualOutcome` | `node54Return` | 40 |

The selected root's returns map exhaustively to these outcomes:

| Producer return | Outcome |
| --- | --- |
| Strict [20] sparse target defect (`sparseSurplusExitRoutingRow`, then `sparseTargetDefectStructureRow`, on the exit arm of `sparseSurplusSurvivorDichotomy`) | [20a] |
| Strict same-token bottleneck: the Type B handoff, or the unresolved same-label pattern pair (`selectedBottleneckDischarge`) | [144a] |
| Strict uncovered pair-system implication | [182] |
| Strict [179] or [180] Type B entry | [187] |
| Near-cubic sparse target defect | [187] |
| Near-cubic blocked barrier overlap | [172a] |
| Near-cubic route-8 joint balance | [186] |
| Near-cubic Type B sublinear, route-8 quotient, route-8 rate, or cold-terminal return | [187] |
| Near-cubic first equal-state pair on a retained cold corridor | [153] |
| Near-cubic heavy-centre first failure on a dense cold pass | [162] |
| Near-cubic failure of the joint realization inequality | [54] |

This is a routing partition of the existing return constructors, not a
count of independent unfinished mathematical branches.

`Holds sparseTargetDefectResidual` is an attempted quotient with
noninjective labels and identified reduced/full realizations differing on
the target. It is not a cycle in the selected graph.
`Holds typeBHandoff` contains the actual active family, capacity
presentation, homogeneous source pattern, maximal packing, core, and
decorated envelope. It does not imply a homogeneous cap. The [179]/[180]
Type B entries have their own source keys. The strict [20a] residual carries
`surplusAbove`, and the near-cubic target defect carries `surplusAtOrBelow`.
These producer histories are kept apart before projection to the common
semantic facts. The former Lean theorem
`node20a_nearCubicTargetDefect_disjoint` proved the two surplus ancestries
incompatible; it was removed as dead code.

A fact that is present on some paths to a residual but cannot be derived on
the others is not part of that residual. Such facts are listed in
`audits/erdos-64-red-team/lean-vs-paper-discrepancies.md`.

## Kernel verification

`lake build HypostructureErdos64EG` (in `proofs/hypostructure_erdos_64_eg`)
completes successfully. Both `selectedCounterexample_reaches_exactBoundary` and
`officialCounterexample_reaches_selectedLedgerBoundary` are declarations in
the compiled `Assembly.Final` owner. Their `#print axioms` results agree:
`propext`, `Classical.choice`, `Quot.sound`, generated `native_decide` axioms,
and the existing external Hegde--Sandeep--Shashank theorem axiom
`p13Free_hasPowerOfTwoCycle`. The reduction introduces no new axiom.
