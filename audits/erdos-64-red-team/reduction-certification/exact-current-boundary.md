# Exact current selected-ledger boundary

*Current as of 2026-09-30 (Lean state `6abf8f58`).  The per-subtype table with
fact counts is in the "Current state (2026-09-30)" section at the top of
`audits/erdos-64-red-team/lean-vs-paper-discrepancies.md`.*

The public finite-graph entry is
`officialCounterexample_reaches_selectedLedgerBoundary` in
`Assembly/Final.lean`.  Its selected continuation is
`selectedLedgerBoundary`.  Both use the canonical `ExactLedger` producers;
neither excludes an endpoint.

`SelectedLedgerBoundaryResult` (`Final.lean` l.136) is a disjunction of six
outcome families with 43 top-level residual subtypes.  Each generic residual is
stated in `Assembly/Residuals.lean` as the explicit conjunction of every fact
on its ledger; each subtype (`Assembly/Residuals/*.lean`) adds the facts of its
own path, and every return site reads each fact with one `ExactLedger.get`.
Counts are the number of `Holds` conjuncts in the abbrev (counted from the
Lean, not from docstrings; "+k" is the subtype's extra conjuncts).

| # | Family | Residual | Subtypes | Generic facts | Return theorems |
| --- | --- | --- | --- | ---: | --- |
| 1 | [144a] | `Node144aOutcome` | 6: `windowHandoff` (+3), `windowFails` (+18), `remainderHandoff` (+4), `remainderFails` (+19), `primitiveHandoff` (+5), `primitiveFails` (+20) | 136 | `node144a{Window,Remainder,Primitive}{Handoff,Fails}Return` |
| 2 | [172a] | `BlockedBarrierOverlapOutcome` | 2: `DeficiencyAtOrAbove` (+1), `DeficiencyBelowRateFails` (+2) | 125 | `blockedBarrierOverlapReturn_*` |
| 3 | [182] | `PairConditionalFactorizationOutcome` | 6: free / blocked × factorization / realizability / increment fails (+3, +8, +12; +12, +17, +21) | 120 | `pairConditionalFactorizationReturn_*` |
| 4 | [186] | `Route8JointBalanceOutcome_product` | 1 product (generic ∧ `Route8LaneEntry` ∧ `NetChargeContinuation`) | 146 | `route8JointBalanceProductReturn` |
| 5 | [187] `OtherReturnedOutcome` | `PairTypeBOutcome` ([179]/[180] Type B entry) | 2: `independentSystem` (+2), `dependentSystem` (+11) | 133 | `pairTypeBIndependentSystemReturn`, `pairTypeBDependentSystemReturn` |
| | | `TypeBSublinearOutcome_product` | 1 product | 128 | `typeBSublinearProductReturn` |
| | | `Route8QuotientOutcome_product` ([348]) | 1 product | 133 | `route8QuotientProductReturn` |
| | | `Route8RateFailsOutcome` | 11 (+5 to +9), all `n < N₀` | 113 | `route8RateFailsReturn_*` |
| | | `ColdBranchClosedOutcome` | 8 (+8 to +18); `linearRealizedSilent`, `linearRealizedDistinguished` are `n < N₀` | 105 | `coldBranchClosed_*Return` |
| 6 | [54] | `Node54ResidualOutcome` | 5: `realizedColdBelow` (+3), `realizedBounded` (+6), `unrealizedTauHighBounded` (+7), `unrealizedRateFailsBounded` (+8), `unrealizedBothRates` (+3) | 92 | `node54Return_*` |

Sixteen of the 43 subtypes carry the order bound `n < N₀`
(`K .realizedOrderSmall` or `K .boundedOrderSmall`): the eleven
`Route8RateFailsOutcome_*` subtypes, `Node54ResidualOutcome_realizedBounded`,
`_unrealizedTauHighBounded`, `_unrealizedRateFailsBounded`, and
`ColdBranchClosedOutcome_linearRealizedSilent`, `_linearRealizedDistinguished`
(`Residuals/ColdBranchClosedOutcome.lean` l.63, l.553).  Inside the three
products, the paths through `Route8LanePrefixBlock_realizedColdAtOrAbove` and
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`
(`Residuals/Route8Blocks.lean` l.51, l.84) carry it as well.

No longer returned: `[20a]` and the near-cubic target defect of `[187]` (exit
(b) of `[125]`, stated about G, is empty: `K .sparseTargetDefectEmpty`, key
7800, `selectedSparseExitClosed`, `NearCubic/Local.lean` l.93); `[153]` (its
equal-state pair continues into `[187]`'s `_repeated` cold-terminal subtypes);
`[162]` (the dense pass needs no heavy-entry terminality).

The selected root's returns map exhaustively to these families:

| Producer return | Outcome |
| --- | --- |
| Strict [20] sparse target defect (exit arm of `sparseSurplusSurvivorDichotomy`) | closed at G (exit (b) empty) |
| Strict same-token bottleneck: the Type B handoff, or the unresolved same-label pattern pair (`selectedBottleneckDischarge`) | [144a] |
| Strict uncovered pair-system implication | [182] |
| Strict [179] or [180] Type B entry (system arm; the increment arm is empty at G) | [187] |
| Near-cubic sparse target defect | closed at G (exit (b) empty) |
| Near-cubic blocked barrier overlap | [172a] |
| Near-cubic route-8 joint balance | [186] |
| Near-cubic Type B sublinear, route-8 quotient, route-8 rate, or cold-terminal return (incl. the `[153]` repeat arm) | [187] |
| Near-cubic failure of the joint realization inequality | [54] |

This is a routing partition of the existing return constructors, not a
count of independent unfinished mathematical branches.

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

The kernel axiom audit of 2026-09-30 (`web/data/eg_axiom_audit.json`, at
`6abf8f58`) records all 347 assembly declarations clean, with no frontier
stubs.  The build statement above was not re-run for this update.

## Superseded (2026-09-30): the earlier boundary description

> Superseded (2026-09-30): the text below described an older root type (nine
> top-level outcomes, 14 residuals, with `[20a]`, the near-cubic target defect,
> `[153]` and `[162]`, and older fact counts).  Kept as history.

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
