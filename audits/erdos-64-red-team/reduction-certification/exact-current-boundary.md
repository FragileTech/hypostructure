# Exact selected-ledger boundary

The public finite-graph entry is
`officialCounterexample_reaches_selectedLedgerBoundary` in
`Assembly/Final.lean`.  Its selected continuation is `selectedLedgerBoundary`.
Both use the canonical `ExactLedger` producers; neither excludes an endpoint.

`SelectedLedgerBoundaryResult` (`Final.lean`) is a disjunction of six outcome
families with 43 top-level residual subtypes.  Each generic residual is stated
in `Assembly/Residuals.lean` as the explicit conjunction of every fact on its
ledger; each subtype (`Assembly/Residuals/*.lean`) adds the facts of its own
path, and every return site reads each fact with one `ExactLedger.get`.  Counts
are the numbers of `Holds` conjuncts in the abbrevs ("+k" is a subtype's extra
conjuncts).  The open proposition of each family is in
`audits/erdos-64-red-team/lean-vs-paper-discrepancies.md`, "Open propositions".

| # | Family | Residual | Subtypes | Generic facts | Return theorems |
| --- | --- | --- | --- | ---: | --- |
| 1 | [144a] | `Node144aOutcome` | 6: `windowHandoff` (+3), `windowFails` (+18), `remainderHandoff` (+4), `remainderFails` (+19), `primitiveHandoff` (+5), `primitiveFails` (+20) | 136 | `node144a{Window,Remainder,Primitive}{Handoff,Fails}Return` |
| 2 | [172a] | `BlockedBarrierOverlapOutcome` | 2: `DeficiencyAtOrAbove` (+1), `DeficiencyBelowRateFails` (+2) | 125 | `blockedBarrierOverlapReturn_*` |
| 3 | [182] | `PairConditionalFactorizationOutcome` | 6: free / blocked × factorization / realizability / increment fails (+3, +8, +12; +12, +17, +21) | 120 | `pairConditionalFactorizationReturn_*` |
| 4 | [186] | `Route8JointBalanceOutcome_product` | 1 product (generic ∧ `Route8LaneEntry` ∧ `NetChargeContinuation`, 750 paths) | 146 | `route8JointBalanceProductReturn` |
| 5 | [187] `OtherReturnedOutcome` | `PairTypeBOutcome` ([179]/[180] Type B entry) | 2: `independentSystem` (+2), `dependentSystem` (+11) | 133 | `pairTypeBIndependentSystemReturn`, `pairTypeBDependentSystemReturn` |
| | | `TypeBSublinearOutcome_product` | 1 product (750 paths) | 128 | `typeBSublinearProductReturn` |
| | | `Route8QuotientOutcome_product` ([348]) | 1 product (750 paths) | 133 | `route8QuotientProductReturn` |
| | | `Route8RateFailsOutcome` | 11 (+5 to +9), all `n < N₀` | 113 | `route8RateFailsReturn_*` |
| | | `ColdBranchClosedOutcome` | 8 (+8 to +18); `linearRealizedSilent`, `linearRealizedDistinguished` are `n < N₀` | 105 | `coldBranchClosed_*Return` |
| 6 | [54] | `Node54ResidualOutcome` | 5: `realizedColdBelow` (+3), `realizedBounded` (+6), `unrealizedTauHighBounded` (+7), `unrealizedRateFailsBounded` (+8), `unrealizedBothRates` (+3) | 92 | `node54Return_*` |

Sixteen of the 43 subtypes carry the order bound `n < N₀`
(`K .realizedOrderSmall` or `K .boundedOrderSmall`): the eleven
`Route8RateFailsOutcome_*` subtypes, `Node54ResidualOutcome_realizedBounded`,
`_unrealizedTauHighBounded`, `_unrealizedRateFailsBounded`, and
`ColdBranchClosedOutcome_linearRealizedSilent`, `_linearRealizedDistinguished`.
Inside each of the three products, the 400 of 750 paths through
`Route8LanePrefixBlock_realizedColdAtOrAbove` and
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`
(`Residuals/Route8Blocks.lean`) carry it as well.

`[20a]` and the near-cubic target defect of `[187]` close at G: exit (b) of
`[125]`, stated about G, is empty (`lem:sparse-exit-b-empty`;
`K .sparseTargetDefectEmpty`, key 7800, `selectedSparseExitClosed`,
`Assembly/NearCubic/Local.lean`).  `[153]`'s equal-state pair is the repeat
subcase of (F5) and continues into the germ routing, reaching `[187]` as the
`_repeated` cold-terminal subtypes.  The dense cold pass `[162]` continues to
`[187]` and `[54]`.

The selected root's returns map exhaustively to these families:

| Producer return | Outcome |
| --- | --- |
| Strict [20] sparse target defect (exit arm of `sparseSurplusSurvivorDichotomy`) | closed at G (exit (b) empty) |
| Strict same-token bottleneck: the Type B handoff, or the unresolved same-label pattern pair (`selectedBottleneckDischarge`) | [144a] |
| Strict uncovered pair-system implication | [182] |
| Strict [179] Type B entry (system arm; the [180] periodic arm is empty at G) | [187] |
| Near-cubic sparse target defect | closed at G (exit (b) empty) |
| Near-cubic blocked barrier overlap | [172a] |
| Near-cubic route-8 joint balance | [186] |
| Near-cubic Type B sublinear, route-8 quotient, route-8 rate, or cold-terminal return (incl. the `[153]` repeat arm) | [187] |
| Near-cubic failure of the joint realization inequality | [54] |

This is a routing partition of the return constructors, not a count of
independent unfinished mathematical branches.

A fact that is present on some paths to a residual but cannot be derived on
the others is not part of that residual; it belongs to the subtype or product
arm whose path carries it.

## Kernel verification

`lake build HypostructureErdos64EG` (in `proofs/hypostructure_erdos_64_eg`)
builds `Assembly.Final`, which declares
`selectedCounterexample_reaches_exactBoundary` and
`officialCounterexample_reaches_selectedLedgerBoundary`.  Their axioms are
`propext`, `Classical.choice`, `Quot.sound`, generated `native_decide` axioms,
and the external Hegde--Sandeep--Shashank theorem axiom
`p13Free_hasPowerOfTwoCycle`; the reduction introduces no other axiom.  The
kernel axiom audit `web/data/eg_axiom_audit.json` records all 347 assembly
declarations clean, with no frontier stubs and no tainted declarations.
