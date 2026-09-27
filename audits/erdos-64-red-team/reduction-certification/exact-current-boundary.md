# Exact current selected-ledger boundary

The public finite-graph entry is
`officialCounterexample_reaches_selectedLedgerBoundary` in
`Assembly/Final.lean`. Its selected continuation is
`selectedLedgerBoundary`. Both use the canonical `ExactLedger` producers;
neither excludes an endpoint.

| Endpoint | Literal producer | Exposed facts |
| --- | --- | --- |
| [20a] | `sparseSurplusExitRoutingRow`, followed by `sparseTargetDefectStructureRow`, run in `selectedLedgerBoundary` on the exit arm of `sparseSurplusSurvivorDichotomy` (strict left arm of [20]) | `sparseTargetDefectResidual`, `sparseTargetDefectStructure`, `sparsePairExit`, `surplusAbove` |
| [144a] | `selectedBottleneckDischarge` on the caps-fail arm of `homogeneousBottleneckDichotomy` ([144]), after the audit row `homogeneousBottleneckAuditRow` at any of the three strict token classes; `Node144aOutcome` is read from the routed ledger | `typeBHandoff`, `typeBFanEntry`, `bottleneckRouting`, `homogeneousBottleneckPattern`, `sparsePressureOverload`, `capacityTokenLedger`, `surplusAbove`, `sparseSurplusSurvivor` |
| [172a] | blocked barrier failure after the negative [170] decision | `blockedBarrierOverlap` at its previously proved strength |
| [182] | first uncovered pair-system implication | `pairConditionalFactorizationResidual` at its previously proved strength |
| [186] | visible-entry route-8 balance | `route8JointBalance` at its previously proved strength |
| [187] | explicit disjunction in `OtherReturnedOutcome` | `typeBSublinearResidual`, `route8QuotientResidual`, `route8RateFails`, or `coldBranchClosed`, each with `surplusAtOrBelow`; near-cubic `sparseTargetDefectResidual` and `sparseTargetDefectStructure` with `surplusAtOrBelow`; or `typeBFanEntry` with `pairSystemEarlyOutcome` or `pairIncrementEarlyOutcome`, `surplusAbove`, and `sparseSurplusSurvivor` |

The selected root's returns map exhaustively to the six endpoints:

| Producer return | Endpoint |
| --- | --- |
| Strict [20] sparse target defect | [20a] |
| Strict same-token bottleneck Type B handoff | [144a] |
| Strict uncovered pair-system implication | [182] |
| Strict [179] or [180] Type B entry | [187] |
| Near-cubic sparse target defect | [187] |
| Near-cubic blocked barrier overlap | [172a] |
| Near-cubic route-8 joint balance | [186] |
| Near-cubic Type B sublinear, route-8 quotient, route-8 rate, or cold-terminal return | [187] |

This is a routing partition of the existing return constructors, not a
count of independent unfinished mathematical branches.

The exact [20a] outgoing key list is:

```text
sparseTargetDefectStructure, sparseTargetDefectResidual,
sparsePairExit, surplusAbove, localAlgebra, maximalPacking,
uncompressible, replacementExclusion, targetCompleteContextUniversality,
degreeProfileFibres, cycleRankConstraint, tightEndpoint,
slackIndependent, noProperBaseline, returnAvoidance,
contractionCritical, gadgetClosure, relabelingDensityCap,
cubicBaseline, selection
```

The exact ledger returned by `selectedBottleneckDischarge` is
`[typeBFanEntry, bottleneckRouting, typeBHandoff] ++ known`;
`Assembly.Internal.strictSurplusDependent` reads the eight `Node144aOutcome`
facts from that same ledger with `.get … .down`. No Type B certificate core
runs on this endpoint.
`selectedBottleneckDischarge` requires these keys in `known`:

```text
homogeneousBottleneckPattern, sparsePressureOverload,
blockedPairEntropySandwich, roleFibrePartition, fibrePressure,
baselineSpineDemand, sparseSlackSurplus, surplusAbove,
activeSurplusDemands, sparsePortActivation, activeSurplusFamily,
cubicBaseline, capacityTokenLedger, canonicalPairLedger,
canonicalBlockerRoute, dependentPairFamily, sparseUpperEnvelope,
maximalPacking, selection, bridgeless, returnAvoidance, tightEndpoint,
slackIndependent, highCentreNormalForm, localAlgebra,
degreeProfileFibres, targetCompleteContextUniversality,
replacementExclusion, exactResponseProfile,
admissibleRankQuotient, uncompressible, noProperBaseline,
remainderNormalized, remainderRelabelingEntropy,
sparseSurplusSurvivor
```

`Holds sparseTargetDefectResidual` is an attempted quotient with
noninjective labels and identified reduced/full realizations differing on
the target. It is not a cycle in the selected graph.
`Holds typeBHandoff` contains the actual active family, capacity
presentation, homogeneous source pattern, maximal packing, core, and
decorated envelope. It does not imply a homogeneous cap. The [179]/[180]
Type B entries have their own source keys; the near-cubic sparse exit has
`surplusAtOrBelow`. These producer histories are kept apart before
projection to the common semantic facts: the strict arm carries
`surplusAbove` and the near-cubic arm `surplusAtOrBelow`. (The former
Lean theorem `node20a_nearCubicTargetDefect_disjoint`, which proved the two
surplus ancestries incompatible, was removed as dead code.) [144a] includes `typeBHandoff` explicitly,
whereas the pair-system return type supplies only its [179]/[180] source
key and `typeBFanEntry`.

## Kernel verification

`lake build HypostructureErdos64EG` (in `proofs/hypostructure_erdos_64_eg`)
completed successfully with 9029 jobs. Both `selectedCounterexample_reaches_exactBoundary` and
`officialCounterexample_reaches_selectedLedgerBoundary` are declarations in
the compiled `Assembly.Final` owner. Their `#print axioms` results agree:
`propext`, `Classical.choice`, `Quot.sound`, generated `native_decide` axioms,
and the existing external Hegde--Sandeep--Shashank theorem axiom
`p13Free_hasPowerOfTwoCycle`. The reduction introduces no new axiom.
