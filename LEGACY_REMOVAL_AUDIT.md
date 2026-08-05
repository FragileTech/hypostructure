# Legacy removal audit -- Core and Graph

Scope: `hypostructure/Hypostructure/Core`, `Graph`, and the `CT*` layer they
carry. `PDE/` and the retired frontend are out of scope; `Fixtures/` is reported
only as a count.

**Method, and what it proves.** The live build closure is the transitive
`import` closure of the two roots `hypostructure/Hypostructure.lean` and
`proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG.lean`. In Lean an
`import` is the only way one module reaches another, so a module outside that
closure cannot affect what compiles: **deleting anything listed below is a no-op
for `make build`** by construction, not by inspection. The tiers add the only
other question that matters -- whether you would keep it anyway, as porting
reference for a row the audit still lists as open.

Counts, measured on the 2026-08-05 working tree:

| | modules | lines |
|---|---|---|
| live in the build closure | 165 | -- |
| dead, all namespaces | 663 | -- |
| dead in Core / Graph / CT (this audit) | 367 | 102,438 |
| -- Tier 1: delete now, unconditional | 273 | 43,753 |
| -- Tier 2: delete now, row already ported | 44 | 22,398 |
| -- Tier 3: keep as porting reference | 50 | 36,287 |

Two things before the lists.

*Deletion is recoverable.* Every file here is committed, so
`git log --diff-filter=D` brings any of it back. Keeping a file on disk is about
discoverability, not preservation.

*`quarantine.txt` is not the inventory.* It lists 306 modules; 663 are actually
dead. Entries marked **unlisted** below are dead *and* unquarantined -- the
canonical-ledger gate never looks at them, so those are the ones that rot
silently.

---

## Tier 1 -- delete now, independent of any remaining row (273 modules, 43,753 lines)

These implement retired *APIs*, not mathematics. The single-official-API rule
means no future port may use them whatever row it is porting, so their
porting-reference value is zero.

### 1a. The CT capability/certificate layer (151 modules, 22,621 lines)

Whole directories. The canonical API has no `Capability`, `Certificate`,
`Search`, `Automation` or `Execution` stage; `AtomicCT.run` replaces all of it.

| directory | files | lines |
|---|---|---|
| `Hypostructure/CT1/` | 9 | 1698 |
| `Hypostructure/CT10/` | 7 | 904 |
| `Hypostructure/CT11/` | 8 | 889 |
| `Hypostructure/CT12/` | 8 | 1033 |
| `Hypostructure/CT13/` | 7 | 1796 |
| `Hypostructure/CT14/` | 7 | 904 |
| `Hypostructure/CT15/` | 7 | 1302 |
| `Hypostructure/CT16/` | 7 | 1349 |
| `Hypostructure/CT17/` | 7 | 1255 |
| `Hypostructure/CT2/` | 7 | 784 |
| `Hypostructure/CT3/` | 12 | 1859 |
| `Hypostructure/CT4/` | 8 | 1265 |
| `Hypostructure/CT5/` | 7 | 917 |
| `Hypostructure/CT6/` | 7 | 623 |
| `Hypostructure/CT7/` | 7 | 1398 |
| `Hypostructure/CT8/` | 7 | 1072 |
| `Hypostructure/CT9/` | 8 | 1176 |
| `Hypostructure/CTAdapters/` | 1 | 207 |
| `Hypostructure/Canonical/` | 1 | 339 |
| `Hypostructure/Graph/` | 19 | 1851 |

(The `Graph/` line is `Graph/CT1.lean`--`CT17.lean` plus `Graph/InducedPathCT1.lean`
and `Graph/ObstructionCT1.lean`.)

### 1b. The legacy residual/ledger stack (17 modules, 3,302 lines)

The carriers `Core.Residual.ExactLedger` replaced outright.

| module | lines | listed? |
|---|---|---|
| `Core.ClosedLedger.Closure` | 142 | quarantined |
| `Core.ClosedLedger.Propagation` | 103 | quarantined |
| `Core.ClosedLedger.Quotient` | 123 | quarantined |
| `Core.Residual.Decision` | 572 | quarantined |
| `Core.Residual.DecisionExhaustion` | 59 | quarantined |
| `Core.Residual.Focus` | 800 | quarantined |
| `Core.Residual.Join` | 141 | quarantined |
| `Core.Residual.Ledger` | 93 | quarantined |
| `Core.Residual.NumericCap` | 225 | **unlisted** |
| `Core.Residual.ProofProjection` | 218 | quarantined |
| `Core.Residual.Query` | 166 | quarantined |
| `Core.Residual.Stage` | 92 | quarantined |
| `Core.Residual.Terminal` | 69 | **unlisted** |
| `Core.Response.FiniteTableLedger` | 59 | **unlisted** |
| `Core.SequentialExtensionLedger` | 191 | quarantined |
| `Graph.InducedPathColdQuery` | 162 | quarantined |
| `Graph.InducedPathWindowLedger` | 87 | quarantined |

### 1c. The Blueprint / ProblemDefinition registry (83 modules, 14,530 lines)

The framework half of the registration layer whose EG half (`Official/`, `AB/`,
`Presentation.lean`) is already deleted. `Core/Strategy/Official/Strategies/*`
is 33 registration shells averaging 40 lines; `Validate.lean` and `Data.lean`
are the validator and record for a topology that no longer exists. Note that
`Core/Strategy/Dag.lean` is **not** here -- rows 26 and 28 still cite
`Core.ScanData` / `Dag.liftScan`, so it sits in Tier 3.

| module | lines | listed? |
|---|---|---|
| `Core.Strategy` | 2141 | quarantined |
| `Core.Strategy.Data` | 798 | quarantined |
| `Core.Strategy.Execution` | 26 | **unlisted** |
| `Core.Strategy.Official` | 15 | **unlisted** |
| `Core.Strategy.Official.Availability` | 144 | quarantined |
| `Core.Strategy.Official.DomainDispatch` | 35 | **unlisted** |
| `Core.Strategy.Official.Features.DeletionFanAccounting` | 126 | quarantined |
| `Core.Strategy.Official.Features.ScaleDependentThreshold` | 272 | **unlisted** |
| `Core.Strategy.Official.FiniteTableKernel` | 182 | **unlisted** |
| `Core.Strategy.Official.ProblemDefinition` | 38 | quarantined |
| `Core.Strategy.Official.Schema` | 132 | quarantined |
| `Core.Strategy.Official.Semantics.FiniteEntropyPipeline` | 153 | **unlisted** |
| `Core.Strategy.Official.Semantics.SparseSurplusRefinement` | 145 | **unlisted** |
| `Core.Strategy.Official.Source` | 43 | **unlisted** |
| `Core.Strategy.Official.Strategies` | 36 | **unlisted** |
| `Core.Strategy.Official.Strategies.CanonicalReplacementSearch` | 38 | **unlisted** |
| `Core.Strategy.Official.Strategies.CapacityAccounting` | 27 | **unlisted** |
| `Core.Strategy.Official.Strategies.ClosedCodeExhaustion` | 30 | **unlisted** |
| `Core.Strategy.Official.Strategies.Common` | 20 | **unlisted** |
| `Core.Strategy.Official.Strategies.Composition` | 64 | **unlisted** |
| `Core.Strategy.Official.Strategies.ContextualQuotientSearch` | 46 | **unlisted** |
| `Core.Strategy.Official.Strategies.DefectiveLoadPeeling` | 24 | **unlisted** |
| `Core.Strategy.Official.Strategies.Dispatcher` | 201 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteContextQuotient` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteEligibleTokenLedger` | 39 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteErrorCoefficientSchedule` | 46 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteHomogeneousFibrePressure` | 55 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteObservationRank` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteObstructionAccounting` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteOverloadGeometry` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteRankCarrierCompression` | 55 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteRankEntropySupportComposition` | 48 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteReplacementClassification` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteResponseCapacity` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteStateBudget` | 39 | **unlisted** |
| `Core.Strategy.Official.Strategies.FiniteTraceSeparator` | 39 | **unlisted** |
| `Core.Strategy.Official.Strategies.FunctionalRankQuotient` | 46 | **unlisted** |
| `Core.Strategy.Official.Strategies.HighCenterFanClosure` | 48 | **unlisted** |
| `Core.Strategy.Official.Strategies.LabelledStateBudget` | 38 | **unlisted** |
| `Core.Strategy.Official.Strategies.MeasuredFinitePeel` | 24 | **unlisted** |
| `Core.Strategy.Official.Strategies.MeasuredFiniteRouting` | 92 | **unlisted** |
| `Core.Strategy.Official.Strategies.MultiplicativeRateTable` | 46 | **unlisted** |
| `Core.Strategy.Official.Strategies.OrderedExhaustion` | 22 | **unlisted** |
| `Core.Strategy.Official.Strategies.OrderedReceiverPressure` | 47 | **unlisted** |
| `Core.Strategy.Official.Strategies.PackedWindowTokenLedger` | 36 | **unlisted** |
| `Core.Strategy.Official.Strategies.RankBudget` | 28 | **unlisted** |
| `Core.Strategy.Official.Strategies.ReceiverExhaustion` | 24 | **unlisted** |
| `Core.Strategy.Official.Strategies.ResponseClassification` | 28 | **unlisted** |
| `Core.Strategy.Official.Strategies.SparseSurplus` | 37 | **unlisted** |
| `Core.Strategy.Official.Strategies.StrictReplacement` | 24 | **unlisted** |
| `Core.Strategy.Official.Strategies.SupportIncidenceLedger` | 38 | **unlisted** |
| `Core.Strategy.Official.Strategies.SupportLocalization` | 31 | **unlisted** |
| `Core.Strategy.Official.Strategies.UniversalTargetResponseObstructions` | 31 | **unlisted** |
| `Core.Strategy.Official.Syntax` | 70 | **unlisted** |
| `Core.Strategy.OfficialRegistry` | 421 | quarantined |
| `Core.Strategy.RegistrationAudit` | 222 | quarantined |
| `Core.Strategy.Validate` | 3298 | quarantined |
| `Graph.External` | 48 | **unlisted** |
| `Graph.Strategy` | 314 | quarantined |
| `Graph.Strategy.Official` | 23 | quarantined |
| `Graph.Strategy.Official.Compiler` | 32 | quarantined |
| `Graph.Strategy.Official.Features.CanonicalConnectedSupportHull` | 198 | **unlisted** |
| `Graph.Strategy.Official.Features.CanonicalDegreeThreePortResponse` | 908 | **unlisted** |
| `Graph.Strategy.Official.Features.CanonicalExcessPortActivation` | 100 | **unlisted** |
| `Graph.Strategy.Official.Features.CanonicalExcessPortCapacity` | 127 | **unlisted** |
| `Graph.Strategy.Official.Features.CanonicalSupportDecomposition` | 298 | **unlisted** |
| `Graph.Strategy.Official.Features.DeletionFanIncidence` | 238 | quarantined |
| `Graph.Strategy.Official.Features.ExactFiniteLabelling` | 69 | **unlisted** |
| `Graph.Strategy.Official.Features.HighCenterFanClosure` | 287 | **unlisted** |
| `Graph.Strategy.Official.Features.MinimalCounterexampleConsequences` | 399 | **unlisted** |
| `Graph.Strategy.Official.Features.PackedSupport` | 68 | **unlisted** |
| `Graph.Strategy.Official.Features.PackedSupportIncidence` | 156 | **unlisted** |
| `Graph.Strategy.Official.Features.PackedWindowAttachmentSemantics` | 133 | **unlisted** |
| `Graph.Strategy.Official.Features.PackedWindowTokenLedger` | 322 | **unlisted** |
| `Graph.Strategy.Official.Features.SupportIncidenceLedger` | 142 | quarantined |
| `Graph.Strategy.Official.Kernel` | 82 | quarantined |
| `Graph.Strategy.Official.Presentation` | 45 | quarantined |
| `Graph.Strategy.Official.Registry` | 72 | **unlisted** |
| `Graph.Strategy.Official.SealedDag` | 124 | quarantined |
| `Graph.Strategy.Official.Semantics.Terminal` | 139 | **unlisted** |
| `Graph.Strategy.Official.Target` | 98 | **unlisted** |
| `Graph.Theorems` | 35 | **unlisted** |
| `Routes.Accumulated` | 83 | quarantined |

### 1d. `*Focus` and `*Semantics` shells (22 modules, 3,300 lines)

A `Focus` is the legacy query lens; a `*Semantics` file is the registration
adapter of a strategy module. Neither shape exists in the canonical API.

| module | lines | listed? |
|---|---|---|
| `Core.Finite.PartitionFocus` | 117 | **unlisted** |
| `Core.MinimalityFocus` | 146 | quarantined |
| `Core.RoutingFocus` | 92 | quarantined |
| `Core.Strategy.AtomContextObstructionDichotomySemantics` | 84 | quarantined |
| `Core.Strategy.BaselineDemandAccountingSemantics` | 36 | **unlisted** |
| `Core.Strategy.CanonicalCapacityTokenAccountingSemantics` | 56 | **unlisted** |
| `Core.Strategy.CanonicalPairResponseAccountingSemantics` | 115 | **unlisted** |
| `Core.Strategy.ColdBranchAggregationSemantics` | 106 | quarantined |
| `Core.Strategy.CoupledHomogeneousFibrePressureSemantics` | 65 | quarantined |
| `Core.Strategy.FiniteBottleneckClassificationSemantics` | 63 | **unlisted** |
| `Core.Strategy.FiniteScheduleCapacitySemantics` | 57 | **unlisted** |
| `Core.Strategy.FiniteStateCapacitySemantics` | 226 | quarantined |
| `Core.Strategy.FiniteStateNetChargeContinuationSemantics` | 71 | quarantined |
| `Core.Strategy.HomogeneousBottleneckSemantics` | 268 | **unlisted** |
| `Core.Strategy.LocalSupplyLowerBoundSemantics` | 499 | quarantined |
| `Core.Strategy.OrderedSurplusActivationSemantics` | 29 | **unlisted** |
| `Core.Strategy.Route8CarrierClosureSemantics` | 139 | quarantined |
| `Core.Strategy.TargetRelativeRankDichotomySemantics` | 202 | **unlisted** |
| `Graph.BoundariedAtomFocus` | 339 | **unlisted** |
| `Graph.MinimalityFocus` | 172 | **unlisted** |
| `Graph.ProgressFocus` | 226 | **unlisted** |
| `Graph.RootedReturnFocus` | 192 | **unlisted** |

---

## Tier 2 -- delete now, the row is ported (44 modules, 22,398 lines)

Mathematics whose audit rows all fall in the ported set (1-11, 20-25, 29,
37-73), paired with the live module that replaced it.

| legacy module | lines | ported row(s) | live replacement |
|---|---|---|---|
| `Core.Finite.ColdCorridor` | 2203 | 43-61 | `Graph/ColdCorridor.lean` |
| `Graph.InducedPathCold` | 3965 | 43-61 | `Graph/ColdCorridor.lean`, `Graph/ColdFirstFailure.lean` |
| `Core.Strategy.ColdBranchAggregation` | 1297 | 55-61 | `Graph/ColdBranchClosure.lean` |
| `Graph.Strategy.ColdBranchAggregation` | 703 | 55-61 | `Graph/Strategy/ColdCorridorRun.lean` |
| `Graph.Strategy.ColdBranchPreludeAggregation` | 790 | 57-61 | `Graph/Strategy/ColdCorridorRun.lean` |
| `Graph.Strategy.ColdBranchFailureRouting` | 579 | 50-51 | `Graph/Strategy/ColdCorridorRows.lean` |
| `Graph.Strategy.ColdBranchGermClosure` | 458 | 52-54, 59 | `Graph/ColdBranchClosure.lean` |
| `Graph.Strategy.ColdBranchF2Closure` | 150 | 46 | `Graph/ColdFirstFailure.lean` |
| `Core.Response.SameInterface` | 320 | 44 | `Graph/ColdCorridor.lean` (`TableRow`) |
| `Core.Strategy.Route8CarrierClosure` | 508 | 62-67 | `Graph/Route8Carrier.lean`, `Route8Closure.lean` |
| `Graph.Strategy.TypeARoute8Closure` | 579 | 62-67 | `Graph/Route8Closure.lean` |
| `Graph.Strategy.TypeARoute8Stages` | 79 | 62-67 | `Graph/Strategy/Route8Run.lean` |
| `Graph.TypeARoute8Carriers` | 84 | 62-67 | `Graph/Route8Carrier.lean` |
| `Graph.Strategy.NormalizationRank` | 2134 | 37-40 | `Graph/BoundaryDemand.lean`, `WedgeLowerBound.lean`, `CurvatureTargetRank.lean` |
| `Core.Strategy.LocalSupplyLowerBound` | 1077 | 39 | `Graph/WedgeLowerBound.lean` |
| `Core.Strategy.TargetRelativeRankDichotomy` | 1114 | 40 | `Graph/CurvatureTargetRank.lean` |
| `Core.Strategy.FiniteStateCapacity` | 1185 | 41 | `Graph/RemainderEntropy.lean`, `WindowRemainder.lean` |
| `Core.Strategy.FiniteStateCapacityTheorems` | 108 | 41 | idem |
| `Graph.Strategy.FiniteStateCapacity` | 595 | 41 | idem |
| `Core.EntropyPackingBudget` | 132 | 41 | `Graph/RemainderEntropy.lean` |
| `Core.Strategy.FiniteStateNetChargeContinuation` | 660 | 42 | `Graph/NetCharge.lean` |
| `Graph.NegativeSupport` | 170 | 42 | `Graph/NetCharge.lean` |
| `Core.OrderThresholdSplit` | 228 | 41 | `Spine.orderThresholdDichotomy` |
| `Graph.WindowAttachmentLabel` | 440 | 10, 37 | `Graph/WindowAttachmentRealization.lean` |
| `Graph.Replacement` | 919 | 5 | `Graph/Strategy/InterfaceReplacement.lean` |
| `Graph.MinimalCounterexampleConnected` | 149 | 1-4 | `Graph/Minimality.lean`, `Graph/Progress.lean` |
| `Graph.Contraction` | 94 | 5 | `Graph/Deletion.lean` |

The rest of Tier 2 is legacy support machinery for those same ported rows, with
no consumer left in either the live tree or an open row:

| module | lines | listed? |
|---|---|---|
| `Core.Assembly.Amalgamation` | 98 | **unlisted** |
| `Core.Assembly.LocalToGlobal` | 108 | quarantined |
| `Core.Degradation` | 38 | quarantined |
| `Core.Finite.CertifiedTableBoundsFixture` | 58 | **unlisted** |
| `Core.Metadata` | 92 | quarantined |
| `Core.Strategy.AtomContextObstructionDichotomy` | 178 | quarantined |
| `Core.Strategy.BinaryDecisionDichotomy` | 87 | quarantined |
| `Core.Strategy.EntropyCap` | 92 | **unlisted** |
| `Core.Strategy.ExhaustiveClosure` | 83 | **unlisted** |
| `Core.Strategy.LocalizedCompressionClosure` | 152 | quarantined |
| `Core.Strategy.RankCapacityExhaustion` | 110 | **unlisted** |
| `Core.Strategy.RankForcing` | 58 | quarantined |
| `Core.Strategy.WellFoundedCompression` | 80 | quarantined |
| `Core.Strategy.WellFoundedExhaustion` | 123 | quarantined |
| `Core.SupportSplit` | 123 | quarantined |
| `Graph.Budget` | 93 | quarantined |
| `Graph.Strategy.AtomContextObstructionDichotomy` | 105 | quarantined |

---

## Tier 3 -- keep, porting reference for the 18 open rows (50 modules, 36,287 lines)

Open rows are 12-19 (Type A saturated-exit ladder), 26-28 (Type B bridge) and
30-36 (non-near-cubic surplus branch). "(cited)" means the row's evidence
section names the module or one of its declarations directly.

| module | lines | for rows |
|---|---|---|
| `Graph.TypeAReceiverClosure` | 746 | 12-19 |
| `Graph.Strategy.TypeAReceiverExhaustion` | 503 | 12-19 |
| `Graph.Strategy.TypeAReceiverStages` | 270 | 12-19 |
| `Graph.ReceiverExhaustion` | 50 | 12 (cited by name) |
| `Graph.AtomResponse` | 432 | 12-19 |
| `Graph.TargetDefectivePeel` | 152 | 16 |
| `Graph.TypeABCertificate` | 520 | 18-19 (cited) |
| `Graph.TypeBHybridLedger` | 965 | 26 (cited) |
| `Graph.TypeBProfileSchedule` | 778 | 26 (cited) |
| `Graph.TypeBFanClosedPorts` | 552 | 26 (cited) |
| `Graph.TypeBOpenPorts` | 639 | 26 |
| `Graph.TypeBPostLedgerCore` | 1082 | 26 |
| `Graph.TypeBFanMass` | 1047 | 27 (cited) |
| `Graph.DecoratedFan` | 118 | 27 (cited) |
| `Graph.TypeBBridgeResidual` | 1409 | 28 |
| `Graph.TypeBExclusion` | 966 | 26, 28 |
| `Graph.Strategy.TypeBFanClosure` | 360 | 26-28 |
| `Graph.TypeBMarkedFan` | 755 | 15, 26 |
| `Graph.TypeBClosure` | 1364 | 15 (cited) |
| `Graph.TypeBOverlapObstruction` | 1644 | 26 |
| `Graph.TypeBDegreeFour` | 867 | 26-28 |
| `Graph.Strategy.SurplusAccounting` | 1408 | 30-36 (cited) |
| `Graph.NearCubicSpine` | 494 | 36 |
| `Graph.TightVertexSuppression` | 767 | 32 |
| `Graph.SimultaneousTightVertexSuppression` | 1390 | 32 |
| `Graph.SupportCharge` + `Graph.AssignedSupportCharge` | 103 | 30-33 |
| `Graph.Strategy.Official.Features.DegreeSurplusLedger` | 119 | 36 |
| `Core.Strategy.OrderedSurplusActivation` | 99 | 30 (cited) |
| `Core.Strategy.BaselineDemandAccounting` | 83 | 27, 31 (cited) |
| `Core.Strategy.CanonicalPairResponseAccounting` | 194 | 32 |
| `Core.Strategy.CanonicalCapacityTokenAccounting` | 327 | 33 |
| `Core.Strategy.CoupledHomogeneousFibrePressure` | 625 | 34 |
| `Core.Strategy.FiniteBottleneckClassification` | 577 | 35 |
| `Core.Strategy.HomogeneousBottleneck` | 1366 | 36 |
| `Core.Strategy.FiniteScheduleCapacity` | 287 | 30-36 |
| `Core.Finite.Accounting` | 182 | 30-36 |
| `Core.Strategy.Dag` | 9798 | 26, 28 (`ScanData`, `liftScan`) |

Deferred rather than cleared -- legacy generic utilities whose declarations are
named in open-row evidence. Cheap to keep; decide them when the row lands.

| module | lines | listed? |
|---|---|---|
| `Core.Budget.Dynamic` | 146 | quarantined |
| `Core.Budget.Transcript` | 167 | quarantined |
| `Core.Compactness.Extraction` | 159 | quarantined |
| `Core.Finite.Flatten` | 171 | quarantined |
| `Core.Finite.ScaleRoute` | 373 | quarantined |
| `Core.Finite.ScheduleEventRoute` | 129 | quarantined |
| `Core.Finite.ScheduleEvents` | 343 | quarantined |
| `Core.Finite.Search` | 309 | quarantined |
| `Core.Finite.SelectedSchedule` | 182 | quarantined |
| `Core.NormalForm.ClassClosure` | 768 | quarantined |
| `Core.NormalForm.EqualityRigidity` | 149 | quarantined |
| `Core.NormalForm.SignGap` | 353 | quarantined |

---

## Out of scope, for completeness

- `Hypostructure/Fixtures/`: 136 dead modules, 100 of them unquarantined --
  fixtures for the retired stack. Most pair 1:1 with a Tier 1 module and belong
  in the same commit.
- `Hypostructure/PDE/`: 157 dead modules, 145 unquarantined. Untouched here by
  request.

## Suggested order

One commit per tier, each verified with `make test`:

1. Tier 1a (CT layer) -- largest, most mechanical, zero row risk.
2. Tier 1b-1d (ledger stack, registry, shells) plus their `Fixtures/` counterparts.
3. Tier 2, cold-corridor / route-8 / rank blocks first.

After each, drop the deleted names from `quarantine.txt`. The gate only checks
`live n quarantined`, so a stale entry is not an error -- but the count it
prints is the inventory people read.
