# Contract-lemma migration: family map

Serial preparation for the parallel contract-lemma migration.  Every key of
`Graph.Strategy.Spine.Key` belongs to exactly one family; every file below has
exactly one owning family.  A family edits only the files it owns, plus its own
lines in the shared files listed at the end.  Current maximum key index: `608`
(314 keys).

## Library statement modules

All statement definitions that `SpineVocabulary.lean` used to hold now live in
`hypostructure/Hypostructure/Graph/Statements/`.  None of these modules imports
`SpineVocabulary` or any `Graph/Strategy` module, directly or transitively.  They
keep the namespace `Hypostructure.Graph.Strategy.Spine`, so every existing fully
qualified name is unchanged.  Each statement takes the registered constants as an
explicit `Parameters` argument (`Graph/Statements/Parameters.lean`); the
vocabulary record is `structure Data extends Parameters`, and each `Holds` branch
instantiates its statement at `data.toParameters` and the object.

| Module | Owner | Imports (statement modules) |
|---|---|---|
| `hypostructure/Hypostructure/Graph/Statements/Parameters.lean` | F5 | - |
| `hypostructure/Hypostructure/Graph/Statements/Spine.lean` | F5 | Parameters |
| `hypostructure/Hypostructure/Graph/Statements/TypeA.lean` | F1 | Spine |
| `hypostructure/Hypostructure/Graph/Statements/TypeB.lean` | F2 | TypeA |
| `hypostructure/Hypostructure/Graph/Statements/RouteEight.lean` | F3 | TypeA |
| `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` | F4 | TypeB |

A family that needs a new statement from a module above its own in this chain
adds it to the lowest module that every consumer imports and records the edit
with that module's owner.  `SurplusPair` sees `TypeB`, `TypeA` and `Spine`;
`RouteEight` and `TypeB` see `TypeA` and `Spine`, not each other.

## Reserved key indices

| Family | New-key `idx` range |
|---|---|
| F1 Type A | 1000-1199 |
| F2 Type B | 1200-1399 |
| F3 Route 8 | 1400-1599 |
| F4 Surplus / Homogeneous / Pair | 1600-1799 |
| F5 Spine / Cold / NearCubic | 1800-1999 |

A new key takes the next unused index of its family's range; existing indices
(0-608) are never renumbered.

## F1: Type A

- Library statement module: `hypostructure/Hypostructure/Graph/Statements/TypeA.lean`
- Reserved new-key range: 1000-1199

### Keys (37)

| idx | Key | Statement | Statement module |
|---|---|---|---|
| 51 | `typeALowSurplus` | `TypeALowSurplusStatement` | TypeA |
| 52 | `typeBHighSurplus` | `TypeBHighSurplusStatement` | TypeA |
| 53 | `typeAReceiverRouting` | `TypeAReceiverRoutingStatement` | TypeA |
| 54 | `typeASaturatedReceiver` | `TypeASaturatedReceiverStatement` | TypeA |
| 55 | `typeAUnsaturatedReceivers` | `TypeAUnsaturatedReceiversStatement` | TypeA |
| 56 | `typeAVisibleEntry` | `TypeAVisibleEntryStatement` | TypeA |
| 57 | `typeAVisibleFirstExcess` | `TypeAVisibleFirstExcessStatement` | TypeA |
| 58 | `typeAExitOneReturn` | `TypeAExitOneReturnStatement` | TypeA |
| 59 | `typeAExitOneFree` | `TypeAExitOneFreeStatement` | TypeA |
| 60 | `typeAExitTwoTheta` | `TypeAExitTwoThetaStatement` | TypeA |
| 61 | `typeAExitTwoFree` | `TypeAExitTwoFreeStatement` | TypeA |
| 62 | `typeAExitThreeCollision` | `TypeAExitThreeCollisionStatement` | TypeA |
| 63 | `typeAExitThreeFree` | `TypeAExitThreeFreeStatement` | TypeA |
| 96 | `typeAExitFive` | `TypeAExitFiveStatement` | TypeA |
| 97 | `typeAExitFiveFree` | `TypeAExitFiveFreeStatement` | TypeA |
| 98 | `typeAExitSix` | `TypeAExitSixStatement` | TypeA |
| 99 | `typeAExitSixFree` | `TypeAExitSixFreeStatement` | TypeA |
| 100 | `typeAExitSixProper` | `TypeAExitSixProperStatement` | TypeA |
| 101 | `typeAExitSixGlobal` | `TypeAExitSixGlobalStatement` | TypeA |
| 121 | `typeAPortReturn` | `TypeAPortReturnStatement` | TypeA |
| 123 | `typeASaturatedExitEntry` | `TypeASaturatedExitEntryStatement` | TypeA |
| 124 | `typeAExitSevenHandoff` | `TypeAExitSevenHandoffStatement` | TypeA |
| 125 | `typeAExitSevenFree` | `TypeAExitSevenFreeStatement` | TypeA |
| 148 | `typeAUnsaturatedDischarge` | `TypeAUnsaturatedDischargeStatement` | TypeA |
| 151 | `typeAExitFourPeeled` | `TypeAExitFourPeeledStatement` | TypeA |
| 152 | `typeAExitFourReceiverDischarged` | `TypeAExitFourReceiverDischargedStatement` | TypeA |
| 153 | `typeAExitFourFiniteDescent` | `TypeAExitFourFiniteDescentFact` | TypeA |
| 156 | `typeASaturatedHandoffExitFour` | `TypeASaturatedHandoffExitFourStatement` | TypeA |
| 157 | `typeASaturatedHandoffExitFourFree` | `TypeASaturatedHandoffExitFourFreeStatement` | TypeA |
| 158 | `typeAExitSevenProduced` | `TypeAExitSevenProducedStatement` | TypeA |
| 328 | `typeABoundedSupport` | `TypeABoundedSupportStatement` | TypeA |
| 343 | `typeAExclusion` | `TypeAExclusionStatement` | TypeA |
| 508 | `typeASilentExitFourFree` | `SelectedSilentExitFourFree` | TypeA |
| 509 | `typeASilentExitFiveFree` | `SelectedSilentExitFiveFree` | TypeA |
| 510 | `typeASilentExitSixFree` | `SelectedSilentExitSixFree` | TypeA |
| 511 | `typeASilentExitSevenFree` | `SelectedSilentExitSevenFree` | TypeA |

### Row and decision modules (29)

- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeABoundedSupport.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExclusion.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitFiveDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourFiniteDescent.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourPeelingStep.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourRetestDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitOneDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitSevenDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitSevenHandoff.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitSixDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitSixScopeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitThreeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAExitTwoDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAPortReturn.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAReceiverRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASaturationDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitEntry.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitFiveDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitFourTerminalDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitSevenDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitSevenRoute8.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitSixDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAUnsaturatedDischarge.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAVisibleEntryDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeAVisibleExitEntry.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeSplitDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/TypeAExitRun.lean`

### EG assembly files (10)

- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/DecoratedHandoff.lean` (EG-NODE [65])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/ExitFiveToSeven.lean` (EG-NODE [103], [104], [105], [106], [107], [108], [66])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/ExitFiveToSevenSilent.lean` (EG-NODE [103], [104], [105], [106], [107], [108], [109])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/ExitFourChain.lean` (EG-NODE [101], [102])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/ExitFourChainSilent.lean` (EG-NODE [101], [102])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/ExitFourDischargedRetest.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/LowSurplusContinuation.lean` (EG-NODE [88], [89], [90], [91], [92], [93], [94], [86], [87])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/SilentExitChain.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/VisibleExitChain.lean` (EG-NODE [95], [96], [97], [98], [99], [100])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeA/VisibleExitFour.lean`

## F2: Type B

- Library statement module: `hypostructure/Hypostructure/Graph/Statements/TypeB.lean`
- Reserved new-key range: 1200-1399

### Keys (44)

| idx | Key | Statement | Statement module |
|---|---|---|---|
| 72 | `highCentreNormalForm` | `HighCentreNormalFormStatement` | TypeB |
| 76 | `fanCertificateCap` | `TypeBFanCertificateCapStatement` | TypeB |
| 77 | `fanCertificateMarked` | `TypeBFanCertificateMarkedStatement` | TypeB |
| 78 | `fanCertificateResidual` | `TypeBFanCertificateResidualStatement` | TypeB |
| 80 | `typeBHybridEntry` | `TypeBFanHybridEntryStatement` | TypeB |
| 81 | `typeBDirectCycle` | `TypeBFanDirectCycleStatement` | TypeB |
| 82 | `typeBDirectCycleFree` | `TypeBFanDirectCycleFreeStatement` | TypeB |
| 84 | `typeBOverlapObstruction` | `TypeBB2ObstructionStatement` | TypeB |
| 85 | `typeBBridgeMass` | `TypeBBridgeMassStatement` | TypeB |
| 149 | `typeBB2Choice` | `TypeBB2ChoiceStatement` | TypeB |
| 150 | `typeBDisjointLedger` | `TypeBDisjointLedgerStatement` | TypeB |
| 166 | `typeBExcluded` | `TypeBExcludedStatement` | TypeB |
| 167 | `typeBExclusionResidual` | `TypeBExclusionResidualStatement` | TypeB |
| 186 | `fanCertificateResidualMass` | `TypeBFanCertificateResidualMassStatement` | TypeB |
| 187 | `typeBOverlapObstructionMass` | `TypeBOverlapObstructionMassStatement` | TypeB |
| 188 | `typeBExclusionResidualMass` | `TypeBExclusionResidualMassStatement` | TypeB |
| 189 | `typeBBridgeSublinear` | `TypeBBridgeSublinearStatement` | TypeB |
| 220 | `typeBDecoratedAssignedSupport` | `TypeBDecoratedAssignedSupportStatement` | TypeB |
| 250 | `typeBAssignedSupport` | `TypeBAssignedSupportStatement` | TypeB |
| 251 | `typeBFanHeavyCentre` | `TypeBFanHeavyCentreStatement` | TypeB |
| 252 | `typeBFanDegreeFourCentres` | `TypeBFanDegreeFourCentresStatement` | TypeB |
| 253 | `typeBFanLocalDichotomy` | `TypeBFanLocalDichotomyStatement` | TypeB |
| 254 | `typeBFanDegreeFourProfile` | `TypeBFanDegreeFourProfileStatement` | TypeB |
| 270 | `typeBFanEntry` | `TypeBFanEntryStatement` | TypeB |
| 344 | `typeBBridgeReduction` | `TypeBBridgeReductionStatement` | TypeB |
| 345 | `typeBSublinearLedger` | `TypeBSublinearHypotheses` | TypeB |
| 346 | `typeBSublinearResidual` | `TypeBSublinearResidualStatement` | TypeB |
| 354 | `sameCenterOpenPortCompatibility` | `SameCenterOpenPortCompatibilityStatement` | TypeB |
| 355 | `triangularFanCore` | `TriangularFanCoreStatement` | TypeB |
| 426 | `triangularShoulderCompletion` | `TriangularShoulderCompletionStatement` | TypeB |
| 427 | `triangularPortReturn` | `TriangularPortReturnStatement` | TypeB |
| 433 | `triangularFirstLanding` | `TriangularFirstLandingStatement` | TypeB |
| 434 | `triangularCrossShoulder` | `TriangularCrossShoulderStatement` | TypeB |
| 435 | `openPortSuppression` | `OpenPortSuppressionStatement` | TypeB |
| 436 | `openPortSuppressionSafe` | `OpenPortSuppressionSafeStatement` | TypeB |
| 437 | `singleOpenPortSuppressionWitness` | `SingleOpenPortSuppressionWitnessStatement` | TypeB |
| 438 | `suppressedFamilyCriticalCycle` | `SuppressedFamilyCriticalCycleStatement` | TypeB |
| 441 | `typeBFanSafe` | `TypeBFanSafeStatement` | TypeB |
| 442 | `fanClosedPort` | `FanClosedPortStatement` | TypeB |
| 443 | `compatiblePairFanClosure` | `CompatiblePairFanClosureStatement` | TypeB |
| 444 | `fanClosedPortTypeBRouting` | `FanClosedPortTypeBRoutingStatement` | TypeB |
| 445 | `compatiblePairTypeBRouting` | `CompatiblePairTypeBRoutingStatement` | TypeB |
| 446 | `triangularPortTypeBRouting` | `TriangularPortTypeBRoutingStatement` | TypeB |
| 447 | `typeBGlobalLocalBridge` | `TypeBGlobalLocalBridgeStatement` | TypeB |

### Row and decision modules (40)

- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/AbsorbedGermFanEnvelope.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/SameTokenTypeBFanEntry.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/B2AssignmentDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/BridgeFanMass.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/CompatiblePairFanClosure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/CompatiblePairTypeBRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DirectCycleDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DisjointPostLedgerComponents.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/FanCertificateCap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/FanCertificateDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/FanCertificateResidualMass.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/FanClosedPort.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/FanClosedPortTypeBRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/HighCentreNormalForm.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/HybridEntry.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/OpenPortSuppression.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/OpenPortSuppressionSafe.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/SameCenterOpenPortCompatibility.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/SingleOpenPortSuppressionWitness.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/SuppressedFamilyCriticalCycle.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TriangularCrossShoulder.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TriangularFanCore.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TriangularFirstLanding.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TriangularPortReturn.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TriangularPortTypeBRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TriangularShoulderCompletion.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBAssignedSupport.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBBridgeReduction.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBBridgeSublinear.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBDecoratedAssignedSupport.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBExclusionDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBExclusionResidualMass.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBFanDegreeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBFanDegreeFourProfile.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBFanLocalDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBFanSafe.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBGlobalLocalBridge.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBOverlapObstructionMass.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TypeBSublinearDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/TypeBClosure.lean`

### EG assembly files (8)

- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Absorbed/FanCharge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/Certificate.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/ChargedRoute.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/Continuation.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/DecoratedContinuation.lean` (EG-NODE [67], [68], [69], [70], [78], [79])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/HighSurplusContinuation.lean` (EG-NODE [65], [67], [68], [69], [70], [71], [75], [78], [79], [80], [84])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/Internal/Certificate.lean` (EG-NODE [71], [75], [80], [84])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/TypeB/NearCubicCertificate.lean`

## F3: Route 8

- Library statement module: `hypostructure/Hypostructure/Graph/Statements/RouteEight.lean`
- Reserved new-key range: 1400-1599

### Keys (48)

| idx | Key | Statement | Statement module |
|---|---|---|---|
| 159 | `route8ResidualProfile` | `SilentCoreResidualProfile` | RouteEight |
| 160 | `route8GlobalSqueeze` | `Route8GlobalSqueeze` | RouteEight |
| 161 | `route8BasinBurden` | `Route8BasinBurden` | RouteEight |
| 162 | `route8LargeBudgetDeficit` | `Route8LargeBudgetDeficit` | RouteEight |
| 163 | `route8CarrierCore` | `Route8CarrierCore` | RouteEight |
| 168 | `route8SmallCoreCollapse` | `Route8SmallCoreCollapse` | RouteEight |
| 170 | `route8CarrierDeletionWitnesses` | `Route8CarrierDeletionWitnesses` | RouteEight |
| 171 | `route8PrivateCarrierBudget` | `Route8PrivateCarrierBudget` | RouteEight |
| 172 | `route8NoTwoCarrierContradiction` | `Route8NoTwoCarrierContradiction` | RouteEight |
| 174 | `route8TerminalNoGo` | `Route8TerminalNoGo` | RouteEight |
| 260 | `route8Census` | `Route8CensusStatement` | RouteEight |
| 261 | `route8TwoCarrierEntry` | `Route8TwoCarrierEntryStatement` | RouteEight |
| 262 | `route8NoTwoCarrierEntry` | `Route8NoTwoCarrierEntryStatement` | RouteEight |
| 263 | `route8Deficit` | `Route8DeficitStatement` | RouteEight |
| 264 | `route8Rate` | `Route8RateStatement` | RouteEight |
| 265 | `route8RateFails` | `Route8RateFailsStatement` | RouteEight |
| 266 | `route8PiecesClassified` | `Route8PiecesClassifiedStatement` | RouteEight |
| 280 | `route8TrueTwoCarrierEntry` | `Route8TrueTwoCarrierEntryStatement` | RouteEight |
| 282 | `route8PeelingDescent` | `Route8PeelingDescentStatement` | RouteEight |
| 329 | `route8LargeBudgetDeficitFails` | `Route8LargeBudgetDeficitFailsStatement` | RouteEight |
| 330 | `route8SmallCoreEntry` | `Route8SmallCoreEntry` | RouteEight |
| 331 | `route8NoSmallCoreEntry` | `Route8NoSmallCoreEntry` | RouteEight |
| 332 | `route8TrueResidual` | `Route8TrueResidual` | RouteEight |
| 333 | `route8CarrierCutParity` | `Route8CarrierCutParity` | RouteEight |
| 334 | `route8UnifiedTrueTwoCarrierEntry` | `Route8UnifiedTrueTwoCarrierEntryStatement` | RouteEight |
| 336 | `route8UnifiedNegative` | `Route8UnifiedNegative` | RouteEight |
| 338 | `route8VisibleExitFourRouting` | `Route8VisibleExitFourRoutingStatement` | RouteEight |
| 339 | `route8UnifiedDeficit` | `Route8UnifiedDeficitFact` | RouteEight |
| 340 | `route8UnifiedEntryCensus` | `Route8UnifiedEntryCensusFact` | RouteEight |
| 342 | `route8StageRateFailed` | `Route8StageRateFailedFact` | RouteEight |
| 347 | `route8QuotientFree` | `Route8QuotientFreeStatement` | RouteEight |
| 348 | `route8QuotientResidual` | `Route8QuotientResidualStatement` | RouteEight |
| 349 | `route8DemandLedger` | `Route8DemandLedgerStatement` | RouteEight |
| 350 | `route8ExtractedEntryCensus` | `Route8ExtractedEntryCensusFact` | RouteEight |
| 351 | `route8DemandAbsorption` | `Route8DemandAbsorptionStatement` | RouteEight |
| 352 | `route8WindowBlockers` | `Route8WindowBlockersStatement` | RouteEight |
| 353 | `route8PeeledDemandResidual` | `Route8PeeledDemandResidualStatement` | RouteEight |
| 503 | `route8UnpaidExitFourResidual` | `Route8UnpaidExitFourResidualStatement` | RouteEight |
| 504 | `route8UnifiedVisibleResidual` | `Route8UnifiedVisibleResidualStatement` | RouteEight |
| 505 | `route8UnifiedVisibleOverload` | `Route8UnifiedVisibleOverloadStatement` | RouteEight |
| 506 | `route8JointBalance` | `Route8JointBalanceStatement` | RouteEight |
| 512 | `route8UnifiedVisibleHistory` | `Route8UnifiedVisibleHistoryStatement` | RouteEight |
| 513 | `windowShadowSingletonTail` | `WindowShadowSingletonTailStatement` | RouteEight |
| 514 | `windowShadowHitCycle` | `WindowShadowHitCycleStatement` | RouteEight |
| 515 | `windowShadowHitExcluded` | `WindowShadowHitExcludedStatement` | RouteEight |
| 516 | `windowShadowSignature` | `WindowShadowSignatureStatement` | RouteEight |
| 517 | `route8OpenBoundarySaturated` | `Route8OpenBoundarySaturatedStatement` | RouteEight |
| 518 | `route8DemandUnitCount` | `Route8DemandUnitCountStatement` | RouteEight |

### Row and decision modules (41)

- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8BasinBurden.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8CarrierCore.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8CarrierCutParity.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8CarrierDeletionWitnesses.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8CarrierDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8Census.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8DemandAbsorption.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8DemandLedgerDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8ExtractedEntryCensus.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8GlobalSqueeze.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8JointBalance.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8LargeBudgetDeficit.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8NoTwoCarrierContradiction.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8OpenBoundarySaturated.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8PeeledDemandResidual.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8PeelingDescent.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8PiecesClassified.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8PrivateCarrierBudget.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8QuotientDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8RateDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8RateFromColdBelow.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8ResidualProfile.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8SmallCoreCollapse.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8SmallCoreExit.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8StageOutcomeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8TerminalNoGo.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8TrueResidual.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8TrueTwoCarrierEntry.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedDeficit.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedEntryCensus.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedNegative.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedTerminalNoGo.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedVisibleOverload.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedVisibleResidual.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8UnpaidExitFourDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8VisibleRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Route8WindowBlockers.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/WindowShadowHitCycle.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/WindowShadowHitExcluded.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/WindowShadowSignature.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/WindowShadowSingletonTail.lean`

### EG assembly files (4)

- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/RouteEight/Local.lean` (EG-NODE [123], [181], [183], [184], [185], [186])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/RouteEight/RateFailure.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/RouteEight/Residual.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/RouteEight/TypeBContinuation.lean`

## F4: Surplus / Homogeneous / Pair

- Library statement module: `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean`
- Reserved new-key range: 1600-1799

### Keys (53)

| idx | Key | Statement | Statement module |
|---|---|---|---|
| 109 | `sparseSlackSurplus` | `SparseSlackSurplusStatement` | SurplusPair |
| 110 | `activeSurplusFamily` | `ActiveSurplusFamilyStatement` | SurplusPair |
| 111 | `sparsePortActivation` | `SparsePortActivationStatement` | SurplusPair |
| 112 | `baselineSpineDemand` | `BaselineSpineDemandStatement` | SurplusPair |
| 113 | `canonicalPairLedger` | `CanonicalPairLedgerStatement` | SurplusPair |
| 114 | `capacityTokenLedger` | `CapacityTokenLedgerStatement` | SurplusPair |
| 115 | `roleFibrePartition` | `RoleFibrePartitionSchema` | SurplusPair |
| 116 | `fibrePressure` | `FibrePressureSchema` | SurplusPair |
| 118 | `homogeneousBottleneck` | `HomogeneousBottleneckStatement` | SurplusPair |
| 119 | `sparseSurplusSurvivor` | `SparseSurplusSurvivorStatement` | SurplusPair |
| 120 | `activeSurplusDemands` | `ActiveSurplusDemandsStatement` | SurplusPair |
| 126 | `spineSurplusEstimate` | `SpineSurplusEstimateStatement` | SurplusPair |
| 127 | `sparsePressureNearCubic` | `SparsePressureNearCubicStatement` | SurplusPair |
| 128 | `sparsePressureOverload` | `SparsePressureOverloadSchema` | SurplusPair |
| 129 | `sparseUpperEnvelope` | `SparseUpperEnvelopeStatement` | SurplusPair |
| 130 | `windowClassOverload` | `WindowClassOverloadStatement` | SurplusPair |
| 131 | `windowClassAbsent` | `WindowClassAbsentStatement` | SurplusPair |
| 132 | `remainderClassOverload` | `RemainderClassOverloadStatement` | SurplusPair |
| 133 | `remainderClassAbsent` | `RemainderClassAbsentStatement` | SurplusPair |
| 137 | `quantitativeOverload` | `Graph.QuantitativeOverloadStatement` | library predicate |
| 140 | `homogeneousCapsHold` | `HomogeneousCapsHoldStatement` | SurplusPair |
| 141 | `homogeneousBottleneckPattern` | `HomogeneousBottleneckPatternSchema` | SurplusPair |
| 142 | `bottleneckRouting` | `BottleneckRoutingStatement` | SurplusPair |
| 143 | `sparsePairExit` | `SparsePairExitStatement` | SurplusPair |
| 144 | `canonicalBlockerRoute` | `CanonicalBlockerRouteStatement` | SurplusPair |
| 184 | `typeBHandoff` | `SameTokenTypeBHandoffStatement` | SurplusPair |
| 201 | `dependentPairFamily` | `DependentPairFamilyStatement` | SurplusPair |
| 202 | `independentPairFamily` | `IndependentPairFamilyStatement` | SurplusPair |
| 203 | `mixedSparseSpineDependence` | `MixedSparseSpineDependenceStatement` | SurplusPair |
| 204 | `exactCubicBaselineBudget` | `ExactCubicBaselineBudgetStatement` | SurplusPair |
| 205 | `incrementalSkeletonRoom` | `IncrementalSkeletonRoomStatement` | SurplusPair |
| 206 | `skeletonDominates` | `SkeletonDominatesStatement` | SurplusPair |
| 240 | `freePairEntropySandwich` | `FreePairEntropySandwichStatement` | SurplusPair |
| 241 | `freePairCodeUnrealized` | `FreePairCodeUnrealizedStatement` | SurplusPair |
| 242 | `blockedPairEntropySandwich` | `BlockedPairEntropySandwichStatement` | SurplusPair |
| 243 | `blockedPairCodeUnrealized` | `BlockedPairCodeUnrealizedStatement` | SurplusPair |
| 356 | `blockedPairEntropySetup` | `BlockedPairEntropySetupStatement` | SurplusPair |
| 357 | `pairOverlapFirstFailure` | `PairOverlapFirstFailureStatement` | SurplusPair |
| 400 | `sparseTargetDefectResidual` | `SparseTargetDefectResidualStatement` | SurplusPair |
| 401 | `pairOverlapSystem` | `PairOverlapSystemStatement` | SurplusPair |
| 402 | `pairFailureOverlap` | `PairFailureOverlapStatement` | SurplusPair |
| 405 | `pairDemandReturns` | `PairDemandReturnsStatement` | SurplusPair |
| 412 | `pairConditionalFactorization` | `PairConditionalFactorizationStatement` | SurplusPair |
| 413 | `pairConditionalFactorizationResidual` | `PairConditionalFactorizationResidualStatement` | SurplusPair |
| 414 | `pairSystemRealizability` | `PairSystemRealizabilityStatement` | SurplusPair |
| 415 | `pairSystemEarlyOutcome` | `PairSystemEarlyOutcomeStatement` | SurplusPair |
| 416 | `pairSerialDemandSystem` | `PairSerialDemandSystemStatement` | SurplusPair |
| 417 | `pairIncrementCovered` | `PairIncrementCoveredStatement` | SurplusPair |
| 418 | `pairIncrementEarlyOutcome` | `PairIncrementEarlyOutcomeStatement` | SurplusPair |
| 419 | `pairSerialArithmetic` | `PairSerialArithmeticStatement` | SurplusPair |
| 420 | `pairPowerOfTwoCycle` | `PairPowerOfTwoCycleStatement` | SurplusPair |
| 600 | `sparseTargetDefectStructure` | `SparseTargetDefectStructureStatement` | SurplusPair |
| 601 | `homogeneousCapsFail` | `HomogeneousCapsFailStatement` | SurplusPair |

### Row and decision modules (20)

- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/Basic.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/BlockedPairEntropy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/FibrePressure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/FreePairCoupledExcess.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/FreePairEntropy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/HomogeneousBottleneckAudit.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/HomogeneousCapsClose.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/PairFailureOverlap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/PairOverlapFirstFailure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/PairOverlapSystem.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/PairPowerOfTwoCycle.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/PairSystemOutcome.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/PressureSpineSurplusEstimate.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/RoleFibrePartition.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/SameTokenBottleneckRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/SparseSurplusExit.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/SparseTargetDefectStructure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows/WindowOverloadClass.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SurplusRows.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SurplusRun.lean`

### EG assembly files (4)

- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Local.lean` (EG-NODE [126], [127], [128], [129], [130], [132], [133], [134], [135], [136], [138], [144])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Strict.lean` (EG-NODE [125])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Strict/Dependent.lean` (EG-NODE [140], [142], [143], [144], [138])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Strict/Independent.lean`

## F5: Spine / Cold / NearCubic

- Library statement module: `hypostructure/Hypostructure/Graph/Statements/Spine.lean` (and `hypostructure/Hypostructure/Graph/Statements/Parameters.lean`)
- Reserved new-key range: 1800-1999

### Keys (132)

| idx | Key | Statement | Statement module |
|---|---|---|---|
| 0 | `selection` | `SelectionStatement` | Spine |
| 1 | `returnAvoidance` | `ReturnAvoidanceStatement` | Spine |
| 2 | `noProperBaseline` | `NoProperBaselineStatement` | Spine |
| 3 | `tightEndpoint` | `TightEndpointStatement` | Spine |
| 4 | `slackIndependent` | `SlackIndependentStatement` | Spine |
| 5 | `uncompressible` | `UncompressibleStatement` | Spine |
| 6 | `maximalPacking` | `MaximalPackingStatement` | Spine |
| 7 | `localAlgebra` | `LocalAlgebraStatement` | Spine |
| 8 | `surplusAbove` | `SurplusAboveStatement` | Spine |
| 9 | `surplusAtOrBelow` | `SurplusAtOrBelowStatement` | Spine |
| 10 | `barrierCap` | `BarrierCapStatement` | Spine |
| 11 | `barrierOverflow` | `BarrierOverflowStatement` | Spine |
| 12 | `densityCap` | `DensityCapStatement` | Spine |
| 13 | `remainderNormalized` | `RemainderNormalizedStatement` | Spine |
| 14 | `boundaryDemand` | `BoundaryDemandStatement` | Spine |
| 15 | `stubSupply` | `StubSupplyStatement` | Spine |
| 16 | `wedgeSupply` | `WedgeSupplyStatement` | Spine |
| 18 | `curvatureTargetRank` | `CurvatureTargetRankStatement` | Spine |
| 19 | `curvatureRankDrop` | `CurvatureRankDropStatement` | Spine |
| 20 | `curvatureFullRank` | `CurvatureFullRankStatement` | Spine |
| 21 | `branchDependence` | `BranchDependenceStatement` | Spine |
| 22 | `contextUniversal` | `ContextUniversalStatement` | Spine |
| 23 | `contextDefect` | `ContextDefectStatement` | Spine |
| 24 | `atomCompression` | `AtomCompressionStatement` | Spine |
| 25 | `delocalizedSupport` | `DelocalizedSupportStatement` | Spine |
| 26 | `properDelocalization` | `ProperDelocalizationStatement` | Spine |
| 27 | `globalDelocalization` | `GlobalDelocalizationStatement` | Spine |
| 28 | `repairIdentity` | `RepairIdentityStatement` | Spine |
| 29 | `globalBarrier` | `GlobalBarrierStatement` | Spine |
| 30 | `coldCorridorState` | `ColdCorridorStateStatement` | Spine |
| 31 | `coldSameInterfaceTable` | `ColdSameInterfaceTableStatement` | Spine |
| 32 | `coldGermRealized` | `ColdGermRealizedStatement` | Spine |
| 33 | `coldGermDistinguished` | `ColdGermDistinguishedStatement` | Spine |
| 34 | `coldGermSilent` | `ColdGermSilentStatement` | Spine |
| 35 | `windowPackageSeparated` | `WindowPackageSeparatedStatement` | Spine |
| 37 | `forcedCurvatureCost` | `ForcedCurvatureCostStatement` | Spine |
| 38 | `remainderEntropyHigh` | `RemainderEntropyHighStatement` | Spine |
| 39 | `remainderEntropyLow` | `RemainderEntropyLowStatement` | Spine |
| 40 | `entropyPackageDemand` | `EntropyPackageDemandStatement` | Spine |
| 41 | `entropyCapActive` | `EntropyCapActiveStatement` | Spine |
| 42 | `largeBudgetResidual` | `LargeBudgetResidual` | Spine |
| 46 | `netChargeLocalization` | `NetChargeLocalizationStatement` | Spine |
| 47 | `netChargeNonNegative` | `NetChargeNonNegativeStatement` | Spine |
| 48 | `netChargeNegative` | `NetChargeNegativeStatement` | Spine |
| 50 | `negativeSupport` | `NegativeSupportStatement` | Spine |
| 64 | `coldFailureCycle` | `ColdFailureCycleStatement` | Spine |
| 65 | `coldFailureDefect` | `ColdFailureDefectStatement` | Spine |
| 66 | `coldFailureCompression` | `ColdFailureCompressionStatement` | Spine |
| 67 | `coldFailureHandoff` | `ColdFailureHandoffStatement` | Spine |
| 68 | `coldFailureRouting` | `ColdFailureRoutingStatement` | Spine |
| 69 | `coldHandoffTransfer` | `ColdFirstHighHandoffStatement` | Spine |
| 70 | `coldGermExtraction` | `ColdGermExtractionStatement` | Spine |
| 71 | `coldGermRouted` | `ColdGermRoutedStatement` | Spine |
| 145 | `netChargeCap` | `NetChargeCapStatement` | Spine |
| 146 | `exactCollisionFails` | `ExactCollisionFailsStatement` | Spine |
| 176 | `coldBranchClosed` | `ColdBranchClosedStatement` | Spine |
| 177 | `coldExchangeBound` | `ColdExchangeBoundStatement` | Spine |
| 179 | `coldSelectedBranchExcess` | `ColdSelectedBranchExcessStatement` | Spine |
| 180 | `coldAmbientCubicStubExcess` | `ColdAmbientCubicStubExcessStatement` | Spine |
| 181 | `coldGermFamilyPositive` | `ColdGermFamilyPositiveStatement` | Spine |
| 182 | `coldPositiveGerm` | `ColdPositiveGermStatement` | Spine |
| 200 | `hotColdPartition` | `HotColdWindowStatement` | Spine |
| 207 | `exactResponseProfile` | `ExactResponseProfileStatement` | Spine |
| 208 | `admissibleRankQuotient` | `AdmissibleRankQuotientStatement` | Spine |
| 210 | `targetRankCircuit` | `TargetRankCircuitStatement` | Spine |
| 211 | `barrierEnumeration` | `BarrierEnumerationStatement` | Spine |
| 212 | `coldRoute8Below` | `ColdRoute8BelowStatement` | Spine |
| 213 | `coldRoute8AtOrAbove` | `ColdRoute8AtOrAboveStatement` | Spine |
| 214 | `coldHotEntropyOverflow` | `ColdHotEntropyOverflowStatement` | Spine |
| 215 | `coldHotEntropyCap` | `ColdHotEntropyCapStatement` | Spine |
| 216 | `coldMass` | `ColdMassStatement` | Spine |
| 217 | `coldAmbientCubic` | `ColdAmbientCubicStatement` | Spine |
| 218 | `coldStubExcess` | `ColdStubExcessStatement` | Spine |
| 219 | `coldGermCandidates` | `ColdGermCandidatesStatement` | Spine |
| 221 | `cubicBaseline` | `CubicBaselineStatement` | Spine |
| 222 | `netDeficiencyCap` | `NetDeficiencyCapStatement` | Spine |
| 223 | `replacementExclusion` | `ReplacementExclusionStatement` | Spine |
| 224 | `coldMassLinear` | `ColdMassLinearStatement` | Spine |
| 225 | `coldMassBounded` | `ColdMassBoundedStatement` | Spine |
| 226 | `bridgeless` | `BridgelessStatement` | Spine |
| 227 | `coldReturnCorridors` | `ColdReturnCorridorsStatement` | Spine |
| 228 | `windowPackageRealized` | `WindowPackageRealizedStatement` | Spine |
| 229 | `windowPackageUnrealized` | `WindowPackageUnrealizedStatement` | Spine |
| 230 | `denseDeficiencyBelow` | `DenseDeficiencyBelowStatement` | Spine |
| 231 | `denseDeficiencyAtOrAbove` | `DenseDeficiencyAtOrAboveStatement` | Spine |
| 232 | `coldWindowStubStructure` | `ColdWindowStubStructureStatement` | Spine |
| 233 | `coldCanonicalNeutralConfiguration` | `CanonicalNeutralConfigurationStatement` | Spine |
| 234 | `coldGenuineSecondStrand` | `GenuineSecondStrandStatement` | Spine |
| 235 | `absorbedGermFanData` | `AbsorbedGermFanDataStatement` | Spine |
| 236 | `coldFamilyPositive` | `ColdFamilyPositiveStatement` | Spine |
| 237 | `coldFamilyEmpty` | `ColdFamilyEmptyStatement` | Spine |
| 238 | `blockedClassMember` | `BlockedClassMemberStatement` | Spine |
| 244 | `coldCanonicalSwapSmaller` | `ColdCanonicalSwapSmallerStatement` | Spine |
| 245 | `coldCanonicalSwapSameSize` | `ColdCanonicalSwapSameSizeStatement` | Spine |
| 320 | `blockedScaleAdditive` | `BlockedScaleAdditivityStatement` | Spine |
| 321 | `blockedBarrierOverlap` | `BlockedBarrierFailureStatement` | Spine |
| 322 | `degreeProfileFibres` | `DegreeProfileFibresStatement` | Spine |
| 323 | `targetCompleteContextUniversality` | `TargetCompleteContextUniversalityStatement` | Spine |
| 324 | `separatedTesters` | `SeparatedTestersStatement` | Spine |
| 325 | `entropyCapBound` | `EntropyCapBoundStatement` | Spine |
| 326 | `absorbedConfigurationResidual` | `AbsorbedConfigurationResidualStatement` | Spine |
| 327 | `absorbedGermSplit` | `AbsorbedGermSplitStatement` | Spine |
| 337 | `densePackingOverflow` | `DensePackingOverflowStatement` | Spine |
| 403 | `denseColdCorridorsTerminal` | `DenseColdCorridorsTerminalStatement` | Spine |
| 404 | `coldFirstFailureOccurrence` | `ColdFirstFailureOccurrenceStatement` | Spine |
| 406 | `coldNeutralEqualLengthTerminal` | `NeutralEqualLengthTerminalConfigurationStatement` | Spine |
| 407 | `coldDeclaredHandoffLedger` | `ColdDeclaredHandoffLedgerStatement` | Spine |
| 408 | `coldCanonicalReplacementSwap` | `CanonicalReplacementSwapStatement` | Spine |
| 409 | `coldCanonicalReplacementTrivial` | `CanonicalReplacementTrivialStatement` | Spine |
| 410 | `coldTwoStrandSurvivor` | `TwoStrandSurvivorStatement` | Spine |
| 411 | `coldSymmetricPairExcluded` | `ColdSymmetricPairExcludedStatement` | Spine |
| 421 | `independentObstructionTranslates` | `IndependentObstructionTranslatesStatement` | Spine |
| 422 | `coldFailureDefectRoute` | `ColdFailureDefectRoutesStatement` | Spine |
| 423 | `blockedCompressionBound` | `BlockedCompressionBoundStatement` | Spine |
| 424 | `blockedCompressionCap` | `BlockedCompressionCapStatement` | Spine |
| 425 | `cycleRankConstraint` | `CycleRankConstraintStatement` | Spine |
| 428 | `dominantRootedWedgeType` | `DominantRootedWedgeTypeStatement` | Spine |
| 429 | `localTypeCoordinateRepetitive` | `LocalTypeCoordinateRepetitiveStatement` | Spine |
| 430 | `localTypeCoordinateNonrepetitive` | `LocalTypeCoordinateNonrepetitiveStatement` | Spine |
| 431 | `dominantRootedType` | `DominantRootedTypeSchema` | Spine |
| 432 | `dominantRootedTypeWedgeFree` | `DominantRootedTypeWedgeFreeStatement` | Spine |
| 439 | `contractionCritical` | `ContractionCriticalStatement` | Spine |
| 500 | `gadgetClosure` | `GadgetClosureStatement` | Spine |
| 501 | `remainderRelabelingEntropy` | `RemainderRelabelingEntropyStatement` | Spine |
| 502 | `relabelingDensityCap` | `RelabelingDensityCapStatement` | Spine |
| 602 | `coldGermSomeRealizing` | `ColdGermSomeRealizingStatement` | Spine |
| 603 | `coldGermNoneRealizing` | `ColdGermNoneRealizingStatement` | Spine |
| 604 | `coldGermSomeDistinguishing` | `ColdGermSomeDistinguishingStatement` | Spine |
| 605 | `coldGermNoneDistinguishing` | `ColdGermNoneDistinguishingStatement` | Spine |
| 606 | `mersenneReturn` | `MersenneReturnStatement` | Spine |
| 607 | `windowFree` | `Graph.InducedPathFree` | library predicate |
| 608 | `windowPresent` | `Graph.HasInducedPath` | library predicate |

### Row and decision modules (74)

- `hypostructure/Hypostructure/Graph/Strategy/BlockedCompressionRows.lean`
- `hypostructure/Hypostructure/Graph/Strategy/BranchDClosure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/AbsorbedGerm.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/Basic.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/CanonicalReplacement.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/ColdFamilyClosure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/ColdMass.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/CorridorState.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/DenseTerminal.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/EntryDichotomies.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/FailureClauses.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/FirstFailureOccurrence.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/FirstFailureRouting.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/GermCandidates.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/GermExtraction.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/GermFamilyPositive.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/GermTrichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/HandoffTransfer.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/NeutralTerminal.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/ReturnCorridor.lean`
- `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows/TwoStrand.lean`
- `hypostructure/Hypostructure/Graph/Strategy/DominantRootedType.lean`
- `hypostructure/Hypostructure/Graph/Strategy/EntropyClosure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/AbsorbedConfigurationResidual.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/AtomCompressionDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/BarrierEnumeration.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/BoundaryDemand.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/BranchDependence.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Bridgeless.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ContextValidityDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ContractionCritical.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/CubicBaseline.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/CurvatureRankDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/CurvatureTargetRank.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/CycleRankConstraint.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DegreeProfileFibres.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DeletionCriticality.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DelocalizationScopeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DenseNetDeficiencyCap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DominantRootedType.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/DominantRootedTypeWedgeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/EntropyCapDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/EntropyPackage.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ExactCollisionDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ForcedCurvatureCost.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/GadgetClosure.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/GlobalBarrier.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/HotColdPartition.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/IndependentObstructionTranslates.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/InterfaceReplacement.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/LiveHotBarrierCap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/LocalAlgebra.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/LocalTypeCoordinateDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/LowEntropyLargeBudget.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/NegativeSupport.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/NetChargeDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/NetChargeLocalization.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/NetDeficiencyCap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/NoProperBaseline.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ObstructionPacking.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/RelabelingDensityCap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/RemainderEntropyDichotomy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/RemainderNormalization.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/RemainderRelabelingEntropy.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/RepairIdentity.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ReplacementExclusion.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/ReturnAvoidance.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/RouteEightNetDeficiencyCap.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/SeparatedTesters.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/StubSupply.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TargetCompleteContextUniversality.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TargetRankCircuit.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/WedgeSupply.lean`
- `hypostructure/Hypostructure/Graph/Strategy/SpineRows/WindowPackage.lean`

### EG assembly files (56)

- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Absorbed/Prerequisites.lean` (EG-NODE [153], [154], [155], [156], [157], [163], [165], [166], [167], [169], [175], [176], [177])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Absorbed/Residual.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Cold/Barrier.lean` (EG-NODE [22], [23], [24])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Cold/Entropy.lean` (EG-NODE [145], [146], [148], [149])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Cold/Germs.lean` (EG-NODE [150], [151], [152], [153], [154], [155], [156], [157])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Entry.lean` (EG-NODE [5], [6], [8], [9], [10], [13], [14], [15], [17], [18], [7], [11], [12], [16], [19], [20], [4])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Local.lean` (EG-NODE [21], [158], [160], [154], [154], [137], [20], [131], [137], [138], [178], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [12])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Replacement.lean` (EG-NODE [170], [171], [159])
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRate.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRate/FullRank.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRate/HighEntropy.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRate/Nonrepetitive.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRate/Wedge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRate/WedgeFree.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/Bounded.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/FullRank.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/HighEntropy.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/Linear.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/Nonrepetitive.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/Wedge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/BelowRateFailure/WedgeFree.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/Bounded.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/FullRank.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/HighEntropy.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/Linear.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/Nonrepetitive.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/Wedge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseAtOrAbove/WedgeFree.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseBelow.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseBelow/FullRank.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseBelow/HighEntropy.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseBelow/Nonrepetitive.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseBelow/Wedge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/DenseBelow/WedgeFree.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/Realized.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/Bounded.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/FullRank.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/HighEntropy.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/Linear.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/Nonrepetitive.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/Wedge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedAtOrAbove/WedgeFree.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedBelow.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedBelow/FullRank.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedBelow/HighEntropy.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedBelow/Nonrepetitive.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedBelow/Wedge.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/RealizedBelow/WedgeFree.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/Unrealized.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/UnrealizedBelow.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Survivor/UnrealizedDense.lean`
- `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NetCharge/Continuation.lean` (EG-NODE [57], [58], [59], [60], [61], [62], [63], [64], [173], [174], [86])

## Shared files

| File | Owner | Rule |
|---|---|---|
| `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` | F5 (structure, `Data`, key-freshness tactic) | A new key is six lines: constructor, `Holds` branch, `label`, `idx`, `ofIdx`, `name`, plus its `LabelPins` line; each family appends only its own key lines, with anchored edits in disjoint regions. |
| `hypostructure/Hypostructure/Graph/Statements/Parameters.lean` | F5 | A new registered constant is added only by F5. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Final.lean` | F5 | Other families change only the arm of their own returned outcome. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Basic.lean` | F5 | Problem, input and selection key; no family-specific content. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean` | F5 | Import aggregator. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/RouteEight/Boundary.lean` | F3 | Boundary chain `Basic <- RouteEight <- Absorbed <- NetCharge <- NearCubic` (and `Basic <- Surplus`); a family edits only its own disjunct. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Absorbed/Boundary.lean` | F5 | Boundary chain `Basic <- RouteEight <- Absorbed <- NetCharge <- NearCubic` (and `Basic <- Surplus`); a family edits only its own disjunct. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NetCharge/Boundary.lean` | F5 | Boundary chain `Basic <- RouteEight <- Absorbed <- NetCharge <- NearCubic` (and `Basic <- Surplus`); a family edits only its own disjunct. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/NearCubic/Boundary.lean` | F5 | Boundary chain `Basic <- RouteEight <- Absorbed <- NetCharge <- NearCubic` (and `Basic <- Surplus`); a family edits only its own disjunct. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Surplus/Boundary.lean` | F4 | Boundary chain `Basic <- RouteEight <- Absorbed <- NetCharge <- NearCubic` (and `Basic <- Surplus`); a family edits only its own disjunct. |
| `hypostructure/Hypostructure/Graph/Strategy/SpineAssembly.lean` | F5 | Aggregator or shared composition surface; append-only imports. |
| `hypostructure/Hypostructure/Graph/Strategy/SpineContinuationRun.lean` | F5 | Aggregator or shared composition surface; append-only imports. |
| `hypostructure/Hypostructure/Graph/Strategy/SpineRows.lean` | F5 | Aggregator or shared composition surface; append-only imports. |
| `hypostructure/Hypostructure/Graph/Strategy/SpineRows/Basic.lean` | F5 | Aggregator or shared composition surface; append-only imports. |
| `hypostructure/Hypostructure/Graph/Strategy/ColdCorridorRows.lean` | F5 | Aggregator or shared composition surface; append-only imports. |
| `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` | F4 | Aggregator or shared composition surface; append-only imports. |
| `hypostructure/Hypostructure.lean` | F5 | Root import list; append-only. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/StrategyDag.lean`, `Problem.lean` | F5 | Application boundary; unchanged by the migration. |

## Cross-family keys

A key produced by a row of another family, or by rows of several families,
belongs to the family of its producing row; where rows of several families
produce the same key, the owner is the family of the majority of its producing
rows.  Each producing row is listed with its own family.

| Key | Owner | Producing row modules |
|---|---|---|
| `typeBFanEntry` | F2 | `ColdCorridorRows/AbsorbedGermFanEnvelope.lean` (F2), `HomogeneousBottleneckRows/PairSystemOutcome.lean` (F4), `HomogeneousBottleneckRows/SameTokenTypeBFanEntry.lean` (F2), `SpineRows/TypeBAssignedSupport.lean` (F2), `SpineRows/TypeBDecoratedAssignedSupport.lean` (F2) |

Assignments that follow the producing row rather than the key name:

- `typeBHighSurplus` (idx 52) is F1: the node-`[62]` decision
  `SpineRows/TypeSplitDichotomy.lean` (F1) produces it together with
  `typeALowSurplus`; F2 consumes it.
- `largeBudgetResidual` (idx 42) is F5: it is produced by the node-`[53]`
  decision `SpineRows/EntropyCapDichotomy.lean` and by
  `SpineRows/LowEntropyLargeBudget.lean`, both F5 rows.
- `typeBHandoff` (idx 184) is F4: it is produced by the node-`[144]` row
  `HomogeneousBottleneckRows/SameTokenBottleneckRouting.lean`.
- `netDeficiencyCap` (idx 222) is F5: all three producing rows
  (`NetDeficiencyCap`, `DenseNetDeficiencyCap`, `RouteEightNetDeficiencyCap`)
  are F5 rows.

Keys with no producing row module under `Graph/Strategy` (produced by the
framework scope initialization or by a decision in an owned assembly file) stay
with the family listed above: `selection` (F5), `surplusAbove` (F5), `surplusAtOrBelow` (F5), `barrierOverflow` (F5), `quantitativeOverload` (F4), `windowPackageRealized` (F5), `windowPackageUnrealized` (F5), `denseDeficiencyBelow` (F5), `denseDeficiencyAtOrAbove` (F5), `route8Deficit` (F3), `route8UnifiedVisibleHistory` (F3), `coldGermSomeRealizing` (F5), `coldGermNoneRealizing` (F5), `coldGermSomeDistinguishing` (F5), `coldGermNoneDistinguishing` (F5).

