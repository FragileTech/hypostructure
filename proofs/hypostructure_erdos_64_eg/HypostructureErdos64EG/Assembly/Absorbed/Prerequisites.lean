import HypostructureErdos64EG.Assembly.NearCubic.ColdPass

/-!
# Assembly: Absorbed / Prerequisites

The node-`[153]` corridor and extraction facts which node `[175]` receives on
the absorbed-configuration residual `[174]`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **Node `[174]`**: the absorbed configurations are the cold corridors whose
charge node `[153]`'s bounded arm discarded.  Their return corridors
(`lem:bridgeless`), states, first failures and candidate family are published
by the registered node-`[153]` owners on this literal residual; `[175]` only
queries them.  Node `[153]`'s exact (★) decision is taken here as on the
spine: its ¬(★) arm returns the explicitly constructed residual
`K .coldRepeatedStateResidual`.  Node `[162]`'s terminality is not run here:
the paper states it only on the dense-packing residual
(`lem:dense-cold-pass`), and node `[176]` does not use it
(`lem:absorbed-germ-fan-data` (i)).

`arm` names the prefix and entropy arm; `[153]` is returned as the absorbed-
lane subtype of that path. -/
noncomputable def selectedAbsorbedGermPrerequisites
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : NetChargeArms selected)
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint
      [K .coldReturnCorridors, K .coldCorridorState,
        K .coldFirstFailureOccurrence, K .coldCutStatesDistinct,
        K .coldRepeatedStateResidual,
        K .coldFailureCycle, K .coldFailureDefectRoute,
        K .coldFailureCompression, K .coldHandoffTransfer,
        K .coldFailureRouting, K .coldExchangeBound,
        K .coldGermCandidates] known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    PSum
      (ExactLedger EGInput.{u} selected
        (K .coldGermCandidates :: K .coldExchangeBound ::
          K .coldFailureRouting :: K .coldHandoffTransfer ::
          K .coldFailureCompression ::
          K .coldFailureDefectRoute :: K .coldFailureCycle ::
          K .coldCutStatesDistinct :: K .coldFirstFailureOccurrence ::
          K .coldCorridorState :: K .coldReturnCorridors :: known))
      (Node153ResidualSubtypes selected) :=
  let state := nearCubicColdCorridorState history
  match nearCubicColdOccurrence state
      (Or.inl ⟨coldBranchClosedAbsorbedCommonReturn history, arm.1, arm.2⟩) with
  | .inl distinct => .inl (nearCubicColdCandidates distinct)
  | .inr repeated => .inr repeated

end HypostructureErdos64EG
