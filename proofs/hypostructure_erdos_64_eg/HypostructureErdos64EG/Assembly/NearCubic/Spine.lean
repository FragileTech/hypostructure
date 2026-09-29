import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.BoundaryDemand
import Hypostructure.Graph.Strategy.SpineRows.BranchDependence
import Hypostructure.Graph.Strategy.SpineRows.CurvatureRankDichotomy
import Hypostructure.Graph.Strategy.SpineRows.CurvatureTargetRank
import Hypostructure.Graph.Strategy.SpineRows.DenseNetDeficiencyCap
import Hypostructure.Graph.Strategy.SpineRows.DominantRootedType
import Hypostructure.Graph.Strategy.SpineRows.DominantRootedTypeWedgeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.EntropyCapDichotomy
import Hypostructure.Graph.Strategy.SpineRows.EntropyPackage
import Hypostructure.Graph.Strategy.SpineRows.ForcedCurvatureCost
import Hypostructure.Graph.Strategy.SpineRows.IndependentObstructionTranslates
import Hypostructure.Graph.Strategy.SpineRows.LocalTypeCoordinateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.LowEntropyLargeBudget
import Hypostructure.Graph.Strategy.SpineRows.NetDeficiencyCap
import Hypostructure.Graph.Strategy.SpineRows.RemainderEntropyDichotomy
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.Route8RateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden
import Hypostructure.Graph.Strategy.SpineRows.Route8RateFailsJoin
import Hypostructure.Graph.Strategy.SpineRows.RouteEightNetDeficiencyCap
import Hypostructure.Graph.Strategy.SpineRows.StubDeficit
import Hypostructure.Graph.Strategy.SpineRows.StubSupply
import Hypostructure.Graph.Strategy.SpineRows.TargetRankCircuit
import Hypostructure.Graph.Strategy.SpineRows.WedgeSupply
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.DenseEntropy
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NetCharge.Continuation

/-!
# Assembly: NearCubic / Spine

The spine `[25]`--`[56]` of Part II--IV, written once and run on every arm
that continues at `[25]`: the bounded arm of `[153]` returning through `[24]`,
the `[146]` yes-arm `[147]` (`θ < 1/78`), and the `[160]` double-yes arm
`[161]`.  Each composition is generic over the incoming ledger index `known`;
its requirements are `FactKeys.Has` constraints and its freshness is one
`List.Disjoint` covering hypothesis, discharged at the literal call sites.

`[56]` reads the arm's density input -- `lem:dense-deficiency-routing`: "nodes
`[56]`--`[64]` consume the density cap only through the inequality
`def⁺(R) − σ(R) < |R|/4`" -- which is `K .densityCap` on the `[24]` arm,
`K .coldRoute8Below` on the `[147]` arm and `K .denseDeficiencyBelow` on the
`[161]` arm.  The route-8 private-carrier rate consumed at `[120]`--`[122]` is
already on the ledger on the `[147]` and `[161]` arms, retained as failed on
the `[160]` second complement, and decided at the entry of the route-8
continuation on the `[24]` arm, whose density cap does not decide it.  These
are the four spine exits `nearCubicLargeBudget*` below.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Every key committed from `[25]` through Branch D's closure `[46]`. -/
noncomputable abbrev nearCubicResidualAKeys : FactKeys EGInput.{u} :=
  [K .remainderNormalized, K .boundaryDemand,
    K .stubSupply, K .wedgeSupply, K .exactResponseProfile,
    K .curvatureTargetRank, K .targetRankCircuit,
    K .curvatureRankDrop, K .curvatureFullRank, K .branchDependence,
    K .contextDefect, K .contextUniversal,
    K .atomCompression, K .delocalizedSupport, K .properDelocalization,
    K .globalDelocalization, K .repairIdentity, K .globalBarrier, closed]

/-- Every key committed from `[47]` through the net-charge continuation, on an
arm whose route-8 rate is already decided. -/
noncomputable abbrev nearCubicResidualBKeys : FactKeys EGInput.{u} :=
  [K .forcedCurvatureCost, K .remainderEntropyHigh, K .remainderEntropyLow,
    K .entropyPackageDemand, K .entropyCapActive, K .largeBudgetResidual,
    K .entropyCapBound, K .entropyJointRealization, K .allColdEntropyResidual, K .stubDeficitIdentity,
    K .remainderCycleSpectrum, K .localTypeCoordinateRepetitive,
    K .localTypeCoordinateNonrepetitive, K .dominantRootedType,
    K .dominantRootedWedgeType, K .dominantRootedTypeWedgeFree,
    K .independentObstructionTranslates, K .netDeficiencyCap] ++
    netChargeContinuationKeys

/-- Branch D, nodes `[36]`--`[46]`, on the literal ledger returned by node
`[35]`.  The displayed state at `[35]` repeats `[33]` verbatim: node `[21]`'s
one certificate `branchCertificate? data G`, which every later test reads.  The context-validity decision `[36]` with its
target-defect terminal `[37]`, the atom-compression test `[38]` with its
terminal `[39]`, the delocalization scope `[40]`/`[41]` with its proper-support
terminal `[42]`, and the whole-graph route `[43]`--`[45]` closed at `[46]`.
Every terminal is a framework closure over the ledger of its arm. -/
-- EG-NODE [35] Branch D: rank-reducing obstruction dependence
-- EG-NODE [36] valid against every outside context?
-- EG-NODE [37] target-defective quotient
-- EG-NODE [38] target-complete with smaller proper representative?
-- EG-NODE [39] proper-piece compression
-- EG-NODE [40] requires enlarged connected support $Z\supsetneq C$
-- EG-NODE [41] $Z\subsetneq G$?
-- EG-NODE [42] proper-support dependence closure: target defect or compression
-- EG-NODE [43] $Z=G$: whole-graph support dependence
-- EG-NODE [44] $1$--$3$ repair identity $s=p-2+2\beta-\sigma$
-- EG-NODE [45] target / replacement / global profile barrier
-- EG-NODE [46] rank-drop branch closed
theorem nearCubicRankDropCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .branchDependence) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .selection) known]
    (fresh : List.Disjoint
      [K .contextDefect, K .contextUniversal, K .atomCompression,
        K .delocalizedSupport, K .properDelocalization,
        K .globalDelocalization, K .repairIdentity, K .globalBarrier, closed]
      known := by key_fresh) : False := by
  match contextValidityDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left defectHistory =>
      -- `[37]`: target-defective quotient, closed against node `[12]`
      -- (`lem:context-universality`; `lem:full-rank`, tex 9388).
      exact (closeIncompatible defectHistory (K .targetCompleteContextUniversality)
        (K .contextDefect) (by key_fresh)).elimClosed (by infer_instance)
  | .right universalHistory =>
      -- `[38]`: target-complete with a smaller proper representative?
      match atomCompressionDichotomy (data := spineData) universalHistory
          (by key_fresh) (by key_fresh) with
      | .left compressionHistory =>
          -- `[39]`: proper atom compression, forbidden by `lem:replacement` `[13]`.
          exact (closeIncompatible compressionHistory (K .replacementExclusion)
            (K .atomCompression) (by key_fresh)).elimClosed
            (by infer_instance)
      | .right delocalizedHistory =>
          -- `[40]`/`[41]`: the enlarged connected support `Z ⊋ C`; is `Z ⊊ G`?
          match delocalizationScopeDichotomy (data := spineData) delocalizedHistory
              (by key_fresh) (by key_fresh) with
          | .left properHistory =>
              -- `[42]`: proper-support smearing closure (`lem:proper-smearing`).
              exact (closeIncompatible properHistory (K .replacementExclusion)
                (K .properDelocalization) (by key_fresh)).elimClosed
                (by infer_instance)
          | .right globalHistory =>
              -- `[43]`--`[45]`: whole-graph delocalization, the `1`--`3` repair
              -- identity, and the target/replacement/global-profile barrier.
              let repaired :=
                (repairIdentityRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  globalHistory (by key_fresh)
              let barrier :=
                (globalBarrierRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  repaired (by key_fresh)
              -- `[46]`: rank-drop branch closed (`lem:no-silent-global-smearing`).
              exact (closeIncompatible barrier (K .selection) (K .globalBarrier)
                (by key_fresh)).elimClosed (by infer_instance)

/-- **Nodes `[25]`--`[34]`** on the literal residual of an arm continuing at
`[25]`: Residual A and its normalization `[25]`--`[28]`, the external-incidence
supply `[29]`, the wedge lower bound `[30]`, the obstruction rank `[31]` with
`lem:target-rank-circuit`, and the exact finite rank split `[32]` at the
canonical maximal packing.  Its rank-drop arm is Branch D `[33]`/`[35]`, closed
by `nearCubicRankDropCloses`; the returned ledger is the full-rank arm `[34]`. -/
-- EG-NODE [25] Residual A: $R=G-\bigcup V(P)$ is large and componentwise $P_{13}$-free
-- EG-NODE [26] Residual A: $R$ large and componentwise $P_{13}$-free
-- EG-NODE [27] no component of $R$ has an internal $3$-core
-- EG-NODE [28] positive deficiency $\defp(X)=\sum_v\max(0,3-d_X(v))$
-- EG-NODE [29] external-incidence supply: $\defp(R)\le15p_{13}+o(n)$ and $\defp(R)-\sigma_R\le15p_{13}+o(n)$
-- EG-NODE [30] wedge lower bound: $W_2(R)\ge\omega_{\rm win}|R|-o(|R|)$ (sharper high-entropy $\omega=2.57407357888\ldots$)
-- EG-NODE [31] obstruction rank $r_\Omega(R)$
-- EG-NODE [32] rank drop? $r_\Omega(R)<W_2(R)-o(W_2)$
-- EG-NODE [33] Branch D: rank-reducing obstruction dependence
-- EG-NODE [34] Residual B: no rank drop; full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$
noncomputable def nearCubicFullRank
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint nearCubicResidualAKeys.{u} known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .curvatureFullRank :: K .targetRankCircuit :: K .exactResponseProfile ::
        K .curvatureTargetRank :: K .wedgeSupply ::
        K .stubSupply :: K .boundaryDemand ::
        K .remainderNormalized :: known) :=
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let boundary :=
    (boundaryDemandRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      remainder (by key_fresh)
  let stubSupply :=
    (stubSupplyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      boundary (by key_fresh)
  let wedge :=
    (wedgeSupplyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      stubSupply (by key_fresh)
  let rank :=
    (curvatureTargetRankRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      wedge (by key_fresh)
  let circuit :=
    (targetRankCircuitRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      rank (by key_fresh)
  match curvatureRankDichotomy (data := spineData) circuit
      (by key_fresh) (by key_fresh) with
  | .left dropHistory =>
      let dependence :=
        (branchDependenceRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          dropHistory (by key_fresh)
      (nearCubicRankDropCloses dependence).elim
  | .right fullRankHistory => fullRankHistory

set_option maxHeartbeats 8000000 in
/-- The route-8 continuation `[57]`--`[124]` entered from the `[24]` arm.  It
consumes the private-carrier rate at `[120]`--`[122]`, and `[24]`'s density cap
does not decide it (`Hypostructure.Fixtures.Route8RateDensityCapGap`); its exact
test is taken here, at the entry of that continuation, and a failed rate is
retained as the `[187]` outcome.

`arm` names the near-cubic route into the `[24]` arm and the entropy arm; the
failed rate is returned as the subtype of that path. -/
noncomputable def nearCubicRouteEightEntry
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : DensityCapArm selected ∧ EntropyArm selected)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint
      (K .route8Rate :: K .route8RateFails :: K .route8RateFailsJoin ::
        K .route8RateFailsPiece :: K .route8RateFailsCrossBound ::
        K .route8RateFailsFlow :: K .route8CarrierInjection :: K .route8RateExactSlack ::
        K .route8BasinBurden :: K .route8StubDeficit :: K .route8DeficitVsStubs ::
        K .route8EntryLowerBound :: K .route8CoreEmpty :: K .route8StrongRate ::
        K .route8ThinIsolation :: K .route8WindowStub :: K .route8ThinSmall ::
        K .route8WindowRPathGap :: K .route8HubStubs ::
        netChargeContinuationKeys.{u}) known := by
        key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNearCubicSurvivorBoundary selected :=
  match route8RateDichotomy (data := spineData) history .netDeficiencyCap
      (Or.inl rfl) (by key_fresh) (by key_fresh) with
  | .left rated => Or.inl (selectedNetChargeContinuation rated (Or.inl ⟨arm.1.toPrefix, arm.2⟩))
  | .right rateFails =>
      -- G audit: the failed rate against the exact window join at `P₀`.
      let joined := (route8RateFailsJoinRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        rateFails (by key_fresh)
      let pieced := (route8RateFailsPieceRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        joined (by key_fresh)
      let crossed := (route8RateFailsCrossBoundRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        pieced (by key_fresh)
      let flowed := (route8RateFailsFlowRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        crossed (by key_fresh)
      let injected := (route8CarrierInjectionRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        flowed (by key_fresh)
      let exacted := (route8RateExactSlackRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        injected (by key_fresh)
      let basined := (route8BasinBurdenRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        exacted (by key_fresh)
      let stubbed := (route8StubDeficitRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        basined (by key_fresh)
      let versus := (route8DeficitVsStubsRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        stubbed (by key_fresh)
      let entried := (route8EntryLowerBoundRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        versus (by key_fresh)
      let coreEmpty := (route8CoreEmptyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        entried (by key_fresh)
      let strongRate := (route8StrongRateRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        coreEmpty (by key_fresh)
      let thinIso := (route8ThinIsolationRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        strongRate (by key_fresh)
      let windowStub := (route8WindowStubRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        thinIso (by key_fresh)
      let thinSmall := (route8ThinSmallRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        windowStub (by key_fresh)
      let rpathGap := (route8WindowRPathGapRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        thinSmall (by key_fresh)
      let hubStubs := (route8HubStubsRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        rpathGap (by key_fresh)
      Or.inr (Or.inl (route8RateFailsSubtypesReturn_routeEightEntry hubStubs arm.1 arm.2))

set_option maxHeartbeats 8000000 in
/-- The route-8 continuation `[57]`--`[124]` on the `[162]` arm entered from
`[160]`'s second complement: the ledger retains the failed private-carrier rate
the continuation would consume at `[120]`--`[122]`, and the retained failure is
the `[187]` outcome.

`entropy` names the entropy arm (a low-entropy arm: the high-entropy arm of
this dense residual is closed at `[53]`); the failed rate is returned as the
subtype of that path. -/
noncomputable def nearCubicRateFailedExit
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (entropy : EntropyArmLow selected)
    (joinFresh : K .route8RateFailsJoin ∉ known := by key_fresh)
    (pieceFresh : K .route8RateFailsPiece ∉ known := by key_fresh)
    (crossFresh : K .route8RateFailsCrossBound ∉ known := by key_fresh)
    (flowFresh : K .route8RateFailsFlow ∉ known := by key_fresh)
    (injectionFresh : K .route8CarrierInjection ∉ known := by key_fresh)
    (exactFresh : K .route8RateExactSlack ∉ known := by key_fresh)
    (basinFresh : K .route8BasinBurden ∉ known := by key_fresh)
    (stubFresh : K .route8StubDeficit ∉ known := by key_fresh)
    (versusFresh : K .route8DeficitVsStubs ∉ known := by key_fresh)
    (entryFresh : K .route8EntryLowerBound ∉ known := by key_fresh)
    (coreEmptyFresh : K .route8CoreEmpty ∉ known := by key_fresh)
    (strongFresh : K .route8StrongRate ∉ known := by key_fresh)
    (thinIsoFresh : K .route8ThinIsolation ∉ known := by key_fresh)
    (windowStubFresh : K .route8WindowStub ∉ known := by key_fresh)
    (thinSmallFresh : K .route8ThinSmall ∉ known := by key_fresh)
    (rpathFresh : K .route8WindowRPathGap ∉ known := by key_fresh)
    (hubFresh : K .route8HubStubs ∉ known := by key_fresh)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .boundedDensityOrder) known]
    [FactKeys.Has (K .boundedOrderSmall) known]
    [FactKeys.Has (K .route8RateFails) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNearCubicSurvivorBoundary selected :=
  let joined := (route8RateFailsJoinRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by key_fresh)
  let pieced := (route8RateFailsPieceRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    joined (by key_fresh)
  let crossed := (route8RateFailsCrossBoundRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    pieced (by key_fresh)
  let flowed := (route8RateFailsFlowRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    crossed (by key_fresh)
  let injected := (route8CarrierInjectionRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    flowed (by key_fresh)
  let exacted := (route8RateExactSlackRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    injected (by key_fresh)
  let basined := (route8BasinBurdenRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    exacted (by key_fresh)
  let stubbed := (route8StubDeficitRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    basined (by key_fresh)
  let versus := (route8DeficitVsStubsRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    stubbed (by key_fresh)
  let entried := (route8EntryLowerBoundRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    versus (by key_fresh)
  let coreEmpty := (route8CoreEmptyRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    entried (by key_fresh)
  let strongRate := (route8StrongRateRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    coreEmpty (by key_fresh)
  let thinIso := (route8ThinIsolationRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    strongRate (by key_fresh)
  let windowStub := (route8WindowStubRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    thinIso (by key_fresh)
  let thinSmall := (route8ThinSmallRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    windowStub (by key_fresh)
  let rpathGap := (route8WindowRPathGapRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    thinSmall (by key_fresh)
  let hubStubs := (route8HubStubsRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    rpathGap (by key_fresh)
  Or.inr (Or.inl (route8RateFailsSubtypesReturn_rateFailedExit hubStubs entropy))

set_option maxHeartbeats 8000000 in
/-- **Nodes `[47]`--`[56]`** on the full-rank arm `[34]`, `[147]` arm (`θ < 1/78`): `[56]` reads the strict cap from `K .coldRoute8Below`,
the route-8 carrier inequality `τ(θ) < 3/13 < 1/4`; the private-carrier rate
`K .route8Rate` consumed at `[120]`--`[122]` is already on this ledger.

`[47]`/`[48]`: `cor:forced-curvature-cost`; `[49]`/`[50]`: the per-vertex
remainder-entropy split; on the high arm `[52]`/`[53]` the joint account and the
entropy-cap test, closed at `[54]`; on the low arm the repetitive and root-wedge
splits of `lem:dominant-type`; every surviving arm is Residual C `[55]`.

`lanePrefix` names the near-cubic route into the `[147]` arm; `[54]` is
returned as that route's subtype and the net-charge continuation receives the
route with the entropy arm. -/
-- EG-NODE [47] Residual B: full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$
-- EG-NODE [48] forced obstruction cost $c_\Omega W_2(R)\ge K_{\rm win}|R|-o(|R|)$ (high entropy: $K=5.89262883286\ldots$)
-- EG-NODE [49] per-vertex remainder entropy $\eta(R)=\log_2|\mathcal G(R)|/|R|$
-- EG-NODE [50] $\eta(R)\ge\frac1{10}\log_2 n$?
-- EG-NODE [51] high-entropy remainder branch
-- EG-NODE [52] window plus remainder accounting bounds $\theta$
-- EG-NODE [53] remaining non-obstruction budget $<K|R|$?
-- EG-NODE [54] entropy cap closes
-- EG-NODE [55] Residual C: large-budget branch; $\theta\le\theta_{\rm win}+o(1)$
-- EG-NODE [56] $\Delta_{\mathrm{net}}(R)=\dfrac{\defp(R)-\sigma_R}{|R|}\le\tau_{\rm win}+o(1)<1/4$
-- EG-NODE [164] all-cold comparison closes: \(|\mathcal G(R)|\le|\mathcal G_{n,m}|\) by the remainder glue
noncomputable def nearCubicLargeBudgetColdRate
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (lanePrefix : ColdRateArm selected)
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint nearCubicResidualBKeys.{u} known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNearCubicSurvivorBoundary selected := by
  let cost :=
    (forcedCurvatureCostRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match remainderEntropyDichotomy (data := spineData) cost
      (by key_fresh) (by key_fresh) with
  | .left highHistory =>
      let package :=
        (entropyPackageRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          highHistory (by key_fresh)
      match entropyCapDichotomy (data := spineData) package
          (by key_fresh) (by key_fresh) with
      | .left activeHistory =>
          -- `[54]`: the exact decision on the joint realization inequality at G.
          match entropyJointRealizationDichotomy (data := spineData) activeHistory
              (by key_fresh) (by key_fresh) with
          | .left jointHistory =>
              exact ((entropyCapBoundRow (BranchState := BranchState)
                (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                (presentation := erdosReceiverLoadProfile)
                (data := spineData)).runAndCloseIncompatible jointHistory
                  (K .entropyCapActive) (K .entropyCapBound)
                  (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
          | .right residualHistory =>
              -- the configuration at G where the joint realization fails,
              -- with the stub-deficit identity and the cycle spectrum of `R₀`,
              -- returned.
              let residualHistory :=
                (stubDeficitRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run residualHistory (by key_fresh)
              exact Or.inr (Or.inr (Or.inr (Or.inr
                (node54SubtypesReturn_coldRate residualHistory lanePrefix))))
      | .right boundHistory =>
          -- `[55]`: Residual C on the high-entropy arm.
          let largeHistory :=
            (highEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              boundHistory (by key_fresh)
          exact Or.inl (selectedNetChargeContinuation
                ((routeEightNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  largeHistory (by key_fresh))
                (Or.inl ⟨lanePrefix.toPrefix, Or.inl (EntropyArmBlock_high.ret largeHistory)⟩))
  | .right lowHistory =>
      match localTypeCoordinateDichotomy (data := spineData) lowHistory
          (by key_fresh) (by key_fresh) with
      | .right nonrepetitiveHistory =>
          let large :=
            (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              nonrepetitiveHistory (by key_fresh)
          exact Or.inl (selectedNetChargeContinuation
                ((routeEightNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inl ⟨lanePrefix.toPrefix, Or.inr (Or.inl (EntropyArmBlock_lowNonrepetitive.ret large))⟩))
      | .left repetitiveHistory =>
          let dominant :=
            (dominantRootedTypeRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              repetitiveHistory (by key_fresh)
          match dominantRootedTypeWedgeDichotomy (data := spineData) dominant
              (by key_fresh) (by key_fresh) with
          | .right wedgeFreeHistory =>
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeFreeHistory (by key_fresh)
              exact Or.inl (selectedNetChargeContinuation
                ((routeEightNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inl ⟨lanePrefix.toPrefix, Or.inr (Or.inr (Or.inl (EntropyArmBlock_lowRepetitiveWedgeFree.ret large)))⟩))
          | .left wedgeHistory =>
              let translated :=
                (independentObstructionTranslatesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeHistory (by key_fresh)
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  translated (by key_fresh)
              exact Or.inl (selectedNetChargeContinuation
                ((routeEightNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inl ⟨lanePrefix.toPrefix, Or.inr (Or.inr (Or.inr (EntropyArmBlock_lowRepetitiveWedge.ret large)))⟩))

set_option maxHeartbeats 8000000 in
/-- **Nodes `[47]`--`[56]`** on the full-rank arm `[34]`, `[161]` arm: `[56]` reads `[160]`'s deficiency cap `K .denseDeficiencyBelow` in place
of `[24]` (`lem:dense-deficiency-routing`); `[160]`'s second test left
`K .route8Rate` on this ledger.

`[47]`/`[48]`: `cor:forced-curvature-cost`; `[49]`/`[50]`: the per-vertex
remainder-entropy split; on the high arm `[52]`/`[53]` the joint account and the
entropy-cap test, closed at `[54]`; on the low arm the repetitive and root-wedge
splits of `lem:dominant-type`; every surviving arm is Residual C `[55]`.  On this dense residual `[53]`'s
bound arm is empty: the package of `[159]` overflows the skeleton budget, so
the entropy cap is active (`denseEntropyCapActiveRow`). -/
noncomputable def nearCubicLargeBudgetDenseRate
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint nearCubicResidualBKeys.{u} known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNearCubicSurvivorBoundary selected := by
  let cost :=
    (forcedCurvatureCostRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match remainderEntropyDichotomy (data := spineData) cost
      (by key_fresh) (by key_fresh) with
  | .left highHistory =>
      let package :=
        (entropyPackageRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          highHistory (by key_fresh)
      match entropyCapDichotomy (data := spineData) package
          (by key_fresh) (by key_fresh) with
      | .left activeHistory =>
          -- `[54]`: the exact decision on the joint realization inequality at G.
          match entropyJointRealizationDichotomy (data := spineData) activeHistory
              (by key_fresh) (by key_fresh) with
          | .left jointHistory =>
              exact ((entropyCapBoundRow (BranchState := BranchState)
                (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                (presentation := erdosReceiverLoadProfile)
                (data := spineData)).runAndCloseIncompatible jointHistory
                  (K .entropyCapActive) (K .entropyCapBound)
                  (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
          | .right residualHistory =>
              -- the configuration at G where the joint realization fails,
              -- with the stub-deficit identity and the cycle spectrum of `R₀`,
              -- returned.
              let residualHistory :=
                (stubDeficitRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run residualHistory (by key_fresh)
              exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr
                  (node54Return_unrealizedBothRates residualHistory))))))))
      | .right boundHistory =>
          -- `[53]`'s bound arm on the dense residual `[159]` with
          -- `τ(θ) < 1/4`: the package of `[159]` overflows the skeleton
          -- budget, so `[52]`'s demand makes the entropy cap active
          -- (`prop:entropy-high-theta`); Residual C `[55]` is not reached.
          exact (denseEntropyCapActiveRow.runAndCloseIncompatible boundHistory
            (K .entropyCapBound) (K .entropyCapActive)
            (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
  | .right lowHistory =>
      match localTypeCoordinateDichotomy (data := spineData) lowHistory
          (by key_fresh) (by key_fresh) with
      | .right nonrepetitiveHistory =>
          let large :=
            (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              nonrepetitiveHistory (by key_fresh)
          exact Or.inl (selectedNetChargeContinuation
                ((denseNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inr ⟨Route8LanePrefixBlock_unrealizedDenseBelow.ret large,
                  Or.inl (EntropyArmBlock_lowNonrepetitive.ret large)⟩))
      | .left repetitiveHistory =>
          let dominant :=
            (dominantRootedTypeRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              repetitiveHistory (by key_fresh)
          match dominantRootedTypeWedgeDichotomy (data := spineData) dominant
              (by key_fresh) (by key_fresh) with
          | .right wedgeFreeHistory =>
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeFreeHistory (by key_fresh)
              exact Or.inl (selectedNetChargeContinuation
                ((denseNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inr ⟨Route8LanePrefixBlock_unrealizedDenseBelow.ret large,
                  Or.inr (Or.inl (EntropyArmBlock_lowRepetitiveWedgeFree.ret large))⟩))
          | .left wedgeHistory =>
              let translated :=
                (independentObstructionTranslatesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeHistory (by key_fresh)
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  translated (by key_fresh)
              exact Or.inl (selectedNetChargeContinuation
                ((denseNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inr ⟨Route8LanePrefixBlock_unrealizedDenseBelow.ret large,
                  Or.inr (Or.inr (EntropyArmBlock_lowRepetitiveWedge.ret large))⟩))

set_option maxHeartbeats 8000000 in
/-- **Nodes `[47]`--`[56]`** on the full-rank arm `[34]`, `[24]` arm (bounded arm of `[153]`): `[56]` reads `[24]`'s density cap
`K .densityCap`.  The density cap does not decide the private-carrier rate
consumed at `[120]`--`[122]` (`Hypostructure.Fixtures.Route8RateDensityCapGap`),
so its exact test is taken at the entry of the route-8 continuation; a failed
rate is retained as the `[187]` outcome.

`[47]`/`[48]`: `cor:forced-curvature-cost`; `[49]`/`[50]`: the per-vertex
remainder-entropy split; on the high arm `[52]`/`[53]` the joint account and the
entropy-cap test, closed at `[54]`; on the low arm the repetitive and root-wedge
splits of `lem:dominant-type`; every surviving arm is Residual C `[55]`.

`lanePrefix` names the near-cubic route into the `[24]` arm; `[54]` is
returned as that route's subtype and the route-8 entry receives the route with
the entropy arm. -/
noncomputable def nearCubicLargeBudgetDensityCap
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (lanePrefix : DensityCapArm selected)
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint
      (K .route8Rate :: K .route8RateFails :: nearCubicResidualBKeys.{u}) known := by
        key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNearCubicSurvivorBoundary selected := by
  let cost :=
    (forcedCurvatureCostRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match remainderEntropyDichotomy (data := spineData) cost
      (by key_fresh) (by key_fresh) with
  | .left highHistory =>
      let package :=
        (entropyPackageRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          highHistory (by key_fresh)
      match entropyCapDichotomy (data := spineData) package
          (by key_fresh) (by key_fresh) with
      | .left activeHistory =>
          -- `[54]`: the exact decision on the joint realization inequality at G.
          match entropyJointRealizationDichotomy (data := spineData) activeHistory
              (by key_fresh) (by key_fresh) with
          | .left jointHistory =>
              exact ((entropyCapBoundRow (BranchState := BranchState)
                (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                (presentation := erdosReceiverLoadProfile)
                (data := spineData)).runAndCloseIncompatible jointHistory
                  (K .entropyCapActive) (K .entropyCapBound)
                  (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
          | .right residualHistory =>
              -- the configuration at G where the joint realization fails,
              -- with the stub-deficit identity and the cycle spectrum of `R₀`,
              -- returned.
              let residualHistory :=
                (stubDeficitRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run residualHistory (by key_fresh)
              exact Or.inr (Or.inr (Or.inr (Or.inr
                (node54SubtypesReturn_densityCap residualHistory lanePrefix))))
      | .right boundHistory =>
          -- `[55]`: Residual C on the high-entropy arm.
          let largeHistory :=
            (highEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              boundHistory (by key_fresh)
          exact nearCubicRouteEightEntry ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  largeHistory (by key_fresh))
                (⟨lanePrefix, Or.inl (EntropyArmBlock_high.ret largeHistory)⟩)
  | .right lowHistory =>
      match localTypeCoordinateDichotomy (data := spineData) lowHistory
          (by key_fresh) (by key_fresh) with
      | .right nonrepetitiveHistory =>
          let large :=
            (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              nonrepetitiveHistory (by key_fresh)
          exact nearCubicRouteEightEntry ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (⟨lanePrefix, Or.inr (Or.inl (EntropyArmBlock_lowNonrepetitive.ret large))⟩)
      | .left repetitiveHistory =>
          let dominant :=
            (dominantRootedTypeRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              repetitiveHistory (by key_fresh)
          match dominantRootedTypeWedgeDichotomy (data := spineData) dominant
              (by key_fresh) (by key_fresh) with
          | .right wedgeFreeHistory =>
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeFreeHistory (by key_fresh)
              exact nearCubicRouteEightEntry ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (⟨lanePrefix, Or.inr (Or.inr (Or.inl (EntropyArmBlock_lowRepetitiveWedgeFree.ret large)))⟩)
          | .left wedgeHistory =>
              let translated :=
                (independentObstructionTranslatesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeHistory (by key_fresh)
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  translated (by key_fresh)
              exact nearCubicRouteEightEntry ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (⟨lanePrefix, Or.inr (Or.inr (Or.inr (EntropyArmBlock_lowRepetitiveWedge.ret large)))⟩)

set_option maxHeartbeats 8000000 in
/-- **Nodes `[47]`--`[56]`** on the full-rank arm `[34]`, `[24]` arm of the `[162]` pass entered from `[160]`'s second complement:
`[56]` reads `[24]`'s density cap, and the ledger retains `[160]`'s failed
private-carrier rate `K .route8RateFails`, which the route-8 continuation would
consume at `[120]`--`[122]`; the retained failure is the `[187]` outcome.

`[47]`/`[48]`: `cor:forced-curvature-cost`; `[49]`/`[50]`: the per-vertex
remainder-entropy split; on the high arm `[52]`/`[53]` the joint account and the
entropy-cap test, closed at `[54]`; on the low arm the repetitive and root-wedge
splits of `lem:dominant-type`; every surviving arm is Residual C `[55]`.  On this dense residual `[53]`'s
bound arm is empty: the package of `[159]` overflows the skeleton budget, so
the entropy cap is active (`denseEntropyCapActiveRow`). -/
noncomputable def nearCubicLargeBudgetRateFailed
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .boundedDensityOrder) known]
    [FactKeys.Has (K .boundedOrderSmall) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .route8RateFails) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint nearCubicResidualBKeys.{u} known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNearCubicSurvivorBoundary selected := by
  let cost :=
    (forcedCurvatureCostRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match remainderEntropyDichotomy (data := spineData) cost
      (by key_fresh) (by key_fresh) with
  | .left highHistory =>
      let package :=
        (entropyPackageRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          highHistory (by key_fresh)
      match entropyCapDichotomy (data := spineData) package
          (by key_fresh) (by key_fresh) with
      | .left activeHistory =>
          -- `[54]`: the exact decision on the joint realization inequality at G.
          match entropyJointRealizationDichotomy (data := spineData) activeHistory
              (by key_fresh) (by key_fresh) with
          | .left jointHistory =>
              exact ((entropyCapBoundRow (BranchState := BranchState)
                (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                (presentation := erdosReceiverLoadProfile)
                (data := spineData)).runAndCloseIncompatible jointHistory
                  (K .entropyCapActive) (K .entropyCapBound)
                  (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
          | .right residualHistory =>
              -- the configuration at G where the joint realization fails,
              -- with the stub-deficit identity and the cycle spectrum of `R₀`,
              -- returned.
              let residualHistory :=
                (stubDeficitRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run residualHistory (by key_fresh)
              exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inl
                  (node54Return_unrealizedRateFailsBounded residualHistory))))))))
      | .right boundHistory =>
          -- `[53]`'s bound arm on the dense residual `[159]` with
          -- `τ(θ) < 1/4`: the package of `[159]` overflows the skeleton
          -- budget, so `[52]`'s demand makes the entropy cap active
          -- (`prop:entropy-high-theta`); Residual C `[55]` is not reached.
          exact (denseEntropyCapActiveRow.runAndCloseIncompatible boundHistory
            (K .entropyCapBound) (K .entropyCapActive)
            (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
  | .right lowHistory =>
      match localTypeCoordinateDichotomy (data := spineData) lowHistory
          (by key_fresh) (by key_fresh) with
      | .right nonrepetitiveHistory =>
          let large :=
            (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              nonrepetitiveHistory (by key_fresh)
          exact nearCubicRateFailedExit ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inl (EntropyArmBlock_lowNonrepetitive.ret large))
      | .left repetitiveHistory =>
          let dominant :=
            (dominantRootedTypeRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              repetitiveHistory (by key_fresh)
          match dominantRootedTypeWedgeDichotomy (data := spineData) dominant
              (by key_fresh) (by key_fresh) with
          | .right wedgeFreeHistory =>
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeFreeHistory (by key_fresh)
              exact nearCubicRateFailedExit ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inr (Or.inl (EntropyArmBlock_lowRepetitiveWedgeFree.ret large)))
          | .left wedgeHistory =>
              let translated :=
                (independentObstructionTranslatesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  wedgeHistory (by key_fresh)
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  translated (by key_fresh)
              exact nearCubicRateFailedExit ((netDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by key_fresh))
                (Or.inr (Or.inr (EntropyArmBlock_lowRepetitiveWedge.ret large)))

end HypostructureErdos64EG
