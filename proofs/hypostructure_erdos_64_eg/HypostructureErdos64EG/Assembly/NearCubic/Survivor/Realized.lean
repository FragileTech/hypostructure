import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGerm
import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.MarkedGerm
import Hypostructure.Graph.Strategy.ColdCorridorRows.NeutralTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.TwoStrand
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.DensityOrder
import Hypostructure.Graph.Strategy.SpineRows.Route8RateFromColdBelow
import HypostructureErdos64EG.Assembly.NearCubic.ColdPass
import HypostructureErdos64EG.Assembly.NearCubic.Spine

/-!
# Assembly: NearCubic / Survivor / Realized

The yes-arm of `[158]`: the hot/cold split `[22]` and the cold branch
`[145]`--`[157]` of Part XI on the realized-package residual.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 200000 in
set_option synthInstance.maxHeartbeats 4000000 in
/-- **The realized-package arm of `[158]`.**  `[22]`--`[23]`, then `[146]`
(`θ < 1/78`).  Its yes arm `[147]`: the route-8 private-carrier inequality
`τ(θ) < 3/13` is `K .coldRoute8Below` read through `|∂R| ≤ 15p + σ_W`
(`route8RateFromColdBelowRow`); the arm runs the spine's route-8 closure
`[25]`--`[124]` with that inequality in place of `[24]`.  Its no arm runs
`[148]`--`[152]` and decides `[153]`: the bounded arm returns through `[24]`
(`densityBudgetRow`, `prop:p13-density` after closure) to `[25]`; the linear arm
extracts the configuration family and decides `[154]`.  G1 closes at `[155]`;
G2 `[156]` and the silent arm `[157]` publish the local cold-terminal exclusion
of `thm:cold-branch-quantitative-closure`, retained at `[187]`. -/
-- EG-NODE [146] \(\theta<1/78\)?
-- EG-NODE [147] route-8 private-incidence collision closes
-- EG-NODE [24] bounded cold-mass return from [153]: $\theta\le\theta_{\rm win}+o(1)$; high entropy: $\theta\le0.01198542083\ldots$
noncomputable def Assembly.Internal.nearCubicRealized
    {selected : EGInput.{u}}
    (enumerated : ExactLedger EGInput.{u} selected
      [K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
         K .admissibleQuotientsLabelInjective, K .replacementExclusion,
         K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
         K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .portEndDegree, K .hubLinkStructure, K .hubClassCounts, K .slotRelation, K .closedClasses, K .hubTwoHopLinks, K .slotLinear, K .hubWindowBudget, K .windowHubBounds, K .cubicNeighbourSupply, K .hubCountBound, K .lowEdgeParity, K .bigHubBound, K .bigHubVShapes, K .highSurplusBound, K .hubLengthThreePairs, K .tightEndpoint,
       K .slackIndependent, K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .densityExcess, K .remainderSlack, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
         K .primitiveCarrierCount, K .remainderPathBounds, K .windowFreeGeometry, K .inducedPathAttachment, K .windowPositionStubs, K .windowAttachmentGap, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
         K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .threeRouteFan, K .threeRouteChain, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
         K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let cap := nearCubicHotColdCap enumerated
  match coldRoute8Dichotomy (data := spineData) cap
      (by key_fresh) (by key_fresh) with
  | .left belowHistory =>
      let rated :=
        (route8RateFromColdBelowRow (BranchState := BranchState)
            (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
            (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          belowHistory (by key_fresh)
      -- `[149]`--`[152]` are facts of G on this arm too: the cold facts are
      -- published from `[22]`'s cap before the spine, so every arm of `[146]`
      -- carries them.
      let stubbed := nearCubicColdStubFacts rated
      exact nearCubicLargeBudgetColdRate (nearCubicFullRank stubbed)
        (Route8LanePrefixBlock_realizedColdBelow.ret stubbed)
  | .right atOrAboveHistory =>
      -- `[146]` no with `[158]` yes: the realized package's entropy count
      -- (`θ ≤ θ_win + o(1)`) against `θ ≥ 1/78`, combined at G; the exact size
      -- test closes `N₀ ≤ n` and retains `n < N₀`.
      let ordered :=
        (realizedDensityOrderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          atOrAboveHistory (by key_fresh)
      match realizedOrderDichotomy (data := spineData) ordered
          (by key_fresh) (by key_fresh) with
      | .left largeHistory =>
          exact ((closeIncompatible largeHistory (K .realizedDensityOrder)
            (K .realizedOrderLarge) (by key_fresh)).elimClosed
              (by infer_instance)).elim
      | .right smallHistory =>
          let stubs := nearCubicColdStubs smallHistory
          match coldMassDichotomy (data := spineData) stubs
              (by key_fresh) (by key_fresh) with
          | .right boundedHistory =>
              let density :=
                (densityBudgetRow (data := spineData)).run boundedHistory
                  (by key_fresh)
              exact nearCubicLargeBudgetDensityCap (nearCubicFullRank density)
                (Or.inl (Route8LanePrefixBlock_realizedColdAtOrAbove.ret density))
          | .left linearHistory =>
              -- `[25]`--`[34]` and `[48]` are facts of G on the linear arm too:
              -- the remainder normalization, the external-incidence and wedge
              -- supply, the obstruction rank (its rank-drop arm is Branch D, closed)
              -- and the forced curvature cost.
              let spine := nearCubicFullRank linearHistory
              let cost :=
                (forcedCurvatureCostRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  spine (by key_fresh)
              -- `[58]`'s net-charge localization is a fact of G here too.
              let localized :=
                (netChargeLocalizationRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  cost (by key_fresh)
              -- `lem:bridgeless` is on the ledger since the entry prefix.
              -- `[153]`: the first failures.  No consumer on this arm reads (★)
              -- (`[162]` runs on the dense arms), so it is not split; a repeat is
              -- the (F5) repeat subcase and is a germ of the family like any
              -- other, which the routing below reads.
              let occurred :=
                (coldFirstFailureOccurrenceRow (data := spineData)).run
                  (nearCubicColdCorridorState localized) (by key_fresh)
              let familyOnly := nearCubicColdGermFamily occurred
              -- `[175]`'s per-half-edge split and `[177]`'s fan data are facts
              -- of G on the extracted family here too.
              let split :=
                (absorbedGermSplitRow (data := spineData)).run familyOnly
                  (by key_fresh)
              let family :=
                (absorbedGermFanDataRow (data := spineData)).run split
                  (by key_fresh)
              let unhit := nearCubicColdNoHit family
              -- `[154]` second test (G2) is decided at G: its yes-arm is
              -- empty (Lean improvement), closed against the selection.
              match coldGermDistinctionDichotomy (data := spineData) unhit
                  (by key_fresh) (by key_fresh) with
              | .left distinguishedHistory =>
                  exact ((closeIncompatible distinguishedHistory
                    (K .coldGermSomeDistinguishing) (K .selection)
                    (by key_fresh)).elimClosed (by infer_instance)).elim
              | .right silentHistory =>
                  -- `[157]`, silent arm: G's silent extracted family has a
                  -- neutral equal-length configuration (`[163]`, read as at
                  -- `[176]`: no dense terminality on this arm).  Its genuine
                  -- second strand is closed at `[167]`--`[168]`; the
                  -- canonical-replacement arm `[165]`--`[166]` forces `Q = E`
                  -- and is retained.
                  let neutral :=
                    (absorbedNeutralConfigurationRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      silentHistory (by key_fresh)
                  let closed := nearCubicColdTable neutral
                  match absorbedNeutralSymmetryDichotomy (data := spineData) closed
                      (by key_fresh) (by key_fresh) with
                  | .left canonicalHistory =>
                      let swapped :=
                        (canonicalReplacementSwapRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                          canonicalHistory (by key_fresh)
                      let trivial :=
                        (canonicalReplacementTrivialRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                          swapped (by key_fresh)
                      -- `[169]`, `def:blocked-class`: on the trivial neutral
                      -- residual G lies in the blocked class `B(P)` of the fixed
                      -- packing, `card B(P) <= skeletonBudget`.  (On `[158]` yes
                      -- its compression cap is `windowPackageRealized` itself:
                      -- `blockedCompressionCap_iff_windowPackageRealized`.)
                      -- `[157]`: the marked germ against the table's compression
                      -- clause: not handed off, replacement not strictly smaller.
                      let uncompressed : ExactLedger EGInput.{u} selected _ :=
                        (coldMarkedGermUncompressedRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                          trivial (by key_fresh)
                      let excised : ExactLedger EGInput.{u} selected _ :=
                        (coldMarkedGermStretchExcisionRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run uncompressed (by key_fresh)
                      exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
                        (coldBranchClosed_linearRealizedSilentReturn excised)))))
                  | .right genuineHistory =>
                      let survivor :=
                        (twoStrandSurvivorRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).run genuineHistory
                          (by key_fresh)
                      let stubbed :=
                        (coldWindowStubStructureRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).run survivor
                          (by key_fresh)
                      exact ((symmetricPairEndpointExclusionRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) (data := spineData)).runAndCloseIncompatible stubbed
                          (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded)
                          (by key_fresh) (by key_fresh)).elimClosed
                            (by infer_instance) |>.elim

end HypostructureErdos64EG
