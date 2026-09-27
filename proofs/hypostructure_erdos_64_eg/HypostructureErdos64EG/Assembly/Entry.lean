import Hypostructure.Graph.Strategy.SpineRows.ContractionCritical
import Hypostructure.Graph.Strategy.SpineRows.CubicBaseline
import Hypostructure.Graph.Strategy.SpineRows.CycleRankConstraint
import Hypostructure.Graph.Strategy.SpineRows.DeletionCriticality
import Hypostructure.Graph.Strategy.SpineRows.GadgetClosure
import Hypostructure.Graph.Strategy.SpineRows.InterfaceReplacement
import Hypostructure.Graph.Strategy.SpineRows.LocalAlgebra
import Hypostructure.Graph.Strategy.SpineRows.NoProperBaseline
import Hypostructure.Graph.Strategy.SpineRows.ObstructionPacking
import Hypostructure.Graph.Strategy.SpineRows.RelabelingDensityCap
import Hypostructure.Graph.Strategy.SpineRows.ReplacementExclusion
import Hypostructure.Graph.Strategy.SpineRows.ReturnAvoidance
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SparseSurplusExit
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SparseTargetDefectStructure
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Entry

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The entry prefix `[5]`--`[18]`, run on the selected exact ledger. -/
-- EG-NODE [5] target algebra: $R_e(G)\cap\Mers=\varnothing$ for every oriented edge
-- EG-NODE [6] Mersenne return exists?
-- EG-NODE [8] no proper subgraph with minimum degree $3$
-- EG-NODE [9] edge deletion critical; every edge touches a degree-$3$ vertex
-- EG-NODE [10] $V_{\ge4}(G)$ independent
-- EG-NODE [13] replacement lemma
-- EG-NODE [14] hereditary target-uncompressibility of proper supports
-- EG-NODE [15] $G$ is $P_{13}$-free?
-- EG-NODE [17] maximal disjoint induced-$P_{13}$ packing $\mathcal P$
-- EG-NODE [18] $P_{13}$ label algebra: $399$ labels; relations $C_s$; obstruction tensor $\Omega_2$
-- EG-NODE [7] power-of-two cycle
-- EG-NODE [16] HSS theorem gives target cycle
noncomputable def selectedEntryPrefix
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    ExactLedger EGInput.{u} selected
      [K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
        K .replacementExclusion,
        K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
        K .relabelingDensityCap,
        K .cubicBaseline, K .selection] := by
  let hCubic :=
    (cubicBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let hDensity :=
    (relabelingDensityCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hCubic (by
        key_fresh)
  let hGadget :=
    (gadgetClosureRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hDensity (by
        key_fresh)
  let hCritical :=
    (contractionCriticalRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hGadget (by
        key_fresh)
  -- `[6]`: Mersenne return exists?
  match returnAvoidanceDichotomy (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      hCritical (by
        key_fresh)
      (by
        key_fresh) with
  | .left mersenneHistory =>
      -- `[7]`: a Mersenne return is a power-of-two cycle.
      exact ((closeIncompatible mersenneHistory (K .selection) (K .mersenneReturn)
        (by key_fresh)).elimClosed
            (by infer_instance)).elim
  | .right h1 =>
      let h2 :=
        (noProperBaselineRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          h1 (by
            key_fresh)
      let h3 :=
        (deletionCriticalityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          h2 (by
            key_fresh)
      let hRank :=
        (cycleRankConstraintRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          h3 (by
            key_fresh)
      let h13 :=
        (replacementExclusionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run hRank (by
            key_fresh)
      let h4 :=
        (interfaceReplacementRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run h13 (by
            key_fresh)
      -- `[15]`: `G` is `P₁₃`-free?
      match windowFreeDichotomy (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)
          h4 (by
            key_fresh)
          (by
            key_fresh) with
      | .left freeHistory =>
          -- `[16]`: the HSS theorem gives a target cycle.
          exact ((closeIncompatible freeHistory (K .selection) (K .windowFree)
            (by key_fresh)).elimClosed (by infer_instance)).elim
      | .right h15 =>
          let h5 :=
            (obstructionPackingRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              h15 (by
                key_fresh)
          exact
            (localAlgebraRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              h5 (by
                key_fresh)

/-- Node `[19]`, run on the selected exact-ledger prefix. -/
-- EG-NODE [19] non-near-cubic surplus? $\sigma(G)>C_{\rm sp}\sqrt n$
noncomputable def selectedSurplusDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .surplusAbove)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .surplusAtOrBelow)
      (selectedEntryPrefix history) :=
  Decision.run (selectedEntryPrefix history) (K .surplusAbove) (K .surplusAtOrBelow)
    `HypostructureErdos64EG.selectedSurplusDichotomy
    (if above : spineData.{u}.surplusThreshold selected.object.vertexCount <
        selected.object.degreeSurplus spineData.{u}.threshold then
      .inl ⟨above⟩
    else
      .inr ⟨Nat.le_of_not_lt above⟩)

-- EG-NODE [4] choose lexicographically minimal counterexample
noncomputable def openSelectedCounterexample
    (input : EGInput) (avoids : ¬ Target input.object) :
    OpenedScope EGSelectionKey := by
  letI :
      FactSystem
        (Input BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData) :=
    instFactSystem
  exact openMinimalCounterexampleScope EGTarget
    (Graph.Strategy.Spine.refinedProgress BranchState
      Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile spineData.{u}.toParameters)
    (fun _ => ())
    EGSelectionKey
    (fun context =>
      ⟨by
        simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData,
          Core.Strategy.selectedInput]
          using context.avoids,
      { sizeMinimal := by
          intro smaller smallerLt baseline
          have refinedLt :
              (Graph.Strategy.Spine.refinedProgress BranchState
                Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
                spineData.{u}.toParameters).Smaller smaller context.G := by
            exact Graph.Strategy.Spine.refinedProgress_smaller_of_size_smaller
              BranchState Graph.ReceiverLoad.LoadCapacityProfile
              erdosReceiverLoadProfile spineData.{u}.toParameters smallerLt
          simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
            using context.minimal smaller refinedLt baseline
        refinedMinimal := by
          intro smaller smallerLt baseline
          simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
            using context.minimal smaller smallerLt baseline }⟩)
    input (by
      simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
        using avoids)

end HypostructureErdos64EG
