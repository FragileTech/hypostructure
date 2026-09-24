import Hypostructure.Graph.Strategy.SpineRows.AtomCompressionDichotomy
import Hypostructure.Graph.Strategy.SpineRows.BarrierEnumeration
import Hypostructure.Graph.Strategy.SpineRows.ContextValidityDichotomy
import Hypostructure.Graph.Strategy.SpineRows.DelocalizationScopeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.GlobalBarrier
import Hypostructure.Graph.Strategy.SpineRows.RepairIdentity
import Hypostructure.Graph.Strategy.SpineRows.WindowPackage
import Hypostructure.Graph.Strategy.BranchDClosure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Graph.Strategy.SurplusRows
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: NearCubic / Local

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-! The two node-[19] arms are separate exact-ledger cursors.  Node `[20]`
is the strict-surplus sibling; only the at-or-below sibling reaches node `[21]`.
Neither branch reads or publishes a fact owned by the other. -/

-- EG-NODE [21] finite enumeration: $c_\Omega$, $c_{13}$
noncomputable def selectedNearCubicNode21
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection] :=
  let enumerated :=
    (barrierEnumerationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff])
  let separated :=
    (windowPackageRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      enumerated (by simp [K_eq_iff])
  (skeletonDominatesRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    separated (by simp [K_eq_iff])

/-- Node `[21]`, `lem:p13-window-package` / `def:target-rank` /
`prop:p13-density`: "all target-complete window states are realized by labelled
near-cubic skeletons".  Per the methodology this is a decision on the literal
`[21]` residual: the yes arm carries the retention of the whole packing's package
in the canonical comparison (`K .windowPackageRealized`) and continues the
manuscript's chain unchanged; the no arm is the residual on which that sentence
fails, carried as a branch of its own (`K .windowPackageUnrealized`). -/
-- EG-NODE [158] joint window package realized in the labelled class?
noncomputable def selectedWindowPackageRealizationDichotomy
    {selected : EGInput.{u}}
    (dominated : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  Decision.run dominated (K .windowPackageRealized) (K .windowPackageUnrealized)
    `HypostructureErdos64EG.selectedWindowPackageRealizationDichotomy
    (by
      classical
      exact if realized : WindowPackageRealized spineData.{u} selected.object
          (canonicalWindowPacking spineData.{u} selected.object) then
        .inl ⟨realized⟩
      else
        .inr ⟨realized⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-! Node `[20]` and the post-`[21]` continuation are explicit branch
functions.  Their arguments and results are exact-ledger indices, so the
strict and near-cubic cursors cannot be accidentally exchanged. -/

/-- Node `[137]`, the manuscript's literal coupled-excess test on the
post-pressure residual.  The decision consumes every quantitative fact its two
arms use through `ExactLedger` and preserves the complete ancestry on either
result. -/
-- EG-NODE [137] coupled excess \(D_{\rm all}>0\)?
noncomputable def selectedCoupledExcessDichotomy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .surplusAbove) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) history :=
  coupledExcessDichotomy (data := spineData) history nearCubicFresh overloadFresh

/-! Node `[20]`, the strict (non-near-cubic) surplus branch, run node by node
along the Part X/XI diagram on the literal `K .surplusAbove` ledger:

* the enclosing `[20]` routing runs `sparseSurplusSurvivorDichotomy` for
  `def:named-surplus-exits`; the five named exits form the left arm, while
  their joint negation is exactly the incoming residual of routing-only
  `[125]`, "after P13 label algebra and sparse exits";
* `[126]`--`[128]` activation, `[129]` baseline spine demand, `[130]` canonical
  pair split;
* `[130]` yes: `[131]` decides the paper's full-pair code count on the exact
  `[129]` baseline witness and, on its realized arm, publishes both that count
  and the cleared free-pair entropy sandwich;
* `[130]` no: `[132]` blocked-pair routing — exit → `[133]` closes; blocker →
  `[134]` canonical pair ledger → `[135]` exact window-join pressure → `[136]`
  capacity-token ledger → `[137]` free-side count, exact role-fibre
  partition, and coupled-excess decision (`selectedCoupledExcessDichotomy`:
  no → `[138]`; yes → `[139]`/`[141]` class tests → `[140]`/`[142]`/`[143]`
  audits → `[144]`).

`selectedCoupledExcessDichotomy` is the next producer of this branch. -/
-- EG-NODE [20] surplus-pair accounting branch
-- EG-NODE [131] free-pair entropy sandwich: \(|\Pi_{\rm free}|\le E_{\rm spine}+(\sigma/2+1)\log_2 n\)
-- EG-NODE [137] coupled excess \(D_{\rm all}>0\)?
-- EG-NODE [138] no coupled overload: explicit quadratic bound on \(\sigma\); near-cubic spine
-- EG-NODE [178] pair-code unrealized residual: conditional factorization gives a minimal connected pair overlap obstruction

set_option maxHeartbeats 2000000 in
/-- **`lem:refined-minimality-swap`, node `[165]`, size-reducing case.**  A
neutral germ whose canonical representative `E` has strictly fewer internal
vertices than its corridor piece `Q`: exchanging `Q` for `E` inside the germ's
own completion yields a graph with fewer vertices, the same target status (the
germ is neutral, so `Q` and `E` are context-equivalent, and the completion is
`G` itself, which avoids the target), and the inherited baseline — a strictly
smaller counterexample, contradicting the selection's minimality. -/
-- EG-NODE [165] canonical replacement \(E\ne Q\): swap \(Q\to E\) gives a same-size counterexample
noncomputable def selectedCanonicalSwapCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldCanonicalSwapSmaller) known]
    [FactKeys.Has (K .selection) known] : False := by
  obtain ⟨germ, neutral, smaller⟩ := (history.get (K .coldCanonicalSwapSmaller)).down
  have selectedFacts := (history.get (K .selection)).down
  -- `G` is the germ's own completion, up to the decomposition's reconstruction.
  have reconstruction : (Graph.glue germ.piece germ.atom.outside).Isomorphic selected.object :=
    ⟨germ.atom.reconstructionIso⟩
  have baselineInvariant := Graph.minimumDegreeAtLeast_isomorphismInvariant spineData.{u}.threshold
  have targetInvariant := (Graph.cycleTargetInterface spineData.{u}.LengthOK).isomorphismInvariant
  have completionBaseline :
      Graph.MinimumDegreeAtLeast spineData.{u}.threshold (Graph.glue germ.piece germ.atom.outside) :=
    (baselineInvariant.iff_of_iso reconstruction).2 selected.baseline
  have completionAvoids :
      ¬ Graph.HasCycleWithLength spineData.{u}.LengthOK (Graph.glue germ.piece germ.atom.outside) :=
    fun hit => selectedFacts.1 ((targetInvariant.iff_of_iso reconstruction).1 hit)
  obtain ⟨vertexLt, swappedBaseline, swappedAvoids⟩ :=
    Graph.CanonicalPiece.swap_smaller_counterexample baselineInvariant targetInvariant
      germ.piece germ.atom.outside smaller completionBaseline completionAvoids
  have vertexEq : (Graph.glue germ.piece germ.atom.outside).vertexCount = selected.object.vertexCount :=
    Graph.FiniteObject.vertexCount_eq_of_isomorphic reconstruction
  exact swappedAvoids (selectedFacts.2 _
    (Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by rw [← vertexEq]; exact vertexLt))
    swappedBaseline)

/-- Branch D, nodes `[36]`--`[46]`, on the literal ledger returned by node
`[35]`.  The displayed state at `[35]` repeats `[33]` verbatim, while the
separate `separatedTestersRow` appends exactly `lem:separated-testers` without
altering that state.  This continuation begins with the context-validity
decision at `[36]`.  That test, with its target-defect terminal `[37]`,
the atom-compression test `[38]` with its terminal `[39]`, the delocalization
scope `[40]`/`[41]` with its proper-support terminal `[42]`, and the
whole-graph route `[43]`--`[45]` closed at `[46]`.  Every terminal is a
framework closure over the ledger of the arm against `K .selection`; the
freshness of the keys committed along the way is decided on the arm's exact
index at the call site. -/
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
-- EG-NODE [12] context-universality for target-complete identifications
noncomputable def selectedRankDropCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .branchDependence) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .selection) known]
    (defectFresh : K .contextDefect ∉ known)
    (universalFresh : K .contextUniversal ∉ known)
    (compressionFresh : K .atomCompression ∉ known)
    (delocalizedFresh : K .delocalizedSupport ∉ known)
    (properFresh : K .properDelocalization ∉ known)
    (globalFresh : K .globalDelocalization ∉ known)
    (repairFresh : K .repairIdentity ∉ known)
    (barrierFresh : K .globalBarrier ∉ known)
    (closureFresh : closed ∉ known) : False := by
  match contextValidityDichotomy (data := spineData) history defectFresh universalFresh with
  | .left defectHistory =>
      -- `[37]`: target-defective quotient — uninhabited (`lem:context-universality`).
      exact (closeImpossible defectHistory (K .contextDefect)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
  | .right universalHistory =>
      -- `[38]`: target-complete with a smaller proper representative?
      match atomCompressionDichotomy (data := spineData) universalHistory
          (by simp [K_eq_iff, compressionFresh]) (by simp [K_eq_iff, delocalizedFresh]) with
      | .left compressionHistory =>
          -- `[39]`: proper atom compression, forbidden by `cor:uncompressible`.
          exact (closeIncompatible compressionHistory (K .selection)
            (K .atomCompression) (by simp [K_eq_iff, closureFresh])).elimClosed
            (by infer_instance)
      | .right delocalizedHistory =>
          -- `[40]`/`[41]`: the enlarged connected support `Z ⊋ C`; is `Z ⊊ G`?
          match delocalizationScopeDichotomy (data := spineData) delocalizedHistory
              (by simp [K_eq_iff, properFresh]) (by simp [K_eq_iff, globalFresh]) with
          | .left properHistory =>
              -- `[42]`: proper-support smearing closure (`lem:proper-smearing`).
              exact (closeIncompatible properHistory (K .selection)
                (K .properDelocalization) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)
          | .right globalHistory =>
              -- `[43]`--`[45]`: whole-graph delocalization, the `1`--`3` repair
              -- identity, and the target/replacement/global-profile barrier.
              let repaired :=
                (repairIdentityRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  globalHistory (by simp [K_eq_iff, repairFresh])
              let barrier :=
                (globalBarrierRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  repaired (by simp [K_eq_iff, barrierFresh])
              -- `[46]`: rank-drop branch closed (`lem:no-silent-global-smearing`).
              exact (closeIncompatible barrier (K .selection) (K .globalBarrier)
                (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)

end HypostructureErdos64EG
