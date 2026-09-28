import Hypostructure.Graph.Strategy.SpineRows.AtomCompressionDichotomy
import Hypostructure.Graph.Strategy.SpineRows.BarrierEnumeration
import Hypostructure.Graph.Strategy.SpineRows.ContextValidityDichotomy
import Hypostructure.Graph.Strategy.SpineRows.DelocalizationScopeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.GlobalBarrier
import Hypostructure.Graph.Strategy.SpineRows.RepairIdentity
import Hypostructure.Graph.Strategy.SpineRows.WindowPackage
import Hypostructure.Graph.Strategy.BranchDClosure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FibrePressure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SparseSurplusExit
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SparseTargetDefectStructure
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
        K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
          K .admissibleQuotientsLabelInjective, K .replacementExclusion,
          K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
          K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .tightEndpoint,
        K .slackIndependent, K .singleBoundaryShape, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
          K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
          K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .cubicBaseline, K .packingOrderBound,
          K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
          K .admissibleQuotientsLabelInjective, K .replacementExclusion,
          K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
          K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .tightEndpoint,
        K .slackIndependent, K .singleBoundaryShape, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
          K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
          K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .cubicBaseline, K .packingOrderBound,
          K .noSuppressionChordViolation, K .specWitnessStructure, K .selection] :=
  let enumerated :=
    (barrierEnumerationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let separated :=
    (windowPackageRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      enumerated (by key_fresh)
  (skeletonDominatesRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    separated (by key_fresh)

/-! Node `[20]` and the post-`[21]` continuation are explicit branch
functions.  Their arguments and results are exact-ledger indices, so the
strict and near-cubic cursors cannot be accidentally exchanged. -/

/-- **The named sparse exit of `[20]`** (`def:named-surplus-exits`): the exit
arm of the enclosing sparse-exit classification routes the literal exit forms
to the attempted-quotient target-defect payload and its structure.  Written
once for the strict arm and the at-or-below arm. -/
noncomputable def selectedSparseTargetDefectExit
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .sparsePairExit) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    (fresh : List.Disjoint
      [K .sparseTargetDefectResidual, K .sparseTargetDefectStructure] known := by
        key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .sparseTargetDefectStructure :: K .sparseTargetDefectResidual :: known) :=
  let targetDefect :=
    (sparseSurplusExitRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  (sparseTargetDefectStructureRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    targetDefect (by key_fresh)

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
  partition, and coupled-excess decision (`coupledExcessDichotomy`:
  no → `[138]`; yes → `[139]`/`[141]` class tests → `[140]`/`[142]`/`[143]`
  audits → `[144]`). -/
-- EG-NODE [20] surplus-pair accounting branch
-- EG-NODE [131] free-pair entropy sandwich: \(|\Pi_{\rm free}|\le E_{\rm spine}+(\sigma/2+1)\log_2 n\)
-- EG-NODE [137] coupled excess \(D_{\rm all}>0\)?
-- EG-NODE [138] no coupled overload: explicit quadratic bound on \(\sigma\); near-cubic spine
-- EG-NODE [178] pair-code unrealized residual: conditional factorization gives a minimal connected pair overlap obstruction

end HypostructureErdos64EG
