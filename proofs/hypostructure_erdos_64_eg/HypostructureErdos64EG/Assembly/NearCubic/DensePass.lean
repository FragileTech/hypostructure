import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.DenseTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.NeutralTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.TwoStrand
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.ColdPass
import HypostructureErdos64EG.Assembly.NearCubic.Replacement

/-!
# Assembly: NearCubic / DensePass

The linear arm of `[153]` inside the dense hot/cold pass `[162]`
(`lem:dense-cold-pass`), written once for both dense arms that run the pass.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Every key committed on the linear arm of the dense pass. -/
noncomputable abbrev denseLinearKeys : FactKeys EGInput.{u} :=
  [K .remainderNormalized, K .bridgeless,
    K .coldReturnCorridors, K .coldCorridorState,
    K .denseColdCorridorsTerminal, K .coldFirstFailureOccurrence,
    K .coldFailureCycle, K .coldFailureDefectRoute,
    K .coldFailureCompression, K .coldHandoffTransfer,
    K .coldFailureRouting, K .coldExchangeBound,
    K .coldGermCandidates, K .coldGermFamilyPositive, K .coldGermSomeRealizing,
    K .coldGermNoneRealizing, K .coldGermSomeDistinguishing,
    K .coldGermNoneDistinguishing, K .coldGermRealized, K .coldGermDistinguished,
    K .coldGermSilent, K .coldGermRouted, K .coldSameInterfaceTable,
    K .coldBranchClosed, K .coldNeutralEqualLengthTerminal,
    K .coldCanonicalNeutralConfiguration, K .coldGenuineSecondStrand,
    K .coldCanonicalReplacementSwap, K .coldCanonicalReplacementTrivial,
    K .blockedClassMember, K .blockedScaleAdditive, K .blockedBarrierOverlap,
    K .blockedCompressionBound, K .blockedCompressionCap,
    K .coldTwoStrandSurvivor, K .coldWindowStubStructure,
    K .coldSymmetricPairExcluded, closed]

/-- **The linear arm of `[153]` in the dense pass `[162]`**
(`lem:dense-cold-pass`).  The pass reads the remainder `R` (`[25]`'s
normalization) because every return corridor of the dense residual is terminal:
the boundaried pieces of `R` are induced-`P₁₃`-free and subcubic, hence of
bounded diameter.  The first failures, the extracted family and `[154]` run as
on the spine; G1 closes at `[155]`.  G2 is the `[156]` outcome.  On the silent
arm `[157]` the only outcome not refuted by a ledger fact is the neutral
equal-length terminal configuration `[163]`, a symmetry
(`lem:neutral-germ-symmetry`): its canonical-replacement arm `[165]`--`[166]`
enters the blocked class `[169]`, and its genuine symmetric strand pair
`[167]`/`[168]` closes against the window stub structure. -/
-- EG-NODE [162] dense hot/cold pass: run [22]--[24] and [145]--[157] on the dense residual; [23], [149], [155], [156], [157] close as before; bounded arm of [153] and [146]/[160] arms return to [25]
-- EG-NODE [163] neutral equal-length terminal configuration: second strand graph-realized?
-- EG-NODE [165] canonical replacement \(E\ne Q\): swap \(Q\to E\) gives a same-size counterexample
-- EG-NODE [167] symmetric strand pair: finite two-strand check on the closing lengths \(2\ell\), \(\ell+d\)
-- EG-NODE [168] surviving pair attaches only at endpoints: not a selected interior half-edge
noncomputable def nearCubicDenseLinear
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .spinePresentationLaws) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (fresh : List.Disjoint denseLinearKeys.{u} known := by key_fresh) :
    SelectedNearCubicSurvivorBoundary selected := by
  let normalized :=
    (remainderNormalizationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      normalized (by key_fresh)
  let state := nearCubicColdCorridorState bridgeless
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state (by key_fresh)
  let family := nearCubicColdGermFamily terminal
  let unhit := nearCubicColdNoHit family
  match coldGermDistinctionDichotomy (data := spineData) unhit
      (by key_fresh) (by key_fresh) with
  | .left distinguishedHistory =>
      exact Or.inr (Or.inr (Or.inr
        ((nearCubicColdTable distinguishedHistory).get (K .coldBranchClosed)).down))
  | .right silentHistory =>
      let neutralConfiguration :=
        (neutralEqualLengthTerminalRow (data := spineData)).run silentHistory
          (by key_fresh)
      let closed := nearCubicColdTable neutralConfiguration
      match neutralGermSymmetryDichotomy (data := spineData) closed
          (by key_fresh) (by key_fresh) with
      | .left canonicalHistory =>
          let swapped :=
            (canonicalReplacementSwapRow (data := spineData)).run
              canonicalHistory (by key_fresh)
          exact Or.inr (Or.inr (Or.inl
            (selectedCanonicalReplacementContinuation swapped)))
      | .right genuineHistory =>
          let survivor :=
            (twoStrandSurvivorRow (data := spineData)).run genuineHistory
              (by key_fresh)
          let stubbed :=
            (coldWindowStubStructureRow (data := spineData)).run survivor
              (by key_fresh)
          exact ((symmetricPairEndpointExclusionRow
            (data := spineData)).runAndCloseIncompatible stubbed
              (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded)
              (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim

end HypostructureErdos64EG
