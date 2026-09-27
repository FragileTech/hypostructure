import Hypostructure.Graph.Contracts.TypeA.Exits
import Hypostructure.Graph.Statements.RouteEight

/-!
# Quarantined: the silent Type A lane closure at node `[184]`

Reference only; no live module imports this file (`quarantine.txt`).

Before the final fix pass the Lean split node `[109]` by the node-`[94]`
silent-excess provenance of the route-`8` residual state (keys
`typeASilentExitSevenFree` / `typeAExitEightNotSilent`, a diamond the paper does
not have) and closed the silent lane at node `[184]` with the argument below:
the lane's selected excess load is a unified entry, and
`lem:typeA-unified-visible-ownership` makes every unified entry visible.  The
paper sends node `[109]` to node `[110]` on every lane and reaches the open leaf
`[186]`; the extra split and closure were removed.  The lemma is kept verbatim
(it no longer elaborates: its input statement `SelectedSilentExitSevenFree`
was deleted with the split, and node `[107]`'s exit `(7)` is now asked at the
terminal state rather than of the whole piece).
-/

namespace Hypostructure.Graph.Contracts.TypeA

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- The node-`[94]` silent-excess origin of a route-`8` residual state is
incompatible with `lem:typeA-unified-visible-ownership`: its selected excess
load is a member of the unified entry family, which is all visible, while the
origin makes it silent. -/
theorem selectedSilentExitSevenFree_unifiedVisibleResidual_contradiction
    (silent : SelectedSilentExitSevenFree data object)
    (visible : Route8UnifiedVisibleResidualStatement data object) : False := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨piece, pinned, receiver, chosen, zero, _state, noHandoff, origin⟩ :=
    silent
  have isReceiver := (canonicalExitReceiverAt_spec_of_eq_some chosen).1
  obtain ⟨component, eq, rfl⟩ := (canonicalNegativePiece_eq_some_iff).mp pinned
  obtain ⟨present, negative⟩ := canonicalNegativeComponent_spec_of_eq_some eq
  obtain ⟨_noVisibleFour, originalSaturated, silentAtOrigin, _count⟩ := origin
  obtain ⟨_portBound, nonemptyExcess, silentSubset⟩ := silentAtOrigin
  obtain ⟨load, loadExcess⟩ := nonemptyExcess
  have componentUnified : component ∈ route8UnifiedComponents data object := by
    unfold route8UnifiedComponents
    dsimp only
    exact Finset.mem_filter.mpr ⟨present, zero, negative, noHandoff⟩
  have receiverUnified : receiver ∈
      Graph.VisibleEntry.saturatedReceivers object
        (object.pieceSupport (canonicalRemainder data object) component)
        data.threshold data.dischargeScale := by
    unfold Graph.VisibleEntry.saturatedReceivers
    exact Finset.mem_filter.mpr ⟨object.mem_receivers.mpr isReceiver,
      originalSaturated⟩
  have loadBasin : load ∈
      Graph.VisibleEntry.excessBasin object
        (object.pieceSupport (canonicalRemainder data object) component)
        data.threshold data.dischargeScale receiver :=
    Graph.ExitFour.unpeeledExcess_subset_excessBasin _ data.threshold
      data.dischargeScale receiver ∅ loadExcess
  have entryMem :
      (object.pieceSupport (canonicalRemainder data object) component, receiver,
        load) ∈ route8UnifiedEntries data object := by
    unfold route8UnifiedEntries Graph.Route8Census.entriesOfComponents
    apply Finset.mem_biUnion.mpr
    refine ⟨component, componentUnified, ?_⟩
    dsimp only
    apply Finset.mem_biUnion.mpr
    refine ⟨receiver, receiverUnified, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨load, loadBasin, rfl⟩
  have isVisible := visible.1 _ entryMem
  have notVisible := (Finset.mem_sdiff.mp (silentSubset loadExcess)).2
  exact notVisible isVisible

end Hypostructure.Graph.Contracts.TypeA
