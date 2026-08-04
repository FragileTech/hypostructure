import Hypostructure.Core.Strategy.ObstructionPackingClosure
import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.Strategy.InducedPathPresentation

/-!
# Graph adapter for obstruction packing

This file supplies only the graph meaning of the generic Core strategy:
induced-path occurrences and overlap of their vertex supports.  It performs no
search, packing selection, routing, ledger update, or target certification.
-/

namespace Hypostructure.Graph.Strategy.ObstructionPackingClosure

open Hypostructure

universe uInput uVertex

/-- Derive Core obstruction-packing semantics from graph values already
available through typed residual queries.  The path order is queried from the
same residual and is never a strategy constant. -/
noncomputable def inducedPathSemantics
    {Input : Type uInput} (Target : Input → Prop)
    (object : Core.Residual.Query Input fun _ => FiniteObject.{uVertex})
    (order : Core.Residual.Query Input fun _ => Nat)
    (freeForcesTarget : ∀ input,
      InducedPathFree (object.read input) (order.read input) → Target input) :
    Core.Strategy.ObstructionPackingClosure.Semantics
      Input Target where
  Occurrence := fun input =>
    InducedPathMaximalPacking.Window
      (object.read input) (order.read input)
  occurrences := fun input =>
    InducedPathMaximalPacking.windowSchedule
      (object.read input) (order.read input)
  conflict := fun input left right =>
    ¬ Disjoint
      (InducedPathMaximalPacking.support
        (object.read input) (order.read input) left)
      (InducedPathMaximalPacking.support
        (object.read input) (order.read input) right)
  conflictDecidable := fun _ => Classical.decRel _
  conflictSymmetric := by
    intro input left right overlaps disjoint
    exact overlaps disjoint.symm
  freeForcesTarget := by
    intro input empty
    apply freeForcesTarget input
    rintro ⟨embedding⟩
    have member :
        embedding ∈
          (InducedPathMaximalPacking.windowSchedule
            (object.read input) (order.read input)).values := by
      simp [InducedPathMaximalPacking.windowSchedule]
    rw [empty] at member
    simp at member

/-- Core obstruction-packing semantics projected from the single closed
induced-path Graph presentation. -/
noncomputable def inducedPathSemanticsOfPresentation
    {Input : Type uInput} {Target : Input → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target) :
    Core.Strategy.ObstructionPackingClosure.Semantics.{
      uInput, max uInput uVertex} Input Target where
  Occurrence := fun input =>
    ULift.{uInput}
      (InducedPathMaximalPacking.Window
        (presentation.object.read input) (presentation.order.read input))
  occurrences := fun input =>
    (InducedPathMaximalPacking.windowSchedule
      (presentation.object.read input) (presentation.order.read input)).map
        ULift.up ULift.up_injective (Classical.decEq _)
  conflict := fun input left right =>
    ¬ Disjoint
      (InducedPathMaximalPacking.support
        (presentation.object.read input) (presentation.order.read input)
        left.down)
      (InducedPathMaximalPacking.support
        (presentation.object.read input) (presentation.order.read input)
        right.down)
  conflictDecidable := fun _ => Classical.decRel _
  conflictSymmetric := by
    intro input left right overlaps disjoint
    exact overlaps disjoint.symm
  freeForcesTarget := by
    intro input empty
    apply presentation.freeForcesTarget input
    rintro ⟨window⟩
    have member :
        ULift.up window ∈
          ((InducedPathMaximalPacking.windowSchedule
            (presentation.object.read input)
            (presentation.order.read input)).map
              ULift.up ULift.up_injective (Classical.decEq _)).values := by
      apply (Core.Finite.Enumeration.mem_map_values
        (InducedPathMaximalPacking.windowSchedule
          (presentation.object.read input)
          (presentation.order.read input))
        ULift.up ULift.up_injective (Classical.decEq _)
        (ULift.up window)).mpr
      exact ⟨window, by
        simp [InducedPathMaximalPacking.windowSchedule], rfl⟩
    rw [empty] at member
    simp at member

/-- Framework-owned typed identification of every registered occurrence with
the literal induced-path window from the same presentation. -/
def inducedPathOccurrenceEquiv
    {Input : Type uInput} {Target : Input → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target)
    (input : Input) :
    (inducedPathSemanticsOfPresentation presentation).Occurrence input ≃
      InducedPathMaximalPacking.Window
        (presentation.object.read input) (presentation.order.read input) :=
  Equiv.ulift

/-- Every literal induced-path window has the canonical lifted occurrence in
the packing projection of the shared presentation. -/
theorem inducedPathOccurrence_mem
    {Input : Type uInput} {Target : Input → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target)
    (input : Input)
    (window : InducedPathMaximalPacking.Window
      (presentation.object.read input) (presentation.order.read input)) :
    ULift.up window ∈
      ((inducedPathSemanticsOfPresentation presentation).occurrences
        input).values := by
  apply (Core.Finite.Enumeration.mem_map_values
    (InducedPathMaximalPacking.windowSchedule
      (presentation.object.read input) (presentation.order.read input))
    ULift.up ULift.up_injective (Classical.decEq _) (ULift.up window)).mpr
  exact ⟨window, by
    simp [InducedPathMaximalPacking.windowSchedule], rfl⟩

/-- Interpret the exact compiler-owned Core packing as the standard graph
induced-path profile.  This is a proof-preserving projection: the selected
list, compatibility, and maximality all come from the same packing ledger
entry, and no graph-side maximal selection is rerun. -/
noncomputable def inducedPathProfileOfPacking
    {Input : Type uInput} {Target : Input → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target)
    (input : Input)
    (packing : Core.Strategy.ObstructionPackingClosure.Packing
      ((inducedPathSemanticsOfPresentation presentation).occurrences input)
      ((inducedPathSemanticsOfPresentation presentation).conflict input)) :
    InducedPathMaximalPacking.Profile
      (presentation.object.read input) (presentation.order.read input) := by
  classical
  exact {
    selected := packing.selected.map ULift.down
    selected_nodup := packing.selected_nodup.map (by
      intro left right equal
      cases left
      cases right
      cases equal
      rfl)
    pairwiseDisjoint := by
      intro left leftMem right rightMem different
      rcases List.mem_map.mp leftMem with ⟨liftedLeft, liftedLeftMem, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨liftedRight, liftedRightMem, rfl⟩
      have liftedDifferent : liftedLeft ≠ liftedRight := by
        intro equal
        exact different (congrArg ULift.down equal)
      exact not_not.mp
        (packing.pairwiseCompatible liftedLeftMem liftedRightMem
          liftedDifferent)
    saturated := by
      intro window
      obtain ⟨selected, selectedMem, overlapOrEqual⟩ :=
        packing.maximal (ULift.up window)
          (inducedPathOccurrence_mem presentation input window)
      refine ⟨selected.down, List.mem_map.mpr
        ⟨selected, selectedMem, rfl⟩, ?_⟩
      rcases overlapOrEqual with overlap | equal
      · exact Or.inl overlap
      · exact Or.inr (congrArg ULift.down equal) }

/-- Nonemptiness of the Core packing is preserved by the graph projection.
The proof is tied to the exact selected list; Graph neither reselects a
window nor accepts a separate witness. -/
theorem inducedPathProfileOfPacking_selected_nonempty
    {Input : Type uInput} {Target : Input → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target)
    (input : Input)
    (packing : Core.Strategy.ObstructionPackingClosure.Packing
      ((inducedPathSemanticsOfPresentation presentation).occurrences input)
      ((inducedPathSemanticsOfPresentation presentation).conflict input))
    (selected_nonempty : packing.selected ≠ []) :
    (inducedPathProfileOfPacking presentation input packing).selected ≠ [] := by
  change packing.selected.map ULift.down ≠ []
  intro mapped_empty
  exact selected_nonempty (List.map_eq_nil_iff.mp mapped_empty)

/-- Residual-query form of `inducedPathProfileOfPacking`.  Downstream graph
Strategies consume the exact earlier packing through `Query.map`; they never
rebuild or reselect it. -/
noncomputable def inducedPathProfileQueryAt
    {Input : Type uInput} {Target : Input → Prop}
    {Previous : Type (max uInput uVertex)}
    [Core.Residual.HasResidual Previous Input]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target)
    (current : Core.Residual.Query Previous fun _ => Input)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathSemanticsOfPresentation presentation).occurrences
          (current.read previous))
        ((inducedPathSemanticsOfPresentation presentation).conflict
          (current.read previous))) :
    Core.Residual.Query Previous fun previous =>
      InducedPathMaximalPacking.Profile
        (presentation.object.read (current.read previous))
        (presentation.order.read (current.read previous)) :=
  packing.dependentMap fun previous exactPacking =>
    inducedPathProfileOfPacking presentation
      (current.read previous) exactPacking

noncomputable def inducedPathProfileQuery
    {Input : Type uInput} {Target : Input → Prop}
    {Previous : Type (max uInput uVertex)}
    [Core.Residual.HasResidual Previous Input]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uInput, uVertex} Input Target)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathSemanticsOfPresentation presentation).occurrences
          (Core.Residual.residualOf previous))
        ((inducedPathSemanticsOfPresentation presentation).conflict
          (Core.Residual.residualOf previous))) :
    Core.Residual.Query Previous fun previous =>
      InducedPathMaximalPacking.Profile
        (presentation.object.read (Core.Residual.residualOf previous))
        (presentation.order.read (Core.Residual.residualOf previous)) :=
  inducedPathProfileQueryAt presentation Core.Residual.Query.residual packing

end Hypostructure.Graph.Strategy.ObstructionPackingClosure
