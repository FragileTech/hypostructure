import Hypostructure.Graph.Route8Residual

/-!
# The selected trace-incidence quotient

The selected trace basin carries the distinguished `traceIncidence` coordinate.
The current trace-response realization factors through `retainedBaseCoordinates`,
so erasing precisely that coordinate leaves the realized boundary piece
unchanged.  This file records the resulting literal response quotient.
-/

namespace Hypostructure.Graph.Route8.TraceBasin

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] Route8.vertexDecEq

/-- Erasing the distinguished trace-incidence coordinate from a selected trace
basin produces a nontrivial response quotient in the current declared response
algebra. -/
theorem exists_traceResponseQuotient_of_selected
    {support : Finset object.Vertex} {threshold : Nat}
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {basin : Finset object.Vertex}
    (selected : select? object support threshold receiver load = some basin)
    (distinct : load ≠ receiver) :
    ∃ retained,
      TraceResponseQuotient object support threshold LengthOK receiver load basin
        retained := by
  classical
  let coordinates :=
    PresentedEntry.traceCoordinates object support threshold receiver load
  let retained := coordinates.erase (.traceIncidence)
  have retainedBaseEq :
      PresentedEntry.retainedBaseCoordinates object support retained =
        PresentedEntry.retainedBaseCoordinates object support coordinates := by
    unfold PresentedEntry.retainedBaseCoordinates
    apply Finset.filter_congr
    intro coordinate _scheduled
    simp [retained]
  refine ⟨retained, ?_, ?_, ?_⟩
  · exact Finset.erase_subset _ _
  · refine ⟨.traceIncidence, ?_, ?_, ?_⟩
    · simp [PresentedEntry.traceCoordinates]
    · simp [retained]
    · refine Or.inl ⟨rfl, ?_⟩
      obtain ⟨trace, traceSelected, traceSubset⟩ :=
        (select?_traceComplete selected).2.1
      refine ⟨trace, traceSelected, ?_, traceSubset⟩
      have nonzero : trace.1.length ≠ 0 := by
        intro zero
        have endpoints : load = receiver := trace.1.eq_of_length_eq_zero zero
        exact distinct endpoints
      exact Nat.pos_of_ne_zero nonzero
  · refine ⟨?_, ?_⟩
    · exact congrArg BoundaryPiece.boundaryDegreeProfile
        (congrArg
          (PresentedEntry.retainedReading object support basin threshold LengthOK)
          retainedBaseEq)
    · intro outside
      rw [retainedBaseEq]

end Hypostructure.Graph.Route8.TraceBasin
