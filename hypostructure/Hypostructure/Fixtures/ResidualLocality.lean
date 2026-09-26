import Hypostructure.Graph.NamedSurplusExits

/-!
# Fixture: clause (b) of the named sparse exits is residual-local

`def:named-surplus-exits` (b) is a target-defective identification
(`lem:context-universality`, tex 6106-6112) of two distinct declared
coordinates of G, each read on G's own piece at the canonical support of their
union.  The former clause accepted an arbitrary coordinate type with a
caller-chosen attempted quotient and arbitrary boundaried pieces; a disjoint
`K₄` added to one piece made it hold on every graph with a vertex.

1. A family with at most one coordinate has no clause-(b) defect.
2. The former vacuity construction used two coordinates with the same (empty)
   declared support.  Two coordinates with equal supports have the same
   reading on G's piece, so no context separates them: that construction no
   longer yields clause (b), on any object.
-/

namespace Hypostructure.Fixtures.ResidualLocality

open Hypostructure.Graph

universe u

/-- (1) At most one coordinate: no clause-(b) defect, on every object. -/
example (Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    {Coordinate : Type} (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (small : family.card ≤ 1) :
    ¬ ResidualTargetDefect Target object family coordinateSupport :=
  not_residualTargetDefect_of_card_le_one Target object family coordinateSupport
    small

/-- Coordinates with one common declared support are never separated: their
readings on G's piece coincide. -/
theorem not_residualTargetDefect_of_supports_eq
    (Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    {Coordinate : Type} (family : Finset Coordinate)
    (common : Finset object.Vertex)
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (constant : ∀ coordinate ∈ family, coordinateSupport coordinate = common) :
    ¬ ResidualTargetDefect Target object family coordinateSupport := by
  rintro ⟨first, firstMem, second, secondMem, _different, support, _selected,
    _profile, _actual, outside, separated⟩
  rw [constant first firstMem, constant second secondMem] at separated
  exact separated Iff.rfl

/-- (2) The former construction's data -- the two-coordinate family
`ULift Bool` with empty declared supports, on any object -- gives no
clause-(b) exit. -/
example (Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u}) :
    ¬ ResidualTargetDefect Target object (Finset.univ : Finset (ULift.{0} Bool))
      (fun _ => ∅) :=
  not_residualTargetDefect_of_supports_eq Target object _ ∅ _
    (fun _ _ => rfl)

end Hypostructure.Fixtures.ResidualLocality
