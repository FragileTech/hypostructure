import Hypostructure.Graph.NamedSurplusExits

/-!
# Fixture: clause (b) of the named sparse exits is residual-local

`def:named-surplus-exits` (b) is a target-defective identification
(`lem:context-universality`, tex 6106-6112) of two distinct declared
coordinates of G, each read on G's own piece at the canonical support of their
union.  A clause over an arbitrary coordinate type with a caller-chosen
attempted quotient and arbitrary boundaried pieces would hold on every graph
with a vertex (add a disjoint `K₄` to one piece); the clause below does not.

1. A family with at most one coordinate has no clause-(b) defect.
2. Two coordinates with the same (empty) declared support have the same
   reading on G's piece, so G's own surroundings do not separate them: that
   vacuity construction yields no clause-(b) defect, on any object.
3. Stated about G, clause (b) asks G's own surroundings `G − Z` to
   separate two readings of G; at a target-avoiding G it is empty
   (`not_residualTargetDefect_of_avoids`).
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
    _profile, separated⟩
  rw [constant first firstMem, constant second secondMem] at separated
  exact separated Iff.rfl

/-- (2) The vacuity construction's data -- the two-coordinate family
`ULift Bool` with empty declared supports, on any object -- gives no
clause-(b) exit. -/
example (Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u}) :
    ¬ ResidualTargetDefect Target object (Finset.univ : Finset (ULift.{0} Bool))
      (fun _ => ∅) :=
  not_residualTargetDefect_of_supports_eq Target object _ ∅ _
    (fun _ _ => rfl)

/-- (3) At a target-avoiding object, clause (b) is empty for every family. -/
example {LengthOK : Nat → Prop} (object : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {Coordinate : Type} (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) :
    ¬ ResidualTargetDefect (HasCycleWithLength LengthOK) object family
      coordinateSupport :=
  not_residualTargetDefect_of_avoids avoids family coordinateSupport

end Hypostructure.Fixtures.ResidualLocality
