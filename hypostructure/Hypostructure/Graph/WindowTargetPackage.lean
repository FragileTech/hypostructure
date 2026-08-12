import Hypostructure.Graph.SeparatedPackageSkeleton
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.DeclaredCoordinateSignature

namespace Hypostructure.Graph

open Hypostructure

universe u

namespace FiniteObject

variable (object : FiniteObject.{u})

/-- A binary coordinate extracted from the certified multi-scale window
package.  Its label records the bit of the package and its declared support is
the packed-window support. -/
abbrev WindowTargetCoordinate (bits : Nat) :=
  DeclaredSignature.Coordinate object.Vertex (Fin bits)

noncomputable def windowTargetCoordinate {bits : Nat}
    (support : Finset object.Vertex) (bit : Fin bits) :
    object.WindowTargetCoordinate bits :=
  .base .windowLabel bit support

noncomputable def windowTargetFamily (bits : Nat)
    (support : Finset object.Vertex) :
    Finset (object.WindowTargetCoordinate bits) := by
  classical
  exact Finset.univ.image (object.windowTargetCoordinate support)

/-- The support projection carried by the finite object, with its canonical
decidable equality made explicit.  Keeping this projection in the package API
prevents downstream strategy rows from manufacturing typeclass plumbing. -/
noncomputable def windowTargetSupport {bits : Nat} :
    object.WindowTargetCoordinate bits → Finset object.Vertex := by
  letI := object.vertices.decEq
  exact DeclaredSignature.Coordinate.support

theorem card_windowTargetFamily (bits : Nat)
    (support : Finset object.Vertex) :
    (object.windowTargetFamily bits support).card = bits := by
  classical
  rw [windowTargetFamily, Finset.card_image_iff.mpr]
  · simp
  · intro left _ right _ equality
    simp only [windowTargetCoordinate,
      DeclaredSignature.Coordinate.base.injEq] at equality
    exact equality.2.1

/-- The declared family used by the mixed sparse-spine count: the selected
window coordinates and one labelled response coordinate for every free pair.
The sum tags make the union disjoint, exactly as the manuscript's labelled
copies clause (D8) requires. -/
abbrev MixedTargetCoordinate (bits : Nat) :=
  Sum (object.WindowTargetCoordinate bits) (PairCoordinate object)

noncomputable def mixedTargetFamily (bits : Nat)
    (windowSupport : Finset object.Vertex)
    (pairs : Finset (PairCoordinate object)) :
    Finset (object.MixedTargetCoordinate bits) := by
  classical
  exact (object.windowTargetFamily bits windowSupport).image Sum.inl ∪
    pairs.image Sum.inr

noncomputable def mixedTargetSupport {bits : Nat} :
    object.MixedTargetCoordinate bits → Finset object.Vertex := by
  letI := object.vertices.decEq
  exact Sum.elim object.windowTargetSupport
    DeclaredSignature.Coordinate.support

theorem card_mixedTargetFamily (bits : Nat)
    (windowSupport : Finset object.Vertex)
    (pairs : Finset (PairCoordinate object)) :
    (object.mixedTargetFamily bits windowSupport pairs).card =
      bits + pairs.card := by
  classical
  rw [mixedTargetFamily, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_iff.mpr Sum.inl_injective.injOn,
      object.card_windowTargetFamily,
      Finset.card_image_iff.mpr Sum.inr_injective.injOn]
  · exact Finset.disjoint_left.mpr fun value left right => by
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp left
      obtain ⟨_, _, equality⟩ := Finset.mem_image.mp right
      cases equality

/-- The complete mathematical object exported by the multi-scale window
package: its concrete packing, declared coordinates, exact support map, full
target rank, and realization in the object's exact edge stratum. -/
structure WindowTargetPackage
    (Baseline : FiniteObject.{u} → Prop) (LengthOK : Nat → Prop)
    (order : Nat) (packing : Finset (Finset object.Vertex)) (bits : Nat) : Prop where
  valid : object.IsWindowPacking order packing
  fullRank :
    Core.TargetRank.targetRank
        (object.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK)
          (object.windowTargetFamily bits (object.windowSupport packing))
          object.windowTargetSupport) = bits
  exactEntropy : 2 ^ bits ≤ skeletonBudget object
  /-- `lem:independent-target-entropy` for the package after adjoining any
  independently target-testable sparse pair family.  This is the positive arm
  selected at node `[21]`; failure belongs to that node's cold arm and is never
  turned into a downstream hypothesis. -/
  mixedEntropy : ∀ pairs : Finset (PairCoordinate object),
    Core.TargetRank.targetRank
        (object.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK)
          (object.mixedTargetFamily bits (object.windowSupport packing) pairs)
          object.mixedTargetSupport) =
      (object.mixedTargetFamily bits
        (object.windowSupport packing) pairs).card →
    2 ^ (bits + pairs.card) ≤ skeletonBudget object

end FiniteObject

end Hypostructure.Graph
