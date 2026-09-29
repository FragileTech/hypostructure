import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort
import Hypostructure.Graph.Finite

/-!
# The lexicographically least family of vertex sets, in G's vertex order

The manuscript fixes "the lexicographically first" family (a maximum window
packing, a maximal retained hot subfamily) "in the fixed vertex order".  The
order is the object's own declared scan order (`FiniteObject.vertices`, the
`FinEnum` numbering behind `orderedVertices`).  A vertex set is read as the
increasing list of its vertex numbers, a family of vertex sets as the increasing
(list-lexicographic) list of its members' lists.  The key is injective, so the
least member of a nonempty finite family of families is unique, and
`lexLeast` is a function of the object and the candidate set alone.
-/

namespace Hypostructure.Graph.FiniteObject

universe u

/-- Sorting a finset is injective. -/
theorem sortInj {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s.sort (· ≤ ·) = t.sort (· ≤ ·)) : s = t := by
  have h1 := Finset.sort_eq s (· ≤ ·)
  have h2 := Finset.sort_eq t (· ≤ ·)
  rw [h] at h1
  exact Finset.val_inj.1 (h1.symm.trans h2)

variable (object : FiniteObject.{u})

/-- The position of a vertex in the object's declared scan order. -/
def vertexRank (vertex : object.Vertex) : Nat :=
  (@FinEnum.equiv object.Vertex object.vertices vertex).val

theorem vertexRank_injective : Function.Injective object.vertexRank := by
  intro a b h
  exact (@FinEnum.equiv object.Vertex object.vertices).injective (Fin.ext h)

/-- A vertex set as the increasing list of its vertex numbers. -/
def supportKey (support : Finset object.Vertex) : List Nat :=
  (support.image object.vertexRank).sort (· ≤ ·)

theorem supportKey_injective : Function.Injective object.supportKey := by
  intro a b h
  have := sortInj h
  exact Finset.image_injective object.vertexRank_injective this

/-- A family of vertex sets as the increasing list of its members' keys. -/
noncomputable def familyKey (family : Finset (Finset object.Vertex)) :
    List (List Nat) := by
  classical
  exact (family.image object.supportKey).sort (· ≤ ·)

theorem familyKey_injective : Function.Injective object.familyKey := by
  classical
  intro a b h
  unfold familyKey at h
  have := sortInj h
  exact Finset.image_injective object.supportKey_injective this

/-- Among a nonempty finite set of families there is exactly one whose key is
least. -/
theorem existsUnique_lexLeast (candidates : Finset (Finset (Finset object.Vertex)))
    (nonempty : candidates.Nonempty) :
    ∃! family, family ∈ candidates ∧
      ∀ other ∈ candidates, object.familyKey family ≤ object.familyKey other := by
  obtain ⟨least, member, minimal⟩ :=
    Finset.exists_min_image candidates object.familyKey nonempty
  refine ⟨least, ⟨member, minimal⟩, ?_⟩
  rintro other ⟨otherMember, otherMinimal⟩
  exact object.familyKey_injective
    (le_antisymm (otherMinimal least member) (minimal other otherMember))

/-- **The lexicographically least family of a candidate set**, in G's vertex
order (`∅` when there is no candidate). -/
noncomputable def lexLeast (candidates : Finset (Finset (Finset object.Vertex))) :
    Finset (Finset object.Vertex) := by
  classical
  exact if h : candidates.Nonempty then
    Classical.choose (object.existsUnique_lexLeast candidates h).exists else ∅

theorem lexLeast_mem (candidates : Finset (Finset (Finset object.Vertex)))
    (nonempty : candidates.Nonempty) : object.lexLeast candidates ∈ candidates := by
  classical
  unfold lexLeast
  rw [dif_pos nonempty]
  exact (Classical.choose_spec (object.existsUnique_lexLeast candidates nonempty).exists).1

theorem lexLeast_le (candidates : Finset (Finset (Finset object.Vertex)))
    (nonempty : candidates.Nonempty) {other : Finset (Finset object.Vertex)}
    (member : other ∈ candidates) :
    object.familyKey (object.lexLeast candidates) ≤ object.familyKey other := by
  classical
  unfold lexLeast
  rw [dif_pos nonempty]
  exact (Classical.choose_spec (object.existsUnique_lexLeast candidates nonempty).exists).2
    other member

/- Integration g-audit-int: `lexLeast` is read only through `lexLeast_mem` and
`lexLeast_le`; left reducible, `whnf` tries to decide the candidate set's
nonemptiness (a powerset filter) wherever `canonicalWindowPacking` occurs. -/
attribute [irreducible] lexLeast

end Hypostructure.Graph.FiniteObject
