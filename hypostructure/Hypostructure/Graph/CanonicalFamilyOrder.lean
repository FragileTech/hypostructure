import Mathlib

/-!
# Lexicographic order on families of vertex sets

A finite object's vertex order is the position in its `FinEnum` list
(`FiniteObject.orderedVertices`).  A vertex set is read as the increasing list
of its positions, and a family of vertex sets as the increasing list of those
lists (list order is lexicographic).  Both readings are injective, so the
lexicographically least member of a nonempty finite family of families is
determined by the object alone; this is the canonical tie-break used to pin a
choice among equal candidates to G's vertex order.
-/

namespace Hypostructure.Graph

universe u

/-- The increasing list of the positions of a vertex set in the vertex order. -/
noncomputable def vertexIndexSet {α : Type u} [FinEnum α] (w : Finset α) :
    List (Fin (FinEnum.card α)) :=
  (w.image (fun a => (FinEnum.equiv a : Fin (FinEnum.card α)))).sort (· ≤ ·)

theorem vertexIndexSet_injective {α : Type u} [FinEnum α] :
    Function.Injective (vertexIndexSet (α := α)) := by
  intro w w' h
  unfold vertexIndexSet at h
  classical
  have h2 := congrArg List.toFinset h
  rw [Finset.sort_toFinset, Finset.sort_toFinset] at h2
  exact Finset.image_injective (FinEnum.equiv (α := α)).injective h2

/-- The lexicographic key of a family of vertex sets: the increasing list of the
position lists of its members. -/
noncomputable def lexFamilyKey {α : Type u} [FinEnum α] (family : Finset (Finset α)) :
    List (List (Fin (FinEnum.card α))) :=
  (family.image vertexIndexSet).sort (· ≤ ·)

theorem lexFamilyKey_injective {α : Type u} [FinEnum α] :
    Function.Injective (lexFamilyKey (α := α)) := by
  intro f f' h
  unfold lexFamilyKey at h
  classical
  have h2 := congrArg List.toFinset h
  rw [Finset.sort_toFinset, Finset.sort_toFinset] at h2
  exact Finset.image_injective vertexIndexSet_injective h2

/-- The lexicographically least member of a nonempty finite set of families. -/
theorem exists_lexLeast_family {α : Type u} [FinEnum α]
    (candidates : Finset (Finset (Finset α))) (nonempty : candidates.Nonempty) :
    ∃ least ∈ candidates, ∀ other ∈ candidates, lexFamilyKey least ≤ lexFamilyKey other :=
  Finset.exists_min_image candidates lexFamilyKey nonempty

end Hypostructure.Graph
