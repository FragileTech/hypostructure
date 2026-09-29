import Hypostructure.Graph.LadderCount
import Hypostructure.Graph.PortPathCover
import Hypostructure.Graph.JointObject

/-!
# The ladder count at a finite object (`[144a]`, G audit S144a)

Instantiates `LadderCount.ladder_count` at `Cubic := (degree = 3)`.
-/

namespace Hypostructure.Graph.LadderBridge

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.PathChords
open Hypostructure.Graph.LadderCount

universe u

variable {object : FiniteObject.{u}}

/-- degree-3 vertices have the stub property -/
theorem stub_of_degree_three (m : object.Vertex) (deg : object.degree m = 3)
    (a b : object.Vertex) (ha : object.graph.Adj m a) (hb : object.graph.Adj m b) (hab : a ≠ b) :
    ∃ s, object.graph.Adj m s ∧ s ≠ a ∧ s ≠ b ∧
      ∀ t, object.graph.Adj m t → t = a ∨ t = b ∨ t = s := by
  haveI : Finite object.Vertex := by letI := object.vertices; infer_instance
  rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
  have fin : (object.graph.neighborSet m).Finite := Set.toFinite _
  obtain ⟨s, hs, sa, sb⟩ : ∃ s, object.graph.Adj m s ∧ s ≠ a ∧ s ≠ b := by
    by_contra none
    push Not at none
    have sub : object.graph.neighborSet m ⊆ {a, b} := by
      intro t ht
      by_cases ta : t = a
      · simp [ta]
      · simp [none t ht ta]
    have := Set.ncard_le_ncard sub (Set.toFinite _)
    have h2' : ({a, b} : Set object.Vertex).ncard ≤ 2 := by
      have := Set.ncard_insert_le a ({b} : Set object.Vertex)
      simpa using this
    omega
  refine ⟨s, hs, sa, sb, fun t ht => ?_⟩
  by_contra none
  push Not at none
  obtain ⟨ta, tb, ts⟩ := none
  have sub : ({a, b, s, t} : Set object.Vertex) ⊆ object.graph.neighborSet m := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hs
    · exact ht
  have card4 : ({a, b, s, t} : Set object.Vertex).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · exact fun h => ts h.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => sb h.symm, fun h => tb h.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, fun h => sa h.symm, fun h => ta h.symm⟩
  have := Set.ncard_le_ncard sub fin
  omega

end Hypostructure.Graph.LadderBridge
