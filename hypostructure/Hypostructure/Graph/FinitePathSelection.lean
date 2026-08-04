import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Hypostructure.Graph.Finite

/-!
# Canonical finite path selection

This module is the reusable Graph adapter for selecting a path from a finite
graph.  The candidate family is generated from Mathlib's complete finite path
type, grouped by length, and scanned in that fixed order.  Applications
supply neither a path nor a selection result.
-/

namespace Hypostructure.Graph.FinitePathSelection

open Hypostructure.Graph

universe u

/-- The complete finite path schedule, grouped first by length and then by
Mathlib's canonical finite enumeration. -/
noncomputable def pathSchedule {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] (left right : V) :
    List (graph.Path left right) :=
  (List.range (Fintype.card V + 1)).flatMap fun length =>
    (Finset.univ.toList.filter fun path => path.1.length = length)

structure SelectedPath {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] (left right : V) where
  path : graph.Path left right
  member : path ∈ pathSchedule graph left right
  first : ∀ earlier, earlier ∈ pathSchedule graph left right →
    (pathSchedule graph left right).idxOf path ≤
      (pathSchedule graph left right).idxOf earlier

/-- Select the first member of the complete finite schedule. -/
noncomputable def select? {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] (left right : V) :
    Option (SelectedPath graph left right) := by
  classical
  let schedule := pathSchedule graph left right
  by_cases nonempty : schedule ≠ []
  · let path := schedule.head nonempty
    have pathFirst : schedule.idxOf path = 0 :=
      (List.idxOf_eq_zero_iff_head_eq nonempty).2 rfl
    exact some {
      path := path
      member := List.head_mem nonempty
      first := by
        intro earlier earlierMem
        rw [show (pathSchedule graph left right).idxOf path = 0 by
          simpa [schedule] using pathFirst]
        exact Nat.zero_le _ }
  · exact none

theorem mem_pathSchedule {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (path : graph.Path left right) :
    path ∈ pathSchedule graph left right := by
  classical
  rw [pathSchedule, List.mem_flatMap]
  refine ⟨path.1.length, ?_, ?_⟩
  · simp only [List.mem_range]
    exact Nat.lt_succ_of_le (Nat.le_of_lt path.2.length_lt)
  · simp

theorem pathSchedule_nonempty_of_reachable
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (reachable : graph.Reachable left right) :
    pathSchedule graph left right ≠ [] := by
  obtain ⟨walk, isPath⟩ := reachable.exists_isPath
  intro empty
  have member : (⟨walk, isPath⟩ : graph.Path left right) ∈
      pathSchedule graph left right :=
    mem_pathSchedule graph ⟨walk, isPath⟩
  simpa [empty] using member

/-- A reachability proof turns the total finite selection into its exact
selected path. -/
noncomputable def selectOfReachable
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (reachable : graph.Reachable left right) :
    SelectedPath graph left right := by
  classical
  have nonempty := pathSchedule_nonempty_of_reachable graph reachable
  exact {
    path := (pathSchedule graph left right).head nonempty
    member := List.head_mem nonempty
    first := by
      intro earlier earlierMem
      rw [(List.idxOf_eq_zero_iff_head_eq nonempty).2 rfl]
      exact Nat.zero_le _ }

/-- Canonical support path between two vertices of a packed finite object. -/
noncomputable def supportPath? (object : FiniteObject.{u})
    (left right : object.Vertex) :
    Option (by
      letI : FinEnum object.Vertex := object.vertices
      letI : Fintype object.Vertex := by infer_instance
      letI : DecidableEq object.Vertex := object.vertices.decEq
      letI : DecidableRel object.graph.Adj := object.decideAdj
      exact SelectedPath object.graph left right) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact select? object.graph left right

/-- Exact finite work represented by the length-major path schedule. -/
def work (object : FiniteObject.{u}) : Nat :=
  object.vertexCount + 1 |> fun lengths => lengths * 2 ^ object.vertexCount

end Hypostructure.Graph.FinitePathSelection
