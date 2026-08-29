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

/-- The complete schedule is length-major: every path appearing earlier has
length at most every path appearing later. -/
theorem pathSchedule_pairwise_length {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] (left right : V) :
    (pathSchedule graph left right).Pairwise
      (fun first second => first.1.length ≤ second.1.length) := by
  classical
  rw [pathSchedule, List.pairwise_flatMap]
  constructor
  · intro length _lengthMem
    rw [List.pairwise_filter]
    apply List.pairwise_of_forall
    intro first second firstLength secondLength
    simp only [decide_eq_true_eq] at firstLength secondLength
    omega
  · refine List.pairwise_lt_range.imp_of_mem ?_
    intro firstLength secondLength _firstMem _secondMem before
    intro first firstMem second secondMem
    have firstEq : first.1.length = firstLength := by simpa using firstMem
    have secondEq : second.1.length = secondLength := by simpa using secondMem
    omega

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

/-- The selected path is shortest.  This is the semantic content of scanning
the complete path schedule by length before applying the canonical tie-break. -/
theorem selectOfReachable_length_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (reachable : graph.Reachable left right)
    (other : graph.Path left right) :
    (selectOfReachable graph reachable).path.1.length ≤ other.1.length := by
  classical
  let schedule := pathSchedule graph left right
  have nonempty := pathSchedule_nonempty_of_reachable graph reachable
  have otherMem : other ∈ schedule := mem_pathSchedule graph other
  have ordered := pathSchedule_pairwise_length graph left right
  change schedule ≠ [] at nonempty
  change List.Pairwise (fun first second => first.1.length ≤ second.1.length)
    schedule at ordered
  change schedule.head nonempty |>.1.length ≤ other.1.length
  obtain ⟨index, indexEq⟩ := List.mem_iff_get.1 otherMem
  have positive : 0 < schedule.length := List.length_pos_of_ne_nil nonempty
  let firstIndex : Fin schedule.length := ⟨0, positive⟩
  have firstEq : schedule.get firstIndex = schedule.head nonempty := by
    simpa [firstIndex] using (List.head_eq_getElem_zero nonempty).symm
  rcases Nat.eq_zero_or_pos index.1 with zero | after
  · have sameIndex : index = firstIndex := Fin.ext zero
    rw [← firstEq, ← indexEq, sameIndex]
  · have before : firstIndex < index := by
      change firstIndex.1 < index.1
      simpa [firstIndex] using after
    have relation := ordered.rel_get_of_lt before
    rw [firstEq, indexEq] at relation
    exact relation

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
