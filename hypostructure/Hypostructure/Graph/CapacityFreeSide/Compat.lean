import Hypostructure.Graph.Statements.CanonicalCapacityExplicit

/-!
# Free side, step 1: a two-port compatible suppression is always a clause-(f) blocker

For two selected ports
`p = (h_p, x_p)`, `q = (h_q, x_q)` of an `ActiveSurplusDemands` certificate, both
open, whose supports `T(p) = {x_p, a_p, b_p}`, `T(q)` are disjoint, whose centres
differ, and whose centres avoid the other support, the simultaneous suppression
of `x_p, x_q` is a `CompatibleFamily`, it keeps the baseline (each centre loses
exactly one edge and is high), it is lexicographically smaller, so minimality
gives it an accepted cycle, and the chord set that cycle uses is a literal member
of `(pairResponseActivation active).chordObstructions {p,q}`.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

/-! ## The chord-set enumeration contains every subset of the ports -/

theorem nil_mem_lexSublists {object : FiniteObject.{u}}
    (l : List (object.Vertex × object.Vertex)) :
    [] ∈ pairResponseActivation.lexicographicSublists l := by
  cases l with
  | nil => simp [pairResponseActivation.lexicographicSublists.eq_1]
  | cons h t => simp [pairResponseActivation.lexicographicSublists.eq_2]

theorem lexSublists_head {object : FiniteObject.{u}}
    (l : List (object.Vertex × object.Vertex)) :
    ∃ rest, pairResponseActivation.lexicographicSublists l = [] :: rest := by
  cases l with
  | nil => exact ⟨[], by simp [pairResponseActivation.lexicographicSublists.eq_1]⟩
  | cons h t => exact ⟨_, pairResponseActivation.lexicographicSublists.eq_2 h t⟩

theorem mem_lexSublists_of_sublist {object : FiniteObject.{u}} :
    ∀ (l s : List (object.Vertex × object.Vertex)), s.Sublist l →
      s ∈ pairResponseActivation.lexicographicSublists l
  | [], s, h => by
      rw [List.sublist_nil.1 h]
      exact nil_mem_lexSublists _
  | h :: t, s, hs => by
      rw [pairResponseActivation.lexicographicSublists.eq_2]
      cases hs with
      | cons _ hs' =>
          have ih := mem_lexSublists_of_sublist t s hs'
          cases s with
          | nil => exact List.mem_cons_self
          | cons a s =>
              obtain ⟨rest, hrest⟩ := lexSublists_head (object := object) t
              rw [hrest] at ih ⊢
              have : a :: s ∈ rest := by
                rcases List.mem_cons.1 ih with e | e
                · cases e
                · exact e
              exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simpa using this))
      | cons_cons _ hs' =>
          exact List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_map.2 ⟨_, mem_lexSublists_of_sublist t _ hs', rfl⟩))

/-- Every subset of the selected ports is one of the enumerated chord sets. -/
theorem mem_orderedChordSets {object : FiniteObject.{u}} {threshold : Nat}
    [DecidableEq (object.Vertex × object.Vertex)]
    (r : object.Vertex × object.Vertex → object.Vertex × object.Vertex → Prop) [DecidableRel r]
    (chords : Finset (object.Vertex × object.Vertex))
    (sub : chords ⊆ object.excessPorts threshold) :
    chords ∈ List.filter (fun chords => decide (chords ∈ (object.excessPorts threshold).powerset))
      (List.map List.toFinset
        (pairResponseActivation.lexicographicSublists
          (List.insertionSort r
            (List.flatMap
              (fun centre =>
                List.map (fun endpoint => (centre, endpoint))
                  (object.selectedPortEndpoints threshold centre))
              object.orderedVertices)))) := by
  classical
  set L := List.insertionSort r
    (List.flatMap
      (fun centre =>
        List.map (fun endpoint => (centre, endpoint))
          (object.selectedPortEndpoints threshold centre))
      object.orderedVertices) with hL
  have inL : ∀ x ∈ chords, x ∈ L := by
    intro x hx
    have hx' := (FiniteObject.mem_excessPorts_iff x).1 (sub hx)
    rw [hL, (List.perm_insertionSort r _).mem_iff, List.mem_flatMap]
    exact ⟨x.1, object.mem_orderedVertices x.1, List.mem_map.2 ⟨x.2, hx', rfl⟩⟩
  refine List.mem_filter.2 ⟨List.mem_map.2 ⟨L.filter (fun x => decide (x ∈ chords)),
    mem_lexSublists_of_sublist _ _ List.filter_sublist, ?_⟩, ?_⟩
  · ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨inL x h, h⟩⟩
  · simpa using sub

end Hypostructure.Graph.CapacityFreeSide
