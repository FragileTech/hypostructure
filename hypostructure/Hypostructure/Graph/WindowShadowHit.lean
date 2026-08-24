import Hypostructure.Graph.Target
import Hypostructure.Graph.WindowAttachmentShadow
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Window-signature hits close accepted cycles

`lem:typeA-window-shadow-hit-routes`, the geometric certificate: a recorded
corridor between two window attachments, together with the window arc between
the attachment positions, closes a simple cycle of length exactly
`s(Q) + 2 + |a − b|`.  When that length is accepted — which is precisely
membership in the attachment signature `Sh_{s(Q)}(a)` of
`def:typeA-window-attachment-shadow`
(`WindowAttachmentShadow.accepted_of_mem_shadow`) — the object carries an
accepted cycle: the manuscript's direct power-of-two certificate (O1).

Everything is parameterized by the window embedding, the corridor, and the
accepted-length predicate; no presentation constant appears.
-/

namespace Hypostructure.Graph.WindowShadowHit

open Hypostructure
open Hypostructure.Graph

universe u

/-- A walk along the path graph between two positions, of length exactly the
index distance, never stepping below the smaller index. -/
theorem exists_pathGraph_walk_le {order : Nat} (i j : Fin order)
    (le : i.1 ≤ j.1) :
    ∃ w : (SimpleGraph.pathGraph order).Walk i j,
      w.IsPath ∧ w.length = j.1 - i.1 ∧ ∀ v ∈ w.support, i.1 ≤ v.1 := by
  obtain ⟨k, hk⟩ : ∃ k, j.1 = i.1 + k := ⟨j.1 - i.1, by omega⟩
  clear le
  induction k generalizing i with
  | zero =>
      have same : i = j := Fin.ext (by omega)
      subst same
      exact ⟨.nil, SimpleGraph.Walk.IsPath.nil, by simp, by simp⟩
  | succ k ih =>
      have nextLt : i.1 + 1 < order := by
        have := j.2
        omega
      let next : Fin order := ⟨i.1 + 1, nextLt⟩
      have step : (SimpleGraph.pathGraph order).Adj i next :=
        SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
      obtain ⟨rest, restPath, restLength, restBound⟩ := ih next (by
        show j.1 = i.1 + 1 + k
        omega)
      have nextVal : next.1 = i.1 + 1 := rfl
      refine ⟨.cons step rest, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨restPath, fun member => ?_⟩
        have := restBound i member
        rw [nextVal] at this
        omega
      · rw [SimpleGraph.Walk.length_cons, restLength, nextVal]
        omega
      · intro v member
        rw [SimpleGraph.Walk.support_cons] at member
        rcases List.mem_cons.mp member with rfl | tailMem
        · exact Nat.le_refl _
        · have := restBound v tailMem
          rw [nextVal] at this
          omega

/-- A path-graph walk between any two positions, of length exactly the index
distance. -/
theorem exists_pathGraph_walk {order : Nat} (i j : Fin order) :
    ∃ w : (SimpleGraph.pathGraph order).Walk i j,
      w.IsPath ∧ w.length = Nat.dist i.1 j.1 := by
  rcases Nat.le_total i.1 j.1 with le | ge
  · obtain ⟨w, path, length, _⟩ := exists_pathGraph_walk_le i j le
    exact ⟨w, path, by rw [length, Nat.dist_eq_sub_of_le le]⟩
  · obtain ⟨w, path, length, _⟩ := exists_pathGraph_walk_le j i ge
    exact ⟨w.reverse, path.reverse, by
      rw [SimpleGraph.Walk.length_reverse, length,
        Nat.dist_eq_sub_of_le_right ge]⟩

/-- **The window-arc walk**: a simple walk between two attachment positions
of an embedded window, of length exactly the index distance, supported on
window vertices. -/
theorem exists_window_arc {order : Nat} {object : FiniteObject.{u}}
    (window : SimpleGraph.pathGraph order ↪g object.graph) (a b : Fin order) :
    ∃ arc : object.graph.Walk (window b) (window a),
      arc.IsPath ∧ arc.length = Nat.dist a.1 b.1 ∧
        ∀ v ∈ arc.support, ∃ i : Fin order, v = window i := by
  obtain ⟨w, path, length⟩ := exists_pathGraph_walk b a
  refine ⟨w.map window.toHom, ?_, ?_, ?_⟩
  · exact SimpleGraph.Walk.map_isPath_of_injective window.injective path
  · rw [SimpleGraph.Walk.length_map, length, Nat.dist_comm]
  · intro v member
    rw [SimpleGraph.Walk.support_map] at member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    exact ⟨i, rfl⟩

/-- **`lem:typeA-window-shadow-hit-routes`, the cycle**: a simple corridor
between two window attachments, avoiding the window, closes a simple cycle of
length exactly `s(Q) + 2 + |a − b|` — the corridor, the two attachment edges,
and the window arc. -/
theorem exists_cycle_of_corridor {order : Nat} {object : FiniteObject.{u}}
    (window : SimpleGraph.pathGraph order ↪g object.graph)
    {x y : object.Vertex} {a b : Fin order}
    (corridor : object.graph.Walk x y) (corridorPath : corridor.IsPath)
    (corridorAvoids : ∀ i : Fin order, window i ∉ corridor.support)
    (attachA : object.graph.Adj (window a) x)
    (attachB : object.graph.Adj y (window b))
    (edgesDistinct : s(x, window a) ≠ s(y, window b)) :
    ∃ c : object.graph.Walk (window a) (window a),
      c.IsCycle ∧ c.length = corridor.length + 2 + Nat.dist a.1 b.1 := by
  classical
  obtain ⟨arc, arcPath, arcLength, arcWindow⟩ := exists_window_arc window a b
  let tail : object.graph.Walk x (window a) :=
    corridor.append (SimpleGraph.Walk.cons attachB arc)
  have tailPath : tail.IsPath := by
    have supportEq : tail.support =
        corridor.support ++ (SimpleGraph.Walk.cons attachB arc).support.tail :=
      SimpleGraph.Walk.support_append _ _
    rw [SimpleGraph.Walk.isPath_def, supportEq,
      SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_append]
    refine ⟨corridorPath.support_nodup, arcPath.support_nodup, ?_⟩
    intro v vCorridor v' vArc
    obtain ⟨i, rfl⟩ := arcWindow v' vArc
    intro same
    exact corridorAvoids i (same ▸ vCorridor)
  have edgeFresh : s(window a, x) ∉ tail.edges := by
    intro member
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      List.mem_append, List.mem_cons] at member
    rcases member with corridorEdge | attachEdge | arcEdge
    · exact corridorAvoids a
        (corridor.fst_mem_support_of_mem_edges corridorEdge)
    · exact edgesDistinct (by rw [Sym2.eq_swap] at attachEdge; exact attachEdge)
    · obtain ⟨i, eq⟩ := arcWindow x (arc.snd_mem_support_of_mem_edges arcEdge)
      exact corridorAvoids i (eq ▸ corridor.start_mem_support)
  refine ⟨.cons attachA tail, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff tail attachA).mpr
      ⟨tailPath, edgeFresh⟩
  · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, arcLength]
    omega

/-- **`lem:typeA-window-shadow-hit-routes`**: a recorded window-signature hit
is a direct accepted-cycle certificate — certificate (O1) of
`def:typeA-same-window-overload-triple`.  The signature membership is exactly
the acceptance of the closed length
(`WindowAttachmentShadow.accepted_of_mem_shadow`). -/
theorem hasCycleWithLength_of_shadow_hit {order : Nat}
    {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (window : SimpleGraph.pathGraph order ↪g object.graph)
    {x y : object.Vertex} {a b : Fin order}
    (corridor : object.graph.Walk x y) (corridorPath : corridor.IsPath)
    (corridorAvoids : ∀ i : Fin order, window i ∉ corridor.support)
    (attachA : object.graph.Adj (window a) x)
    (attachB : object.graph.Adj y (window b))
    (edgesDistinct : s(x, window a) ≠ s(y, window b))
    (hit : b.1 ∈ WindowAttachmentShadow.shadow LengthOK order
      corridor.length a.1) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨c, cycle, length⟩ := exists_cycle_of_corridor window corridor
    corridorPath corridorAvoids attachA attachB edgesDistinct
  refine ⟨⟨_, c, cycle, ?_⟩⟩
  rw [length]
  exact WindowAttachmentShadow.accepted_of_mem_shadow hit

end Hypostructure.Graph.WindowShadowHit
