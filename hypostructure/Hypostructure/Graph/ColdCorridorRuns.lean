import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.WindowCombination

/-!
# The cold return corridor is a shortest path of `K`

`Corridor.inside` is the length-major path of the framework's canonical
schedule (`inside_length_le`), so it is a shortest path of the component `K`.
This module derives what shortestness says about G:

* `inside_induced`: two corridor vertices that are not consecutive on the
  corridor are not adjacent in G (the corridor is an induced path of G);
* `inside_run_short`: two corridor vertices that lie in a set `S` disjoint from
  the deleted windows and are joined by a walk inside `S`, which the
  window-free geometry of the maximal packing shortens to at most `11` steps,
  are at most `11` positions apart on the corridor.

Both are facts of G's canonical corridors; nothing outside G enters.
-/

open Hypostructure.Graph.WindowCombination

namespace Hypostructure.Graph.ColdCorridor

universe u

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

namespace Corridor

variable {object : FiniteObject.{u}} {windows component : Finset object.Vertex}

/-- **Shortcuts do not shorten the corridor.**  A walk of `K` between the
vertices at positions `i ≤ j` of the corridor has at least `j - i` edges: replacing
the stretch `i..j` of the shortest path by it would otherwise give a shorter path. -/
theorem shortcut_le (corridor : Corridor object windows component) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ corridor.inside.1.length)
    (q : (object.induce component).graph.Walk
      (corridor.inside.1.getVert i) (corridor.inside.1.getVert j)) :
    j - i ≤ q.length := by
  classical
  have shortest := corridor.inside_length_le
    (((corridor.inside.1.take i).append (q.append (corridor.inside.1.drop j))).toPath)
  have bypass := SimpleGraph.Walk.length_bypass_le_length
    ((corridor.inside.1.take i).append (q.append (corridor.inside.1.drop j)))
  have takeLen := SimpleGraph.Walk.take_length corridor.inside.1 i
  have dropLen := SimpleGraph.Walk.drop_length corridor.inside.1 j
  simp only [SimpleGraph.Walk.length_append] at bypass
  have toPathLen : (((corridor.inside.1.take i).append
      (q.append (corridor.inside.1.drop j))).toPath).1.length =
      ((corridor.inside.1.take i).append
        (q.append (corridor.inside.1.drop j))).bypass.length := rfl
  rw [toPathLen] at shortest
  have iL : i ⊓ corridor.inside.1.length = i := inf_eq_left.mpr (le_trans hij hj)
  omega

/-- **The corridor is an induced path of G.** -/
theorem inside_induced (corridor : Corridor object windows component) {i j : ℕ}
    (hij : i + 1 < j) (hj : j ≤ corridor.inside.1.length) :
    ¬ object.graph.Adj (corridor.inside.1.getVert i).1 (corridor.inside.1.getVert j).1 := by
  intro adj
  have step : (object.induce component).graph.Adj (corridor.inside.1.getVert i)
      (corridor.inside.1.getVert j) := SimpleGraph.induce_adj.mpr adj
  have := shortcut_le corridor (le_of_lt (lt_of_le_of_lt (Nat.le_succ i) hij)) hj
    (SimpleGraph.Walk.cons step SimpleGraph.Walk.nil)
  simp at this
  omega

/-- **Runs of the corridor in a window-free set are short.**  Let `S` be a set of
vertices avoiding the deleted windows, such that a walk inside `S` between two
vertices can always be replaced by one of at most `11` steps (the window-free
geometry of the maximal packing).  Two corridor vertices in `S` joined by a walk
in `S` are at most `11` positions apart on the corridor. -/
theorem inside_run_short (corridor : Corridor object windows component)
    (outside : IsOutsideComponent object windows component)
    (S : Set object.Vertex) (avoids : ∀ v ∈ S, v ∉ (↑windows : Set object.Vertex))
    (short : ∀ u v : object.Vertex, (∃ k, Reach object.graph S u v k) →
      ∃ k, k ≤ 11 ∧ Reach object.graph S u v k)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ corridor.inside.1.length)
    (joined : ∃ k, Reach object.graph S (corridor.inside.1.getVert i).1
      (corridor.inside.1.getVert j).1 k) :
    j - i ≤ 11 := by
  classical
  obtain ⟨k, klt, g, ⟨steps, inS⟩, g0, gk⟩ := short _ _ joined
  -- the walk stays in `K`
  have inK : ∀ t ≤ k, g t ∈ component := by
    intro t
    induction t with
    | zero => intro _; rw [g0]; exact (corridor.inside.1.getVert i).2
    | succ t ih =>
        intro ht
        have prev := ih (Nat.le_of_succ_le ht)
        exact outside.2.1 (g t) prev (g (t + 1)) (steps t (Nat.lt_of_succ_le ht))
          (avoids _ (inS _ ht))
  have lift : ∀ t (ht : t ≤ k), ∃ q : (object.induce component).graph.Walk
      (corridor.inside.1.getVert i) ⟨g t, inK t ht⟩, q.length ≤ t := by
    intro t
    induction t with
    | zero =>
        intro ht
        refine ⟨(SimpleGraph.Walk.nil : (object.induce component).graph.Walk _ _).copy rfl
          (Subtype.ext g0.symm), ?_⟩
        simp
    | succ t ih =>
        intro ht
        obtain ⟨q, qlen⟩ := ih (Nat.le_of_succ_le ht)
        have adj : (object.induce component).graph.Adj ⟨g t, inK t (Nat.le_of_succ_le ht)⟩
            ⟨g (t + 1), inK (t + 1) ht⟩ :=
          SimpleGraph.induce_adj.mpr (steps t (Nat.lt_of_succ_le ht))
        refine ⟨q.concat adj, ?_⟩
        simp [SimpleGraph.Walk.length_concat]
        omega
  obtain ⟨q, qlen⟩ := lift k le_rfl
  have final : (⟨g k, inK k le_rfl⟩ : (object.induce component).Vertex) =
      corridor.inside.1.getVert j := Subtype.ext gk
  have := shortcut_le corridor hij hj (q.copy rfl final)
  simp only [SimpleGraph.Walk.length_copy] at this
  omega

end Corridor

end Hypostructure.Graph.ColdCorridor
