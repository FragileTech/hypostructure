import Hypostructure.Graph.ReadingProfiles

/-!
# Cycles through an edge

A cycle of a graph through an edge `ab` gives an `a`–`b` path avoiding that edge,
one shorter than the cycle (`cycle_through_edge`, with `path_first_edge`).
Statements about walks of one graph.  (G-only restatement: the single-edge and
degree-two chain contexts, and the path-spectrum transfer between readings they
carried, built boundaried contexts other than `G − Z` and are removed.)
-/

universe u v

namespace Hypostructure.Graph.ReadingSpectrum.EdgeContext

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Classical

variable {object : FiniteObject.{u}}

/-- Lemma P (vocabulary-free): a path starting at `u` that uses the edge `uz`
uses it first. -/
theorem path_first_edge {V : Type*} {G : SimpleGraph V} :
    ∀ {u v z : V} (p : G.Walk u v), p.IsPath → s(u, z) ∈ p.edges →
      ∃ (h : G.Adj u z) (r : G.Walk z v), p = .cons h r
  | _, _, _, .nil, _, mem => by simp at mem
  | u, v, z, .cons (v := w) h r, path, mem => by
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at mem
      rcases mem with eq | mem
      · rcases Sym2.eq_iff.1 eq with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨h, r, rfl⟩
        · exact absurd h (G.loopless.irrefl _)
      · exact absurd (r.fst_mem_support_of_mem_edges mem)
          ((SimpleGraph.Walk.cons_isPath_iff h r).1 path).2

/-- **Cycle-through-edge decomposition** (vocabulary-free): a cycle using the
edge `ab` yields an `a`–`b` path avoiding `ab` of length one less. -/
theorem cycle_through_edge {V : Type*} {G : SimpleGraph V} {v a b : V}
    (c : G.Walk v v) (cyc : c.IsCycle) (mem : s(a, b) ∈ c.edges) :
    ∃ w : G.Walk a b, w.IsPath ∧ s(a, b) ∉ w.edges ∧ w.length + 1 = c.length := by
  have aSupp : a ∈ c.support := c.fst_mem_support_of_mem_edges mem
  let c1 := c.rotate a aSupp
  have cyc1 : c1.IsCycle := cyc.rotate aSupp
  have mem1 : s(a, b) ∈ c1.edges :=
    (SimpleGraph.Walk.rotate_edges c a aSupp).mem_iff.2 mem
  have len1 : c1.length = c.length := SimpleGraph.Walk.length_rotate c a aSupp
  rw [← len1]
  clear_value c1
  cases c1 with
  | nil => exact absurd cyc1 SimpleGraph.Walk.IsCycle.not_of_nil
  | cons h1 q1 =>
    rename_i x
    obtain ⟨qPath, qFresh⟩ := (SimpleGraph.Walk.cons_isCycle_iff q1 h1).1 cyc1
    by_cases hx : x = b
    · subst hx
      refine ⟨q1.reverse, qPath.reverse, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
        exact qFresh
      · simp
    · have memq : s(a, b) ∈ q1.edges := by
        rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at mem1
        rcases mem1 with eq | m
        · rcases Sym2.eq_iff.1 eq with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd h.symm hx
          · subst h; exact absurd h1 (G.loopless.irrefl _)
        · exact m
      have memr : s(a, b) ∈ q1.reverse.edges := by
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact memq
      obtain ⟨hab, r, hr⟩ := path_first_edge q1.reverse qPath.reverse memr
      have rPath : r.IsPath := by
        have := qPath.reverse; rw [hr] at this
        exact ((SimpleGraph.Walk.cons_isPath_iff hab r).1 this).1
      have aNot : a ∉ r.support := by
        have := qPath.reverse; rw [hr] at this
        exact ((SimpleGraph.Walk.cons_isPath_iff hab r).1 this).2
      have abNot : s(a, b) ∉ r.edges := by
        have := qPath.reverse.edges_nodup; rw [hr, SimpleGraph.Walk.edges_cons] at this
        exact (List.nodup_cons.1 this).1
      have lenq : q1.length = r.length + 1 := by
        have := congrArg SimpleGraph.Walk.length hr
        simp at this; omega
      refine ⟨.cons h1 r.reverse, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        exact ⟨rPath.reverse, by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact aNot⟩
      · rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or]
        refine ⟨?_, ?_⟩
        · intro eq
          rcases Sym2.eq_iff.1 eq with ⟨-, h⟩ | ⟨h, -⟩
          · exact hx h.symm
          · subst h; exact absurd h1 (G.loopless.irrefl _)
        · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact abNot
      · simp [lenq]

end Hypostructure.Graph.ReadingSpectrum.EdgeContext

