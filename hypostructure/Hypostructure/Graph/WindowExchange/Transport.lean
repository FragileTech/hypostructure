import Hypostructure.Graph.PackingExchange
import Hypostructure.Graph.HubWindow
import Hypostructure.Graph.Target

/-!
# Transport of concrete witnesses into a finite object

A finite local configuration is a Boolean adjacency `H` on `{0, …, N−1}`.  A map
`F : ℕ → object.Vertex` realises it when `F` is injective on `{0, …, N−1}` and, for the
checked pairs, `object.graph.Adj (F u) (F v) ↔ H u v`.  Two checkers read witnesses off `H`:

* `chkIndPath H N n w`: `w` lists an induced path on `n` vertices of `H`; its image under a
  realisation is a support inducing a window of order `n` (`inducesWindow_of_chkIndPath`);
* `chkCycle H N w`: `w` lists, in cyclic order, the vertices of a cycle of `H`; its image
  under a map that preserves the edges of `H` is a Mathlib cycle of length `|w|`
  (`cycle_of_chkCycle`).

Nothing here depends on a manuscript: `H`, `N`, `n` are parameters.
-/

namespace Hypostructure.Graph.WindowExchange

open Hypostructure
open Hypostructure.Graph

universe u

/-- `w` lists an induced path on `n` vertices of `H` inside `{0, …, N−1}`. -/
def chkIndPath (H : ℕ → ℕ → Bool) (N n : ℕ) (w : List ℕ) : Bool :=
  decide w.Nodup && w.all (· < N) && w.length == n &&
    (List.range n).all fun i => (List.range n).all fun j =>
      H (w.getD i 0) (w.getD j 0) == (i + 1 == j || j + 1 == i)

/-- `w` lists, in cyclic order, the vertices of a cycle of `H` inside `{0, …, N−1}`
(chords allowed). -/
def chkCycle (H : ℕ → ℕ → Bool) (N : ℕ) (w : List ℕ) : Bool :=
  decide w.Nodup && w.all (· < N) && decide (3 ≤ w.length) &&
    (List.range (w.length - 1)).all (fun i => H (w.getD i 0) (w.getD (i + 1) 0)) &&
    H (w.getD (w.length - 1) 0) (w.getD 0 0)

theorem getD_eq_getElem {w : List ℕ} {i : ℕ} (h : i < w.length) : w.getD i 0 = w[i] := by
  simp [List.getD_eq_getElem?_getD, h]

variable {object : FiniteObject.{u}}

/-- **Induced paths transport.**  If `F` realises `H` on `{0, …, N−1}` (adjacency both ways,
injective) and `w` passes `chkIndPath H N n`, the image of `w` induces a window of order `n`. -/
theorem inducesWindow_of_chkIndPath {H : ℕ → ℕ → Bool} {N n : ℕ} {F : ℕ → object.Vertex}
    (hF : ∀ u v, u < N → v < N → (object.graph.Adj (F u) (F v) ↔ H u v = true))
    (hinj : ∀ u v, u < N → v < N → F u = F v → u = v) {w : List ℕ}
    (h : chkIndPath H N n w = true) :
    ∃ S : Finset object.Vertex, object.InducesWindow n S ∧
      ∀ v, v ∈ S ↔ ∃ x ∈ w, F x = v := by
  simp only [chkIndPath, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hnd, hlt⟩, hlen⟩, hadj⟩ := h
  have hlt' : ∀ i : Fin n, w.getD i.1 0 < N := by
    intro i
    rw [getD_eq_getElem (by omega)]
    exact hlt _ (List.getElem_mem _)
  let q : Fin n → object.Vertex := fun i => F (w.getD i.1 0)
  have qinj : Function.Injective q := by
    intro i j e
    have e' := hinj _ _ (hlt' i) (hlt' j) e
    rw [getD_eq_getElem (by omega), getD_eq_getElem (by omega)] at e'
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 e')
  have qlaw : ∀ i j : Fin n, object.graph.Adj (q i) (q j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
    intro i j
    rw [hF _ _ (hlt' i) (hlt' j)]
    have := hadj i.1 i.2 j.1 j.2
    rw [this]
    simp
  obtain ⟨S, hS, mem⟩ := PackingExchange.exists_inducesWindow_of_pathMap qinj qlaw
  refine ⟨S, hS, fun v => ?_⟩
  rw [mem]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨w.getD i.1 0, by rw [getD_eq_getElem (by omega)]; exact List.getElem_mem _, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact ⟨⟨k, by omega⟩, by simp only [q]; rw [getD_eq_getElem hk]⟩

/-- **Cycles transport.**  If `F` is injective on `{0, …, N−1}` and carries every edge of `H`
there to an edge of the object, a list passing `chkCycle H N` is the vertex list of a
Mathlib cycle of the object of the same length. -/
theorem cycle_of_chkCycle {H : ℕ → ℕ → Bool} {N : ℕ} {F : ℕ → object.Vertex}
    (hF : ∀ u v, u < N → v < N → H u v = true → object.graph.Adj (F u) (F v))
    (hinj : ∀ u v, u < N → v < N → F u = F v → u = v) {w : List ℕ}
    (h : chkCycle H N w = true) :
    ∃ (x : object.Vertex) (c : object.graph.Walk x x), c.IsCycle ∧ c.length = w.length := by
  simp only [chkCycle, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hnd, hlt⟩, hlen⟩, hadj⟩, hclose⟩ := h
  obtain ⟨a, l, rfl⟩ : ∃ a l, w = a :: l := by
    cases w with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  have hmnd : (F a :: l.map F).Nodup := by
    have := hnd.map_on (f := F) fun x hx y hy hxy => hinj x y (hlt x hx) (hlt y hy) hxy
    simpa using this
  have hch : List.IsChain object.graph.Adj (F a :: l.map F) := by
    rw [← List.map_cons, List.isChain_map, List.isChain_iff_getElem]
    intro i hi
    have := hadj i (by simp at hi ⊢; omega)
    rw [getD_eq_getElem (by omega), getD_eq_getElem (by omega)] at this
    exact hF _ _ (hlt _ (List.getElem_mem _)) (hlt _ (List.getElem_mem _)) this
  have hcl : object.graph.Adj ((F a :: l.map F).getLast (List.cons_ne_nil _ _)) (F a) := by
    simp only [← List.map_cons, List.getLast_map]
    have e1 : (a :: l).getLast (List.cons_ne_nil _ _) = (a :: l).getD ((a :: l).length - 1) 0 := by
      rw [List.getLast_eq_getElem, getD_eq_getElem (by simp)]
    rw [e1]
    have e2 : (a :: l).getD 0 0 = a := rfl
    rw [e2] at hclose
    exact hF _ _ (hlt _ (by rw [getD_eq_getElem (by simp)]; exact List.getElem_mem _))
      (hlt _ List.mem_cons_self) hclose
  obtain ⟨c, hc, hcl'⟩ := HubWin.list_cycle (F a) (l.map F) hmnd hch
    (by simp at hlen ⊢; omega) hcl
  exact ⟨F a, c, hc, by simpa using hcl'⟩

/-- A cycle of a power-of-two length refutes the dyadic target avoidance. -/
theorem hasCycle_of_walk {LengthOK : ℕ → Prop}
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {x : object.Vertex} (c : object.graph.Walk x x) (hc : c.IsCycle)
    (pow : Core.DyadicLength.PowerOfTwoLength c.length) :
    HasCycleWithLength LengthOK object :=
  ⟨⟨x, c, hc, (lengthLaw _).2 pow⟩⟩

end Hypostructure.Graph.WindowExchange
