import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-!
# Index-based decompositions of walks (`[144a]`, G audit S144a)

Vocabulary-free.  `exists_decomp_idx`: for `i ≤ j ≤ |w|`, a walk `w` splits as
`p₁ ++ p₂ ++ p₃` with `p₁` of length `i`, `p₂` of length `j − i` from `w.getVert i` to
`w.getVert j`.  `mem_segment_support`: the vertices of `p₂` are `w.getVert (i + s)`,
`s ≤ |p₂|`.
-/

namespace Hypostructure.Graph.WalkIndex

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem exists_split {a b : V} (w : G.Walk a b) (k : ℕ) (hk : k ≤ w.length) :
    ∃ (u : V) (p : G.Walk a u) (q : G.Walk u b),
      u = w.getVert k ∧ w = p.append q ∧ p.length = k := by
  induction w generalizing k with
  | nil =>
    have : k = 0 := by simpa using hk
    subst this
    exact ⟨_, SimpleGraph.Walk.nil, SimpleGraph.Walk.nil, rfl, rfl, rfl⟩
  | cons h w' ih =>
    cases k with
    | zero => exact ⟨_, SimpleGraph.Walk.nil, SimpleGraph.Walk.cons h w', rfl, rfl, rfl⟩
    | succ k =>
      obtain ⟨u, p', q', hu, hw, hl⟩ := ih k (by simpa using hk)
      refine ⟨u, SimpleGraph.Walk.cons h p', q', ?_, ?_, by simp [hl]⟩
      · simpa using hu
      · rw [SimpleGraph.Walk.cons_append, ← hw]

theorem exists_decomp_idx {a b : V} (w : G.Walk a b) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ w.length) :
    ∃ (u v : V) (p1 : G.Walk a u) (p2 : G.Walk u v) (p3 : G.Walk v b),
      u = w.getVert i ∧ v = w.getVert j ∧ w = p1.append (p2.append p3) ∧
        p1.length = i ∧ p2.length = j - i := by
  obtain ⟨u, p1, q, hu, hw, hl⟩ := exists_split w i (le_trans hij hj)
  have hq : q.length = w.length - i := by
    have := congrArg SimpleGraph.Walk.length hw
    simp [SimpleGraph.Walk.length_append, hl] at this
    omega
  obtain ⟨v, p2, p3, hv, hq2, hl2⟩ := exists_split q (j - i) (by omega)
  have hget : v = w.getVert j := by
    rw [hv, hw, SimpleGraph.Walk.getVert_append]
    have : ¬ j < i := by omega
    simp only [hl, this, if_false]
  refine ⟨u, v, p1, p2, p3, hu, hget, ?_, hl, hl2⟩
  rw [hw, hq2, SimpleGraph.Walk.append_assoc]

/-- the vertices of a segment are the vertices of the walk at the segment's indices -/
theorem mem_segment_support {a b u v : V} {w : G.Walk a b} {p1 : G.Walk a u}
    {p2 : G.Walk u v} {p3 : G.Walk v b} (hw : w = p1.append (p2.append p3)) {y : V}
    (hy : y ∈ p2.support) :
    ∃ s, s ≤ p2.length ∧ y = w.getVert (p1.length + s) := by
  obtain ⟨s, hs, hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hy
  refine ⟨s, hle, ?_⟩
  subst hw
  rw [SimpleGraph.Walk.getVert_append]
  have h1 : ¬ p1.length + s < p1.length := by omega
  simp only [h1, if_false, Nat.add_sub_cancel_left, SimpleGraph.Walk.getVert_append]
  by_cases h2 : s < p2.length
  · simp [h2, hs]
  · have : s = p2.length := by omega
    subst this
    simp [SimpleGraph.Walk.getVert_length, ← hs]

end Hypostructure.Graph.WalkIndex
