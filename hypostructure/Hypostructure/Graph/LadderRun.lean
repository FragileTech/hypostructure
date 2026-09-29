import Hypostructure.Graph.PathChords
import Hypostructure.Graph.WalkIndex
import Hypostructure.Graph.LadderWindow

/-!
# A run of twelve rungs into a geodesic walk has a free neighbour (`[144a]`, G audit S144a)

Vocabulary-free.  `w₁`, `w₂` are two paths of a graph `G`, each a shortest path avoiding the
edge joining its own ends (`GeodesicDetours`).  A *run* is twelve consecutive interior vertices
`v_j = w₁.getVert (m + j)` of `w₁`, cubic, off `w₂`, each joined by its stub to a cubic interior
vertex `q_j = w₂.getVert (σ j)` off `w₁`.  Then a neighbour position `σ r ± 1` of one of the two
deep rungs `r = 5, 6` on `w₂` is *exceptional*: an end of `w₂`, a non-cubic vertex, or a vertex
whose stub is non-cubic, an end of `w₁`, or off `w₁`.  This is the window lemma of
`LadderWindow.lean` fed by the geodesic detours and the rung cycles.
-/

namespace Hypostructure.Graph.LadderRun

open Hypostructure.Graph.PathChords
open Hypostructure.Graph.WalkIndex

universe u

section Basic

variable {V : Type u} {G : SimpleGraph V}

/-- **Index distance is bounded by any detour** (shortest path avoiding `e`). -/
theorem idx_dist_le {e : Sym2 V} {a b : V} {w : G.Walk a b} (det : GeodesicDetours e w)
    {s t : ℕ} (hs : s ≤ w.length) (ht : t ≤ w.length)
    (r : G.Walk (w.getVert s) (w.getVert t)) (hr : ∀ ε ∈ r.edges, ε ≠ e) :
    s ≤ t + r.length ∧ t ≤ s + r.length := by
  rcases le_total s t with hst | hts
  · obtain ⟨u, v, p1, p2, p3, hu, hv, hw, hl1, hl2⟩ := exists_decomp_idx w s t hst ht
    subst hu hv
    have := det _ _ p1 p2 p3 r hw hr
    omega
  · obtain ⟨u, v, p1, p2, p3, hu, hv, hw, hl1, hl2⟩ := exists_decomp_idx w t s hts hs
    subst hu hv
    have hr' : ∀ ε ∈ r.reverse.edges, ε ≠ e := by
      intro ε hε
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hε
      exact hr ε hε
    have := det _ _ p1 p2 p3 r.reverse hw hr'
    simp only [SimpleGraph.Walk.length_reverse] at this
    omega

theorem getVert_inj {a b : V} {w : G.Walk a b} (hp : w.IsPath) {s t : ℕ} (hs : s ≤ w.length)
    (ht : t ≤ w.length) (h : w.getVert s = w.getVert t) : s = t :=
  hp.getVert_injOn (by simpa using hs) (by simpa using ht) h

theorem ends_ne {a b : V} {w : G.Walk a b} (hp : w.IsPath) {y : ℕ} (h0 : 0 < y)
    (hl : y < w.length) : w.getVert y ≠ a ∧ w.getVert y ≠ b := by
  constructor
  · intro h
    have := getVert_inj hp (le_of_lt hl) (Nat.zero_le _) (by rw [h, SimpleGraph.Walk.getVert_zero])
    omega
  · intro h
    have := getVert_inj hp (le_of_lt hl) le_rfl (by rw [h, SimpleGraph.Walk.getVert_length])
    omega

/-- The edge from an interior vertex is never the port edge `s(a, b)`. -/
theorem edge_ne_ends {a b : V} {w : G.Walk a b} (hp : w.IsPath) {y : ℕ} (h0 : 0 < y)
    (hl : y < w.length) (z : V) : s(w.getVert y, z) ≠ s(a, b) := by
  intro h
  rw [Sym2.eq_iff] at h
  obtain ⟨n1, n2⟩ := ends_ne hp h0 hl
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact n1 h1
  · exact n2 h1

/-- **An interior vertex of a geodesic path has only its two path neighbours on the path.** -/
theorem induced_nbrs {a b : V} {w : G.Walk a b} (hp : w.IsPath) (det : GeodesicDetours s(a, b) w)
    {y : ℕ} (h0 : 0 < y) (hl : y < w.length) {z : V} (hz : z ∈ w.support)
    (hadj : G.Adj (w.getVert y) z) : z = w.getVert (y - 1) ∨ z = w.getVert (y + 1) := by
  obtain ⟨t, ht, htl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz
  subst ht
  let r : G.Walk (w.getVert y) (w.getVert t) := SimpleGraph.Walk.cons hadj .nil
  have hr : ∀ ε ∈ r.edges, ε ≠ s(a, b) := by
    intro ε hε
    simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hε
    subst hε
    exact edge_ne_ends hp h0 hl _
  have hd := idx_dist_le det (le_of_lt hl) htl r hr
  have hne : t ≠ y := by
    intro h; subst h; exact hadj.ne rfl
  simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hd
  have : t = y - 1 ∨ t = y + 1 := by omega
  rcases this with h | h
  · left; rw [h]
  · right; rw [h]

end Basic


section Hyp

variable {V : Type u} {G : SimpleGraph V}

theorem edge_ne_of_notMem {a b x y : V} {w : G.Walk a b} (hx : x ∉ w.support) :
    s(x, y) ≠ s(a, b) ∧ s(y, x) ≠ s(a, b) := by
  constructor
  · intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hx (h1 ▸ w.start_mem_support)
    · exact hx (h1 ▸ w.end_mem_support)
  · intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact hx (h1 ▸ w.end_mem_support)
    · exact hx (h1 ▸ w.start_mem_support)

/-- A cubic interior vertex of a path has at most one neighbour off the path. -/
theorem nbr_outside_unique {V : Type u} {G : SimpleGraph V} (Cubic : V → Prop)
    (stub : ∀ m, Cubic m → ∀ a b, G.Adj m a → G.Adj m b → a ≠ b →
      ∃ s, G.Adj m s ∧ s ≠ a ∧ s ≠ b ∧ ∀ t, G.Adj m t → t = a ∨ t = b ∨ t = s)
    {a b : V} {w : G.Walk a b} (hp : w.IsPath) {y : ℕ} (h0 : 0 < y) (hl : y < w.length)
    (hc : Cubic (w.getVert y)) {z1 z2 : V} (h1 : z1 ∉ w.support) (h2 : z2 ∉ w.support)
    (a1 : G.Adj (w.getVert y) z1) (a2 : G.Adj (w.getVert y) z2) : z1 = z2 := by
  have hpred : G.Adj (w.getVert y) (w.getVert (y - 1)) := by
    have := w.adj_getVert_succ (i := y - 1) (by omega)
    have e : y - 1 + 1 = y := by omega
    rw [e] at this
    exact this.symm
  have hsucc : G.Adj (w.getVert y) (w.getVert (y + 1)) := w.adj_getVert_succ hl
  have hne : w.getVert (y - 1) ≠ w.getVert (y + 1) := by
    intro h
    have := getVert_inj hp (by omega) (by omega) h
    omega
  obtain ⟨s, -, -, -, hall⟩ := stub _ hc _ _ hpred hsucc hne
  have mem1 : w.getVert (y - 1) ∈ w.support := SimpleGraph.Walk.getVert_mem_support _ _
  have mem2 : w.getVert (y + 1) ∈ w.support := SimpleGraph.Walk.getVert_mem_support _ _
  rcases hall z1 a1 with e | e | e
  · exact absurd (e ▸ mem1) h1
  · exact absurd (e ▸ mem2) h1
  · rcases hall z2 a2 with e' | e' | e'
    · exact absurd (e' ▸ mem1) h2
    · exact absurd (e' ▸ mem2) h2
    · rw [e, e']

/-- **Rung cycle bound at indices.** -/
theorem rung_not_ok {LengthOK : Nat → Prop} {a1 b1 a2 b2 : V} {w1 : G.Walk a1 b1}
    {w2 : G.Walk a2 b2} (rc : RungCycles LengthOK w1 w2) {s1 s2 t1 t2 : ℕ} (hs : s1 < s2)
    (hs2 : s2 ≤ w1.length) (ht : t1 ≠ t2) (ht1 : t1 ≤ w2.length) (ht2 : t2 ≤ w2.length)
    (hdis : ∀ x, s1 ≤ x → x ≤ s2 → w1.getVert x ∉ w2.support)
    (hA : G.Adj (w1.getVert s1) (w2.getVert t1)) (hB : G.Adj (w1.getVert s2) (w2.getVert t2)) :
    ¬ LengthOK ((s2 - s1) + (max t1 t2 - min t1 t2) + 2) := by
  obtain ⟨u, v, p1, p2, p3, hu, hv, hw, hl1, hl2⟩ := exists_decomp_idx w1 s1 s2 hs.le hs2
  have hdisj : ∀ (q2support : V → Prop), (∀ y, q2support y → y ∈ w2.support) →
      ∀ y, y ∈ p2.support → q2support y → False := by
    intro P hP y hy hPy
    obtain ⟨s', hs', hy'⟩ := mem_segment_support hw hy
    rw [hl1] at hy'
    exact hdis (s1 + s') (by omega) (by omega) (hy' ▸ hP y hPy)
  subst hu hv
  rcases lt_or_gt_of_ne ht with h | h
  · obtain ⟨c, d, q1, q2, q3, hc, hd, hw2, hl3, hl4⟩ :=
      exists_decomp_idx w2 t1 t2 h.le ht2
    subst hc hd
    have := rc _ _ _ _ p1 p2 p3 q1 q2 q3 hw hw2 (by omega) (by omega)
      (hdisj (· ∈ q2.support) (fun y hy => by
        obtain ⟨s', -, hy'⟩ := mem_segment_support hw2 hy
        rw [hy']; exact SimpleGraph.Walk.getVert_mem_support _ _))
      (Or.inr ⟨hB, hA.symm⟩)
    have e1 : max t1 t2 - min t1 t2 = t2 - t1 := by omega
    rw [e1, ← hl2, ← hl4]; exact this
  · obtain ⟨c, d, q1, q2, q3, hc, hd, hw2, hl3, hl4⟩ :=
      exists_decomp_idx w2 t2 t1 h.le ht1
    subst hc hd
    have := rc _ _ _ _ p1 p2 p3 q1 q2 q3 hw hw2 (by omega) (by omega)
      (hdisj (· ∈ q2.support) (fun y hy => by
        obtain ⟨s', -, hy'⟩ := mem_segment_support hw2 hy
        rw [hy']; exact SimpleGraph.Walk.getVert_mem_support _ _))
      (Or.inl ⟨hB, hA.symm⟩)
    have e1 : max t1 t2 - min t1 t2 = t1 - t2 := by omega
    rw [e1, ← hl2, ← hl4]; exact this

end Hyp


section RunLemma

variable {V : Type u} {G : SimpleGraph V}

/-- The data of a run of twelve rungs. -/
structure RunHyp (G : SimpleGraph V) (LengthOK : Nat → Prop) (Cubic : V → Prop)
    {a1 b1 a2 b2 : V} (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) (m : ℕ) (σ : ℕ → ℕ) : Prop where
  stub : ∀ x, Cubic x → ∀ a b, G.Adj x a → G.Adj x b → a ≠ b →
    ∃ s, G.Adj x s ∧ s ≠ a ∧ s ≠ b ∧ ∀ t, G.Adj x t → t = a ∨ t = b ∨ t = s
  avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length
  ok4 : LengthOK 4
  ok8 : LengthOK 8
  ok16 : LengthOK 16
  hp1 : w1.IsPath
  hp2 : w2.IsPath
  det1 : GeodesicDetours s(a1, b1) w1
  det2 : GeodesicDetours s(a2, b2) w2
  m_pos : 0 < m
  m_len : m + 12 ≤ w1.length
  v_cubic : ∀ j < 12, Cubic (w1.getVert (m + j))
  v_off : ∀ j < 12, w1.getVert (m + j) ∉ w2.support
  q_cubic : ∀ j < 12, Cubic (w2.getVert (σ j))
  q_off : ∀ j < 12, w2.getVert (σ j) ∉ w1.support
  q_pos : ∀ j < 12, 0 < σ j
  q_len : ∀ j < 12, σ j < w2.length
  rung : ∀ j < 12, G.Adj (w1.getVert (m + j)) (w2.getVert (σ j))

namespace RunHyp

variable {LengthOK : Nat → Prop} {Cubic : V → Prop} {a1 b1 a2 b2 : V} {w1 : G.Walk a1 b1}
  {w2 : G.Walk a2 b2} {m : ℕ} {σ : ℕ → ℕ}

theorem v_adj (R : RunHyp G LengthOK Cubic w1 w2 m σ) {j : ℕ} (hj : j + 1 < 12) :
    G.Adj (w1.getVert (m + j)) (w1.getVert (m + (j + 1))) := by
  have := w1.adj_getVert_succ (i := m + j) (by have := R.m_len; omega)
  simpa [Nat.add_assoc] using this

/-- consecutive rung positions are at most three apart -/
theorem step_le (R : RunHyp G LengthOK Cubic w1 w2 m σ) {j : ℕ} (hj : j + 1 < 12) :
    σ j ≤ σ (j + 1) + 3 ∧ σ (j + 1) ≤ σ j + 3 := by
  let r : G.Walk (w2.getVert (σ j)) (w2.getVert (σ (j + 1))) :=
    SimpleGraph.Walk.cons (R.rung j (by omega)).symm
      (SimpleGraph.Walk.cons (R.v_adj hj) (SimpleGraph.Walk.cons (R.rung (j + 1) hj) .nil))
  have hr : ∀ ε ∈ r.edges, ε ≠ s(a2, b2) := by
    intro ε hε
    simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hε
    rcases hε with rfl | rfl | rfl
    · exact (edge_ne_of_notMem (R.v_off j (by omega))).2
    · exact (edge_ne_of_notMem (R.v_off j (by omega))).1
    · exact (edge_ne_of_notMem (R.v_off (j + 1) hj)).1
  have := idx_dist_le R.det2 (le_of_lt (R.q_len j (by omega))) (le_of_lt (R.q_len (j + 1) hj)) r hr
  simpa [r] using this

theorem q_inj (R : RunHyp G LengthOK Cubic w1 w2 m σ) {i j : ℕ} (hi : i < 12) (hj : j < 12)
    (h : σ i = σ j) : i = j := by
  have := nbr_outside_unique Cubic R.stub R.hp2 (R.q_pos i hi) (R.q_len i hi) (R.q_cubic i hi)
    (R.v_off i hi) (R.v_off j hj) (R.rung i hi).symm (by rw [h]; exact (R.rung j hj).symm)
  have := getVert_inj R.hp1 (by have := R.m_len; omega) (by have := R.m_len; omega) this
  omega

theorem v_disjoint (R : RunHyp G LengthOK Cubic w1 w2 m σ) {i j x : ℕ} (hi : i ≤ x) (hx : x ≤ j)
    (hj : j < 12) : w1.getVert (m + x) ∉ w2.support := R.v_off x (by omega)

theorem rungCycles (R : RunHyp G LengthOK Cubic w1 w2 m σ) : RungCycles LengthOK w1 w2 :=
  rungCycles_of_avoids w1 w2 R.hp1 R.hp2 R.avoids

theorem pair_not_ok (R : RunHyp G LengthOK Cubic w1 w2 m σ) {i j : ℕ} (hij : i < j)
    (hj : j < 12) :
    ¬ LengthOK ((j - i) + (max (σ i) (σ j) - min (σ i) (σ j)) + 2) := by
  have := rung_not_ok (w1 := w1) (w2 := w2) R.rungCycles (s1 := m + i) (s2 := m + j)
    (t1 := σ i) (t2 := σ j) (by omega) (by have := R.m_len; omega)
    (fun h => by have := R.q_inj (by omega) hj h; omega)
    (le_of_lt (R.q_len i (by omega))) (le_of_lt (R.q_len j hj))
    (fun x h1 h2 => R.v_off (x - m) (by omega) |> fun h => by
      have e : m + (x - m) = x := by omega
      rwa [e] at h)
    (R.rung i (by omega)) (R.rung j hj)
  have e : m + j - (m + i) = j - i := by omega
  rwa [e] at this

theorem gap_ne_one (R : RunHyp G LengthOK Cubic w1 w2 m σ) {j : ℕ} (hj : j + 1 < 12) :
    σ (j + 1) ≠ σ j + 1 ∧ σ j ≠ σ (j + 1) + 1 := by
  have h := R.pair_not_ok (i := j) (j := j + 1) (by omega) hj
  constructor
  · intro e
    apply h
    have : max (σ j) (σ (j + 1)) - min (σ j) (σ (j + 1)) = 1 := by omega
    rw [this]
    have e2 : j + 1 - j = 1 := by omega
    rw [e2]; exact R.ok4
  · intro e
    apply h
    have : max (σ j) (σ (j + 1)) - min (σ j) (σ (j + 1)) = 1 := by omega
    rw [this]
    have e2 : j + 1 - j = 1 := by omega
    rw [e2]; exact R.ok4


end RunHyp

/-- **An exceptional position of the second walk**: an end, a non-cubic vertex, or a vertex
with a neighbour off the walk that is non-cubic, an end of the first walk, or off the first
walk. -/
def Exceptional (Cubic : V → Prop) {a1 b1 a2 b2 : V} (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2)
    (y : ℕ) : Prop :=
  y = 0 ∨ w2.length ≤ y ∨ ¬ Cubic (w2.getVert y) ∨
    ∃ s, G.Adj (w2.getVert y) s ∧ s ∉ w2.support ∧
      (¬ Cubic s ∨ s = a1 ∨ s = b1 ∨ s ∉ w1.support)

namespace RunHyp

variable {LengthOK : Nat → Prop} {Cubic : V → Prop} {a1 b1 a2 b2 : V} {w1 : G.Walk a1 b1}
  {w2 : G.Walk a2 b2} {m : ℕ} {σ : ℕ → ℕ}

/-- **Closure at a deep rung**: a non-exceptional neighbour position of a deep rung is the
position of a rung two or three indices away. -/
theorem closure (R : RunHyp G LengthOK Cubic w1 w2 m σ) {r : ℕ} (hr : r = 5 ∨ r = 6) {y : ℕ}
    (hy : y = σ r + 1 ∨ y + 1 = σ r) (hne : ¬ Exceptional Cubic w1 w2 y) :
    ∃ k, 2 ≤ k ∧ k < 10 ∧ σ k = y ∧ (k = r + 2 ∨ k = r + 3 ∨ r = k + 2 ∨ r = k + 3) := by
  have hr12 : r < 12 := by omega
  unfold Exceptional at hne
  push Not at hne
  obtain ⟨hy0, hylen, hycub, hstub⟩ := hne
  have hy0' : 0 < y := Nat.pos_of_ne_zero hy0
  have hqr_len := R.q_len r hr12
  -- adjacency of `q_y` and `q_r`
  have hyr : G.Adj (w2.getVert (σ r)) (w2.getVert y) := by
    rcases hy with h | h
    · have := w2.adj_getVert_succ (i := σ r) hqr_len
      rw [h]; exact this
    · have := w2.adj_getVert_succ (i := y) (by omega)
      rw [← h]; exact this.symm
  have hyne : y ≠ σ r := by omega
  -- the stub of `q_y`
  have hpred : G.Adj (w2.getVert y) (w2.getVert (y - 1)) := by
    have := w2.adj_getVert_succ (i := y - 1) (by omega)
    have e : y - 1 + 1 = y := by omega
    rw [e] at this
    exact this.symm
  have hsucc : G.Adj (w2.getVert y) (w2.getVert (y + 1)) := w2.adj_getVert_succ (by omega)
  have hpne : w2.getVert (y - 1) ≠ w2.getVert (y + 1) := by
    intro h
    have := getVert_inj R.hp2 (by omega) (by omega) h
    omega
  obtain ⟨s, hs_adj, hsp, hss, hall⟩ := R.stub _ hycub _ _ hpred hsucc hpne
  have hs_off : s ∉ w2.support := by
    intro hs
    rcases induced_nbrs R.hp2 R.det2 hy0' (by omega) hs hs_adj with h | h
    · exact hsp h
    · exact hss h
  obtain ⟨hs_cub, hsa, hsb, hs_w1⟩ := hstub s hs_adj hs_off
  obtain ⟨t, ht, htl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hs_w1
  subst ht
  have ht0 : t ≠ 0 := by
    intro h; apply hsa; rw [h, SimpleGraph.Walk.getVert_zero]
  have htl' : t ≠ w1.length := by
    intro h; apply hsb; rw [h, SimpleGraph.Walk.getVert_length]
  have hmlen := R.m_len
  -- detour `v_r – q_r – q_y – s` bounds `t`
  let d : G.Walk (w1.getVert (m + r)) (w1.getVert t) :=
    SimpleGraph.Walk.cons (R.rung r hr12) (SimpleGraph.Walk.cons hyr
      (SimpleGraph.Walk.cons hs_adj .nil))
  have hd : ∀ ε ∈ d.edges, ε ≠ s(a1, b1) := by
    intro ε hε
    simp only [d, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hε
    rcases hε with rfl | rfl | rfl
    · exact (edge_ne_of_notMem (R.q_off r hr12)).2
    · exact (edge_ne_of_notMem (R.q_off r hr12)).1
    · intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · exact hsb h
      · exact hsa h
  have hdist := idx_dist_le R.det1 (by omega) htl d hd
  simp only [d, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hdist
  -- so `t` lies in the run
  have hk_lo : m + 2 ≤ t := by omega
  have hk_hi : t ≤ m + 9 := by omega
  obtain ⟨k, rfl⟩ : ∃ k, t = m + k := ⟨t - m, by omega⟩
  have hk12 : k < 12 := by omega
  -- `q_y` is off `w1`
  have hy_off1 : w2.getVert y ∉ w1.support := by
    intro hin
    rcases induced_nbrs R.hp1 R.det1 (by omega) (by omega) hin hs_adj.symm with h | h
    · have := R.v_off (k - 1) (by omega)
      have e : m + (k - 1) = m + k - 1 := by omega
      rw [e] at this
      exact this (h ▸ SimpleGraph.Walk.getVert_mem_support _ _)
    · have := R.v_off (k + 1) (by omega)
      have e : m + (k + 1) = m + k + 1 := by omega
      rw [e] at this
      exact this (h ▸ SimpleGraph.Walk.getVert_mem_support _ _)
  have huniq : ∀ (z1 z2 : V), z1 ∉ w1.support → z2 ∉ w1.support →
      G.Adj (w1.getVert (m + k)) z1 → G.Adj (w1.getVert (m + k)) z2 → z1 = z2 := by
    intro z1 z2 h1 h2 a1' a2'
    exact nbr_outside_unique Cubic R.stub R.hp1 (by omega) (by omega) hs_cub h1 h2 a1' a2'
  -- `k ≠ r`
  have hkr : k ≠ r := by
    intro h
    subst h
    have := huniq _ _ (R.q_off k hr12) hy_off1 (R.rung k hr12) hs_adj.symm
    exact hyne (getVert_inj R.hp2 (by omega) (by omega) this.symm)
  -- `|k - r| ≠ 1`
  have hk1 : k ≠ r + 1 ∧ r ≠ k + 1 := by
    have rc := R.rungCycles
    constructor
    · intro h
      have := rung_not_ok rc (s1 := m + r) (s2 := m + k) (t1 := σ r) (t2 := y) (by omega)
        (by omega) (fun e => hyne e.symm) (by omega) (by omega)
        (fun x h1 h2 => by
          have := R.v_off (x - m) (by omega)
          have e : m + (x - m) = x := by omega
          rwa [e] at this)
        (R.rung r hr12) hs_adj.symm
      apply this
      have e1 : max (σ r) y - min (σ r) y = 1 := by omega
      have e2 : m + k - (m + r) = 1 := by omega
      rw [e1, e2]; exact R.ok4
    · intro h
      have := rung_not_ok rc (s1 := m + k) (s2 := m + r) (t1 := y) (t2 := σ r) (by omega)
        (by omega) (fun e => hyne e) (by omega) (by omega)
        (fun x h1 h2 => by
          have := R.v_off (x - m) (by omega)
          have e : m + (x - m) = x := by omega
          rwa [e] at this)
        hs_adj.symm (R.rung r hr12)
      apply this
      have e1 : max y (σ r) - min y (σ r) = 1 := by omega
      have e2 : m + r - (m + k) = 1 := by omega
      rw [e1, e2]; exact R.ok4
  -- the partner of `v_k`
  have hσk : σ k = y := by
    have := huniq _ _ (R.q_off k hk12) hy_off1 (R.rung k hk12) hs_adj.symm
    exact getVert_inj R.hp2 (le_of_lt (R.q_len k hk12)) (by omega) this
  refine ⟨k, by omega, by omega, hσk, ?_⟩
  omega


/-- **The run lemma.**  Twelve consecutive clean rungs of `w₁` into the geodesic walk `w₂`:
a neighbour position of one of the two deep rungs is exceptional. -/
theorem run_exceptional (R : RunHyp G LengthOK Cubic w1 w2 m σ) :
    ∃ r, (r = 5 ∨ r = 6) ∧ ∃ y : ℕ, (y = σ r + 1 ∨ y + 1 = σ r) ∧
      Exceptional Cubic w1 w2 y := by
  by_contra hno
  push Not at hno
  let τ : ℕ → ℤ := fun i => (σ (i + 2) : ℤ)
  have hstep : ∀ i < 7, τ (i + 1) - τ i = -3 ∨ τ (i + 1) - τ i = -2 ∨ τ (i + 1) - τ i = 2 ∨
      τ (i + 1) - τ i = 3 := by
    intro i hi
    have h1 := R.step_le (j := i + 2) (by omega)
    have h2 := R.gap_ne_one (j := i + 2) (by omega)
    have h3 : σ (i + 2 + 1) ≠ σ (i + 2) := fun h => by
      have := R.q_inj (by omega) (by omega) h; omega
    simp only [τ]
    have e : i + 1 + 2 = i + 2 + 1 := by omega
    rw [e]
    omega
  have hinj : LadderWindow.OkInj τ := by
    intro i hi j hj hij h
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    have := R.q_inj (i := i + 2) (j := j + 2) (by omega) (by omega) (by simpa [τ] using h)
    omega
  have hpair : LadderWindow.OkPair τ := by
    intro i hi j hj hij
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    have h := R.pair_not_ok (i := i + 2) (j := j + 2) (by omega) (by omega)
    have e : j + 2 - (i + 2) = j - i := by omega
    rw [e] at h
    have habs : |τ j - τ i| = ((max (σ (i + 2)) (σ (j + 2)) - min (σ (i + 2)) (σ (j + 2)) : ℕ) : ℤ) := by
      simp only [τ]
      rcases le_total (σ (i + 2)) (σ (j + 2)) with hle | hle
      · rw [max_eq_right hle, min_eq_left hle, abs_of_nonneg (by omega)]
        push_cast [Nat.cast_sub hle]; ring
      · rw [max_eq_left hle, min_eq_right hle, abs_of_nonpos (by omega)]
        push_cast [Nat.cast_sub hle]; ring
    rw [habs]
    refine ⟨fun h2 => ?_, fun h2 => ?_, fun h2 => ?_⟩
    · apply h
      have : (j - i) + (max (σ (i + 2)) (σ (j + 2)) - min (σ (i + 2)) (σ (j + 2))) + 2 = 4 := by
        omega
      rw [this]; exact R.ok4
    · apply h
      have : (j - i) + (max (σ (i + 2)) (σ (j + 2)) - min (σ (i + 2)) (σ (j + 2))) + 2 = 8 := by
        omega
      rw [this]; exact R.ok8
    · apply h
      have : (j - i) + (max (σ (i + 2)) (σ (j + 2)) - min (σ (i + 2)) (σ (j + 2))) + 2 = 16 := by
        omega
      rw [this]; exact R.ok16
  have hclosed : LadderWindow.OkClosed τ := by
    intro i hi h3 h4 e he
    have hi' := List.mem_range.1 hi
    have hr : i + 2 = 5 ∨ i + 2 = 6 := by omega
    have hpos := R.q_pos (i + 2) (by omega)
    have hyy : ∃ y : ℕ, (y : ℤ) = τ i + e ∧ (y = σ (i + 2) + 1 ∨ y + 1 = σ (i + 2)) := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨σ (i + 2) + 1, by simp [τ], Or.inl rfl⟩
      · exact ⟨σ (i + 2) - 1, by simp [τ]; omega, Or.inr (by omega)⟩
    obtain ⟨y, hy, hyrel⟩ := hyy
    have hne := hno (i + 2) hr y hyrel
    obtain ⟨k, hk2, hk10, hσk, hkrel⟩ := R.closure hr hyrel hne
    refine ⟨k - 2, List.mem_range.2 (by omega), ?_, by omega⟩
    have e2 : k - 2 + 2 = k := by omega
    simp only [τ, e2]
    rw [hσk] at *
    exact_mod_cast hy
  exact LadderWindow.window8 τ hstep ⟨hinj, hpair, hclosed⟩

end RunHyp

end RunLemma

end Hypostructure.Graph.LadderRun
