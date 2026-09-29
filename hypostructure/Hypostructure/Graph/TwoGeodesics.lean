import Hypostructure.Graph.LadderRun

/-!
# Two geodesic paths in a graph (generic; `[144a]`, G audit S144a)

Vocabulary-free and application-free.  `w₁ : a₁ ⇝ b₁` and `w₂ : a₂ ⇝ b₂` are two paths of a
graph `G`, each a shortest path avoiding the edge joining its own ends (`GeodesicDetours`), and
neither uses the other's end edge (`E1`, `E2`).  Then, in terms of positions on the two paths:

* `common_iso`: two common vertices are at the same distance on both paths (the common part of
  the two walks is an isometry);
* `rung_offset`: a rung `w₁ j — w₂ q` between vertices off the other path is within one of the
  offset of every common vertex (`| |j − t| − |q − p| | ≤ 1`);
* `bubble_exc`: between two consecutive common vertices `t < t'` with `t + 2 ≤ t'` some interior
  vertex of `w₁` is exceptional: non-cubic, or joined to a vertex of the exceptional set `S`
  (the ends of `w₂`, the non-cubic vertices, the cubic vertices off both paths);
* `ovDiv_card_le`: the meeting points are at most `2|Exc| + 4`.
-/

namespace Hypostructure.Graph.TwoGeodesics

open Hypostructure.Graph.PathChords
open Hypostructure.Graph.WalkIndex
open Hypostructure.Graph.LadderRun

universe u

section Seg

variable {V : Type u} {G : SimpleGraph V}

/-- **A segment of a walk between two indices** (in either order). -/
theorem seg_walk {a b : V} (w : G.Walk a b) (i j : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length) :
    ∃ r : G.Walk (w.getVert i) (w.getVert j),
      r.length = max i j - min i j ∧ ∀ ε ∈ r.edges, ε ∈ w.edges := by
  rcases le_total i j with h | h
  · obtain ⟨u, v, p1, p2, p3, hu, hv, hw, hl1, hl2⟩ := exists_decomp_idx w i j h hj
    subst hu hv
    refine ⟨p2, by omega, fun ε hε => ?_⟩
    rw [hw]
    simp [SimpleGraph.Walk.edges_append, hε]
  · obtain ⟨u, v, p1, p2, p3, hu, hv, hw, hl1, hl2⟩ := exists_decomp_idx w j i h hi
    subst hu hv
    refine ⟨p2.reverse, by simp [SimpleGraph.Walk.length_reverse]; omega, fun ε hε => ?_⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hε
    rw [hw]
    simp [SimpleGraph.Walk.edges_append, hε]

end Seg

section Geo

variable {V : Type u} {G : SimpleGraph V} {a1 b1 a2 b2 : V}

/-- **The hypotheses on the two paths.** -/
structure Geo2 (G : SimpleGraph V) (LengthOK : ℕ → Prop) (Cubic : V → Prop)
    (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) : Prop where
  stub : ∀ x, Cubic x → ∀ a b, G.Adj x a → G.Adj x b → a ≠ b →
    ∃ s, G.Adj x s ∧ s ≠ a ∧ s ≠ b ∧ ∀ t, G.Adj x t → t = a ∨ t = b ∨ t = s
  avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length
  ok4 : LengthOK 4
  hp1 : w1.IsPath
  hp2 : w2.IsPath
  det1 : GeodesicDetours s(a1, b1) w1
  det2 : GeodesicDetours s(a2, b2) w2
  E1 : ∀ ε ∈ w2.edges, ε ≠ s(a1, b1)
  E2 : ∀ ε ∈ w1.edges, ε ≠ s(a2, b2)

variable {LengthOK : ℕ → Prop} {Cubic : V → Prop} {w1 : G.Walk a1 b1} {w2 : G.Walk a2 b2}

/-- **Common vertices are no farther apart on `w₂` than on `w₁`.** -/
theorem common_dist_le (H : Geo2 G LengthOK Cubic w1 w2) {t t' p p' : ℕ} (ht : t ≤ w1.length)
    (ht' : t' ≤ w1.length) (hp : p ≤ w2.length) (hp' : p' ≤ w2.length)
    (h1 : w1.getVert t = w2.getVert p) (h2 : w1.getVert t' = w2.getVert p') :
    p ≤ p' + (max t t' - min t t') ∧ p' ≤ p + (max t t' - min t t') := by
  obtain ⟨r, hr, hedges⟩ := seg_walk w1 t t' ht ht'
  let r' : G.Walk (w2.getVert p) (w2.getVert p') := r.copy h1 h2
  have := idx_dist_le H.det2 hp hp' r' (fun ε hε => H.E2 ε (hedges ε (by simpa [r'] using hε)))
  simpa [r', hr] using this

/-- **Common vertices are no farther apart on `w₁` than on `w₂`.** -/
theorem common_dist_le' (H : Geo2 G LengthOK Cubic w1 w2) {t t' p p' : ℕ} (ht : t ≤ w1.length)
    (ht' : t' ≤ w1.length) (hp : p ≤ w2.length) (hp' : p' ≤ w2.length)
    (h1 : w1.getVert t = w2.getVert p) (h2 : w1.getVert t' = w2.getVert p') :
    t ≤ t' + (max p p' - min p p') ∧ t' ≤ t + (max p p' - min p p') := by
  obtain ⟨r, hr, hedges⟩ := seg_walk w2 p p' hp hp'
  let r' : G.Walk (w1.getVert t) (w1.getVert t') := r.copy h1.symm h2.symm
  have := idx_dist_le H.det1 ht ht' r' (fun ε hε => H.E1 ε (hedges ε (by simpa [r'] using hε)))
  simpa [r', hr] using this

/-- **The common part is an isometry.** -/
theorem common_iso (H : Geo2 G LengthOK Cubic w1 w2) {t t' p p' : ℕ} (ht : t ≤ w1.length)
    (ht' : t' ≤ w1.length) (hp : p ≤ w2.length) (hp' : p' ≤ w2.length)
    (h1 : w1.getVert t = w2.getVert p) (h2 : w1.getVert t' = w2.getVert p') :
    max t t' - min t t' = max p p' - min p p' := by
  have a := common_dist_le H ht ht' hp hp' h1 h2
  have b := common_dist_le' H ht ht' hp hp' h1 h2
  omega

/-- **A rung is within one of the offset of every common vertex.** -/
theorem rung_offset (H : Geo2 G LengthOK Cubic w1 w2) {t p j q : ℕ} (ht : t ≤ w1.length)
    (hp : p ≤ w2.length) (hj : j ≤ w1.length) (hq : q ≤ w2.length)
    (h1 : w1.getVert t = w2.getVert p) (hjo : w1.getVert j ∉ w2.support)
    (hqo : w2.getVert q ∉ w1.support) (hadj : G.Adj (w1.getVert j) (w2.getVert q)) :
    max j t - min j t ≤ (max q p - min q p) + 1 ∧
      max q p - min q p ≤ (max j t - min j t) + 1 := by
  constructor
  · obtain ⟨r, hr, hedges⟩ := seg_walk w2 p q hp hq
    let d : G.Walk (w1.getVert t) (w1.getVert j) :=
      (r.copy h1.symm rfl).append (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)
    have hd : ∀ ε ∈ d.edges, ε ≠ s(a1, b1) := by
      intro ε hε
      simp only [d, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hε
      rcases hε with h | h
      · exact H.E1 ε (hedges ε h)
      · rw [h]; exact (edge_ne_of_notMem hqo).1
    have := idx_dist_le H.det1 ht hj d hd
    simp only [d, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hr] at this
    omega
  · obtain ⟨r, hr, hedges⟩ := seg_walk w1 t j ht hj
    let d : G.Walk (w2.getVert p) (w2.getVert q) :=
      (r.copy h1 rfl).append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    have hd : ∀ ε ∈ d.edges, ε ≠ s(a2, b2) := by
      intro ε hε
      simp only [d, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hε
      rcases hε with h | h
      · exact H.E2 ε (hedges ε h)
      · rw [h]; exact (edge_ne_of_notMem hjo).1
    have := idx_dist_le H.det2 hp hq d hd
    simp only [d, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hr] at this
    omega

end Geo

section Bubble

variable {V : Type u} {G : SimpleGraph V} {a1 b1 a2 b2 : V}
variable {LengthOK : ℕ → Prop} {Cubic : V → Prop} {w1 : G.Walk a1 b1} {w2 : G.Walk a2 b2}

/-- **A position of `w₁` is exceptional** for the finset `S`: its vertex is non-cubic, or it is
adjacent to a vertex of `S` off `w₁`. -/
def ExcS (Cubic : V → Prop) (w1 : G.Walk a1 b1) (S : Finset V) (s : ℕ) : Prop :=
  ¬ Cubic (w1.getVert s) ∨ ∃ z ∈ S, z ∉ w1.support ∧ G.Adj (w1.getVert s) z

/-- the increasing chain of stub images -/
theorem chain_bound (t t' : ℕ) (π : ℕ → ℤ) (h0 : ∀ s, t < s → s < t' → (t : ℤ) < π s)
    (hstep : ∀ s, t < s → s + 1 < t' → π s + 2 ≤ π (s + 1)) :
    ∀ k, 1 ≤ k → t + k < t' → (t : ℤ) + 2 * k - 1 ≤ π (t + k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hk
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := h0 (t + 1) (by omega) (by omega)
      simp only [Nat.zero_add]
      push_cast
      omega
    · have := ih h (by omega)
      have h2 := hstep (t + k) (by omega) (by omega)
      have e : t + (k + 1) = t + k + 1 := by omega
      rw [e]
      push_cast
      omega

/-- adjacency of consecutive positions -/
theorem adj_pos {a b : V} (w : G.Walk a b) {i : ℕ} (h : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := w.adj_getVert_succ h

/-- **A 4-cycle is not accepted.** -/
theorem no_four_cycle (H : Geo2 G LengthOK Cubic w1 w2) {u x v y : V} (hux : G.Adj u x)
    (hxv : G.Adj x v) (hvy : G.Adj v y) (hyu : G.Adj y u) (huv : u ≠ v) (hxy : x ≠ y)
    (hxu : x ≠ u) (hxv' : x ≠ v) (hyu' : y ≠ u) (hyv : y ≠ v) : False := by
  have n1 := hxu.symm
  have n2 := huv.symm
  have n3 := hxy.symm
  have n4 := hxv'.symm
  have n5 := hyu'.symm
  have n6 := hyv.symm
  let p : G.Walk u v := SimpleGraph.Walk.cons hux (SimpleGraph.Walk.cons hxv SimpleGraph.Walk.nil)
  let q : G.Walk v u := SimpleGraph.Walk.cons hvy (SimpleGraph.Walk.cons hyu SimpleGraph.Walk.nil)
  have hp : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp only [p, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, not_or]
    tauto
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, not_or]
    tauto
  obtain ⟨c, hc, hl⟩ := ear_cycle p q hp hq (by
    intro z hzp hzq
    simp only [p, q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hzp hzq
    rcases hzp with h | h | h
    · left; exact h
    · rcases hzq with h' | h' | h'
      · right; exact h'
      · exact absurd (h.symm.trans h') hxy
      · left; exact h'
    · right; exact h) (by simp [p]) (by simp [q]) (by simp [p, q])
  exact H.avoids ⟨u, c, hc, by
    have : c.length = 4 := by simp [hl, p, q]
    rw [this]; exact H.ok4⟩

/-- **Every bubble contains an exceptional vertex.**  Between two consecutive common vertices
`t < t'` of the two paths (`t + 2 ≤ t'`, everything strictly between off `w₂`) some interior
vertex of `w₁` is non-cubic or adjacent to a vertex of `S` off `w₁`.  Here `S` contains the
ends of `w₂`, the non-cubic vertices and the cubic vertices off both paths. -/
theorem bubble_exc (H : Geo2 G LengthOK Cubic w1 w2) (S : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ S)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ S)
    (ha : a2 ∈ S) (hb : b2 ∈ S)
    {t t' p p' : ℕ} (htt : t + 2 ≤ t') (ht' : t' ≤ w1.length) (hp : p ≤ w2.length)
    (hp' : p' ≤ w2.length)
    (h1 : w1.getVert t = w2.getVert p) (h2 : w1.getVert t' = w2.getVert p')
    (hoff : ∀ s, t < s → s < t' → w1.getVert s ∉ w2.support) :
    ∃ s, t < s ∧ s < t' ∧ ExcS Cubic w1 S s := by
  classical
  by_contra hno
  push Not at hno
  have hno' : ∀ s, t < s → s < t' → Cubic (w1.getVert s) ∧
      ∀ z ∈ S, z ∉ w1.support → ¬ G.Adj (w1.getVert s) z := by
    intro s hs1 hs2
    have := hno s hs1 hs2
    unfold ExcS at this
    push Not at this
    exact this
  -- the stub of each interior vertex lies in the interior of `w₂`
  have hex : ∀ s : ℕ, ∃ q : ℕ, t < s → s < t' → (0 < q ∧ q < w2.length ∧
      G.Adj (w1.getVert s) (w2.getVert q) ∧ w2.getVert q ∉ w1.support ∧
      Cubic (w2.getVert q)) := by
    intro s
    by_cases hs : t < s ∧ s < t'
    · obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨hc, hnS⟩ := hno' s hs1 hs2
      have hpred : G.Adj (w1.getVert s) (w1.getVert (s - 1)) := by
        have := w1.adj_getVert_succ (i := s - 1) (by omega)
        have e : s - 1 + 1 = s := by omega
        rw [e] at this
        exact this.symm
      have hsucc : G.Adj (w1.getVert s) (w1.getVert (s + 1)) := w1.adj_getVert_succ (by omega)
      have hpne : w1.getVert (s - 1) ≠ w1.getVert (s + 1) := by
        intro h
        have := getVert_inj H.hp1 (by omega) (by omega) h
        omega
      obtain ⟨z, hz_adj, hzp, hzs, hall⟩ := H.stub _ hc _ _ hpred hsucc hpne
      have hz_off : z ∉ w1.support := by
        intro hz
        rcases induced_nbrs H.hp1 H.det1 (by omega) (by omega) hz hz_adj with h | h
        · exact hzp h
        · exact hzs h
      have hzS : z ∉ S := fun hzS => hnS z hzS hz_off hz_adj
      have hzc : Cubic z := by
        by_contra h
        exact hzS (hX z h)
      have hz2 : z ∈ w2.support := by
        by_contra h
        exact hzS (hU z hzc hz_off h)
      obtain ⟨q, hq, hql⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz2
      have hq0 : q ≠ 0 := by
        intro h0
        apply hzS
        rw [← hq, h0, SimpleGraph.Walk.getVert_zero]
        exact ha
      have hql' : q ≠ w2.length := by
        intro h0
        apply hzS
        rw [← hq, h0, SimpleGraph.Walk.getVert_length]
        exact hb
      refine ⟨q, fun _ _ => ⟨by omega, by omega, ?_, ?_, ?_⟩⟩
      · rw [hq]; exact hz_adj
      · rw [hq]; exact hz_off
      · rw [hq]; exact hzc
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩
  choose q hq using hex
  -- the two ends
  have hiso := common_iso H (by omega) ht' hp hp' h1 h2
  have hu_mem : w1.getVert t ∈ w1.support := SimpleGraph.Walk.getVert_mem_support _ _
  have hv_mem : w1.getVert t' ∈ w1.support := SimpleGraph.Walk.getVert_mem_support _ _
  -- the rung offsets
  have hoffs : ∀ s, t < s → s < t' →
      (max s t - min s t ≤ (max (q s) p - min (q s) p) + 1 ∧
        max (q s) p - min (q s) p ≤ (max s t - min s t) + 1) ∧
      (max s t' - min s t' ≤ (max (q s) p' - min (q s) p') + 1 ∧
        max (q s) p' - min (q s) p' ≤ (max s t' - min s t') + 1) ∧
      q s ≠ p ∧ q s ≠ p' := by
    intro s hs1 hs2
    obtain ⟨hq0, hql, hadj, hoq, -⟩ := hq s hs1 hs2
    refine ⟨rung_offset H (by omega) hp (by omega) (by omega) h1 (hoff s hs1 hs2) hoq hadj,
      rung_offset H ht' hp' (by omega) (by omega) h2 (hoff s hs1 hs2) hoq hadj, ?_, ?_⟩
    · intro h
      apply hoq
      rw [h, ← h1]; exact hu_mem
    · intro h
      apply hoq
      rw [h, ← h2]; exact hv_mem
  -- the image coordinate
  let π : ℕ → ℤ := fun s => if p ≤ p' then (t : ℤ) + ((q s : ℤ) - p) else (t : ℤ) + ((p : ℤ) - q s)
  have hπ : ∀ s, t < s → s < t' → (t : ℤ) < π s ∧ π s < t' ∧ π s - s ≤ 1 ∧ (s : ℤ) - π s ≤ 1 := by
    intro s hs1 hs2
    obtain ⟨o1, o2, n1, n2⟩ := hoffs s hs1 hs2
    simp only [π]
    split_ifs with hpp <;> omega
  have hstep : ∀ s, t < s → s + 1 < t' → π s + 2 ≤ π (s + 1) := by
    intro s hs1 hs2
    obtain ⟨-, -, hadj, -, -⟩ := hq s hs1 (by omega)
    obtain ⟨hq0', hql', hadj', hoq', hcub'⟩ := hq (s + 1) (by omega) hs2
    obtain ⟨hq0, hql, -, -, hcub⟩ := hq s hs1 (by omega)
    have hne : q s ≠ q (s + 1) := by
      intro h
      have := nbr_outside_unique Cubic H.stub H.hp2 hq0 hql hcub (hoff s hs1 (by omega))
        (hoff (s + 1) (by omega) hs2) hadj.symm (by rw [h]; exact hadj'.symm)
      have := getVert_inj H.hp1 (by omega) (by omega) this
      omega
    have hc4 : max (q s) (q (s + 1)) - min (q s) (q (s + 1)) ≠ 1 := by
      intro h1'
      have rc := rungCycles_of_avoids w1 w2 H.hp1 H.hp2 H.avoids
      have := rung_not_ok (LengthOK := LengthOK) rc (s1 := s) (s2 := s + 1)
        (t1 := q s) (t2 := q (s + 1)) (by omega) (by omega) hne (by omega) (by omega)
        (fun x hx1 hx2 => hoff x (by omega) (by omega)) hadj hadj'
      apply this
      have e : s + 1 - s + (max (q s) (q (s + 1)) - min (q s) (q (s + 1))) + 2 = 4 := by omega
      rw [e]; exact H.ok4
    obtain ⟨-, -, a1', a2'⟩ := hπ s hs1 (by omega)
    obtain ⟨-, -, b1', b2'⟩ := hπ (s + 1) (by omega) hs2
    simp only [π] at a1' a2' b1' b2' ⊢
    split_ifs at * <;> omega
  by_cases hd : 3 ≤ t' - t
  · have := chain_bound t t' π (fun s h1 h2 => (hπ s h1 h2).1) hstep (t' - t - 1) (by omega)
      (by omega)
    have h3 := hπ (t + (t' - t - 1)) (by omega) (by omega)
    omega
  · -- `t' = t + 2`: a four-cycle
    have hd2 : t' = t + 2 := by omega
    subst hd2
    obtain ⟨o1, o2, n1, n2⟩ := hoffs (t + 1) (by omega) (by omega)
    obtain ⟨hq0, hql, hadj, hoq, -⟩ := hq (t + 1) (by omega) (by omega)
    have hπ1 := hπ (t + 1) (by omega) (by omega)
    have hpp : (p : ℤ) ≠ p' := by
      intro h
      have : p = p' := by exact_mod_cast h
      subst this
      omega
    have hy_u : G.Adj (w2.getVert p) (w2.getVert (q (t + 1))) ∨
        G.Adj (w2.getVert (q (t + 1))) (w2.getVert p) := by
      have hd1 : q (t + 1) = p + 1 ∨ q (t + 1) + 1 = p := by
        simp only [π] at hπ1
        split_ifs at hπ1 <;> omega
      rcases hd1 with e | e
      · left; rw [e]; exact adj_pos w2 (by omega)
      · right; rw [← e]; exact adj_pos w2 (by omega)
    have hy_v : G.Adj (w2.getVert p') (w2.getVert (q (t + 1))) ∨
        G.Adj (w2.getVert (q (t + 1))) (w2.getVert p') := by
      have hd1 : q (t + 1) = p' + 1 ∨ q (t + 1) + 1 = p' := by
        simp only [π] at hπ1
        split_ifs at hπ1 <;> omega
      rcases hd1 with e | e
      · left; rw [e]; exact adj_pos w2 (by omega)
      · right; rw [← e]; exact adj_pos w2 (by omega)
    have hyu : G.Adj (w2.getVert (q (t + 1))) (w1.getVert t) := by
      rw [h1]; rcases hy_u with h | h
      · exact h.symm
      · exact h
    have hyv : G.Adj (w1.getVert (t + 2)) (w2.getVert (q (t + 1))) := by
      rw [h2]; rcases hy_v with h | h
      · exact h
      · exact h.symm
    have hux : G.Adj (w1.getVert t) (w1.getVert (t + 1)) := adj_pos w1 (by omega)
    have hxv : G.Adj (w1.getVert (t + 1)) (w1.getVert (t + 2)) := adj_pos w1 (by omega)
    refine no_four_cycle H hux hxv hyv.symm.symm hyu ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := getVert_inj H.hp1 (by omega) (by omega) h
      omega
    · intro h
      exact hoff (t + 1) (by omega) (by omega) (h ▸ SimpleGraph.Walk.getVert_mem_support _ _)
    · intro h
      have := getVert_inj H.hp1 (by omega) (by omega) h
      omega
    · intro h
      have := getVert_inj H.hp1 (by omega) (by omega) h
      omega
    · intro h
      apply hoq
      rw [h]; exact hu_mem
    · intro h
      apply hoq
      rw [h]; exact hv_mem

end Bubble

end Hypostructure.Graph.TwoGeodesics
