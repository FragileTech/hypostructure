import Hypostructure.Graph.LadderG
import Hypostructure.Graph.WalkAttachment
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Hubs escape to the vertices off two geodesic walks (`[144a]` exchange attack)

Vocabulary-free.  `w₁ : a₁ ⇝ b₁`, `w₂ : a₂ ⇝ b₂` are two triangular port walks of a finite
object (`bᵢ ~ aᵢ`, each a shortest `aᵢ`–`bᵢ` path avoiding its port edge), in a graph with
minimum degree `3`, independent hubs (`H = {deg ≠ 3}`) and no accepted cycle of length `4`.
`Y = V ∖ (W₁ ∪ W₂)` (`Yset`).

* (A) every vertex has at most two neighbours on each walk (`Tri2.pos1`, `Tri2.pos2`), so
  `d(v) ≤ 4 + |N(v) ∩ Y|` (`deg_le`, `deg_le_four`, `deg_le_Y`);
* (K1) `w0_shape`, `stub_rule`, `w0_escape`: a hub `h = w₁(i)` off `W₂`, not an end, with no
  neighbour in `Y`, has exactly the neighbours `w₁(i ± 1)` and `w₂(j)`, `w₂(j + 1)`; a
  `W₂`-neighbour `w₂(k)` of `w₁(i ± 1)` has `k = j − 2` or `k = j + 3`, and not both of
  `w₁(i ± 1)` have one, so one of them has a neighbour in `Y`;
* (B) `crossing_exit`, `exitPos_le`: a crossing hub leaves `W₂` at its next position, and the
  exits are at most one more than the exceptional positions (`TwoGeodesics.bubble_exc`, one
  exceptional position per bubble);
* (C) `hub_count`, `sigma_count`: `|H| ≤ 37|Y| + 21` and `σ ≤ |H| + |H_Y|·|Y|` with
  `|H_Y| ≤ 3|Y|` (`H_Y` the hubs with a neighbour in `Y`), given `EndEdgesFree`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.WalkHubEscape

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.PathChords
open Hypostructure.Graph.LadderRun
open Hypostructure.Graph.LadderCount
open Hypostructure.Graph.TwoGeodesics

universe u

section Walk

variable {V : Type u} {G : SimpleGraph V}

/-- **A `4`-cycle is not accepted** (from the cycle avoidance alone). -/
theorem c4 {LengthOK : ℕ → Prop}
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    (ok4 : LengthOK 4) {u x v y : V} (hux : G.Adj u x)
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
  exact avoids ⟨u, c, hc, by
    have : c.length = 4 := by simp [hl, p, q]
    rw [this]; exact ok4⟩

/-- **The neighbours of a path vertex on its own geodesic path** are its path neighbours, or
the other end across the port edge. -/
theorem own_pos {a b : V} {w : G.Walk a b} (hp : w.IsPath) (det : GeodesicDetours s(a, b) w)
    {t j : ℕ} (ht : t ≤ w.length) (hj : j ≤ w.length)
    (hadj : G.Adj (w.getVert t) (w.getVert j)) :
    j + 1 = t ∨ t + 1 = j ∨ (t = 0 ∧ j = w.length) ∨ (t = w.length ∧ j = 0) := by
  have hne : t ≠ j := by
    rintro rfl
    exact hadj.ne rfl
  by_cases hport : s(w.getVert t, w.getVert j) = s(a, b)
  · rw [Sym2.eq_iff] at hport
    rcases hport with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; right; left
      exact ⟨getVert_inj hp ht (Nat.zero_le _) (h1.trans w.getVert_zero.symm),
        getVert_inj hp hj le_rfl (h2.trans w.getVert_length.symm)⟩
    · right; right; right
      exact ⟨getVert_inj hp ht le_rfl (h1.trans w.getVert_length.symm),
        getVert_inj hp hj (Nat.zero_le _) (h2.trans w.getVert_zero.symm)⟩
  · let r : G.Walk (w.getVert t) (w.getVert j) := SimpleGraph.Walk.cons hadj .nil
    have hr : ∀ ε ∈ r.edges, ε ≠ s(a, b) := by
      intro ε hε
      simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hε
      rw [hε]; exact hport
    have := idx_dist_le det ht hj r hr
    simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega

/-- **A path vertex has at most two neighbours on its own geodesic path.** -/
theorem own_card {a b : V} {w : G.Walk a b} (hp : w.IsPath) (det : GeodesicDetours s(a, b) w)
    {t : ℕ} (ht : t ≤ w.length) : (nbrPos w (w.getVert t)).card ≤ 2 := by
  classical
  have mem : ∀ j ∈ nbrPos w (w.getVert t), j ≤ w.length ∧ (j + 1 = t ∨ t + 1 = j ∨
      (t = 0 ∧ j = w.length) ∨ (t = w.length ∧ j = 0)) := by
    intro j hj
    simp only [nbrPos, Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨by omega, own_pos hp det ht (by omega) hj.2⟩
  by_cases h0 : t = 0
  · have sub : nbrPos w (w.getVert t) ⊆ {1, w.length} := by
      intro j hj
      have := mem j hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact le_trans (Finset.card_le_card sub) Finset.card_le_two
  · by_cases hl : t = w.length
    · have sub : nbrPos w (w.getVert t) ⊆ {t - 1, 0} := by
        intro j hj
        have := mem j hj
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact le_trans (Finset.card_le_card sub) Finset.card_le_two
    · have sub : nbrPos w (w.getVert t) ⊆ {t - 1, t + 1} := by
        intro j hj
        have := mem j hj
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact le_trans (Finset.card_le_card sub) Finset.card_le_two

/-- A triangular walk avoiding its port edge has length at least `2`. -/
theorem two_le_length {a b : V} {w : G.Walk a b} (hab : G.Adj b a)
    (av : ∀ ε ∈ w.edges, ε ≠ s(a, b)) : 2 ≤ w.length := by
  cases w with
  | nil => exact (hab.ne rfl).elim
  | cons h p =>
    cases p with
    | nil => exact (av _ (by simp) rfl).elim
    | cons h' p' =>
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- **Every vertex of a triangular path has two walk neighbours** (cyclically). -/
theorem two_nbrs {a b : V} {w : G.Walk a b} (hp : w.IsPath) (hab : G.Adj b a)
    (hl : 2 ≤ w.length) {j : ℕ} (hj : j ≤ w.length) :
    ∃ p q, p ∈ w.support ∧ q ∈ w.support ∧ p ≠ q ∧ G.Adj (w.getVert j) p ∧
      G.Adj (w.getVert j) q := by
  by_cases h0 : j = 0
  · subst h0
    refine ⟨w.getVert 1, w.getVert w.length, SimpleGraph.Walk.getVert_mem_support _ _,
      SimpleGraph.Walk.getVert_mem_support _ _, fun e => ?_, w.adj_getVert_succ (by omega), ?_⟩
    · have := getVert_inj hp (by omega) le_rfl e
      omega
    · rw [w.getVert_zero, w.getVert_length]; exact hab.symm
  · by_cases hL : j = w.length
    · subst hL
      refine ⟨w.getVert (w.length - 1), w.getVert 0, SimpleGraph.Walk.getVert_mem_support _ _,
        SimpleGraph.Walk.getVert_mem_support _ _, fun e => ?_, ?_, ?_⟩
      · have := getVert_inj hp (by omega) (Nat.zero_le _) e
        omega
      · have := w.adj_getVert_succ (i := w.length - 1) (by omega)
        rw [show w.length - 1 + 1 = w.length by omega] at this
        exact this.symm
      · rw [w.getVert_zero, w.getVert_length]; exact hab
    · refine ⟨w.getVert (j - 1), w.getVert (j + 1), SimpleGraph.Walk.getVert_mem_support _ _,
        SimpleGraph.Walk.getVert_mem_support _ _, fun e => ?_, ?_, w.adj_getVert_succ (by omega)⟩
      · have := getVert_inj hp (by omega) (by omega) e
        omega
      · have := w.adj_getVert_succ (i := j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        exact this.symm

/-! ### Exits and bubbles -/

variable {a1 b1 a2 b2 : V}

open Classical in
/-- The positions `t < |w₁|` where `w₁` leaves `W₂`: `w₁(t) ∈ W₂`, `w₁(t + 1) ∉ W₂`. -/
noncomputable def exitPos (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) : Finset ℕ :=
  (Finset.range w1.length).filter fun t =>
    w1.getVert t ∈ w2.support ∧ w1.getVert (t + 1) ∉ w2.support

open Classical in
/-- The positions of `w₁` off `W₂` that are exceptional for `S` (`TwoGeodesics.ExcS`). -/
noncomputable def excPos (Cubic : V → Prop) (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2)
    (S : Finset V) : Finset ℕ :=
  (Finset.range (w1.length + 1)).filter fun s =>
    w1.getVert s ∉ w2.support ∧ ExcS Cubic w1 S s

/-- **The exits are at most one more than the exceptional positions**: every exit but the
last opens a bubble, and every bubble carries an exceptional position (`bubble_exc`). -/
theorem exitPos_le {LengthOK : ℕ → Prop} {Cubic : V → Prop} {w1 : G.Walk a1 b1}
    {w2 : G.Walk a2 b2} (H : Geo2 G LengthOK Cubic w1 w2) (S : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ S)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ S)
    (ha : a2 ∈ S) (hb : b2 ∈ S) :
    (exitPos w1 w2).card ≤ (excPos Cubic w1 w2 S).card + 1 := by
  classical
  have memA : ∀ t, t ∈ exitPos w1 w2 ↔ t < w1.length ∧ w1.getVert t ∈ w2.support ∧
      w1.getVert (t + 1) ∉ w2.support := by
    intro t
    simp only [exitPos, Finset.mem_filter, Finset.mem_range]
  let later : ℕ → Prop := fun t => ∃ k, k ≤ w1.length ∧ t < k ∧ w1.getVert k ∈ w2.support
  have split := Finset.card_filter_add_card_filter_not (s := exitPos w1 w2) later
  have last : ((exitPos w1 w2).filter (fun t => ¬ later t)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro t1 h1 t2 h2
    rw [Finset.mem_filter, memA] at h1 h2
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | lt
    · exact h1.2 ⟨t2, by omega, lt, h2.1.2.1⟩
    · exact h2.2 ⟨t1, by omega, lt, h1.1.2.1⟩
  have main : ((exitPos w1 w2).filter later).card ≤ (excPos Cubic w1 w2 S).card := by
    apply Finset.card_le_card_of_forall_subsingleton
      (fun t s => t < s ∧ ∀ k, t < k → k ≤ s → w1.getVert k ∉ w2.support)
    · intro t ht
      rw [Finset.mem_filter, memA] at ht
      obtain ⟨⟨htl, htm, hts⟩, k0, hk0l, htk0, hk0m⟩ := ht
      let C := (Finset.range (w1.length + 1)).filter
        (fun k => t < k ∧ w1.getVert k ∈ w2.support)
      have hne : C.Nonempty :=
        ⟨k0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), htk0, hk0m⟩⟩
      have t'mem := C.min'_mem hne
      have t'min : ∀ k ∈ C, C.min' hne ≤ k := fun k hk => C.min'_le k hk
      obtain ⟨t'r, tt', t'm⟩ := Finset.mem_filter.1 t'mem
      have t'l := Finset.mem_range.1 t'r
      have hoff : ∀ k, t < k → k < C.min' hne → w1.getVert k ∉ w2.support := by
        intro k h1 h2 m
        have := t'min k (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h1, m⟩)
        omega
      have htt : t + 2 ≤ C.min' hne := by
        by_contra lt
        have e : C.min' hne = t + 1 := by omega
        rw [e] at t'm
        exact hts t'm
      obtain ⟨p, hp, hpl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 htm
      obtain ⟨p', hp', hpl'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 t'm
      obtain ⟨s, hs1, hs2, hexc⟩ := bubble_exc H S hX hU ha hb htt (by omega) hpl hpl'
        hp.symm hp'.symm hoff
      refine ⟨s, ?_, hs1, fun k h1 h2 => hoff k h1 (by omega)⟩
      simp only [excPos, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hoff s hs1 hs2, hexc⟩
    · intro s _ t1 ht1 t2 ht2
      obtain ⟨m1, r1⟩ := ht1
      obtain ⟨m2, r2⟩ := ht2
      have m1' : t1 ∈ (exitPos w1 w2).filter later := m1
      have m2' : t2 ∈ (exitPos w1 w2).filter later := m2
      rw [Finset.mem_filter, memA] at m1' m2'
      by_contra ne
      rcases lt_or_gt_of_ne ne with lt | lt
      · exact r1.2 t2 lt (le_of_lt r2.1) m2'.1.2.1
      · exact r2.2 t1 lt (le_of_lt r1.1) m1'.1.2.1
  omega

end Walk

section Object

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

variable {object : FiniteObject.{u}} {LengthOK : ℕ → Prop}
variable {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1}
  {w2 : object.graph.Walk a2 b2}

/-- **The hypotheses on two triangular port walks.** -/
structure Tri2 (object : FiniteObject.{u}) (LengthOK : ℕ → Prop) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Prop where
  C : CountHyp object.graph LengthOK (fun v => object.degree v = 3) w1 w2
  t1 : object.graph.Adj b1 a1
  t2 : object.graph.Adj b2 a2
  av1 : ∀ ε ∈ w1.edges, ε ≠ s(a1, b1)
  av2 : ∀ ε ∈ w2.edges, ε ≠ s(a2, b2)
  base3 : ∀ v, 3 ≤ object.degree v
  slack : ∀ l r, 3 < object.degree l → 3 < object.degree r → ¬ object.graph.Adj l r

theorem Tri2.swap (T : Tri2 object LengthOK w1 w2) : Tri2 object LengthOK w2 w1 :=
  ⟨⟨T.C.stub, T.C.avoids, T.C.ok4, T.C.ok8, T.C.ok16, T.C.hp2, T.C.hp1, T.C.det2, T.C.det1,
    T.C.hub2, T.C.hub1, T.C.match_⟩, T.t2, T.t1, T.av2, T.av1, T.base3, T.slack⟩

/-- The vertices off both walks. -/
noncomputable def Yset (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) :
    Finset object.Vertex :=
  Finset.univ.filter fun v => v ∉ w1.support ∧ v ∉ w2.support

theorem mem_Yset {v : object.Vertex} : v ∈ Yset w1 w2 ↔ v ∉ w1.support ∧ v ∉ w2.support := by
  simp [Yset]

theorem Yset_comm : Yset w2 w1 = Yset w1 w2 := by
  ext v
  rw [mem_Yset, mem_Yset]
  exact And.comm

theorem Tri2.pos1 (T : Tri2 object LengthOK w1 w2) (v : object.Vertex) :
    (nbrPos w1 v).card ≤ 2 := by
  by_cases hv : v ∈ w1.support
  · obtain ⟨t, rfl, ht⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hv
    exact own_card T.C.hp1 T.C.det1 ht
  · exact nbrPos_le_two_of_match T.C.hp1 T.C.hub1 T.C.ok4 T.C.match_ hv

theorem Tri2.pos2 (T : Tri2 object LengthOK w1 w2) (v : object.Vertex) :
    (nbrPos w2 v).card ≤ 2 :=
  T.swap.pos1 v

theorem Tri2.cubic (T : Tri2 object LengthOK w1 w2) {h x : object.Vertex}
    (hh : 4 ≤ object.graph.degree h) (adj : object.graph.Adj h x) :
    object.graph.degree x = 3 := by
  have b : 3 ≤ object.graph.degree x := T.base3 x
  by_contra ne
  exact T.slack h x (show 3 < object.degree h by change 3 < object.graph.degree h; omega)
    (show 3 < object.degree x by change 3 < object.graph.degree x; omega) adj

/-- **(A) The degree splits over the two walks and `Y`.** -/
theorem deg_le (T : Tri2 object LengthOK w1 w2) (v : object.Vertex) :
    object.graph.degree v ≤ (nbrPos w1 v).card + (nbrPos w2 v).card +
      ((object.graph.neighborFinset v).filter fun y => y ∉ w1.support ∧ y ∉ w2.support).card := by
  have sub : object.graph.neighborFinset v ⊆ (nbrPos w1 v).image w1.getVert ∪
      (nbrPos w2 v).image w2.getVert ∪
      (object.graph.neighborFinset v).filter (fun y => y ∉ w1.support ∧ y ∉ w2.support) := by
    intro y hy
    have hy' := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    by_cases m1 : y ∈ w1.support
    · left; left
      obtain ⟨j, rfl, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m1
      refine ⟨j, ?_, rfl⟩
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hy'⟩
    · by_cases m2 : y ∈ w2.support
      · left; right
        obtain ⟨j, rfl, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m2
        refine ⟨j, ?_, rfl⟩
        simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hy'⟩
      · right; exact ⟨hy, m1, m2⟩
  have c := Finset.card_le_card sub
  have u1 := Finset.card_union_le ((nbrPos w1 v).image w1.getVert ∪
    (nbrPos w2 v).image w2.getVert)
    ((object.graph.neighborFinset v).filter (fun y => y ∉ w1.support ∧ y ∉ w2.support))
  have u2 := Finset.card_union_le ((nbrPos w1 v).image w1.getVert)
    ((nbrPos w2 v).image w2.getVert)
  have i1 := Finset.card_image_le (s := nbrPos w1 v) (f := w1.getVert)
  have i2 := Finset.card_image_le (s := nbrPos w2 v) (f := w2.getVert)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at c
  omega

/-- **(A) A vertex with no neighbour in `Y` has degree at most `4`.** -/
theorem deg_le_four (T : Tri2 object LengthOK w1 w2) (v : object.Vertex)
    (noY : ∀ y, object.graph.Adj v y → y ∈ w1.support ∨ y ∈ w2.support) :
    object.graph.degree v ≤ 4 := by
  have d := deg_le T v
  have z : ((object.graph.neighborFinset v).filter
      fun y => y ∉ w1.support ∧ y ∉ w2.support).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    rcases noY y hy.1 with m | m
    · exact hy.2.1 m
    · exact hy.2.2 m
  have := T.pos1 v
  have := T.pos2 v
  omega

/-- **(A) `d(v) ≤ 4 + |Y|`.** -/
theorem deg_le_Y (T : Tri2 object LengthOK w1 w2) (v : object.Vertex) :
    object.graph.degree v ≤ 4 + (Yset w1 w2).card := by
  have d := deg_le T v
  have sub : ((object.graph.neighborFinset v).filter
      fun y => y ∉ w1.support ∧ y ∉ w2.support) ⊆ Yset w1 w2 := by
    intro y hy
    exact mem_Yset.2 (Finset.mem_filter.1 hy).2
  have := Finset.card_le_card sub
  have := T.pos1 v
  have := T.pos2 v
  omega

/-! ### K1: the W0 escape -/

/-- **Two neighbours on `w₂` of a vertex off `W₂` are consecutive.** -/
theorem consec (T : Tri2 object LengthOK w1 w2) {h : object.Vertex} (hh : h ∉ w2.support)
    {j j' : ℕ} (hjj : j < j') (hj' : j' ≤ w2.length)
    (hx : object.graph.Adj h (w2.getVert j)) (hy : object.graph.Adj h (w2.getVert j')) :
    j' = j + 1 := by
  let r : object.graph.Walk (w2.getVert j) (w2.getVert j') := .cons hx.symm (.cons hy .nil)
  have hr : ∀ ε ∈ r.edges, ε ≠ s(a2, b2) := by
    intro ε hε
    simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hε
    rcases hε with rfl | rfl
    · exact (edge_ne_of_notMem (w := w2) hh).2
    · exact (edge_ne_of_notMem (w := w2) hh).1
  have d := idx_dist_le T.C.det2 (by omega) hj' r hr
  simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at d
  by_contra ne
  have e : j' = j + 2 := by omega
  subst e
  have a01 := w2.adj_getVert_succ (i := j) (by omega)
  have a12 := w2.adj_getVert_succ (i := j + 1) (by omega)
  refine c4 T.C.avoids T.C.ok4 hx a01 a12 hy.symm ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun e => hh (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)
  · intro e
    have := getVert_inj T.C.hp2 (by omega) (by omega) e
    omega
  · exact fun e => hh (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)
  · intro e
    have := getVert_inj T.C.hp2 (by omega) (by omega) e
    omega
  · exact fun e => hh (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)
  · intro e
    have := getVert_inj T.C.hp2 (by omega) (by omega) e
    omega

/-- **(K1, shape) A W0 hub.**  A hub `h = w₁(i)` off `W₂`, not an end, with no neighbour in
`Y`: its `W₂`-neighbours are `w₂(j)`, `w₂(j + 1)`, and `w₁(i ± 1)` are off `W₂`. -/
theorem w0_shape (T : Tri2 object LengthOK w1 w2) {i : ℕ} (hi0 : 0 < i) (hil : i < w1.length)
    (hoff : w1.getVert i ∉ w2.support) (hhub : 4 ≤ object.graph.degree (w1.getVert i))
    (noY : ∀ y, object.graph.Adj (w1.getVert i) y → y ∈ w1.support ∨ y ∈ w2.support) :
    ∃ j, j + 1 ≤ w2.length ∧ object.graph.Adj (w1.getVert i) (w2.getVert j) ∧
      object.graph.Adj (w1.getVert i) (w2.getVert (j + 1)) ∧
      w1.getVert (i - 1) ∉ w2.support ∧ w1.getVert (i + 1) ∉ w2.support := by
  classical
  have N1 : ∀ z, object.graph.Adj (w1.getVert i) z → z ∈ w1.support →
      z = w1.getVert (i - 1) ∨ z = w1.getVert (i + 1) := by
    intro z hz m
    obtain ⟨j', rfl, hj'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m
    rcases own_pos T.C.hp1 T.C.det1 (le_of_lt hil) hj' hz with e | e | e | e
    · left; congr 1; omega
    · right; congr 1; omega
    · omega
    · omega
  have d := deg_le T (w1.getVert i)
  have z : ((object.graph.neighborFinset (w1.getVert i)).filter
      fun y => y ∉ w1.support ∧ y ∉ w2.support).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    rcases noY y hy.1 with m | m
    · exact hy.2.1 m
    · exact hy.2.2 m
  have p1 := T.pos1 (w1.getVert i)
  have p2 := T.pos2 (w1.getVert i)
  have two : 1 < (nbrPos w2 (w1.getVert i)).card := by omega
  obtain ⟨j1, hj1, j2, hj2, ne⟩ := Finset.one_lt_card.1 two
  simp only [nbrPos, Finset.mem_filter, Finset.mem_range] at hj1 hj2
  obtain ⟨j, hj, hx, hy⟩ : ∃ j, j + 1 ≤ w2.length ∧
      object.graph.Adj (w1.getVert i) (w2.getVert j) ∧
      object.graph.Adj (w1.getVert i) (w2.getVert (j + 1)) := by
    rcases lt_or_gt_of_ne ne with lt | lt
    · have e := consec T hoff lt (by omega) hj1.2 hj2.2
      subst e
      exact ⟨j1, by omega, hj1.2, hj2.2⟩
    · have e := consec T hoff lt (by omega) hj2.2 hj1.2
      subst e
      exact ⟨j2, by omega, hj2.2, hj1.2⟩
  have N2 : ∀ q, q ≤ w2.length → object.graph.Adj (w1.getVert i) (w2.getVert q) →
      q = j ∨ q = j + 1 := by
    intro q hq aq
    by_contra hne
    push Not at hne
    have : 2 < (nbrPos w2 (w1.getVert i)).card := by
      refine Finset.two_lt_card.2 ⟨j, ?_, j + 1, ?_, q, ?_, by omega, by omega, by omega⟩
      · simp only [nbrPos, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hx⟩
      · simp only [nbrPos, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hy⟩
      · simp only [nbrPos, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, aq⟩
    omega
  have nbrs : ∀ z, object.graph.Adj (w1.getVert i) z → z = w1.getVert (i - 1) ∨
      z = w1.getVert (i + 1) ∨ z = w2.getVert j ∨ z = w2.getVert (j + 1) := by
    intro z hz
    rcases noY z hz with m | m
    · rcases N1 z hz m with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · obtain ⟨q, rfl, hq⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m
      rcases N2 q hq hz with e | e
      · right; right; left; rw [e]
      · right; right; right; rw [e]
  have aum : object.graph.Adj (w1.getVert i) (w1.getVert (i - 1)) := by
    have := w1.adj_getVert_succ (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    exact this.symm
  have aup : object.graph.Adj (w1.getVert i) (w1.getVert (i + 1)) := w1.adj_getVert_succ hil
  have small : ∀ z0, (z0 = w2.getVert j ∨ z0 = w2.getVert (j + 1)) →
      ∀ z1, (∀ z, object.graph.Adj (w1.getVert i) z → z = z0 ∨ z = z1 ∨
        z = w2.getVert j ∨ z = w2.getVert (j + 1)) → False := by
    intro z0 h0 z1 hall
    have sub : object.graph.neighborFinset (w1.getVert i) ⊆
        {z1, w2.getVert j, w2.getVert (j + 1)} := by
      intro z hz
      rw [SimpleGraph.mem_neighborFinset] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hall z hz with e | e | e | e
      · rcases h0 with e' | e'
        · right; left; rw [e, e']
        · right; right; rw [e, e']
      · left; exact e
      · right; left; exact e
      · right; right; exact e
    have := Finset.card_le_card sub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at this
    have := Finset.card_le_three (a := z1) (b := w2.getVert j) (c := w2.getVert (j + 1))
    omega
  refine ⟨j, hj, hx, hy, fun m => ?_, fun m => ?_⟩
  · obtain ⟨q, hq, hql⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m
    have e := N2 q hql (hq ▸ aum)
    refine small (w1.getVert (i - 1)) ?_ (w1.getVert (i + 1)) nbrs
    rcases e with e | e
    · left; rw [← hq, e]
    · right; rw [← hq, e]
  · obtain ⟨q, hq, hql⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m
    have e := N2 q hql (hq ▸ aup)
    refine small (w1.getVert (i + 1)) ?_ (w1.getVert (i - 1)) (fun z hz => ?_)
    · rcases e with e | e
      · left; rw [← hq, e]
      · right; rw [← hq, e]
    · rcases nbrs z hz with e' | e' | e' | e'
      · right; left; exact e'
      · left; exact e'
      · right; right; left; exact e'
      · right; right; right; exact e'

/-- **(K1, stub rule)** At a hub `h` off `W₂` adjacent to `w₂(j)`, `w₂(j + 1)`: a neighbour
`u` of `h` off `W₂` adjacent to `w₂(k)` has `k = j − 2` or `k = j + 3`. -/
theorem stub_rule (T : Tri2 object LengthOK w1 w2) {h u : object.Vertex} (hh : h ∉ w2.support)
    (hhub : 4 ≤ object.graph.degree h) (hu : u ∉ w2.support) (hhu : object.graph.Adj h u)
    {j : ℕ} (hj : j + 1 ≤ w2.length) (hx : object.graph.Adj h (w2.getVert j))
    (hy : object.graph.Adj h (w2.getVert (j + 1))) {k : ℕ} (hk : k ≤ w2.length)
    (huk : object.graph.Adj u (w2.getVert k)) : k + 2 = j ∨ k = j + 3 := by
  have hl2 : 2 ≤ w2.length := two_le_length T.t2 T.av2
  have dist : ∀ m, m ≤ w2.length → object.graph.Adj h (w2.getVert m) →
      m ≤ k + 3 ∧ k ≤ m + 3 := by
    intro m hm am
    let r : object.graph.Walk (w2.getVert m) (w2.getVert k) :=
      .cons am.symm (.cons hhu (.cons huk .nil))
    have hr : ∀ ε ∈ r.edges, ε ≠ s(a2, b2) := by
      intro ε hε
      simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hε
      rcases hε with rfl | rfl | rfl
      · exact (edge_ne_of_notMem (w := w2) hh).2
      · exact (edge_ne_of_notMem (w := w2) hh).1
      · exact (edge_ne_of_notMem (w := w2) hu).1
    have := idx_dist_le T.C.det2 hm hk r hr
    simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega
  have d1 := dist j (by omega) hx
  have d2 := dist (j + 1) hj hy
  have full : ∀ m, m ≤ w2.length → object.graph.Adj h (w2.getVert m) →
      ¬ object.graph.Adj u (w2.getVert m) := by
    intro m hm ahm aum
    have cm := T.cubic hhub ahm
    obtain ⟨p, q, hp, hq, hpq, ap, aq⟩ := two_nbrs T.C.hp2 T.t2 hl2 hm
    obtain ⟨s, -, -, -, hall⟩ := T.C.stub _ cm p q ap aq hpq
    have e1 : h = s := by
      rcases hall h ahm.symm with e | e | e
      · exact absurd (e ▸ hp) hh
      · exact absurd (e ▸ hq) hh
      · exact e
    have e2 : u = s := by
      rcases hall u aum.symm with e | e | e
      · exact absurd (e ▸ hp) hu
      · exact absurd (e ▸ hq) hu
      · exact e
    exact hhu.ne (e1.trans e2.symm)
  have k0 : k ≠ j := fun e => full j (by omega) hx (e ▸ huk)
  have k1 : k ≠ j + 1 := fun e => full (j + 1) hj hy (e ▸ huk)
  have hne_h : ∀ m, h ≠ w2.getVert m := fun m e => hh (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)
  have hne_u : ∀ m, u ≠ w2.getVert m := fun m e => hu (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)
  have k2 : k + 1 ≠ j := by
    intro e
    have avx : object.graph.Adj (w2.getVert k) (w2.getVert j) := by
      have := w2.adj_getVert_succ (i := k) (by omega)
      rw [e] at this
      exact this
    refine c4 T.C.avoids T.C.ok4 hhu huk avx hx.symm (hne_h k) (hne_u j) hhu.ne.symm
      (hne_u k) (hne_h j).symm ?_
    intro e'
    have := getVert_inj T.C.hp2 (by omega) hk e'
    omega
  have k3 : k ≠ j + 2 := by
    intro e
    have avy : object.graph.Adj (w2.getVert k) (w2.getVert (j + 1)) := by
      have := w2.adj_getVert_succ (i := j + 1) (by omega)
      rw [e]
      exact this.symm
    refine c4 T.C.avoids T.C.ok4 hhu huk avy hy.symm (hne_h k) (hne_u (j + 1)) hhu.ne.symm
      (hne_u k) (hne_h (j + 1)).symm ?_
    intro e'
    have := getVert_inj T.C.hp2 hj hk e'
    omega
  omega

/-- **(K1, escape)** One of `w₁(i ± 1)` has a neighbour in `Y`. -/
theorem w0_escape (T : Tri2 object LengthOK w1 w2) {i : ℕ} (hi0 : 0 < i) (hil : i < w1.length)
    (hoff : w1.getVert i ∉ w2.support) (hhub : 4 ≤ object.graph.degree (w1.getVert i))
    (noY : ∀ y, object.graph.Adj (w1.getVert i) y → y ∈ w1.support ∨ y ∈ w2.support) :
    ∃ y, y ∉ w1.support ∧ y ∉ w2.support ∧
      (object.graph.Adj (w1.getVert (i - 1)) y ∨ object.graph.Adj (w1.getVert (i + 1)) y) := by
  classical
  obtain ⟨j, hj, hx, hy, um, up⟩ := w0_shape T hi0 hil hoff hhub noY
  have aum : object.graph.Adj (w1.getVert i) (w1.getVert (i - 1)) := by
    have := w1.adj_getVert_succ (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    exact this.symm
  have aup : object.graph.Adj (w1.getVert i) (w1.getVert (i + 1)) := w1.adj_getVert_succ hil
  have notBoth : ¬ ((∃ k, k ≤ w2.length ∧ object.graph.Adj (w1.getVert (i - 1)) (w2.getVert k)) ∧
      (∃ k, k ≤ w2.length ∧ object.graph.Adj (w1.getVert (i + 1)) (w2.getVert k))) := by
    rintro ⟨⟨k1, hk1, a1'⟩, ⟨k2, hk2, a2'⟩⟩
    have s1 := stub_rule T hoff hhub um aum hj hx hy hk1 a1'
    have s2 := stub_rule T hoff hhub up aup hj hx hy hk2 a2'
    have hne_h : ∀ m, w1.getVert i ≠ w2.getVert m :=
      fun m e => hoff (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)
    by_cases e : k1 = k2
    · subst e
      refine c4 T.C.avoids T.C.ok4 a1'.symm aum.symm aup a2' (hne_h k1).symm ?_
        (fun e => um (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)) aum.ne.symm
        (fun e => up (e ▸ SimpleGraph.Walk.getVert_mem_support _ _)) aup.ne.symm
      intro e
      have := getVert_inj T.C.hp1 (by omega) (by omega) e
      omega
    · let r : object.graph.Walk (w2.getVert k1) (w2.getVert k2) :=
        .cons a1'.symm (.cons aum.symm (.cons aup (.cons a2' .nil)))
      have hr : ∀ ε ∈ r.edges, ε ≠ s(a2, b2) := by
        intro ε hε
        simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hε
        rcases hε with rfl | rfl | rfl | rfl
        · exact (edge_ne_of_notMem (w := w2) um).2
        · exact (edge_ne_of_notMem (w := w2) um).1
        · exact (edge_ne_of_notMem (w := w2) hoff).1
        · exact (edge_ne_of_notMem (w := w2) up).1
      have := idx_dist_le T.C.det2 hk1 hk2 r hr
      simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
      omega
  have escape : ∀ u, object.graph.Adj (w1.getVert i) u →
      (∀ k, k ≤ w2.length → ¬ object.graph.Adj u (w2.getVert k)) →
      ∃ y, y ∉ w1.support ∧ y ∉ w2.support ∧ object.graph.Adj u y := by
    intro u ahu none
    have cu := T.cubic hhub ahu
    have z : (nbrPos w2 u).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro k hk
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range] at hk
      exact none k (by omega) hk.2
    have d := deg_le T u
    have p1 := T.pos1 u
    have pos : 0 < ((object.graph.neighborFinset u).filter
        fun y => y ∉ w1.support ∧ y ∉ w2.support).card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.1 pos
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    exact ⟨y, hy.2.1, hy.2.2, hy.1⟩
  by_cases A : ∃ k, k ≤ w2.length ∧ object.graph.Adj (w1.getVert (i - 1)) (w2.getVert k)
  · have B : ∀ k, k ≤ w2.length → ¬ object.graph.Adj (w1.getVert (i + 1)) (w2.getVert k) :=
      fun k hk a => notBoth ⟨A, k, hk, a⟩
    obtain ⟨y, n1, n2, a⟩ := escape _ aup B
    exact ⟨y, n1, n2, Or.inr a⟩
  · have A' : ∀ k, k ≤ w2.length → ¬ object.graph.Adj (w1.getVert (i - 1)) (w2.getVert k) :=
      fun k hk a => A ⟨k, hk, a⟩
    obtain ⟨y, n1, n2, a⟩ := escape _ aum A'
    exact ⟨y, n1, n2, Or.inl a⟩

/-- **(K1) The W0 escape at `w₁`, with the stub rule.** -/
def W0Escape (object : FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Prop :=
  ∀ i, 0 < i → i < w1.length → w1.getVert i ∉ w2.support →
    4 ≤ object.degree (w1.getVert i) →
    (∀ y, object.graph.Adj (w1.getVert i) y → y ∈ w1.support ∨ y ∈ w2.support) →
    (∃ j, j + 1 ≤ w2.length ∧ object.graph.Adj (w1.getVert i) (w2.getVert j) ∧
      object.graph.Adj (w1.getVert i) (w2.getVert (j + 1)) ∧
      w1.getVert (i - 1) ∉ w2.support ∧ w1.getVert (i + 1) ∉ w2.support ∧
      ∀ u, (u = w1.getVert (i - 1) ∨ u = w1.getVert (i + 1)) → ∀ k, k ≤ w2.length →
        object.graph.Adj u (w2.getVert k) → k + 2 = j ∨ k = j + 3) ∧
    ∃ y, y ∉ w1.support ∧ y ∉ w2.support ∧
      (object.graph.Adj (w1.getVert (i - 1)) y ∨ object.graph.Adj (w1.getVert (i + 1)) y)

theorem w0Escape_of (T : Tri2 object LengthOK w1 w2) : W0Escape object w1 w2 := by
  intro i hi0 hil hoff hhub noY
  have hhub' : 4 ≤ object.graph.degree (w1.getVert i) := hhub
  obtain ⟨j, hj, hx, hy, um, up⟩ := w0_shape T hi0 hil hoff hhub' noY
  have aum : object.graph.Adj (w1.getVert i) (w1.getVert (i - 1)) := by
    have := w1.adj_getVert_succ (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    exact this.symm
  have aup : object.graph.Adj (w1.getVert i) (w1.getVert (i + 1)) := w1.adj_getVert_succ hil
  refine ⟨⟨j, hj, hx, hy, um, up, fun u hu k hk huk => ?_⟩, w0_escape T hi0 hil hoff hhub' noY⟩
  rcases hu with rfl | rfl
  · exact stub_rule T hoff hhub' um aum hj hx hy hk huk
  · exact stub_rule T hoff hhub' up aup hj hx hy hk huk

/-! ### Crossings -/

/-- **A crossing hub leaves `W₂` at its next position.**  A common hub `h = w₁(t) = w₂(p)`,
interior to both walks, with no neighbour in `Y`, has degree `4` split `2 + 2`; so
`w₁(t + 1) ∉ W₂` (a common `w₁(t + 1)` would be at `w₂`-distance `1`, `common_iso`). -/
theorem crossing_exit (T : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2)
    {t p : ℕ} (ht0 : 0 < t) (htl : t < w1.length) (hp0 : 0 < p) (hpl : p < w2.length)
    (hc : w1.getVert t = w2.getVert p) (hhub : 4 ≤ object.graph.degree (w1.getVert t))
    (noY : ∀ y, object.graph.Adj (w1.getVert t) y → y ∈ w1.support ∨ y ∈ w2.support) :
    w1.getVert (t + 1) ∉ w2.support := by
  intro m
  obtain ⟨q, hq, hql⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m
  have Hg : Geo2 object.graph LengthOK (fun v => object.degree v = 3) w1 w2 :=
    Geo2.ofCount T.C E.1 E.2
  have iso := common_iso Hg (le_of_lt htl) (by omega) (le_of_lt hpl) hql hc hq.symm
  have nbrs : ∀ z, object.graph.Adj (w1.getVert t) z → z = w1.getVert (t - 1) ∨
      z = w2.getVert (p - 1) ∨ z = w2.getVert (p + 1) := by
    intro z hz
    rcases noY z hz with m1 | m2
    · obtain ⟨j', rfl, hj'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m1
      rcases own_pos T.C.hp1 T.C.det1 (le_of_lt htl) hj' hz with e | e | e | e
      · left; congr 1; omega
      · subst e
        rw [← hq]
        rcases (show q + 1 = p ∨ p + 1 = q by omega) with e' | e'
        · right; left; congr 1; omega
        · right; right; congr 1; omega
      · omega
      · omega
    · obtain ⟨j', rfl, hj'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m2
      rw [hc] at hz
      rcases own_pos T.C.hp2 T.C.det2 (le_of_lt hpl) hj' hz with e | e | e | e
      · right; left; congr 1; omega
      · right; right; congr 1; omega
      · omega
      · omega
  have sub : object.graph.neighborFinset (w1.getVert t) ⊆
      {w1.getVert (t - 1), w2.getVert (p - 1), w2.getVert (p + 1)} := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact nbrs z hz
  have := Finset.card_le_card sub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  have := Finset.card_le_three (a := w1.getVert (t - 1)) (b := w2.getVert (p - 1))
    (c := w2.getVert (p + 1))
  omega

/-! ### (C) The count -/

/-- The hubs with a neighbour in `Y`. -/
noncomputable def hubsY (object : FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Finset object.Vertex :=
  (JointObject.hubs object).filter fun h => ∃ y ∈ Yset w1 w2, object.graph.Adj h y

/-- The W0 hubs of `w₁`: on `W₁`, off `W₂`, not an end of `w₁`, no neighbour in `Y`. -/
noncomputable def coreOn (object : FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Finset object.Vertex :=
  (JointObject.hubs object).filter fun h => h ∈ w1.support ∧ h ∉ w2.support ∧
    (∀ y ∈ Yset w1 w2, ¬ object.graph.Adj h y) ∧ h ≠ a1 ∧ h ≠ b1

/-- The crossing hubs: common, not an end, no neighbour in `Y`. -/
noncomputable def crossings (object : FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Finset object.Vertex :=
  (JointObject.hubs object).filter fun h => h ∈ w1.support ∧ h ∈ w2.support ∧
    (∀ y ∈ Yset w1 w2, ¬ object.graph.Adj h y) ∧ h ≠ a1 ∧ h ≠ b1 ∧ h ≠ a2 ∧ h ≠ b2

/-- The exceptional set of the bubbles: the hubs, `Y`, and the ends of `w₂`. -/
noncomputable def escapeSet (object : FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Finset object.Vertex :=
  JointObject.hubs object ∪ Yset w1 w2 ∪ {a2, b2}

theorem hub4 (T : Tri2 object LengthOK w1 w2) {h : object.Vertex}
    (hh : h ∈ JointObject.hubs object) : 4 ≤ object.graph.degree h := by
  have := (JointObject.mem_hubs).1 hh
  have b : 3 ≤ object.graph.degree h := T.base3 h
  omega

theorem noY_of (h : object.Vertex) (hY : ∀ y ∈ Yset w1 w2, ¬ object.graph.Adj h y) :
    ∀ y, object.graph.Adj h y → y ∈ w1.support ∨ y ∈ w2.support := by
  intro y hy
  by_contra n
  push Not at n
  exact hY y (mem_Yset.2 n) hy

theorem hubsY_card (T : Tri2 object LengthOK w1 w2) :
    (hubsY object w1 w2).card ≤ 3 * (Yset w1 w2).card :=
  WalkAttachment.card_le_of_cubic_cover _ _ (fun v hv => by
    obtain ⟨hH, y, hy, adj⟩ := Finset.mem_filter.1 hv
    exact ⟨y, hy, adj, T.cubic (hub4 T hH) adj⟩)

theorem pos_union_card (T : Tri2 object LengthOK w1 w2) (S : Finset object.Vertex) :
    (S.biUnion (nbrPos w1)).card ≤ 2 * S.card := by
  have c1 := Finset.card_biUnion_le (s := S) (t := nbrPos w1)
  have c2 : ∑ y ∈ S, (nbrPos w1 y).card ≤ S.card * 2 := by
    have := Finset.sum_le_card_nsmul S (fun y => (nbrPos w1 y).card) 2 (fun y _ => T.pos1 y)
    simpa using this
  omega

/-- **(K1, count) The W0 hubs of `w₁` are at most `4|Y|`.** -/
theorem coreOn_card (T : Tri2 object LengthOK w1 w2) :
    (coreOn object w1 w2).card ≤ 4 * (Yset w1 w2).card := by
  let P := (Yset w1 w2).biUnion (nbrPos w1)
  have hP : P.card ≤ 2 * (Yset w1 w2).card := pos_union_card T (Yset w1 w2)
  have sub : coreOn object w1 w2 ⊆
      (P.image (· + 1) ∪ P.image (· - 1)).image w1.getVert := by
    intro h hh
    obtain ⟨hH, m1, m2, hY, na, nb⟩ := Finset.mem_filter.1 hh
    obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m1
    have hi0 : 0 < i := by
      by_contra z
      apply na
      rw [show i = 0 by omega, SimpleGraph.Walk.getVert_zero]
    have hil : i < w1.length := by
      by_contra z
      apply nb
      rw [show i = w1.length by omega, SimpleGraph.Walk.getVert_length]
    obtain ⟨y, n1, n2, a⟩ := w0_escape T hi0 hil m2 (hub4 T hH) (noY_of _ hY)
    have hyY : y ∈ Yset w1 w2 := mem_Yset.2 ⟨n1, n2⟩
    rw [Finset.mem_image]
    refine ⟨i, ?_, rfl⟩
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases a with a | a
    · left
      refine ⟨i - 1, Finset.mem_biUnion.2 ⟨y, hyY, ?_⟩, by omega⟩
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, a.symm⟩
    · right
      refine ⟨i + 1, Finset.mem_biUnion.2 ⟨y, hyY, ?_⟩, by omega⟩
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, a.symm⟩
  have c1 := Finset.card_le_card sub
  have c2 := Finset.card_image_le (s := P.image (· + 1) ∪ P.image (· - 1)) (f := w1.getVert)
  have c3 := Finset.card_union_le (P.image (· + 1)) (P.image (· - 1))
  have c4' := Finset.card_image_le (s := P) (f := (· + 1))
  have c5 := Finset.card_image_le (s := P) (f := (· - 1))
  omega

/-- **(B) Every bubble carries a position exceptional for `H ∪ Y ∪ {a₂, b₂}`.** -/
theorem bubble_escape (T : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2)
    {t t' p p' : ℕ} (htt : t + 2 ≤ t') (ht' : t' ≤ w1.length) (hp : p ≤ w2.length)
    (hp' : p' ≤ w2.length) (h1 : w1.getVert t = w2.getVert p)
    (h2 : w1.getVert t' = w2.getVert p')
    (hoff : ∀ s, t < s → s < t' → w1.getVert s ∉ w2.support) :
    ∃ s, t < s ∧ s < t' ∧
      ExcS (fun v => object.degree v = 3) w1 (escapeSet object w1 w2) s :=
  bubble_exc (Geo2.ofCount T.C E.1 E.2) (escapeSet object w1 w2)
    (fun z hz => by
      simp only [escapeSet, Finset.mem_union]
      left; left
      exact (JointObject.mem_hubs).2 hz)
    (fun z _ n1 n2 => by
      simp only [escapeSet, Finset.mem_union]
      left; right
      exact mem_Yset.2 ⟨n1, n2⟩)
    (by simp [escapeSet]) (by simp [escapeSet]) htt ht' hp hp' h1 h2 hoff

/-- **The crossing hubs are at most one more than the exceptional positions.** -/
theorem crossings_card (T : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2) :
    (crossings object w1 w2).card ≤
      (excPos (fun v => object.degree v = 3) w1 w2 (escapeSet object w1 w2)).card + 1 := by
  have Hg : Geo2 object.graph LengthOK (fun v => object.degree v = 3) w1 w2 :=
    Geo2.ofCount T.C E.1 E.2
  have ex := exitPos_le Hg (escapeSet object w1 w2)
    (fun z hz => by
      simp only [escapeSet, Finset.mem_union]
      left; left
      exact (JointObject.mem_hubs).2 hz)
    (fun z _ n1 n2 => by
      simp only [escapeSet, Finset.mem_union]
      left; right
      exact mem_Yset.2 ⟨n1, n2⟩)
    (by simp [escapeSet]) (by simp [escapeSet])
  have sub : crossings object w1 w2 ⊆ (exitPos w1 w2).image w1.getVert := by
    intro h hh
    obtain ⟨hH, m1, m2, hY, na1, nb1, na2, nb2⟩ := Finset.mem_filter.1 hh
    obtain ⟨t, rfl, ht⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m1
    obtain ⟨p, hp, hpl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 m2
    have ht0 : 0 < t := by
      by_contra z
      apply na1
      rw [show t = 0 by omega, SimpleGraph.Walk.getVert_zero]
    have htl : t < w1.length := by
      by_contra z
      apply nb1
      rw [show t = w1.length by omega, SimpleGraph.Walk.getVert_length]
    have hp0 : 0 < p := by
      by_contra z
      apply na2
      rw [← hp, show p = 0 by omega, SimpleGraph.Walk.getVert_zero]
    have hpl' : p < w2.length := by
      by_contra z
      apply nb2
      rw [← hp, show p = w2.length by omega, SimpleGraph.Walk.getVert_length]
    have out := crossing_exit T E ht0 htl hp0 hpl' hp.symm (hub4 T hH) (noY_of _ hY)
    rw [Finset.mem_image]
    refine ⟨t, ?_, rfl⟩
    simp only [exitPos, Finset.mem_filter, Finset.mem_range]
    exact ⟨htl, m2, out⟩
  have c1 := Finset.card_le_card sub
  have c2 := Finset.card_image_le (s := exitPos w1 w2) (f := w1.getVert)
  omega

/-- **(B, count) The crossing hubs are at most `25|Y| + 17`.** -/
theorem crossings_le (T : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2) :
    (crossings object w1 w2).card ≤ 25 * (Yset w1 w2).card + 17 := by
  have hY := hubsY_card T
  have c1 := coreOn_card T
  have c2 := coreOn_card T.swap
  rw [Yset_comm] at c2
  have cx := crossings_card T E
  -- the non-crossing hubs off `W₂` on `W₁`
  have hubPos_card : ((Finset.range (w1.length + 1)).filter
      fun s => w1.getVert s ∈ JointObject.hubs object ∧ w1.getVert s ∉ w2.support).card ≤
      (hubsY object w1 w2).card + 4 + (coreOn object w1 w2).card := by
    have sub : ((Finset.range (w1.length + 1)).filter
        fun s => w1.getVert s ∈ JointObject.hubs object ∧ w1.getVert s ∉ w2.support).image
          w1.getVert ⊆ hubsY object w1 w2 ∪ ({a1, b1, a2, b2} : Finset object.Vertex) ∪
            coreOn object w1 w2 := by
      intro h hh
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hh
      obtain ⟨hsr, hH, m2⟩ := Finset.mem_filter.1 hs
      simp only [Finset.mem_union]
      by_cases hy : ∃ y ∈ Yset w1 w2, object.graph.Adj (w1.getVert s) y
      · left; left; exact Finset.mem_filter.2 ⟨hH, hy⟩
      · by_cases he : w1.getVert s = a1 ∨ w1.getVert s = b1
        · left; right
          rcases he with e | e <;> simp [e]
        · right
          push Not at hy he
          exact Finset.mem_filter.2 ⟨hH, SimpleGraph.Walk.getVert_mem_support _ _, m2, hy,
            he.1, he.2⟩
    have inj : Set.InjOn w1.getVert ((Finset.range (w1.length + 1)).filter
        fun s => w1.getVert s ∈ JointObject.hubs object ∧ w1.getVert s ∉ w2.support :
          Set ℕ) := by
      intro s hs s' hs' e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hs hs'
      exact getVert_inj T.C.hp1 (by omega) (by omega) e
    have c := Finset.card_le_card sub
    rw [Finset.card_image_of_injOn inj] at c
    have u1 := Finset.card_union_le (hubsY object w1 w2 ∪
      ({a1, b1, a2, b2} : Finset object.Vertex)) (coreOn object w1 w2)
    have u2 := Finset.card_union_le (hubsY object w1 w2)
      ({a1, b1, a2, b2} : Finset object.Vertex)
    have e4 := Finset.card_le_four (a := a1) (b := b1) (c := a2) (d := b2)
    omega
  -- the exceptional set off `W₁`
  have S'_card : ((escapeSet object w1 w2).filter fun z => z ∉ w1.support).card ≤
      (Yset w1 w2).card + (hubsY object w1 w2).card + 4 + (coreOn object w2 w1).card := by
    have sub : (escapeSet object w1 w2).filter (fun z => z ∉ w1.support) ⊆
        Yset w1 w2 ∪ hubsY object w1 w2 ∪ ({a1, b1, a2, b2} : Finset object.Vertex) ∪
          coreOn object w2 w1 := by
      intro z hz
      obtain ⟨hzS, m1⟩ := Finset.mem_filter.1 hz
      simp only [escapeSet, Finset.mem_union] at hzS
      simp only [Finset.mem_union]
      rcases hzS with (hH | hYz) | hab
      · by_cases m2 : z ∈ w2.support
        · by_cases hy : ∃ y ∈ Yset w1 w2, object.graph.Adj z y
          · left; left; right; exact Finset.mem_filter.2 ⟨hH, hy⟩
          · by_cases he : z = a2 ∨ z = b2
            · left; right
              rcases he with e | e <;> simp [e]
            · right
              push Not at hy he
              refine Finset.mem_filter.2 ⟨hH, m2, m1, fun y hy' => hy y ?_, he.1, he.2⟩
              rw [Yset_comm] at hy'
              exact hy'
        · left; left; left
          exact mem_Yset.2 ⟨m1, m2⟩
      · left; left; left
        exact hYz
      · left; right
        simp only [Finset.mem_insert, Finset.mem_singleton] at hab ⊢
        tauto
    have c := Finset.card_le_card sub
    have u1 := Finset.card_union_le (Yset w1 w2 ∪ hubsY object w1 w2 ∪
      ({a1, b1, a2, b2} : Finset object.Vertex)) (coreOn object w2 w1)
    have u2 := Finset.card_union_le (Yset w1 w2 ∪ hubsY object w1 w2)
      ({a1, b1, a2, b2} : Finset object.Vertex)
    have u3 := Finset.card_union_le (Yset w1 w2) (hubsY object w1 w2)
    have e4 := Finset.card_le_four (a := a1) (b := b1) (c := a2) (d := b2)
    omega
  -- the exceptional positions
  have exc_card : (excPos (fun v => object.degree v = 3) w1 w2 (escapeSet object w1 w2)).card ≤
      ((Finset.range (w1.length + 1)).filter
        fun s => w1.getVert s ∈ JointObject.hubs object ∧ w1.getVert s ∉ w2.support).card +
      2 * ((escapeSet object w1 w2).filter fun z => z ∉ w1.support).card := by
    have sub : excPos (fun v => object.degree v = 3) w1 w2 (escapeSet object w1 w2) ⊆
        (Finset.range (w1.length + 1)).filter
          (fun s => w1.getVert s ∈ JointObject.hubs object ∧ w1.getVert s ∉ w2.support) ∪
        ((escapeSet object w1 w2).filter fun z => z ∉ w1.support).biUnion (nbrPos w1) := by
      intro s hs
      simp only [excPos, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨hsl, m2, hexc⟩ := hs
      rw [Finset.mem_union]
      rcases hexc with nc | ⟨z, hz, m1, adj⟩
      · left
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hsl, (JointObject.mem_hubs).2 nc, m2⟩
      · right
        rw [Finset.mem_biUnion]
        refine ⟨z, Finset.mem_filter.2 ⟨hz, m1⟩, ?_⟩
        simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
        exact ⟨hsl, adj.symm⟩
    have c := Finset.card_le_card sub
    have u := Finset.card_union_le ((Finset.range (w1.length + 1)).filter
          (fun s => w1.getVert s ∈ JointObject.hubs object ∧ w1.getVert s ∉ w2.support))
        (((escapeSet object w1 w2).filter fun z => z ∉ w1.support).biUnion (nbrPos w1))
    have b := pos_union_card T ((escapeSet object w1 w2).filter fun z => z ∉ w1.support)
    omega
  omega

/-- **(C) The hub count.** -/
theorem hub_count (T : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2) :
    (JointObject.hubs object).card ≤ 37 * (Yset w1 w2).card + 21 := by
  have hY := hubsY_card T
  have c1 := coreOn_card T
  have c2 := coreOn_card T.swap
  rw [Yset_comm] at c2
  have cx := crossings_le T E
  -- the partition of the hubs
  have sub : JointObject.hubs object ⊆ Yset w1 w2 ∪ hubsY object w1 w2 ∪
      ({a1, b1, a2, b2} : Finset object.Vertex) ∪ coreOn object w1 w2 ∪ coreOn object w2 w1 ∪
        crossings object w1 w2 := by
    intro h hH
    simp only [Finset.mem_union]
    by_cases hYh : h ∈ Yset w1 w2
    · left; left; left; left; left; exact hYh
    · by_cases hy : ∃ y ∈ Yset w1 w2, object.graph.Adj h y
      · left; left; left; left; right; exact Finset.mem_filter.2 ⟨hH, hy⟩
      · by_cases he : h = a1 ∨ h = b1 ∨ h = a2 ∨ h = b2
        · left; left; left; right
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact he
        · push Not at hy he
          rw [mem_Yset] at hYh
          by_cases m1 : h ∈ w1.support
          · by_cases m2 : h ∈ w2.support
            · right
              exact Finset.mem_filter.2 ⟨hH, m1, m2, hy, he.1, he.2.1, he.2.2.1, he.2.2.2⟩
            · left; left; right
              exact Finset.mem_filter.2 ⟨hH, m1, m2, hy, he.1, he.2.1⟩
          · have m2 : h ∈ w2.support := by
              by_contra m2
              exact hYh ⟨m1, m2⟩
            left; right
            refine Finset.mem_filter.2 ⟨hH, m2, m1, fun y hy' => hy y ?_, he.2.2.1, he.2.2.2⟩
            rw [Yset_comm] at hy'
            exact hy'
  have c := Finset.card_le_card sub
  have u1 := Finset.card_union_le (Yset w1 w2 ∪ hubsY object w1 w2 ∪
      ({a1, b1, a2, b2} : Finset object.Vertex) ∪ coreOn object w1 w2 ∪ coreOn object w2 w1)
    (crossings object w1 w2)
  have u2 := Finset.card_union_le (Yset w1 w2 ∪ hubsY object w1 w2 ∪
      ({a1, b1, a2, b2} : Finset object.Vertex) ∪ coreOn object w1 w2) (coreOn object w2 w1)
  have u3 := Finset.card_union_le (Yset w1 w2 ∪ hubsY object w1 w2 ∪
      ({a1, b1, a2, b2} : Finset object.Vertex)) (coreOn object w1 w2)
  have u4 := Finset.card_union_le (Yset w1 w2 ∪ hubsY object w1 w2)
      ({a1, b1, a2, b2} : Finset object.Vertex)
  have u5 := Finset.card_union_le (Yset w1 w2) (hubsY object w1 w2)
  have e4 := Finset.card_le_four (a := a1) (b := b1) (c := a2) (d := b2)
  omega

/-- **(C) The surplus is at most `|H| + |H_Y|·|Y|`.** -/
theorem sigma_count (T : Tri2 object LengthOK w1 w2) (base : MinimumDegreeAtLeast 3 object) :
    object.degreeSurplus 3 ≤
      (JointObject.hubs object).card + (hubsY object w1 w2).card * (Yset w1 w2).card := by
  rw [JointObject.degreeSurplus_eq base]
  have hsub : hubsY object w1 w2 ⊆ JointObject.hubs object := Finset.filter_subset _ _
  rw [← Finset.sum_sdiff hsub]
  have s1 : ∑ v ∈ JointObject.hubs object \ hubsY object w1 w2, (object.graph.degree v - 3) ≤
      (JointObject.hubs object \ hubsY object w1 w2).card := by
    have := Finset.sum_le_card_nsmul (JointObject.hubs object \ hubsY object w1 w2)
      (fun v => object.graph.degree v - 3) 1 (fun v hv => by
        obtain ⟨hH, hn⟩ := Finset.mem_sdiff.1 hv
        have hY : ∀ y ∈ Yset w1 w2, ¬ object.graph.Adj v y := by
          intro y hy a
          exact hn (Finset.mem_filter.2 ⟨hH, y, hy, a⟩)
        have := deg_le_four T v (noY_of v hY)
        omega)
    simpa using this
  have s2 : ∑ v ∈ hubsY object w1 w2, (object.graph.degree v - 3) ≤
      (hubsY object w1 w2).card * (1 + (Yset w1 w2).card) := by
    have := Finset.sum_le_card_nsmul (hubsY object w1 w2)
      (fun v => object.graph.degree v - 3) (1 + (Yset w1 w2).card) (fun v _ => by
        have := deg_le_Y T v
        omega)
    simpa using this
  have split := Finset.card_sdiff_add_card_eq_card hsub
  have e : (hubsY object w1 w2).card * (1 + (Yset w1 w2).card) =
      (hubsY object w1 w2).card + (hubsY object w1 w2).card * (Yset w1 w2).card := by ring
  omega

end Object

end Hypostructure.Graph.WalkHubEscape
