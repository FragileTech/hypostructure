import Hypostructure.Graph.SpliceLift

/-!
# Suppressing an edge with two cubic ends

Let `u v` be adjacent with `N(u) = {v, p, x}` and `N(v) = {u, y, q}`.  Delete `u` and `v` and
add the edges `p x` and `y q`.  Every degree is preserved when the new edges are new and
distinct; the result is smaller by `2`; a cycle of the result lifts to a cycle of `G` longer by
`0`, `1` or `2` (the two shortcuts are `p u x` and `y v q`).
-/

namespace Hypostructure.Graph.DoubleSuppress

open SimpleGraph Hypostructure.Graph Hypostructure.Graph.SpliceLift

universe u

variable {V : Type*}

/-- The shortcut `a — m — b` of length two. -/
def sc2 {G : SimpleGraph V} {a m b : V} (h1 : G.Adj a m) (h2 : G.Adj m b) (hab : a ≠ b) :
    Shortcut G where
  a := a
  b := b
  p := Walk.cons h1 (Walk.cons h2 Walk.nil)
  isPath := by
    have h1' := G.ne_of_adj h1
    have h2' := G.ne_of_adj h2
    simp [Walk.cons_isPath_iff, h1', h2', hab]
  two_le := by simp

theorem support_sc2 {G : SimpleGraph V} {a m b : V} (h1 : G.Adj a m) (h2 : G.Adj m b)
    (hab : a ≠ b) : (sc2 h1 h2 hab).p.support = [a, m, b] := rfl

theorem interior_sc2 {G : SimpleGraph V} {a m b : V} (h1 : G.Adj a m) (h2 : G.Adj m b)
    (hab : a ≠ b) : SpliceLift.interior (sc2 h1 h2 hab).p = {m} := by
  have h1' := G.ne_of_adj h1
  have h2' := G.ne_of_adj h2
  ext z
  simp only [SpliceLift.interior, sc2, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hza, hzb⟩
    rcases hz with rfl | rfl | rfl
    · exact absurd rfl hza
    · rfl
    · exact absurd rfl hzb
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl), h1'.symm, h2'⟩

/-- The configuration: an edge `u v` with `N(u) = {v, pl, x}`, `N(v) = {u, y, q}`, and the two
new edges `pl x`, `y q` new and distinct. -/
structure Config (G : SimpleGraph V) where
  u : V
  v : V
  pl : V
  x : V
  y : V
  q : V
  nu : ∀ z, G.Adj u z ↔ z = v ∨ z = pl ∨ z = x
  nv : ∀ z, G.Adj v z ↔ z = u ∨ z = y ∨ z = q
  hpx : pl ≠ x
  hpv : pl ≠ v
  hxv : x ≠ v
  hyq : y ≠ q
  hyu : y ≠ u
  hqu : q ≠ u
  hn1 : ¬ G.Adj pl x
  hn2 : ¬ G.Adj y q
  hne : s(pl, x) ≠ s(y, q)

namespace Config

variable {G : SimpleGraph V} (c : Config G)

theorem adj_pl_u : G.Adj c.pl c.u := ((c.nu c.pl).2 (Or.inr (Or.inl rfl))).symm
theorem adj_u_x : G.Adj c.u c.x := (c.nu c.x).2 (Or.inr (Or.inr rfl))
theorem adj_y_v : G.Adj c.y c.v := ((c.nv c.y).2 (Or.inr (Or.inl rfl))).symm
theorem adj_v_q : G.Adj c.v c.q := (c.nv c.q).2 (Or.inr (Or.inr rfl))
theorem adj_u_v : G.Adj c.u c.v := (c.nu c.v).2 (Or.inl rfl)
theorem huv : c.u ≠ c.v := G.ne_of_adj c.adj_u_v

/-- The two shortcuts `pl — u — x` and `y — v — q`. -/
def family : List (Shortcut G) :=
  [sc2 c.adj_pl_u c.adj_u_x c.hpx, sc2 c.adj_y_v c.adj_v_q c.hyq]

theorem delSet_family : delSet c.family = {c.u, c.v} := by
  simp only [family, delSet, interior_sc2]
  ext z; simp [or_comm]

theorem compatible_family : Compatible c.family := by
  have huv := c.huv
  have hux := G.ne_of_adj c.adj_u_x
  have hvq := G.ne_of_adj c.adj_v_q
  unfold Compatible family
  simp only [List.pairwise_pair, interior_sc2, support_sc2]
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_singleton_left]
    simp only [Set.mem_setOf_eq, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨c.hyu.symm, huv, c.hqu.symm⟩
  · rw [Set.disjoint_singleton_left]
    simp only [Set.mem_setOf_eq, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨c.hpv.symm, huv.symm, c.hxv.symm⟩

theorem adj_family {w z : V} (hwu : w ≠ c.u) (hwv : w ≠ c.v) (hzu : z ≠ c.u) (hzv : z ≠ c.v) :
    (multiSplice G c.family).Adj w z ↔
      G.Adj w z ∨ (s(w, z) = s(c.pl, c.x) ∧ w ≠ z) ∨ (s(w, z) = s(c.y, c.q) ∧ w ≠ z) := by
  simp only [family, multiSplice, splice, interior_sc2, Set.mem_singleton_iff]
  change ((G.Adj w z ∧ ¬w = c.v ∧ ¬z = c.v ∨ s(w, z) = s(c.y, c.q) ∧ w ≠ z) ∧ ¬w = c.u ∧
      ¬z = c.u ∨ s(w, z) = s(c.pl, c.x) ∧ w ≠ z) ↔ _
  constructor
  · rintro (⟨(⟨h, _, _⟩ | ⟨h, hne⟩), _, _⟩ | ⟨h, hne⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h, hne⟩)
    · exact Or.inr (Or.inl ⟨h, hne⟩)
  · rintro (h | ⟨h, hne⟩ | ⟨h, hne⟩)
    · exact Or.inl ⟨Or.inl ⟨h, hwv, hzv⟩, hwu, hzu⟩
    · exact Or.inr ⟨h, hne⟩
    · exact Or.inl ⟨Or.inr ⟨h, hne⟩, hwu, hzu⟩

end Config

open Classical in
/-- The degree of a kept vertex in the multiply excised object. -/
theorem degree_multiSpliceObject_eq (G : FiniteObject.{u}) (L : List (Shortcut G.graph))
    (w : G.Vertex) (hw : w ∈ G.vertexFinset.filter (fun v => v ∉ delSet L)) :
    (multiSpliceObject G L).degree ⟨w, hw⟩ =
      {z | z ∉ delSet L ∧ (multiSplice G.graph L).Adj w z}.ncard := by
  unfold multiSpliceObject
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have hset : ((FiniteObject.of (multiSplice G.graph L) G.vertices
      (fun _ _ => Classical.propDecidable _)).induce
      (G.vertexFinset.filter (fun v => v ∉ delSet L))).graph.neighborSet ⟨w, hw⟩ =
      (fun x : {x // x ∈ G.vertexFinset.filter (fun v => v ∉ delSet L)} => x.1) ⁻¹'
        {z | z ∉ delSet L ∧ (multiSplice G.graph L).Adj w z} := by
    ext x
    have hx : x.1 ∉ delSet L := (Finset.mem_filter.1 x.2).2
    simp only [SimpleGraph.mem_neighborSet, Set.mem_preimage, Set.mem_setOf_eq]
    change (multiSplice G.graph L).Adj w x.1 ↔ _
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [hset]
  refine Set.ncard_preimage_of_injective_subset_range Subtype.val_injective ?_
  intro z hz
  have hzv : z ∈ G.vertexFinset := by simp [FiniteObject.vertexFinset]
  exact ⟨⟨z, Finset.mem_filter.2 ⟨hzv, hz.1⟩⟩, rfl⟩

namespace Config

variable {G : SimpleGraph V} (c : Config G)

open Classical in
/-- The replacement neighbour of `u` (resp. `v`) at a kept vertex `w`. -/
noncomputable def repl (w : V) (z : V) : V :=
  if z = c.u then (if w = c.pl then c.x else c.pl)
  else if z = c.v then (if w = c.y then c.q else c.y) else z

theorem nbr_u {w : V} (hwv : w ≠ c.v) (h : G.Adj w c.u) : w = c.pl ∨ w = c.x := by
  rcases (c.nu w).1 h.symm with e | e | e
  · exact absurd e hwv
  · exact Or.inl e
  · exact Or.inr e

theorem nbr_v {w : V} (hwu : w ≠ c.u) (h : G.Adj w c.v) : w = c.y ∨ w = c.q := by
  rcases (c.nv w).1 h.symm with e | e | e
  · exact absurd e hwu
  · exact Or.inl e
  · exact Or.inr e

theorem hux : c.u ≠ c.x := G.ne_of_adj c.adj_u_x
theorem hvq : c.v ≠ c.q := G.ne_of_adj c.adj_v_q
theorem hpu : c.pl ≠ c.u := G.ne_of_adj c.adj_pl_u
theorem hyv : c.y ≠ c.v := G.ne_of_adj c.adj_y_v

/-- The kept vertices are adjacent to their replacement neighbours. -/
theorem repl_adj {w z : V} (hwu : w ≠ c.u) (hwv : w ≠ c.v) (hz : G.Adj w z) :
    (repl c w z ≠ c.u ∧ repl c w z ≠ c.v) ∧
      (multiSplice G c.family).Adj w (repl c w z) := by
  have hpu := c.hpu; have hyv := c.hyv; have hux := c.hux; have hvq := c.hvq
  unfold repl
  by_cases hzu : z = c.u
  · subst hzu
    rcases c.nbr_u hwv hz with rfl | rfl
    · simp only [if_true]
      refine ⟨⟨hux.symm, c.hxv⟩, ?_⟩
      rw [c.adj_family hwu hwv hux.symm c.hxv]
      exact Or.inr (Or.inl ⟨rfl, c.hpx⟩)
    · have hne : c.x ≠ c.pl := c.hpx.symm
      simp only [hne, if_false, if_true]
      refine ⟨⟨hpu, c.hpv⟩, ?_⟩
      rw [c.adj_family hwu hwv hpu c.hpv]
      exact Or.inr (Or.inl ⟨Sym2.eq_swap, c.hpx.symm⟩)
  · by_cases hzv : z = c.v
    · subst hzv
      rcases c.nbr_v hwu hz with rfl | rfl
      · simp only [hzu, if_false, if_true]
        refine ⟨⟨c.hqu, hvq.symm⟩, ?_⟩
        rw [c.adj_family hwu hwv c.hqu hvq.symm]
        exact Or.inr (Or.inr ⟨rfl, c.hyq⟩)
      · have hne : c.q ≠ c.y := c.hyq.symm
        simp only [hzu, hne, if_false, if_true]
        refine ⟨⟨c.hyu, hyv⟩, ?_⟩
        rw [c.adj_family hwu hwv c.hyu hyv]
        exact Or.inr (Or.inr ⟨Sym2.eq_swap, c.hyq.symm⟩)
    · simp only [hzu, hzv, if_false]
      refine ⟨⟨hzu, hzv⟩, ?_⟩
      rw [c.adj_family hwu hwv hzu hzv]
      exact Or.inl hz

theorem repl_other {w z : V} (hzu : z ≠ c.u) (hzv : z ≠ c.v) : repl c w z = z := by
  simp [repl, hzu, hzv]

theorem repl_u {w : V} (hwv : w ≠ c.v) (h : G.Adj w c.u) :
    (w = c.pl ∧ repl c w c.u = c.x) ∨ (w = c.x ∧ repl c w c.u = c.pl) := by
  rcases c.nbr_u hwv h with e | e
  · exact Or.inl ⟨e, by simp [repl, e]⟩
  · exact Or.inr ⟨e, by simp [repl, e, c.hpx.symm]⟩

theorem repl_v {w : V} (hwu : w ≠ c.u) (h : G.Adj w c.v) :
    (w = c.y ∧ repl c w c.v = c.q) ∨ (w = c.q ∧ repl c w c.v = c.y) := by
  have hvu : c.v ≠ c.u := c.huv.symm
  rcases c.nbr_v hwu h with e | e
  · exact Or.inl ⟨e, by simp [repl, e, hvu]⟩
  · exact Or.inr ⟨e, by simp [repl, e, c.hyq.symm, hvu]⟩

theorem caseA {w z : V} (hwu : w ≠ c.u) (hwv : w ≠ c.v) (hzu : z ≠ c.u) (hzv : z ≠ c.v)
    (hu : G.Adj w c.u) (hz : G.Adj w z) (heq : repl c w c.u = repl c w z) : False := by
  rw [c.repl_other hzu hzv] at heq
  rcases c.repl_u hwv hu with ⟨rfl, e⟩ | ⟨rfl, e⟩
  · rw [e] at heq; subst heq; exact c.hn1 hz
  · rw [e] at heq; subst heq; exact c.hn1 hz.symm

theorem caseB {w z : V} (hwu : w ≠ c.u) (hwv : w ≠ c.v) (hzu : z ≠ c.u) (hzv : z ≠ c.v)
    (hv : G.Adj w c.v) (hz : G.Adj w z) (heq : repl c w c.v = repl c w z) : False := by
  rw [c.repl_other hzu hzv] at heq
  rcases c.repl_v hwu hv with ⟨rfl, e⟩ | ⟨rfl, e⟩
  · rw [e] at heq; subst heq; exact c.hn2 hz
  · rw [e] at heq; subst heq; exact c.hn2 hz.symm

theorem caseC {w : V} (hwu : w ≠ c.u) (hwv : w ≠ c.v) (hu : G.Adj w c.u) (hv : G.Adj w c.v)
    (heq : repl c w c.u = repl c w c.v) : False := by
  apply c.hne
  rcases c.repl_u hwv hu with ⟨e1, r1⟩ | ⟨e1, r1⟩ <;>
    rcases c.repl_v hwu hv with ⟨e2, r2⟩ | ⟨e2, r2⟩ <;> rw [r1, r2] at heq
  · rw [e1.symm.trans e2, heq]
  · rw [e1.symm.trans e2, heq]; exact Sym2.eq_swap
  · rw [e1.symm.trans e2, heq]; exact Sym2.eq_swap
  · rw [e1.symm.trans e2, heq]

theorem repl_injOn {w : V} (hwu : w ≠ c.u) (hwv : w ≠ c.v) :
    Set.InjOn (repl c w) {z | G.Adj w z} := by
  intro z1 h1 z2 h2 heq
  simp only [Set.mem_setOf_eq] at h1 h2
  by_cases a1 : z1 = c.u
  · subst a1
    by_cases a2 : z2 = c.u
    · exact a2.symm
    by_cases b2 : z2 = c.v
    · subst b2; exact (c.caseC hwu hwv h1 h2 heq).elim
    · exact (c.caseA hwu hwv a2 b2 h1 h2 heq).elim
  by_cases b1 : z1 = c.v
  · subst b1
    by_cases a2 : z2 = c.u
    · subst a2; exact (c.caseC hwu hwv h2 h1 heq.symm).elim
    by_cases b2 : z2 = c.v
    · exact b2.symm
    · exact (c.caseB hwu hwv a2 b2 h1 h2 heq).elim
  · by_cases a2 : z2 = c.u
    · subst a2; exact (c.caseA hwu hwv a1 b1 h2 h1 heq.symm).elim
    by_cases b2 : z2 = c.v
    · subst b2; exact (c.caseB hwu hwv a1 b1 h2 h1 heq.symm).elim
    · rw [c.repl_other a1 b1, c.repl_other a2 b2] at heq
      exact heq

theorem shift_family : ∀ s ∈ c.family, s.shift = 1 := by
  intro s hs
  simp only [family, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> rfl

end Config

theorem sum_shift_eq_length {G : SimpleGraph V} :
    ∀ (S : List (Shortcut G)), (∀ s ∈ S, s.shift = 1) → (S.map Shortcut.shift).sum = S.length
  | [], _ => rfl
  | s :: S, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h s (List.mem_cons_self), sum_shift_eq_length S (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    omega

open Classical in
open Hypostructure.Graph in
theorem degree_le_multiSpliceObject (G : FiniteObject.{u}) (c : Config G.graph) (w : G.Vertex)
    (hw : w ∈ G.vertexFinset.filter (fun v => v ∉ delSet c.family)) :
    G.degree w ≤ (multiSpliceObject G c.family).degree ⟨w, hw⟩ := by
  have hwd : w ∉ delSet c.family := (Finset.mem_filter.1 hw).2
  rw [c.delSet_family] at hwd
  have hwu : w ≠ c.u := fun h => hwd (Or.inl h)
  have hwv : w ≠ c.v := fun h => hwd (Or.inr h)
  rw [degree_multiSpliceObject_eq, FiniteObject.degree_eq_ncard_neighborSet]
  letI : FinEnum G.Vertex := G.vertices
  apply Set.ncard_le_ncard_of_injOn (Config.repl c w)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, hadj⟩ := c.repl_adj hwu hwv hz
    refine ⟨?_, hadj⟩
    rw [c.delSet_family]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  · exact c.repl_injOn hwu hwv

open Classical in
open Hypostructure.Graph in
/-- **F08 for the suppression of a cubic edge.**  In a minimal target-avoiding `G` with
minimum degree `t`, for every configuration `c` (an edge `u v` with `N(u) = {v, pl, x}`,
`N(v) = {u, y, q}`, and the new edges `pl x`, `y q` new and distinct), `G` has a cycle of length
`Lk + j` with `Lk` accepted, `j ∈ {1, 2}`, and `Lk + j` not accepted. -/
theorem pair_suppression_dichotomy (G : FiniteObject.{u}) (c : Config G.graph) (t : Nat)
    (hG : MinimumDegreeAtLeast t G) (LengthOK : Nat → Prop)
    (avoids : ¬ HasCycleWithLength LengthOK G)
    (minimal : ∀ X : FiniteObject.{u}, MinimumDegreeAtLeast t X →
      X.LexicographicallySmaller G → HasCycleWithLength LengthOK X) :
    ∃ (Lk j : Nat) (y : G.Vertex) (d : G.graph.Walk y y),
      LengthOK Lk ∧ (j = 1 ∨ j = 2) ∧ ¬ LengthOK (Lk + j) ∧ d.IsCycle ∧ d.length = Lk + j := by
  have hu : c.u ∈ delSet c.family := by rw [c.delSet_family]; exact Or.inl rfl
  rcases multi_excision_dichotomy G c.family c.compatible_family c.u hu LengthOK avoids
      (MinimumDegreeAtLeast t) minimal with hb | ⟨S, Lk, y, d, hS, hok, hnok, hd, hl⟩
  · exfalso
    apply hb
    have hpl : c.pl ∈ G.vertexFinset.filter (fun v => v ∉ delSet c.family) := by
      refine Finset.mem_filter.2 ⟨by simp [FiniteObject.vertexFinset], ?_⟩
      rw [c.delSet_family]
      rintro (h | h)
      · exact c.hpu h
      · exact c.hpv h
    haveI : Nonempty (multiSpliceObject G c.family).Vertex := ⟨⟨c.pl, hpl⟩⟩
    apply FiniteObject.le_minDegree_of_forall_le_degree
    intro ⟨w, hw⟩
    exact hG.trans ((FiniteObject.minDegree_le_degree G w).trans
      (degree_le_multiSpliceObject G c w hw))
  · have hsum := sum_shift_eq_length S (fun s hs => c.shift_family s (hS.subset hs))
    have hlen : S.length ≤ 2 := by simpa [Config.family] using hS.length_le
    refine ⟨Lk, S.length, y, d, hok, ?_, by rwa [hsum] at hnok, hd, by rwa [hsum] at hl⟩
    rcases Nat.lt_or_ge S.length 1 with h0 | h1
    · exfalso
      have : S.length = 0 := by omega
      rw [hsum, this] at hnok
      simp at hnok
      exact hnok hok
    · omega

end Hypostructure.Graph.DoubleSuppress
