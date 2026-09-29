import Hypostructure.Graph.SpliceRoute
import Hypostructure.Graph.DoubleSuppress

/-!
# The route of the pair suppression: Mersenne paths

`DoubleSuppress.pair_suppression_dichotomy` gives a cycle of length `Lk + j`.  With routes
(`SpliceRoute`) the cycle is located: it runs through `pl u x` (then `x ⇝ pl` is a path of
length `Lk - 1` avoiding `u` and `v`), or through `y v q`, or through both.
-/

namespace Hypostructure.Graph.PairRoute

open SimpleGraph Hypostructure.Graph Hypostructure.Graph.SpliceLift
  Hypostructure.Graph.DoubleSuppress

universe u

variable {V : Type*} [DecidableEq V]

/-- Removing a vertex `u` with both its cycle edges from a cycle leaves a path. -/
theorem path_around {G : SimpleGraph V} {z u pl x : V} (d : G.Walk z z) (hd : d.IsCycle)
    (hne : pl ≠ x) (h1 : s(u, pl) ∈ d.edges) (h2 : s(u, x) ∈ d.edges) :
    ∃ M : G.Walk pl x, M.IsPath ∧ u ∉ M.support ∧ M.length + 2 = d.length ∧
      ∀ e ∈ M.edges, e ∈ d.edges := by
  obtain ⟨hadj, rest, hrest, hn, hl, hedges⟩ := exists_cycle_snd_edges d hd h2
  have h1' : s(u, pl) ∈ rest.edges := by
    rcases (hedges _).1 h1 with h | h
    · exfalso
      rcases Sym2.eq_iff.1 h with ⟨_, e⟩ | ⟨e, _⟩
      · exact hne e
      · exact G.ne_of_adj hadj e
    · exact h
  have hpath : rest.reverse.IsPath := hrest.reverse
  have he' : s(u, pl) ∈ rest.reverse.edges := by simpa using h1'
  obtain ⟨h', q', hq⟩ := path_first_step rest.reverse hpath he'
  rw [hq, Walk.cons_isPath_iff] at hpath
  refine ⟨q', hpath.1, hpath.2, ?_, ?_⟩
  · have : rest.reverse.length = rest.length := Walk.length_reverse _
    rw [hq, Walk.length_cons] at this
    omega
  · intro e he
    apply (hedges e).2
    right
    have : e ∈ rest.reverse.edges := by rw [hq, Walk.edges_cons]; exact List.mem_cons_of_mem _ he
    simpa using this

theorem edges_sc2 {G : SimpleGraph V} {a m b : V} (h1 : G.Adj a m) (h2 : G.Adj m b)
    (hab : a ≠ b) : (sc2 h1 h2 hab).p.edges = [s(a, m), s(m, b)] := rfl

theorem routeCompatible_family {G : SimpleGraph V} (c : Config G) :
    RouteCompatible c.family := by
  have n1 := c.hpu; have n2 := c.hyv; have n3 := c.hux; have n4 := c.hvq
  have n5 := c.huv; have n6 := c.hpx; have n7 := c.hpv; have n8 := c.hxv
  have n9 := c.hyq; have n10 := c.hyu; have n11 := c.hqu
  refine ⟨c.compatible_family, ?_, ?_⟩
  · intro s hs
    simp only [Config.family, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;>
      simp [edges_sc2, sc2, Sym2.eq_iff, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11,
        n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm,
        n10.symm, n11.symm]
  · unfold Config.family
    simp [List.pairwise_pair, edges_sc2, sc2, Sym2.eq_iff, c.hne, n1, n2, n3, n4, n5, n6, n7, n8,
      n9, n10, n11, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm,
      n9.symm, n10.symm, n11.symm]
    refine ⟨fun h1 h2 => c.hne ?_, fun h1 h2 => c.hne ?_⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact Sym2.eq_swap

theorem iso_u {G : SimpleGraph V} (c : Config G) (z : V) :
    ¬ (multiSplice G c.family).Adj c.u z := by
  simp only [Config.family, multiSplice, splice, interior_sc2, Set.mem_singleton_iff]
  change ¬ (((G.Adj c.u z ∧ ¬c.u = c.v ∧ ¬z = c.v ∨ s(c.u, z) = s(c.y, c.q) ∧ c.u ≠ z) ∧
      ¬True ∧ ¬z = c.u) ∨ s(c.u, z) = s(c.pl, c.x) ∧ c.u ≠ z)
  rintro (⟨_, h, _⟩ | ⟨h, _⟩)
  · exact h trivial
  · rcases Sym2.eq_iff.1 h with ⟨e, _⟩ | ⟨e, _⟩
    · exact c.hpu e.symm
    · exact c.hux e

theorem iso_v {G : SimpleGraph V} (c : Config G) (z : V) :
    ¬ (multiSplice G c.family).Adj c.v z := by
  simp only [Config.family, multiSplice, splice, interior_sc2, Set.mem_singleton_iff]
  change ¬ (((G.Adj c.v z ∧ ¬True ∧ ¬z = c.v ∨ s(c.v, z) = s(c.y, c.q) ∧ c.v ≠ z) ∧
      ¬c.v = c.u ∧ ¬z = c.u) ∨ s(c.v, z) = s(c.pl, c.x) ∧ c.v ≠ z)
  rintro (⟨(⟨_, h, _⟩ | ⟨h, _⟩), _, _⟩ | ⟨h, _⟩)
  · exact h trivial
  · rcases Sym2.eq_iff.1 h with ⟨e, _⟩ | ⟨e, _⟩
    · exact c.hyv e.symm
    · exact c.hvq e
  · rcases Sym2.eq_iff.1 h with ⟨e, _⟩ | ⟨e, _⟩
    · exact c.hpv e.symm
    · exact c.hxv e.symm

/-- The edges of a cycle of the excised graph avoid `u` and `v`. -/
theorem edge_avoids {G : SimpleGraph V} (c : Config G) {x : V}
    (cc : (multiSplice G c.family).Walk x x) {e : Sym2 V} (he : e ∈ cc.edges) :
    c.u ∉ e ∧ c.v ∉ e := by
  induction e using Sym2.ind with
  | h a b =>
    have hadj := cc.adj_of_mem_edges he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases Sym2.mem_iff.1 h with rfl | rfl
      · exact iso_u c b hadj
      · exact iso_u c a hadj.symm
    · rcases Sym2.mem_iff.1 h with rfl | rfl
      · exact iso_v c b hadj
      · exact iso_v c a hadj.symm

open Classical in
/-- **The route of the pair suppression: Mersenne paths.**  In a minimal target-avoiding `G`
with minimum degree `t`, for every configuration `c`: there is an accepted length `Lk` and
either a path `M : pl ⇝ x` avoiding `u, v` of length `Lk - 1` (the cycle through `pl u x`), or
a path `M : y ⇝ q` avoiding `u, v` of length `Lk - 1` (the cycle through `y v q`), or a cycle of
length `Lk + 2` through all four edges `u pl`, `u x`, `v y`, `v q`; the cycle lengths `Lk + 1`
(resp. `Lk + 2`) are not accepted. -/
theorem pair_route (G : FiniteObject.{u}) (c : Config G.graph) (t : Nat)
    (hG : MinimumDegreeAtLeast t G) (LengthOK : Nat → Prop)
    (avoids : ¬ HasCycleWithLength LengthOK G)
    (minimal : ∀ X : FiniteObject.{u}, MinimumDegreeAtLeast t X →
      X.LexicographicallySmaller G → HasCycleWithLength LengthOK X) :
    ∃ Lk : Nat, LengthOK Lk ∧
      ((∃ M : G.graph.Walk c.pl c.x, M.IsPath ∧ c.u ∉ M.support ∧ c.v ∉ M.support ∧
          M.length + 1 = Lk ∧ ¬ LengthOK (Lk + 1)) ∨
        (∃ M : G.graph.Walk c.y c.q, M.IsPath ∧ c.u ∉ M.support ∧ c.v ∉ M.support ∧
          M.length + 1 = Lk ∧ ¬ LengthOK (Lk + 1)) ∨
        (∃ (z : G.Vertex) (d : G.graph.Walk z z), d.IsCycle ∧ d.length = Lk + 2 ∧
          ¬ LengthOK (Lk + 2) ∧ s(c.u, c.pl) ∈ d.edges ∧ s(c.u, c.x) ∈ d.edges ∧
          s(c.v, c.y) ∈ d.edges ∧ s(c.v, c.q) ∈ d.edges)) := by
  have hu : c.u ∈ delSet c.family := by rw [c.delSet_family]; exact Or.inl rfl
  have hb : MinimumDegreeAtLeast t (multiSpliceObject G c.family) := by
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
  obtain ⟨x0, cc, hcc, hok, y0, d, hd, hnok, R1, R2, R3, R4⟩ :=
    multi_excision_route G c.family (routeCompatible_family c) c.u hu LengthOK avoids
      (MinimumDegreeAtLeast t) minimal hb
  have hn1 := c.hpu; have hn2 := c.hyv; have hn3 := c.hux; have hn4 := c.hvq
  have hn5 := c.huv; have hn6 := c.hpx; have hn7 := c.hpv; have hn8 := c.hxv
  have hn9 := c.hyq; have hn10 := c.hyu; have hn11 := c.hqu
  refine ⟨cc.length, hok, ?_⟩
  -- an edge of `d` touching `u` or `v` lies on the path of a used shortcut
  have touch : ∀ e ∈ d.edges, (c.u ∈ e ∨ c.v ∈ e) →
      ∃ sc ∈ c.family, s(sc.a, sc.b) ∈ cc.edges ∧ e ∈ sc.p.edges := by
    intro e he hev
    rcases R1 e he with h | h
    · exfalso
      have := edge_avoids c cc h
      rcases hev with h' | h'
      · exact this.1 h'
      · exact this.2 h'
    · exact h
  have hP1 : (sc2 c.adj_pl_u c.adj_u_x c.hpx) ∈ c.family := by simp [Config.family]
  have hP2 : (sc2 c.adj_y_v c.adj_v_q c.hyq) ∈ c.family := by simp [Config.family]
  have e1 : ∀ e ∈ (sc2 c.adj_pl_u c.adj_u_x c.hpx).p.edges,
      e = s(c.pl, c.u) ∨ e = s(c.u, c.x) := by
    intro e he; rw [edges_sc2] at he; simpa using he
  have e2 : ∀ e ∈ (sc2 c.adj_y_v c.adj_v_q c.hyq).p.edges,
      e = s(c.y, c.v) ∨ e = s(c.v, c.q) := by
    intro e he; rw [edges_sc2] at he; simpa using he
  have mem1 : s(c.pl, c.u) ∈ (sc2 c.adj_pl_u c.adj_u_x c.hpx).p.edges := by
    rw [edges_sc2]; simp
  have mem1' : s(c.u, c.x) ∈ (sc2 c.adj_pl_u c.adj_u_x c.hpx).p.edges := by
    rw [edges_sc2]; simp
  have mem2 : s(c.y, c.v) ∈ (sc2 c.adj_y_v c.adj_v_q c.hyq).p.edges := by
    rw [edges_sc2]; simp
  have mem2' : s(c.v, c.q) ∈ (sc2 c.adj_y_v c.adj_v_q c.hyq).p.edges := by
    rw [edges_sc2]; simp
  have vne1 : ∀ e, (e = s(c.pl, c.u) ∨ e = s(c.u, c.x)) → c.v ∉ e := by
    rintro e (rfl | rfl) <;> simp [Sym2.mem_iff, hn7.symm, hn5.symm, hn8.symm]
  have une2 : ∀ e, (e = s(c.y, c.v) ∨ e = s(c.v, c.q)) → c.u ∉ e := by
    rintro e (rfl | rfl) <;> simp [Sym2.mem_iff, hn10.symm, hn5, hn11.symm]
  by_cases h1 : s(c.pl, c.x) ∈ cc.edges <;> by_cases h2 : s(c.y, c.q) ∈ cc.edges
  · -- both shortcuts used
    right; right
    have hl : d.length = cc.length + 2 := by
      unfold Config.family at R4
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact h1),
        List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact h2), List.filter_nil] at R4
      exact R4.trans (congrArg (cc.length + ·) (rfl : (List.map Shortcut.shift [sc2 c.adj_pl_u c.adj_u_x c.hpx, sc2 c.adj_y_v c.adj_v_q c.hyq]).sum = 2))
    refine ⟨y0, d, hd, hl, fun h => hnok (hl ▸ h), ?_, ?_, ?_, ?_⟩
    · have := R3 _ hP1 h1 _ mem1; rwa [Sym2.eq_swap] at this
    · exact R3 _ hP1 h1 _ mem1'
    · have := R3 _ hP2 h2 _ mem2; rwa [Sym2.eq_swap] at this
    · exact R3 _ hP2 h2 _ mem2'
  · -- only `pl u x`
    left
    have hl : d.length = cc.length + 1 := by
      unfold Config.family at R4
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact h1),
        List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact h2), List.filter_nil] at R4
      exact R4.trans (congrArg (cc.length + ·) (rfl : (List.map Shortcut.shift [sc2 c.adj_pl_u c.adj_u_x c.hpx]).sum = 1))
    have he1 : s(c.u, c.pl) ∈ d.edges := by
      have := R3 _ hP1 h1 _ mem1; rwa [Sym2.eq_swap] at this
    have he2 : s(c.u, c.x) ∈ d.edges := R3 _ hP1 h1 _ mem1'
    obtain ⟨M, hM, huM, hlM, hed⟩ := path_around d hd c.hpx he1 he2
    refine ⟨M, hM, huM, ?_, by omega, fun h => hnok (hl ▸ h)⟩
    intro hv
    rcases (Walk.mem_support_iff_exists_mem_edges).1 hv with h | ⟨e, he, hve⟩
    · first | exact hn7 h.symm | exact hn8 h.symm
    · obtain ⟨sc, hsc, hused, hsce⟩ := touch e (hed e he) (Or.inr hve)
      simp only [Config.family, List.mem_cons, List.not_mem_nil, or_false] at hsc
      rcases hsc with rfl | rfl
      · exact vne1 e (e1 e hsce) hve
      · exact h2 hused
  · -- only `y v q`
    right; left
    have hl : d.length = cc.length + 1 := by
      unfold Config.family at R4
      rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact h1),
        List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact h2), List.filter_nil] at R4
      exact R4.trans (congrArg (cc.length + ·) (rfl : (List.map Shortcut.shift [sc2 c.adj_y_v c.adj_v_q c.hyq]).sum = 1))
    have he1 : s(c.v, c.y) ∈ d.edges := by
      have := R3 _ hP2 h2 _ mem2; rwa [Sym2.eq_swap] at this
    have he2 : s(c.v, c.q) ∈ d.edges := R3 _ hP2 h2 _ mem2'
    obtain ⟨M, hM, hvM, hlM, hed⟩ := path_around d hd c.hyq he1 he2
    refine ⟨M, hM, ?_, hvM, by omega, fun h => hnok (hl ▸ h)⟩
    intro hu'
    rcases (Walk.mem_support_iff_exists_mem_edges).1 hu' with h | ⟨e, he, hve⟩
    · first | exact hn10 h.symm | exact hn11 h.symm
    · obtain ⟨sc, hsc, hused, hsce⟩ := touch e (hed e he) (Or.inl hve)
      simp only [Config.family, List.mem_cons, List.not_mem_nil, or_false] at hsc
      rcases hsc with rfl | rfl
      · exact h1 hused
      · exact une2 e (e2 e hsce) hve
  · -- neither
    exfalso
    have hl : d.length = cc.length := by
      unfold Config.family at R4
      rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact h1),
        List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact h2), List.filter_nil] at R4
      exact R4
    exact hnok (hl ▸ hok)

end Hypostructure.Graph.PairRoute
