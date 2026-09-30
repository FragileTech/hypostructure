import Hypostructure.Graph.DensityCert.BlocksAux

/-!
# Density certificate: the block of a root and its hanging pieces (P1, P2)

For a connected admissible `G[W]` and a root `r ∈ W`:

* `blk G W r` is the vertex set of the bridgeless component of `r`: the vertices
  reachable from `r` inside `W` without crossing a bridge of `G[W]`.  It is
  either `{r}` or 2-connected with minimum degree `≥ 2` (P1: in a subcubic graph
  2-edge-connected pieces are 2-connected).
* `kids G W r` are the connected components of `G[W \ blk]`.  Each is joined to
  the block by exactly one edge `port C – att C` (a bridge).
* `dIn` is additive: every hanging piece adds `8` for its bridge.
* P2: induced paths concatenate across bridges, which bounds the longest
  induced paths of the pieces against each other.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `u v` is a bridge of `G[W]`. -/
def IsBridgeIn (G : SimpleGraph V) (W : Finset V) (u v : V) : Prop :=
  u ∈ W ∧ v ∈ W ∧ G.Adj u v ∧ ¬ ReachIn (G.deleteEdges {s(u, v)}) W u v

/-- The non-bridge edges of `G[W]` (as a graph on `V`). -/
def nonBridge (G : SimpleGraph V) (W : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ IsBridgeIn G W u v
  symm := ⟨fun u v h => by
    refine ⟨h.1.symm, fun hb => h.2 ⟨hb.2.1, hb.1, hb.2.2.1.symm, ?_⟩⟩
    intro hr
    apply hb.2.2.2
    have hs : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [hs]
    exact Relation.ReflTransGen.mono (fun a b h' => ⟨h'.2.1, h'.1, h'.2.2.symm⟩)
      (Relation.ReflTransGen.swap hr)⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

open Classical in
/-- The bridgeless component of `r` in `G[W]`. -/
noncomputable def blk (G : SimpleGraph V) (W : Finset V) (r : V) : Finset V :=
  W.filter fun v => ReachIn (nonBridge G W) W r v

open Classical in
/-- The component of `v` in `G[S]`. -/
noncomputable def compIn (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => ReachIn G S v w

open Classical in
/-- The pieces hanging off the block of `r`: components of `G[W \ blk]`. -/
noncomputable def kids (G : SimpleGraph V) (W : Finset V) (r : V) : Finset (Finset V) :=
  (W \ blk G W r).image (compIn G (W \ blk G W r))

open Classical in
/-- The bridge `(port, att)` joining a hanging piece `C` to the block
(`port ∈ blk`, `att ∈ C`); junk `(r, r)` if there is none. -/
noncomputable def bridgeOf (G : SimpleGraph V) (W : Finset V) (r : V) (C : Finset V) : V × V :=
  if h : ∃ pc : V × V, pc.1 ∈ blk G W r ∧ pc.2 ∈ C ∧ G.Adj pc.1 pc.2 then Classical.choose h
  else (r, r)

/-- The block vertex carrying the bridge to `C`. -/
noncomputable def port (G : SimpleGraph V) (W : Finset V) (r : V) (C : Finset V) : V :=
  (bridgeOf G W r C).1

/-- The vertex of `C` carrying the bridge. -/
noncomputable def att (G : SimpleGraph V) (W : Finset V) (r : V) (C : Finset V) : V :=
  (bridgeOf G W r C).2

section Aux

/-! Auxiliary facts about the block and the hanging pieces. -/

set_option linter.unusedSectionVars false

variable {G : SimpleGraph V} {W : Finset V} {r : V}

theorem mem_blk_iff {v : V} : v ∈ blk G W r ↔ v ∈ W ∧ ReachIn (nonBridge G W) W r v := by
  classical
  unfold blk
  exact Finset.mem_filter

theorem mem_compIn_iff {S : Finset V} {v w : V} :
    w ∈ compIn G S v ↔ w ∈ S ∧ ReachIn G S v w := by
  classical
  unfold compIn
  exact Finset.mem_filter

theorem mem_kids_iff {C : Finset V} :
    C ∈ kids G W r ↔ ∃ x ∈ W \ blk G W r, compIn G (W \ blk G W r) x = C := by
  unfold kids
  exact Finset.mem_image

theorem isBridgeIn_symm {u v : V} (h : IsBridgeIn G W u v) : IsBridgeIn G W v u := by
  refine ⟨h.2.1, h.1, h.2.2.1.symm, fun hr => h.2.2.2 ?_⟩
  rw [Sym2.eq_swap]
  exact reachIn_symm hr

/-- An edge whose ends are joined by non-bridge edges is not a bridge. -/
theorem not_bridge_of_reach {x y : V} (h : ReachIn (nonBridge G W) W x y) :
    ¬ IsBridgeIn G W x y := by
  intro hb
  apply hb.2.2.2
  refine Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, hab.2.1, ?_⟩) h
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hab.2.2.1, fun he => hab.2.2.2 ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hb
  · exact isBridgeIn_symm hb

theorem blk_sub' : blk G W r ⊆ W := fun _ hv => (mem_blk_iff.1 hv).1

theorem mem_blk_self' (hr : r ∈ W) : r ∈ blk G W r := mem_blk_iff.2 ⟨hr, .refl⟩

theorem not_bridge_of_mem_blk {x y : V} (hx : x ∈ blk G W r) (hy : y ∈ blk G W r) :
    ¬ IsBridgeIn G W x y :=
  not_bridge_of_reach (reachIn_trans (reachIn_symm (mem_blk_iff.1 hx).2) (mem_blk_iff.1 hy).2)

theorem mem_blk_of_adj {x y : V} (hx : x ∈ blk G W r) (hy : y ∈ W) (h : G.Adj x y)
    (hnb : ¬ IsBridgeIn G W x y) : y ∈ blk G W r :=
  mem_blk_iff.2 ⟨hy, (mem_blk_iff.1 hx).2.tail ⟨(mem_blk_iff.1 hx).1, hy, h, hnb⟩⟩

theorem blk_reachIn_of {v : V} (h : ReachIn (nonBridge G W) W r v) :
    ReachIn G (blk G W r) r v := by
  induction h with
  | refl => exact .refl
  | @tail b c hrb hbc ih =>
    exact ih.tail ⟨mem_blk_iff.2 ⟨hbc.1, hrb⟩, mem_blk_iff.2 ⟨hbc.2.1, hrb.tail hbc⟩, hbc.2.2.1⟩

theorem blk_reachIn {v : V} (hv : v ∈ blk G W r) : ReachIn G (blk G W r) r v :=
  blk_reachIn_of (mem_blk_iff.1 hv).2

theorem blk_connIn (hr : r ∈ W) : ConnIn G (blk G W r) :=
  ⟨⟨r, mem_blk_self' hr⟩, fun _ hu _ hv =>
    reachIn_trans (reachIn_symm (blk_reachIn hu)) (blk_reachIn hv)⟩

theorem resG_deleteEdges (s : Set (Sym2 V)) :
    (resG G W).deleteEdges s = resG (G.deleteEdges s) W := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, resG_adj]
  tauto

theorem isBridge_resG_of {x y : V} (h : IsBridgeIn G W x y) : (resG G W).IsBridge s(x, y) := by
  rw [SimpleGraph.isBridge_iff, resG_deleteEdges, ← reachIn_iff_reachable]
  exact h.2.2.2

/-- The cycle lemma: a block edge `v a` has a second block edge `v b` at `v`, and
`b`, `a` are joined inside the block avoiding `v`. -/
theorem blk_cyc {v a : V} (hv : v ∈ blk G W r) (ha : a ∈ blk G W r) (hva : G.Adj v a) :
    ∃ b ∈ blk G W r, b ≠ a ∧ G.Adj v b ∧ ReachIn G ((blk G W r).erase v) b a := by
  classical
  have hvW := blk_sub' hv
  have haW := blk_sub' ha
  have hre : ReachIn (G.deleteEdges {s(v, a)}) W v a := by
    by_contra hc
    exact not_bridge_of_mem_blk hv ha ⟨hvW, haW, hva, hc⟩
  rw [reachIn_iff_reachable] at hre
  obtain ⟨p⟩ := hre
  obtain ⟨q, hq⟩ : ∃ q : (resG (G.deleteEdges {s(v, a)}) W).Walk v a, q.IsPath :=
    ⟨p.bypass, p.bypass_isPath⟩
  have hKH : resG (G.deleteEdges {s(v, a)}) W ≤ resG G W := fun x y h =>
    ⟨h.1, h.2.1, ((SimpleGraph.deleteEdges_adj ..).1 h.2.2).1⟩
  have hav : (resG G W).Adj a v := ⟨haW, hvW, hva.symm⟩
  have hcyc : (SimpleGraph.Walk.cons hav (q.mapLe hKH)).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨hq.mapLe hKH, ?_⟩
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    intro he
    have h1 := q.edges_subset_edgeSet he
    rw [SimpleGraph.mem_edgeSet] at h1
    have h2 := (SimpleGraph.deleteEdges_adj ..).1 h1.2.2
    exact h2.2 (by rw [Sym2.eq_swap]; exact Set.mem_singleton _)
  have hsupp : ∀ x ∈ q.support, x ∈ blk G W r := by
    have hR := walk_support_rtg (R := fun x y => x ∈ W ∧ y ∈ W ∧ (nonBridge G W).Adj x y)
      (SimpleGraph.Walk.cons hav (q.mapLe hKH)) (fun x y hxy hH => ⟨hH.1, hH.2.1, hH.2.2,
        fun hb => (SimpleGraph.IsBridge.notMem_edges_of_isCycle (isBridge_resG_of hb) hcyc) hxy⟩)
    intro x hx
    have h1 : ReachIn (nonBridge G W) W a x := hR x (by
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_mapLe_eq_support]
      exact List.mem_cons_of_mem _ hx)
    exact mem_blk_iff.2 ⟨reachIn_mem h1 haW, reachIn_trans (mem_blk_iff.1 ha).2 h1⟩
  cases q with
  | nil => exact absurd rfl hva.ne
  | @cons _ b _ h q' =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hq
    have hG := (SimpleGraph.deleteEdges_adj ..).1 h.2.2
    refine ⟨b, hsupp b (by simp), ?_, hG.1, ?_⟩
    · rintro rfl
      exact hG.2 (Set.mem_singleton _)
    · refine walk_reachIn (K := resG (G.deleteEdges {s(v, a)}) W)
        (fun x y h => ((SimpleGraph.deleteEdges_adj ..).1 h.2.2).1) q' (fun x hx => ?_)
      refine Finset.mem_erase.2 ⟨?_, hsupp x (by simp [hx])⟩
      rintro rfl
      exact hq.2 hx

theorem blk_first_step {v u : V} (hv : v ∈ blk G W r) (hu : u ∈ blk G W r) (hne : v ≠ u) :
    ∃ a ∈ blk G W r, G.Adj v a ∧ ReachIn G ((blk G W r).erase v) a u :=
  reachIn_first_step (reachIn_trans (reachIn_symm (blk_reachIn hv)) (blk_reachIn hu)) hne

theorem compIn_sub {S : Finset V} {x : V} : compIn G S x ⊆ S :=
  fun _ h => (mem_compIn_iff.1 h).1

theorem self_mem_compIn {S : Finset V} {x : V} (hx : x ∈ S) : x ∈ compIn G S x :=
  mem_compIn_iff.2 ⟨hx, .refl⟩

theorem compIn_eq_of_mem {S : Finset V} {x y : V} (hy : y ∈ compIn G S x) :
    compIn G S y = compIn G S x := by
  have hxy := (mem_compIn_iff.1 hy).2
  ext z
  simp only [mem_compIn_iff]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, reachIn_trans hxy h⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, reachIn_trans (reachIn_symm hxy) h⟩

theorem compIn_reach {S : Finset V} {x y z : V} (hy : y ∈ compIn G S x)
    (hz : z ∈ compIn G S x) : ReachIn G S y z :=
  reachIn_trans (reachIn_symm (mem_compIn_iff.1 hy).2) (mem_compIn_iff.1 hz).2

theorem compIn_closed {S : Finset V} {x y z : V} (hy : y ∈ compIn G S x) (hz : z ∈ S)
    (h : G.Adj y z) : z ∈ compIn G S x :=
  mem_compIn_iff.2 ⟨hz, (mem_compIn_iff.1 hy).2.tail ⟨(mem_compIn_iff.1 hy).1, hz, h⟩⟩

theorem compIn_reach_inside {S : Finset V} {x y : V} (h : ReachIn G S x y) :
    ReachIn G (compIn G S x) x y := by
  induction h with
  | refl => exact .refl
  | @tail b c hxb hbc ih =>
    exact ih.tail ⟨mem_compIn_iff.2 ⟨hbc.1, hxb⟩, mem_compIn_iff.2 ⟨hbc.2.1, hxb.tail hbc⟩,
      hbc.2.2⟩

theorem compIn_connIn {S : Finset V} {x : V} (hx : x ∈ S) : ConnIn G (compIn G S x) :=
  ⟨⟨x, self_mem_compIn hx⟩, fun _ hu _ hv =>
    reachIn_trans (reachIn_symm (compIn_reach_inside (mem_compIn_iff.1 hu).2))
      (compIn_reach_inside (mem_compIn_iff.1 hv).2)⟩

theorem kid_sub {C : Finset V} (hC : C ∈ kids G W r) : C ⊆ W \ blk G W r := by
  obtain ⟨x, _, rfl⟩ := mem_kids_iff.1 hC
  exact compIn_sub

theorem kid_subW {C : Finset V} (hC : C ∈ kids G W r) : C ⊆ W :=
  fun _ hy => (Finset.mem_sdiff.1 (kid_sub hC hy)).1

theorem kid_disj_blk {C : Finset V} (hC : C ∈ kids G W r) : Disjoint C (blk G W r) := by
  rw [Finset.disjoint_left]
  intro y hy hyb
  exact (Finset.mem_sdiff.1 (kid_sub hC hy)).2 hyb

theorem kid_nonempty {C : Finset V} (hC : C ∈ kids G W r) : C.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := mem_kids_iff.1 hC
  exact ⟨x, self_mem_compIn hx⟩

theorem kid_closed {C : Finset V} (hC : C ∈ kids G W r) {y z : V} (hy : y ∈ C)
    (hz : z ∈ W \ blk G W r) (h : G.Adj y z) : z ∈ C := by
  obtain ⟨x, _, rfl⟩ := mem_kids_iff.1 hC
  exact compIn_closed hy hz h

theorem kid_reach {C : Finset V} (hC : C ∈ kids G W r) {y z : V} (hy : y ∈ C) (hz : z ∈ C) :
    ReachIn G (W \ blk G W r) y z := by
  obtain ⟨x, _, rfl⟩ := mem_kids_iff.1 hC
  exact compIn_reach hy hz

theorem kid_connIn {C : Finset V} (hC : C ∈ kids G W r) : ConnIn G C := by
  obtain ⟨x, hx, rfl⟩ := mem_kids_iff.1 hC
  exact compIn_connIn hx

theorem kid_disj {C C' : Finset V} (hC : C ∈ kids G W r) (hC' : C' ∈ kids G W r)
    (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨x, _, rfl⟩ := mem_kids_iff.1 hC
  obtain ⟨x', _, rfl⟩ := mem_kids_iff.1 hC'
  rw [Finset.disjoint_left]
  intro y hy hy'
  exact hne ((compIn_eq_of_mem hy).symm.trans (compIn_eq_of_mem hy'))

theorem mem_kid_of {v : V} (hv : v ∈ W) (hvb : v ∉ blk G W r) : ∃ C ∈ kids G W r, v ∈ C :=
  ⟨compIn G (W \ blk G W r) v, mem_kids_iff.2 ⟨v, Finset.mem_sdiff.2 ⟨hv, hvb⟩, rfl⟩,
    self_mem_compIn (Finset.mem_sdiff.2 ⟨hv, hvb⟩)⟩

theorem kid_edge_exists (hc : ConnIn G W) (hr : r ∈ W) {C : Finset V} (hC : C ∈ kids G W r) :
    ∃ pc : V × V, pc.1 ∈ blk G W r ∧ pc.2 ∈ C ∧ G.Adj pc.1 pc.2 := by
  by_contra hne
  have hne' : ∀ p ∈ blk G W r, ∀ c ∈ C, ¬ G.Adj p c := fun p hp c hc' h =>
    hne ⟨(p, c), hp, hc', h⟩
  obtain ⟨c, hcC⟩ := kid_nonempty hC
  have hcl : ∀ x ∈ C, ∀ y ∈ W, G.Adj x y → y ∈ C := by
    intro x hx y hy hxy
    by_cases hyb : y ∈ blk G W r
    · exact absurd hxy.symm (hne' y hyb x hx)
    · exact kid_closed hC hx (Finset.mem_sdiff.2 ⟨hy, hyb⟩) hxy
  have := reachIn_closed hcl (hc.2 c (kid_subW hC hcC) r hr) hcC
  exact Finset.disjoint_left.1 (kid_disj_blk hC) this (mem_blk_self' hr)

/-- A hanging piece is joined to the block by at most one edge. -/
theorem kid_edge_unique {C : Finset V} (hC : C ∈ kids G W r) {p1 c1 p2 c2 : V}
    (hp1 : p1 ∈ blk G W r) (hc1 : c1 ∈ C) (h1 : G.Adj p1 c1)
    (hp2 : p2 ∈ blk G W r) (hc2 : c2 ∈ C) (h2 : G.Adj p2 c2) : p1 = p2 ∧ c1 = c2 := by
  by_contra hne
  have hc1b : c1 ∉ blk G W r := Finset.disjoint_left.1 (kid_disj_blk hC) hc1
  have hp1C : p1 ∉ W \ blk G W r := fun h => (Finset.mem_sdiff.1 h).2 hp1
  apply hc1b
  refine mem_blk_of_adj hp1 (kid_subW hC hc1) h1 (fun hb => hb.2.2.2 ?_)
  have e1 : ReachIn (G.deleteEdges {s(p1, c1)}) W p1 p2 := by
    refine reachIn_deleteEdges blk_sub' (fun x hx y hy he => hc1b ?_)
      (reachIn_trans (reachIn_symm (blk_reachIn hp1)) (blk_reachIn hp2))
    have : c1 ∈ s(x, y) := by
      rw [Set.mem_singleton_iff.1 he]
      exact Sym2.mem_mk_right _ _
    rcases Sym2.mem_iff.1 this with rfl | rfl <;> assumption
  have e3 : ReachIn (G.deleteEdges {s(p1, c1)}) W c2 c1 := by
    refine reachIn_deleteEdges Finset.sdiff_subset (fun x hx y hy he => hp1C ?_)
      (kid_reach hC hc2 hc1)
    have : p1 ∈ s(x, y) := by
      rw [Set.mem_singleton_iff.1 he]
      exact Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.1 this with rfl | rfl <;> assumption
  have e2 : (G.deleteEdges {s(p1, c1)}).Adj p2 c2 := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨h2, fun he => ?_⟩
    rw [Set.mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne ⟨rfl, rfl⟩
    · exact hc1b hp2
  exact reachIn_trans e1 (Relation.ReflTransGen.head ⟨blk_sub' hp2, kid_subW hC hc2, e2⟩ e3)

theorem bridge_spec (hc : ConnIn G W) (hr : r ∈ W) {C : Finset V} (hC : C ∈ kids G W r) :
    port G W r C ∈ blk G W r ∧ att G W r C ∈ C ∧ G.Adj (port G W r C) (att G W r C) := by
  have h := kid_edge_exists hc hr hC
  unfold port att bridgeOf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem kid_bridge (hc : ConnIn G W) (hr : r ∈ W) {C : Finset V} (hC : C ∈ kids G W r) :
    ∀ u ∈ C, ∀ v ∈ W, v ∉ C → G.Adj u v → u = att G W r C ∧ v = port G W r C := by
  intro u hu v hv hvC huv
  obtain ⟨hp, ha', hpa⟩ := bridge_spec hc hr hC
  by_cases hvb : v ∈ blk G W r
  · obtain ⟨h1, h2⟩ := kid_edge_unique hC hvb hu huv.symm hp ha' hpa
    exact ⟨h2, h1⟩
  · exact absurd (kid_closed hC hu (Finset.mem_sdiff.2 ⟨hv, hvb⟩) huv) hvC

theorem kid_bridge_blk (hc : ConnIn G W) (hr : r ∈ W) {C : Finset V} (hC : C ∈ kids G W r) :
    ∀ u ∈ C, ∀ v ∈ blk G W r, G.Adj u v → u = att G W r C ∧ v = port G W r C :=
  fun u hu v hv huv => kid_bridge hc hr hC u hu v (blk_sub' hv)
    (fun h => Finset.disjoint_left.1 (kid_disj_blk hC) h hv) huv

theorem kids_pwd : ((kids G W r : Set (Finset V))).PairwiseDisjoint id :=
  fun _ hC _ hC' hne => kid_disj hC hC' hne

theorem blk_disj_kids : Disjoint (blk G W r) ((kids G W r).biUnion id) :=
  (Finset.disjoint_biUnion_right _ _ _).2 fun _ hC => (kid_disj_blk hC).symm

theorem W_eq_union : W = blk G W r ∪ (kids G W r).biUnion id := by
  ext v
  simp only [Finset.mem_union, Finset.mem_biUnion, id]
  constructor
  · intro hv
    by_cases hvb : v ∈ blk G W r
    · exact Or.inl hvb
    · exact Or.inr (mem_kid_of hv hvb)
  · rintro (h | ⟨C, hC, h⟩)
    · exact blk_sub' h
    · exact kid_subW hC h

end Aux

section API

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable (G : SimpleGraph V) (W : Finset V) (r : V)

/-! Standing hypotheses of every statement below: `ConnIn G W`, `AdmIn G W`, `r ∈ W`. -/

theorem mem_blk_self (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) : r ∈ blk G W r := by
  exact mem_blk_self' hr

theorem blk_subset : blk G W r ⊆ W := by
  exact blk_sub'

/-- P1: the block of `r` is `{r}` or 2-connected with minimum degree `≥ 2`. -/
theorem blk_twoConn (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W)
    (h2 : 2 ≤ (blk G W r).card) :
    TwoConnIn G (blk G W r) ∧ ∀ v ∈ blk G W r, 2 ≤ degIn G (blk G W r) v := by
  have hmate : ∀ v ∈ blk G W r, ∀ a ∈ blk G W r, G.Adj v a →
      ∃ b ∈ blk G W r, b ≠ a ∧ G.Adj v b ∧ ReachIn G ((blk G W r).erase v) a b := by
    intro v hv a ha hva
    obtain ⟨b, hb, hba, hvb, hr'⟩ := blk_cyc hv ha hva
    exact ⟨b, hb, hba, hvb, reachIn_symm hr'⟩
  refine ⟨⟨h2, blk_connIn hr, fun v hv => ⟨?_, fun u hu u' hu' => ?_⟩⟩, fun v hv => ?_⟩
  · obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne h2 v
    exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩
  · obtain ⟨huv, huB⟩ := Finset.mem_erase.1 hu
    obtain ⟨hu'v, hu'B⟩ := Finset.mem_erase.1 hu'
    obtain ⟨a, haB, hva, hau⟩ := blk_first_step hv huB (Ne.symm huv)
    obtain ⟨a', ha'B, hva', ha'u'⟩ := blk_first_step hv hu'B (Ne.symm hu'v)
    have key : ReachIn G ((blk G W r).erase v) a a' := by
      by_contra hna
      obtain ⟨b, hbB, hba, hvb, hab⟩ := hmate v hv a haB hva
      obtain ⟨b', hb'B, hb'a', hvb', ha'b'⟩ := hmate v hv a' ha'B hva'
      have n1 : a ≠ a' := by
        rintro rfl
        exact hna .refl
      have n2 : a ≠ b' := by
        rintro rfl
        exact hna (reachIn_symm ha'b')
      have n3 : b ≠ a' := by
        rintro rfl
        exact hna hab
      have n4 : b ≠ b' := by
        rintro rfl
        exact hna (reachIn_trans hab (reachIn_symm ha'b'))
      have hT : ({a, b, a', b'} : Finset V).card ≤ degIn G (blk G W r) v := by
        refine le_degIn fun x hx => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨haB, hva⟩
        · exact ⟨hbB, hvb⟩
        · exact ⟨ha'B, hva'⟩
        · exact ⟨hb'B, hvb'⟩
      have h4 : ({a, b, a', b'} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hba, n1, n2]),
          Finset.card_insert_of_notMem (by simp [n3, n4]), Finset.card_pair (Ne.symm hb'a')]
      have h3 := (degIn_mono (blk_subset G W r) v).trans (ha.1 v (blk_sub' hv))
      omega
    exact reachIn_trans (reachIn_symm hau) (reachIn_trans key ha'u')
  · obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne h2 v
    obtain ⟨a, haB, hva, _⟩ := blk_first_step hv hu (Ne.symm huv)
    obtain ⟨b, hbB, hba, hvb, _⟩ := hmate v hv a haB hva
    have hT : ({a, b} : Finset V).card ≤ degIn G (blk G W r) v := by
      refine le_degIn fun x hx => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨haB, hva⟩
      · exact ⟨hbB, hvb⟩
    rwa [Finset.card_pair (Ne.symm hba)] at hT

theorem blk_eq_singleton (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W)
    (h1 : (blk G W r).card < 2) : blk G W r = {r} := by
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨mem_blk_self' hr, fun x hx => ?_⟩
  exact Finset.card_le_one.1 (by omega) x hx r (mem_blk_self' hr)

/-- The hanging pieces are nonempty, pairwise disjoint, disjoint from the block,
and together with the block they cover `W`. -/
theorem kids_partition (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    (∀ C ∈ kids G W r, C.Nonempty ∧ C ⊆ W ∧ Disjoint C (blk G W r)) ∧
    (∀ C ∈ kids G W r, ∀ C' ∈ kids G W r, C ≠ C' → Disjoint C C') ∧
    (∀ v ∈ W, v ∉ blk G W r → ∃ C ∈ kids G W r, v ∈ C) := by
  exact ⟨fun C hC => ⟨kid_nonempty hC, kid_subW hC, kid_disj_blk hC⟩,
    fun C hC C' hC' hne => kid_disj hC hC' hne, fun v hv hvb => mem_kid_of hv hvb⟩

/-- Each hanging piece is joined to the rest of `W` by exactly one edge, the
bridge `port – att`; there are no edges between distinct pieces. -/
theorem kids_bridge (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    ∀ C ∈ kids G W r,
      port G W r C ∈ blk G W r ∧ att G W r C ∈ C ∧ G.Adj (port G W r C) (att G W r C) ∧
      (∀ u ∈ C, ∀ v ∈ W, v ∉ C → G.Adj u v → u = att G W r C ∧ v = port G W r C) := by
  intro C hC
  exact ⟨(bridge_spec hc hr hC).1, (bridge_spec hc hr hC).2.1, (bridge_spec hc hr hC).2.2,
    kid_bridge hc hr hC⟩

/-- Additivity of `8e − 11n` over the block and the hanging pieces. -/
theorem dIn_blk_kids (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    dIn G W = dIn G (blk G W r) + ∑ C ∈ kids G W r, (dIn G C + 8) := by
  have hpw := kids_pwd (G := G) (W := W) (r := r)
  have hu2 : ∀ C ∈ kids G W r, ∀ u ∈ blk G W r, ∀ v ∈ C, G.Adj u v →
      u = port G W r C ∧ v = att G W r C := fun C hC u hu v hv huv =>
    (kid_bridge_blk hc hr hC v hv u hu huv.symm).symm
  have s1 : ∀ C ∈ kids G W r, (∑ x ∈ blk G W r, degIn G C x) = 1 := fun C hC =>
    sum_degIn_eq_one (bridge_spec hc hr hC).1 (bridge_spec hc hr hC).2.1
      (bridge_spec hc hr hC).2.2 (kid_bridge_blk hc hr hC)
  have s2 : ∀ C ∈ kids G W r, (∑ x ∈ C, degIn G (blk G W r) x) = 1 := fun C hC =>
    sum_degIn_eq_one (bridge_spec hc hr hC).2.1 (bridge_spec hc hr hC).1
      (bridge_spec hc hr hC).2.2.symm (hu2 C hC)
  have z : ∀ C ∈ kids G W r, ∀ C' ∈ kids G W r, C ≠ C' → ∀ x ∈ C, degIn G C' x = 0 := by
    intro C hC C' hC' hne x hx
    classical
    unfold degIn
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hxy
    have hyC : y ∉ C := fun h => Finset.disjoint_left.1 (kid_disj hC hC' hne) h hy
    obtain ⟨_, rfl⟩ := kid_bridge hc hr hC x hx y (kid_subW hC' hy) hyC hxy
    exact Finset.disjoint_left.1 (kid_disj_blk hC') hy (bridge_spec hc hr hC).1
  have hsumU : ∑ x ∈ (kids G W r).biUnion id, degIn G ((kids G W r).biUnion id) x =
      ∑ C ∈ kids G W r, ∑ x ∈ C, degIn G C x := by
    rw [Finset.sum_biUnion hpw]
    refine Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun x hx => ?_
    rw [degIn_biUnion _ hpw, Finset.sum_eq_single_of_mem C hC
      (fun C' hC' hne => z C hC C' hC' (Ne.symm hne) x hx)]
  have hdU : dIn G ((kids G W r).biUnion id) = ∑ C ∈ kids G W r, dIn G C := by
    simp only [dIn_eq_sum]
    rw [hsumU, Finset.card_biUnion hpw, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    push_cast
    rfl
  have c1 : ∑ x ∈ blk G W r, degIn G ((kids G W r).biUnion id) x = (kids G W r).card := by
    simp only [degIn_biUnion _ hpw]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl s1
  have c2 : ∑ x ∈ (kids G W r).biUnion id, degIn G (blk G W r) x = (kids G W r).card := by
    rw [Finset.sum_biUnion hpw, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl s2
  have e := dIn_union (G := G) (blk_disj_kids (G := G) (W := W) (r := r))
  rw [← W_eq_union] at e
  rw [e, hdU, c1, c2, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- Degree in `W` = degree in the block + number of pieces hanging at the vertex. -/
theorem degIn_blk_kids (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    ∀ p ∈ blk G W r,
      degIn G W p = degIn G (blk G W r) p + ((kids G W r).filter fun C => port G W r C = p).card := by
  intro p hp
  have e := degIn_union (G := G) (blk_disj_kids (G := G) (W := W) (r := r)) p
  rw [← W_eq_union] at e
  rw [e, degIn_biUnion _ kids_pwd, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun C hC => ?_
  rw [degIn_eq_ite (A := blk G W r) (bridge_spec hc hr hC).2.1 (bridge_spec hc hr hC).2.2
    (kid_bridge_blk hc hr hC) hp]
  by_cases h : port G W r C = p
  · simp [h]
  · simp [h, Ne.symm h]

/-- The hanging pieces are admissible, connected, strictly smaller, and their
attachment vertex has degree `≤ 2` in them. -/
theorem kids_facts (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    ∀ C ∈ kids G W r,
      AdmIn G C ∧ ConnIn G C ∧ C.card < W.card ∧ degIn G C (att G W r C) ≤ 2 := by
  intro C hC
  refine ⟨ha.mono (kid_subW hC), kid_connIn hC, ?_, ?_⟩
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (kid_subW hC)]
    exact ⟨r, hr, fun h => Finset.disjoint_left.1 (kid_disj_blk hC) h (mem_blk_self' hr)⟩
  · obtain ⟨hp, hat, hpa⟩ := bridge_spec hc hr hC
    have h1 := degIn_union (G := G) (Finset.sdiff_disjoint : Disjoint (W \ C) C) (att G W r C)
    rw [Finset.sdiff_union_of_subset (kid_subW hC)] at h1
    have h2 : ({port G W r C} : Finset V).card ≤ degIn G (W \ C) (att G W r C) := by
      refine le_degIn fun x hx => ?_
      rw [Finset.mem_singleton.1 hx]
      exact ⟨Finset.mem_sdiff.2 ⟨blk_sub' hp, fun h => Finset.disjoint_left.1 (kid_disj_blk hC) h hp⟩,
        hpa.symm⟩
    have h3 := ha.1 _ (kid_subW hC hat)
    rw [Finset.card_singleton] at h2
    omega

/-- The block is admissible. -/
theorem blk_adm (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) : AdmIn G (blk G W r) := by
  exact ha.mono blk_sub'

/-- No induced path of `G[W]` has more than 12 vertices; in particular
`lamIn G W v ≤ 12`. -/
theorem lamIn_le_twelve (ha : AdmIn G W) (v : V) : lamIn G W v ≤ 12 := by
  exact lamIn_le_of_adm ha v

/-- P2 (i): a longest induced path of the block ending at the port, followed by
a longest induced path of the piece from its attachment vertex. -/
theorem lam_port_add_lam_att_le (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    ∀ C ∈ kids G W r,
      lamIn G (blk G W r) (port G W r C) + lamIn G C (att G W r C) ≤ 12 := by
  intro C hC
  obtain ⟨hp, hat, hpa⟩ := bridge_spec hc hr hC
  exact lam_add_lam_le ha blk_sub' (kid_subW hC) (kid_disj_blk hC).symm hp hat hpa
    (kid_bridge_blk hc hr hC)

/-- P2 (ii): two distinct pieces joined through an induced path of the block. -/
theorem lam_att_add_L_add_lam_att_le (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    ∀ C ∈ kids G W r, ∀ C' ∈ kids G W r, C ≠ C' →
      lamIn G C (att G W r C) + LIn G (blk G W r) (port G W r C) (port G W r C') +
        lamIn G C' (att G W r C') ≤ 12 := by
  intro C hC C' hC' hne
  obtain ⟨hp, hat, hpa⟩ := bridge_spec hc hr hC
  obtain ⟨hp', hat', hpa'⟩ := bridge_spec hc hr hC'
  refine lam_L_lam_le ha (kid_subW hC) blk_sub' (kid_subW hC') (kid_disj_blk hC)
    (kid_disj hC hC' hne) (kid_disj_blk hC').symm hat hp hat' hpa.symm hpa'
    (kid_bridge_blk hc hr hC) ?_
    (reachIn_trans (reachIn_symm (blk_reachIn hp)) (blk_reachIn hp'))
  · intro u hu v hv huv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact kid_bridge hc hr hC' u hu v (kid_subW hC hv)
        (fun h => Finset.disjoint_left.1 (kid_disj hC hC' hne) hv h) huv
    · exact kid_bridge_blk hc hr hC' u hu v hv huv

/-- P2 (iii): the root sees each piece through an induced path of the block. -/
theorem lam_root_ge (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    lamIn G (blk G W r) r ≤ lamIn G W r ∧
    ∀ C ∈ kids G W r,
      LIn G (blk G W r) r (port G W r C) + lamIn G C (att G W r C) ≤ lamIn G W r := by
  refine ⟨lamIn_mono blk_sub', fun C hC => ?_⟩
  obtain ⟨hp, hat, hpa⟩ := bridge_spec hc hr hC
  exact L_add_lam_le_lam blk_sub' (kid_subW hC) (kid_disj_blk hC).symm (mem_blk_self' hr) hat hpa
    (kid_bridge_blk hc hr hC) (blk_reachIn hp)

/-- The single-vertex path: `LIn G W v v = 1` and `1 ≤ lamIn G W v` for `v ∈ W`. -/
theorem LIn_self (v : V) (hv : v ∈ W) : LIn G W v v = 1 ∧ 1 ≤ lamIn G W v := by
  refine ⟨LIn_self_eq hv, ?_⟩
  have := le_lamIn (G := G) (W := W) (v := v) (IsIndPath.singleton v) (by simpa using hv) rfl
  simpa using this

/-- Bridge split (for the unrooted bound): removing a hanging piece `C` leaves a
connected admissible remainder, `dIn` splits with `+8`, the port has degree
`≤ 2` in the remainder, and the two sides' longest induced paths from the
bridge ends sum to at most 12. -/
theorem split_at_kid (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    ∀ C ∈ kids G W r,
      ConnIn G (W \ C) ∧ AdmIn G (W \ C) ∧ (W \ C).card < W.card ∧
      port G W r C ∈ W \ C ∧ degIn G (W \ C) (port G W r C) ≤ 2 ∧
      dIn G W = dIn G (W \ C) + dIn G C + 8 ∧
      lamIn G (W \ C) (port G W r C) + lamIn G C (att G W r C) ≤ 12 := by
  intro C hC
  obtain ⟨hp, hat, hpa⟩ := bridge_spec hc hr hC
  have hCW := kid_subW hC
  have hpC : port G W r C ∉ C := fun h => Finset.disjoint_left.1 (kid_disj_blk hC) h hp
  have hpWC : port G W r C ∈ W \ C := Finset.mem_sdiff.2 ⟨blk_sub' hp, hpC⟩
  have hblkWC : blk G W r ⊆ W \ C := fun x hx =>
    Finset.mem_sdiff.2 ⟨blk_sub' hx, fun h => Finset.disjoint_left.1 (kid_disj_blk hC) h hx⟩
  have huC : ∀ u ∈ C, ∀ v ∈ W \ C, G.Adj u v → u = att G W r C ∧ v = port G W r C :=
    fun u hu v hv huv =>
      kid_bridge hc hr hC u hu v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2 huv
  have huC' : ∀ u ∈ W \ C, ∀ v ∈ C, G.Adj u v → u = port G W r C ∧ v = att G W r C :=
    fun u hu v hv huv => (huC v hv u hu huv.symm).symm
  have hdisj : Disjoint (W \ C) C := Finset.sdiff_disjoint
  have hunion : W \ C ∪ C = W := Finset.sdiff_union_of_subset hCW
  have hreach : ∀ u ∈ W \ C, ReachIn G (W \ C) r u := by
    intro u hu
    by_cases hub : u ∈ blk G W r
    · exact reachIn_mono hblkWC (blk_reachIn hub)
    · obtain ⟨C', hC', huK⟩ := mem_kid_of (Finset.mem_sdiff.1 hu).1 hub
      have hC'ne : C' ≠ C := by
        rintro rfl
        exact (Finset.mem_sdiff.1 hu).2 huK
      have hC'WC : C' ⊆ W \ C := fun x hx => Finset.mem_sdiff.2 ⟨kid_subW hC' hx,
        fun h => Finset.disjoint_left.1 (kid_disj hC' hC hC'ne) hx h⟩
      obtain ⟨hp', hat', hpa'⟩ := bridge_spec hc hr hC'
      exact reachIn_trans (reachIn_mono hblkWC (blk_reachIn hp'))
        (Relation.ReflTransGen.head ⟨hblkWC hp', hC'WC hat', hpa'⟩
          (reachIn_mono hC'WC ((kid_connIn hC').2 _ hat' _ huK)))
  refine ⟨⟨⟨r, hblkWC (mem_blk_self' hr)⟩, fun u hu v hv =>
      reachIn_trans (reachIn_symm (hreach u hu)) (hreach v hv)⟩,
    ha.mono Finset.sdiff_subset, ?_, hpWC, ?_, ?_, ?_⟩
  · apply Finset.card_lt_card
    exact Finset.sdiff_ssubset hCW (kid_nonempty hC)
  · have h1 := degIn_union (G := G) hdisj (port G W r C)
    rw [hunion] at h1
    have h2 : ({att G W r C} : Finset V).card ≤ degIn G C (port G W r C) := by
      refine le_degIn fun x hx => ?_
      rw [Finset.mem_singleton.1 hx]
      exact ⟨hat, hpa⟩
    have h3 := ha.1 _ (blk_sub' hp)
    rw [Finset.card_singleton] at h2
    omega
  · have e := dIn_union (G := G) hdisj
    rw [hunion] at e
    rw [e, sum_degIn_eq_one hpWC hat hpa huC, sum_degIn_eq_one hat hpWC hpa.symm huC']
    push_cast
    ring
  · exact lam_add_lam_le ha Finset.sdiff_subset hCW hdisj hpWC hat hpa huC

/-- A bridgeless connected `W` is its own block. -/
theorem kids_empty_iff (hc : ConnIn G W) (ha : AdmIn G W) (hr : r ∈ W) :
    kids G W r = ∅ ↔ blk G W r = W := by
  constructor
  · intro h
    refine Finset.Subset.antisymm blk_sub' fun v hv => ?_
    by_contra hvb
    obtain ⟨C, hC, _⟩ := mem_kid_of hv hvb
    rw [h] at hC
    simp at hC
  · intro h
    unfold kids
    rw [h, Finset.sdiff_self, Finset.image_empty]

end API

end Hypostructure.Graph.DensityCert
