import Mathlib

/-!
# Hubs, cubic vertices and V-shapes in a degenerate, quadrilateral-free graph

Vocabulary-free, Mathlib-only.  `G` is a finite simple graph with
* `hmin`  : `δ ≥ 3`;
* `hind`  : vertices of degree `≥ 4` pairwise non-adjacent;
* `hC4`   : two distinct vertices have `≤ 1` common neighbour (no `C₄`);
* `hC8`   : no cycle of length 8;
* `hdeg`  : every nonempty proper vertex set spans a vertex of internal degree `≤ 2`
            (no proper induced subgraph has `δ ≥ 3`).

`L = {deg = 3}`, `H = {deg ≥ 4}`, `B = {deg ≥ 5}`, `σ = Σ (deg − 3)`, `n = |V|`.

* every cubic vertex has a cubic neighbour (`cubic_has_cubic_nbr`), so `5|H| + σ ≤ 2n`
  (`five_hub_bound`) and `|L| ≤ 2e(L)` (`LL_supply`);
* the components of `G[L]`, each dominated by a hub, give `2|B| + σ ≤ n` (`big_hub_bound`);
* V-shapes between two vertices of `B` number at most `12` (no `C₈`, `Vmid_card_le`), and the
  count of V-shapes against the surplus gives `24σ + 465|B| ≤ 18n + 375|B|²`
  (`high_surplus_bound`), i.e. `8n ≤ 32s + 125s²` with `s = n − σ` (`high_surplus_closure`);
* the parity of `L–L` edges on a walk (`ll_parity`, `forced_path_uses_LL`);
* the order windows `C r < σ ≤ n − 8` this refutes (`band_closed`, `first_band_closed`,
  `minimal_order_closed`).
-/

open Finset
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-! ## 0. The forest bound (any finite graph) -/

theorem comp_bound (Γ : SimpleGraph V) (c : Γ.ConnectedComponent) :
    2 * (univ.filter (· ∈ c.supp)).card ≤
      ∑ v ∈ univ.filter (· ∈ c.supp), Γ.degree v + 2 := by
  set T := Γ.induce c.supp with hT
  have hconn : T.Connected := c.connected_toSimpleGraph
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have hs := T.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : c.supp, T.degree v = Γ.degree v := by
    intro v
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro w hw
    exact c.mem_supp_of_adj_mem_supp v.2 hw
  have hcard : Nat.card c.supp = (univ.filter (· ∈ c.supp)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hE : Nat.card T.edgeSet = #T.edgeFinset := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  have hsum : ∑ v : c.supp, T.degree v = ∑ v ∈ univ.filter (· ∈ c.supp), Γ.degree v := by
    rw [Finset.sum_subtype (univ.filter (· ∈ c.supp)) (p := (· ∈ c.supp)) (by simp)]
    exact Finset.sum_congr rfl (fun v _ => hdeg v)
  omega

/-- **Forest bound**: `2|V| ≤ Σ deg + 2·#components`. -/
theorem card_le_degsum_comp (Γ : SimpleGraph V) :
    2 * Fintype.card V ≤ ∑ v, Γ.degree v + 2 * Fintype.card Γ.ConnectedComponent := by
  have hpart : ∀ f : V → ℕ, ∑ v, f v =
      ∑ c : Γ.ConnectedComponent, ∑ v ∈ univ.filter (· ∈ c.supp), f v := by
    intro f
    rw [← Finset.sum_fiberwise univ (fun v => Γ.connectedComponentMk v) f]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr
    · ext v; simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
    · intros; rfl
  have hc := hpart (fun _ => 1)
  have hd := hpart (fun v => Γ.degree v)
  simp only [sum_const, smul_eq_mul, mul_one, card_univ] at hc
  rw [hc, hd, ← Finset.card_univ, Finset.mul_sum, Finset.card_eq_sum_ones, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun c _ => ?_)
  simpa using comp_bound Γ c

/-! ## 1. Vocabulary -/

/-- Codegree `≤ 1` (no `C₄`). -/
abbrev C4Free : Prop :=
  ∀ a b c c' : V, a ≠ b → G.Adj a c → G.Adj b c → G.Adj a c' → G.Adj b c' → c = c'

/-- No cycle of length `k` (injective cyclic sequence). -/
abbrev NoCycleLen (k : ℕ) [NeZero k] : Prop :=
  ∀ f : Fin k → V, Function.Injective f → ¬ ∀ i : Fin k, G.Adj (f i) (f (i + 1))

/-- `noProperBaseline`, induced form. -/
abbrev ProperTwoLow : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ univ → ∃ v ∈ S, (G.neighborFinset v ∩ S).card ≤ 2

noncomputable abbrev Lset : Finset V := univ.filter (fun v => G.degree v = 3)
noncomputable abbrev Hset : Finset V := univ.filter (fun v => 4 ≤ G.degree v)
noncomputable abbrev Bset : Finset V := univ.filter (fun v => 5 ≤ G.degree v)
noncomputable abbrev sigma : ℕ := ∑ v, (G.degree v - 3)

/-- No `C₄` ⇒ codegree `≤ 1`. -/
theorem c4Free_of_noCycle4 (h4 : NoCycleLen G 4) : C4Free G := by
  intro a b c c' hab hac hbc hac' hbc'
  by_contra hcc
  apply h4 ![a, c, b, c']
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    all_goals first
      | exact absurd hij hab | exact absurd hij.symm hab
      | exact absurd hij hcc | exact absurd hij.symm hcc
      | exact absurd hij (G.ne_of_adj hac) | exact absurd hij.symm (G.ne_of_adj hac)
      | exact absurd hij (G.ne_of_adj hbc) | exact absurd hij.symm (G.ne_of_adj hbc)
      | exact absurd hij (G.ne_of_adj hac') | exact absurd hij.symm (G.ne_of_adj hac')
      | exact absurd hij (G.ne_of_adj hbc') | exact absurd hij.symm (G.ne_of_adj hbc')
  · intro i
    fin_cases i
    · exact hac
    · exact hbc.symm
    · exact hbc'
    · exact hac'.symm

/-! ## 2. Double counting and the hub sum -/

theorem inter_eq_filter (a : V) (C : Finset V) :
    G.neighborFinset a ∩ C = C.filter (fun c => G.Adj a c) := by
  ext; simp [and_comm]

theorem double_count (A C : Finset V) :
    ∑ a ∈ A, (G.neighborFinset a ∩ C).card = ∑ c ∈ C, (G.neighborFinset c ∩ A).card := by
  simp only [inter_eq_filter, card_filter]
  rw [sum_comm]
  simp [G.adj_comm]

theorem split_card (S T : Finset V) : (S ∩ T).card + (S \ T).card = S.card := by
  rw [add_comm]; exact card_sdiff_add_card_inter S T

variable {G}

theorem deg_three_of_hub_adj (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    {h a : V} (hh : 4 ≤ G.degree h) (ha : G.Adj h a) : G.degree a = 3 := by
  have := hmin a
  by_contra hne
  exact hind h a hh (by omega) ha

theorem L_eq_compl (hmin : ∀ v, 3 ≤ G.degree v) : Lset G = univ \ Hset G := by
  ext v; simp only [mem_filter, mem_univ, true_and, mem_sdiff]; have := hmin v; omega

theorem card_L_add_H (hmin : ∀ v, 3 ≤ G.degree v) :
    (Lset G).card + (Hset G).card = Fintype.card V := by
  rw [L_eq_compl hmin, card_sdiff_of_subset (subset_univ _), card_univ]
  have : (Hset G).card ≤ Fintype.card V := card_le_univ _
  omega

/-- `Σ_H deg = 3|H| + σ`. -/
theorem hub_sum (hmin : ∀ v, 3 ≤ G.degree v) :
    ∑ h ∈ Hset G, G.degree h = 3 * (Hset G).card + sigma G := by
  have hs : sigma G = ∑ h ∈ Hset G, (G.degree h - 3) := by
    unfold sigma
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · have := hmin v; omega
  rw [hs, card_eq_sum_ones, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  simp only [mem_filter] at hv
  omega

/-- `Σ_H deg = Σ_B deg + 4(|H| − |B|)`. -/
theorem hub_sum_split :
    ∑ h ∈ Hset G, G.degree h + 4 * (Bset G).card
      = ∑ b ∈ Bset G, G.degree b + 4 * (Hset G).card := by
  have hBH : Bset G = (Hset G).filter (fun v => 5 ≤ G.degree v) := by
    ext v; simp only [mem_filter, mem_univ, true_and]; omega
  have e1 : ∑ b ∈ Bset G, G.degree b =
      ∑ h ∈ Hset G, (if 5 ≤ G.degree h then G.degree h else 0) := by
    rw [hBH, sum_filter]
  have e2 : (Bset G).card = ∑ h ∈ Hset G, (if 5 ≤ G.degree h then 1 else 0) := by
    rw [hBH, card_filter]
  have e3 : (Hset G).card = ∑ h ∈ Hset G, 1 := card_eq_sum_ones _
  rw [e1, e2, e3, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have hv4 : 4 ≤ G.degree v := by simpa using hv
  split_ifs with h
  · ring
  · omega

/-! ## 3. Step 1: every cubic vertex has a cubic neighbour (near-bipartite refuted) -/

theorem cubic_has_cubic_nbr (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G)
    {v : V} (hv : G.degree v = 3) : ∃ u, G.Adj v u ∧ G.degree u = 3 := by
  by_contra hno
  push Not at hno
  have hS : (univ.erase v).Nonempty := by
    have : 0 < G.degree v := by omega
    obtain ⟨u, hu⟩ := G.degree_pos_iff_exists_adj v |>.1 this
    exact ⟨u, mem_erase.2 ⟨(G.ne_of_adj hu).symm, mem_univ _⟩⟩
  obtain ⟨w, hw, hwl⟩ := hdeg (univ.erase v) hS (fun h => by
    have := mem_univ v; rw [← h] at this; simp at this)
  have hwv : w ≠ v := (mem_erase.1 hw).1
  have hsub : G.neighborFinset w ∩ univ.erase v = (G.neighborFinset w).erase v := by
    ext x; simp [and_comm]
  rw [hsub] at hwl
  have hc := card_erase_le (s := G.neighborFinset w) (a := v)
  by_cases hadj : G.Adj v w
  · have h4 : G.degree w ≠ 3 := hno w hadj
    have := hmin w
    have hmem : v ∈ G.neighborFinset w := by simpa using hadj.symm
    rw [card_erase_of_mem hmem, G.card_neighborFinset_eq_degree] at hwl
    omega
  · have hmem : v ∉ G.neighborFinset w := by simpa [G.adj_comm] using hadj
    rw [erase_eq_of_notMem hmem, G.card_neighborFinset_eq_degree] at hwl
    have := hmin w
    omega

/-- For `v ∈ L`: `|N(v) ∩ H| ≤ 2`. -/
theorem cubic_hub_nbrs_le_two (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G)
    {v : V} (hv : G.degree v = 3) : (G.neighborFinset v ∩ Hset G).card ≤ 2 := by
  obtain ⟨u, hu, hu3⟩ := cubic_has_cubic_nbr hmin hdeg hv
  have hsub : G.neighborFinset v ∩ Hset G ⊆ (G.neighborFinset v).erase u := by
    intro x hx
    simp only [mem_inter, mem_filter, mem_univ, true_and] at hx
    refine mem_erase.2 ⟨fun h => ?_, hx.1⟩
    subst h; omega
  have hmem : u ∈ G.neighborFinset v := by simpa using hu
  have := card_le_card hsub
  rw [card_erase_of_mem hmem, G.card_neighborFinset_eq_degree] at this
  omega

/-- **(Step 1, numeric)** `5|H| + σ ≤ 2n`. -/
theorem five_hub_bound (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G) :
    5 * (Hset G).card + sigma G ≤ 2 * Fintype.card V := by
  have h1 : ∑ h ∈ Hset G, G.degree h = ∑ h ∈ Hset G, (G.neighborFinset h ∩ Lset G).card := by
    apply sum_congr rfl
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext a
    simp only [mem_inter, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨fun ha => ⟨ha, deg_three_of_hub_adj hmin hind hh ha⟩, fun ha => ha.1⟩
  have h2 := double_count G (Hset G) (Lset G)
  have h3 : ∑ v ∈ Lset G, (G.neighborFinset v ∩ Hset G).card ≤ ∑ v ∈ Lset G, 2 :=
    sum_le_sum (fun v hv => cubic_hub_nbrs_le_two hmin hdeg (by simpa using hv))
  rw [sum_const, smul_eq_mul] at h3
  have h4 := hub_sum hmin
  have h5 := card_L_add_H hmin
  omega

/-- **Supply of `L–L` edges**: `|L| ≤ Σ_{v∈L} |N(v) ∩ L| = 2e(L)`. -/
theorem LL_supply (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G) :
    (Lset G).card ≤ ∑ v ∈ Lset G, (G.neighborFinset v ∩ Lset G).card := by
  rw [card_eq_sum_ones]
  apply sum_le_sum
  intro v hv
  simp only [mem_filter, mem_univ, true_and] at hv
  obtain ⟨u, hu, hu3⟩ := cubic_has_cubic_nbr hmin hdeg hv
  exact card_pos.2 ⟨u, by simp [hu, hu3]⟩

/-! ## 4. Step 2: the components of `G[L]` and `2|B| + σ ≤ n` -/

variable (G) in
/-- `Γ`: the `L–L` edges of `G`, on all of `V` (hubs are isolated in `Γ`). -/
def cubicGraph : SimpleGraph V where
  Adj u v := G.Adj u v ∧ G.degree u = 3 ∧ G.degree v = 3
  symm := ⟨fun _ _ ⟨h, a, b⟩ => ⟨h.symm, b, a⟩⟩
  loopless := ⟨fun v ⟨h, _, _⟩ => G.irrefl h⟩

theorem cubicGraph_degree (v : V) :
    (cubicGraph G).degree v =
      if G.degree v = 3 then (G.neighborFinset v ∩ Lset G).card else 0 := by
  rw [← (cubicGraph G).card_neighborFinset_eq_degree]
  split_ifs with h
  · congr 1
    ext w
    simp [cubicGraph, h]
  · rw [card_eq_zero]
    ext w
    simp [cubicGraph, h]

theorem hub_deg_eq_inter_L (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) :
    ∑ h ∈ Hset G, G.degree h = ∑ h ∈ Hset G, (G.neighborFinset h ∩ Lset G).card := by
  apply sum_congr rfl
  intro h hh
  simp only [mem_filter, mem_univ, true_and] at hh
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext a
  simp only [mem_inter, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact ⟨fun ha => ⟨ha, deg_three_of_hub_adj hmin hind hh ha⟩, fun ha => ha.1⟩

/-- `Σ_v deg_Γ v + Σ_H deg = 3|L|`. -/
theorem cubic_degsum (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) :
    ∑ v, (cubicGraph G).degree v + ∑ h ∈ Hset G, G.degree h = 3 * (Lset G).card := by
  have e1 : ∑ v, (cubicGraph G).degree v = ∑ v ∈ Lset G, (G.neighborFinset v ∩ Lset G).card := by
    simp_rw [cubicGraph_degree]
    rw [sum_filter]
  rw [e1, hub_deg_eq_inter_L hmin hind, double_count G (Hset G) (Lset G), ← sum_add_distrib,
    card_eq_sum_ones (Lset G), mul_sum]
  apply sum_congr rfl
  intro v hv
  simp only [mem_filter, mem_univ, true_and] at hv
  have hs := split_card (G.neighborFinset v) (Hset G)
  have hLH : G.neighborFinset v \ Hset G = G.neighborFinset v ∩ Lset G := by
    ext w; simp only [mem_sdiff, mem_inter, mem_filter, mem_univ, true_and]
    have := hmin w
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [hLH, G.card_neighborFinset_eq_degree, hv] at hs
  omega

variable (G) in
noncomputable abbrev hubComps : Finset (cubicGraph G).ConnectedComponent :=
  (Hset G).image (cubicGraph G).connectedComponentMk

variable (G) in
/-- The `L`-components dominated by the hub `h`: `|N(h) ∩ c| ≥ deg h − 2`. -/
noncomputable abbrev domComps (h : V) : Finset (cubicGraph G).ConnectedComponent :=
  univ.filter (fun c => c ∉ hubComps G ∧
    G.degree h - 2 ≤ (G.neighborFinset h ∩ univ.filter (· ∈ c.supp)).card)

/-- A hub dominates at most two components, and at most one if `deg ≥ 5`. -/
theorem domComps_card {h : V} (hh : 4 ≤ G.degree h) :
    (domComps G h).card + (if 5 ≤ G.degree h then 1 else 0) ≤ 2 := by
  have hdisj : ∀ c ∈ domComps G h, ∀ c' ∈ domComps G h, c ≠ c' →
      Disjoint (G.neighborFinset h ∩ univ.filter (· ∈ c.supp))
        (G.neighborFinset h ∩ univ.filter (· ∈ c'.supp)) := by
    intro c _ c' _ hcc
    rw [disjoint_left]
    intro v hv hv'
    simp only [mem_inter, mem_filter, mem_univ, true_and,
      SimpleGraph.ConnectedComponent.mem_supp_iff] at hv hv'
    exact hcc (hv.2.symm.trans hv'.2)
  have hsum := card_biUnion hdisj
  have hsub : (domComps G h).biUnion (fun c => G.neighborFinset h ∩ univ.filter (· ∈ c.supp))
      ⊆ G.neighborFinset h := biUnion_subset.2 (fun _ _ => inter_subset_left)
  have hle := card_le_card hsub
  rw [hsum, G.card_neighborFinset_eq_degree] at hle
  have hlow : ∑ c ∈ domComps G h, (G.degree h - 2) ≤
      ∑ c ∈ domComps G h, (G.neighborFinset h ∩ univ.filter (· ∈ c.supp)).card :=
    sum_le_sum (fun c hc => (mem_filter.1 hc).2.2)
  rw [sum_const, smul_eq_mul] at hlow
  have key : (domComps G h).card * (G.degree h - 2) ≤ G.degree h := hlow.trans hle
  set k := (domComps G h).card
  set d := G.degree h
  split_ifs with h5
  · by_contra hc
    have hk : 2 ≤ k := by omega
    have := Nat.mul_le_mul_right (d - 2) hk
    omega
  · by_contra hc
    have hk : 3 ≤ k := by omega
    have := Nat.mul_le_mul_right (d - 2) hk
    omega

/-- **Domination**: every component of `Γ` without a hub has a hub `h` with
`|N(h) ∩ c| ≥ deg h − 2` (noProperBaseline at `S = V ∖ c`). -/
theorem dominate (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G)
    (hH : (Hset G).Nonempty) (c : (cubicGraph G).ConnectedComponent) (hc : c ∉ hubComps G) :
    ∃ h ∈ Hset G, c ∈ domComps G h := by
  have hcub : ∀ v ∈ c.supp, G.degree v = 3 := by
    intro v hv
    by_contra hne
    apply hc
    rw [mem_image]
    refine ⟨v, ?_, (SimpleGraph.ConnectedComponent.mem_supp_iff c v).1 hv⟩
    simp only [mem_filter, mem_univ, true_and]; have := hmin v; omega
  obtain ⟨h0, hh0⟩ := hH
  have h0S : h0 ∉ c.supp := by
    intro hm; have := hcub h0 hm; simp only [mem_filter, mem_univ, true_and] at hh0; omega
  obtain ⟨r, hr⟩ := c.exists_rep
  have hrS : r ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff c r).2 hr
  set S := univ.filter (fun w => w ∉ c.supp) with hSdef
  obtain ⟨w, hwS, hwl⟩ := hdeg S ⟨h0, mem_filter.2 ⟨mem_univ _, h0S⟩⟩ (fun he => by
    have : r ∈ S := he ▸ mem_univ r
    exact (mem_filter.1 this).2 hrS)
  have hwc : w ∉ c.supp := (mem_filter.1 hwS).2
  have hsplit := split_card (G.neighborFinset w) S
  have hdiff : G.neighborFinset w \ S = G.neighborFinset w ∩ univ.filter (· ∈ c.supp) := by
    ext x; simp [S]
  rw [hdiff, G.card_neighborFinset_eq_degree] at hsplit
  have hw4 : 4 ≤ G.degree w := by
    by_contra hlt
    have hw3 : G.degree w = 3 := by have := hmin w; omega
    have hempty : G.neighborFinset w ∩ univ.filter (· ∈ c.supp) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      simp only [mem_inter, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset] at hx
      have hadj : (cubicGraph G).Adj x w := ⟨hx.1.symm, hcub x hx.2, hw3⟩
      exact hwc (c.mem_supp_of_adj_mem_supp hx.2 hadj)
    rw [hempty, card_empty] at hsplit
    omega
  refine ⟨w, by simp [hw4], ?_⟩
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hc, by omega⟩

/-- **(Step 2)** `2|B| + σ ≤ n`: at most `(n − σ)/2` hubs of degree `≥ 5`. -/
theorem big_hub_bound (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G) :
    2 * (Bset G).card + sigma G ≤ Fintype.card V := by
  have hsum := hub_sum hmin
  have hLH := card_L_add_H hmin
  by_cases hH : (Hset G).Nonempty
  · have hforest := card_le_degsum_comp (cubicGraph G)
    have hcov : (univ : Finset (cubicGraph G).ConnectedComponent) ⊆
        hubComps G ∪ (Hset G).biUnion (domComps G) := by
      intro c _
      by_cases hc : c ∈ hubComps G
      · exact mem_union_left _ hc
      · obtain ⟨h, hh, hch⟩ := dominate hmin hdeg hH c hc
        exact mem_union_right _ (mem_biUnion.2 ⟨h, hh, hch⟩)
    have hcc : Fintype.card (cubicGraph G).ConnectedComponent ≤
        (Hset G).card + ∑ h ∈ Hset G, (domComps G h).card := by
      rw [← card_univ]
      calc _ ≤ (hubComps G ∪ (Hset G).biUnion (domComps G)).card := card_le_card hcov
        _ ≤ (hubComps G).card + ((Hset G).biUnion (domComps G)).card := card_union_le _ _
        _ ≤ _ := add_le_add card_image_le card_biUnion_le
    have hdom : ∑ h ∈ Hset G, ((domComps G h).card + (if 5 ≤ G.degree h then 1 else 0))
        ≤ ∑ h ∈ Hset G, 2 :=
      sum_le_sum (fun h hh => domComps_card (by simpa using hh))
    rw [sum_add_distrib, sum_const, smul_eq_mul] at hdom
    have hB : ∑ h ∈ Hset G, (if 5 ≤ G.degree h then 1 else 0) = (Bset G).card := by
      rw [← card_filter]; congr 1; ext v; simp only [mem_filter, mem_univ, true_and]; omega
    rw [hB] at hdom
    have hcd := cubic_degsum hmin hind
    omega
  · have hHe : Hset G = ∅ := not_nonempty_iff_eq_empty.1 hH
    rw [hHe, sum_empty, card_empty] at hsum
    have hB : Bset G = ∅ := by
      rw [eq_empty_iff_forall_notMem]; intro v hv
      have : v ∈ Hset G := by simp only [mem_filter, mem_univ, true_and] at hv ⊢; omega
      rw [hHe] at this; simp at this
    rw [hB, card_empty]
    omega

/-! ## 5. Step 3: V-shapes between two big hubs; no `C₈` caps them at 12 per pair -/

variable (G) in
/-- Middles `x ∉ B` of a V-shape `a – x – y` with `a ∈ N(b)`, `y ∈ N(b')`, `a ≠ y`. -/
noncomputable abbrev Vmid (b b' : V) : Finset V :=
  univ.filter (fun x => x ∉ Bset G ∧
    ∃ a y, G.Adj b a ∧ G.Adj b' y ∧ a ≠ y ∧ G.Adj x a ∧ G.Adj x y)

theorem Vmid_card_le (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC8 : NoCycleLen G 8) {b b' : V} (hb : b ∈ Bset G) (hb' : b' ∈ Bset G) (hbb : b ≠ b') :
    (Vmid G b b').card ≤ 12 := by
  have db : 5 ≤ G.degree b := by simpa using hb
  have db' : 5 ≤ G.degree b' := by simpa using hb'
  by_cases hne : (Vmid G b b').Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  obtain ⟨x0, hx0⟩ := hne
  simp only [mem_filter, mem_univ, true_and] at hx0
  obtain ⟨hx0B, a0, y0, hba0, hby0, ha0y0, hxa0, hxy0⟩ := hx0
  have dA0 : G.degree a0 = 3 := deg_three_of_hub_adj hmin hind (by omega) hba0
  have dY0 : G.degree y0 = 3 := deg_three_of_hub_adj hmin hind (by omega) hby0
  set N' := (G.neighborFinset x0).filter (fun _ => G.degree x0 = 3) with hN'
  set R := ({a0, x0, y0} : Finset V) ∪ G.neighborFinset a0 ∪ G.neighborFinset y0 ∪ N' with hRdef
  have hR : R.card ≤ 12 := by
    rw [hRdef]
    have c1 : ({a0, x0, y0} : Finset V).card ≤ 3 :=
      (card_insert_le _ _).trans (by
        have := card_insert_le x0 ({y0} : Finset V); simp at this ⊢; omega)
    have c2 : (G.neighborFinset a0).card = 3 := by rw [G.card_neighborFinset_eq_degree, dA0]
    have c3 : (G.neighborFinset y0).card = 3 := by rw [G.card_neighborFinset_eq_degree, dY0]
    have c4 : N'.card ≤ 3 := by
      by_cases h3 : G.degree x0 = 3
      · exact (card_filter_le _ _).trans (by rw [G.card_neighborFinset_eq_degree, h3])
      · rw [hN', filter_false_of_mem (fun _ _ => h3)]; simp
    have u1 := card_union_le (({a0, x0, y0} : Finset V) ∪ G.neighborFinset a0 ∪
      G.neighborFinset y0) N'
    have u2 := card_union_le (({a0, x0, y0} : Finset V) ∪ G.neighborFinset a0)
      (G.neighborFinset y0)
    have u3 := card_union_le ({a0, x0, y0} : Finset V) (G.neighborFinset a0)
    omega
  have hsub : Vmid G b b' ⊆ R := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hxB, a, y, hba, hby, hay, hxa, hxy⟩ := hx
    by_contra hxR
    have dA : G.degree a = 3 := deg_three_of_hub_adj hmin hind (by omega) hba
    have dY : G.degree y = 3 := deg_three_of_hub_adj hmin hind (by omega) hby
    have dx : ¬ 5 ≤ G.degree x := by simpa using hxB
    have dx0 : ¬ 5 ≤ G.degree x0 := by simpa using hx0B
    simp only [hRdef, hN', mem_union, mem_insert, mem_singleton, SimpleGraph.mem_neighborFinset,
      mem_filter, not_or, not_and] at hxR
    obtain ⟨⟨⟨⟨nxa0, nxx0, nxy0⟩, na0x⟩, ny0x⟩, nx0x⟩ := hxR
    -- the 28 disequalities of the 8-cycle `b a0 x0 y0 b' y x a`
    have e01 : b ≠ a0 := G.ne_of_adj hba0
    have e02 : b ≠ x0 := fun h => by rw [← h] at dx0; omega
    have e03 : b ≠ y0 := fun h => by rw [← h] at dY0; omega
    have e04 : b ≠ b' := hbb
    have e05 : b ≠ y := fun h => by rw [← h] at dY; omega
    have e06 : b ≠ x := fun h => by rw [← h] at dx; omega
    have e07 : b ≠ a := G.ne_of_adj hba
    have e12 : a0 ≠ x0 := (G.ne_of_adj hxa0).symm
    have e13 : a0 ≠ y0 := ha0y0
    have e14 : a0 ≠ b' := fun h => by rw [h] at dA0; omega
    have e15 : a0 ≠ y := fun h => na0x (h ▸ hxy.symm)
    have e16 : a0 ≠ x := fun h => nxa0 h.symm
    have e17 : a0 ≠ a := fun h => na0x (h ▸ hxa.symm)
    have e23 : x0 ≠ y0 := G.ne_of_adj hxy0
    have e24 : x0 ≠ b' := fun h => by rw [h] at dx0; omega
    have e25 : x0 ≠ y := fun h => nx0x (h ▸ hxy.symm) (h ▸ dY)
    have e26 : x0 ≠ x := fun h => nxx0 h.symm
    have e27 : x0 ≠ a := fun h => nx0x (h ▸ hxa.symm) (h ▸ dA)
    have e34 : y0 ≠ b' := (G.ne_of_adj hby0).symm
    have e35 : y0 ≠ y := fun h => ny0x (h ▸ hxy.symm)
    have e36 : y0 ≠ x := fun h => nxy0 h.symm
    have e37 : y0 ≠ a := fun h => ny0x (h ▸ hxa.symm)
    have e45 : b' ≠ y := G.ne_of_adj hby
    have e46 : b' ≠ x := fun h => by rw [← h] at dx; omega
    have e47 : b' ≠ a := fun h => by rw [← h] at dA; omega
    have e56 : y ≠ x := (G.ne_of_adj hxy).symm
    have e57 : y ≠ a := fun h => hay h.symm
    have e67 : x ≠ a := G.ne_of_adj hxa
    apply hC8 ![b, a0, x0, y0, b', y, x, a]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      all_goals first
        | exact absurd hij (by assumption)
        | exact absurd hij.symm (by assumption)
    · intro i
      fin_cases i
      · exact hba0
      · exact hxa0.symm
      · exact hxy0
      · exact hby0.symm
      · exact hby
      · exact hxy.symm
      · exact hxa
      · exact hba.symm
  exact (card_le_card hsub).trans hR

/-! ## 6. Step 4: counting V-shapes against the surplus -/

variable (G) in
noncomputable abbrev Uset : Finset V := (Bset G).biUnion (fun b => G.neighborFinset b)

variable (G) in
noncomputable abbrev X2 : Finset V :=
  (Bset G)ᶜ.filter (fun x => 2 ≤ (G.neighborFinset x ∩ Uset G).card)

theorem X2_sub (hC4 : C4Free G) :
    X2 G ⊆ (Bset G).offDiag.biUnion (fun p => Vmid G p.1 p.2) := by
  intro x hx
  rw [mem_filter, mem_compl] at hx
  obtain ⟨hxB, h2⟩ := hx
  obtain ⟨a, ha, y, hy, hay⟩ := one_lt_card.1 (by omega : 1 < (G.neighborFinset x ∩ Uset G).card)
  simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_biUnion] at ha hy
  obtain ⟨hxa, b, hb, hba⟩ := ha
  obtain ⟨hxy, b', hb', hby⟩ := hy
  have hbb : b ≠ b' := by
    rintro rfl
    have := hC4 a y x b hay hxa.symm hxy.symm hba.symm hby.symm
    exact hxB (this ▸ hb)
  rw [mem_biUnion]
  refine ⟨(b, b'), mem_offDiag.2 ⟨hb, hb', hbb⟩, ?_⟩
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨by simpa using hxB, a, y, hba, hby, hay, hxa, hxy⟩

theorem X2_card (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) :
    (X2 G).card ≤ 12 * ((Bset G).card * (Bset G).card - (Bset G).card) := by
  calc (X2 G).card ≤ ((Bset G).offDiag.biUnion (fun p => Vmid G p.1 p.2)).card :=
        card_le_card (X2_sub hC4)
    _ ≤ ∑ p ∈ (Bset G).offDiag, (Vmid G p.1 p.2).card := card_biUnion_le
    _ ≤ ∑ p ∈ (Bset G).offDiag, 12 := sum_le_sum (fun p hp => by
        obtain ⟨h1, h2, h3⟩ := mem_offDiag.1 hp
        exact Vmid_card_le hmin hind hC8 h1 h2 h3)
    _ = _ := by rw [sum_const, smul_eq_mul, offDiag_card, mul_comm]

/-- `Σ_{x∉B} |N(x) ∩ U| + Σ_B deg = 3|U|`. -/
theorem t_sum (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) :
    ∑ x ∈ (Bset G)ᶜ, (G.neighborFinset x ∩ Uset G).card + ∑ b ∈ Bset G, G.degree b
      = 3 * (Uset G).card := by
  have hU3 : ∀ u ∈ Uset G, G.degree u = 3 := by
    intro u hu
    simp only [mem_biUnion, SimpleGraph.mem_neighborFinset] at hu
    obtain ⟨b, hb, hbu⟩ := hu
    exact deg_three_of_hub_adj hmin hind (by simp at hb; omega) hbu
  have e1 : ∑ b ∈ Bset G, G.degree b = ∑ b ∈ Bset G, (G.neighborFinset b ∩ Uset G).card := by
    apply sum_congr rfl
    intro b hb
    rw [inter_eq_left.2 (subset_biUnion_of_mem (fun b => G.neighborFinset b) hb),
      G.card_neighborFinset_eq_degree]
  rw [e1, double_count G _ (Uset G), double_count G (Bset G) (Uset G), ← sum_add_distrib,
    card_eq_sum_ones (Uset G), mul_sum]
  apply sum_congr rfl
  intro u hu
  have hs := split_card (G.neighborFinset u) (Bset G)
  rw [sdiff_eq_inter_compl, G.card_neighborFinset_eq_degree, hU3 u hu] at hs
  omega

/-- `Σ_{x∉B} |N(x) ∩ U| ≤ (n − |B|) + 3|X₂|`. -/
theorem t_upper :
    ∑ x ∈ (Bset G)ᶜ, (G.neighborFinset x ∩ Uset G).card
      ≤ (Bset G)ᶜ.card + 3 * (X2 G).card := by
  have hX : (X2 G).card = ∑ x ∈ (Bset G)ᶜ,
      (if 2 ≤ (G.neighborFinset x ∩ Uset G).card then 1 else 0) := card_filter _ _
  rw [hX, card_eq_sum_ones, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro x hx
  have hxB : ¬ 5 ≤ G.degree x := by simpa using hx
  have hle : (G.neighborFinset x ∩ Uset G).card ≤ G.degree x :=
    (card_le_card inter_subset_left).trans (G.card_neighborFinset_eq_degree x).le
  split_ifs with h <;> omega

/-- **Bonferroni with codegree `≤ 1`**: `2Σ_A deg + |A| ≤ 2|⋃_A N| + |A|²`. -/
theorem bonferroni (hC4 : C4Free G) (A : Finset V) :
    2 * ∑ b ∈ A, G.degree b + A.card
      ≤ 2 * (A.biUnion (fun b => G.neighborFinset b)).card + A.card * A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert b A hbA ih =>
    rw [sum_insert hbA, card_insert_of_notMem hbA, biUnion_insert]
    have hU := card_union_add_card_inter (G.neighborFinset b)
      (A.biUnion (fun b => G.neighborFinset b))
    have hI : (G.neighborFinset b ∩ A.biUnion (fun b => G.neighborFinset b)).card ≤ A.card := by
      rw [inter_biUnion]
      calc _ ≤ ∑ b' ∈ A, (G.neighborFinset b ∩ G.neighborFinset b').card := card_biUnion_le
        _ ≤ ∑ b' ∈ A, 1 := sum_le_sum (fun b' hb' => by
            apply card_le_one.2
            intro c hc c' hc'
            simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hc hc'
            exact hC4 b b' c c' (fun h => hbA (h ▸ hb')) hc.1 hc.2 hc'.1 hc'.2)
        _ = A.card := by rw [sum_const, smul_eq_mul, mul_one]
    rw [G.card_neighborFinset_eq_degree] at hU
    nlinarith [hU, hI, ih]

/-- **The high-surplus bound** (joint: scale ⊕ noProperBaseline ⊕ slackIndependent ⊕
no `C₄` ⊕ no `C₈`): with `k = |B|`, `24σ + 465k ≤ 18n + 375k²`. -/
theorem high_surplus_bound (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) (hdeg : ProperTwoLow G) :
    24 * sigma G + 465 * (Bset G).card
      ≤ 18 * Fintype.card V + 375 * ((Bset G).card * (Bset G).card) := by
  have i1 := hub_sum hmin
  have i2 := hub_sum_split (G := G)
  have i3 := five_hub_bound hmin hind hdeg
  have i4 : 2 * ∑ b ∈ Bset G, G.degree b + (Bset G).card
      ≤ 2 * (Uset G).card + (Bset G).card * (Bset G).card := bonferroni hC4 (Bset G)
  have i5 := t_sum hmin hind
  have i6 := t_upper (G := G)
  have i7 := X2_card hmin hind hC4 hC8
  have hc : (Bset G)ᶜ.card + (Bset G).card = Fintype.card V := by
    rw [card_compl]; have := card_le_univ (Bset G); omega
  have hkk : (Bset G).card ≤ (Bset G).card * (Bset G).card := Nat.le_mul_self _
  generalize (Bset G).card * (Bset G).card = kk at *
  omega

/-- **Closure**, in `s = n − σ`: `8n ≤ 32s + 125s²`.  Any `(n, σ)` with
`8n > 32(n−σ) + 125(n−σ)²` is contradictory. -/
theorem high_surplus_closure (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) (hdeg : ProperTwoLow G)
    (s : ℕ) (hs : sigma G + s = Fintype.card V) :
    8 * Fintype.card V ≤ 32 * s + 125 * (s * s) := by
  have h1 := high_surplus_bound hmin hind hC4 hC8 hdeg
  have h2 := big_hub_bound hmin hind hdeg
  set k := (Bset G).card
  have hk : 2 * k ≤ s := by omega
  have hk2 : 4 * (k * k) ≤ s * s := by nlinarith
  omega

/-! ## 7. Scale regime: the exact `e(L)`/`|H|` trade-off and the parity of forced paths -/

/-- **Trade-off** `2e(L) + 6|H| + σ = 3n` (`2e(L) = Σ deg_Γ`). -/
theorem LL_identity (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) :
    ∑ v, (cubicGraph G).degree v + 6 * (Hset G).card + sigma G = 3 * Fintype.card V := by
  have h1 := cubic_degsum hmin hind
  have h2 := hub_sum hmin
  have h3 := card_L_add_H hmin
  omega

/-- At `σ = n − 8`: `Σ_H deg = 6|H| + e(L) − 12`, i.e. `2Σ_H deg + 24 = 12|H| + Σ deg_Γ`. -/
theorem hub_mean_at_top (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (htop : sigma G + 8 = Fintype.card V) :
    2 * ∑ h ∈ Hset G, G.degree h + 24 = 12 * (Hset G).card + ∑ v, (cubicGraph G).degree v := by
  have h1 := LL_identity hmin hind
  have h2 := hub_sum hmin
  omega

/-- **Parity of `L–L` edges on a walk** (`H` independent): `#LL + [u∈H] + [v∈H] + |p|` is
even.  So an odd walk between two cubic vertices uses an odd number of `L–L` edges. -/
theorem ll_parity (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    {u v : V} (p : G.Walk u v) :
    (p.darts.countP (fun d => decide (G.degree d.fst < 4 ∧ G.degree d.snd < 4))
      + (if 4 ≤ G.degree u then 1 else 0) + (if 4 ≤ G.degree v then 1 else 0) + p.length) % 2
      = 0 := by
  induction p with
  | nil => simp only [SimpleGraph.Walk.darts_nil, List.countP_nil,
      SimpleGraph.Walk.length_nil]; split_ifs <;> omega
  | @cons a w b h q ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.countP_cons, SimpleGraph.Walk.length_cons]
    have hab := hind a w
    simp only [decide_eq_true_eq] at ih ⊢
    split_ifs at ih ⊢ <;> first | omega | exact absurd h (hab (by omega) (by omega))

theorem forced_path_uses_LL (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    {u v : V} (hu : G.degree u = 3) (hv : G.degree v = 3) (p : G.Walk u v)
    (hodd : p.length % 2 = 1) :
    (p.darts.countP (fun d => decide (G.degree d.fst < 4 ∧ G.degree d.snd < 4))) % 2 = 1 := by
  have := ll_parity hind p
  simp only [show ¬ 4 ≤ G.degree u by omega, show ¬ 4 ≤ G.degree v by omega, if_false] at this
  omega

/-! ## 8. The closure against a scale window (`r` any upper bound on `C + 1`) -/

/-- At the least admissible order `n = C(C+1)+9` (`C ≥ 8`) the window
`C⌈√n⌉ < σ ≤ n − 8` is the single value `σ = n − 8`. -/
theorem minimal_order_slice (C n r σ : ℕ) (hn : n = C * (C + 1) + 9)
    (hrC : C + 1 ≤ r) (habove : C * r < σ) (henv : σ + 8 ≤ n) :
    σ + 8 = n := by
  have : C * (C + 1) ≤ C * r := Nat.mul_le_mul_left C hrC
  omega

/-- **Band closure**: if the whole window `C r < σ ≤ n − 8` satisfies
`8n > 32 s + 125 s²` at its widest point `s_max = n − C r − 1`, every `σ` in it is refuted. -/
theorem band_closed (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) (hdeg : ProperTwoLow G)
    (C r smax : ℕ) (habove : C * r < sigma G) (hsmax : C * r + 1 + smax = Fintype.card V)
    (hwide : 32 * smax + 125 * (smax * smax) < 8 * Fintype.card V) : False := by
  have hσn : sigma G ≤ Fintype.card V := by
    have := big_hub_bound hmin hind hdeg; omega
  obtain ⟨s, hs⟩ : ∃ s, sigma G + s = Fintype.card V := ⟨_, Nat.add_sub_of_le hσn⟩
  have h := high_surplus_closure hmin hind hC4 hC8 hdeg s hs
  have hss : s ≤ smax := by omega
  have := Nat.mul_le_mul hss hss
  omega

/-- **The least admissible order is closed**: at `n = C(C+1)+9` with `C ≥ 32`, the
window `C(C+1) < σ ≤ n − 8` is empty of graphs. -/
theorem minimal_order_closed (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) (hdeg : ProperTwoLow G)
    (C r : ℕ) (hC : 32 ≤ C) (hn : Fintype.card V = C * (C + 1) + 9) (hrC : C + 1 ≤ r)
    (habove : C * r < sigma G) (henv : sigma G + 8 ≤ Fintype.card V) : False := by
  have h8 := minimal_order_slice C _ r _ hn hrC habove henv
  have h := high_surplus_closure hmin hind hC4 hC8 hdeg 8 h8
  have : 32 * 32 ≤ C * C := Nat.mul_le_mul hC hC
  nlinarith

/-- **First band, generic form**: in the band `⌈√n⌉ = C + 1`, if
`125 t² + 24 t < 8(C² + C + 1)` then every order `n ≤ C² + C + 1 + t` is closed. -/
theorem first_band_closed (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) (hdeg : ProperTwoLow G)
    (C t : ℕ) (ht : 125 * (t * t) + 24 * t < 8 * (C * C + C + 1))
    (habove : C * (C + 1) < sigma G) (hn : Fintype.card V ≤ C * C + C + 1 + t)
    (henv : sigma G + 8 ≤ Fintype.card V) : False := by
  obtain ⟨sm, hsm⟩ : ∃ sm, C * (C + 1) + 1 + sm = Fintype.card V :=
    ⟨Fintype.card V - (C * (C + 1) + 1), by
      have : C * (C + 1) + 1 ≤ Fintype.card V := by omega
      omega⟩
  have hsmt : sm ≤ t := by nlinarith
  have := Nat.mul_le_mul hsmt hsmt
  exact band_closed hmin hind hC4 hC8 hdeg C (C + 1) sm habove hsm (by nlinarith)


/-! ## 9. The facts as propositions -/

variable (G) in
/-- **Cubic neighbours**: every cubic vertex has a cubic neighbour and at most two hub
neighbours, and `|L| ≤ Σ_{v∈L} |N(v) ∩ L| = 2e(L)`. -/
abbrev CubicSupply : Prop :=
  (∀ v, G.degree v = 3 → ∃ u, G.Adj v u ∧ G.degree u = 3) ∧
    (∀ v, G.degree v = 3 → (G.neighborFinset v ∩ Hset G).card ≤ 2) ∧
    (Lset G).card ≤ ∑ v ∈ Lset G, (G.neighborFinset v ∩ Lset G).card

theorem cubicSupply (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G) : CubicSupply G :=
  ⟨fun _ hv => cubic_has_cubic_nbr hmin hdeg hv,
    fun _ hv => cubic_hub_nbrs_le_two hmin hdeg hv, LL_supply hmin hdeg⟩

variable (G) in
/-- **Parity of `L–L` edges on walks**: `#LL + [u∈H] + [v∈H] + |p|` is even on every walk,
so an odd walk between two cubic vertices uses an odd number of `L–L` edges. -/
abbrev LowEdgeParity : Prop :=
  (∀ u v (p : G.Walk u v),
    (p.darts.countP (fun d => decide (G.degree d.fst < 4 ∧ G.degree d.snd < 4))
      + (if 4 ≤ G.degree u then 1 else 0) + (if 4 ≤ G.degree v then 1 else 0) + p.length) % 2
      = 0) ∧
  (∀ u v, G.degree u = 3 → G.degree v = 3 → ∀ p : G.Walk u v, p.length % 2 = 1 →
    (p.darts.countP (fun d => decide (G.degree d.fst < 4 ∧ G.degree d.snd < 4))) % 2 = 1)

theorem lowEdgeParity (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) :
    LowEdgeParity G :=
  ⟨fun _ _ p => ll_parity hind p, fun _ _ hu hv p hodd => forced_path_uses_LL hind hu hv p hodd⟩

variable (G) in
/-- **Hub domination of the cubic components**: a hub dominates at most two components of
`G[L]` without a hub, at most one if its degree is `≥ 5`; every such component is dominated
by some hub (when there is a hub). -/
abbrev HubDomination : Prop :=
  (∀ h, 4 ≤ G.degree h → (domComps G h).card + (if 5 ≤ G.degree h then 1 else 0) ≤ 2) ∧
    ((Hset G).Nonempty → ∀ c, c ∉ hubComps G → ∃ h ∈ Hset G, c ∈ domComps G h)

theorem hubDomination (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G) :
    HubDomination G :=
  ⟨fun _ hh => domComps_card hh, fun hH c hc => dominate hmin hdeg hH c hc⟩

variable (G) in
/-- **V-shape caps**: two distinct vertices of `B` are joined through at most `12` V-shape
middles, so `|X₂| ≤ 12(|B|² − |B|)`. -/
abbrev VShapeCaps : Prop :=
  (∀ b ∈ Bset G, ∀ b' ∈ Bset G, b ≠ b' → (Vmid G b b').card ≤ 12) ∧
    (X2 G).card ≤ 12 * ((Bset G).card * (Bset G).card - (Bset G).card)

theorem vShapeCaps (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) : VShapeCaps G :=
  ⟨fun _ hb _ hb' hbb => Vmid_card_le hmin hind hC8 hb hb' hbb, X2_card hmin hind hC4 hC8⟩

/-! ## 10. The first band, from the closure alone -/

/-- **First band, arithmetic form**: if every split `σ + s = n` has
`8n ≤ 32s + 125s²`, `C(C+1) < σ ≤ n` and `125t² + 24t < 8(C² + C + 1)`, then
`n > C² + C + 1 + t`. -/
theorem first_band_of_closure (n σ C t : ℕ)
    (closure : ∀ s, σ + s = n → 8 * n ≤ 32 * s + 125 * (s * s))
    (habove : C * (C + 1) < σ) (hσ : σ ≤ n)
    (ht : 125 * (t * t) + 24 * t < 8 * (C * C + C + 1)) :
    C * C + C + 1 + t < n := by
  by_contra hn
  push Not at hn
  obtain ⟨s, hs⟩ : ∃ s, σ + s = n := ⟨n - σ, by omega⟩
  have h := closure s hs
  have hst : s ≤ t := by nlinarith
  have := Nat.mul_le_mul hst hst
  nlinarith

/-- **The closure in `n` alone**: if every split `σ + s = n` has `8n ≤ 32s + 125s²` and
`b < σ ≤ n`, then `8n ≤ 32(n − b − 1) + 125(n − b − 1)²`. -/
theorem closure_at_window (n σ b : ℕ)
    (closure : ∀ s, σ + s = n → 8 * n ≤ 32 * s + 125 * (s * s))
    (habove : b < σ) (hσ : σ ≤ n) :
    8 * n ≤ 32 * (n - b - 1) + 125 * ((n - b - 1) * (n - b - 1)) := by
  obtain ⟨s, hs⟩ : ∃ s, σ + s = n := ⟨n - σ, by omega⟩
  have h := closure s hs
  have hs' : s ≤ n - b - 1 := by omega
  have := Nat.mul_le_mul hs' hs'
  omega

end Hypostructure.Graph.JointSystem
