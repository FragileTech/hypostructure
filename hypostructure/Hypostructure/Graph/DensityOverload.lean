import Mathlib

/-!
# Density vs forced path families at a hub

Vocabulary-free, Mathlib-only.

`int S := ∑_{u ∈ S} #(N u ∩ S)` is twice the number of edges spanned by `S`;
`bd S := ∑_{u ∈ S} #(N u \ S)` is the number of edges leaving `S`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Hypostructure.Graph.DensityOverload

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. Degeneracy ⇒ edge bound (with the constant), and the failed converse -/

/-- Adding a vertex `v ∉ S` raises the internal degree sum by `2 · #(N v ∩ S)`. -/
theorem sum_insert_internal (S : Finset V) (v : V) (hv : v ∉ S) :
    ∑ u ∈ insert v S, (G.neighborFinset u ∩ insert v S).card
      = ∑ u ∈ S, (G.neighborFinset u ∩ S).card + 2 * (G.neighborFinset v ∩ S).card := by
  rw [sum_insert hv]
  have hvv : v ∉ G.neighborFinset v := by simp
  rw [inter_insert_of_notMem hvv]
  have hterm : ∀ u ∈ S, (G.neighborFinset u ∩ insert v S).card
      = (G.neighborFinset u ∩ S).card + (if G.Adj u v then 1 else 0) := by
    intro u _
    by_cases hA : G.Adj u v
    · have hm : v ∈ G.neighborFinset u := by simpa using hA
      rw [inter_insert_of_mem hm, card_insert_of_notMem (by simp [hv]), if_pos hA]
    · have hm : v ∉ G.neighborFinset u := by simpa using hA
      rw [inter_insert_of_notMem hm, if_neg hA, add_zero]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_boole]
  have hf : ({u ∈ S | G.Adj u v} : Finset V) = G.neighborFinset v ∩ S := by
    ext u; simp [G.adj_comm, and_comm]
  rw [hf]; push_cast; ring

/-- Internal degree is at most `#S - 1`. -/
theorem internal_le (S : Finset V) (u : V) (hu : u ∈ S) :
    (G.neighborFinset u ∩ S).card ≤ S.card - 1 := by
  rw [← card_erase_of_mem hu]
  apply card_le_card
  intro w hw
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hw
  exact mem_erase.2 ⟨fun h => by subst h; exact G.irrefl hw.1, hw.2⟩

/-- **Degeneracy ⇒ edge bound.**  If every nonempty proper vertex set has a vertex of
internal degree `≤ 2`, then every proper `S` with `#S ≥ 2` spans at most `2#S - 3`
edges, i.e. `int S + 6 ≤ 4 #S`. -/
theorem degenerate_internal_sum_le
    (hdeg : ∀ S : Finset V, S.Nonempty → S ≠ univ →
      ∃ v ∈ S, (G.neighborFinset v ∩ S).card ≤ 2) :
    ∀ S : Finset V, S ≠ univ → 2 ≤ S.card →
      ∑ u ∈ S, (G.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hS h2
  obtain ⟨v, hvS, hv⟩ := hdeg S (card_pos.1 (by omega)) hS
  have hST : insert v (S.erase v) = S := insert_erase hvS
  have hvT : v ∉ S.erase v := notMem_erase v S
  have hcard : S.card = (S.erase v).card + 1 := by
    rw [← hST, card_insert_of_notMem hvT, hST]
  have hsum := sum_insert_internal G (S.erase v) v hvT
  rw [hST] at hsum
  have hvT' : (G.neighborFinset v ∩ S.erase v).card ≤ 2 :=
    le_trans (card_le_card (inter_subset_inter_left (erase_subset v S))) hv
  by_cases hT : 2 ≤ (S.erase v).card
  · have hTne : S.erase v ≠ univ := by
      intro h; apply hS; exact eq_univ_of_forall fun x => erase_subset v S (h ▸ mem_univ x)
    have := ih (S.erase v) (erase_ssubset hvS) hTne hT
    omega
  · have h1 : (S.erase v).card = 1 := by omega
    have h0 : ∑ u ∈ S.erase v, (G.neighborFinset u ∩ S.erase v).card = 0 := by
      apply sum_eq_zero; intro u hu
      have := internal_le G (S.erase v) u hu; omega
    have hle : (G.neighborFinset v ∩ S.erase v).card ≤ 1 :=
      le_trans (card_le_card inter_subset_right) h1.le
    omega

/-- The claimed converse is **false**: the edge bound is blind to cubic blocks.
Any `S` with `#S ≥ 6` all of whose internal degrees are `3` satisfies `int S + 6 ≤ 4#S`,
yet has no vertex of internal degree `≤ 2`. -/
theorem cubic_block_satisfies_sum_bound (S : Finset V)
    (h3 : ∀ v ∈ S, (G.neighborFinset v ∩ S).card = 3) (h6 : 6 ≤ S.card) :
    ∑ u ∈ S, (G.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card := by
  rw [sum_congr rfl h3, sum_const, smul_eq_mul]; omega

/-- The true converse: the edge bound only yields a vertex of internal degree `≤ 3`. -/
theorem sum_bound_gives_deg_le_three (S : Finset V)
    (h : ∑ u ∈ S, (G.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card) :
    ∃ v ∈ S, (G.neighborFinset v ∩ S).card ≤ 3 := by
  by_contra hc
  push Not at hc
  have : ∑ _u ∈ S, 4 ≤ ∑ u ∈ S, (G.neighborFinset u ∩ S).card :=
    sum_le_sum fun u hu => hc u hu
  rw [sum_const, smul_eq_mul] at this
  omega

/-! ## 2. The exact slack formula -/

/-- `∑_S deg = int S + bd S`. -/
theorem degree_split (S : Finset V) :
    ∑ u ∈ S, G.degree u
      = ∑ u ∈ S, (G.neighborFinset u ∩ S).card + ∑ u ∈ S, (G.neighborFinset u \ S).card := by
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro u _
  rw [← G.card_neighborFinset_eq_degree, ← card_sdiff_add_card_inter (G.neighborFinset u) S]
  ring

/-- **Exact slack formula.**  Writing `σ_S = ∑_S (deg - 3)` and `bd S` for the cut,
`slack(S) := 4#S - 6 - int S = #S + bd S - 6 - σ_S`.  Hence the density fact at `S` is
*equivalent* to `σ_S ≤ #S + bd S - 6`: only hub excess can consume density. -/
theorem slack_formula (S : Finset V) :
    (4 * S.card - 6 - ∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℤ)
      = S.card + ∑ u ∈ S, ((G.neighborFinset u \ S).card : ℤ) - 6
        - ∑ u ∈ S, ((G.degree u : ℤ) - 3) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (degree_split G S)
  simp only [Nat.cast_add, Nat.cast_sum] at h
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, h]
  push_cast
  ring

theorem density_iff_excess (S : Finset V) :
    (∑ u ∈ S, (G.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card) ↔
      ∑ u ∈ S, ((G.degree u : ℤ) - 3)
        ≤ S.card + ∑ u ∈ S, ((G.neighborFinset u \ S).card : ℤ) - 6 := by
  have h := slack_formula G S
  constructor
  · intro hle
    have : ((∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℕ) : ℤ) + 6 ≤ 4 * (S.card : ℤ) := by
      exact_mod_cast hle
    push_cast at this h ⊢; linarith
  · intro hle
    have : ((∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℕ) : ℤ) + 6 ≤ 4 * (S.card : ℤ) := by
      push_cast at h ⊢; linarith
    exact_mod_cast this

/-- **Slack step.**  `slack(S ∪ {v}) = slack(S) + 4 - 2 #(N v ∩ S)`: a fresh vertex with
`t` neighbours already in `S` changes the slack by `4 - 2t`.  A fresh ear with `k ≥ 1`
interior vertices raises the slack by `2(k-1)`; only chords (`t = 3` closings / ears with
no interior vertex) consume slack. -/
theorem slack_insert (S : Finset V) (v : V) (hv : v ∉ S) :
    (4 * (insert v S).card - 6 - ∑ u ∈ insert v S, (G.neighborFinset u ∩ insert v S).card : ℤ)
      = (4 * S.card - 6 - ∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℤ)
        + 4 - 2 * (G.neighborFinset v ∩ S).card := by
  rw [card_insert_of_notMem hv]
  have h := congrArg (fun n : ℕ => (n : ℤ)) (sum_insert_internal G S v hv)
  push_cast at h ⊢
  rw [h]; ring

/-- **Single hub: density is never binding.**  If `S ⊇ N[h]` and every other vertex of
`S` has degree `3`, then `slack(S) = (#S - deg h - 1) + (bd S - 2)`.  With the cut
`bd S ≥ 2` (bridgeless, `S` proper) the forced-path union at one hub has slack
`≥ #S - deg h - 1 ≥ 0`. -/
theorem single_hub_slack (S : Finset V) (h : V) (hh : h ∈ S)
    (h3 : ∀ u ∈ S, u ≠ h → G.degree u = 3) :
    (4 * S.card - 6 - ∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℤ)
      = ((S.card : ℤ) - G.degree h - 1)
        + (∑ u ∈ S, ((G.neighborFinset u \ S).card : ℤ) - 2) := by
  rw [slack_formula]
  have : ∑ u ∈ S.erase h, ((G.degree u : ℤ) - 3) = 0 := by
    apply sum_eq_zero; intro u hu
    rw [h3 u (mem_of_mem_erase hu) (ne_of_mem_erase hu)]; norm_num
  rw [← add_sum_erase S (fun u => ((G.degree u : ℤ) - 3)) hh, this]; ring

theorem single_hub_density_automatic (S : Finset V) (h : V) (hh : h ∈ S)
    (hN : G.neighborFinset h ⊆ S)
    (h3 : ∀ u ∈ S, u ≠ h → G.degree u = 3)
    (hcut : 2 ≤ ∑ u ∈ S, (G.neighborFinset u \ S).card) :
    G.degree h + 1 ≤ S.card ∧
    ((∑ u ∈ S, (G.neighborFinset u ∩ S).card : ℕ) : ℤ)
      + ((S.card : ℤ) - (G.degree h + 1)) + 6 ≤ 4 * (S.card : ℤ) := by
  have hs := single_hub_slack G S h hh h3
  have hsub : insert h (G.neighborFinset h) ⊆ S := insert_subset hh hN
  have hc := card_le_card hsub
  rw [card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree] at hc
  refine ⟨hc, ?_⟩
  have hcut' : (2 : ℤ) ≤ ∑ u ∈ S, ((G.neighborFinset u \ S).card : ℤ) := by exact_mod_cast hcut
  have hc' : (G.degree h : ℤ) + 1 ≤ S.card := by exact_mod_cast hc
  push_cast at hs ⊢
  nlinarith

/-! ## 3. C4-freeness at a hub: matching, private second neighbourhoods, length-3 pairs -/

/-- C4-freeness in "two vertices have at most one common neighbour" form. -/
def C4Free : Prop :=
  ∀ a b c c' : V, a ≠ b → G.Adj a c → G.Adj b c → G.Adj a c' → G.Adj b c' → c = c'

/-- C4-free ⇒ `G[N(h)]` is a matching (the high-centre normal form is implied). -/
theorem nbhd_matching (hC4 : C4Free G) (h x u w : V) (hx : G.Adj h x) (hu : G.Adj h u)
    (hw : G.Adj h w) (hxu : G.Adj x u) (hxw : G.Adj x w) : u = w := by
  by_contra hne
  have := hC4 u w h x hne hu.symm hw.symm hxu.symm hxw.symm
  subst this; exact G.irrefl hx

/-- The private second neighbourhoods of distinct hub neighbours are disjoint. -/
theorem private_second_disjoint (hC4 : C4Free G) (h x y w : V) (hx : G.Adj h x)
    (hy : G.Adj h y) (hxy : x ≠ y) (hxw : G.Adj x w) (hyw : G.Adj y w) : w = h :=
  hC4 x y w h hxy hxw hyw hx.symm hy.symm

/-- Ordered non-adjacent pairs of `N(h)`. -/
def nonadjPairs (h : V) : Finset (V × V) :=
  (G.neighborFinset h ×ˢ G.neighborFinset h).filter fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2

/-- Pairs joined by an `x–u–v–y` path avoiding `h` (these close 5-cycles with `h`). -/
def len3Pairs (h : V) : Finset (V × V) :=
  (nonadjPairs G h).filter fun p =>
    ∃ u v, u ≠ h ∧ v ≠ h ∧ G.Adj p.1 u ∧ G.Adj u v ∧ G.Adj v p.2

/-- Private second neighbourhood `P = N(N(h)) \ N[h]`. -/
def secondNbhd (h : V) : Finset V :=
  univ.filter fun w => w ≠ h ∧ w ∉ G.neighborFinset h ∧ ∃ x ∈ G.neighborFinset h, G.Adj x w

/-- **Length-3 pairs inject into oriented edges inside `P`.** -/
theorem len3Pairs_card_le (hC4 : C4Free G) (h : V) :
    (len3Pairs G h).card ≤
      ((secondNbhd G h ×ˢ secondNbhd G h).filter fun q => G.Adj q.1 q.2).card := by
  have key : ∀ p : V × V, ∃ q : V × V, p ∈ len3Pairs G h →
      q.1 ≠ h ∧ q.2 ≠ h ∧ G.Adj p.1 q.1 ∧ G.Adj q.1 q.2 ∧ G.Adj q.2 p.2 := by
    intro p
    by_cases hp : p ∈ len3Pairs G h
    · simp only [len3Pairs, mem_filter] at hp
      obtain ⟨_, u, v, h1, h2, h3, h4, h5⟩ := hp
      exact ⟨(u, v), fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨(h, h), fun hp' => absurd hp' hp⟩
  choose f hf using key
  apply card_le_card_of_injOn f
  · intro p hp
    have hp' := hp
    simp only [len3Pairs, nonadjPairs, mem_filter, mem_product,
      SimpleGraph.mem_neighborFinset, coe_filter, Set.mem_setOf_eq] at hp'
    obtain ⟨⟨⟨hx, hy⟩, hxy, hnadj⟩, _⟩ := hp'
    obtain ⟨hu, hv, hxu, huv, hvy⟩ := hf p hp
    -- u ∉ N(h)
    have hu' : ¬ G.Adj h (f p).1 := by
      intro hhu
      by_cases hey : (f p).1 = p.2
      · exact hnadj (hey ▸ hxu)
      · exact hv (hC4 _ _ _ _ hey hhu.symm hy.symm huv hvy.symm).symm
    have hv' : ¬ G.Adj h (f p).2 := by
      intro hhv
      by_cases hex : p.1 = (f p).2
      · exact hnadj (hex ▸ hvy)
      · exact hu (hC4 _ _ _ _ hex hx.symm hhv.symm hxu huv.symm).symm
    simp only [coe_filter, mem_product, secondNbhd, mem_filter, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset, Set.mem_setOf_eq]
    exact ⟨⟨⟨hu, hu', p.1, hx, hxu⟩, ⟨hv, hv', p.2, hy, hvy.symm⟩⟩, huv⟩
  · intro p hp p' hp' heq
    have hp1 := hp; have hp1' := hp'
    simp only [coe_filter, len3Pairs, nonadjPairs, mem_filter, mem_product,
      SimpleGraph.mem_neighborFinset, Set.mem_setOf_eq] at hp1 hp1'
    obtain ⟨⟨⟨hx, hy⟩, _⟩, _⟩ := hp1
    obtain ⟨⟨⟨hx', hy'⟩, _⟩, _⟩ := hp1'
    obtain ⟨_, _, hxu, _, hvy⟩ := hf p hp
    obtain ⟨hu, hv, hxu', _, hvy'⟩ := hf p' hp'
    rw [heq] at hxu hvy
    have e1 : p.1 = p'.1 := by
      by_contra hne; exact hu (hC4 _ _ _ _ hne hxu hxu' hx.symm hx'.symm)
    have e2 : p.2 = p'.2 := by
      by_contra hne; exact hv (hC4 _ _ _ _ hne hvy.symm hvy'.symm hy.symm hy'.symm)
    exact Prod.ext e1 e2

/-- `#P ≤ ∑_{x ∈ N(h)} (deg x - 1)`. -/
theorem secondNbhd_card_le (h : V) :
    (secondNbhd G h).card ≤ ∑ x ∈ G.neighborFinset h, (G.degree x - 1) := by
  have hsub : secondNbhd G h ⊆ (G.neighborFinset h).biUnion fun x => (G.neighborFinset x).erase h := by
    intro w hw
    simp only [secondNbhd, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hwh, _, x, hx, hxw⟩ := hw
    exact mem_biUnion.2 ⟨x, hx, mem_erase.2 ⟨hwh, by simpa using hxw⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (le_of_eq (sum_congr rfl ?_)))
  intro x hx
  rw [card_erase_of_mem (by simpa [G.adj_comm] using hx), G.card_neighborFinset_eq_degree]

/-- Oriented edges inside `P`: each `u ∈ P` has its `N(h)`-neighbour outside `P`. -/
theorem secondNbhd_edges_le (h : V) :
    ((secondNbhd G h ×ˢ secondNbhd G h).filter fun q => G.Adj q.1 q.2).card
      ≤ ∑ u ∈ secondNbhd G h, (G.degree u - 1) := by
  rw [card_filter, sum_product]
  apply sum_le_sum; intro u hu
  rw [← card_filter]
  have hu' := hu
  simp only [secondNbhd, mem_filter, mem_univ, true_and] at hu'
  obtain ⟨_, _, x, hx, hxu⟩ := hu'
  have hxP : x ∉ secondNbhd G h := by
    simp only [secondNbhd, mem_filter, mem_univ, true_and, not_and]
    intro _ hxn; exact absurd hx hxn
  have hsub : (secondNbhd G h).filter (G.Adj u) ⊆ (G.neighborFinset u).erase x := by
    intro w hw
    simp only [mem_filter] at hw
    exact mem_erase.2 ⟨fun e => hxP (e ▸ hw.1), by simpa using hw.2⟩
  refine (card_le_card hsub).trans (le_of_eq ?_)
  rw [card_erase_of_mem (by simpa using hxu.symm), G.card_neighborFinset_eq_degree]

/-- **Length-3 budget at a hub.**  If `N(h) ∪ P` is cubic, at most `4d` ordered
(`2d` unordered) non-adjacent pairs of `N(h)` are joined by a length-3 path. -/
theorem len3Pairs_le_four_d (hC4 : C4Free G) (h : V)
    (hA : ∀ x ∈ G.neighborFinset h, G.degree x = 3)
    (hP : ∀ u ∈ secondNbhd G h, G.degree u = 3) :
    (len3Pairs G h).card ≤ 4 * G.degree h := by
  have e1 := len3Pairs_card_le G hC4 h
  have e2 := secondNbhd_edges_le G h
  have e3 := secondNbhd_card_le G h
  rw [sum_congr rfl (fun u hu => by rw [hP u hu]), sum_const, smul_eq_mul] at e2
  rw [sum_congr rfl (fun x hx => by rw [hA x hx]), sum_const, smul_eq_mul,
    G.card_neighborFinset_eq_degree] at e3
  omega

/-- Ordered non-adjacent pairs: at least `d(d-2)` (C4 ⇒ matching). -/
theorem nonadjPairs_card_ge (hC4 : C4Free G) (h : V) :
    G.degree h * (G.degree h - 2) ≤ (nonadjPairs G h).card := by
  set A := G.neighborFinset h with hAdef
  have hrow : ∀ x ∈ A, A.card - 2 ≤ (A.filter fun y => x ≠ y ∧ ¬ G.Adj x y).card := by
    intro x hx
    have hsub : (A.erase x) ⊆ (A.filter fun y => x ≠ y ∧ ¬ G.Adj x y) ∪ (A.filter (G.Adj x)) := by
      intro y hy
      obtain ⟨hyx, hyA⟩ := mem_erase.1 hy
      by_cases hxy : G.Adj x y
      · exact mem_union_right _ (mem_filter.2 ⟨hyA, hxy⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hyA, Ne.symm hyx, hxy⟩)
    have hle1 : (A.filter (G.Adj x)).card ≤ 1 := by
      apply card_le_one.2
      intro u hu w hw
      simp only [mem_filter, hAdef, SimpleGraph.mem_neighborFinset] at hu hw hx
      exact nbhd_matching G hC4 h x u w hx hu.1 hw.1 hu.2 hw.2
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_erase_of_mem hx] at this
    omega
  have hcard : (nonadjPairs G h).card = ∑ x ∈ A, (A.filter fun y => x ≠ y ∧ ¬ G.Adj x y).card := by
    rw [nonadjPairs, ← hAdef, card_filter, sum_product]
    exact sum_congr rfl fun x _ => (card_filter _ _).symm
  rw [hcard]
  have : ∑ _x ∈ A, (A.card - 2) ≤ ∑ x ∈ A, (A.filter fun y => x ≠ y ∧ ¬ G.Adj x y).card :=
    sum_le_sum hrow
  rw [sum_const, smul_eq_mul, hAdef, G.card_neighborFinset_eq_degree] at this
  exact this

/-- **Pairs that need a long Mersenne path.**  At least `d(d-2) - 4d = d(d-6)` ordered
non-adjacent pairs of `N(h)` have *no* length-3 connection; their forced path has length
`≥ 7` (a `≥ 9`-cycle through `h`). -/
theorem long_pairs_card_ge (hC4 : C4Free G) (h : V)
    (hA : ∀ x ∈ G.neighborFinset h, G.degree x = 3)
    (hP : ∀ u ∈ secondNbhd G h, G.degree u = 3) :
    G.degree h * (G.degree h - 2) ≤
      ((nonadjPairs G h).filter fun p =>
          ¬ ∃ u v, u ≠ h ∧ v ≠ h ∧ G.Adj p.1 u ∧ G.Adj u v ∧ G.Adj v p.2).card
        + 4 * G.degree h := by
  have h1 := nonadjPairs_card_ge G hC4 h
  have h2 := len3Pairs_le_four_d G hC4 h hA hP
  have h3 := card_filter_add_card_filter_not (s := nonadjPairs G h)
    (p := fun p => ∃ u v, u ≠ h ∧ v ≠ h ∧ G.Adj p.1 u ∧ G.Adj u v ∧ G.Adj v p.2)
  unfold len3Pairs at h2
  omega

end Hypostructure.Graph.DensityOverload
