import Mathlib

/-!
# Hubs against windows: budgets, slack, lifted cycles, big-hub neighbourhoods

Vocabulary-free, Mathlib-only.

* **Budget.**  `H` the hubs (independent, every vertex off `H` cubic), `L = Hᶜ`,
  `intL = ∑_{v ∈ L} #(N v ∩ L) = 2e(L)`.  A window `P` is a vertex set with
  `∑_{v∈P} #(N v ∩ P) = 24` and every internal degree `1` or `2` (an induced path on 13
  vertices).  The `L–L` darts inside a window (`window_LL_exact`) and their split over a
  packing (`LL_split`).
* **Slack.**  `slack S = 4|S| − 6 − ∑_{u∈S} #(N u ∩ S)`; density (2-degeneracy) gives
  `slack S ≥ 0` for proper `S`, `|S| ≥ 2`; windows hanging on a set consume slack
  (`hanging_bound`).
* **Lift.**  Vertex lists that close cycles (`list_cycle`, `lift_cycle`) and the dyadic
  arithmetic of their lengths.
* **Big-hub neighbourhood.**  On an induced 13-window, `|U ∩ P| ≤ 7 + |(X2 ∪ B) ∩ P|`
  (`window_U`), `U = N(B)`, `X2 = {x ∉ B : ≥ 2 neighbours in U}`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubWin

/-! ## hub budget against windows, edge ends -/

section Budget


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem nbr_inter_eq_filter (v : V) (B : Finset V) :
    G.neighborFinset v ∩ B = B.filter (fun w => G.Adj v w) := by
  ext w; simp [SimpleGraph.mem_neighborFinset, and_comm]

/-- Double counting of `A`–`B` adjacencies. -/
theorem sum_inter_comm (A B : Finset V) :
    ∑ v ∈ A, (G.neighborFinset v ∩ B).card = ∑ w ∈ B, (G.neighborFinset w ∩ A).card := by
  simp_rw [nbr_inter_eq_filter, card_filter]
  rw [sum_comm]
  apply sum_congr rfl; intro w _; apply sum_congr rfl; intro v _
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem card_inter_split (v : V) (A B : Finset V) :
    (G.neighborFinset v ∩ A).card
      = (G.neighborFinset v ∩ (A \ B)).card + (G.neighborFinset v ∩ (A ∩ B)).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext w; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  · rw [disjoint_left]; intro w h1 h2
    simp only [mem_inter, mem_sdiff] at h1 h2; exact h1.2.2 h2.2.2

/-- **`2e(L) + ∑_H deg = 3|L|`**. -/
theorem intL_formula (H : Finset V) (hind : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b)
    (hcub : ∀ v ∉ H, G.degree v = 3) :
    ∑ v ∈ Hᶜ, (G.neighborFinset v ∩ Hᶜ).card + ∑ h ∈ H, G.degree h = 3 * Hᶜ.card := by
  have hsplit : ∀ v : V, (G.neighborFinset v ∩ Hᶜ).card + (G.neighborFinset v ∩ H).card
      = G.degree v := by
    intro v
    rw [← G.card_neighborFinset_eq_degree, ← card_union_of_disjoint]
    · congr 1; ext w; simp only [mem_union, mem_inter, mem_compl]; tauto
    · rw [disjoint_left]; intro w h1 h2
      simp only [mem_inter, mem_compl] at h1 h2; exact h1.2 h2.2
  have hH : ∀ h ∈ H, (G.neighborFinset h ∩ Hᶜ).card = G.degree h := by
    intro h hh
    rw [← G.card_neighborFinset_eq_degree]; congr 1
    ext w; simp only [mem_inter, mem_compl, SimpleGraph.mem_neighborFinset, and_iff_left_iff_imp]
    intro hw hwH; exact hind h hh w hwH hw
  have e1 : ∑ v ∈ Hᶜ, (G.neighborFinset v ∩ H).card = ∑ h ∈ H, G.degree h := by
    rw [sum_inter_comm G Hᶜ H]; exact sum_congr rfl hH
  have e2 : ∑ v ∈ Hᶜ, G.degree v = 3 * Hᶜ.card := by
    rw [sum_congr rfl (fun v hv => hcub v (mem_compl.1 hv)), sum_const, smul_eq_mul, mul_comm]
  rw [← e1, ← sum_add_distrib, ← e2]
  exact sum_congr rfl (fun v _ => hsplit v)

/-- **`2e(L) + 6|H| + σ = 3n`** (`σ = ∑_H (deg − 3)`). -/
theorem intL_sigma (H : Finset V) (hind : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b)
    (hcub : ∀ v ∉ H, G.degree v = 3) (hdeg : ∀ h ∈ H, 3 ≤ G.degree h) :
    ∑ v ∈ Hᶜ, (G.neighborFinset v ∩ Hᶜ).card + 6 * H.card + ∑ h ∈ H, (G.degree h - 3)
      = 3 * Fintype.card V := by
  have h1 := intL_formula G H hind hcub
  have h2 : ∑ h ∈ H, G.degree h = ∑ h ∈ H, (G.degree h - 3) + 3 * H.card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
    exact sum_congr rfl (fun h hh => by have := hdeg h hh; omega)
  have h3 : Hᶜ.card + H.card = Fintype.card V := by
    rw [card_compl]; have := card_le_univ H; omega
  omega

/-! ## One window: the exact `L–L` dart count -/

/-- **Window `L–L` darts (exact).**  For a window `P` (internal degree sum `24`, internal
degrees in `{1,2}`) and independent hubs: with `h_P = |P ∩ H|` and `ε_P` the hubs of `P`
at a window end (internal degree `1`),
`#LL-darts(P) + 4 h_P = 24 + 2 ε_P`, i.e. `e_LL(P) = 12 − 2h_P + ε_P`. -/
theorem window_LL_exact (H P : Finset V) (hind : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b)
    (hsum : ∑ v ∈ P, (G.neighborFinset v ∩ P).card = 24)
    (h12 : ∀ v ∈ P, (G.neighborFinset v ∩ P).card = 1 ∨ (G.neighborFinset v ∩ P).card = 2) :
    ∑ v ∈ P \ H, (G.neighborFinset v ∩ (P \ H)).card + 4 * (P ∩ H).card
      = 24 + 2 * ((P ∩ H).filter (fun v => (G.neighborFinset v ∩ P).card = 1)).card := by
  have hs := sum_sdiff (f := fun v => (G.neighborFinset v ∩ P).card)
    (inter_subset_left : P ∩ H ⊆ P)
  rw [sdiff_inter_self_left, hsum] at hs
  have e1 : ∑ v ∈ P \ H, (G.neighborFinset v ∩ P).card
      = ∑ v ∈ P \ H, (G.neighborFinset v ∩ (P \ H)).card
        + ∑ v ∈ P \ H, (G.neighborFinset v ∩ (P ∩ H)).card := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun v _ => card_inter_split G v P H)
  have e2 : ∑ v ∈ P \ H, (G.neighborFinset v ∩ (P ∩ H)).card
      = ∑ h ∈ P ∩ H, (G.neighborFinset h ∩ P).card := by
    rw [sum_inter_comm G (P \ H) (P ∩ H)]
    apply sum_congr rfl; intro h hh
    congr 1; ext w
    simp only [mem_inter, mem_sdiff, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩; exact ⟨a, b, fun hw => hind h (mem_inter.1 hh).2 w hw a⟩
  have e3 : ∑ h ∈ P ∩ H, (G.neighborFinset h ∩ P).card
      + ((P ∩ H).filter (fun v => (G.neighborFinset v ∩ P).card = 1)).card
      = 2 * (P ∩ H).card := by
    rw [card_filter, ← sum_add_distrib, mul_comm, ← smul_eq_mul, ← sum_const]
    apply sum_congr rfl; intro v hv
    rcases h12 v (mem_inter.1 hv).1 with h | h <;> simp [h]
  omega

/-! ## All windows plus the cubic-neighbour fact -/

/-- **`L–L` split.**  Pairwise disjoint windows `mem P`; every cubic vertex has a cubic
neighbour.  Then `2e(L) ≥ ∑_P #LL-darts(P) + I`, where `I` counts the cubic vertices with
no cubic neighbour inside their own window (every cubic vertex of `R` counts). -/
theorem LL_split {ι : Type*} [DecidableEq ι] (H : Finset V) (Ws : Finset ι)
    (mem : ι → Finset V) (hdisj : ∀ P ∈ Ws, ∀ Q ∈ Ws, P ≠ Q → Disjoint (mem P) (mem Q))
    (hcubnbr : ∀ v ∉ H, ∃ u, G.Adj v u ∧ u ∉ H) :
    ∑ P ∈ Ws, ∑ v ∈ mem P \ H, (G.neighborFinset v ∩ (mem P \ H)).card
        + (Hᶜ.filter (fun v => ∀ P ∈ Ws, v ∈ mem P →
            (G.neighborFinset v ∩ (mem P \ H)).card = 0)).card
      ≤ ∑ v ∈ Hᶜ, (G.neighborFinset v ∩ Hᶜ).card := by
  have hper : ∀ v ∈ Hᶜ,
      ∑ P ∈ Ws.filter (fun P => v ∈ mem P), (G.neighborFinset v ∩ (mem P \ H)).card
        + (if ∀ P ∈ Ws, v ∈ mem P → (G.neighborFinset v ∩ (mem P \ H)).card = 0
            then 1 else 0)
        ≤ (G.neighborFinset v ∩ Hᶜ).card := by
    intro v hv
    have hvH : v ∉ H := mem_compl.1 hv
    obtain ⟨u, hu, huH⟩ := hcubnbr v hvH
    have hone : (Ws.filter (fun P => v ∈ mem P)).card ≤ 1 := by
      rw [card_le_one]; intro P hP Q hQ
      simp only [mem_filter] at hP hQ
      by_contra hne
      exact disjoint_left.1 (hdisj P hP.1 Q hQ.1 hne) hP.2 hQ.2
    have hu' : u ∈ G.neighborFinset v ∩ Hᶜ := by simp [hu, huH]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hone with h0 | h1
    · rw [card_eq_zero] at h0
      rw [h0, sum_empty, zero_add]
      split_ifs
      · exact card_pos.2 ⟨u, hu'⟩
      · exact Nat.zero_le _
    · obtain ⟨P, hP⟩ := card_eq_one.1 h1
      have hPmem : P ∈ Ws.filter (fun P => v ∈ mem P) := by rw [hP]; exact mem_singleton_self _
      simp only [mem_filter] at hPmem
      rw [hP, sum_singleton]
      have hsub : G.neighborFinset v ∩ (mem P \ H) ⊆ G.neighborFinset v ∩ Hᶜ := by
        intro w hw; simp only [mem_inter, mem_sdiff, mem_compl] at hw ⊢; exact ⟨hw.1, hw.2.2⟩
      split_ifs with hiso
      · have h0 := hiso P hPmem.1 hPmem.2
        rw [h0, zero_add]; exact card_pos.2 ⟨u, hu'⟩
      · simpa using card_le_card hsub
  have hsum := sum_le_sum hper
  rw [sum_add_distrib, ← card_filter] at hsum
  have hswap : ∑ v ∈ Hᶜ, ∑ P ∈ Ws.filter (fun P => v ∈ mem P),
        (G.neighborFinset v ∩ (mem P \ H)).card
      = ∑ P ∈ Ws, ∑ v ∈ mem P \ H, (G.neighborFinset v ∩ (mem P \ H)).card := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl; intro P _
    rw [← sum_filter]
    apply sum_congr
    · ext v; simp [mem_sdiff, and_comm]
    · intros; rfl
  rw [hswap] at hsum
  exact hsum

/-! ## Global arithmetic of the hub budget -/

/-- **The hub budget, exact, with the cubic-neighbour fact**:
* `intL + 6h + σ = 3n` (dart identity), `σ + s = n`, `n = 13ν + r`;
* `∑_P #LL(P) + 4h_W = 24ν + 2ε` (`window_LL_exact` summed);
* `intL = ∑_P #LL(P) + 2X` (`2X`: the `L–L` darts off the window paths);
* `2X ≥ I` (`LL_split`), `I ≥ I_W + (r − h_R)` (every cubic vertex of `R` is counted);
* `h = h_W + h_R`.
Then `2X = 2ν + 2r + s − 2h − 4h_R − 2ε` and `2h + 3h_R + 2ε + I_W ≤ 2ν + r + s`. -/
theorem hub_budget (intL h hW hR σ s n ν r LLW X ε I IW : ℤ)
    (hL : intL + 6 * h + σ = 3 * n) (hσ : σ + s = n) (hn : n = 13 * ν + r)
    (hF : LLW + 4 * hW = 24 * ν + 2 * ε) (hX : intL = LLW + 2 * X)
    (hI : I ≤ 2 * X) (hIW : IW + (r - hR) ≤ I) (hh : h = hW + hR) :
    2 * X = 2 * ν + 2 * r + s - 2 * h - 4 * hR - 2 * ε ∧
      2 * h + 3 * hR + 2 * ε + IW ≤ 2 * ν + r + s := by
  refine ⟨by linarith, by linarith⟩

/-- **Edge ends.**  Cubic window free ends `15ν − h_W − ε` split as
`Y_W + 2X_WW + X_WR` (hub / window cubic / remainder cubic), `X_WW + X_WR ≤ X`.  Hence the
cubic window ends not on a hub number `2X_WW + X_WR ≤ 2ν + 2r + s − 2h − 4h_R − 2ε`, and
`Y_W ≥ 13ν − 2r − s + h + 5h_R + ε`. -/
theorem edge_ends (h hW hR ν r s X ε YW XWW XWR : ℤ) (hh : h = hW + hR)
    (h2X : 2 * X = 2 * ν + 2 * r + s - 2 * h - 4 * hR - 2 * ε)
    (hcub : 15 * ν - hW - ε = YW + 2 * XWW + XWR) (hXs : XWW + XWR ≤ X)
    (hWW : 0 ≤ XWW) (hWR : 0 ≤ XWR) :
    2 * XWW + XWR ≤ 2 * ν + 2 * r + s - 2 * h - 4 * hR - 2 * ε ∧
      13 * ν - 2 * r - s + h + 5 * hR + ε ≤ YW := by
  refine ⟨by linarith, by linarith⟩

/-- **The joint hub system** (the hub budget ⊕ `five_hub_bound` ⊕ `big_hub_bound` ⊕ the dart
identity): with `h₄ = h − k` hubs of degree 4 and `k` big hubs carrying `σ_B = ∑_B (d−3)`:
`σ = h₄ + σ_B`, `h ≤ ν + (r+s)/2`, `5h ≤ n + s`, `2k ≤ s`, hence
`2σ_B ≥ 24ν + r − 3s` and `2σ_B ≥ 2n − 2s − 2(n+s)/5` i.e. `5σ_B ≥ 4n − 6s`. -/
theorem big_hub_mass (h h4 k σ σB s n ν r hR ε IW : ℤ) (hk : h = h4 + k) (hσB : σ = h4 + σB)
    (hσ : σ + s = n) (hn : n = 13 * ν + r)
    (hbud : 2 * h + 3 * hR + 2 * ε + IW ≤ 2 * ν + r + s) (h5 : 5 * h + σ ≤ 2 * n)
    (h2k : 2 * k + σ ≤ n) (h0 : 0 ≤ hR) (h0' : 0 ≤ ε) (h0'' : 0 ≤ IW) (hk0 : 0 ≤ k) :
    24 * ν + r - 3 * s ≤ 2 * σB ∧ 4 * n - 6 * s ≤ 5 * σB ∧ 2 * k ≤ s := by
  refine ⟨by linarith, by linarith, by linarith⟩


end Budget

/-! ## windows hanging on a vertex set; the partition slack -/

section Slack


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

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

theorem internal_le (S : Finset V) (u : V) (hu : u ∈ S) :
    (G.neighborFinset u ∩ S).card ≤ S.card - 1 := by
  rw [← card_erase_of_mem hu]
  apply card_le_card
  intro w hw
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hw
  exact mem_erase.2 ⟨fun h => by subst h; exact G.irrefl hw.1, hw.2⟩

/-- **Degeneracy ⇒ density** : proper `S`, `|S| ≥ 2` ⇒ `int S + 6 ≤ 4|S|`. -/
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

/-- The slack of a vertex set. -/
def slack (S : Finset V) : ℤ :=
  4 * (S.card : ℤ) - 6 - ∑ u ∈ S, ((G.neighborFinset u ∩ S).card : ℤ)

theorem card_inter_union (v : V) (K P : Finset V) (hKP : Disjoint K P) :
    (G.neighborFinset v ∩ (K ∪ P)).card
      = (G.neighborFinset v ∩ K).card + (G.neighborFinset v ∩ P).card := by
  rw [inter_union_distrib_left, card_union_of_disjoint]
  exact Disjoint.mono inter_subset_right inter_subset_right hKP

theorem sum_inter_comm' (A B : Finset V) :
    ∑ v ∈ A, (G.neighborFinset v ∩ B).card = ∑ w ∈ B, (G.neighborFinset w ∩ A).card := by
  have e : ∀ v (C : Finset V), G.neighborFinset v ∩ C = C.filter (fun w => G.Adj v w) := by
    intro v C; ext w; simp [SimpleGraph.mem_neighborFinset, and_comm]
  simp_rw [e, card_filter]
  rw [sum_comm]
  apply sum_congr rfl; intro w _; apply sum_congr rfl; intro v _
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- **One hanging window.**  `P` disjoint from `K`, `|P| = 13`, `int P = 24`, every edge
leaving `P` goes into `K`.  Then `slack(K ∪ P) = slack(K) − 2 − 2σ_P`. -/
theorem hang_one (K P : Finset V) (hKP : Disjoint K P) (hcard : P.card = 13)
    (h24 : ∑ v ∈ P, (G.neighborFinset v ∩ P).card = 24)
    (hout : ∀ v ∈ P, G.neighborFinset v ⊆ K ∪ P) (hdeg : ∀ v ∈ P, 3 ≤ G.degree v) :
    slack G (K ∪ P) = slack G K - 2 - 2 * ∑ v ∈ P, ((G.degree v : ℤ) - 3) := by
  unfold slack
  rw [card_union_of_disjoint hKP, sum_union hKP]
  have hP : ∀ v ∈ P, (G.neighborFinset v ∩ (K ∪ P)).card = G.degree v := by
    intro v hv
    rw [← G.card_neighborFinset_eq_degree, inter_eq_left.2 (hout v hv)]
  have hK : ∀ v ∈ K, (G.neighborFinset v ∩ (K ∪ P)).card
      = (G.neighborFinset v ∩ K).card + (G.neighborFinset v ∩ P).card :=
    fun v _ => card_inter_union G v K P hKP
  have hPK : ∀ v ∈ P, G.degree v
      = (G.neighborFinset v ∩ K).card + (G.neighborFinset v ∩ P).card := by
    intro v hv; rw [← hP v hv]; exact card_inter_union G v K P hKP
  have e1 := sum_congr rfl hK
  have e2 := sum_congr rfl hP
  have e3 := sum_congr rfl hPK
  rw [sum_add_distrib] at e1 e3
  have e4 := sum_inter_comm' G K P
  have e5 : ∑ v ∈ P, ((G.degree v : ℤ) - 3) = ∑ v ∈ P, (G.degree v : ℤ) - 39 := by
    rw [sum_sub_distrib, sum_const, hcard]; simp
  rw [e5]
  have e3' : (∑ v ∈ P, (G.degree v : ℤ)) = ∑ v ∈ P, ((G.neighborFinset v ∩ K).card : ℤ)
      + ∑ v ∈ P, ((G.neighborFinset v ∩ P).card : ℤ) := by exact_mod_cast e3
  have e4' : (∑ v ∈ K, ((G.neighborFinset v ∩ P).card : ℤ))
      = ∑ v ∈ P, ((G.neighborFinset v ∩ K).card : ℤ) := by exact_mod_cast e4
  have h24' : (∑ v ∈ P, ((G.neighborFinset v ∩ P).card : ℤ)) = 24 := by exact_mod_cast h24
  have e1' : (∑ x ∈ K, ((G.neighborFinset x ∩ (K ∪ P)).card : ℤ))
      = ∑ x ∈ K, ((G.neighborFinset x ∩ K).card : ℤ)
        + ∑ x ∈ K, ((G.neighborFinset x ∩ P).card : ℤ) := by exact_mod_cast e1
  have e2' : (∑ x ∈ P, ((G.neighborFinset x ∩ (K ∪ P)).card : ℤ))
      = ∑ x ∈ P, (G.degree x : ℤ) := by exact_mod_cast e2
  have hc' : ((P.card : ℕ) : ℤ) = 13 := by exact_mod_cast hcard
  rw [e1', e2']
  push_cast
  rw [hc']
  linarith

/-- **Several hanging windows.**  Pairwise disjoint windows `mem P` (`P ∈ Ws`), each
disjoint from `K`, of order 13 with `int = 24`, every edge leaving each goes into `K`:
`slack(K ∪ ⋃P) = slack(K) − ∑_P (2 + 2σ_P)`. -/
theorem hang_many {ι : Type*} [DecidableEq ι] (K : Finset V) (mem : ι → Finset V)
    (hdeg : ∀ v, 3 ≤ G.degree v) :
    ∀ Ws : Finset ι, (∀ P ∈ Ws, ∀ Q ∈ Ws, P ≠ Q → Disjoint (mem P) (mem Q)) →
      (∀ P ∈ Ws, Disjoint K (mem P)) → (∀ P ∈ Ws, (mem P).card = 13) →
      (∀ P ∈ Ws, ∑ v ∈ mem P, (G.neighborFinset v ∩ mem P).card = 24) →
      (∀ P ∈ Ws, ∀ v ∈ mem P, G.neighborFinset v ⊆ K ∪ mem P) →
      slack G (K ∪ Ws.biUnion mem)
        = slack G K - ∑ P ∈ Ws, (2 + 2 * ∑ v ∈ mem P, ((G.degree v : ℤ) - 3)) := by
  intro Ws
  induction Ws using Finset.induction_on with
  | empty => intros; simp
  | @insert Q Ws hQ ih =>
    intro hdisj hK hc h24 hout
    have ih' := ih (fun P hP R hR => hdisj P (mem_insert_of_mem hP) R (mem_insert_of_mem hR))
      (fun P hP => hK P (mem_insert_of_mem hP)) (fun P hP => hc P (mem_insert_of_mem hP))
      (fun P hP => h24 P (mem_insert_of_mem hP))
      (fun P hP => hout P (mem_insert_of_mem hP))
    have hdQ : Disjoint (K ∪ Ws.biUnion mem) (mem Q) := by
      rw [disjoint_union_left]
      refine ⟨hK Q (mem_insert_self _ _), ?_⟩
      rw [disjoint_biUnion_left]
      intro P hP
      exact hdisj P (mem_insert_of_mem hP) Q (mem_insert_self _ _)
        (fun e => hQ (e ▸ hP))
    have hone := hang_one G (K ∪ Ws.biUnion mem) (mem Q) hdQ (hc Q (mem_insert_self _ _))
      (h24 Q (mem_insert_self _ _))
      (fun v hv => by
        intro w hw
        have := hout Q (mem_insert_self _ _) v hv hw
        simp only [mem_union] at this ⊢; tauto)
      (fun v _ => hdeg v)
    have eU : K ∪ (insert Q Ws).biUnion mem = K ∪ Ws.biUnion mem ∪ mem Q := by
      rw [biUnion_insert]; ext x; simp only [mem_union]; tauto
    rw [eU, hone, ih', sum_insert hQ]
    ring

/-- **Hanging bound.**  If `K ∪ ⋃P` is proper, the density fact gives
`∑_P (2 + 2σ_P) ≤ slack(K)`: at most `slack(K)/2` windows hang entirely on `K`. -/
theorem hanging_bound {ι : Type*} [DecidableEq ι] (K : Finset V) (mem : ι → Finset V)
    (hdeg : ∀ v, 3 ≤ G.degree v)
    (hdens : ∀ S : Finset V, S ≠ univ → 2 ≤ S.card →
      ∑ u ∈ S, (G.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card)
    (Ws : Finset ι) (hne : Ws.Nonempty)
    (hdisj : ∀ P ∈ Ws, ∀ Q ∈ Ws, P ≠ Q → Disjoint (mem P) (mem Q))
    (hK : ∀ P ∈ Ws, Disjoint K (mem P)) (hc : ∀ P ∈ Ws, (mem P).card = 13)
    (h24 : ∀ P ∈ Ws, ∑ v ∈ mem P, (G.neighborFinset v ∩ mem P).card = 24)
    (hout : ∀ P ∈ Ws, ∀ v ∈ mem P, G.neighborFinset v ⊆ K ∪ mem P)
    (hproper : K ∪ Ws.biUnion mem ≠ univ) :
    ∑ P ∈ Ws, (2 + 2 * ∑ v ∈ mem P, ((G.degree v : ℤ) - 3)) ≤ slack G K := by
  have hh := hang_many G K mem hdeg Ws hdisj hK hc h24 hout
  obtain ⟨P, hP⟩ := hne
  have h2 : 2 ≤ (K ∪ Ws.biUnion mem).card := by
    have : mem P ⊆ K ∪ Ws.biUnion mem := fun x hx => mem_union_right _ (mem_biUnion.2 ⟨P, hP, hx⟩)
    have := card_le_card this; rw [hc P hP] at this; omega
  have hd := hdens _ hproper h2
  have hs : 0 ≤ slack G (K ∪ Ws.biUnion mem) := by
    unfold slack; push_cast
    have : ((∑ u ∈ K ∪ Ws.biUnion mem,
        (G.neighborFinset u ∩ (K ∪ Ws.biUnion mem)).card : ℕ) : ℤ) + 6
          ≤ 4 * ((K ∪ Ws.biUnion mem).card : ℤ) := by exact_mod_cast hd
    push_cast at this; linarith
  linarith

/-- The slack of a single vertex is `−2`. -/
theorem slack_singleton (v : V) : slack G {v} = -2 := by
  unfold slack
  have : (G.neighborFinset v ∩ {v}).card = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro w hw
    simp only [mem_inter, mem_singleton, SimpleGraph.mem_neighborFinset] at hw
    obtain ⟨h1, rfl⟩ := hw; exact G.irrefl h1
  simp [this]

/-- **Slack formula** : `slack S = |S| + ∂S − 6 − σ_S`. -/
theorem slack_formula (S : Finset V) :
    slack G S = S.card + ∑ u ∈ S, ((G.neighborFinset u \ S).card : ℤ) - 6
        - ∑ u ∈ S, ((G.degree u : ℤ) - 3) := by
  unfold slack
  have hd : ∀ u, (G.degree u : ℤ) = (G.neighborFinset u ∩ S).card
      + (G.neighborFinset u \ S).card := by
    intro u
    rw [← G.card_neighborFinset_eq_degree, ← card_inter_add_card_sdiff (G.neighborFinset u) S]
    push_cast; ring
  simp_rw [hd, sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
  ring

/-! ## The partition slack and the component/cross trade-off -/

/-- **Partition slack identity.**  Components `K` of `G[R]` with `slack(K) = |K| + e(K,W) −
6 − σ_K`, `∑|K| = r`, `∑ e(K,W) = e(R,W)`, `∑σ_K = σ_R`; join `e(R,W) + 2e× = 15ν + σ_W`,
`σ_W + σ_R = σ`, `σ + s = n = 13ν + r`:
`∑_K slack(K) = s + 2ν + 2σ_W − 2e× − 6c`. -/
theorem partition_slack (sumSlack r eRW σR σW σ s n ν ex c : ℤ)
    (hsum : sumSlack = r + eRW - 6 * c - σR) (hjoin : eRW + 2 * ex = 15 * ν + σW)
    (hσ : σW + σR = σ) (hs : σ + s = n) (hn : n = 13 * ν + r) :
    sumSlack = s + 2 * ν + 2 * σW - 2 * ex - 6 * c := by
  linarith

/-- **Trade-off.**  Non-singleton components have `slack ≥ 2·(hanging windows) ≥ 0`,
singletons have slack `−2`; so with `c₁` singleton components and `ν_h` windows hanging
entirely on single components: `6c − 2c₁ + 2e× + 2ν_h ≤ s + 2ν + 2σ_W`.  With the
bridgeless cut `e(K,W) ≥ 2`: `2c ≤ e(R,W) ≤ 15ν + σ_W`. -/
theorem trade_off (sumSlack c c1 ex νh ν σW s eRW : ℤ)
    (hid : sumSlack = s + 2 * ν + 2 * σW - 2 * ex - 6 * c)
    (hlow : 2 * νh - 2 * c1 ≤ sumSlack) (hcut : 2 * c ≤ eRW)
    (hjoin : eRW + 2 * ex = 15 * ν + σW) (hex : 0 ≤ ex) :
    6 * c - 2 * c1 + 2 * ex + 2 * νh ≤ s + 2 * ν + 2 * σW ∧ 2 * c ≤ 15 * ν + σW := by
  constructor <;> linarith


end Slack

/-! ## lifting incidence cycles; the length constraints -/

section Lift


variable {V : Type*} {G : SimpleGraph V}

/-- A chain list is the support of a walk from its head to its last element. -/
theorem exists_walk_of_chain : ∀ (l : List V) (a : V), List.IsChain G.Adj (a :: l) →
    ∃ p : G.Walk a ((a :: l).getLast (List.cons_ne_nil _ _)), p.support = a :: l
  | [], a, _ => ⟨SimpleGraph.Walk.nil, rfl⟩
  | b :: l, a, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨p, hp⟩ := exists_walk_of_chain l b h.2
    exact ⟨SimpleGraph.Walk.cons h.1 p, by simp [hp]⟩

/-- **List cycle.**  A duplicate-free chain list `a :: l` of length `≥ 3` whose last element
is adjacent to `a` is (the support of) a cycle of length `|a :: l|`. -/
theorem list_cycle (a : V) (l : List V) (hnd : (a :: l).Nodup)
    (hch : List.IsChain G.Adj (a :: l)) (hlen : 2 ≤ l.length)
    (hclose : G.Adj ((a :: l).getLast (List.cons_ne_nil _ _)) a) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = l.length + 1 := by
  obtain ⟨p, hp⟩ := exists_walk_of_chain l a hch
  let q : G.Walk _ a := SimpleGraph.Walk.cons hclose SimpleGraph.Walk.nil
  have hpP : p.IsPath := by rw [SimpleGraph.Walk.isPath_def, hp]; exact hnd
  have hqP : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, and_true]
    exact G.ne_of_adj hclose
  have hplen : p.length = l.length := by
    have := congrArg List.length hp
    rw [SimpleGraph.Walk.length_support] at this; simpa using this
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    rw [hp]
    simp only [List.tail_cons, q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    intro x hx hx'
    simp only [List.mem_singleton] at hx'
    subst hx'
    exact (List.nodup_cons.1 hnd).1 hx
  refine ⟨p.append q, hpP.isCycle_append hqP hdisj (Or.inl (by omega)), ?_⟩
  rw [SimpleGraph.Walk.length_append, hplen]; rfl

/-! ## Blocks `h :: seg` -/

/-- Flatten of blocks `h :: seg`. -/
def blockList (bs : List (V × List V)) : List V := bs.flatMap (fun b => b.1 :: b.2)

/-- Last vertex of a block. -/
def blockLast (b : V × List V) : V := (b.1 :: b.2).getLast (List.cons_ne_nil _ _)

theorem blockList_length (bs : List (V × List V)) :
    (blockList bs).length = (bs.map (fun b => b.2.length + 1)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [blockList, List.flatMap_cons, List.length_append, List.length_cons,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- The flattened blocks form a chain when each block is a chain and the last vertex of each
block is adjacent to the next hub. -/
theorem blockList_chain : ∀ (bs : List (V × List V)),
    (∀ b ∈ bs, List.IsChain G.Adj (b.1 :: b.2)) →
    List.IsChain (fun b b' => G.Adj (blockLast b) b'.1) bs →
    List.IsChain G.Adj (blockList bs)
  | [], _, _ => List.IsChain.nil
  | [b], hb, _ => by simpa [blockList] using hb b (by simp)
  | b :: b' :: bs, hb, hc => by
    rw [List.isChain_cons_cons] at hc
    have ih := blockList_chain (b' :: bs) (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hc.2
    have e : blockList (b :: b' :: bs) = (b.1 :: b.2) ++ blockList (b' :: bs) := by
      simp [blockList]
    rw [e, List.isChain_append]
    refine ⟨hb b (by simp), ih, ?_⟩
    intro x hx y hy
    simp only [List.getLast?_eq_some_getLast (List.cons_ne_nil b.1 b.2), Option.mem_def,
      Option.some.injEq] at hx
    simp only [blockList, List.flatMap_cons, List.cons_append, List.head?_cons,
      Option.mem_def, Option.some.injEq] at hy
    subst hx; subst hy
    exact hc.1


theorem blockList_getLast? : ∀ (b₀ : V × List V) (bs : List (V × List V)),
    (blockList (b₀ :: bs)).getLast? = some (blockLast ((b₀ :: bs).getLast (List.cons_ne_nil _ _)))
  | b₀, [] => by
    simp only [blockList, List.flatMap_cons, List.flatMap_nil, List.append_nil, blockLast,
      List.getLast_singleton]
    exact List.getLast?_eq_some_getLast _
  | b₀, b :: bs => by
    have e1 : blockList (b₀ :: b :: bs) = (b₀.1 :: b₀.2) ++ blockList (b :: bs) := by
      simp [blockList]
    rw [e1, List.getLast?_append, blockList_getLast? b bs, List.getLast_cons_cons]
    rfl

/-- **The lift is a cycle.**  Blocks `(h_i, seg_i)`, `t ≥ 1`: every block `h_i :: seg_i` a
chain (hub adjacent to the start of its segment, segment a path), the end of each segment
adjacent to the next hub and the last one to `h₁`, all vertices distinct, total `≥ 3`.
Then `G` has a cycle of length `∑ (|seg_i| + 1)` (`= ∑ gap_i + 2t` with `gap_i = |seg_i| − 1`). -/
theorem lift_cycle (b₀ : V × List V) (bs : List (V × List V))
    (hnd : (blockList (b₀ :: bs)).Nodup)
    (hb : ∀ b ∈ b₀ :: bs, List.IsChain G.Adj (b.1 :: b.2))
    (hc : List.IsChain (fun b b' => G.Adj (blockLast b) b'.1) (b₀ :: bs))
    (hclose : G.Adj (blockLast ((b₀ :: bs).getLast (List.cons_ne_nil _ _))) b₀.1)
    (h3 : 3 ≤ (blockList (b₀ :: bs)).length) :
    ∃ c : G.Walk b₀.1 b₀.1, c.IsCycle ∧
      c.length = ((b₀ :: bs).map (fun b => b.2.length + 1)).sum := by
  have hch := blockList_chain (b₀ :: bs) hb hc
  have hlast := blockList_getLast? b₀ bs
  have hlen := blockList_length (b₀ :: bs)
  have e : blockList (b₀ :: bs) = b₀.1 :: (b₀.2 ++ blockList bs) := by simp [blockList]
  rw [e] at hnd hch h3 hlast hlen
  have hclose' : ∀ z ∈ (b₀.1 :: (b₀.2 ++ blockList bs)).getLast?, G.Adj z b₀.1 := by
    intro z hz
    rw [hlast, Option.mem_def, Option.some.injEq] at hz
    subst hz; exact hclose
  obtain ⟨c, hcyc, hclen⟩ := list_cycle b₀.1 (b₀.2 ++ blockList bs) hnd hch
    (by simp only [List.length_cons] at h3; omega)
    (hclose' _ (by rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]; rfl))
  refine ⟨c, hcyc, ?_⟩
  rw [hclen, ← hlen]
  rfl

/-! ## Arithmetic of lift lengths -/

/-- Powers of two `≥ 4`. -/
def Dyadic (L : ℕ) : Prop := ∃ k, 2 ≤ k ∧ L = 2 ^ k

/-- **Interval ⇒ power of two.**  Every interval `[L, 2L)` with `L ≥ 3` contains a power of
two `≥ 4`: a family of lifts realizing every length in `[L, 2L)` has a dyadic member. -/
theorem interval_has_dyadic (L : ℕ) (hL : 3 ≤ L) : ∃ m, L ≤ m ∧ m < 2 * L ∧ Dyadic m := by
  have h1 := Nat.pow_log_le_self 2 (show L ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
  set k := Nat.log 2 L
  rw [Nat.succ_eq_add_one, pow_succ] at h2
  rcases Nat.eq_or_lt_of_le h1 with he | hlt
  · refine ⟨L, le_rfl, by omega, k, ?_, he.symm⟩
    by_contra hk; push Not at hk
    interval_cases k <;> simp at he <;> omega
  · refine ⟨2 ^ (k + 1), by rw [pow_succ]; omega, by rw [pow_succ]; omega, k + 1, ?_, rfl⟩
    by_contra hk; push Not at hk
    have : k = 0 := by omega
    rw [this] at h2; simp at h2; omega

/-- **Sumset of intervals.**  Gap choices `[a_i, b_i]` on the `t` windows of a lifted cycle
(every value realized) realize every length in `[∑a_i + 2t, ∑b_i + 2t]`; if
`∑ b_i + 2t ≥ 2(∑ a_i + 2t) − 1` some lift has dyadic length. -/
theorem sumset_interval_dyadic (A Bs t : ℕ) (hA : 3 ≤ A + 2 * t)
    (hwide : 2 * (A + 2 * t) ≤ Bs + 2 * t + 1)
    (realized : ∀ m, A + 2 * t ≤ m → m ≤ Bs + 2 * t → ¬ Dyadic m) : False := by
  obtain ⟨m, h1, h2, hm⟩ := interval_has_dyadic (A + 2 * t) hA
  exact realized m h1 (by omega) hm

theorem not_dyadic_of_bounds (L k0 : ℕ) (hlt : L < 2 ^ k0)
    (h : ∀ k, 2 ≤ k → k < k0 → L ≠ 2 ^ k) : ¬ Dyadic L := by
  rintro ⟨k, hk, e⟩
  by_cases hk0 : k < k0
  · exact h k hk hk0 e
  · push Not at hk0
    have : 2 ^ k0 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk0
    omega

/-! ##  at the level of gaps -/

/-- **Two hubs, two windows (the `B`-4-cycle).**  Gaps `g_P, g_Q ≤ 12` of two distinct hubs
on two distinct windows lift to a cycle of length `g_P + g_Q + 4`; it is non-dyadic iff
`g_P + g_Q ∉ {0, 4, 12}`. -/
theorem b4_constraint (gP gQ : ℕ) (hP : gP ≤ 12) (hQ : gQ ≤ 12) :
    ¬ Dyadic (gP + gQ + 4) ↔ gP + gQ ≠ 0 ∧ gP + gQ ≠ 4 ∧ gP + gQ ≠ 12 := by
  constructor
  · intro h
    refine ⟨fun e => h ⟨2, le_rfl, by omega⟩, fun e => h ⟨3, by norm_num, by omega⟩,
      fun e => h ⟨4, by norm_num, by omega⟩⟩
  · rintro ⟨h0, h4, h12⟩
    apply not_dyadic_of_bounds _ 5 (by norm_num; omega)
    intro k hk hk5
    interval_cases k <;> omega

/-- **Shared-window gaps `≡ 1 (mod 4)` always pass the `B`-4-cycle test**
(`g + g' ≡ 2 (mod 4)`): two hubs may share any number of windows at gap `1`. -/
theorem gaps_one_mod_four_pass (g g' : ℕ) (h : g % 4 = 1) (h' : g' % 4 = 1)
    (hg : g ≤ 12) (hg' : g' ≤ 12) : ¬ Dyadic (g + g' + 4) := by
  rw [b4_constraint g g' hg hg']; omega

/-- **Same hub twice on one window**: positions at distance `d` close a cycle of length
`d + 2`; non-dyadic iff `d ∉ {2, 6}`. -/
theorem same_hub_constraint (d : ℕ) (hd12 : d ≤ 12) :
    ¬ Dyadic (d + 2) ↔ d ≠ 2 ∧ d ≠ 6 := by
  constructor
  · intro h
    exact ⟨fun e => h ⟨2, le_rfl, by omega⟩, fun e => h ⟨3, by norm_num, by omega⟩⟩
  · rintro ⟨h2, h6⟩
    apply not_dyadic_of_bounds _ 4 (by norm_num; omega)
    intro k hk hk4
    interval_cases k <;> omega

/-- **Multi-lift example** (one hub at two adjacent positions `a, a+1` of `P`, the other at
`b = a + 5`, gap `1` on `Q`): the two lifts have lengths `10` and `9`, both non-dyadic. -/
theorem multi_lift_example : ¬ Dyadic (5 + 1 + 4) ∧ ¬ Dyadic (4 + 1 + 4) := by
  constructor
  · apply not_dyadic_of_bounds _ 4 (by norm_num); intro k hk hk4; interval_cases k <;> norm_num
  · apply not_dyadic_of_bounds _ 4 (by norm_num); intro k hk hk4; interval_cases k <;> norm_num

/-- **Where the gap-`1 (mod 4)` escape meets a dyadic length.**  With every gap `≡ 1 (mod 4)`
a lift through 4 windows has length `∑g_i + 8 ≡ 0 (mod 4)` in `[12, 56]`; it is dyadic
exactly when `∑ g_i ∈ {8, 24}` (lengths `16`, `32`; `∑ g_i ≥ 4` excludes `0`). -/
theorem four_window_dyadic (S : ℕ) (hS4 : 4 ≤ S) (hS : S ≤ 48) :
    Dyadic (S + 8) ↔ (S = 8 ∨ S = 24) := by
  constructor
  · rintro ⟨k, hk, e⟩
    have hk6 : k < 6 := by
      by_contra hc; push Not at hc
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases k <;> norm_num at e <;> omega
  · rintro (e | e)
    · exact ⟨4, by norm_num, by omega⟩
    · exact ⟨5, by norm_num, by omega⟩


end Lift

/-! ## windows against the big-hub neighbourhood -/

section WindowU


theorem block4 (T : Finset ℕ) (a : ℕ) :
    (if a ∈ T then 1 else 0) + (if a + 1 ∈ T then 1 else 0) + (if a + 2 ∈ T then 1 else 0)
      + (if a + 3 ∈ T then 1 else 0)
      ≤ 2 + (if a ∈ T ∧ a + 2 ∈ T then 1 else 0) + (if a + 1 ∈ T ∧ a + 1 + 2 ∈ T then 1 else 0) := by
  have e : a + 1 + 2 = a + 3 := by omega
  rw [e]
  by_cases h0 : a ∈ T <;> by_cases h1 : a + 1 ∈ T <;> by_cases h2 : a + 2 ∈ T <;>
    by_cases h3 : a + 3 ∈ T <;> simp [h0, h1, h2, h3]

/-- **No gap-2 pair ⇒ at most 7 positions** (13 positions): `|T ∩ [0,12]| ≤ 7 + #{i ≤ 10 :
i, i+2 ∈ T}`. -/
theorem block_ineq (T : Finset ℕ) :
    ((range 13).filter (· ∈ T)).card
      ≤ 7 + ((range 11).filter (fun i => i ∈ T ∧ i + 2 ∈ T)).card := by
  rw [card_filter, card_filter]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  have b0 := block4 T 0
  have b4 := block4 T 4
  have b8 := block4 T 8
  simp only [zero_add] at b0
  norm_num at b0 b4 b8 ⊢
  have h12 : (if (12 : ℕ) ∈ T then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- **One window against `U`.**  `g 0 … g 12` an injective path (consecutive adjacent);
`X2 ⊇ {x ∉ B : two distinct neighbours in U}`.  Then
`#{t : g t ∈ U} ≤ 7 + #{t : g t ∈ X2 ∪ B}`. -/
theorem window_U (U B X2 : Finset V) (g : ℕ → V)
    (hinj : ∀ a < 13, ∀ b < 13, g a = g b → a = b)
    (hadj : ∀ i < 12, G.Adj (g i) (g (i + 1)))
    (hX2 : ∀ x, x ∉ B → ∀ a b, a ≠ b → a ∈ U → b ∈ U → G.Adj x a → G.Adj x b → x ∈ X2) :
    ((range 13).filter (fun t => g t ∈ U)).card
      ≤ 7 + ((range 13).filter (fun t => g t ∈ X2 ∪ B)).card := by
  classical
  set T : Finset ℕ := (range 13).filter (fun t => g t ∈ U) with hT
  have h1 := block_ineq T
  have e1 : (range 13).filter (· ∈ T) = T := by
    ext t; simp [hT]
  rw [e1] at h1
  have h2 : ((range 11).filter (fun i => i ∈ T ∧ i + 2 ∈ T)).card
      ≤ ((range 13).filter (fun t => g t ∈ X2 ∪ B)).card := by
    apply card_le_card_of_injOn (fun i => i + 1)
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, hT, mem_filter] at hi ⊢
      obtain ⟨hi11, ⟨-, hu0⟩, ⟨-, hu2⟩⟩ := hi
      refine ⟨by omega, ?_⟩
      rw [mem_union]
      by_cases hB : g (i + 1) ∈ B
      · exact Or.inr hB
      · left
        refine hX2 (g (i + 1)) hB (g i) (g (i + 2)) (fun e => ?_) hu0 hu2
          (hadj i (by omega)).symm ?_
        · have := hinj i (by omega) (i + 2) (by omega) e; omega
        · have := hadj (i + 1) (by omega); rwa [show i + 1 + 1 = i + 2 by omega] at this
    · intro a _ b _ e; simpa using e
  omega


end WindowU

end Hypostructure.Graph.HubWin
