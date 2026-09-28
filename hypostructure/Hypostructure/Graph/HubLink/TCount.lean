import Hypostructure.Graph.JointSystem

/-!
# Hub-degree of the cubic vertices and links

Vocabulary-free.

`JointSystem` setting: `δ ≥ 3` (`hmin`), `H = {deg ≥ 4}` independent (`hind`), no `C₄`
(`hC4`), noProperBaseline (`hdeg`).  `t(x) = |N(x) ∩ H|`, `A_j = {x ∈ L : t(x) = j}`.

* `tsum`: `Σ_{x∈L} t(x) = e(H,L) = 3|H| + σ`.
* `acount`: `|A₀| + |A₁| + |A₂| = |L|`, `|A₁| + 2|A₂| = 3|H| + σ` (`t ≤ 2`).
* `a2_le`: `|A₂| ≤ C(|H|, 2)` (two hubs share `≤ 1` neighbour).
* `exception_identity`: `|A₂| + n = |A₀| + 4|H| + σ`, i.e. `|A₂| − |A₀| = 4|H| − s`.
* `outer_cubic`, `linked_of_not_unlinked`, `unlinked_card`: every `x ∈ A₁` outside the
  unlinked set `U` has a cubic neighbour `y` with a hub `h'` not adjacent to `x` (a link), and
  `|U| ≤ 3|A₀|`.
* `hub_link_count`: `d_h ≤ (|H| − 1) + |N(h) ∩ U| + #(linked neighbours of h)`,
  `Σ_{h∈H} |N(h) ∩ U| = |U|`.
-/

open Finset Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

variable (G) in
/-- `t(x) = |N(x) ∩ H|`. -/
noncomputable abbrev tc (x : V) : ℕ := (G.neighborFinset x ∩ Hset G).card

variable (G) in
/-- `A_j = {x ∈ L : t(x) = j}`. -/
noncomputable abbrev Aset (j : ℕ) : Finset V := (Lset G).filter (fun x => tc G x = j)

/-- **`Σ_{x∈L} t(x) = 3|H| + σ`.** -/
theorem tsum (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) :
    ∑ x ∈ Lset G, tc G x = 3 * (Hset G).card + sigma G := by
  rw [double_count G (Lset G) (Hset G), ← hub_deg_eq_inter_L hmin hind, hub_sum hmin]

theorem tc_le_two (hmin : ∀ v, 3 ≤ G.degree v) (hdeg : ProperTwoLow G) {x : V}
    (hx : x ∈ Lset G) : tc G x ≤ 2 :=
  cubic_hub_nbrs_le_two hmin hdeg (by simpa using hx)

/-- **The `t`-classes.** -/
theorem acount (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G) :
    (Aset G 0).card + (Aset G 1).card + (Aset G 2).card = (Lset G).card ∧
      (Aset G 1).card + 2 * (Aset G 2).card = 3 * (Hset G).card + sigma G := by
  have ht := tsum hmin hind
  have e : ∀ j, (Aset G j).card = ∑ x ∈ Lset G, if tc G x = j then 1 else 0 :=
    fun j => card_filter _ _
  rw [e 0, e 1, e 2]
  constructor
  · rw [← sum_add_distrib, ← sum_add_distrib, card_eq_sum_ones (Lset G)]
    apply sum_congr rfl; intro x hx
    have := tc_le_two hmin hdeg hx
    interval_cases (tc G x) <;> simp
  · rw [← ht, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro x hx
    have := tc_le_two hmin hdeg hx
    interval_cases (tc G x) <;> simp

/-- Two distinct vertices share at most one neighbour. -/
theorem codeg_le_one (hC4 : C4Free G) {a b : V} (hab : a ≠ b) :
    (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 := by
  rw [card_le_one]
  intro c hc c' hc'
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hc hc'
  exact hC4 a b c c' hab hc.1 hc.2 hc'.1 hc'.2

/-- **`|A₂| ≤ C(|H|, 2)`.** -/
theorem a2_le (hC4 : C4Free G) : (Aset G 2).card ≤ (Hset G).card.choose 2 := by
  rw [← card_powersetCard]
  refine card_le_card_of_injOn (fun x => G.neighborFinset x ∩ Hset G) ?_ ?_
  · intro x hx
    rw [mem_coe, mem_filter] at hx
    rw [mem_coe, mem_powersetCard]
    exact ⟨inter_subset_right, hx.2⟩
  · intro x hx x' hx' e
    rw [mem_coe, mem_filter] at hx hx'
    obtain ⟨a, b, hab, hS⟩ := card_eq_two.1 hx.2
    have ha : a ∈ G.neighborFinset x ∩ Hset G := by rw [hS]; simp
    have hb : b ∈ G.neighborFinset x ∩ Hset G := by rw [hS]; simp
    have ha' : a ∈ G.neighborFinset x' ∩ Hset G := by
      simp only at e; rw [← e]; exact ha
    have hb' : b ∈ G.neighborFinset x' ∩ Hset G := by
      simp only at e; rw [← e]; exact hb
    simp only [mem_inter, SimpleGraph.mem_neighborFinset] at ha hb ha' hb'
    exact hC4 a b x x' hab ha.1.symm hb.1.symm ha'.1.symm hb'.1.symm

/-- **The exception identity**: `|A₂| + n = |A₀| + 4|H| + σ` (i.e. `|A₂| − |A₀| = 4|H| − s`). -/
theorem exception_identity (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G) :
    (Aset G 2).card + Fintype.card V = (Aset G 0).card + 4 * (Hset G).card + sigma G := by
  obtain ⟨h1, h2⟩ := acount hmin hind hdeg
  have h3 := card_L_add_H hmin
  omega

/-! ## Links -/

/-- `x` shares a hub with `y`. -/
def SharesHub (G : SimpleGraph V) (x y : V) : Prop := ∃ h, 4 ≤ G.degree h ∧ G.Adj x h ∧ G.Adj y h

variable (G) in
/-- The unlinked vertices of `A₁`: every cubic neighbour shares the hub or has `t = 0`. -/
noncomputable abbrev Uset : Finset V :=
  (Aset G 1).filter (fun x => ∀ y, G.Adj x y → G.degree y = 3 → SharesHub G x y ∨ tc G y = 0)

theorem mem_A1 {x : V} (hx : x ∈ Aset G 1) :
    G.degree x = 3 ∧ ∃ h, G.neighborFinset x ∩ Hset G = {h} := by
  simp only [mem_filter, mem_univ, true_and] at hx
  exact ⟨hx.1, card_eq_one.1 hx.2⟩

/-- **The two cubic neighbours of `x ∈ A₁` do not both share its hub.** -/
theorem outer_cubic (hmin : ∀ v, 3 ≤ G.degree v) (hC4 : C4Free G) {x : V}
    (hx : x ∈ Aset G 1) : ∃ y, G.Adj x y ∧ G.degree y = 3 ∧ ¬ SharesHub G x y := by
  obtain ⟨hx3, h, hH⟩ := mem_A1 hx
  have hsplit := card_sdiff_add_card_inter (G.neighborFinset x) (Hset G)
  rw [hH, card_singleton, G.card_neighborFinset_eq_degree, hx3] at hsplit
  obtain ⟨y, z, hyz, hS⟩ := card_eq_two.1 (show (G.neighborFinset x \ Hset G).card = 2 by omega)
  have hy : y ∈ G.neighborFinset x \ Hset G := by rw [hS]; simp
  have hz : z ∈ G.neighborFinset x \ Hset G := by rw [hS]; simp
  simp only [mem_sdiff, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and,
    not_le] at hy hz
  have hy3 : G.degree y = 3 := by have := hmin y; omega
  have hz3 : G.degree z = 3 := by have := hmin z; omega
  have onehub : ∀ w, 4 ≤ G.degree w → G.Adj x w → w = h := by
    intro w hw hxw
    have : w ∈ G.neighborFinset x ∩ Hset G := by simp [hxw, hw]
    rw [hH] at this; simpa using this
  by_contra hall
  push Not at hall
  have sy := hall y hy.1 hy3
  have sz := hall z hz.1 hz3
  obtain ⟨h1, hh1, hx1, hy1⟩ := sy
  obtain ⟨h2, hh2, hx2, hz2⟩ := sz
  rw [onehub h1 hh1 hx1] at hy1
  rw [onehub h2 hh2 hx2] at hz2
  have hxh : x ≠ h := G.ne_of_adj (by rw [← onehub h1 hh1 hx1]; exact hx1)
  exact hyz (hC4 x h y z hxh hy.1 hy1.symm hz.1 hz2.symm)

/-- **Linked**: `x ∈ A₁ ∖ U` has a cubic neighbour `y` with a hub `h'` not adjacent to `x`. -/
theorem linked_of_not_unlinked {x : V} (hx : x ∈ Aset G 1) (hU : x ∉ Uset G) :
    ∃ y h', G.Adj x y ∧ G.degree y = 3 ∧ 4 ≤ G.degree h' ∧ G.Adj y h' ∧ ¬ G.Adj x h' := by
  simp only [Uset, mem_filter, not_and, not_forall] at hU
  obtain ⟨y, hxy, hy3, hno⟩ := hU (by simpa only [mem_filter] using hx)
  push Not at hno
  obtain ⟨hsh, ht⟩ := hno
  have hpos : 0 < tc G y := by omega
  obtain ⟨h', hh'⟩ := card_pos.1 hpos
  simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and] at hh'
  exact ⟨y, h', hxy, hy3, hh'.2, hh'.1, fun hxh => hsh ⟨h', hh'.2, hxh, hh'.1⟩⟩

/-- **`|U| ≤ 3|A₀|`.** -/
theorem unlinked_card (hmin : ∀ v, 3 ≤ G.degree v) (hC4 : C4Free G) :
    (Uset G).card ≤ 3 * (Aset G 0).card := by
  have hone : ∀ x ∈ Uset G, 1 ≤ (G.neighborFinset x ∩ Aset G 0).card := by
    intro x hx
    have hx1 : x ∈ Aset G 1 := (mem_filter.1 hx).1
    obtain ⟨y, hxy, hy3, hsh⟩ := outer_cubic hmin hC4 hx1
    have ht0 : tc G y = 0 := ((mem_filter.1 hx).2 y hxy hy3).resolve_left hsh
    exact card_pos.2 ⟨y, by simp [hxy, hy3, ht0]⟩
  have h1 : (Uset G).card ≤ ∑ x ∈ Uset G, (G.neighborFinset x ∩ Aset G 0).card := by
    rw [card_eq_sum_ones]; exact sum_le_sum hone
  rw [double_count G (Uset G) (Aset G 0)] at h1
  have h2 : ∑ y ∈ Aset G 0, (G.neighborFinset y ∩ Uset G).card ≤ ∑ y ∈ Aset G 0, 3 := by
    apply sum_le_sum; intro y hy
    have hy3 : G.degree y = 3 := by simp only [mem_filter, mem_univ, true_and] at hy; exact hy.1
    rw [← hy3, ← G.card_neighborFinset_eq_degree]; exact card_le_card inter_subset_left
  rw [sum_const, smul_eq_mul] at h2
  omega

/-- The linked neighbours `A₁ ∖ U`. -/
noncomputable abbrev linkedSet (G : SimpleGraph V) : Finset V := Aset G 1 \ Uset G

/-- **Links at a hub.**  `d_h ≤ (|H| − 1) + |N(h) ∩ U| + |N(h) ∩ (A₁ ∖ U)|`. -/
theorem hub_link_count (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G)
    (hC4 : C4Free G) {h : V} (hh : 4 ≤ G.degree h) :
    G.degree h ≤ ((Hset G).card - 1) + (G.neighborFinset h ∩ Uset G).card
      + (G.neighborFinset h ∩ linkedSet G).card := by
  have hhH : h ∈ Hset G := by simp [hh]
  -- every neighbour of `h` is cubic, in `A₁ ∪ A₂`
  have hcover : G.neighborFinset h ⊆ (G.neighborFinset h ∩ Aset G 2) ∪
      ((G.neighborFinset h ∩ Uset G) ∪ (G.neighborFinset h ∩ linkedSet G)) := by
    intro x hx
    have hxh : G.Adj h x := by simpa using hx
    have hx3 := deg_three_of_hub_adj hmin hind hh hxh
    have hxL : x ∈ Lset G := by simp [hx3]
    have hpos : 1 ≤ tc G x := card_pos.2 ⟨h, by simp [hxh.symm, hh]⟩
    have hle := tc_le_two hmin hdeg hxL
    by_cases h2 : tc G x = 2
    · exact mem_union_left _ (mem_inter.2 ⟨hx, mem_filter.2 ⟨hxL, h2⟩⟩)
    · have hA1 : x ∈ Aset G 1 := mem_filter.2 ⟨hxL, by omega⟩
      by_cases hU : x ∈ Uset G
      · exact mem_union_right _ (mem_union_left _ (mem_inter.2 ⟨hx, hU⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_inter.2 ⟨hx, mem_sdiff.2 ⟨hA1, hU⟩⟩))
  -- `|N(h) ∩ A₂| ≤ |H| − 1`
  have hA2 : (G.neighborFinset h ∩ Aset G 2).card ≤ (Hset G).card - 1 := by
    have hsub : G.neighborFinset h ∩ Aset G 2 ⊆
        ((Hset G).erase h).biUnion (fun h' => G.neighborFinset h ∩ G.neighborFinset h') := by
      intro x hx
      simp only [mem_inter, mem_filter, SimpleGraph.mem_neighborFinset] at hx
      obtain ⟨hxh, hxL, h2⟩ := hx
      obtain ⟨a, b, hab, hS⟩ := card_eq_two.1 h2
      have ha : a ∈ G.neighborFinset x ∩ Hset G := by rw [hS]; simp
      have hb : b ∈ G.neighborFinset x ∩ Hset G := by rw [hS]; simp
      simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
        at ha hb
      by_cases hah : a = h
      · refine mem_biUnion.2 ⟨b, mem_erase.2 ⟨fun e => hab (hah.trans e.symm),
          by simp [hb.2]⟩, ?_⟩
        simp [hxh, hb.1.symm]
      · refine mem_biUnion.2 ⟨a, mem_erase.2 ⟨hah, by simp [ha.2]⟩, ?_⟩
        simp [hxh, ha.1.symm]
    calc _ ≤ _ := card_le_card hsub
      _ ≤ ∑ h' ∈ (Hset G).erase h, (G.neighborFinset h ∩ G.neighborFinset h').card :=
          card_biUnion_le
      _ ≤ ∑ h' ∈ (Hset G).erase h, 1 :=
          sum_le_sum (fun h' hh' => codeg_le_one hC4 (Ne.symm (mem_erase.1 hh').1))
      _ = (Hset G).card - 1 := by rw [sum_const, smul_eq_mul, mul_one, card_erase_of_mem hhH]
  have := card_le_card hcover
  rw [G.card_neighborFinset_eq_degree] at this
  have hu1 := card_union_le (G.neighborFinset h ∩ Aset G 2)
    ((G.neighborFinset h ∩ Uset G) ∪ (G.neighborFinset h ∩ linkedSet G))
  have hu2 := card_union_le (G.neighborFinset h ∩ Uset G) (G.neighborFinset h ∩ linkedSet G)
  omega

/-- **`Σ_{h∈H} |N(h) ∩ U| = |U|`** (each vertex of `A₁` has exactly one hub). -/
theorem unlinked_hub_sum :
    ∑ h ∈ Hset G, (G.neighborFinset h ∩ Uset G).card = (Uset G).card := by
  rw [← double_count G (Uset G) (Hset G), card_eq_sum_ones]
  apply sum_congr rfl; intro x hx
  exact (mem_filter.1 (mem_filter.1 hx).1).2

end Hypostructure.Graph.HubLink
