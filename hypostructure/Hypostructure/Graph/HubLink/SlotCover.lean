import Hypostructure.Graph.HubLink.SlotC8

/-!
# The slot cover with explicit classes

Vocabulary-free.

`MLall`: vertices of `A₁` matched-and-linked at some hub pair `h ≠ c`; `LLall`: vertices of
`A₁` doubly linked at some hub pair `a ≠ b`.

* `slot_cover`: `|A₁| ≤ 3|A₀| + |A₂| + |MLall| + |LLall|`.
* `slot_classes`: `4σ + 15|H| ≤ 3n + 6|A₂| + |MLall| + |LLall|`.
-/

open Finset Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

variable (G) in
noncomputable def MLall : Finset V :=
  (Aset G 1).filter (fun x => ∃ h c, 4 ≤ G.degree h ∧ 4 ≤ G.degree c ∧ h ≠ c ∧ MLat G h c x)

variable (G) in
noncomputable def LLall : Finset V :=
  (Aset G 1).filter (fun x => ∃ a b, 4 ≤ G.degree a ∧ 4 ≤ G.degree b ∧ a ≠ b ∧ LLat G a b x)

theorem slot_cover (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G)
    (hC4 : C4Free G) :
    (Aset G 1).card ≤ 3 * (Aset G 0).card + (Aset G 2).card + (MLall G).card
      + (LLall G).card := by
  set E0 := (Aset G 1).filter (fun x => ∃ w, G.Adj x w ∧ w ∈ Aset G 0) with hE0
  set E2 := (Aset G 1).filter (fun x => ∃ w, G.Adj x w ∧ w ∈ Aset G 2) with hE2
  have hcover : Aset G 1 ⊆ E0 ∪ E2 ∪ MLall G ∪ LLall G := by
    intro x hx
    obtain ⟨hx3, h, hH⟩ := mem_A1 hx
    have hxL : x ∈ Lset G := (mem_filter.1 hx).1
    have hhN : h ∈ G.neighborFinset x ∩ Hset G := by rw [hH]; simp
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      at hhN
    have onehub : ∀ w, 4 ≤ G.degree w → G.Adj x w → w = h := by
      intro w hw hxw
      have : w ∈ G.neighborFinset x ∩ Hset G := by simp [hxw, hw]
      rw [hH] at this; simpa using this
    by_cases hbad : ∃ w, G.Adj x w ∧ G.degree w = 3 ∧ ¬ G.Adj w h ∧ tc G w ≠ 1
    · obtain ⟨w, hxw, hw3, hwh, htw⟩ := hbad
      have hwL : w ∈ Lset G := by simp [hw3]
      have hle := tc_le_two hmin hdeg hwL
      by_cases h0 : tc G w = 0
      · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
        exact mem_filter.2 ⟨hx, w, hxw, mem_filter.2 ⟨hwL, h0⟩⟩
      · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
        exact mem_filter.2 ⟨hx, w, hxw, mem_filter.2 ⟨hwL, by omega⟩⟩
    push Not at hbad
    obtain ⟨z, hxz, hz3, hzs⟩ := outer_cubic hmin hC4 hx
    have hzh : ¬ G.Adj z h := fun e => hzs ⟨h, hhN.2, hhN.1, e⟩
    have tz : tc G z = 1 := hbad z hxz hz3 hzh
    obtain ⟨c, hcS⟩ := card_eq_one.1 tz
    have hcN : c ∈ G.neighborFinset z ∩ Hset G := by rw [hcS]; simp
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      at hcN
    have hch : c ≠ h := fun e => hzh (e ▸ hcN.1)
    by_cases hM : ∃ y, G.Adj x y ∧ G.Adj y h
    · refine mem_union_left _ (mem_union_right _ ?_)
      exact mem_filter.2 ⟨hx, h, c, hhN.2, hcN.2, hch.symm,
        hhN.1, hx3, hM, z, hxz, hcN.1, tz, hz3⟩
    push Not at hM
    have hsplit := card_sdiff_add_card_inter (G.neighborFinset x) (Hset G)
    rw [hH, card_singleton, G.card_neighborFinset_eq_degree, hx3] at hsplit
    obtain ⟨y, hy, hyz⟩ := exists_mem_ne (show 1 < (G.neighborFinset x \ Hset G).card
      by omega) z
    simp only [mem_sdiff, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and,
      not_le] at hy
    have hy3 : G.degree y = 3 := by have := hmin y; omega
    have hyh : ¬ G.Adj y h := hM y hy.1
    have ty : tc G y = 1 := hbad y hy.1 hy3 hyh
    obtain ⟨a, haS⟩ := card_eq_one.1 ty
    have haN : a ∈ G.neighborFinset y ∩ Hset G := by rw [haS]; simp
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      at haN
    have hah : a ≠ h := fun e => hyh (e ▸ haN.1)
    have hac : a ≠ c := by
      intro e; subst e
      exact hyz (hC4 x a y z (ne_deg hx3 haN.2) hy.1 haN.1.symm hxz hcN.1.symm)
    refine mem_union_right _ (mem_filter.2 ⟨hx, a, c, haN.2, hcN.2, hac, hx3,
      fun e => hah (onehub a haN.2 e), fun e => hch (onehub c hcN.2 e),
      y, z, hy.1, hxz, haN.1, hcN.1, ty, tz, hy3, hz3⟩)
  have bE0 : E0.card ≤ 3 * (Aset G 0).card := by
    have h1 : E0.card ≤ ∑ x ∈ E0, (G.neighborFinset x ∩ Aset G 0).card := by
      rw [card_eq_sum_ones]; apply sum_le_sum; intro x hx
      obtain ⟨w, hxw, hw⟩ := (mem_filter.1 hx).2
      exact card_pos.2 ⟨w, by simp [hxw, hw]⟩
    rw [double_count G E0 (Aset G 0)] at h1
    have h2 : ∑ y ∈ Aset G 0, (G.neighborFinset y ∩ E0).card ≤ ∑ y ∈ Aset G 0, 3 := by
      apply sum_le_sum; intro y hy
      have hy3 : G.degree y = 3 := by simp only [mem_filter, mem_univ, true_and] at hy; exact hy.1
      rw [← hy3, ← G.card_neighborFinset_eq_degree]; exact card_le_card inter_subset_left
    rw [sum_const, smul_eq_mul] at h2
    omega
  have bE2 : E2.card ≤ (Aset G 2).card := by
    have h1 : E2.card ≤ ∑ x ∈ E2, (G.neighborFinset x ∩ Aset G 2).card := by
      rw [card_eq_sum_ones]; apply sum_le_sum; intro x hx
      obtain ⟨w, hxw, hw⟩ := (mem_filter.1 hx).2
      exact card_pos.2 ⟨w, by simp [hxw, hw]⟩
    rw [double_count G E2 (Aset G 2)] at h1
    have h2 : ∑ y ∈ Aset G 2, (G.neighborFinset y ∩ E2).card ≤ ∑ y ∈ Aset G 2, 1 := by
      apply sum_le_sum; intro y hy
      rw [← A2_one_cubic hmin hy]
      apply card_le_card; intro w hw
      simp only [mem_inter] at hw ⊢
      exact ⟨hw.1, (mem_filter.1 (mem_filter.1 hw.2).1).1⟩
    rw [sum_const, smul_eq_mul, mul_one] at h2
    omega
  have hc := card_le_card hcover
  have u1 := card_union_le (E0 ∪ E2 ∪ MLall G) (LLall G)
  have u2 := card_union_le (E0 ∪ E2) (MLall G)
  have u3 := card_union_le E0 E2
  omega

/-- **The slot classes**: `4σ + 15|H| ≤ 3n + 6|A₂| + |MLall| + |LLall|`. -/
theorem slot_classes (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G)
    (hC4 : C4Free G) :
    4 * sigma G + 15 * (Hset G).card
      ≤ 3 * Fintype.card V + 6 * (Aset G 2).card + (MLall G).card + (LLall G).card := by
  have hs := slot_cover hmin hind hdeg hC4
  obtain ⟨a1, a2⟩ := acount hmin hind hdeg
  have hL := card_L_add_H hmin
  have hid := exception_identity hmin hind hdeg
  omega

end Hypostructure.Graph.HubLink

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The two hubs of a vertex of `A₂`. -/
theorem A2_hubs {x : V} (hx : x ∈ Aset G 2) :
    x ∈ Lset G ∧ ∃ a b, a ≠ b ∧ a ∈ Hset G ∧ b ∈ Hset G ∧ G.Adj x a ∧ G.Adj x b ∧
      ∀ w ∈ Hset G, G.Adj x w → w = a ∨ w = b := by
  obtain ⟨hxL, h2⟩ := mem_filter.1 hx
  obtain ⟨a, b, hab, hS⟩ := card_eq_two.1 h2
  have ha : a ∈ G.neighborFinset x ∩ Hset G := by rw [hS]; simp
  have hb : b ∈ G.neighborFinset x ∩ Hset G := by rw [hS]; simp
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  refine ⟨hxL, a, b, hab, ha.2, hb.2, ha.1, hb.1, fun w hw hxw => ?_⟩
  have : w ∈ G.neighborFinset x ∩ Hset G := by simp [hxw, hw]
  rw [hS] at this; simpa using this

end Hypostructure.Graph.HubLink

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The hub of a vertex of `A₁`. -/
theorem A1_hub {x : V} (hx : x ∈ Aset G 1) :
    ∃ c, c ∈ Hset G ∧ G.Adj x c ∧ ∀ w ∈ Hset G, G.Adj x w → w = c := by
  obtain ⟨-, c, hH⟩ := mem_A1 hx
  have hc : c ∈ G.neighborFinset x ∩ Hset G := by rw [hH]; simp
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hc
  refine ⟨c, hc.2, hc.1, fun w hw hxw => ?_⟩
  have : w ∈ G.neighborFinset x ∩ Hset G := by simp [hxw, hw]
  rw [hH] at this; simpa using this

theorem mem_LLall {x : V} (hx : x ∈ LLall G) :
    x ∈ Aset G 1 ∧ ∃ a b, a ∈ Hset G ∧ b ∈ Hset G ∧ a ≠ b ∧ LLat G a b x := by
  obtain ⟨hA, a, b, ha, hb, hab, hl⟩ := mem_filter.1 hx
  exact ⟨hA, a, b, by simpa using ha, by simpa using hb, hab, hl⟩

theorem mem_MLall {x : V} (hx : x ∈ MLall G) :
    x ∈ Aset G 1 ∧ ∃ h c, h ∈ Hset G ∧ c ∈ Hset G ∧ h ≠ c ∧ MLat G h c x := by
  obtain ⟨hA, a, b, ha, hb, hab, hl⟩ := mem_filter.1 hx
  exact ⟨hA, a, b, by simpa using ha, by simpa using hb, hab, hl⟩

theorem A1_L {x : V} (hx : x ∈ Aset G 1) : x ∈ Lset G ∧ tc G x = 1 := mem_filter.1 hx

theorem deg3_L {x : V} (hx : G.degree x = 3) : x ∈ Lset G := by simp [hx]

theorem Hset_deg {v : V} (hv : v ∈ Hset G) : 4 ≤ G.degree v := by simpa using hv

end Hypostructure.Graph.HubLink
