import Mathlib

/-!
# Counting marked pairs

Vocabulary-free.

A family of 2-sets `{p,q}` of a finite set `P` each of which has a "marked"
element or an element whose centre `c p` lies in the other's support `T q`
has at most `|marked|·|P| + Σ_{q∈P} Σ_{v∈T q} |c⁻¹(v) ∩ P|` members.
-/

namespace Hypostructure.Graph.PairCount

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem card_pairs_le (P : Finset α) (c : α → β) (T : α → Finset β)
    (mark : α → Prop) [DecidablePred mark] (F : Finset (Finset α))
    (hF : ∀ pair ∈ F, ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ pair = {p, q} ∧
      (mark p ∨ mark q ∨ c p ∈ T q ∨ c q ∈ T p)) :
    F.card ≤ (P.filter mark).card * P.card +
      ∑ q ∈ P, ∑ v ∈ T q, (P.filter fun p => c p = v).card := by
  classical
  let S : Finset (α × α) := (P ×ˢ P).filter fun x => c x.1 ∈ T x.2
  let g : α × α → Finset α := fun x => {x.1, x.2}
  have sub : F ⊆ ((P.filter mark) ×ˢ P).image g ∪ S.image g := by
    intro pair hpair
    obtain ⟨p, hp, q, hq, -, rfl, h⟩ := hF pair hpair
    rcases h with h | h | h | h
    · exact mem_union_left _ (mem_image.2 ⟨(p, q), by simp [hp, hq, h], rfl⟩)
    · exact mem_union_left _ (mem_image.2 ⟨(q, p), by simp [hp, hq, h], by simp [g, pair_comm]⟩)
    · exact mem_union_right _ (mem_image.2 ⟨(p, q), by simp [S, hp, hq, h], rfl⟩)
    · exact mem_union_right _ (mem_image.2 ⟨(q, p), by simp [S, hp, hq, h], by simp [g, pair_comm]⟩)
  have hS : S.card ≤ ∑ q ∈ P, ∑ v ∈ T q, (P.filter fun p => c p = v).card := by
    have : S.card = ∑ q ∈ P, (P.filter fun p => c p ∈ T q).card := by
      rw [show S = P.biUnion (fun q => (P.filter fun p => c p ∈ T q).image (fun p => (p, q))) by
        ext ⟨a, b⟩; simp [S]; tauto]
      rw [card_biUnion]
      · refine sum_congr rfl fun q _ => card_image_of_injective _ ?_
        intro a b h; simpa using h
      · intro x _ y _ hxy
        rw [Function.onFun, disjoint_left]
        intro z hz hz'
        simp only [mem_image, mem_filter] at hz hz'
        obtain ⟨a, -, rfl⟩ := hz
        obtain ⟨b, -, hb⟩ := hz'
        simp at hb
        exact hxy hb.2.symm
    rw [this]
    refine sum_le_sum fun q _ => ?_
    calc (P.filter fun p => c p ∈ T q).card
        = ((T q).biUnion fun v => P.filter fun p => c p = v).card := by
          congr 1; ext p; simp; tauto
      _ ≤ ∑ v ∈ T q, (P.filter fun p => c p = v).card := card_biUnion_le
  calc F.card ≤ (((P.filter mark) ×ˢ P).image g ∪ S.image g).card := card_le_card sub
    _ ≤ (((P.filter mark) ×ˢ P).image g).card + (S.image g).card := card_union_le _ _
    _ ≤ ((P.filter mark) ×ˢ P).card + S.card := add_le_add card_image_le card_image_le
    _ ≤ _ := by rw [card_product]; omega

end Hypostructure.Graph.PairCount
