import Hypostructure.Graph.CapacityFreeSide.SeparatedCharge

/-!
# Congestion versus separation

`|pairs of P| ≤ Σ_v C(d_D(v),2) + Σ_v C(d_R(v),2) + |Sep|`, where
`d_X(v) = #{p ∈ P : v ∈ X(p)}` and `Sep` = pairs with disjoint `D` and disjoint `R`.
-/

namespace Hypostructure.Graph.PairCount

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pairs whose `X`-sets meet number at most `Σ_{v∈V} C(d_X(v), 2)`. -/
theorem card_meeting_pairs_le (P : Finset α) (X : α → Finset β) (V : Finset β)
    (hV : ∀ p ∈ P, X p ⊆ V) :
    ((P.powersetCard 2).filter fun pr => ∃ p ∈ pr, ∃ q ∈ pr, p ≠ q ∧ ¬ Disjoint (X p) (X q)).card ≤
      ∑ v ∈ V, ((P.filter fun p => v ∈ X p).card).choose 2 := by
  classical
  calc _ ≤ (V.biUnion fun v => (P.filter fun p => v ∈ X p).powersetCard 2).card := by
        apply card_le_card
        intro pr hpr
        simp only [mem_filter, mem_powersetCard] at hpr
        obtain ⟨⟨hsub, hcard⟩, p, hp, q, hq, hpq, hmeet⟩ := hpr
        obtain ⟨v, hvp, hvq⟩ := Finset.not_disjoint_iff.1 hmeet
        refine mem_biUnion.2 ⟨v, hV p (hsub hp) hvp, mem_powersetCard.2 ⟨?_, hcard⟩⟩
        intro x hx
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
        have hpq' : p ∈ ({a, b} : Finset α) := hp
        simp only [mem_insert, mem_singleton] at hx hp hq
        refine mem_filter.2 ⟨hsub (by simp [hx]), ?_⟩
        rcases hx with rfl | rfl <;> rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
          first | exact hvp | exact hvq | exact (hpq rfl).elim
    _ ≤ ∑ v ∈ V, ((P.filter fun p => v ∈ X p).powersetCard 2).card := card_biUnion_le
    _ = _ := by simp [card_powersetCard]

end Hypostructure.Graph.PairCount
