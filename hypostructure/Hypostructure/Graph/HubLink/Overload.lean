import Hypostructure.Graph.JointSystem

/-!
# The centre overload

Vocabulary-free.  In the `JointSystem` setting, the cubic vertices outside `N(c) ∪ {c}` with
a neighbour in `N(c)` number at most `2 d_c` (`into_centre_le`).
-/

open Finset Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Centre overload**: vertices outside `N(c) ∪ {c}` with a neighbour in `N(c)` number
at most `2 d_c`. -/
theorem into_centre_le (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) {c : V}
    (hc : 4 ≤ G.degree c) :
    (univ.filter (fun x => x ≠ c ∧ ¬ G.Adj x c ∧ ∃ y, G.Adj x y ∧ G.Adj y c)).card
      ≤ 2 * G.degree c := by
  set X := univ.filter (fun x => x ≠ c ∧ ¬ G.Adj x c ∧ ∃ y, G.Adj x y ∧ G.Adj y c) with hX
  have h1 : X.card ≤ ∑ x ∈ X, (G.neighborFinset x ∩ G.neighborFinset c).card := by
    rw [card_eq_sum_ones]; apply sum_le_sum; intro x hx
    obtain ⟨-, -, y, hxy, hyc⟩ := (mem_filter.1 hx).2
    exact card_pos.2 ⟨y, by simp [hxy, hyc.symm]⟩
  rw [double_count G X (G.neighborFinset c)] at h1
  have h2 : ∑ y ∈ G.neighborFinset c, (G.neighborFinset y ∩ X).card
      ≤ ∑ y ∈ G.neighborFinset c, 2 := by
    apply sum_le_sum; intro y hy
    have hyc : G.Adj c y := by simpa using hy
    have hy3 := deg_three_of_hub_adj hmin hind hc hyc
    have hsub : G.neighborFinset y ∩ X ⊆ (G.neighborFinset y).erase c := by
      intro x hx
      simp only [mem_inter, hX, mem_filter, mem_univ, true_and] at hx
      exact mem_erase.2 ⟨hx.2.1, hx.1⟩
    have := card_le_card hsub
    rw [card_erase_of_mem (by simpa using hyc.symm), G.card_neighborFinset_eq_degree, hy3]
      at this
    omega
  rw [sum_const, smul_eq_mul, G.card_neighborFinset_eq_degree] at h2
  omega

end Hypostructure.Graph.HubLink
