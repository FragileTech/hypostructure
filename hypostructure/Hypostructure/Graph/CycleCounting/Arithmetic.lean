import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Degree and surplus arithmetic of pair counts

`Σ_{h∈H} C(d_h, 2)` against `σ = Σ_{h∈H} (d_h − 3)`: the linear bound `5σ`,
the exact Cauchy–Schwarz form, the quadratic cap `16σ²`; the matching count of
adjacent pairs; the heavy centre and the pigeonhole over dyadic exponents.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace Hypostructure.Graph.CycleCounting
open Finset

/-! ## Arithmetic of the per-centre pair counts -/

/-- `C(e+3, 2)` exactly: `2·C(e+3,2) = e² + 5e + 6`. -/
theorem two_mul_choose (e : ℕ) : 2 * (e + 3).choose 2 = e ^ 2 + 5 * e + 6 := by
  rw [Nat.choose_two_right]
  have : 2 ∣ (e + 3) * (e + 3 - 1) := by
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨(k + k + 3) * (k + 1), by rw [show k + k + 3 - 1 = 2 * (k + 1) by omega]; ring⟩
    · exact ⟨(k + 2) * (2 * k + 3), by rw [show 2 * k + 1 + 3 - 1 = 2 * k + 3 by omega]; ring⟩
  rw [Nat.mul_div_cancel' this, show e + 3 - 1 = e + 2 by omega]
  ring

/-- `5(d − 3) ≤ C(d, 2)` for every `d` (equality at `d = 5, 6`): `(e−2)(e−3) ≥ 0`. -/
theorem five_mul_le_choose (d : ℕ) : 5 * (d - 3) ≤ d.choose 2 := by
  by_cases hd : d < 3
  · simp [show d - 3 = 0 by omega]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  have h := two_mul_choose e
  rw [show e + 3 - 3 = e by omega]
  have : 10 * e ≤ e ^ 2 + 5 * e + 6 := by
    rcases Nat.lt_or_ge e 3 with he | he
    · interval_cases e <;> norm_num
    · nlinarith
  omega

variable {ι : Type*} (H : Finset ι) (d : ι → ℕ)

/-- **Convexity bound, linear form**: `Σ_{h∈H} C(d_h,2) ≥ 5σ` with `σ = Σ (d_h − 3)`. -/
theorem five_sigma_le (_ : ∀ h ∈ H, 4 ≤ d h) :
    5 * ∑ h ∈ H, (d h - 3) ≤ ∑ h ∈ H, (d h).choose 2 := by
  rw [mul_sum]
  exact sum_le_sum (fun h _ => five_mul_le_choose (d h))

/-- **Convexity bound, exact Cauchy–Schwarz form**:
`σ² + 5σ|H| + 6|H|² ≤ 2|H| · Σ_{h∈H} C(d_h,2)`, where `σ = Σ (d_h − 3)` and `d_h ≥ 3`. -/
theorem cauchy_choose (hd : ∀ h ∈ H, 3 ≤ d h) :
    (∑ h ∈ H, (d h - 3)) ^ 2 + 5 * (∑ h ∈ H, (d h - 3)) * #H + 6 * #H ^ 2 ≤
      2 * #H * ∑ h ∈ H, (d h).choose 2 := by
  have ex : ∀ h ∈ H, 2 * (d h).choose 2 = (d h - 3) ^ 2 + 5 * (d h - 3) + 6 := by
    intro h hh
    have := two_mul_choose (d h - 3)
    rwa [show d h - 3 + 3 = d h by have := hd h hh; omega] at this
  have sum2 : 2 * ∑ h ∈ H, (d h).choose 2 =
      ∑ h ∈ H, (d h - 3) ^ 2 + 5 * ∑ h ∈ H, (d h - 3) + 6 * #H := by
    rw [mul_sum, sum_congr rfl ex, sum_add_distrib, sum_add_distrib, mul_sum, sum_const,
      smul_eq_mul, mul_comm (#H) 6]
  have cs := sq_sum_le_card_mul_sum_sq (s := H) (f := fun h => d h - 3)
  calc (∑ h ∈ H, (d h - 3)) ^ 2 + 5 * (∑ h ∈ H, (d h - 3)) * #H + 6 * #H ^ 2
      ≤ #H * ∑ h ∈ H, (d h - 3) ^ 2 + 5 * (∑ h ∈ H, (d h - 3)) * #H + 6 * #H ^ 2 := by
        simpa using cs
    _ = #H * (2 * ∑ h ∈ H, (d h).choose 2) := by rw [sum2]; ring
    _ = 2 * #H * ∑ h ∈ H, (d h).choose 2 := by ring

/-- **The forced count is at most quadratic**: `2 Σ C(d_h,2) ≤ (Σ d_h)²`. -/
theorem choose_sum_le_sq : 2 * ∑ h ∈ H, (d h).choose 2 ≤ (∑ h ∈ H, d h) ^ 2 := by
  have step : ∀ h ∈ H, 2 * (d h).choose 2 ≤ d h ^ 2 := by
    intro h _
    rw [Nat.choose_two_right]
    have := Nat.mul_div_le (d h * (d h - 1)) 2
    have : d h * (d h - 1) ≤ d h ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  calc 2 * ∑ h ∈ H, (d h).choose 2 = ∑ h ∈ H, 2 * (d h).choose 2 := mul_sum _ _ _
    _ ≤ ∑ h ∈ H, d h ^ 2 := sum_le_sum step
    _ ≤ (∑ h ∈ H, d h) ^ 2 := by
      simpa using (sum_sq_le_sq_sum_of_nonneg (s := H) (f := d) (fun _ _ => Nat.zero_le _))

/-- With `Σ d_h = 3|H| + σ` and `|H| ≤ σ`: `2 Σ C(d_h,2) ≤ 16 σ²`. -/
theorem choose_sum_le_sigma (hd : ∀ h ∈ H, 4 ≤ d h) :
    2 * ∑ h ∈ H, (d h).choose 2 ≤ 16 * (∑ h ∈ H, (d h - 3)) ^ 2 := by
  have hs : ∑ h ∈ H, d h ≤ 4 * ∑ h ∈ H, (d h - 3) := by
    rw [mul_sum]; exact sum_le_sum (fun h hh => by have := hd h hh; omega)
  calc 2 * ∑ h ∈ H, (d h).choose 2 ≤ (∑ h ∈ H, d h) ^ 2 := choose_sum_le_sq H d
    _ ≤ (4 * ∑ h ∈ H, (d h - 3)) ^ 2 := Nat.pow_le_pow_left hs 2
    _ = 16 * (∑ h ∈ H, (d h - 3)) ^ 2 := by ring

end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacent 2-subsets of `N`. -/
def adjPairs (N : Finset V) : Finset (Finset V) :=
  (N.powersetCard 2).filter (fun T => ∃ x ∈ T, ∃ y ∈ T, G.Adj x y)

/-- Non-adjacent 2-subsets of `N` (the same-vertex switch pairs when `N = N(h)`). -/
def nonAdjPairs (N : Finset V) : Finset (Finset V) :=
  (N.powersetCard 2).filter (fun T => ¬ ∃ x ∈ T, ∃ y ∈ T, G.Adj x y)

variable {G}

theorem adjPairs_shape {N T : Finset V} (hT : T ∈ adjPairs G N) {v : V} (hv : v ∈ T) :
    ∃ u, G.Adj v u ∧ T = {v, u} := by
  simp only [adjPairs, mem_filter, mem_powersetCard] at hT
  obtain ⟨⟨-, c2⟩, x, hx, y, hy, a⟩ := hT
  have eq : T = {x, y} := by
    symm
    apply eq_of_subset_of_card_le
    · intro w hw; rw [mem_insert, mem_singleton] at hw; rcases hw with rfl | rfl <;> assumption
    · rw [c2, card_pair a.ne]
  rw [eq, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨y, a, eq⟩
  · exact ⟨x, a.symm, eq.trans (pair_comm _ _)⟩

/-- **Matching count.** If `G[N]` is a matching, `2·#(adjacent pairs in N) ≤ #N`. -/
theorem two_mul_card_adjPairs_le (N : Finset V)
    (matching : ∀ x ∈ N, ∀ y ∈ N, ∀ z ∈ N, G.Adj x y → G.Adj x z → y = z) :
    2 * #(adjPairs G N) ≤ #N := by
  have disj : (adjPairs G N : Set (Finset V)).PairwiseDisjoint id := by
    intro T₁ h₁ T₂ h₂ ne
    rw [Function.onFun, id, id, disjoint_left]
    intro v v₁ v₂
    obtain ⟨u₁, a₁, e₁⟩ := adjPairs_shape h₁ v₁
    obtain ⟨u₂, a₂, e₂⟩ := adjPairs_shape h₂ v₂
    have sub : ∀ {T}, T ∈ adjPairs G N → T ⊆ N := fun hT =>
      (mem_powersetCard.1 (mem_filter.1 hT).1).1
    have vN := sub h₁ v₁
    have u₁N := sub h₁ (e₁ ▸ mem_insert_of_mem (mem_singleton_self u₁))
    have u₂N := sub h₂ (e₂ ▸ mem_insert_of_mem (mem_singleton_self u₂))
    exact ne (e₁.trans ((matching v vN u₁ u₁N u₂ u₂N a₁ a₂) ▸ e₂.symm))
  have card := card_biUnion (s := adjPairs G N) (t := id) (fun T₁ h₁ T₂ h₂ ne => disj h₁ h₂ ne)
  have two : ∀ T ∈ adjPairs G N, #(id T) = 2 := fun T hT =>
    (mem_powersetCard.1 (mem_filter.1 hT).1).2
  rw [sum_congr rfl two, sum_const, smul_eq_mul] at card
  have sub : (adjPairs G N).biUnion id ⊆ N := by
    intro v hv
    obtain ⟨T, hT, vT⟩ := mem_biUnion.1 hv
    exact (mem_powersetCard.1 (mem_filter.1 hT).1).1 vT
  have := card_le_card sub
  omega

/-- **Non-adjacent pair count**: `#nonAdjPairs + #adjPairs = C(#N, 2)`, so with a matching
`#nonAdjPairs ≥ C(#N,2) − ⌊#N/2⌋`. -/
theorem card_nonAdjPairs (N : Finset V)
    (matching : ∀ x ∈ N, ∀ y ∈ N, ∀ z ∈ N, G.Adj x y → G.Adj x z → y = z) :
    (#N).choose 2 - #N / 2 ≤ #(nonAdjPairs G N) := by
  have split := card_filter_add_card_filter_not
    (s := N.powersetCard 2) (fun T => ∃ x ∈ T, ∃ y ∈ T, G.Adj x y)
  rw [card_powersetCard] at split
  have := two_mul_card_adjPairs_le N matching
  change #(adjPairs G N) + #(nonAdjPairs G N) = _ at split
  omega

end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

/-! ## Single-centre pigeonhole: the exact comparison -/

/-- **Heavy centre.** Some `h ∈ H` has `σ ≤ |H| · (d_h − 3)`, i.e. `d_h ≥ 3 + σ/|H|`. -/
theorem exists_heavy {ι : Type*} (H : Finset ι) (hH : H.Nonempty) (d : ι → ℕ) :
    ∃ h ∈ H, ∑ i ∈ H, (d i - 3) ≤ #H * (d h - 3) := by
  apply exists_le_of_sum_le hH
  rw [sum_const, smul_eq_mul, ← mul_sum]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Partners at `x`.** With `G[N(h)]` a matching (`x` has at most one neighbour in `N`),
`x` has at least `|N| − 2` non-adjacent partners in `N`. -/
theorem partners_card (N : Finset V) {x : V} (hx : x ∈ N)
    (match1 : #(N.filter (G.Adj x)) ≤ 1) :
    #N - 2 ≤ #((N.erase x).filter (fun y => ¬ G.Adj x y)) := by
  have split := card_filter_add_card_filter_not (s := N.erase x) (G.Adj x)
  rw [card_erase_of_mem hx] at split
  have : #((N.erase x).filter (G.Adj x)) ≤ #(N.filter (G.Adj x)) :=
    card_le_card (filter_subset_filter _ (erase_subset _ _))
  omega

/-- The forced lengths `2^j + 1 ≤ n` give `j ≤ log₂ n`. -/
theorem j_le_log {j n : ℕ} (h : 2 ^ j + 1 ≤ n) : j ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- **Pigeonhole over `j`.** Partners `A` labelled by `j ∈ Js` have a label class of size at
least `#A / #Js`. -/
theorem pigeonhole_j (A : Finset V) (Js : Finset ℕ) (hJ : Js.Nonempty) (jOf : V → ℕ)
    (maps : ∀ a ∈ A, jOf a ∈ Js) :
    ∃ j ∈ Js, #A / #Js ≤ #(A.filter (fun a => jOf a = j)) :=
  exists_le_card_fiber_of_mul_le_card_of_maps_to maps hJ (Nat.mul_div_le _ _)


end Hypostructure.Graph.CycleCounting
