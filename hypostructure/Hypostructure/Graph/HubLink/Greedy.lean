import Hypostructure.Graph.HubLink.Rainbow

/-!
# Greedy labelled paths

Vocabulary-free.

`Lk h h' b` a labelled relation with `cap` (`≤ M` partners of `h` through one label `b`), and a
forbid map `F` (`|F b| ≤ f`).  A **`k`-path** in `T` (`FPath`): hubs `h 0, …, h k` of `T`,
pairwise distinct, `Lk (h i) (h (i+1)) (b i)`, every later label outside `F` of every earlier
one.

* `greedy_path`: if every `h ∈ T` has `≥ m(1 + fM) + 1` partners in `T`, every `k ≤ m + 1`
  has a `k`-path.
* `greedy_degenerate`: without `(m+1)`-paths in `S`, every nonempty `T ⊆ S` has a hub with at
  most `m(1 + fM)` partners in `T`.
-/

open Finset Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

variable {ι β : Type*} [Fintype ι] [Nonempty β]

/-- A `k`-path of `Lk` in `T` avoiding `F`. -/
def FPath (Lk : ι → ι → β → Prop) (F : β → Finset β) (T : Finset ι) (k : ℕ)
    (h : ℕ → ι) (b : ℕ → β) : Prop :=
  (∀ i ≤ k, h i ∈ T) ∧ (∀ i ≤ k, ∀ j ≤ k, h i = h j → i = j) ∧
    (∀ i < k, Lk (h i) (h (i + 1)) (b i)) ∧ (∀ i < k, ∀ j < i, b i ∉ F (b j))

theorem greedy_path (Lk : ι → ι → β → Prop) (M f : ℕ)
    (cap : ∀ h b, (univ.filter (fun h' => Lk h h' b)).card ≤ M)
    (F : β → Finset β) (hFc : ∀ b, (F b).card ≤ f)
    (T : Finset ι) (hT : T.Nonempty) (m : ℕ)
    (hdeg : ∀ h ∈ T, m * (1 + f * M) + 1 ≤ (part Lk T h).card) :
    ∀ k ≤ m + 1, ∃ h b, FPath Lk F T k h b := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨h0, m0⟩ := hT
    refine ⟨fun _ => h0, fun _ => Classical.arbitrary β, ?_, ?_, ?_, ?_⟩
    · intro i _; exact m0
    · intro i hi j hj _; omega
    · intro i hi; omega
    · intro i hi; omega
  | succ k ih =>
    intro hk
    obtain ⟨h, b, hT', hinj, hl, hav⟩ := ih (by omega)
    set X := (range k).image h with hX
    set U := (range k).biUnion (fun j => F (b j)) with hU
    have cX : X.card ≤ k := card_image_le.trans (by simp)
    have cU : U.card ≤ k * f := by
      calc U.card ≤ ∑ j ∈ range k, (F (b j)).card := card_biUnion_le
        _ ≤ ∑ j ∈ range k, f := sum_le_sum (fun j _ => hFc _)
        _ = k * f := by simp
    have hd := hdeg (h k) (hT' k le_rfl)
    have hkm : k ≤ m := by omega
    have e1 : X.card + U.card * M ≤ k * (1 + f * M) := by
      have := Nat.mul_le_mul_right M cU
      nlinarith
    have e2 : k * (1 + f * M) ≤ m * (1 + f * M) := Nat.mul_le_mul_right _ hkm
    obtain ⟨h', mh', nh', nX, b', nU, lk⟩ :=
      extend Lk M cap T (h k) X U (by omega)
    have nX' : ∀ j < k, h' ≠ h j := fun j hj e => nX (mem_image.2 ⟨j, mem_range.2 hj, e.symm⟩)
    have nU' : ∀ j < k, b' ∉ F (b j) := fun j hj hm => nU (mem_biUnion.2 ⟨j, mem_range.2 hj, hm⟩)
    refine ⟨fun i => if i = k + 1 then h' else h i, fun i => if i = k then b' else b i,
      ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases e : i = k + 1
      · simp [e, mh']
      · simp only [e, if_false]; exact hT' i (by omega)
    · intro i hi j hj e
      by_cases ei : i = k + 1 <;> by_cases ej : j = k + 1 <;>
        simp only [ei, ej, if_true, if_false] at e
      · omega
      · exfalso
        by_cases ejk : j = k
        · subst ejk; exact nh' e
        · exact nX' j (by omega) e
      · exfalso
        by_cases eik : i = k
        · subst eik; exact nh' e.symm
        · exact nX' i (by omega) e.symm
      · exact hinj i (by omega) j (by omega) e
    · intro i hi
      by_cases ei : i = k
      · subst ei; simpa using lk
      · have hi' : i < k := by omega
        simp only [show i ≠ k + 1 by omega, show i + 1 ≠ k + 1 by omega, ei, if_false]
        exact hl i hi'
    · intro i hi j hj
      have ej : j ≠ k := by omega
      by_cases ei : i = k
      · subst ei; simp only [if_true, ej, if_false]; exact nU' j hj
      · simp only [ei, ej, if_false]; exact hav i (by omega) j hj

/-- **Greedy degeneracy.** -/
theorem greedy_degenerate (Lk : ι → ι → β → Prop) (M f : ℕ)
    (cap : ∀ h b, (univ.filter (fun h' => Lk h h' b)).card ≤ M)
    (F : β → Finset β) (hFc : ∀ b, (F b).card ≤ f) (S : Finset ι) (m : ℕ)
    (hno : ∀ h b, ¬ FPath Lk F S (m + 1) h b) :
    ∀ T ⊆ S, T.Nonempty → ∃ h ∈ T, (part Lk T h).card ≤ m * (1 + f * M) := by
  intro T hTS hT
  by_contra hall
  push Not at hall
  obtain ⟨h, b, p1, p2, p3, p4⟩ :=
    greedy_path Lk M f cap F hFc T hT m (fun h hh => hall h hh) (m + 1) le_rfl
  exact hno h b ⟨fun i hi => hTS (p1 i hi), p2, p3, p4⟩

end Hypostructure.Graph.HubLink
