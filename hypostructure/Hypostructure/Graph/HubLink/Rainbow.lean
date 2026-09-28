import Mathlib

/-!
# Rainbow paths in a bag-labelled relation

Vocabulary-free.

`Lk h h' b`: "`h` is linked to `h'` through bag `b`".  `cap`: through one bag, a hub has at
most `M` partners.  Partners of `h` inside `T`: `part Lk T h`.

* `rainbow5`: if every `h ∈ T` has `≥ 3M + 4` partners in `T`, there is a path
  `h₁ h₂ h₃ h₄ h₅` of distinct hubs of `T` linked through 4 distinct bags.
* `strong_rainbow5`: the same when every `h ∈ T` has `≥ 4` *strong* partners in `T`
  (linked through `≥ 4` distinct bags).
* `degenerate_sum`: a symmetric relation all of whose nonempty subsets `T ⊆ S` have a member
  with `≤ d` partners in `T` has `Σ_{h∈S} #partners_S(h) ≤ 2d|S|`.
-/

open Finset Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

variable {ι β : Type*} [Fintype ι]

/-- Partners of `h` inside `T`. -/
noncomputable def part (Lk : ι → ι → β → Prop) (T : Finset ι) (h : ι) : Finset ι :=
  T.filter (fun h' => h' ≠ h ∧ ∃ b, Lk h h' b)

/-- Strong link: linked through at least 4 distinct bags. -/
def SLk (Lk : ι → ι → β → Prop) (h h' : ι) : Prop :=
  ∃ B : Finset β, 4 ≤ B.card ∧ ∀ b ∈ B, Lk h h' b

/-- Strong partners of `h` inside `T`. -/
noncomputable def spart (Lk : ι → ι → β → Prop) (T : Finset ι) (h : ι) : Finset ι :=
  T.filter (fun h' => h' ≠ h ∧ SLk Lk h h')

/-- A path of 5 distinct hubs of `T` linked consecutively through 4 distinct bags. -/
def Rainbow5 (Lk : ι → ι → β → Prop) (T : Finset ι) : Prop :=
  ∃ h₁ h₂ h₃ h₄ h₅ : ι, ∃ b₁ b₂ b₃ b₄ : β,
    h₁ ∈ T ∧ h₂ ∈ T ∧ h₃ ∈ T ∧ h₄ ∈ T ∧ h₅ ∈ T ∧
    h₁ ≠ h₂ ∧ h₁ ≠ h₃ ∧ h₁ ≠ h₄ ∧ h₁ ≠ h₅ ∧ h₂ ≠ h₃ ∧ h₂ ≠ h₄ ∧ h₂ ≠ h₅ ∧
    h₃ ≠ h₄ ∧ h₃ ≠ h₅ ∧ h₄ ≠ h₅ ∧
    b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₃ ≠ b₄ ∧
    Lk h₁ h₂ b₁ ∧ Lk h₂ h₃ b₂ ∧ Lk h₃ h₄ b₃ ∧ Lk h₄ h₅ b₄

theorem Rainbow5.mono {Lk : ι → ι → β → Prop} {T S : Finset ι} (hTS : T ⊆ S)
    (h : Rainbow5 Lk T) : Rainbow5 Lk S := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, b₁, b₂, b₃, b₄, m1, m2, m3, m4, m5, rest⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, h₅, b₁, b₂, b₃, b₄, hTS m1, hTS m2, hTS m3, hTS m4, hTS m5, rest⟩

/-- **One greedy step**: more partners than `|X| + |U| M` give a partner outside `X`
linked through a bag outside `U`. -/
theorem extend (Lk : ι → ι → β → Prop) (M : ℕ)
    (cap : ∀ h b, (univ.filter (fun h' => Lk h h' b)).card ≤ M)
    (T : Finset ι) (h : ι) (X : Finset ι) (U : Finset β)
    (hc : X.card + U.card * M < (part Lk T h).card) :
    ∃ h' ∈ T, h' ≠ h ∧ h' ∉ X ∧ ∃ b, b ∉ U ∧ Lk h h' b := by
  set B := U.biUnion (fun b => univ.filter (fun h' => Lk h h' b)) with hBdef
  have hB : B.card ≤ U.card * M := by
    calc B.card ≤ ∑ b ∈ U, (univ.filter (fun h' => Lk h h' b)).card := card_biUnion_le
      _ ≤ ∑ b ∈ U, M := sum_le_sum (fun b _ => cap h b)
      _ = U.card * M := by rw [sum_const, smul_eq_mul]
  have h1 := card_le_card_sdiff_add_card (s := part Lk T h) (t := X)
  have h2 := card_le_card_sdiff_add_card (s := part Lk T h \ X) (t := B)
  have hne : ((part Lk T h \ X) \ B).Nonempty := by
    rw [← card_pos]; omega
  obtain ⟨h', hh'⟩ := hne
  simp only [mem_sdiff, part, mem_filter] at hh'
  obtain ⟨⟨⟨hT, hne', b0, hb0⟩, hX⟩, hBn⟩ := hh'
  refine ⟨h', hT, hne', hX, b0, fun hU => hBn ?_, hb0⟩
  rw [hBdef, mem_biUnion]
  exact ⟨b0, hU, by simp [hb0]⟩

theorem card_two_le {α : Type*} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 2 :=
  (card_insert_le _ _).trans (by simp)

theorem card_three_le {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  (card_insert_le _ _).trans (by have := card_two_le b c; omega)

/-- **Rainbow path from partner degree `≥ 3M + 4`.** -/
theorem rainbow5 (Lk : ι → ι → β → Prop) (M : ℕ)
    (cap : ∀ h b, (univ.filter (fun h' => Lk h h' b)).card ≤ M)
    (T : Finset ι) (hT : T.Nonempty) (hdeg : ∀ h ∈ T, 3 * M + 4 ≤ (part Lk T h).card) :
    Rainbow5 Lk T := by
  obtain ⟨h₁, m1⟩ := hT
  obtain ⟨h₂, m2, n21, -, b₁, -, l1⟩ := extend Lk M cap T h₁ ∅ ∅
    (by have := hdeg h₁ m1; simp only [card_empty, zero_mul, add_zero]; omega)
  obtain ⟨h₃, m3, n32, n31, b₂, nb21, l2⟩ := extend Lk M cap T h₂ {h₁} {b₁}
    (by have := hdeg h₂ m2; simp only [card_singleton, one_mul]; omega)
  obtain ⟨h₄, m4, n43, n4X, b₃, nb3U, l3⟩ := extend Lk M cap T h₃ {h₁, h₂} {b₁, b₂}
    (by
      have := hdeg h₃ m3
      have c1 := card_two_le h₁ h₂
      have c2 := card_two_le b₁ b₂
      have c3 := Nat.mul_le_mul_right M c2
      omega)
  obtain ⟨h₅, m5, n54, n5X, b₄, nb4U, l4⟩ := extend Lk M cap T h₄ {h₁, h₂, h₃} {b₁, b₂, b₃}
    (by
      have := hdeg h₄ m4
      have c1 := card_three_le h₁ h₂ h₃
      have c2 := card_three_le b₁ b₂ b₃
      have c3 := Nat.mul_le_mul_right M c2
      omega)
  simp only [mem_singleton, mem_insert, not_or] at n31 nb21 n4X nb3U n5X nb4U
  exact ⟨h₁, h₂, h₃, h₄, h₅, b₁, b₂, b₃, b₄, m1, m2, m3, m4, m5,
    Ne.symm n21, Ne.symm n31, Ne.symm n4X.1, Ne.symm n5X.1, Ne.symm n32, Ne.symm n4X.2,
    Ne.symm n5X.2.1, Ne.symm n43, Ne.symm n5X.2.2, Ne.symm n54,
    Ne.symm nb21, Ne.symm nb3U.1, Ne.symm nb4U.1, Ne.symm nb3U.2, Ne.symm nb4U.2.1,
    Ne.symm nb4U.2.2, l1, l2, l3, l4⟩

/-- **Partner degeneracy.**  Without a rainbow path in `S`, every nonempty `T ⊆ S` has a hub
with at most `3M + 3` partners in `T`. -/
theorem part_degenerate (Lk : ι → ι → β → Prop) (M : ℕ)
    (cap : ∀ h b, (univ.filter (fun h' => Lk h h' b)).card ≤ M)
    (S : Finset ι) (hno : ¬ Rainbow5 Lk S) :
    ∀ T ⊆ S, T.Nonempty → ∃ h ∈ T, (part Lk T h).card ≤ 3 * M + 3 := by
  intro T hTS hT
  by_contra hall
  push Not at hall
  exact hno ((rainbow5 Lk M cap T hT (fun h hh => hall h hh)).mono hTS)

/-- **Strong partners of degree `≥ 4` give a rainbow path.** -/
theorem strong_rainbow5 (Lk : ι → ι → β → Prop) (T : Finset ι) (hT : T.Nonempty)
    (hdeg : ∀ h ∈ T, 4 ≤ (spart Lk T h).card) : Rainbow5 Lk T := by
  have step : ∀ h ∈ T, ∀ X : Finset ι, X.card ≤ 3 →
      ∃ h' ∈ T, h' ≠ h ∧ h' ∉ X ∧ SLk Lk h h' := by
    intro h hh X hX
    have h1 := card_le_card_sdiff_add_card (s := spart Lk T h) (t := X)
    have := hdeg h hh
    have hne : (spart Lk T h \ X).Nonempty := by rw [← card_pos]; omega
    obtain ⟨h', hh'⟩ := hne
    simp only [mem_sdiff, spart, mem_filter] at hh'
    exact ⟨h', hh'.1.1, hh'.1.2.1, hh'.2, hh'.1.2.2⟩
  have pick : ∀ (B : Finset β) (U : Finset β), U.card ≤ 3 → 4 ≤ B.card →
      ∃ b ∈ B, b ∉ U := by
    intro B U hU hB
    have h1 := card_le_card_sdiff_add_card (s := B) (t := U)
    have hne : (B \ U).Nonempty := by rw [← card_pos]; omega
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, (mem_sdiff.1 hb).1, (mem_sdiff.1 hb).2⟩
  obtain ⟨h₁, m1⟩ := hT
  obtain ⟨h₂, m2, n21, -, s1⟩ := step h₁ m1 ∅ (by simp)
  obtain ⟨h₃, m3, n32, n31, s2⟩ := step h₂ m2 {h₁} (by simp)
  obtain ⟨h₄, m4, n43, n4X, s3⟩ := step h₃ m3 {h₁, h₂} (by have := card_two_le h₁ h₂; omega)
  obtain ⟨h₅, m5, n54, n5X, s4⟩ := step h₄ m4 {h₁, h₂, h₃}
    (by have := card_three_le h₁ h₂ h₃; omega)
  obtain ⟨B1, c1, l1⟩ := s1
  obtain ⟨B2, c2, l2⟩ := s2
  obtain ⟨B3, c3, l3⟩ := s3
  obtain ⟨B4, c4, l4⟩ := s4
  obtain ⟨b₁, hb1, -⟩ := pick B1 ∅ (by simp) c1
  obtain ⟨b₂, hb2, nb2⟩ := pick B2 {b₁} (by simp) c2
  obtain ⟨b₃, hb3, nb3⟩ := pick B3 {b₁, b₂} (by have := card_two_le b₁ b₂; omega) c3
  obtain ⟨b₄, hb4, nb4⟩ := pick B4 {b₁, b₂, b₃} (by have := card_three_le b₁ b₂ b₃; omega) c4
  simp only [mem_singleton, mem_insert, not_or] at n31 n4X n5X nb2 nb3 nb4
  exact ⟨h₁, h₂, h₃, h₄, h₅, b₁, b₂, b₃, b₄, m1, m2, m3, m4, m5,
    Ne.symm n21, Ne.symm n31, Ne.symm n4X.1, Ne.symm n5X.1, Ne.symm n32, Ne.symm n4X.2,
    Ne.symm n5X.2.1, Ne.symm n43, Ne.symm n5X.2.2, Ne.symm n54,
    Ne.symm nb2, Ne.symm nb3.1, Ne.symm nb4.1, Ne.symm nb3.2, Ne.symm nb4.2.1,
    Ne.symm nb4.2.2, l1 b₁ hb1, l2 b₂ hb2, l3 b₃ hb3, l4 b₄ hb4⟩

/-- **Strong degeneracy.**  Without a rainbow path in `S`, every nonempty `T ⊆ S` has a hub
with at most 3 strong partners in `T`. -/
theorem spart_degenerate (Lk : ι → ι → β → Prop) (S : Finset ι) (hno : ¬ Rainbow5 Lk S) :
    ∀ T ⊆ S, T.Nonempty → ∃ h ∈ T, (spart Lk T h).card ≤ 3 := by
  intro T hTS hT
  by_contra hall
  push Not at hall
  exact hno ((strong_rainbow5 Lk T hT (fun h hh => hall h hh)).mono hTS)

/-- **Degenerate ⇒ few partner pairs**: `Σ_{h∈S} #partners_S(h) ≤ 2d|S|`. -/
theorem degenerate_sum (P : ι → ι → Prop) (hsym : ∀ a b, P a b → P b a) (d : ℕ) :
    ∀ S : Finset ι,
      (∀ T ⊆ S, T.Nonempty → ∃ h ∈ T, (T.filter (fun h' => h' ≠ h ∧ P h h')).card ≤ d) →
      ∑ h ∈ S, (S.filter (fun h' => h' ≠ h ∧ P h h')).card ≤ 2 * d * S.card := by
  intro S
  induction hn : S.card generalizing S with
  | zero =>
    intro _
    rw [card_eq_zero.1 hn]; simp
  | succ n ih =>
    intro hdeg
    have hSne : S.Nonempty := by rw [← card_pos]; omega
    obtain ⟨v, hv, hvd⟩ := hdeg S subset_rfl hSne
    set S' := S.erase v with hS'
    have hS'c : S'.card = n := by rw [hS', card_erase_of_mem hv]; omega
    have hdeg' : ∀ T ⊆ S', T.Nonempty →
        ∃ h ∈ T, (T.filter (fun h' => h' ≠ h ∧ P h h')).card ≤ d :=
      fun T hT hne => hdeg T (hT.trans (erase_subset v S)) hne
    have ih' := ih S' hS'c hdeg'
    have hins : S = insert v S' := (insert_erase hv).symm
    have hvS' : v ∉ S' := notMem_erase v S
    -- degree in S of h ∈ S' = degree in S' + [P h v]
    have hsplit : ∀ h ∈ S', (S.filter (fun h' => h' ≠ h ∧ P h h')).card
        = (S'.filter (fun h' => h' ≠ h ∧ P h h')).card + (if P h v then 1 else 0) := by
      intro h hh
      have hvh : v ≠ h := fun e => hvS' (e ▸ hh)
      conv_lhs => rw [hins]
      rw [filter_insert]
      by_cases hp : P h v
      · rw [if_pos ⟨hvh, hp⟩, if_pos hp, card_insert_of_notMem (fun hm => hvS' (mem_filter.1 hm).1)]
      · rw [if_neg (fun hc => hp hc.2), if_neg hp, add_zero]
    have hvdeg : (S.filter (fun h' => h' ≠ v ∧ P v h')).card = (S'.filter (fun h => P h v)).card := by
      congr 1
      ext h
      simp only [mem_filter, hS', mem_erase]
      constructor
      · rintro ⟨hS, hne, hp⟩; exact ⟨⟨hne, hS⟩, hsym _ _ hp⟩
      · rintro ⟨⟨hne, hS⟩, hp⟩; exact ⟨hS, hne, hsym _ _ hp⟩
    have hsum : ∑ h ∈ S, (S.filter (fun h' => h' ≠ h ∧ P h h')).card
        = (S.filter (fun h' => h' ≠ v ∧ P v h')).card
          + ∑ h ∈ S', (S.filter (fun h' => h' ≠ h ∧ P h h')).card := by
      rw [← add_sum_erase S _ hv]
    rw [hsum, sum_congr rfl hsplit, sum_add_distrib, ← card_filter, ← hvdeg]
    have : S.card = n + 1 := hn
    have e : 2 * d * (n + 1) = 2 * d * n + 2 * d := by ring
    omega

end Hypostructure.Graph.HubLink

namespace Hypostructure.Graph.HubLink

open Finset Classical

variable {ι β : Type*} [Fintype ι]

/-- **A path of strong links is rainbow**: 5 distinct hubs of `T`, consecutive pairs linked
through `≥ 4` bags, can be linked through 4 distinct bags. -/
theorem strong_path_rainbow (Lk : ι → ι → β → Prop) (T : Finset ι)
    {h₁ h₂ h₃ h₄ h₅ : ι} (m1 : h₁ ∈ T) (m2 : h₂ ∈ T) (m3 : h₃ ∈ T) (m4 : h₄ ∈ T)
    (m5 : h₅ ∈ T) (n12 : h₁ ≠ h₂) (n13 : h₁ ≠ h₃) (n14 : h₁ ≠ h₄) (n15 : h₁ ≠ h₅)
    (n23 : h₂ ≠ h₃) (n24 : h₂ ≠ h₄) (n25 : h₂ ≠ h₅) (n34 : h₃ ≠ h₄) (n35 : h₃ ≠ h₅)
    (n45 : h₄ ≠ h₅) (s1 : SLk Lk h₁ h₂) (s2 : SLk Lk h₂ h₃) (s3 : SLk Lk h₃ h₄)
    (s4 : SLk Lk h₄ h₅) : Rainbow5 Lk T := by
  have pick : ∀ (B : Finset β) (U : Finset β), U.card ≤ 3 → 4 ≤ B.card →
      ∃ b ∈ B, b ∉ U := by
    intro B U hU hB
    have h1 := card_le_card_sdiff_add_card (s := B) (t := U)
    have hne : (B \ U).Nonempty := by rw [← card_pos]; omega
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, (mem_sdiff.1 hb).1, (mem_sdiff.1 hb).2⟩
  obtain ⟨B1, c1, l1⟩ := s1
  obtain ⟨B2, c2, l2⟩ := s2
  obtain ⟨B3, c3, l3⟩ := s3
  obtain ⟨B4, c4, l4⟩ := s4
  obtain ⟨b₁, hb1, -⟩ := pick B1 ∅ (by simp) c1
  obtain ⟨b₂, hb2, nb2⟩ := pick B2 {b₁} (by simp) c2
  obtain ⟨b₃, hb3, nb3⟩ := pick B3 {b₁, b₂} (by have := card_two_le b₁ b₂; omega) c3
  obtain ⟨b₄, hb4, nb4⟩ := pick B4 {b₁, b₂, b₃} (by have := card_three_le b₁ b₂ b₃; omega) c4
  simp only [mem_singleton, mem_insert, not_or] at nb2 nb3 nb4
  exact ⟨h₁, h₂, h₃, h₄, h₅, b₁, b₂, b₃, b₄, m1, m2, m3, m4, m5,
    n12, n13, n14, n15, n23, n24, n25, n34, n35, n45,
    Ne.symm nb2, Ne.symm nb3.1, Ne.symm nb4.1, Ne.symm nb3.2, Ne.symm nb4.2.1,
    Ne.symm nb4.2.2, l1 b₁ hb1, l2 b₂ hb2, l3 b₃ hb3, l4 b₄ hb4⟩

end Hypostructure.Graph.HubLink

namespace Hypostructure.Graph.HubLink

open Finset Classical

variable {ι β : Type*} [Fintype ι]

theorem mem_part {Lk : ι → ι → β → Prop} {T : Finset ι} {h h' : ι} :
    h' ∈ part Lk T h ↔ h' ∈ T ∧ h' ≠ h ∧ ∃ b, Lk h h' b := mem_filter

end Hypostructure.Graph.HubLink

namespace Hypostructure.Graph.HubLink

open Finset Classical

variable {ι β : Type*} [Fintype ι]

theorem part_subset {Lk : ι → ι → β → Prop} {T : Finset ι} {h : ι} : part Lk T h ⊆ T :=
  filter_subset _ _

end Hypostructure.Graph.HubLink
