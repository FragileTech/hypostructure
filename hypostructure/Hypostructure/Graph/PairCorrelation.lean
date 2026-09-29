import Hypostructure.Graph.SparseEntropySandwich

/-!
# The correlation mass of an exposure order

`Graph.SparsePairSkeletonModel.RealizingOrder` asks that every realized
`(baseline word, exposed prefix)` signature extend in both values of the next
pair response.  This module measures how far an exposure order is from that,
exactly, by counting realized signatures in G's labelled `(n,m)` class:

* `signatureCount k` is the number of distinct `(baseline word, first k
  responses)` signatures realized by members of the class;
* `signatureCount 0 = 2 ^ |baselineFamily|` (the baseline code is realized);
* `signatureCount k ≤ signatureCount (k+1) ≤ 2 · signatureCount k`;
* `signatureCount k ≤ |class|`;
* the **correlation mass** `Σ_{k<t} 2^{t-1-k} (2 P_k − P_{k+1})` satisfies
  `2^t P_0 = P_t + mass`, hence `2^{b+t} ≤ |class| + mass`.

A count failure `|class| < 2^{b+t}` therefore forces a positive mass, hence a
first non-branching index `k*` at which the first `k*` responses are jointly
free (`P_{k*} = 2^{b+k*}`) and the next one is correlated with the earlier ones
and the baseline word (`P_{k*+1} < 2 P_{k*}`).
-/

namespace Hypostructure.Graph.SparsePairSkeletonModel

open Hypostructure
open Hypostructure.Graph

universe u

/-! ## The arithmetic of a doubling profile -/

/-- The doubling deficiency of a profile: `2 P_k − P_{k+1}`, the number of
non-branching prefixes at step `k`. -/
def deficiency (P : Nat → Nat) (k : Nat) : Nat := 2 * P k - P (k + 1)

/-- The correlation mass of a doubling profile of length `t`. -/
def mass (P : Nat → Nat) (t : Nat) : Nat :=
  ∑ k ∈ Finset.range t, 2 ^ (t - 1 - k) * deficiency P k

/-- **The telescoping identity**: `2^t P_0 = P_t + mass`. -/
theorem two_pow_mul_eq_add_mass (P : Nat → Nat) (t : Nat)
    (bound : ∀ k < t, P (k + 1) ≤ 2 * P k) :
    2 ^ t * P 0 = P t + mass P t := by
  induction t with
  | zero => simp [mass]
  | succ t ih =>
      have ihBound := ih (fun k hk => bound k (Nat.lt_succ_of_lt hk))
      have last := bound t (Nat.lt_succ_self t)
      have sumEq : mass P (t + 1) = 2 * mass P t + deficiency P t := by
        unfold mass
        rw [Finset.sum_range_succ, Finset.mul_sum]
        have inner : ∀ k ∈ Finset.range t,
            2 ^ (t + 1 - 1 - k) * deficiency P k =
              2 * (2 ^ (t - 1 - k) * deficiency P k) := by
          intro k hk
          have kLt := Finset.mem_range.mp hk
          have exponent : t + 1 - 1 - k = (t - 1 - k) + 1 := by omega
          rw [exponent, pow_succ]
          ring
        rw [Finset.sum_congr rfl inner]
        simp
      have deficiencyEq : P (t + 1) + deficiency P t = 2 * P t := by
        unfold deficiency
        omega
      rw [sumEq, pow_succ]
      calc 2 ^ t * 2 * P 0 = 2 * (2 ^ t * P 0) := by ring
        _ = 2 * (P t + mass P t) := by rw [ihBound]
        _ = P (t + 1) + (2 * mass P t + deficiency P t) := by omega

/-- **A count failure forces a first non-branching index.**  If
`P_t < 2^t P_0` and the profile is doubling, some step `k < t` has
`P_{k+1} < 2 P_k`; the least such `k` has `P_j+1 = 2 P_j` for all `j < k`, so
`P_k = 2^k P_0`. -/
theorem exists_first_nonbranching (P : Nat → Nat) (t : Nat)
    (bound : ∀ k < t, P (k + 1) ≤ 2 * P k)
    (failure : P t < 2 ^ t * P 0) :
    ∃ k < t, (∀ j < k, P (j + 1) = 2 * P j) ∧ P (k + 1) < 2 * P k := by
  classical
  have exists_step : ∃ k, k < t ∧ P (k + 1) < 2 * P k := by
    by_contra none
    push Not at none
    have allEq : ∀ k < t, P (k + 1) = 2 * P k := fun k hk =>
      le_antisymm (bound k hk) (none k hk)
    have massZero : mass P t = 0 := by
      unfold mass
      apply Finset.sum_eq_zero
      intro k hk
      have kLt := Finset.mem_range.mp hk
      have : deficiency P k = 0 := by
        unfold deficiency
        rw [allEq k kLt]
        omega
      simp [this]
    have identity := two_pow_mul_eq_add_mass P t bound
    omega
  refine ⟨Nat.find exists_step, (Nat.find_spec exists_step).1, ?_,
    (Nat.find_spec exists_step).2⟩
  intro j hj
  have notStep := Nat.find_min exists_step hj
  have jLt : j < t := lt_trans hj (Nat.find_spec exists_step).1
  have : ¬ P (j + 1) < 2 * P j := fun h => notStep ⟨jLt, h⟩
  exact le_antisymm (bound j jLt) (not_lt.mp this)

/-! ## Signature counts in the skeleton class -/

variable {object : FiniteObject.{u}} {Coordinate Chord : Type u}
  {activation : object.DemandActivation Coordinate Chord}
  {schedule : Finset (Finset (object.Vertex × object.Vertex))}

/-- The baseline code words of the model. -/
abbrev BaselineWord (model : SparsePairSkeletonModel activation schedule) : Type _ :=
  {coordinate // coordinate ∈ model.baselineFamily} → Bool

/-- The responses of a member along an exposure order, as a sequence:
`False` past the end of the family. -/
noncomputable def responseSequence {LengthOK : Nat → Prop}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (member : model.Skeleton) (index : Nat) : Prop :=
  if h : index < family.card then
    model.response (LengthOK := LengthOK) member (order ⟨index, h⟩).1
  else False

/-- The signature of a member at depth `k`: its baseline word and its first `k`
responses along the exposure order. -/
noncomputable def signature {LengthOK : Nat → Prop}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (k : Nat) (member : model.Skeleton) : model.BaselineWord × (Nat → Prop) :=
  (model.baseline.response member.1, fun index =>
    if index < k then
      responseSequence (LengthOK := LengthOK) model family order member index
    else False)

/-- **`P_k`**: the number of distinct `(baseline word, first k responses)`
signatures realized in G's labelled `(n,m)` class. -/
noncomputable def signatureCount {LengthOK : Nat → Prop}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (k : Nat) : Nat :=
  (Set.range (signature (LengthOK := LengthOK) model family order k)).ncard

variable {LengthOK : Nat → Prop}
  (model : SparsePairSkeletonModel activation schedule)
  (family : Finset {pair // pair ∈ model.pairSet})
  (order : Fin family.card ≃ {pair // pair ∈ family})

theorem signatureCount_zero :
    signatureCount (LengthOK := LengthOK) model family order 0 =
      2 ^ model.baselineFamily.card := by
  classical
  have rangeEq : Set.range (signature (LengthOK := LengthOK) model family order 0) =
      (fun word : model.BaselineWord => (word, fun _ : Nat => (False : Prop))) ''
        Set.univ := by
    ext point
    constructor
    · rintro ⟨member, rfl⟩
      refine ⟨model.baseline.response member.1, trivial, ?_⟩
      simp [signature]
    · rintro ⟨word, -, rfl⟩
      obtain ⟨member, realizes⟩ := model.baseline.realized word
      refine ⟨member, Prod.ext realizes ?_⟩
      funext index
      simp [signature]
  unfold signatureCount
  rw [rangeEq, Set.ncard_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
    Set.ncard_univ]
  rw [Nat.card_fun]
  simp

theorem signatureCount_le_class (k : Nat) :
    signatureCount (LengthOK := LengthOK) model family order k ≤
      Nat.card model.Skeleton := by
  unfold signatureCount
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective)

theorem signatureCount_succ_le (k : Nat) :
    signatureCount (LengthOK := LengthOK) model family order (k + 1) ≤
      2 * signatureCount (LengthOK := LengthOK) model family order k := by
  classical
  let extend : (model.BaselineWord × (Nat → Prop)) × Prop →
      model.BaselineWord × (Nat → Prop) := fun pair =>
    (pair.1.1, fun index => if index = k then pair.2 else pair.1.2 index)
  have subset : Set.range (signature (LengthOK := LengthOK) model family order (k + 1)) ⊆
      extend '' (Set.range (signature (LengthOK := LengthOK) model family order k) ×ˢ
        (Set.univ : Set Prop)) := by
    rintro point ⟨member, rfl⟩
    refine ⟨(signature (LengthOK := LengthOK) model family order k member,
      responseSequence (LengthOK := LengthOK) model family order member k),
      ⟨⟨member, rfl⟩, trivial⟩, ?_⟩
    refine Prod.ext rfl ?_
    funext index
    by_cases hIndex : index = k
    · subst hIndex
      simp [extend, signature]
    · by_cases hLt : index < k
      · have : index < k + 1 := Nat.lt_succ_of_lt hLt
        simp only [extend, signature]
        rw [if_neg hIndex, if_pos hLt, if_pos this]
      · have : ¬ index < k + 1 := by omega
        simp only [extend, signature]
        rw [if_neg hIndex, if_neg hLt, if_neg this]
  unfold signatureCount
  calc _ ≤ (extend '' (Set.range (signature (LengthOK := LengthOK) model family order k) ×ˢ
        (Set.univ : Set Prop))).ncard :=
        Set.ncard_le_ncard subset
          ((Set.toFinite _).image _)
    _ ≤ (Set.range (signature (LengthOK := LengthOK) model family order k) ×ˢ
        (Set.univ : Set Prop)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = (Set.range (signature (LengthOK := LengthOK) model family order k)).ncard * 2 := by
        rw [Set.ncard_prod, Set.ncard_univ]
        simp
    _ = _ := by ring

theorem signatureCount_le_succ (k : Nat) :
    signatureCount (LengthOK := LengthOK) model family order k ≤
      signatureCount (LengthOK := LengthOK) model family order (k + 1) := by
  classical
  let project : model.BaselineWord × (Nat → Prop) → model.BaselineWord × (Nat → Prop) :=
    fun point => (point.1, fun index => if index < k then point.2 index else False)
  have subset : Set.range (signature (LengthOK := LengthOK) model family order k) ⊆
      project '' Set.range (signature (LengthOK := LengthOK) model family order (k + 1)) := by
    rintro point ⟨member, rfl⟩
    refine ⟨signature (LengthOK := LengthOK) model family order (k + 1) member,
      ⟨member, rfl⟩, ?_⟩
    refine Prod.ext rfl ?_
    funext index
    by_cases hLt : index < k
    · have : index < k + 1 := Nat.lt_succ_of_lt hLt
      simp only [project, signature]
      rw [if_pos hLt, if_pos this, if_pos hLt]
    · simp only [project, signature]
      rw [if_neg hLt, if_neg hLt]
  unfold signatureCount
  calc _ ≤ (project '' Set.range
        (signature (LengthOK := LengthOK) model family order (k + 1))).ncard :=
        Set.ncard_le_ncard subset ((Set.toFinite _).image _)
    _ ≤ _ := Set.ncard_image_le (Set.toFinite _)

/-- **The correlation mass identity in G's class.**  For every exposure order of
`family` and every `t ≤ |family|`,
`2^{b+t} = P_t + mass`, hence `2^{b+t} ≤ |class| + mass`. -/
theorem two_pow_le_class_add_mass (t : Nat) :
    2 ^ (model.baselineFamily.card + t) ≤
      Nat.card model.Skeleton +
        mass (signatureCount (LengthOK := LengthOK) model family order) t := by
  have bound : ∀ k < t, signatureCount (LengthOK := LengthOK) model family order (k + 1) ≤
      2 * signatureCount (LengthOK := LengthOK) model family order k :=
    fun k _ => signatureCount_succ_le model family order k
  have identity := two_pow_mul_eq_add_mass
    (signatureCount (LengthOK := LengthOK) model family order) t bound
  rw [signatureCount_zero] at identity
  have classBound := signatureCount_le_class (LengthOK := LengthOK) model family order (k := t)
  calc 2 ^ (model.baselineFamily.card + t)
      = 2 ^ t * 2 ^ model.baselineFamily.card := by rw [pow_add]; ring
    _ = _ := identity
    _ ≤ _ := by omega

/-- **Aggregate realization of a family**: some exposure order doubles the
signature count at every step, `P_{k+1} = 2 P_k`.  This is the manuscript's
`|𝒮(π_i | π_1, …, π_{i−1})| ≥ 2` in every conditional fibre, stated as the
count of realized signatures in G's labelled `(n,m)` class: a numerical fact
about G, with no class member as witness. -/
def CountRealizing (LengthOK : Nat → Prop)
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet}) : Prop :=
  ∃ order : Fin family.card ≃ {pair // pair ∈ family},
    ∀ k < family.card,
      signatureCount (LengthOK := LengthOK) model family order (k + 1) =
        2 * signatureCount (LengthOK := LengthOK) model family order k

/-- **A count failure defeats every aggregate realization.**  If the class is
smaller than `2^{b + |family|}` then no exposure order of `family` doubles the
signature count at every step: the correlation mass of every order is
positive. -/
theorem not_countRealizing_of_class_lt
    (family : Finset {pair // pair ∈ model.pairSet})
    (small : Nat.card model.Skeleton <
      2 ^ (model.baselineFamily.card + family.card)) :
    ¬ CountRealizing LengthOK model family := by
  rintro ⟨order, doubling⟩
  have massZero : mass (signatureCount (LengthOK := LengthOK) model family order)
      family.card = 0 := by
    unfold mass
    apply Finset.sum_eq_zero
    intro k hk
    have kLt := Finset.mem_range.mp hk
    have : deficiency (signatureCount (LengthOK := LengthOK) model family order) k = 0 := by
      unfold deficiency
      rw [doubling k kLt]
      omega
    simp [this]
  have bound := two_pow_le_class_add_mass (LengthOK := LengthOK) model family order
    family.card
  omega

/-- **Aggregate realization is the top-level doubling** `P_t = 2^t P_0`: the form
`P_{|family|} = 2^{|family|} · P_0` (each level has at most twice as many
signatures as the one before, so equality at the top forces doubling at every
level) is equivalent to `CountRealizing`.  Any other statement of the aggregate
test is this one. -/
theorem countRealizing_iff_top_doubling (family : Finset {pair // pair ∈ model.pairSet}) :
    CountRealizing LengthOK model family ↔
      ∃ order : Fin family.card ≃ {pair // pair ∈ family},
        signatureCount (LengthOK := LengthOK) model family order family.card =
          2 ^ family.card * signatureCount (LengthOK := LengthOK) model family order 0 := by
  constructor
  · rintro ⟨order, doubling⟩
    refine ⟨order, ?_⟩
    have bound : ∀ k < family.card,
        signatureCount (LengthOK := LengthOK) model family order (k + 1) ≤
          2 * signatureCount (LengthOK := LengthOK) model family order k :=
      fun k _ => signatureCount_succ_le model family order k
    have identity := two_pow_mul_eq_add_mass
      (signatureCount (LengthOK := LengthOK) model family order) family.card bound
    have massZero : mass (signatureCount (LengthOK := LengthOK) model family order)
        family.card = 0 := by
      unfold mass
      apply Finset.sum_eq_zero
      intro k hk
      have kLt := Finset.mem_range.mp hk
      have : deficiency (signatureCount (LengthOK := LengthOK) model family order) k = 0 := by
        unfold deficiency
        rw [doubling k kLt]
        omega
      simp [this]
    omega
  · rintro ⟨order, top⟩
    refine ⟨order, fun k hk => ?_⟩
    have bound : ∀ k < family.card,
        signatureCount (LengthOK := LengthOK) model family order (k + 1) ≤
          2 * signatureCount (LengthOK := LengthOK) model family order k :=
      fun k _ => signatureCount_succ_le model family order k
    have identity := two_pow_mul_eq_add_mass
      (signatureCount (LengthOK := LengthOK) model family order) family.card bound
    have massZero : mass (signatureCount (LengthOK := LengthOK) model family order)
        family.card = 0 := by omega
    have term : 2 ^ (family.card - 1 - k) *
        deficiency (signatureCount (LengthOK := LengthOK) model family order) k = 0 := by
      have := Finset.sum_eq_zero_iff.mp massZero k (Finset.mem_range.mpr hk)
      exact this
    have defZero : deficiency (signatureCount (LengthOK := LengthOK) model family order) k = 0 := by
      rcases Nat.mul_eq_zero.mp term with h | h
      · exact absurd h (by positivity)
      · exact h
    have le := bound k hk
    unfold deficiency at defZero
    omega

/-- The mass of any profile obeys `mass ≤ Σ 2^{t-1-k} · 2 P_k`: the deficiency
`2 P_k − P_{k+1}` is at most `2 P_k`. -/
theorem mass_le_weighted_sum (P : Nat → Nat) (t : Nat) :
    mass P t ≤ ∑ k ∈ Finset.range t, 2 ^ (t - 1 - k) * (2 * P k) := by
  unfold mass
  apply Finset.sum_le_sum
  intro k _
  apply Nat.mul_le_mul_left
  unfold deficiency
  omega

/-- Each level of a doubling profile has at most `2^k P_0` signatures. -/
theorem le_pow_mul_zero (P : Nat → Nat) (t : Nat) (bound : ∀ k < t, P (k + 1) ≤ 2 * P k) :
    ∀ k ≤ t, P k ≤ 2 ^ k * P 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have := ih (Nat.le_of_succ_le hk)
      have := bound k (Nat.lt_of_succ_le hk)
      calc P (k + 1) ≤ 2 * P k := ‹_›
        _ ≤ 2 * (2 ^ k * P 0) := Nat.mul_le_mul_left _ (ih (Nat.le_of_succ_le hk))
        _ = 2 ^ (k + 1) * P 0 := by ring

/-- **No channel of correlation exceeds one maximal step.**  The weighted deficiency of a
single step `k < t` is at most `2^t P_0`: a step contributes at most the whole gap
`2^t P_0 − P_t`'s scale, so one correlated step can carry the entire mass. -/
theorem weighted_deficiency_le (P : Nat → Nat) (t : Nat)
    (mono : ∀ k < t, P k ≤ P (k + 1)) (bound : ∀ k < t, P (k + 1) ≤ 2 * P k) (k : Nat)
    (hk : k < t) : 2 ^ (t - 1 - k) * deficiency P k ≤ 2 ^ (t - 1) * P 0 := by
  have hP := le_pow_mul_zero P t bound k hk.le
  have hd : deficiency P k ≤ 2 ^ k * P 0 := by
    unfold deficiency
    have := mono k hk
    omega
  calc 2 ^ (t - 1 - k) * deficiency P k ≤ 2 ^ (t - 1 - k) * (2 ^ k * P 0) :=
        Nat.mul_le_mul_left _ hd
    _ = 2 ^ (t - 1) * P 0 := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega

/-- Extend a signature at depth `k` by the value `v` of the `(k+1)`-th response. -/
def extendSignature {α β : Type*} (k : Nat) (p : α × (Nat → β)) (v : β) : α × (Nat → β) :=
  (p.1, fun index => if index = k then v else p.2 index)

/-- **The repetition at a correlated step, in aggregate form.**  If the count of
realized signatures at depth `k+1` is below twice that at depth `k`, then some
realized `k`-signature (a baseline word with its first `k` responses, a point of
the code space and not a class member) has a forbidden extension: the value of the
`(k+1)`-th response is forced by that prefix, over the whole labelled `(n,m)`
class. -/
theorem exists_forbidden_extension (k : Nat)
    (correlated : signatureCount (LengthOK := LengthOK) model family order (k + 1) <
      2 * signatureCount (LengthOK := LengthOK) model family order k) :
    ∃ p ∈ Set.range (signature (LengthOK := LengthOK) model family order k), ∃ v : Prop,
      extendSignature k p v ∉
        Set.range (signature (LengthOK := LengthOK) model family order (k + 1)) := by
  classical
  by_contra none
  push Not at none
  let extend : (model.BaselineWord × (Nat → Prop)) × Prop →
      model.BaselineWord × (Nat → Prop) := fun q => extendSignature k q.1 q.2
  have inj : Set.InjOn extend
      (Set.range (signature (LengthOK := LengthOK) model family order k) ×ˢ
        (Set.univ : Set Prop)) := by
    rintro ⟨p, v⟩ ⟨⟨m, rfl⟩, -⟩ ⟨p', v'⟩ ⟨⟨m', rfl⟩, -⟩ same
    have h1 := congrArg Prod.fst same
    have h2 := congrArg Prod.snd same
    simp only [extend, extendSignature] at h1 h2
    have hk : v = v' := by
      have := congrFun h2 k
      simpa using this
    have hs : signature (LengthOK := LengthOK) model family order k m =
        signature (LengthOK := LengthOK) model family order k m' := by
      refine Prod.ext h1 ?_
      funext index
      by_cases hi : index = k
      · subst hi
        simp [signature]
      · have := congrFun h2 index
        simpa [hi] using this
    simp [hs, hk]
  have subset : extend '' (Set.range (signature (LengthOK := LengthOK) model family order k) ×ˢ
      (Set.univ : Set Prop)) ⊆
      Set.range (signature (LengthOK := LengthOK) model family order (k + 1)) := by
    rintro _ ⟨⟨p, v⟩, ⟨hp, -⟩, rfl⟩
    exact none p hp v
  have le := Set.ncard_le_ncard subset (Set.toFinite _)
  rw [inj.ncard_image, Set.ncard_prod, Set.ncard_univ] at le
  unfold signatureCount at correlated
  simp at le
  omega

end Hypostructure.Graph.SparsePairSkeletonModel
