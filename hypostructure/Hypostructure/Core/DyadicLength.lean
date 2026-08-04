import Hypostructure.Core.Prelude

/-!
# Executable dyadic length algebra

The dyadic length family is domain-neutral arithmetic on `Nat`: it mentions no
ambient object, no target, and no strategy.  Applications whose target selects
cycle lengths that are powers of two register `PowerOfTwoLength` and consume
the completeness theorem below; they do not restate either.

The bounded exponent makes the predicate a finite search space, hence
decidable.  `powerOfTwoLength_iff` keeps it equivalent to the unbounded
exponent form in which external theorems and pinned public statements are
written, so no application has to prove the bridge.
-/

namespace Hypostructure.Core.DyadicLength

/-- Executable predicate for lengths that are powers of two with exponent at
least two. -/
def PowerOfTwoLength (length : Nat) : Prop :=
  ∃ exponent : Fin (length + 1),
    2 ≤ exponent.1 ∧ length = 2 ^ exponent.1

instance powerOfTwoLengthDecidable (length : Nat) :
    Decidable (PowerOfTwoLength length) := by
  unfold PowerOfTwoLength
  infer_instance

theorem exponent_le_two_pow (exponent : Nat) :
    exponent ≤ 2 ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent inductionHypothesis =>
      rw [pow_succ]
      have positive : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
      omega

/-- The executable predicate is equivalent to the unbounded exponent form. -/
theorem powerOfTwoLength_iff (length : Nat) :
    PowerOfTwoLength length ↔
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent := by
  constructor
  · rintro ⟨exponent, lower, equality⟩
    exact ⟨exponent.1, lower, equality⟩
  · rintro ⟨exponent, lower, equality⟩
    have bound : exponent < length + 1 := by
      rw [equality]
      exact Nat.lt_succ_of_le (exponent_le_two_pow exponent)
    exact ⟨⟨exponent, bound⟩, lower, equality⟩

/-- The unbounded exponent form entering the executable predicate.  This is
the bridge consumed by external theorems whose conclusion is stated with a
free exponent. -/
theorem powerOfTwoLength_of_exists {length : Nat}
    (witness : ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) :
    PowerOfTwoLength length :=
  (powerOfTwoLength_iff length).mpr witness

/-- Four is the first accepted dyadic length. -/
theorem powerOfTwoLength_four : PowerOfTwoLength 4 :=
  ⟨⟨2, by decide⟩, by decide, by decide⟩

/-- Executable return length whose successor is an accepted dyadic length. -/
def MersenneLength (length : Nat) : Prop :=
  PowerOfTwoLength (length + 1)

instance mersenneLengthDecidable (length : Nat) :
    Decidable (MersenneLength length) :=
  powerOfTwoLengthDecidable (length + 1)

/-- The executable return lengths are exactly `2^k - 1` for `k ≥ 2`. -/
theorem mersenneLength_iff (length : Nat) :
    MersenneLength length ↔
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent - 1 := by
  rw [MersenneLength, powerOfTwoLength_iff]
  constructor
  · rintro ⟨exponent, lower, equality⟩
    refine ⟨exponent, lower, ?_⟩
    have positive : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
    omega
  · rintro ⟨exponent, lower, equality⟩
    refine ⟨exponent, lower, ?_⟩
    have positive : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
    omega

/-- The dyadic return-length set. -/
def MersenneSet : Set Nat := {length | MersenneLength length}

end Hypostructure.Core.DyadicLength
