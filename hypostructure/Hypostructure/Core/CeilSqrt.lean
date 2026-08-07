import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# The integer ceiling square root

A scale basis a problem can register a threshold against: `⌈√n⌉`, computed from
Lean's certified integer square root.  Nothing here is specific to any problem
or manuscript -- it is the arithmetic a `√n`-scaled threshold is read at.
-/

namespace Hypostructure.Core

/-- Integer ceiling of the square root. -/
def ceilSqrt (size : Nat) : Nat :=
  if Nat.sqrt size ^ 2 = size then Nat.sqrt size else Nat.sqrt size + 1

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

/-- The computed ceiling square root really covers the source size. -/
theorem le_ceilSqrt_sq (size : Nat) : size ≤ ceilSqrt size ^ 2 := by
  by_cases perfect : Nat.sqrt size ^ 2 = size
  · simp [ceilSqrt, perfect]
  · rw [ceilSqrt, if_neg perfect]
    exact Nat.le_of_lt (Nat.lt_succ_sqrt' size)

theorem ceilSqrt_le_sqrt_succ (size : Nat) :
    ceilSqrt size ≤ Nat.sqrt size + 1 := by
  by_cases perfect : Nat.sqrt size ^ 2 = size
  · simp [ceilSqrt, perfect]
  · simp [ceilSqrt, if_neg perfect]

/-- The binary logarithm is bounded by the integer ceiling square root.  This
is the exact finite estimate used when the sparse entropy sandwich absorbs its
`sigma log₂ n` term. -/
theorem log2_le_ceilSqrt (size : Nat) : Nat.log2 size ≤ ceilSqrt size := by
  have sq_lt_pow : ∀ root : Nat, root * root < 2 ^ (root + 1) := by
    intro root
    by_cases small : root ≤ 2
    · interval_cases root <;> norm_num
    · have three_le : 3 ≤ root := by omega
      induction root, three_le using Nat.le_induction with
      | base => norm_num
      | succ root three_le ih =>
          rw [show root + 1 + 1 = (root + 1) + 1 by omega, pow_succ]
          have ih' := ih (by omega)
          have linear : 2 * root + 1 ≤ root * root := by nlinarith
          nlinarith
  by_cases zero : size = 0
  · simp [zero]
  · have covered := le_ceilSqrt_sq size
    have below : size < 2 ^ (ceilSqrt size + 1) :=
      lt_of_le_of_lt covered (by
        simpa [pow_two] using sq_lt_pow (ceilSqrt size))
    rw [Nat.log2_eq_log_two]
    have := Nat.log_lt_of_lt_pow zero below
    omega

/-- **A `√n`-scaled quantity is eventually below any positive linear one.**

`scale · ⌈√n⌉ ≤ rate · n + scale` as soon as `scale² ≤ rate²·n`, which is the
only thing a registered `O(√n)` threshold is ever asked for: that it is
sublinear.  The additive `scale` is the ceiling's own rounding, and a consumer
that needs a strict comparison takes `n` past it.

Nothing here knows what the scale or the rate are; both are the caller's. -/
theorem mul_ceilSqrt_le (scale rate size : Nat)
    (dominates : scale * scale ≤ rate * rate * size) :
    scale * ceilSqrt size ≤ rate * size + scale := by
  have root : scale * Nat.sqrt size ≤ rate * size := by
    have squared : (scale * Nat.sqrt size) * (scale * Nat.sqrt size) ≤
        (rate * size) * (rate * size) := by
      have sqrtLe : Nat.sqrt size * Nat.sqrt size ≤ size := Nat.sqrt_le size
      calc (scale * Nat.sqrt size) * (scale * Nat.sqrt size)
          = (scale * scale) * (Nat.sqrt size * Nat.sqrt size) := by ring
        _ ≤ (rate * rate * size) * size :=
            Nat.mul_le_mul dominates sqrtLe
        _ = (rate * size) * (rate * size) := by ring
    exact Nat.mul_self_le_mul_self_iff.mp squared
  calc scale * ceilSqrt size
      ≤ scale * (Nat.sqrt size + 1) :=
        Nat.mul_le_mul_left _ (ceilSqrt_le_sqrt_succ size)
    _ = scale * Nat.sqrt size + scale := by ring
    _ ≤ rate * size + scale := Nat.add_le_add_right root _

end Hypostructure.Core
