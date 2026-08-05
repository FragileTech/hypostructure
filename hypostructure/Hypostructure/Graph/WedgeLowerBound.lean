import Mathlib.Data.Nat.Choose.Basic
import Hypostructure.Graph.BoundaryDemand

/-!
# The wedge lower bound

`lem:wedge-lower`.  For a region `X` of a finite object, the number of internal
length-two wedges is

  `W₂(X) = Σ_{v∈X} C(d_X(v), 2)`,

a wedge being a choice of two distinct neighbours of a common centre *inside*
`X`.  The lemma bounds it from below by the region's own size against the
registered baseline:

  `W₂(X) ≥ δ·|X| − 2·def⁺(X)`,

stated here subtraction-free as `δ·|X| ≤ W₂(X) + 2·def⁺(X)`.

The manuscript proves it by the degree count.  With `n_i` the number of
vertices of internal degree `i`,

  `W₂(X) − (δ|X| − 2def⁺(X)) = 3n₀ + n₁ + Σ_{i≥3}(C(i,2) − 3)n_i ≥ 0`

at the manuscript's own baseline.  Every term of that identity is one vertex's
contribution, so the argument is pointwise and the sum is the whole of it:
`baseline_le_choose_two_add_two_mul_deficit` below is the per-vertex clause,
with slack `3`, `1`, `0` at internal degrees `0`, `1`, `2` and `C(d,2) − 3`
above them — the manuscript's four cases exactly.

The baseline is a parameter, and `3` is not written as a value of it: the two
insufficiency theorems below *prove*, from this file's own definitions, that the
per-vertex clause fails at baseline `1` and at baseline `2`, so `3 ≤ δ` is
derived here as the precise threshold the count needs rather than copied from a
manuscript.  A spine registering a baseline already carries that hypothesis for
an unrelated reason (Stirling's `⌈e⌉` in the skeleton budget); this file needs
it a second time, and independently.

Nothing here mentions components.  The manuscript states the bound for a
component `C` of the remainder and then sums over components, using that
`d_C = d_R` inside a component; the count below holds at *every* region, so
both of its displayed inequalities — the componentwise one and its sum over
`R` — are instances of one theorem, and no component decomposition has to be
built to connect them.
-/

namespace Hypostructure.Graph

open scoped BigOperators

universe u

namespace FiniteObject

/-- **`W₂(X)`.**  The internal length-two wedges of a region: `C(d_X(v), 2)`
summed over the region, where `d_X` counts only neighbours inside `X`. -/
noncomputable def internalWedgeCount (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Nat :=
  ∑ vertex ∈ support, (object.internalDegree support vertex).choose 2

/-- `2·C(d,2) = d(d−1)` for every `d`, including `d = 0` (`Nat` subtraction
truncates `0 − 1` to `0` on both sides). -/
private theorem two_mul_choose_two (d : Nat) :
    2 * d.choose 2 = d * (d - 1) := by
  rw [Nat.choose_two_right, mul_comm]
  exact Nat.div_mul_cancel d.even_mul_pred_self.two_dvd

/-- The baseline-free core of the count: a vertex's own wedge contribution
covers twice its degree up to three units of slack, with equality at `d = 2`
and `d = 3`.  This is the manuscript's `3n₀ + n₁ + Σ_{i≥3}(C(i,2) − 3)n_i`
read one vertex at a time. -/
private theorem two_mul_le_choose_two_add_three (d : Nat) :
    2 * d ≤ d.choose 2 + 3 := by
  match d with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (m + 4) =>
    have h2 := two_mul_choose_two (m + 4)
    have hsub : m + 4 - 1 = m + 3 := by omega
    rw [hsub] at h2
    nlinarith

/-- The threshold `3 ≤ δ` is necessary, not merely sufficient: at `δ = 1` a
vertex of internal degree exactly `1` is not deficient and contributes no
wedge, so the per-vertex clause reads `1 ≤ 0`. -/
theorem baseline_one_insufficient :
    ¬ (1 ≤ (1 : Nat).choose 2 + 2 * (1 - 1)) := by decide

/-- Likewise at `δ = 2`: a vertex of internal degree exactly `2` is not
deficient and contributes `C(2,2) = 1`, so the clause reads `2 ≤ 1`. -/
theorem baseline_two_insufficient :
    ¬ (2 ≤ (2 : Nat).choose 2 + 2 * (2 - 2)) := by decide

/-- **The per-vertex clause of `lem:wedge-lower`** at a registered baseline
`δ ≥ 3`: one vertex's own wedge contribution, together with twice its own
deficiency below `δ`, always covers `δ`.

Below the baseline the doubled deficiency makes up the gap between `2d` and
`2δ`; at or above it the deficiency vanishes and `C(d,2)` alone suffices,
which is where `3 ≤ δ` is spent. -/
theorem baseline_le_choose_two_add_two_mul_deficit
    (baseline d : Nat) (baseline_ge : 3 ≤ baseline) :
    baseline ≤ d.choose 2 + 2 * (baseline - d) := by
  rcases Nat.lt_or_ge d baseline with below | above
  · have h := two_mul_le_choose_two_add_three d
    omega
  · have vanishes : baseline - d = 0 := by omega
    rw [vanishes, mul_zero]
    have monotone : baseline.choose 2 ≤ d.choose 2 := Nat.choose_le_choose 2 above
    have h := two_mul_le_choose_two_add_three baseline
    omega

/-- **`lem:wedge-lower`, subtraction-free.**

  `δ·|X| ≤ W₂(X) + 2·def⁺(X)`

at every region `X` of the object, for every registered baseline `δ ≥ 3`.
This is the manuscript's `W₂(X) ≥ δ|X| − 2def⁺(X)` with the truncation moved
to the side where it cannot silently absorb a failure.

The proof is the manuscript's: sum the per-vertex clause over the region.  Both
of the lemma's displayed inequalities are instances — the componentwise one at
a component of the remainder, and its sum over `R` at the remainder itself. -/
theorem baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (baseline : Nat) (baseline_ge : 3 ≤ baseline) :
    baseline * support.card ≤
      object.internalWedgeCount support +
        2 * object.positiveDeficiency support baseline := by
  classical
  calc baseline * support.card
      = ∑ _vertex ∈ support, baseline := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ vertex ∈ support,
          ((object.internalDegree support vertex).choose 2 +
            2 * (baseline - object.internalDegree support vertex)) :=
        Finset.sum_le_sum fun vertex _ =>
          baseline_le_choose_two_add_two_mul_deficit baseline
            (object.internalDegree support vertex) baseline_ge
    _ = object.internalWedgeCount support +
          2 * object.positiveDeficiency support baseline := by
        rw [Finset.sum_add_distrib, internalWedgeCount, positiveDeficiency,
          Finset.mul_sum]

end FiniteObject

end Hypostructure.Graph
