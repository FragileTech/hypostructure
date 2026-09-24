import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The density cap does not imply the route-8 private-carrier rate

This fixture is **evidence, not machinery**: it exhibits concrete numbers at
which node `[24]`'s density cap holds while `Graph.Route8Census.Rate` — the
object-level inequality carried by `K .route8Rate` and consumed by
`route8NoTwoCarrierContradictionRow` at nodes `[120]`--`[122]` — fails.

It exists so that the gap between the two is recorded permanently, with the
manuscript's own constants, and cannot be "repaired" later by quietly asserting
the implication.

## The two shapes

`densityCapShape` is the arithmetic core of `Value .densityCap`
(`Graph/Strategy/SpineVocabulary.lean`).  `rateShape` is the whole of
`Graph.Route8Census.Rate` (`Graph/Route8Census.lean`).  Both are stated
here on free naturals so that the fixture depends on no object construction; the
correspondence with the registered data is:

* `threshold = 3`, `windowOrder = 13`, `dischargeScale = 4` (`Problem.lean`);
* `windowRate = 118`, the integer part of the manuscript's
  `c₁₃ = 118.108581006…` (constants table);
* `scaleCount` is `Data.separatedScaleCount = Nat.log2`
  (`Problem.lean`), which is definitionally `Graph.dyadicScaleCount`
  (`Graph/SkeletonBudget.lean`) — so the density cap's slack factor is
  *exactly* `(scaleCount + 1) / scaleCount`;
* `supply ≤ 15 · packingNumber + surplus` is node `[29]`'s stub supply, with
  `15 = coldExternalStubCount` (`SpineVocabulary.lean`);
* `remainder = size - 13 · packingNumber`.

## Why the witness is the *hardest* case

The surplus threshold `T(n) = spineScale · ⌈√n⌉` occurs on the **right** of
`densityCapShape` and on the **left** of `rateShape`, so a larger `T(n)` makes
the density cap easier to satisfy and the rate harder to satisfy — i.e. it makes
this counterexample *easier*.  Taking `surplus = 0` below is therefore the
strongest form of the statement, not a convenient one.

## The arithmetic

With `θ = p/n`, `densityCapShape` reads `θ ≲ θ_win · (1 + 1/scaleCount)` where
`θ_win = 3/(2·c₁₃) = 0.01270017798…`, and `rateShape` requires `θ < 1/78 =
0.01282051282…`.  The absolute gap is `0.00012033483832…` — the constant the
manuscript prints in `thm:cold-branch-quantitative-closure` — so the implication
needs `θ_win / scaleCount < 0.00012033…`, i.e. `scaleCount > 105.54`.

At `scaleCount = 100` the implication therefore fails, and `witness` below is a
concrete instance: `size = 2 ^ 100` (so that `Nat.log2 size = 100` really is the
registered scale count) and `packingNumber = ⌈size / 78⌉`.
-/

namespace Hypostructure.Fixtures.Route8RateDensityCapGap

/-- The arithmetic core of `Value .densityCap`
(`Graph/Strategy/SpineVocabulary.lean`). -/
def densityCapShape
    (windowRate scaleCount packingNumber threshold size surplus densitySlack : Nat) :
    Prop :=
  2 * (windowRate * scaleCount * packingNumber) ≤
    (scaleCount + 1) * (threshold * size + surplus) +
      densitySlack * (windowRate * scaleCount) * surplus

/-- `Graph.Route8Census.Rate` (`Graph/Route8Census.lean`). -/
def rateShape (threshold discharge supply slack remainder : Nat) : Prop :=
  (threshold * discharge + 1) * supply + threshold * slack < threshold * remainder

/-- **The gap.**  At the registered constants, with the scale count equal to the
witness object's own `Nat.log2`, the density cap holds and the route-8
private-carrier rate fails.  Hence no row can derive `K .route8Rate` from
`K .densityCap` together with node `[29]`'s stub supply alone. -/
theorem witness :
    densityCapShape 118 100 16251930772156787198675682121 3
        1267650600228229401496703205376 0 0 ∧
      ¬ rateShape 3 4 (15 * 16251930772156787198675682121) 0
          (1267650600228229401496703205376 -
            13 * 16251930772156787198675682121) := by
  constructor
  · show 2 * (118 * 100 * 16251930772156787198675682121) ≤
      (100 + 1) * (3 * 1267650600228229401496703205376 + 0) +
        0 * (118 * 100) * 0
    norm_num
  · show ¬ ((3 * 4 + 1) * (15 * 16251930772156787198675682121) + 3 * 0 <
      3 * (1267650600228229401496703205376 -
        13 * 16251930772156787198675682121))
    norm_num

/-! ## The manuscript's claims, implemented and judged by Lean

`prop:p13-density` and `rem:route8-carrier-margin` are
stated below at the *registered* `windowRate = 118`, where the manuscript's real
constants become exact rationals:

* `θ_win = 1.5 / 118 = 3 / 236`;
* `τ_win = 15·θ_win / (1 - 13·θ_win) = (45/236) / (197/236) = 45 / 197`
  (`= 0.2284264…`; the manuscript prints `0.22817486846…` at the unrounded
  `c₁₃ = 118.108581006…`);
* `3 / 13 = 0.2307692…`.

Writing `θ = p/n` and `|R| = n - 13p`, the rate `τ < 3/13` is `195·p < 3·|R|`,
i.e. `234·p < 3·n` — exactly `rateShape` after the node-`[29]` stub supply.
-/

/-- **`rem:route8-carrier-margin`, the closed constant fact.**
`τ_win < 3/13` at the registered `windowRate`, cleared of denominators:
`45/197 < 3/13`.  Decided, with no object and no condition on `n`. -/
theorem tauWin_lt_three_over_thirteen : 45 * 13 < 3 * 197 := by norm_num

/-- **`prop:p13-density`'s rate claim, implemented as stated.**  From the
density cap (here at `surplus = 0`, its strongest form) the route-8 rate
`234·p < 3·n` follows — *given* the scale-count bound `117 < scaleCount`.

Lean's verdict: the claim goes through, and `117 < scaleCount` is exactly the
residue it leaves.  `234·(scaleCount+1) < 236·scaleCount` is the whole of it. -/
theorem rate_of_densityCap (scaleCount size packingNumber : Nat)
    (sizePos : 0 < size) (scale : 117 < scaleCount)
    (cap : 2 * (118 * scaleCount * packingNumber) ≤
      (scaleCount + 1) * (3 * size)) :
    234 * packingNumber < 3 * size := by
  rcases Nat.eq_zero_or_pos packingNumber with rfl | packingPos
  · omega
  · by_contra contra
    have contra' : 3 * size ≤ 234 * packingNumber := Nat.not_lt.mp contra
    have step : (scaleCount + 1) * (3 * size) ≤
        (scaleCount + 1) * (234 * packingNumber) :=
      Nat.mul_le_mul_left _ contra'
    have combined : 2 * (118 * scaleCount * packingNumber) ≤
        (scaleCount + 1) * (234 * packingNumber) := le_trans cap step
    have lhs : 2 * (118 * scaleCount * packingNumber) =
        236 * (scaleCount * packingNumber) := by ring
    have rhs : (scaleCount + 1) * (234 * packingNumber) =
        234 * (scaleCount * packingNumber) + 234 * packingNumber := by ring
    rw [lhs, rhs] at combined
    have descend : 118 * packingNumber ≤ scaleCount * packingNumber :=
      Nat.mul_le_mul_right packingNumber (by omega)
    omega

/-- **The residue, exhibited.**  `witness` above is the instance
`scaleCount = 100`, which satisfies the density cap and violates the rate.  So
`117 < scaleCount` in `rate_of_densityCap` is not an artifact of the proof: it
is necessary.  In the spine's terms `scaleCount = Nat.log2 object.vertexCount`,
so the exact goal the branch cannot discharge is

  `117 < Nat.log2 object.vertexCount`,   i.e.   `2 ^ 118 ≤ object.vertexCount`.
-/
theorem residue_is_necessary :
    ¬ ∀ scaleCount size packingNumber : Nat, 0 < size →
        2 * (118 * scaleCount * packingNumber) ≤ (scaleCount + 1) * (3 * size) →
        234 * packingNumber < 3 * size := by
  intro universal
  have applied := universal 100 1267650600228229401496703205376
    16251930772156787198675682121 (by norm_num) (by norm_num)
  norm_num at applied

end Hypostructure.Fixtures.Route8RateDensityCapGap

-- Axiom audit: every claim must rest on nothing but Lean's own foundations.
#print axioms Hypostructure.Fixtures.Route8RateDensityCapGap.witness
#print axioms Hypostructure.Fixtures.Route8RateDensityCapGap.tauWin_lt_three_over_thirteen
#print axioms Hypostructure.Fixtures.Route8RateDensityCapGap.rate_of_densityCap
#print axioms Hypostructure.Fixtures.Route8RateDensityCapGap.residue_is_necessary
