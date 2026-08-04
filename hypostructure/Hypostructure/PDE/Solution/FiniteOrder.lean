import Hypostructure.PDE.Solution.Bessel

/-!
# Placing a polynomially bounded state at a finite Sobolev grade

The graded elliptic interface of `PDE/EllipticLocalTail.lean` can only accept a
local component once that component inhabits `Bessel.sobolev grade` for *some*
real `grade`.  An application's raw datum is an arbitrary tempered distribution
carrying no assumed regularity — deliberately, because assuming regularity would
assume what the framework exists to produce.  So a placement theorem is needed:
something that takes a distribution which is known only to be *localized*, and
produces a grade it lives at.

The classical route is Paley–Wiener–Schwartz.  A compactly supported
distribution has finite order `N`; its Fourier transform is then a smooth
function of polynomial growth `≤ C (1 + ‖ξ‖) ^ N`; and a polynomially bounded
transform is square integrable once it is damped by a strong enough Bessel
weight, which is exactly membership in a Sobolev space of sufficiently negative
grade.

This module formalizes the **second and third steps**, which are the ones that
actually produce the grade:

* `memLp_two_japaneseBracket_pow_mul_rpow` — the weight computation.  The
  monomial `(1 + ‖ξ‖) ^ degree` damped by `(1 + ‖ξ‖²) ^ (-grade/2)` is square
  integrable as soon as `finrank ℝ Point < 2 * (grade - degree)`.  This is where
  the dimension enters, and it is the only place it does.
* `memLp_two_besselWeight_smul` — the same statement for a vector-valued
  function obeying a polynomial bound, which is the shape a Fourier transform
  comes in.
* `memSobolev_of_fourier_eq_integral` — **the placement theorem.**  A state
  whose Fourier transform is represented by a polynomially bounded measurable
  function lies in the Sobolev space of grade `-grade` for every
  `grade > degree + dim/2`.
* `exists_memSobolev_of_fourier_eq_integral` and `mem_sobolev_of_fourier_eq_integral`
  — the two consequences the interface asks for: *some* grade exists, and the
  state inhabits the graded carrier `Bessel.sobolev` at that grade.

The first step — that a compactly supported distribution *has* a polynomially
bounded transform — is **not** proved here and is not assumed anywhere either;
it is a hypothesis of the placement theorem, discharged by whoever supplies the
Fourier data.  See the section `Remaining gap` below.

## Why the hypothesis is stated as an integral pairing

Mathlib has no embedding of a merely measurable, polynomially bounded function
into `𝓢'`: `Function.HasTemperateGrowth.toTemperedDistribution` needs smoothness
and `MeasureTheory.Lp.toTemperedDistribution` needs an `Lp` bound, and a
polynomially growing function has neither.  So "the transform is represented by
`transform`" is spelled out directly, as the pairing identity
`𝓕 state test = ∫ ξ, test ξ • transform ξ`, which is what any representation
theorem would deliver anyway and what the proof actually consumes.

## Remaining gap

What is missing for the unconditional statement "a compactly supported tempered
distribution lies in some Sobolev space" is precisely the easy half of
Paley–Wiener–Schwartz: that for a compactly supported `state` the function
`ξ ↦ state (χ · e_{-ξ})` represents `𝓕 state` in the sense of `represents`
below.  Mathlib (as of this pin) contains no Paley–Wiener material at all, and
the standard proof needs the vector-valued identity
`χ · 𝓕 test = ∫ ξ, test ξ • (χ · e_{-ξ})` as a Bochner integral valued in the
Fréchet space `𝓓_{K}(Point, ℝ)`, for which mathlib has no integration theory.
Nothing below papers over that: every theorem here is unconditional apart from
the explicitly stated Fourier representation.

Nothing in this file names an equation, a dimension or a problem.
-/

namespace Hypostructure.PDE.Solution.FiniteOrder

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal

universe uPoint uValue

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]

/-! ## The elementary monomial comparison

The polynomial bound produced by a finite-order estimate is naturally stated in
the monomial `(1 + ‖ξ‖) ^ degree`, while every Sobolev weight in mathlib is a
power of the *Japanese bracket* `1 + ‖ξ‖²`.  The two are comparable up to a
constant, and fixing that constant once is what keeps the integrability
computation below free of case splits.
-/

omit [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
  [BorelSpace Point] in
/-- `1 + ‖ξ‖ ≤ 2 * (1 + ‖ξ‖²) ^ (1/2)`.

The square of the left side is `1 + 2‖ξ‖ + ‖ξ‖² ≤ 2 (1 + ‖ξ‖²)`, by
`2‖ξ‖ ≤ 1 + ‖ξ‖²`; a further factor of two is spent to make the constant an
integer, which costs nothing and avoids carrying a square root. -/
theorem one_add_norm_le_two_mul_japaneseBracket_sqrt (frequency : Point) :
    1 + ‖frequency‖ ≤ 2 * (1 + ‖frequency‖ ^ 2) ^ (1 / 2 : ℝ) := by
  set root := (1 + ‖frequency‖ ^ 2) ^ (1 / 2 : ℝ) with root_def
  have root_nonneg : 0 ≤ root := Real.rpow_nonneg (by positivity) _
  have root_sq : root ^ 2 = 1 + ‖frequency‖ ^ 2 := by
    rw [root_def, ← Real.rpow_natCast ((1 + ‖frequency‖ ^ 2) ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have cross : 2 * ‖frequency‖ ≤ 1 + ‖frequency‖ ^ 2 := by
    nlinarith [sq_nonneg (1 - ‖frequency‖)]
  have squared : (1 + ‖frequency‖) ^ 2 ≤ (2 * root) ^ 2 := by
    have expand : (2 * root) ^ 2 = 4 * (1 + ‖frequency‖ ^ 2) := by
      rw [mul_pow, root_sq]; ring
    rw [expand]
    nlinarith [norm_nonneg frequency]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp squared

omit [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point] [MeasurableSpace Point]
  [BorelSpace Point] in
/-- `(1 + ‖ξ‖) ^ degree ≤ 2 ^ degree * (1 + ‖ξ‖²) ^ (degree / 2)`: the previous
comparison raised to the `degree`-th power. -/
theorem one_add_norm_pow_le (degree : ℕ) (frequency : Point) :
    (1 + ‖frequency‖) ^ degree ≤
      2 ^ degree * (1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ) / 2) := by
  have step := one_add_norm_le_two_mul_japaneseBracket_sqrt frequency
  have raised : (1 + ‖frequency‖) ^ degree ≤
      (2 * (1 + ‖frequency‖ ^ 2) ^ (1 / 2 : ℝ)) ^ degree :=
    pow_le_pow_left₀ (by positivity) step degree
  refine raised.trans_eq ?_
  rw [mul_pow, ← Real.rpow_natCast ((1 + ‖frequency‖ ^ 2) ^ (1 / 2 : ℝ)) degree,
    ← Real.rpow_mul (by positivity)]
  ring_nf

/-! ## The weight computation

This is where the dimension is spent.  The damped monomial is square integrable
exactly when the total exponent beats half the dimension, and mathlib's
`integrable_rpow_neg_one_add_norm_sq` is the integrability input.
-/

/-- **The weight estimate.**  `(1 + ‖ξ‖) ^ degree * (1 + ‖ξ‖²) ^ (-grade/2)` is
square integrable as soon as `finrank ℝ Point < 2 * (grade - degree)`.

Reading the exponents: the Bessel weight of grade `grade` supplies `grade`
powers of decay, the polynomial bound of a finite-order transform consumes
`degree` of them, and square integrability in dimension `d` needs the remaining
`grade - degree` to exceed `d/2`. -/
theorem memLp_two_japaneseBracket_pow_mul_rpow {degree : ℕ} {grade : ℝ}
    (dimension_lt : (Module.finrank ℝ Point : ℝ) < 2 * (grade - degree)) :
    MemLp (fun frequency : Point =>
        (1 + ‖frequency‖) ^ degree * (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) 2
      (volume : Measure Point) := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  have decay : Integrable (fun frequency : Point =>
      (1 + ‖frequency‖ ^ 2) ^ (-(2 * (grade - (degree : ℝ))) / 2))
      (volume : Measure Point) :=
    integrable_rpow_neg_one_add_norm_sq dimension_lt
  refine (decay.const_mul ((4 : ℝ) ^ degree)).mono' (by fun_prop) ?_
  filter_upwards with frequency
  have base_pos : (0 : ℝ) < 1 + ‖frequency‖ ^ 2 := by positivity
  have square :
      ((1 + ‖frequency‖) ^ degree * (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) ^ 2 =
        ((1 + ‖frequency‖) ^ degree) ^ 2 * (1 + ‖frequency‖ ^ 2) ^ (-grade) := by
    rw [mul_pow, ← Real.rpow_natCast ((1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) 2,
      ← Real.rpow_mul base_pos.le]
    congr 2
    norm_num
  have monomial_le : ((1 + ‖frequency‖) ^ degree) ^ 2 ≤
      4 ^ degree * (1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ)) := by
    have step := one_add_norm_pow_le degree frequency
    have squared : ((1 + ‖frequency‖) ^ degree) ^ 2 ≤
        (2 ^ degree * (1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) step 2
    refine squared.trans_eq ?_
    have scalar : ((2 : ℝ) ^ degree) ^ 2 = 4 ^ degree := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have bracket : ((1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ) / 2)) ^ 2 =
        (1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ)) := by
      rw [← Real.rpow_natCast ((1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ) / 2)) 2,
        ← Real.rpow_mul base_pos.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, scalar, bracket]
  have collapse :
      4 ^ degree * (1 + ‖frequency‖ ^ 2) ^ ((degree : ℝ)) *
          (1 + ‖frequency‖ ^ 2) ^ (-grade) =
        4 ^ degree * (1 + ‖frequency‖ ^ 2) ^ (-(2 * (grade - (degree : ℝ))) / 2) := by
    rw [mul_assoc, ← Real.rpow_add base_pos]
    congr 2
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), square, ← collapse]
  gcongr

section Vector

variable {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]

omit [CompleteSpace Value] in
/-- **The weight estimate for Fourier data.**  A measurable function obeying the
polynomial bound `‖transform ξ‖ ≤ constant * (1 + ‖ξ‖) ^ degree` becomes square
integrable after multiplication by the Bessel weight of grade `-grade`, provided
`finrank ℝ Point < 2 * (grade - degree)`.

This is the previous estimate with the scalar bound put in front; nothing about
the transform other than the bound is used, which is why an arbitrary measurable
function is allowed. -/
theorem memLp_two_besselWeight_smul {degree : ℕ} {grade constant : ℝ}
    (dimension_lt : (Module.finrank ℝ Point : ℝ) < 2 * (grade - degree))
    {transform : Point → Value}
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ degree) :
    MemLp (fun frequency : Point =>
        ((1 + ‖frequency‖ ^ 2) ^ (-grade / 2) : ℝ) • transform frequency) 2
      (volume : Measure Point) := by
  have constant_nonneg : 0 ≤ constant := by
    have first := polynomial 0
    have positive : (0 : ℝ) < (1 + ‖(0 : Point)‖) ^ degree := by positivity
    nlinarith [norm_nonneg (transform 0)]
  have dominating : MemLp (fun frequency : Point =>
      constant * ((1 + ‖frequency‖) ^ degree * (1 + ‖frequency‖ ^ 2) ^ (-grade / 2))) 2
      (volume : Measure Point) :=
    (memLp_two_japaneseBracket_pow_mul_rpow dimension_lt).const_mul constant
  have weight_continuous : Continuous
      (fun frequency : Point => (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) :=
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow Point (-grade / 2)).1.continuous
  refine dominating.mono' (weight_continuous.aestronglyMeasurable.smul measurable) ?_
  filter_upwards with frequency
  have weight_nonneg : (0 : ℝ) ≤ (1 + ‖frequency‖ ^ 2) ^ (-grade / 2) :=
    Real.rpow_nonneg (by positivity) _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg weight_nonneg]
  calc (1 + ‖frequency‖ ^ 2) ^ (-grade / 2) * ‖transform frequency‖
      ≤ (1 + ‖frequency‖ ^ 2) ^ (-grade / 2) *
          (constant * (1 + ‖frequency‖) ^ degree) := by
        exact mul_le_mul_of_nonneg_left (polynomial frequency) weight_nonneg
    _ = constant * ((1 + ‖frequency‖) ^ degree *
          (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) := by ring

/-! ## The placement theorem -/

/--
**Placement at a finite grade.**

If the Fourier transform of `state` is represented — in the sense of pairing
against every Schwartz function — by a measurable function of polynomial growth
of degree `degree`, then `state` is a Sobolev function of grade `-grade` for
every `grade` with `finrank ℝ Point < 2 * (grade - degree)`.

The proof is mathlib's characterization `memSobolev_iff_exists_smulLeftCLM_fourier`
read backwards: membership at grade `-grade` asks for an `L²` function equal, as
a tempered distribution, to `(1 + ‖ξ‖²) ^ (-grade/2) · 𝓕 state`.  The candidate
is the pointwise product of the weight with `transform`, which is `L²` by the
weight estimate; and the identification is pointwise under the integral sign,
because multiplying the distribution by the weight is by definition multiplying
the *test function* by it, and a scalar can be moved across a `•` freely.
-/
theorem memSobolev_of_fourier_eq_integral {state : 𝓢'(Point, Value)}
    {transform : Point → Value} {degree : ℕ} {grade constant : ℝ}
    (dimension_lt : (Module.finrank ℝ Point : ℝ) < 2 * (grade - degree))
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ degree)
    (represents : ∀ test : 𝓢(Point, ℂ),
      𝓕 state test = ∫ frequency : Point, test frequency • transform frequency) :
    MemSobolev (-grade) 2 state := by
  have weighted : MemLp (fun frequency : Point =>
      ((1 + ‖frequency‖ ^ 2) ^ (-grade / 2) : ℝ) • transform frequency) 2
      (volume : Measure Point) :=
    memLp_two_besselWeight_smul dimension_lt measurable polynomial
  have temperate : (fun frequency : Point =>
      (((1 + ‖frequency‖ ^ 2) ^ (-grade / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  refine memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨weighted.toLp _, ?_⟩
  ext test
  rw [smulLeftCLM_apply_apply, MeasureTheory.Lp.toTemperedDistribution_apply]
  have left : 𝓕 state (SchwartzMap.smulLeftCLM ℂ
      (fun frequency : Point => (((1 + ‖frequency‖ ^ 2) ^ (-grade / 2) : ℝ) : ℂ)) test) =
      ∫ frequency : Point,
        ((((1 + ‖frequency‖ ^ 2) ^ (-grade / 2) : ℝ) : ℂ) * test frequency) •
          transform frequency := by
    rw [represents]
    refine integral_congr_ae (Filter.Eventually.of_forall fun frequency => ?_)
    simp only [SchwartzMap.smulLeftCLM_apply_apply temperate, smul_eq_mul]
  rw [left]
  refine integral_congr_ae ?_
  filter_upwards [weighted.coeFn_toLp] with frequency pointwise
  rw [pointwise, smul_comm, ← Complex.coe_smul, smul_smul]

/-- **Some grade exists.**  Specializing the placement theorem to a grade that
clears the dimension budget: `degree + finrank ℝ Point` always does. -/
theorem exists_memSobolev_of_fourier_eq_integral {state : 𝓢'(Point, Value)}
    {transform : Point → Value} {degree : ℕ} {constant : ℝ}
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ degree)
    (represents : ∀ test : 𝓢(Point, ℂ),
      𝓕 state test = ∫ frequency : Point, test frequency • transform frequency) :
    ∃ grade : ℝ, MemSobolev grade 2 state := by
  refine ⟨-((degree : ℝ) + (Module.finrank ℝ Point : ℝ) + 1), ?_⟩
  refine memSobolev_of_fourier_eq_integral ?_ measurable polynomial represents
  have dimension_nonneg : (0 : ℝ) ≤ (Module.finrank ℝ Point : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The consequence the graded interface wants.**  The state inhabits the
graded carrier `Bessel.sobolev` at some grade, which is exactly the hypothesis a
`ComponentEllipticOperator` needs before it can accept a local component. -/
theorem mem_sobolev_of_fourier_eq_integral {state : 𝓢'(Point, Value)}
    {transform : Point → Value} {degree : ℕ} {constant : ℝ}
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ degree)
    (represents : ∀ test : 𝓢(Point, ℂ),
      𝓕 state test = ∫ frequency : Point, test frequency • transform frequency) :
    ∃ grade : ℝ, state ∈ Bessel.sobolev (Point := Point) (Value := Value) grade := by
  obtain ⟨grade, member⟩ :=
    exists_memSobolev_of_fourier_eq_integral measurable polynomial represents
  exact ⟨grade, member⟩

end Vector

end Hypostructure.PDE.Solution.FiniteOrder
