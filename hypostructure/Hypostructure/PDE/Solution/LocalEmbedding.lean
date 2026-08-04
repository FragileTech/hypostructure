import Hypostructure.PDE.Solution.InteriorRegularity

/-!
# The local Sobolev embedding: from `H^∞_loc` on a window to classical smoothness

`PDE/Solution/InteriorRegularity.lean` ends with `SmoothOn region state` — *the
state sits at every real grade on the window*.  That is the `H^∞_loc` reading of
smoothness, and it is the strongest conclusion a purely `L²`-based elliptic
bootstrap can reach.  It is however still a statement about a **distribution**:
nothing in it says that the state is a function, let alone a differentiable one.

This module closes that last gap.  It produces, from `SmoothOn`, an honest
`ContDiff ℝ ∞` function together with the statement that this function
*represents* the state on the window — i.e. testing the state against any test
function supported there is integration against the representative.

## The route

Three ingredients, in this order.

1. **The cutoff reduction.**  `SobolevOn` quantifies over *every* bump supported
   in the window, so a single fixed cutoff `χ` supported in the window turns a
   local hypothesis into a *global* one: `χ • state` is a genuine element of the
   whole-space `H^grade` for every `grade`.  And `χ • state` agrees with `state`
   wherever `χ` is one, so nothing is lost on the inner window.  This is the same
   trick that made the interior bootstrap work, run once more, in the opposite
   direction: there it converted a global theorem into a local one, here it
   converts a local hypothesis into a global one.

2. **The global embedding, with weights.**  Mathlib's
   `TemperedDistribution.MemSobolev.fourier_memL1` says that a whole-space
   `H^s` distribution with `finrank ℝ E < 2 * s` has an `L¹` Fourier transform.
   That gives boundedness and continuity but no derivatives.  Gaining `k`
   derivatives costs `k` grades, and the honest form of that bookkeeping is a
   *weighted* `L¹` bound: at grade `s` with `finrank ℝ E < 2 * (s - k)` the
   Fourier transform satisfies `‖ξ‖ ^ k * ‖𝓕 state ξ‖ ∈ L¹`.  That statement is
   proved here (`integrable_norm_pow_mul_norm_of_memSobolev`) by rerunning
   mathlib's own Cauchy–Schwarz split with the monomial `‖ξ‖ ^ k` absorbed into
   the decaying factor; mathlib proves only the unweighted case.

   Since `SmoothOn` supplies *every* grade, every `k` is available at once, and
   `Real.contDiff_fourier` — which asks exactly for `‖ξ‖ ^ n * ‖f ξ‖` integrable
   for all `n` — returns `ContDiff ℝ ∞` outright, not merely `C^k`.

3. **Fourier inversion at the level of pairings.**  Knowing that `𝓕 state` is an
   `L¹` function is not yet knowing that `state` is the smooth function
   `𝓕⁻ (𝓕 state)`; the two are related by the multiplication formula
   `∫ 𝓕 f · g = ∫ f · 𝓕 g` (mathlib's
   `VectorFourier.integral_fourierIntegral_smul_eq_flip`, which needs only
   integrability).  Applying it to the `L¹` Fourier data and a test function
   turns the abstract pairing `state test` into the concrete integral
   `∫ test · representative`.

## What is proved

* `memLp_two_weightedDecay` — the elementary weight estimate: the monomial
  `‖ξ‖ ^ k` times the Bessel decay `(1 + ‖ξ‖²) ^ (-s/2)` is square integrable
  exactly when `finrank ℝ E < 2 * (s - k)`.  This is the arithmetic that
  converts grades into derivatives;
* `integrable_norm_pow_mul_norm_of_memSobolev` — the weighted global embedding;
* `contDiff_fourierInv_of_integrable` — every-order weighted `L¹` Fourier data
  gives a genuinely `C^∞` inverse transform;
* `apply_eq_integral_fourierInv` — the inversion at the level of pairings;
* `exists_contDiff_representative_of_memSobolev` — the **global** embedding:
  a distribution at every grade is a smooth function;
* `exists_contDiff_representative_of_smoothOn` and
  `exists_contDiff_representative_of_laplacian_smoothOn` — the **local** payoff:
  a state smooth on a window (respectively, whose Laplacian is smooth on a
  window) agrees on a smaller window with a `ContDiff ℝ ∞` function.

Nothing here names an equation, a dimension, a boundary condition or a physical
quantity.
-/

namespace Hypostructure.PDE.Solution.LocalEmbedding

open MeasureTheory Metric TemperedDistribution FourierTransform
open Hypostructure.PDE.Solution.InteriorRegularity
open scoped SchwartzMap ENNReal ContDiff Laplacian

universe uPoint uValue uIndex

/-! ## The weight estimate

Everything about how many grades a derivative costs is contained in one
inequality: the monomial `‖ξ‖ ^ order` is dominated by the Japanese bracket
`(1 + ‖ξ‖²) ^ (order/2)`, so multiplying the Bessel decay of grade `grade` by
that monomial simply lowers the grade by `order`.  Square integrability of the
result is then mathlib's `integrable_rpow_neg_one_add_norm_sq`, at the reduced
grade.
-/

section Weight

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]

/-- **The weight estimate.**  `‖ξ‖ ^ order * (1 + ‖ξ‖²) ^ (-grade/2)` is square
integrable as soon as `finrank ℝ Point < 2 * (grade - order)`.

The `order` monomial is exactly the price of `order` derivatives: it eats
`order` grades and nothing more.  With `order = 0` this is the estimate mathlib
performs inline inside `MemSobolev.fourier_memL1`; the point of isolating it is
that the same proof carries the monomial for free. -/
theorem memLp_two_weightedDecay {order : ℕ} {grade : ℝ}
    (dimension_lt : (Module.finrank ℝ Point : ℝ) < 2 * (grade - order)) :
    MemLp (fun frequency : Point =>
        ‖frequency‖ ^ order * (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) 2
      (volume : Measure Point) := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  have decay : Integrable (fun frequency : Point =>
      (1 + ‖frequency‖ ^ 2) ^ (-(2 * (grade - (order : ℝ))) / 2)) (volume : Measure Point) :=
    integrable_rpow_neg_one_add_norm_sq dimension_lt
  refine decay.mono' (by fun_prop) ?_
  filter_upwards with frequency
  have base_pos : (0 : ℝ) < 1 + ‖frequency‖ ^ 2 := by positivity
  have square :
      (‖frequency‖ ^ order * (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) ^ 2 =
        ‖frequency‖ ^ (order * 2) * (1 + ‖frequency‖ ^ 2) ^ (-grade) := by
    rw [mul_pow, ← pow_mul, ← Real.rpow_natCast ((1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) 2,
      ← Real.rpow_mul base_pos.le]
    congr 2
    push_cast
    ring
  have monomial_le :
      ‖frequency‖ ^ (order * 2) ≤ (1 + ‖frequency‖ ^ 2) ^ ((order : ℝ)) := by
    rw [Real.rpow_natCast, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) order
  have collapse :
      (1 + ‖frequency‖ ^ 2) ^ ((order : ℝ)) * (1 + ‖frequency‖ ^ 2) ^ (-grade) =
        (1 + ‖frequency‖ ^ 2) ^ (-(2 * (grade - (order : ℝ))) / 2) := by
    rw [← Real.rpow_add base_pos]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), square, ← collapse]
  exact mul_le_mul_of_nonneg_right monomial_le (Real.rpow_nonneg base_pos.le _)

end Weight

/-! ## The weighted global embedding

Mathlib's `MemSobolev.fourier_memL1` produces *some* `L¹` representative of the
Fourier transform.  The weighted bound below is proved for *any* such
representative: two `L¹` functions inducing the same tempered distribution are
equal (mathlib's `Lp.ker_toTemperedDistributionCLM_eq_bot`), so it is enough to
verify the bound for the explicit representative that the Cauchy–Schwarz split
produces, and then transport it.  Stating it for an arbitrary representative is
what lets a single representative serve every order at once.
-/

section GlobalEmbedding

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]

/-- **The weighted global embedding.**  A whole-space state at grade `grade`
whose Fourier transform is represented by the `L¹` function `transform`
satisfies the weighted bound `‖ξ‖ ^ order * ‖transform ξ‖ ∈ L¹`, provided
`finrank ℝ Point < 2 * (grade - order)`.

The proof is mathlib's own Cauchy–Schwarz split, carrying the monomial: the
Fourier transform factors as (Bessel profile at grade `grade`, which is `L²` by
definition of the Sobolev space) times (Bessel decay of grade `grade`, which is
`L²` by the weight estimate — even after multiplication by `‖ξ‖ ^ order`), and a
product of two `L²` functions is `L¹`. -/
theorem integrable_norm_pow_mul_norm_of_memSobolev {order : ℕ} {grade : ℝ}
    (dimension_lt : (Module.finrank ℝ Point : ℝ) < 2 * (grade - order))
    {state : 𝓢'(Point, Value)} (member : MemSobolev grade 2 state)
    (transform : Lp Value 1 (volume : Measure Point))
    (represents : 𝓕 state = (transform : 𝓢'(Point, Value))) :
    Integrable (fun frequency : Point => ‖frequency‖ ^ order * ‖transform frequency‖)
      (volume : Measure Point) := by
  obtain ⟨profile, profile_eq⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp member
  have grade_gt : (Module.finrank ℝ Point : ℝ) < 2 * grade := by
    have : (0 : ℝ) ≤ (order : ℝ) := Nat.cast_nonneg order
    linarith
  have decay_real : MemLp (fun frequency : Point =>
      (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) 2 (volume : Measure Point) := by
    have zeroth := memLp_two_weightedDecay (Point := Point) (order := 0) (grade := grade)
      (by push_cast; linarith)
    simpa using zeroth
  have decay : MemLp (fun frequency : Point =>
      (Complex.ofReal ((1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) : ℂ)) 2
      (volume : Measure Point) := decay_real.ofReal
  -- The explicit representative built by the Cauchy–Schwarz split.
  set candidate : Lp Value 1 (volume : Measure Point) := decay.toLp _ • profile with candidate_def
  have candidate_represents : 𝓕 state = (candidate : 𝓢'(Point, Value)) := by
    rw [candidate_def, MeasureTheory.Lp.toTemperedDistribution_smul_eq]
    · rw [← profile_eq, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      convert! (smulLeftCLM_const 1 (𝓕 state)).symm using 1
      · simp
      · congr
        ext frequency
        rw [Pi.mul_apply]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
    · fun_prop
  -- Two `L¹` functions inducing the same distribution agree.
  have same : transform = candidate := by
    have injective := LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
        (F := Value) (μ := (volume : Measure Point)) (p := 1))
    refine injective ?_
    show MeasureTheory.Lp.toTemperedDistribution transform =
      MeasureTheory.Lp.toTemperedDistribution candidate
    rw [← represents, ← candidate_represents]
  -- The bound, for the explicit representative.
  have factorization : ∀ᵐ frequency : Point,
      ‖frequency‖ ^ order * ‖transform frequency‖ =
        (‖frequency‖ ^ order * (1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) * ‖profile frequency‖ := by
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (decay.toLp _) profile,
      decay.coeFn_toLp] with frequency pointwise scalar
    have expand : ((⇑(decay.toLp
        (fun frequency : Point => (Complex.ofReal ((1 + ‖frequency‖ ^ 2) ^ (-grade / 2)) : ℂ)))) •
          (⇑profile : Point → Value)) frequency =
        (⇑(decay.toLp _) : Point → ℂ) frequency • (⇑profile : Point → Value) frequency := rfl
    rw [same, candidate_def, pointwise, expand, scalar, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    ring
  refine Integrable.congr ?_ (Filter.EventuallyEq.symm factorization)
  have weight_member := memLp_two_weightedDecay (Point := Point) dimension_lt
  have profile_member : MemLp (fun frequency : Point => ‖profile frequency‖) 2
      (volume : Measure Point) := (MeasureTheory.Lp.memLp profile).norm
  exact weight_member.integrable_mul profile_member

omit [CompleteSpace Value] in
/-- **Smoothness from every-order weighted `L¹` Fourier data.**  If every
monomial weight `‖ξ‖ ^ order` keeps the transform integrable, then the inverse
Fourier transform is `C^∞`.

This is mathlib's `Real.contDiff_fourier` — which allows the smoothness
exponent `⊤` — composed with the reflection that turns `𝓕` into `𝓕⁻`. -/
theorem contDiff_fourierInv_of_integrable {transform : Point → Value}
    (weighted : ∀ order : ℕ,
      Integrable (fun frequency : Point => ‖frequency‖ ^ order * ‖transform frequency‖)
        (volume : Measure Point)) :
    ContDiff ℝ ∞ (𝓕⁻ transform) := by
  have forward : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕 transform) :=
    Real.contDiff_fourier fun order _ => weighted order
  have reflected : 𝓕⁻ transform = (𝓕 transform) ∘ fun place : Point => -place := by
    funext place
    simp [Real.fourierInv_eq_fourier_neg]
  rw [reflected]
  exact forward.comp contDiff_neg

/-! ### Inversion at the level of pairings

Knowing `𝓕 state = transform` with `transform` an `L¹` function does not by
itself say that `state` is the function `𝓕⁻ transform`: the left-hand side is a
pairing against test functions, the right-hand side an integral.  The bridge is
the multiplication formula, which mathlib proves under bare integrability
hypotheses — exactly what is available here.
-/

/-- Reflecting a test function through the origin gives a test function.  This
is only needed to feed the multiplication formula, which wants an integrable
function, and integrability of a Schwartz map is free. -/
theorem integrable_comp_neg (test : 𝓢(Point, ℂ)) :
    Integrable (fun place : Point => test (-place)) (volume : Measure Point) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
    (LinearIsometryEquiv.neg ℝ (E := Point)).toContinuousLinearEquiv test).integrable

/-- **Inversion at the level of pairings.**  A state whose Fourier transform is
an `L¹` function pairs with every test function as integration against the
inverse Fourier transform of that function.

The whole content is the multiplication formula `∫ 𝓕 f · g = ∫ f · 𝓕 g`, applied
to the reflected test function and the `L¹` Fourier data; the two reflections
cancel because Lebesgue measure is invariant under `x ↦ -x`. -/
theorem apply_eq_integral_fourierInv {state : 𝓢'(Point, Value)}
    (transform : Lp Value 1 (volume : Measure Point))
    (represents : 𝓕 state = (transform : 𝓢'(Point, Value)))
    (test : 𝓢(Point, ℂ)) :
    state test = ∫ place : Point, test place • (𝓕⁻ (⇑transform : Point → Value)) place := by
  have inverted : state = 𝓕⁻ (transform : 𝓢'(Point, Value)) := by
    rw [← represents, fourierInv_fourier_eq]
  have transform_integrable : Integrable (⇑transform : Point → Value)
      (volume : Measure Point) := MeasureTheory.L1.integrable_coeFn transform
  have pairing : state test = ∫ frequency : Point,
      (𝓕 (fun place : Point => test (-place))) frequency • transform frequency := by
    rw [inverted, TemperedDistribution.fourierInv_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun frequency => ?_)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg]
  have scalar_unfold : (𝓕 (fun place : Point => test (-place)) : Point → ℂ) =
      VectorFourier.fourierIntegral Real.fourierChar (volume : Measure Point) (innerₗ Point)
        (fun place : Point => test (-place)) := rfl
  have vector_unfold : (𝓕 (⇑transform : Point → Value)) =
      VectorFourier.fourierIntegral Real.fourierChar (volume : Measure Point) (innerₗ Point)
        (⇑transform : Point → Value) := rfl
  have flipped : ∫ frequency : Point,
      (𝓕 (fun place : Point => test (-place))) frequency • transform frequency =
        ∫ place : Point, test (-place) • (𝓕 (⇑transform : Point → Value)) place := by
    rw [scalar_unfold, vector_unfold]
    simpa only [flip_innerₗ] using
      VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ Point) (μ := (volume : Measure Point)) (ν := (volume : Measure Point))
        Real.continuous_fourierChar continuous_inner
        (integrable_comp_neg test) transform_integrable
  have reflect : ∫ place : Point, test place • (𝓕⁻ (⇑transform : Point → Value)) place =
      ∫ place : Point, test (-place) • (𝓕⁻ (⇑transform : Point → Value)) (-place) :=
    (MeasureTheory.integral_neg_eq_self
      (fun place : Point => test place • (𝓕⁻ (⇑transform : Point → Value)) place)
      (volume : Measure Point)).symm
  rw [pairing, flipped, reflect]
  refine integral_congr_ae (Filter.Eventually.of_forall fun place => ?_)
  simp only [Real.fourierInv_eq_fourier_neg, neg_neg]

/-- **The global embedding.**  A tempered distribution that sits at *every*
Sobolev grade is a `C^∞` function, in the precise sense that it pairs with every
test function as integration against one.

The grade budget is explicit: the representative is produced from grade
`finrank ℝ Point + 1`, and the `order`-th derivative is licensed by grade
`order + finrank ℝ Point + 1`.  Since every grade is available, every order is,
so the exponent is `∞` and not merely some finite `k`. -/
theorem exists_contDiff_representative_of_memSobolev {state : 𝓢'(Point, Value)}
    (member : ∀ grade : ℝ, MemSobolev grade 2 state) :
    ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ),
        state test = ∫ place : Point, test place • representative place := by
  have base_gt : (Module.finrank ℝ Point : ℝ) <
      2 * ((Module.finrank ℝ Point : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (Module.finrank ℝ Point : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨transform, transform_eq⟩ :=
    (member ((Module.finrank ℝ Point : ℝ) + 1)).fourier_memL1 base_gt
  refine ⟨𝓕⁻ (⇑transform : Point → Value), contDiff_fourierInv_of_integrable fun order => ?_,
    fun test => apply_eq_integral_fourierInv transform transform_eq test⟩
  refine integrable_norm_pow_mul_norm_of_memSobolev (order := order)
    (grade := (order : ℝ) + (Module.finrank ℝ Point : ℝ) + 1) ?_
    (member _) transform transform_eq
  have : (0 : ℝ) ≤ (Module.finrank ℝ Point : ℝ) := Nat.cast_nonneg _
  linarith

end GlobalEmbedding

/-! ## The local payoff

The cutoff reduction is the only new ingredient, and it is exactly the
observation that makes `SobolevOn` the right local space: since it quantifies
over *every* bump supported in the window, one particular bump — the framework's
cutoff, which is one on an inner ball — may be selected, and the cut-off state is
then a global Sobolev element of every grade agreeing with the state on that
inner ball.
-/

section LocalPayoff

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [HasContDiffBump Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- The framework's cutoff lives in the closed outer ball.  Complexification
does not change a support, and the closure of the open outer ball is contained
in the closed one. -/
theorem tsupport_cutoffBumpMultiplier_subset (center : Point) {innerRadius outerRadius : ℝ}
    (inner_pos : 0 < innerRadius) (nested : innerRadius < outerRadius) :
    tsupport (cutoffBumpMultiplier center inner_pos nested).weight ⊆
      closedBall center outerRadius := by
  have support_eq : Function.support
      (cutoffBumpMultiplier center inner_pos nested).weight = ball center outerRadius := by
    rw [← Localization.cutoff_support center inner_pos nested]
    ext place
    simp [cutoffBumpMultiplier, Function.mem_support]
  rw [tsupport, support_eq]
  exact closure_ball_subset_closedBall

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- Multiplying a test function supported in the inner ball by the framework's
cutoff changes nothing: the cutoff is one there, and outside the support of the
test function both sides vanish. -/
theorem smulLeftCLM_cutoffBumpMultiplier_eq (center : Point) {innerRadius outerRadius : ℝ}
    (inner_pos : 0 < innerRadius) (nested : innerRadius < outerRadius)
    (test : 𝓢(Point, ℂ)) (supported : tsupport (⇑test) ⊆ ball center innerRadius) :
    SchwartzMap.smulLeftCLM ℂ (cutoffBumpMultiplier center inner_pos nested).weight test =
      test := by
  have temperate := (cutoffBumpMultiplier center inner_pos nested).hasTemperateGrowth
  ext place
  by_cases mem : place ∈ tsupport (⇑test)
  · have one : (cutoffBumpMultiplier center inner_pos nested).weight place = 1 :=
      (cutoffBumpMultiplier_eventuallyEq_one center inner_pos nested
        (supported mem)).self_of_nhds
    simp [SchwartzMap.smulLeftCLM_apply_apply temperate, one]
  · simp [SchwartzMap.smulLeftCLM_apply_apply temperate,
      image_eq_zero_of_notMem_tsupport mem]

omit [HasContDiffBump Point] in
/-- **The cutoff reduction.**  A state smooth on a window, cut off by a bump
supported in that window, is a *global* Sobolev element of every grade.

This is the step that converts a local hypothesis into the global one the
whole-space embedding needs, and it is available only because `SobolevOn`
quantifies over all bumps. -/
theorem memSobolev_localize_of_smoothOn {region : Set Point} {state : 𝓢'(Point, Value)}
    (smooth : SmoothOn region state) (bump : Bump Point)
    (supported : tsupport bump.weight ⊆ region) (grade : ℝ) :
    MemSobolev grade 2 (localize bump state) :=
  smooth grade bump supported

/-- **The local Sobolev embedding.**  A state smooth on a window agrees, on
every strictly smaller concentric ball, with a genuinely `ContDiff ℝ ∞`
function.

"Agrees" is stated the only way it can be stated for an object that is a priori
a distribution: testing the state against any test function supported in the
inner ball is integration of that test function against the representative.
That is precisely what a classical regularity conclusion asserts, and it is what
a consumer needing classical derivatives will use.

The outer radius is where the cutoff is allowed to live; the hypothesis is that
the closed outer ball still sits inside the window on which smoothness is
known. -/
theorem exists_contDiff_representative_of_smoothOn {region : Set Point} (center : Point)
    {innerRadius outerRadius : ℝ} (inner_pos : 0 < innerRadius)
    (nested : innerRadius < outerRadius)
    (window : closedBall center outerRadius ⊆ region)
    {state : 𝓢'(Point, Value)} (smooth : SmoothOn region state) :
    ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center innerRadius →
        state test = ∫ place : Point, test place • representative place := by
  set cutoff := cutoffBumpMultiplier center inner_pos nested with cutoff_def
  have cutoff_supported : tsupport cutoff.weight ⊆ region :=
    (tsupport_cutoffBumpMultiplier_subset center inner_pos nested).trans window
  obtain ⟨representative, representative_smooth, representative_pairs⟩ :=
    exists_contDiff_representative_of_memSobolev
      (state := localize cutoff state)
      (fun grade => memSobolev_localize_of_smoothOn smooth cutoff cutoff_supported grade)
  refine ⟨representative, representative_smooth, fun test supported => ?_⟩
  have untouched : localize cutoff state test = state test := by
    rw [localize, TemperedDistribution.smulLeftCLM_apply_apply,
      smulLeftCLM_cutoffBumpMultiplier_eq center inner_pos nested test supported]
  rw [← untouched, representative_pairs test]

/--
**The bridge from `SmoothOn` to a classical smooth function**, phrased for two
concentric balls rather than for a window and a cutoff radius.

This is `exists_contDiff_representative_of_smoothOn` with the cutoff radius
chosen — the midpoint `(windowRadius + outerRadius) / 2`, which is the only
arithmetic in the proof.  A consumer that already knows `SmoothOn` on a ball and
wants a classical representative on a strictly smaller concentric ball should
reach for this form: it spends the gap between the two radii on the cutoff
itself, so nothing at the call site has to name a third radius.
-/
theorem exists_contDiff_representative_of_smoothOn_ball (center : Point)
    {windowRadius outerRadius : ℝ} (window_pos : 0 < windowRadius)
    (window_nested : windowRadius < outerRadius) {state : 𝓢'(Point, Value)}
    (smooth : SmoothOn (ball center outerRadius) state) :
    ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center windowRadius →
        state test = ∫ place : Point, test place • representative place := by
  refine exists_contDiff_representative_of_smoothOn center window_pos
    (show windowRadius < (windowRadius + outerRadius) / 2 by linarith) ?_ smooth
  intro place mem
  rw [mem_closedBall] at mem
  rw [mem_ball]
  linarith

/-- **The locally closed regularity statement.**  A state whose Laplacian is
smooth on a window, and which sits at *some* grade there, agrees on every
strictly smaller concentric ball with a `ContDiff ℝ ∞` function.

This composes the interior bootstrap of `PDE/Solution/InteriorRegularity.lean`
with the embedding proved here, and it is the form in which a local residual can
state its conclusion classically: the hypotheses are local and distributional,
the conclusion is a classical smooth function. -/
theorem exists_contDiff_representative_of_laplacian_smoothOn {Index : Type uIndex} [Fintype Index]
    (basis : OrthonormalBasis Index ℝ Point) {region : Set Point} (center : Point)
    {innerRadius outerRadius : ℝ} (inner_pos : 0 < innerRadius)
    (nested : innerRadius < outerRadius)
    (window : closedBall center outerRadius ⊆ region)
    {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source : SmoothOn region (Δ state)) :
    ∃ representative : Point → Value, ContDiff ℝ ∞ representative ∧
      ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ ball center innerRadius →
        state test = ∫ place : Point, test place • representative place :=
  exists_contDiff_representative_of_smoothOn center inner_pos nested window
    (smoothOn_of_laplacian_smoothOn basis state_held source)

end LocalPayoff

end Hypostructure.PDE.Solution.LocalEmbedding
