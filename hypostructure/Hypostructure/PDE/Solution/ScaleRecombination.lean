import Hypostructure.PDE.Solution.SliceRestriction

/-!
# Leaving the spatial scale: spatial regularity plus a time derivative is isotropic regularity

`PDE/Solution/SliceRestriction.lean` bootstraps the spatial operator `1 − Δ_x`
and is explicit about the price: the gain it delivers is measured by the
**spatial** symbol `σ_x(ξ) = 1 + (2π)²‖ξ_x‖²`, and
`exists_norm_sq_gt_mul_spatialSymbol` shows that no constant converts that gain
into an isotropic one.  A consumer that only ever runs a spatial elliptic
recovery is therefore stuck at `SpatialSmoothOn`: it knows every spatial
derivative of its field, at one fixed isotropic grade, and it cannot do better,
because `u(x,t) = a(t)` is a counterexample to any improvement.

What breaks the deadlock is the **equation**.  An evolution equation says what
`∂_t u` is; and the missing direction is exactly the time direction.  This module
is the bookkeeping that turns "all spatial derivatives" plus "the time
derivative" into "all derivatives", and it is careful to keep every statement
window-local.

## The inequality

Write `A = ‖ξ_x‖²` for the squared spatial frequency and `t = ⟪ξ, e_t⟫` for the
time frequency, so that `‖ξ‖² = A + t²` (`norm_sq_eq_spaceFrequencySq_add`).  The
whole module rests on the single algebraic fact

> `σ_x(ξ) + (2π)² t² = 1 + (2π)²‖ξ‖² =: σ(ξ)`,

with `σ` — `combinedSymbol` below — a symbol whose every real power is temperate
for free, because it is `1 + ‖L ξ‖²` for the dilation `L = 2π · id`.  Since
`(2π)² ≥ 1` the isotropic Bessel symbol `1 + ‖ξ‖²` is bounded by `σ`, and so is
each of the two summands separately.  Consequently

> `⟨ξ⟩ · σ_x(ξ)^{1/2} ≤ σ(ξ)`  and  `⟨ξ⟩ · 2π|t| ≤ σ(ξ)`,

each by squaring and multiplying the two bounds.  Dividing by `σ` produces the
two **bounded** multipliers `spatialShare` and `timeShare` of this file, whose
defining property is the exact partition of unity

> `σ_x^{1/2} · spatialShare + (2πi t) · timeShare = ⟨ξ⟩`.

The left-hand side is *one spatial half-derivative applied to the state* plus
*the time derivative of the state*; the right-hand side is *one isotropic
derivative*.  The constant is one, and no regularization is needed: the
denominator `σ` never vanishes.

## What is proved

* `memSpatialSobolev_grade_add_one` — the multiplier statement: a state with
  spatial gain `gain + 1` at isotropic grade `grade`, whose time derivative has
  spatial gain `gain` at grade `grade`, has spatial gain `gain` at grade
  `grade + 1`.  The extra spatial half-derivative is what pays for the isotropic
  one, and the `gain` parameter is carried along because the induction below
  consumes it;
* `memSobolev_add_one_of_memSpatialSobolev` — the `gain = 0` reading, which is
  the statement in its plainest form: `Λ_x u ∈ H^grade` and `∂_t u ∈ H^grade`
  give `u ∈ H^{grade+1}`;
* `spatialSobolevOn_grade_add_one`, `sobolevOn_add_one_of_spatialSobolevOn` —
  the window-local versions.  The cutoff commutator costs nothing here: the
  Leibniz error `(∂_t χ) u` is a *plain* localization of `u`, which the spatial
  hypothesis already covers;
* `smoothOn_of_spatialSmoothOn_timeDerivIterate` — the induction.  It genuinely
  needs `∂_t^k`: the one-step lemma raises the isotropic grade only by spending
  a spatial gain, and the spatial gain at the *new* grade is not something
  spatial smoothness at the old grade supplies.  Carrying the whole tower
  `∂_t^k u` closes the loop, since the step consumes the tower at level `k + 1`
  and reproduces it at level `k`;
* `smoothOn_of_spatialSmoothOn_of_timeDeriv_smoothOn` — **the payoff**, in the
  shape a consumer has it: spatial smoothness of the state on a window, plus
  space–time smoothness of its time derivative there, give space–time smoothness
  of the state.  The tower is built inside the proof, because smoothness of
  `∂_t u` already contains smoothness of every `∂_t^k u` for `k ≥ 1`, and
  smoothness implies spatial smoothness by `spatialSmoothOn_of_smoothOn`.

Nothing here names an equation, a dimension or a physical quantity: the time
derivative is a hypothesis, and it is the caller's equation that supplies it.
-/

namespace Hypostructure.PDE.Solution.ScaleRecombination

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open Hypostructure.PDE.Solution.SliceRestriction
open scoped SchwartzMap ENNReal Real LineDeriv Laplacian ContDiff

universe uPoint uValue uIndex

/-! ## The combined symbol

`combinedSymbol` is the symbol that the spatial symbol and the squared time
frequency add up to.  It is written as `1 + ‖L ξ‖²` for the dilation `L = 2π·id`
for exactly the reason `spatialSymbol` is written that way in
`SliceRestriction`: mathlib proves `(1 + ‖·‖²)^r` temperate on an inner product
space, so every real power of `combinedSymbol` is temperate for free and the
reciprocal — the only one this module needs — comes at no cost.
-/

section Symbol

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The frequency scaled by `2π`, as a continuous linear map.  Writing the
dilation as a *linear map* is what makes every real power of `combinedSymbol`
temperate without any estimate. -/
noncomputable def scaledFrequency (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] : Point →L[ℝ] Point :=
  (2 * π) • ContinuousLinearMap.id ℝ Point

/-- The symbol that the spatial symbol and the squared time frequency add up to:
`σ(ξ) = 1 + (2π)²‖ξ‖²`.  It is the isotropic Bessel symbol with the Fourier
convention's `2π` put back in, and it dominates that symbol because `(2π)² ≥ 1`. -/
noncomputable def combinedSymbol (place : Point) : ℝ :=
  1 + ‖scaledFrequency Point place‖ ^ 2

theorem combinedSymbol_eq (place : Point) :
    combinedSymbol place = 1 + (2 * π) ^ 2 * ‖place‖ ^ 2 := by
  have apply_eq : scaledFrequency Point place = (2 * π) • place := by
    rw [scaledFrequency]
    simp
  rw [combinedSymbol, apply_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π), mul_pow]

theorem one_le_combinedSymbol (place : Point) : 1 ≤ combinedSymbol place := by
  have nonneg : 0 ≤ ‖scaledFrequency Point place‖ ^ 2 := sq_nonneg _
  rw [combinedSymbol]
  linarith

theorem combinedSymbol_pos (place : Point) : 0 < combinedSymbol place :=
  lt_of_lt_of_le zero_lt_one (one_le_combinedSymbol place)

/-- **The recombination identity.**  The spatial symbol and the squared time
frequency partition the combined symbol exactly — this is Pythagoras and nothing
else, and it is the reason the two multipliers below add up to one isotropic
derivative with constant one. -/
theorem spatialSymbol_add_timeFrequency_sq (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    spatialSymbol basis timeIndex place +
        (2 * π) ^ 2 * (inner ℝ place (basis timeIndex) : ℝ) ^ 2 =
      combinedSymbol place := by
  rw [spatialSymbol_eq, combinedSymbol_eq, norm_sq_eq_spaceFrequencySq_add basis timeIndex place]
  ring

/-- The isotropic Bessel symbol is dominated by the combined one, because the
Fourier convention's `2π` is at least one.  This is the only place the constant
`(2π)² ≥ 1` is used, and it is used with room to spare. -/
theorem besselSymbol_le_combinedSymbol (place : Point) :
    1 + ‖place‖ ^ 2 ≤ combinedSymbol place := by
  have scale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  rw [combinedSymbol_eq]
  nlinarith [sq_nonneg ‖place‖]

/-- Each summand of the partition is bounded by the whole, the spatial one. -/
theorem spatialSymbol_le_combinedSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    spatialSymbol basis timeIndex place ≤ combinedSymbol place := by
  have split := spatialSymbol_add_timeFrequency_sq basis timeIndex place
  nlinarith [sq_nonneg (inner ℝ place (basis timeIndex) : ℝ), sq_nonneg (2 * π)]

/-- Each summand of the partition is bounded by the whole, the time one. -/
theorem timeFrequency_sq_le_combinedSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    (2 * π) ^ 2 * (inner ℝ place (basis timeIndex) : ℝ) ^ 2 ≤ combinedSymbol place := by
  have split := spatialSymbol_add_timeFrequency_sq basis timeIndex place
  have positive := spatialSymbol_pos basis timeIndex place
  linarith

/-- The reciprocal of the combined symbol, written as a real power so that its
temperate growth is mathlib's statement about `(1 + ‖·‖²)^r` composed with a
continuous linear map.  No regularization is needed: `combinedSymbol` is bounded
below by one, so its reciprocal is a genuine bounded multiplier. -/
noncomputable def combinedReciprocal (place : Point) : ℝ :=
  combinedSymbol place ^ (-1 : ℝ)

theorem combinedReciprocal_eq_inv (place : Point) :
    combinedReciprocal place = (combinedSymbol place)⁻¹ := by
  rw [combinedReciprocal, Real.rpow_neg_one]

theorem combinedReciprocal_pos (place : Point) : 0 < combinedReciprocal place :=
  Real.rpow_pos_of_pos (combinedSymbol_pos place) _

theorem combinedReciprocal_hasTemperateGrowth :
    (fun place : Point => ((combinedReciprocal place : ℝ) : ℂ)).HasTemperateGrowth := by
  have base : (fun frequency : Point => (1 + ‖frequency‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow Point (-1)
  have composed : Function.HasTemperateGrowth (fun place : Point => combinedReciprocal place) :=
    base.comp (scaledFrequency Point).hasTemperateGrowth
  exact Function.Complex.hasTemperateGrowth_ofReal.comp composed

end Symbol

/-! ## The two bounded shares

The isotropic weight `⟨ξ⟩` is split into the part the spatial scale carries and
the part the time derivative carries.  Both shares are bounded by **one**, which
is what makes the resulting Sobolev statement lossless.
-/

section Shares

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The share of one isotropic derivative carried by the spatial scale:
`⟨ξ⟩ σ_x^{1/2} / σ`.  It multiplies `Λ_x^{gain+1} u`, i.e. the state with one
spatial half-derivative more than the conclusion asks for. -/
noncomputable def spatialShare (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : ℂ :=
  ((besselWeight 1 place * spatialWeight basis timeIndex 1 place *
    combinedReciprocal place : ℝ) : ℂ)

/-- The share of one isotropic derivative carried by the time derivative:
`-i ⟨ξ⟩ (2π t) / σ`.  The factor `-i` undoes the `i` in the symbol of `∂_t`, so
that what is left is the real quantity whose size the partition controls. -/
noncomputable def timeShare (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : ℂ :=
  -Complex.I * ((besselWeight 1 place * (2 * π * (inner ℝ place (basis timeIndex) : ℝ)) *
    combinedReciprocal place : ℝ) : ℂ)

omit [DecidableEq Index] in
theorem spatialShare_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    (spatialShare basis timeIndex (Point := Point)).HasTemperateGrowth := by
  have factored : spatialShare basis timeIndex =
      ((fun place : Point => ((besselWeight 1 place : ℝ) : ℂ)) *
          fun place : Point => ((spatialWeight basis timeIndex 1 place : ℝ) : ℂ)) *
        fun place : Point => ((combinedReciprocal place : ℝ) : ℂ) := by
    funext place
    simp only [Pi.mul_apply, spatialShare]
    push_cast
    ring
  rw [factored]
  exact ((besselWeight_hasTemperateGrowth 1).mul
    (spatialWeight_hasTemperateGrowth basis timeIndex 1)).mul combinedReciprocal_hasTemperateGrowth

omit [DecidableEq Index] in
theorem timeShare_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    (timeShare basis timeIndex (Point := Point)).HasTemperateGrowth := by
  have inner_temperate : Function.HasTemperateGrowth
      (fun place : Point =>
        ((2 * π * (inner ℝ place (basis timeIndex) : ℝ) : ℝ) : ℂ)) := by
    have rewritten : (fun place : Point =>
        ((2 * π * (inner ℝ place (basis timeIndex) : ℝ) : ℝ) : ℂ)) =
          fun place : Point =>
            2 * (π : ℂ) * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ) := by
      funext place
      push_cast
      ring
    rw [rewritten]
    fun_prop
  have factored : timeShare basis timeIndex =
      ((fun _ : Point => -Complex.I) *
          fun place : Point => ((besselWeight 1 place : ℝ) : ℂ)) *
        ((fun place : Point => ((2 * π * (inner ℝ place (basis timeIndex) : ℝ) : ℝ) : ℂ)) *
          fun place : Point => ((combinedReciprocal place : ℝ) : ℂ)) := by
    funext place
    simp only [Pi.mul_apply, timeShare]
    push_cast
    ring
  have constant_temperate : Function.HasTemperateGrowth (fun _ : Point => -Complex.I) := by
    fun_prop
  rw [factored]
  exact (constant_temperate.mul (besselWeight_hasTemperateGrowth 1)).mul
    (inner_temperate.mul combinedReciprocal_hasTemperateGrowth)

/-- **The partition, with constant one.**  One spatial half-derivative of the
state plus the time derivative of the state reconstruct one isotropic derivative
of the state, and the two reconstruction multipliers are the shares above.

The computation is the recombination identity `σ_x + (2π t)² = σ` divided by `σ`;
the factor `i · (-i) = 1` is where the `-i` in `timeShare` earns its place. -/
theorem spatialWeight_mul_spatialShare_add_timeSymbol_mul_timeShare
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (place : Point) :
    ((spatialWeight basis timeIndex 1 place : ℝ) : ℂ) * spatialShare basis timeIndex place +
        2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ) *
          timeShare basis timeIndex place =
      ((besselWeight 1 place : ℝ) : ℂ) := by
  have square : spatialWeight basis timeIndex 1 place ^ 2 = spatialSymbol basis timeIndex place :=
    spatialWeight_one_sq basis timeIndex place
  have split := spatialSymbol_add_timeFrequency_sq basis timeIndex place
  have nonzero : combinedSymbol place ≠ 0 := (combinedSymbol_pos place).ne'
  have real_identity :
      spatialWeight basis timeIndex 1 place * (besselWeight 1 place *
            spatialWeight basis timeIndex 1 place * combinedReciprocal place) +
          2 * π * (inner ℝ place (basis timeIndex) : ℝ) *
            (besselWeight 1 place * (2 * π * (inner ℝ place (basis timeIndex) : ℝ)) *
              combinedReciprocal place) =
        besselWeight 1 place := by
    have expand :
        spatialWeight basis timeIndex 1 place * (besselWeight 1 place *
              spatialWeight basis timeIndex 1 place * combinedReciprocal place) +
            2 * π * (inner ℝ place (basis timeIndex) : ℝ) *
              (besselWeight 1 place * (2 * π * (inner ℝ place (basis timeIndex) : ℝ)) *
                combinedReciprocal place) =
          besselWeight 1 place * combinedReciprocal place *
            (spatialWeight basis timeIndex 1 place ^ 2 +
              (2 * π) ^ 2 * (inner ℝ place (basis timeIndex) : ℝ) ^ 2) := by
      ring
    rw [expand, square, split, combinedReciprocal_eq_inv]
    field_simp
  have cast_identity := congrArg (fun value : ℝ => (value : ℂ)) real_identity
  push_cast at cast_identity
  rw [spatialShare, timeShare]
  push_cast
  linear_combination cast_identity -
    (4 * (π : ℂ) ^ 2 * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ) ^ 2 *
      ((besselWeight 1 place : ℝ) : ℂ) * ((combinedReciprocal place : ℝ) : ℂ)) *
      Complex.I_mul_I

/-- The spatial share is bounded by one.  Squaring turns the claim into
`⟨ξ⟩² σ_x ≤ σ²`, which is the product of the two halves of the partition
bound — there is no constant to lose. -/
theorem norm_spatialShare_le_one (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : ‖spatialShare basis timeIndex place‖ ≤ 1 := by
  have weight_nonneg : (0 : ℝ) ≤ besselWeight 1 place := besselWeight_nonneg 1 place
  have spatial_nonneg : (0 : ℝ) ≤ spatialWeight basis timeIndex 1 place :=
    (spatialWeight_pos basis timeIndex 1 place).le
  have squares :
      (besselWeight 1 place * spatialWeight basis timeIndex 1 place) ^ 2 ≤
        combinedSymbol place ^ 2 := by
    rw [mul_pow, besselWeight_one_sq, spatialWeight_one_sq, pow_two (combinedSymbol place)]
    exact mul_le_mul (besselSymbol_le_combinedSymbol place)
      (spatialSymbol_le_combinedSymbol basis timeIndex place)
      (spatialSymbol_pos basis timeIndex place).le (combinedSymbol_pos place).le
  have bound : besselWeight 1 place * spatialWeight basis timeIndex 1 place ≤
      combinedSymbol place := by
    nlinarith [squares, mul_nonneg weight_nonneg spatial_nonneg, combinedSymbol_pos place]
  have nonneg : (0 : ℝ) ≤ besselWeight 1 place * spatialWeight basis timeIndex 1 place *
      combinedReciprocal place :=
    mul_nonneg (mul_nonneg weight_nonneg spatial_nonneg) (combinedReciprocal_pos place).le
  rw [spatialShare, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonneg,
    combinedReciprocal_eq_inv, ← div_eq_mul_inv, div_le_one (combinedSymbol_pos place)]
  exact bound

/-- The time share is bounded by one, for the same reason: squaring turns the
claim into `⟨ξ⟩² (2π t)² ≤ σ²`. -/
theorem norm_timeShare_le_one (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : ‖timeShare basis timeIndex place‖ ≤ 1 := by
  have weight_nonneg : (0 : ℝ) ≤ besselWeight 1 place := besselWeight_nonneg 1 place
  have squares :
      (besselWeight 1 place * |2 * π * (inner ℝ place (basis timeIndex) : ℝ)|) ^ 2 ≤
        combinedSymbol place ^ 2 := by
    have expand : (2 * π * (inner ℝ place (basis timeIndex) : ℝ)) ^ 2 =
        (2 * π) ^ 2 * (inner ℝ place (basis timeIndex) : ℝ) ^ 2 := by ring
    rw [mul_pow, besselWeight_one_sq, sq_abs, expand, pow_two (combinedSymbol place)]
    exact mul_le_mul (besselSymbol_le_combinedSymbol place)
      (timeFrequency_sq_le_combinedSymbol basis timeIndex place)
      (by positivity) (combinedSymbol_pos place).le
  have bound : besselWeight 1 place * |2 * π * (inner ℝ place (basis timeIndex) : ℝ)| ≤
      combinedSymbol place := by
    nlinarith [squares,
      mul_nonneg weight_nonneg (abs_nonneg (2 * π * (inner ℝ place (basis timeIndex) : ℝ))),
      combinedSymbol_pos place]
  have head : ‖timeShare basis timeIndex place‖ =
      |besselWeight 1 place * (2 * π * (inner ℝ place (basis timeIndex) : ℝ)) *
        combinedReciprocal place| := by
    rw [timeShare, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have absolute : |besselWeight 1 place * (2 * π * (inner ℝ place (basis timeIndex) : ℝ)) *
      combinedReciprocal place| =
        besselWeight 1 place * |2 * π * (inner ℝ place (basis timeIndex) : ℝ)| *
          combinedReciprocal place := by
    rw [abs_mul, abs_mul, abs_of_nonneg weight_nonneg,
      abs_of_nonneg (combinedReciprocal_pos place).le]
  rw [head, absolute, combinedReciprocal_eq_inv, ← div_eq_mul_inv,
    div_le_one (combinedSymbol_pos place)]
  exact bound

end Shares

/-! ## The multiplier statement

The partition is now fed to `MemSobolev.fourierMultiplierCLM_of_bounded` twice.
The `gain` parameter is carried through untouched: it is a spectator of the
identity, and the induction of the last section needs it to be one.
-/

section Scale

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- **One isotropic grade, bought with one spatial gain and one time
derivative.**

If `Λ_x^{gain+1} u ∈ H^grade` and `Λ_x^{gain} ∂_t u ∈ H^grade`, then
`Λ_x^{gain} u ∈ H^{grade+1}`.

This is the converse of `exists_norm_sq_gt_mul_spatialSymbol` in the only sense
in which a converse is available: the spatial symbol alone gains nothing
isotropically, but the spatial symbol *together with* the time direction gains
everything, because the two symbols partition the isotropic one.  Nothing is
lost in the transfer — both reconstruction multipliers have norm at most one. -/
theorem memSpatialSobolev_grade_add_one (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {gain grade : ℝ} {state : 𝓢'(Point, Value)}
    (spatial_member : MemSpatialSobolev basis timeIndex (gain + 1) grade state)
    (time_member : MemSpatialSobolev basis timeIndex gain grade (∂_{basis timeIndex} state)) :
    MemSpatialSobolev basis timeIndex gain (grade + 1) state := by
  classical
  set lineSymbol : Point → ℂ := fun place =>
    2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ) with lineSymbol_def
  have line_temperate : lineSymbol.HasTemperateGrowth := by
    rw [lineSymbol_def]
    fun_prop
  have spatial_eq :
      fourierMultiplierCLM Value (spatialShare basis timeIndex)
          (spatialPotential basis timeIndex (gain + 1) state) =
        fourierMultiplierCLM Value
          ((fun place : Point => ((spatialWeight basis timeIndex (gain + 1) place : ℝ) : ℂ)) *
            spatialShare basis timeIndex) state := by
    rw [spatialPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply
      (spatialWeight_hasTemperateGrowth basis timeIndex (gain + 1))
      (spatialShare_hasTemperateGrowth basis timeIndex)]
  have time_eq :
      fourierMultiplierCLM Value (timeShare basis timeIndex)
          (spatialPotential basis timeIndex gain (∂_{basis timeIndex} state)) =
        fourierMultiplierCLM Value
          ((lineSymbol *
              fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) *
            timeShare basis timeIndex) state := by
    rw [spatialPotential, lineDerivOp_eq_fourierMultiplierCLM, ← lineSymbol_def,
      fourierMultiplierCLM_fourierMultiplierCLM_apply line_temperate
        (spatialWeight_hasTemperateGrowth basis timeIndex gain),
      fourierMultiplierCLM_fourierMultiplierCLM_apply
        (line_temperate.mul (spatialWeight_hasTemperateGrowth basis timeIndex gain))
        (timeShare_hasTemperateGrowth basis timeIndex)]
  have bessel_apply :
      besselPotential Point Value 1 (spatialPotential basis timeIndex gain state) =
        fourierMultiplierCLM Value (fun place : Point => ((besselWeight 1 place : ℝ) : ℂ))
          (spatialPotential basis timeIndex gain state) := rfl
  have symbols :
      ((fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) *
          fun place : Point => ((besselWeight 1 place : ℝ) : ℂ)) =
        fun place : Point =>
          (((fun position : Point =>
                ((spatialWeight basis timeIndex (gain + 1) position : ℝ) : ℂ)) *
              spatialShare basis timeIndex) place) +
            (((lineSymbol *
                fun position : Point =>
                  ((spatialWeight basis timeIndex gain position : ℝ) : ℂ)) *
              timeShare basis timeIndex) place) := by
    funext place
    have partition :=
      spatialWeight_mul_spatialShare_add_timeSymbol_mul_timeShare basis timeIndex place
    have split : spatialWeight basis timeIndex (gain + 1) place =
        spatialWeight basis timeIndex gain place * spatialWeight basis timeIndex 1 place :=
      spatialWeight_add basis timeIndex gain 1 place
    simp only [Pi.mul_apply, lineSymbol_def, split]
    push_cast
    linear_combination (-((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) * partition
  have bessel_compose :
      besselPotential Point Value 1 (spatialPotential basis timeIndex gain state) =
        fourierMultiplierCLM Value
          ((fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) *
            fun place : Point => ((besselWeight 1 place : ℝ) : ℂ)) state := by
    rw [bessel_apply, spatialPotential,
      fourierMultiplierCLM_fourierMultiplierCLM_apply
        (spatialWeight_hasTemperateGrowth basis timeIndex gain)
        (besselWeight_hasTemperateGrowth 1)]
  have decomposition :
      besselPotential Point Value 1 (spatialPotential basis timeIndex gain state) =
        fourierMultiplierCLM Value (spatialShare basis timeIndex)
            (spatialPotential basis timeIndex (gain + 1) state) +
          fourierMultiplierCLM Value (timeShare basis timeIndex)
            (spatialPotential basis timeIndex gain (∂_{basis timeIndex} state)) := by
    rw [bessel_compose,
      symbols,
      Bessel.fourierMultiplier_add
        ((spatialWeight_hasTemperateGrowth basis timeIndex (gain + 1)).mul
          (spatialShare_hasTemperateGrowth basis timeIndex))
        ((line_temperate.mul (spatialWeight_hasTemperateGrowth basis timeIndex gain)).mul
          (timeShare_hasTemperateGrowth basis timeIndex)) state,
      ← spatial_eq, ← time_eq]
  have reorder : grade + 1 = 1 + grade := by ring
  show MemSobolev (grade + 1) 2 (spatialPotential basis timeIndex gain state)
  rw [reorder, ← memSobolev_besselPotential_iff, decomposition]
  refine MemSobolev.add ?_ ?_
  · exact MemSobolev.fourierMultiplierCLM_of_bounded spatial_member
      (spatialShare_hasTemperateGrowth basis timeIndex)
      ⟨1, norm_spatialShare_le_one basis timeIndex⟩
  · exact MemSobolev.fourierMultiplierCLM_of_bounded time_member
      (timeShare_hasTemperateGrowth basis timeIndex)
      ⟨1, norm_timeShare_le_one basis timeIndex⟩

/-- **The plain reading**, with no spatial gain left over: a state with one
spatial derivative at grade `grade` whose time derivative is at grade `grade`
sits at grade `grade + 1`.  This is `memSpatialSobolev_grade_add_one` at
`gain = 0`, and it is the statement a consumer recognizes. -/
theorem memSobolev_add_one_of_memSpatialSobolev (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {grade : ℝ} {state : 𝓢'(Point, Value)}
    (spatial_member : MemSpatialSobolev basis timeIndex 1 grade state)
    (time_member : MemSobolev grade 2 (∂_{basis timeIndex} state)) :
    MemSobolev (grade + 1) 2 state := by
  have gained : MemSpatialSobolev basis timeIndex 0 (grade + 1) state := by
    refine memSpatialSobolev_grade_add_one basis timeIndex (gain := 0) ?_ ?_
    · simpa using spatial_member
    · exact memSpatialSobolev_zero_iff.mpr time_member
  exact memSpatialSobolev_zero_iff.mp gained

end Scale

/-! ## The window-local statement

Localization is free here, which is worth saying explicitly.  The one place a
cutoff could cost something is the Leibniz error in `∂_t(χ u) = χ ∂_t u +
(∂_t χ) u`; but that error is a **plain** localization of `u` by another
admissible bump, and the spatial hypothesis already covers every such
localization.  Nothing is spent, and the local statement has exactly the same
shape as the global one.
-/

section LocalGain

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- **The local one-step gain in the isotropic grade.**  On a window, spatial
gain `gain + 1` for the state and spatial gain `gain` for its time derivative
give spatial gain `gain` at one isotropic grade more.

Everything is read through bumps supported in the window, so no hypothesis about
the state anywhere else is used or available. -/
theorem spatialSobolevOn_grade_add_one (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {gain grade : ℝ} {state : 𝓢'(Point, Value)}
    (spatial_held : SpatialSobolevOn basis timeIndex region (gain + 1) grade state)
    (time_held : SpatialSobolevOn basis timeIndex region gain grade
      (∂_{basis timeIndex} state)) :
    SpatialSobolevOn basis timeIndex region gain (grade + 1) state := by
  intro bump supported
  have deriv_supported : tsupport (bump.deriv (basis timeIndex)).weight ⊆ region :=
    (bump.tsupport_deriv_subset (basis timeIndex)).trans supported
  refine memSpatialSobolev_grade_add_one basis timeIndex (spatial_held bump supported) ?_
  rw [lineDerivOp_localize]
  exact MemSpatialSobolev.add (time_held bump supported)
    ((spatial_held (bump.deriv (basis timeIndex)) deriv_supported).mono_gain (by linarith))

/-- The `gain = 0` reading of the local gain, phrased entirely in the isotropic
local scale: one spatial derivative on the window plus a time derivative on the
window buy one isotropic grade there. -/
theorem sobolevOn_add_one_of_spatialSobolevOn (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (spatial_held : SpatialSobolevOn basis timeIndex region 1 grade state)
    (time_held : SobolevOn region grade (∂_{basis timeIndex} state)) :
    SobolevOn region (grade + 1) state := by
  refine (spatialSobolevOn_zero_iff (basis := basis) (timeIndex := timeIndex)).mp ?_
  refine spatialSobolevOn_grade_add_one basis timeIndex (gain := 0) ?_ ?_
  · simpa using spatial_held
  · exact spatialSobolevOn_zero_iff.mpr time_held

end LocalGain

/-! ## The iteration and the payoff

The one-step gain raises the isotropic grade only by **spending** a spatial gain,
and the spatial gain at the *new* grade is precisely what spatial smoothness at
the *old* grade does not supply — this is the isotropic obstruction again.  What
closes the loop is the tower of time derivatives: the step consumes the tower at
level `order + 1` and reproduces it at level `order`, so an induction that
quantifies over every level and every spatial gain goes through.

The user-facing theorem never mentions the tower, because smoothness of `∂_t u`
already contains smoothness of every `∂_t^k u` with `k ≥ 1`, and smoothness
implies spatial smoothness for free.
-/

section Payoff

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The tower of time derivatives, `∂_t^order`.  It appears only as the
induction's carrier: the user-facing payoff builds it from a single time
derivative. -/
noncomputable def timeDerivIterate (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (order : ℕ) (state : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  (fun current : 𝓢'(Point, Value) => ∂_{basis timeIndex} current)^[order] state

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] [DecidableEq Index] in
@[simp]
theorem timeDerivIterate_zero (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (state : 𝓢'(Point, Value)) : timeDerivIterate basis timeIndex 0 state = state := rfl

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] [DecidableEq Index] in
/-- Peeling the tower from the inside: this is the form the payoff uses, since
it turns a statement about `∂_t u` into one about every level. -/
theorem timeDerivIterate_succ_inner (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (order : ℕ) (state : 𝓢'(Point, Value)) :
    timeDerivIterate basis timeIndex (order + 1) state =
      timeDerivIterate basis timeIndex order (∂_{basis timeIndex} state) :=
  Function.iterate_succ_apply _ _ _

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] [DecidableEq Index] in
/-- Peeling the tower from the outside: this is the form the induction uses,
since the one-step gain asks for the time derivative of the current level. -/
theorem timeDerivIterate_succ_outer (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (order : ℕ) (state : 𝓢'(Point, Value)) :
    timeDerivIterate basis timeIndex (order + 1) state =
      ∂_{basis timeIndex} (timeDerivIterate basis timeIndex order state) :=
  Function.iterate_succ_apply' _ _ _

/-- Differentiating a state that is smooth on a window leaves it smooth there:
smoothness is *every* grade, and differentiating costs exactly one. -/
theorem smoothOn_lineDerivOp {region : Set Point} {state : 𝓢'(Point, Value)}
    (smooth : SmoothOn region state) (direction : Point) :
    SmoothOn region (∂_{direction} state) := by
  intro grade
  have shifted := (smooth (grade + 1)).lineDerivOp direction
  rwa [add_sub_cancel_right] at shifted

omit [DecidableEq Index] in
/-- Every level of the tower is smooth on the window as soon as the state is. -/
theorem smoothOn_timeDerivIterate (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {region : Set Point} {state : 𝓢'(Point, Value)} (smooth : SmoothOn region state) :
    ∀ order : ℕ, SmoothOn region (timeDerivIterate basis timeIndex order state) := by
  intro order
  induction order with
  | zero =>
      rw [timeDerivIterate_zero]
      exact smooth
  | succ previous gained =>
      rw [timeDerivIterate_succ_outer]
      exact smoothOn_lineDerivOp gained (basis timeIndex)

/-- **The induction.**  Spatial regularity of *every* order for *every* level of
the time tower, at one base grade, delivers spatial regularity of every order at
every whole grade above the base.

The step is `spatialSobolevOn_grade_add_one`: at level `order` it consumes the
inductive hypothesis at spatial gain `gain + 1` and, for the time derivative, the
inductive hypothesis at level `order + 1`.  The tower is what makes the second
call legal, and it is the honest price of leaving the spatial scale. -/
theorem spatialSobolevOn_grade_natCast (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (held : ∀ (order : ℕ) (gain : ℝ), SpatialSobolevOn basis timeIndex region gain grade
      (timeDerivIterate basis timeIndex order state)) :
    ∀ (step order : ℕ) (gain : ℝ), SpatialSobolevOn basis timeIndex region gain
      (grade + step) (timeDerivIterate basis timeIndex order state) := by
  intro step
  induction step with
  | zero =>
      intro order gain
      simpa using held order gain
  | succ previous gained =>
      intro order gain
      have time_held : SpatialSobolevOn basis timeIndex region gain (grade + previous)
          (∂_{basis timeIndex} (timeDerivIterate basis timeIndex order state)) := by
        have next := gained (order + 1) gain
        rwa [timeDerivIterate_succ_outer] at next
      have advanced := spatialSobolevOn_grade_add_one basis timeIndex
        (gained order (gain + 1)) time_held
      have rewrite : grade + (previous : ℝ) + 1 = grade + ((previous + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rwa [rewrite] at advanced

/-- **The payoff, in tower form.**  Spatial smoothness on a window of every time
derivative of the state, all at one base grade, gives space–time smoothness of
the state on that window. -/
theorem smoothOn_of_spatialSmoothOn_timeDerivIterate (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (held : ∀ order : ℕ, SpatialSmoothOn basis timeIndex region grade
      (timeDerivIterate basis timeIndex order state)) :
    SmoothOn region state := by
  intro target
  obtain ⟨step, step_ge⟩ := exists_nat_ge (target - grade)
  have reached := spatialSobolevOn_grade_natCast basis timeIndex
    (fun order gain => held order gain) step 0 0
  rw [timeDerivIterate_zero] at reached
  exact (spatialSobolevOn_zero_iff.mp reached).mono_grade (by linarith)

/-- **The payoff.**

A state that is spatially smooth on a window — the strongest conclusion a purely
spatial elliptic recovery can produce, by
`SliceRestriction.exists_norm_sq_gt_mul_spatialSymbol` — and whose **time
derivative** is space–time smooth there is itself space–time smooth there.

This is the theorem an evolution equation is consumed through: the equation is
what supplies `∂_t u`, and the spatial recovery is what supplies the rest.
Neither hypothesis alone suffices, and neither is weakened here: the isotropic
grade is gained one unit at a time, with constant one, from the exact partition
`σ_x + (2π t)² = 1 + (2π)²‖ξ‖²`.

Both hypotheses and the conclusion are read only through bumps supported in the
window; nothing about the state outside it is used. -/
theorem smoothOn_of_spatialSmoothOn_of_timeDeriv_smoothOn
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) {region : Set Point}
    {grade : ℝ} {state : 𝓢'(Point, Value)}
    (spatial_smooth : SpatialSmoothOn basis timeIndex region grade state)
    (time_smooth : SmoothOn region (∂_{basis timeIndex} state)) :
    SmoothOn region state := by
  refine smoothOn_of_spatialSmoothOn_timeDerivIterate basis timeIndex (grade := grade) ?_
  intro order
  match order with
  | 0 =>
      rw [timeDerivIterate_zero]
      exact spatial_smooth
  | (previous + 1) =>
      rw [timeDerivIterate_succ_inner]
      exact spatialSmoothOn_of_smoothOn basis timeIndex grade
        (smoothOn_timeDerivIterate basis timeIndex time_smooth previous)

/-- **The payoff on nested windows**, in the shape a residual carrying a nested
pair of balls consumes: the hypotheses are asked for on the outer ball and the
conclusion is delivered on the inner one. -/
theorem smoothOn_ball_of_spatialSmoothOn_of_timeDeriv_smoothOn
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (center : Point)
    {innerRadius outerRadius : ℝ} (nested : innerRadius ≤ outerRadius) {grade : ℝ}
    {state : 𝓢'(Point, Value)}
    (spatial_smooth : SpatialSmoothOn basis timeIndex (ball center outerRadius) grade state)
    (time_smooth : SmoothOn (ball center outerRadius) (∂_{basis timeIndex} state)) :
    SmoothOn (ball center innerRadius) state :=
  (smoothOn_of_spatialSmoothOn_of_timeDeriv_smoothOn basis timeIndex spatial_smooth
    time_smooth).mono_region (ball_subset_ball nested)

end Payoff

end Hypostructure.PDE.Solution.ScaleRecombination
