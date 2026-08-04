import Hypostructure.PDE.Solution.ParabolicRegularity

/-!
# Regularity in the spatial directions alone, and what it does *not* give

`PDE/Solution/InteriorRegularity.lean` bootstraps the **ambient** Laplacian
`Δ = ∑ᵢ ∂ᵢ∂ᵢ` of a `Point`; `PDE/Solution/ParabolicRegularity.lean` bootstraps
`∂_t − Δ_x`.  A consumer that works on a space–time window and recovers a field
from an elliptic identity in the *spatial* variables needs neither: it needs the
**spatial** Laplacian `Δ_x = ∑_{i ≠ t} ∂ᵢ∂ᵢ` alone.  Feeding one and the same
state to the ambient bootstrap and to a spatial one would force `Δ = Δ_x`, that
is `∂_t∂_t = 0`; so the spatial operator has to be bootstrapped on its own
terms.  This module does that, and it is careful about what "its own terms"
means.

## The accounting, verified rather than assumed

The shifted spatial operator is `1 − Δ_x`, whose symbol

> `σ_x(ξ) = 1 + (2π)²‖ξ_x‖²`

never vanishes — so, unlike the heat symbol, there is no need for a regularized
reciprocal: `σ_x^r` is a temperate multiplier for **every** real `r`, because
`σ_x = 1 + ‖L ξ‖²` for the continuous linear map `L = 2π·(1 − ⟪·,e_t⟫e_t)` and
mathlib proves `(1 + ‖·‖²)^r` temperate.  That is `spatialFrequency` and
`spatialWeight` below.

The gain, however, is **not** isotropic, and this is the point the module exists
to record honestly.  `σ_x` does not grow at all in the time direction:
`exists_norm_sq_gt_mul_spatialSymbol` exhibits, for every constant, a frequency
at which `1 + ‖ξ‖²` exceeds that constant times `σ_x(ξ)`.  So `1 − Δ_x` gains
**zero** isotropic Sobolev derivatives, and no amount of proof engineering can
change that: `u(x,t) = a(t)` has `Δ_x u = 0` smooth and `u` as rough as `a`.

What `1 − Δ_x` does gain is measured on the scale it is elliptic for.  Writing
`Λ_x^gain` for the Fourier multiplier `σ_x^{gain/2}` (`spatialPotential`), the
statements proved here are:

* `memSpatialSobolev_add_two` — **the whole-space gain is two spatial
  derivatives**: `Λ_x^{gain}(1 − Δ_x)u ∈ H^grade` gives `Λ_x^{gain+2}u ∈ H^grade`;
* `memSpatialSobolev_add_one_of_split` — **the same gain in localizable form**,
  where the shifted image is allowed to be a source at spatial order `gain − 1`
  plus **spatial** derivatives of fluxes at spatial order `gain`.  A spatial
  frequency is worth exactly one of the two available derivatives —
  `abs_inner_mul_spatialWeight_neg_one_le_one`, with constant one — so this form
  delivers `gain + 1`;
* `spatialSobolevOn_add_one` — **the local one-step gain**: one spatial
  derivative per step on a window.  The cutoff commutator spends one of the two
  the operator supplies, exactly as in the elliptic case, and the surviving
  derivative is kept *outside* a plain localization by the second-order Leibniz
  rule `spatialLaplacian_localize` of `ParabolicRegularity`;
* `spatialSobolevOn_natCast`, `spatialSmoothOn_of_spatialLaplacian_smoothOn`,
  `spatialSmoothOn_ball_of_spatialLaplacian_smoothOn`, `spatialSobolevOn_chain`
  — the iteration and the payoff, shaped exactly like
  `InteriorRegularity.smoothOn_ball_of_laplacian_smoothOn` and
  `ParabolicRegularity.smoothOn_ball_of_heat_smoothOn`, but landing in the
  spatial scale, which is the strongest true conclusion.

So the localized gain is **one spatial derivative per step**, and the whole-space
gain is **two spatial derivatives** — both stated on the spatial scale, and the
isotropic gain is zero.  The prediction "gain two, localize to one" is correct;
what has to be corrected is the scale on which it is true.

## Slice restriction

A genuine restriction operator `𝓢'(Point) → 𝓢'(slice)` is not built here: it
needs a Fubini theorem for tempered distributions, which mathlib does not have.
What is built is the statement such an operator would be used for, and it is
strictly about windows:

* `spatialSmoothOn_of_smoothOn` — space–time smoothness on a window implies
  spatial regularity of every order on that window, at every base grade.  This
  is the direction a caller consumes when a predecessor has already produced
  `SmoothOn`;
* `spatialSmoothOn_of_spatialLaplacian_smoothOn` — the converse-flavoured
  statement, and the one that is genuinely new: a state at *some* grade on a
  window whose **spatial** Laplacian is smooth there has every spatial
  derivative there, still at that base grade.  This is exactly what an elliptic
  recovery in the spatial variables can be asked to produce, and — by the
  isotropic obstruction above — it is exactly what it can produce.

Nothing here names an equation, a dimension, a boundary condition or a physical
quantity.
-/

namespace Hypostructure.PDE.Solution.SliceRestriction

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open scoped SchwartzMap ENNReal Real LineDeriv Laplacian ContDiff

universe uPoint uValue uIndex

/-! ## The spatial symbol, as a norm square of a linear map

The whole reason `1 − Δ_x` is easier than the heat operator is that its symbol
is a *positive* quantity of the form `1 + ‖L ξ‖²`.  Every power of it is then
temperate for free, and in particular the reciprocal is — so none of the
regularization machinery of `ParabolicRegularity` is needed.
-/

section Symbol

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The spatial part of a frequency, scaled by `2π`, as a continuous linear map.

Writing the spatial frequency as the image of a *linear map* is what makes every
real power of the spatial symbol temperate: mathlib proves `(1 + ‖·‖²)^r`
temperate on an inner product space, and a continuous linear map is temperate,
so the composite is. -/
noncomputable def spatialFrequency (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) : Point →L[ℝ] Point :=
  (2 * π) • (ContinuousLinearMap.id ℝ Point -
    (innerSL ℝ (basis timeIndex)).smulRight (basis timeIndex))

omit [DecidableEq Index] in
theorem spatialFrequency_apply (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    spatialFrequency basis timeIndex place =
      (2 * π) • (place - (inner ℝ place (basis timeIndex) : ℝ) • basis timeIndex) := by
  simp [spatialFrequency, real_inner_comm]

/-- The scaled spatial projection has exactly the squared spatial frequency as
its squared norm.  The computation is Pythagoras: subtracting the component
along the distinguished direction removes precisely that direction's square from
the total, and `norm_sq_eq_spaceFrequencySq_add` says the remainder is the
spatial sum. -/
theorem norm_spatialFrequency_sq (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    ‖spatialFrequency basis timeIndex place‖ ^ 2 =
      (2 * π) ^ 2 * spaceFrequencySq basis timeIndex place := by
  have unit : ‖basis timeIndex‖ = 1 := basis.orthonormal.1 timeIndex
  have pythagoras :
      ‖place - (inner ℝ place (basis timeIndex) : ℝ) • basis timeIndex‖ ^ 2 =
        ‖place‖ ^ 2 - (inner ℝ place (basis timeIndex) : ℝ) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, unit, Real.norm_eq_abs]
    have square : (|(inner ℝ place (basis timeIndex) : ℝ)| * 1) ^ 2 =
        (inner ℝ place (basis timeIndex) : ℝ) ^ 2 := by
      rw [mul_one, sq_abs]
    rw [square]
    ring
  rw [spatialFrequency_apply, norm_smul, mul_pow, pythagoras,
    norm_sq_eq_spaceFrequencySq_add basis timeIndex place, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π)]
  ring

/-- The symbol of `1 − Δ_x`.  It is written as `1 + ‖·‖²` of the scaled spatial
projection so that its temperate powers are immediate. -/
noncomputable def spatialSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℝ :=
  1 + ‖spatialFrequency basis timeIndex place‖ ^ 2

theorem spatialSymbol_eq (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) :
    spatialSymbol basis timeIndex place =
      1 + (2 * π) ^ 2 * spaceFrequencySq basis timeIndex place := by
  rw [spatialSymbol, norm_spatialFrequency_sq]

omit [DecidableEq Index] in
theorem one_le_spatialSymbol (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : 1 ≤ spatialSymbol basis timeIndex place := by
  have nonneg : 0 ≤ ‖spatialFrequency basis timeIndex place‖ ^ 2 := sq_nonneg _
  rw [spatialSymbol]
  linarith

omit [DecidableEq Index] in
theorem spatialSymbol_pos (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : 0 < spatialSymbol basis timeIndex place :=
  lt_of_lt_of_le zero_lt_one (one_le_spatialSymbol basis timeIndex place)

/-- **The isotropic obstruction.**  No constant makes `1 + ‖ξ‖²` dominated by
the spatial symbol: along the distinguished direction the spatial symbol is
identically one while the isotropic weight is unbounded.

This is why the module's conclusions are stated on the spatial scale and not on
the isotropic one.  It is the frequency-side form of the parasitic mode
`u(x,t) = a(t)`, which is killed by `Δ_x` and is exactly as rough as `a`. -/
theorem exists_norm_sq_gt_mul_spatialSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (bound : ℝ) :
    ∃ place : Point, bound * spatialSymbol basis timeIndex place < 1 + ‖place‖ ^ 2 := by
  classical
  set height : ℝ := |bound| + 1 with height_def
  refine ⟨height • basis timeIndex, ?_⟩
  have unit : ‖basis timeIndex‖ = 1 := basis.orthonormal.1 timeIndex
  have spatial_zero :
      spaceFrequencySq basis timeIndex (height • basis timeIndex) = 0 := by
    refine Finset.sum_eq_zero fun index member => ?_
    have different : index ≠ timeIndex := (Finset.mem_erase.mp member).1
    have orthogonal : (inner ℝ (basis timeIndex) (basis index) : ℝ) = 0 :=
      basis.orthonormal.2 (Ne.symm different)
    rw [real_inner_smul_left, orthogonal]
    simp
  have symbol_one : spatialSymbol basis timeIndex (height • basis timeIndex) = 1 := by
    rw [spatialSymbol_eq, spatial_zero]
    ring
  have height_pos : 0 < height := by
    rw [height_def]
    positivity
  have norm_eq : ‖height • basis timeIndex‖ = height := by
    rw [norm_smul, unit, Real.norm_eq_abs, abs_of_pos height_pos, mul_one]
  rw [symbol_one, norm_eq, mul_one, height_def]
  nlinarith [abs_nonneg bound, le_abs_self bound]

/-! ## The spatial Bessel weight

`spatialWeight gain` is `σ_x^{gain/2}`: the multiplier that measures `gain`
derivatives **in the spatial directions only**.  Three facts about it carry the
whole module: it is temperate for every real gain, it is multiplicative in the
gain, and one spatial frequency costs exactly one unit of gain.
-/

/-- The multiplier measuring `gain` spatial derivatives. -/
noncomputable def spatialWeight (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (gain : ℝ) (place : Point) : ℝ :=
  spatialSymbol basis timeIndex place ^ (gain / 2)

omit [DecidableEq Index] in
theorem spatialWeight_pos (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (gain : ℝ) (place : Point) : 0 < spatialWeight basis timeIndex gain place :=
  Real.rpow_pos_of_pos (spatialSymbol_pos basis timeIndex place) _

omit [DecidableEq Index] in
theorem one_le_spatialWeight (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {gain : ℝ} (gain_nonneg : 0 ≤ gain) (place : Point) :
    1 ≤ spatialWeight basis timeIndex gain place :=
  Real.one_le_rpow (one_le_spatialSymbol basis timeIndex place) (by linarith)

omit [DecidableEq Index] in
@[simp]
theorem spatialWeight_zero (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) : spatialWeight basis timeIndex 0 place = 1 := by
  rw [spatialWeight, zero_div, Real.rpow_zero]

omit [DecidableEq Index] in
@[simp]
theorem spatialWeight_two (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) :
    spatialWeight basis timeIndex 2 place = spatialSymbol basis timeIndex place := by
  rw [spatialWeight]
  norm_num

omit [DecidableEq Index] in
/-- Gains add, because the weight is a power of a single positive quantity.
This is what lets the scale be composed and inverted without any analysis. -/
theorem spatialWeight_add (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (first second : ℝ) (place : Point) :
    spatialWeight basis timeIndex (first + second) place =
      spatialWeight basis timeIndex first place * spatialWeight basis timeIndex second place := by
  rw [spatialWeight, spatialWeight, spatialWeight,
    show (first + second) / 2 = first / 2 + second / 2 by ring,
    Real.rpow_add (spatialSymbol_pos basis timeIndex place)]

omit [DecidableEq Index] in
/-- A non-positive gain is a contraction: the base is at least one. -/
theorem spatialWeight_le_one_of_nonpos (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {gain : ℝ} (gain_nonpos : gain ≤ 0) (place : Point) :
    spatialWeight basis timeIndex gain place ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_spatialSymbol basis timeIndex place)
    (by linarith)

omit [DecidableEq Index] in
theorem spatialWeight_one_sq (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) :
    spatialWeight basis timeIndex 1 place ^ 2 = spatialSymbol basis timeIndex place := by
  rw [spatialWeight, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (spatialSymbol_pos basis timeIndex place).le]
  norm_num

/-- **One spatial frequency costs exactly one unit of spatial gain**, with
constant one.  This is the estimate that makes the *localized* bootstrap gain:
the commutator leaves one derivative outside a localization, and the spatial
symbol absorbs it while still having one unit of gain to spare. -/
theorem abs_inner_mul_spatialWeight_neg_one_le_one
    (basis : OrthonormalBasis Index ℝ Point) {timeIndex index : Index}
    (different : index ≠ timeIndex) (place : Point) :
    |(inner ℝ place (basis index) : ℝ)| * spatialWeight basis timeIndex (-1) place ≤ 1 := by
  have frequency_le : |(inner ℝ place (basis index) : ℝ)| ≤
      spatialWeight basis timeIndex 1 place := by
    have squares : |(inner ℝ place (basis index) : ℝ)| ^ 2 ≤
        spatialWeight basis timeIndex 1 place ^ 2 := by
      rw [sq_abs, spatialWeight_one_sq, spatialSymbol_eq]
      have single := sq_inner_le_spaceFrequencySq basis different place
      have scale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [spaceFrequencySq_nonneg basis timeIndex place]
    nlinarith [abs_nonneg (inner ℝ place (basis index) : ℝ),
      (spatialWeight_pos basis timeIndex 1 place).le]
  have product :
      spatialWeight basis timeIndex 1 place * spatialWeight basis timeIndex (-1) place = 1 := by
    rw [← spatialWeight_add]
    norm_num
  nlinarith [(spatialWeight_pos basis timeIndex (-1) place).le]

/-- The spatial weight is dominated by the isotropic one, up to a constant.
Spatial frequencies are a *part* of the full frequency, so measuring `gain`
derivatives spatially asks strictly less than measuring `gain` isotropically —
which is why space–time smoothness delivers spatial regularity for free. -/
theorem spatialWeight_le_mul_besselWeight (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {gain : ℝ} (gain_nonneg : 0 ≤ gain) (place : Point) :
    spatialWeight basis timeIndex gain place ≤
      ((2 * π) ^ 2) ^ (gain / 2) * besselWeight gain place := by
  have scale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have split : spatialSymbol basis timeIndex place ≤ (2 * π) ^ 2 * (1 + ‖place‖ ^ 2) := by
    rw [spatialSymbol_eq]
    have spatial_le : spaceFrequencySq basis timeIndex place ≤ ‖place‖ ^ 2 := by
      rw [norm_sq_eq_spaceFrequencySq_add basis timeIndex place]
      nlinarith [sq_nonneg (inner ℝ place (basis timeIndex) : ℝ)]
    nlinarith [spaceFrequencySq_nonneg basis timeIndex place]
  calc spatialWeight basis timeIndex gain place
      ≤ ((2 * π) ^ 2 * (1 + ‖place‖ ^ 2)) ^ (gain / 2) :=
        Real.rpow_le_rpow (spatialSymbol_pos basis timeIndex place).le split (by linarith)
    _ = ((2 * π) ^ 2) ^ (gain / 2) * besselWeight gain place := by
        rw [besselWeight, Real.mul_rpow (by positivity) (by positivity)]

omit [DecidableEq Index] in
theorem spatialWeight_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (gain : ℝ) :
    (fun place : Point =>
      ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)).HasTemperateGrowth := by
  have base : (fun frequency : Point => (1 + ‖frequency‖ ^ 2) ^ (gain / 2)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow Point (gain / 2)
  have composed : Function.HasTemperateGrowth
      (fun place : Point => spatialWeight basis timeIndex gain place) :=
    base.comp (spatialFrequency basis timeIndex).hasTemperateGrowth
  exact Function.Complex.hasTemperateGrowth_ofReal.comp composed

/-- The reciprocal isotropic Bessel weight is temperate — it is the isotropic
weight of the opposite gain.  It is needed to *undo* an isotropic lift and
replace it by a spatial one. -/
theorem besselWeight_inv_hasTemperateGrowth (gain : ℝ) :
    (fun place : Point => (((besselWeight gain place)⁻¹ : ℝ) : ℂ)).HasTemperateGrowth := by
  have rewritten : (fun place : Point => (besselWeight gain place)⁻¹) =
      fun place : Point => (1 + ‖place‖ ^ 2) ^ (-(gain / 2)) := by
    funext place
    rw [besselWeight, ← Real.rpow_neg (by positivity)]
  refine Function.Complex.hasTemperateGrowth_ofReal.comp ?_
  rw [rewritten]
  exact Function.hasTemperateGrowth_one_add_norm_sq_rpow Point (-(gain / 2))

omit [DecidableEq Index] in
theorem spatialSymbol_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    (fun place : Point =>
      ((spatialSymbol basis timeIndex place : ℝ) : ℂ)).HasTemperateGrowth := by
  have rewritten : (fun place : Point => ((spatialSymbol basis timeIndex place : ℝ) : ℂ)) =
      fun place : Point => ((spatialWeight basis timeIndex 2 place : ℝ) : ℂ) := by
    funext place
    rw [spatialWeight_two]
  rw [rewritten]
  exact spatialWeight_hasTemperateGrowth basis timeIndex 2

end Symbol

/-! ## The operator and its symbol -/

section Operator

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The shifted spatial Laplacian `1 − Δ_x`.  Shifting is what removes the zero
of the symbol at zero spatial frequency; the unshifted `Δ_x` has no inverse,
because it kills everything constant in the spatial variables. -/
noncomputable def shiftedSpatialLaplacian (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (state : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  state - spatialLaplacian basis timeIndex state

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point] in
/-- The shifted symbol, split into the pieces the operator identity produces:
the constant `1` and one summand per spatial direction. -/
theorem spatialSymbol_eq_sum (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    (fun place : Point => ((spatialSymbol basis timeIndex place : ℝ) : ℂ)) =
      fun place => (1 : ℂ) +
        ∑ index ∈ Finset.univ.erase timeIndex,
          (2 * (π : ℂ)) ^ 2 * ((inner ℝ place (basis index) : ℝ) : ℂ) ^ 2 := by
  funext place
  rw [spatialSymbol_eq, spaceFrequencySq]
  push_cast
  rw [Finset.mul_sum]

/-- **The symbol of the shifted spatial Laplacian.**  `1 − Δ_x` is the Fourier
multiplier with symbol `1 + (2π)²‖ξ_x‖²`, a strictly positive real number. -/
theorem shiftedSpatialLaplacian_eq_fourierMultiplierCLM
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (state : 𝓢'(Point, Value)) :
    shiftedSpatialLaplacian basis timeIndex state =
      fourierMultiplierCLM Value
        (fun place => ((spatialSymbol basis timeIndex place : ℝ) : ℂ)) state := by
  classical
  set spacePart : Index → Point → ℂ := fun index place =>
    (2 * (π : ℂ)) ^ 2 * ((inner ℝ place (basis index) : ℝ) : ℂ) ^ 2 with spacePart_def
  have temperate_const : (fun _ : Point => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  have temperate_space :
      ∀ index ∈ Finset.univ.erase timeIndex, (spacePart index).HasTemperateGrowth := by
    intro index _
    rw [spacePart_def]
    fun_prop
  have temperate_sum :
      (fun place : Point => ∑ index ∈ Finset.univ.erase timeIndex,
        spacePart index place).HasTemperateGrowth :=
    Function.HasTemperateGrowth.sum temperate_space
  rw [spatialSymbol_eq_sum basis timeIndex,
    Bessel.fourierMultiplier_add temperate_const temperate_sum state,
    fourierMultiplierCLM_sum Value temperate_space]
  simp only [fourierMultiplierCLM_const, sum_apply, ContinuousLinearMap.id_apply, one_smul]
  simp only [← neg_lineDerivOp_two_eq_fourierMultiplierCLM, spacePart_def]
  rw [shiftedSpatialLaplacian, spatialLaplacian, Finset.sum_neg_distrib]
  abel

end Operator

/-! ## The spatial Sobolev scale -/

section Scale

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- `Λ_x^{gain}`: the Fourier multiplier `σ_x^{gain/2}`, which raises the spatial
regularity by `gain` and does nothing at all in the time direction. -/
noncomputable def spatialPotential (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (gain : ℝ) : 𝓢'(Point, Value) →L[ℂ] 𝓢'(Point, Value) :=
  fourierMultiplierCLM Value (fun place => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ))

omit [CompleteSpace Value] in
omit [DecidableEq Index] in
theorem spatialPotential_apply_zero (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (state : 𝓢'(Point, Value)) :
    spatialPotential basis timeIndex (Value := Value) 0 state = state := by
  have rewritten :
      (fun place : Point => ((spatialWeight basis timeIndex 0 place : ℝ) : ℂ)) =
        fun _ : Point => (1 : ℂ) := by
    funext place
    rw [spatialWeight_zero]
    norm_num
  rw [spatialPotential, rewritten]
  simp

omit [CompleteSpace Value] [DecidableEq Index] in
/-- Composing spatial potentials adds their gains: the scale is a genuine
one-parameter group, because the weight is a power of a single positive
quantity. -/
theorem spatialPotential_spatialPotential (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (first second : ℝ) (state : 𝓢'(Point, Value)) :
    spatialPotential basis timeIndex second (spatialPotential basis timeIndex first state) =
      spatialPotential basis timeIndex (first + second) state := by
  have symbols :
      ((fun place : Point => ((spatialWeight basis timeIndex first place : ℝ) : ℂ)) *
        fun place : Point => ((spatialWeight basis timeIndex second place : ℝ) : ℂ)) =
      fun place : Point => ((spatialWeight basis timeIndex (first + second) place : ℝ) : ℂ) := by
    funext place
    rw [Pi.mul_apply, spatialWeight_add]
    push_cast
    ring
  rw [spatialPotential, spatialPotential, spatialPotential,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      (spatialWeight_hasTemperateGrowth basis timeIndex first)
      (spatialWeight_hasTemperateGrowth basis timeIndex second), symbols]

/-- **`H^grade` after `gain` spatial derivatives.**  This is the scale the
spatial operator is elliptic for: `grade` measures isotropic regularity and is
never gained, `gain` measures spatial regularity and is what the bootstrap
increases. -/
def MemSpatialSobolev (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (gain grade : ℝ) (state : 𝓢'(Point, Value)) : Prop :=
  MemSobolev grade 2 (spatialPotential basis timeIndex gain state)

omit [DecidableEq Index] in
theorem memSpatialSobolev_zero_iff {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {grade : ℝ} {state : 𝓢'(Point, Value)} :
    MemSpatialSobolev basis timeIndex 0 grade state ↔ MemSobolev grade 2 state := by
  rw [MemSpatialSobolev, spatialPotential_apply_zero]

omit [DecidableEq Index] in
theorem MemSpatialSobolev.add {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
    {gain grade : ℝ} {first second : 𝓢'(Point, Value)}
    (first_member : MemSpatialSobolev basis timeIndex gain grade first)
    (second_member : MemSpatialSobolev basis timeIndex gain grade second) :
    MemSpatialSobolev basis timeIndex gain grade (first + second) := by
  rw [MemSpatialSobolev, map_add]
  exact MemSobolev.add first_member second_member

omit [DecidableEq Index] in
theorem MemSpatialSobolev.sub {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
    {gain grade : ℝ} {first second : 𝓢'(Point, Value)}
    (first_member : MemSpatialSobolev basis timeIndex gain grade first)
    (second_member : MemSpatialSobolev basis timeIndex gain grade second) :
    MemSpatialSobolev basis timeIndex gain grade (first - second) := by
  rw [MemSpatialSobolev, map_sub]
  exact MemSobolev.sub first_member second_member

omit [DecidableEq Index] in
theorem MemSpatialSobolev.smul {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
    {gain grade : ℝ} (scalar : ℂ) {state : 𝓢'(Point, Value)}
    (member : MemSpatialSobolev basis timeIndex gain grade state) :
    MemSpatialSobolev basis timeIndex gain grade (scalar • state) := by
  rw [MemSpatialSobolev, map_smul]
  exact MemSobolev.smul scalar member

omit [DecidableEq Index] in
theorem MemSpatialSobolev.sum {basis : OrthonormalBasis Index ℝ Point} {timeIndex : Index}
    {gain grade : ℝ} {family : Index → 𝓢'(Point, Value)} {support : Finset Index}
    (members : ∀ index ∈ support, MemSpatialSobolev basis timeIndex gain grade (family index)) :
    MemSpatialSobolev basis timeIndex gain grade (∑ index ∈ support, family index) := by
  rw [MemSpatialSobolev, map_sum]
  exact Bessel.mem_sobolev.mp
    (AddSubgroup.sum_mem _ fun index member => Bessel.mem_sobolev.mpr (members index member))

omit [DecidableEq Index] in
/-- Spatial gains are inherited downwards: the ratio of two spatial weights is a
weight of non-positive gain, hence bounded by one. -/
theorem MemSpatialSobolev.mono_gain {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {lower upper grade : ℝ} {state : 𝓢'(Point, Value)}
    (le : lower ≤ upper) (member : MemSpatialSobolev basis timeIndex upper grade state) :
    MemSpatialSobolev basis timeIndex lower grade state := by
  have decomposition :
      spatialPotential basis timeIndex lower state =
        fourierMultiplierCLM Value
          (fun place => ((spatialWeight basis timeIndex (lower - upper) place : ℝ) : ℂ))
          (spatialPotential basis timeIndex upper state) := by
    have symbols :
        ((fun place : Point => ((spatialWeight basis timeIndex upper place : ℝ) : ℂ)) *
          fun place : Point =>
            ((spatialWeight basis timeIndex (lower - upper) place : ℝ) : ℂ)) =
        fun place : Point => ((spatialWeight basis timeIndex lower place : ℝ) : ℂ) := by
      funext place
      rw [Pi.mul_apply, ← Complex.ofReal_mul, ← spatialWeight_add]
      norm_num
    rw [spatialPotential, spatialPotential,
      fourierMultiplierCLM_fourierMultiplierCLM_apply
        (spatialWeight_hasTemperateGrowth basis timeIndex upper)
        (spatialWeight_hasTemperateGrowth basis timeIndex (lower - upper)), symbols]
  rw [MemSpatialSobolev, decomposition]
  refine member.fourierMultiplierCLM_of_bounded
    (spatialWeight_hasTemperateGrowth basis timeIndex (lower - upper)) ⟨1, fun place => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (spatialWeight_pos basis timeIndex (lower - upper) place).le]
  exact spatialWeight_le_one_of_nonpos basis timeIndex (by linarith) place

omit [DecidableEq Index] in
theorem MemSpatialSobolev.mono_grade {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {gain lower grade : ℝ} {state : 𝓢'(Point, Value)}
    (le : lower ≤ grade) (member : MemSpatialSobolev basis timeIndex gain grade state) :
    MemSpatialSobolev basis timeIndex gain lower state :=
  MemSobolev.mono le member

/-- **Isotropic regularity is spatial regularity.**  A state at isotropic grade
`grade + gain` has `gain` spatial derivatives at grade `grade`, because a
spatial frequency is bounded by the full frequency.

This is the direction that costs nothing, and it is the one a caller uses when a
predecessor already delivered space–time smoothness. -/
theorem memSpatialSobolev_of_memSobolev {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {gain grade : ℝ} (gain_nonneg : 0 ≤ gain)
    {state : 𝓢'(Point, Value)} (member : MemSobolev (grade + gain) 2 state) :
    MemSpatialSobolev basis timeIndex gain grade state := by
  have lifted : MemSobolev grade 2 (besselPotential Point Value gain state) := by
    rw [memSobolev_besselPotential_iff]
    rwa [add_comm] at member
  have bessel_eq : besselPotential Point Value gain state =
      fourierMultiplierCLM Value (fun place : Point => ((besselWeight gain place : ℝ) : ℂ))
        state := rfl
  set ratio : Point → ℂ := fun place =>
    (((spatialWeight basis timeIndex gain place * (besselWeight gain place)⁻¹ : ℝ)) : ℂ)
    with ratio_def
  have ratio_temperate : ratio.HasTemperateGrowth := by
    have factored : ratio =
        (fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) *
          fun place : Point => (((besselWeight gain place)⁻¹ : ℝ) : ℂ) := by
      funext place
      rw [ratio_def]
      push_cast
      rfl
    rw [factored]
    exact (spatialWeight_hasTemperateGrowth basis timeIndex gain).mul
      (besselWeight_inv_hasTemperateGrowth gain)
  have decomposition :
      spatialPotential basis timeIndex gain state =
        fourierMultiplierCLM Value ratio (besselPotential Point Value gain state) := by
    have symbols :
        ((fun place : Point => ((besselWeight gain place : ℝ) : ℂ)) * ratio) =
          fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ) := by
      funext place
      have positive : (0 : ℝ) < besselWeight gain place :=
        Real.rpow_pos_of_pos (by positivity) _
      rw [Pi.mul_apply, ratio_def, ← Complex.ofReal_mul]
      field_simp
    rw [bessel_eq, spatialPotential,
      fourierMultiplierCLM_fourierMultiplierCLM_apply (besselWeight_hasTemperateGrowth gain)
        ratio_temperate, symbols]
  rw [MemSpatialSobolev, decomposition]
  refine lifted.fourierMultiplierCLM_of_bounded ratio_temperate
    ⟨((2 * π) ^ 2) ^ (gain / 2), fun place => ?_⟩
  have positive : (0 : ℝ) < besselWeight gain place :=
    Real.rpow_pos_of_pos (by positivity) _
  have bounded := spatialWeight_le_mul_besselWeight basis timeIndex gain_nonneg place
  have nonneg : (0 : ℝ) ≤
      spatialWeight basis timeIndex gain place * (besselWeight gain place)⁻¹ :=
    mul_nonneg (spatialWeight_pos basis timeIndex gain place).le (inv_nonneg.mpr positive.le)
  rw [ratio_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonneg,
    ← div_eq_mul_inv, div_le_iff₀ positive]
  exact bounded

/-! ## The whole-space gain: two spatial derivatives -/

omit [CompleteSpace Value] in
/-- Applying the shifted spatial Laplacian *is* a shift of the spatial scale by
exactly two.  Everything the module proves is bookkeeping around this one
identity, which holds because the operator's symbol is the square of the
scale's generator. -/
theorem spatialPotential_shiftedSpatialLaplacian (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (gain : ℝ) (state : 𝓢'(Point, Value)) :
    spatialPotential basis timeIndex gain (shiftedSpatialLaplacian basis timeIndex state) =
      spatialPotential basis timeIndex (gain + 2) state := by
  have symbols :
      ((fun place : Point => ((spatialSymbol basis timeIndex place : ℝ) : ℂ)) *
        fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) =
      fun place : Point => ((spatialWeight basis timeIndex (gain + 2) place : ℝ) : ℂ) := by
    funext place
    rw [Pi.mul_apply, ← spatialWeight_two, ← Complex.ofReal_mul, ← spatialWeight_add,
      add_comm (2 : ℝ) gain]
  rw [shiftedSpatialLaplacian_eq_fourierMultiplierCLM, spatialPotential, spatialPotential,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      (spatialSymbol_hasTemperateGrowth basis timeIndex)
      (spatialWeight_hasTemperateGrowth basis timeIndex gain), symbols]

/-- **The whole-space gain.**  `1 − Δ_x` gains exactly **two spatial
derivatives**: if its image sits at spatial order `gain`, the state sits at
spatial order `gain + 2`, at the same isotropic grade.

The isotropic grade is untouched, and by `exists_norm_sq_gt_mul_spatialSymbol`
it cannot be: the spatial symbol is bounded along the distinguished direction. -/
theorem memSpatialSobolev_add_two (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {gain grade : ℝ} {state : 𝓢'(Point, Value)}
    (source_member : MemSpatialSobolev basis timeIndex gain grade
      (shiftedSpatialLaplacian basis timeIndex state)) :
    MemSpatialSobolev basis timeIndex (gain + 2) grade state := by
  rw [MemSpatialSobolev, ← spatialPotential_shiftedSpatialLaplacian]
  exact source_member

/-- **The gain, in the form a localization can use.**

A cutoff commutator differentiates the state once, and a naive localization
would therefore spend one of the two derivatives on the state and gain only
one — which is what happens.  The point of this form is that the surviving
derivative sits *outside* a localization, so the question is how large the
multiplier `⟪ξ,eᵢ⟫·σ_x^{-1/2}` is; along a **spatial** direction it is bounded
by one (`abs_inner_mul_spatialWeight_neg_one_le_one`), so a source at spatial
order `gain − 1` and fluxes at spatial order `gain` deliver `gain + 1`.

One spatial derivative per step, honestly, and one per step reaches every
order. -/
theorem memSpatialSobolev_add_one_of_split (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {gain grade : ℝ} {state source : 𝓢'(Point, Value)}
    {flux : Index → 𝓢'(Point, Value)}
    (identity : shiftedSpatialLaplacian basis timeIndex state =
      source + ∑ index ∈ Finset.univ.erase timeIndex, ∂_{basis index} (flux index))
    (source_member : MemSpatialSobolev basis timeIndex (gain - 1) grade source)
    (flux_member : ∀ index ∈ Finset.univ.erase timeIndex,
      MemSpatialSobolev basis timeIndex gain grade (flux index)) :
    MemSpatialSobolev basis timeIndex (gain + 1) grade state := by
  have shift : spatialPotential basis timeIndex (gain - 1)
      (shiftedSpatialLaplacian basis timeIndex state) =
        spatialPotential basis timeIndex (gain + 1) state := by
    rw [spatialPotential_shiftedSpatialLaplacian,
      show gain - 1 + 2 = gain + 1 by ring]
  rw [MemSpatialSobolev, ← shift, identity, map_add, map_sum]
  refine MemSobolev.add source_member ?_
  refine Bessel.mem_sobolev.mp
    (AddSubgroup.sum_mem _ fun index member => Bessel.mem_sobolev.mpr ?_)
  have different : index ≠ timeIndex := (Finset.mem_erase.mp member).1
  set corrector : Point → ℂ := fun place =>
    (2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)) *
      ((spatialWeight basis timeIndex (-1) place : ℝ) : ℂ) with corrector_def
  have line_temperate : Function.HasTemperateGrowth
      (fun place : Point =>
        2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)) := by
    fun_prop
  have corrector_temperate : Function.HasTemperateGrowth corrector :=
    line_temperate.mul (spatialWeight_hasTemperateGrowth basis timeIndex (-1))
  have identity_index :
      spatialPotential basis timeIndex (gain - 1) (∂_{basis index} (flux index)) =
        fourierMultiplierCLM Value corrector
          (spatialPotential basis timeIndex gain (flux index)) := by
    have symbols :
        ((fun place : Point => ((spatialWeight basis timeIndex gain place : ℝ) : ℂ)) *
          corrector) =
        ((fun place : Point =>
            2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)) *
          fun place : Point =>
            ((spatialWeight basis timeIndex (gain - 1) place : ℝ) : ℂ)) := by
      funext place
      have real_eq : spatialWeight basis timeIndex gain place *
          spatialWeight basis timeIndex (-1) place =
            spatialWeight basis timeIndex (gain - 1) place := by
        rw [← spatialWeight_add, ← sub_eq_add_neg]
      have cast_eq : ((spatialWeight basis timeIndex gain place : ℝ) : ℂ) *
          ((spatialWeight basis timeIndex (-1) place : ℝ) : ℂ) =
            ((spatialWeight basis timeIndex (gain - 1) place : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, real_eq]
      simp only [Pi.mul_apply, corrector_def]
      linear_combination
        (2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)) * cast_eq
    rw [spatialPotential, spatialPotential,
      lineDerivOp_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_fourierMultiplierCLM_apply line_temperate
        (spatialWeight_hasTemperateGrowth basis timeIndex (gain - 1)),
      fourierMultiplierCLM_fourierMultiplierCLM_apply
        (spatialWeight_hasTemperateGrowth basis timeIndex gain) corrector_temperate,
      symbols]
  rw [identity_index]
  refine MemSobolev.fourierMultiplierCLM_of_bounded (flux_member index member)
    corrector_temperate ⟨2 * π, fun place => ?_⟩
  have head : ‖2 * (π : ℂ) * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)‖ =
      2 * π * |(inner ℝ place (basis index) : ℝ)| := by
    simp [abs_of_nonneg Real.pi_pos.le]
  have weight_norm : ‖((spatialWeight basis timeIndex (-1) place : ℝ) : ℂ)‖ =
      spatialWeight basis timeIndex (-1) place := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (spatialWeight_pos basis timeIndex (-1) place).le]
  simp only [corrector_def]
  rw [norm_mul, head, weight_norm]
  nlinarith [abs_inner_mul_spatialWeight_neg_one_le_one basis different place,
    Real.pi_pos, abs_nonneg (inner ℝ place (basis index) : ℝ),
    (spatialWeight_pos basis timeIndex (-1) place).le]

end Scale

/-! ## Localization

The commutator is the elliptic one restricted to the spatial directions, and it
is rearranged exactly as in `ParabolicRegularity`: every surviving derivative is
kept **outside** a plain localization, so that the gain lemma above can spend a
spatial frequency rather than a spatial derivative of the state.
-/

section Localization

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- **The spatial commutator, localized.**

`(1 − Δ_x)(χ u)` is `χ (1 − Δ_x) u` plus terms every one of which carries a
derivative of the cutoff, and the only terms that carry a derivative at all
carry it *outside* a localization of `u`, along a **spatial** direction. -/
theorem shiftedSpatialLaplacian_localize (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    shiftedSpatialLaplacian basis timeIndex (localize bump state) =
      (localize bump (shiftedSpatialLaplacian basis timeIndex state) +
          ∑ index ∈ Finset.univ.erase timeIndex,
            localize ((bump.deriv (basis index)).deriv (basis index)) state) +
        ∑ index ∈ Finset.univ.erase timeIndex,
          ∂_{basis index} ((-(2 : ℂ)) • localize (bump.deriv (basis index)) state) := by
  have derivative_smul : ∀ index : Index,
      ∂_{basis index} ((-(2 : ℂ)) • localize (bump.deriv (basis index)) state) =
        -((2 : ℂ) • ∂_{basis index} (localize (bump.deriv (basis index)) state)) := by
    intro index
    rw [LineDerivSMul.lineDerivOp_smul, neg_smul]
  simp only [shiftedSpatialLaplacian]
  rw [spatialLaplacian_localize, localize_sub]
  simp only [derivative_smul]
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  abel

end Localization

/-! ## The local scale, the one-step gain, and the payoff -/

section LocalGain

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- **`gain` spatial derivatives at isotropic grade `grade`, on a window.**  The
local companion of `MemSpatialSobolev`, and the exact analogue of
`InteriorRegularity.SobolevOn`: quantifying over every bump supported in the
region is what makes the commutator's new multipliers admissible for free. -/
def SpatialSobolevOn (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (region : Set Point) (gain grade : ℝ) (state : 𝓢'(Point, Value)) : Prop :=
  ∀ bump : Bump Point, tsupport bump.weight ⊆ region →
    MemSpatialSobolev basis timeIndex gain grade (localize bump state)

omit [DecidableEq Index] in
theorem SpatialSobolevOn.mono_region {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {smaller larger : Set Point} {gain grade : ℝ}
    {state : 𝓢'(Point, Value)} (subset : smaller ⊆ larger)
    (held : SpatialSobolevOn basis timeIndex larger gain grade state) :
    SpatialSobolevOn basis timeIndex smaller gain grade state :=
  fun bump supported => held bump (supported.trans subset)

omit [DecidableEq Index] in
theorem SpatialSobolevOn.mono_gain {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {region : Set Point} {lower upper grade : ℝ}
    {state : 𝓢'(Point, Value)} (le : lower ≤ upper)
    (held : SpatialSobolevOn basis timeIndex region upper grade state) :
    SpatialSobolevOn basis timeIndex region lower grade state :=
  fun bump supported => (held bump supported).mono_gain le

omit [DecidableEq Index] in
theorem SpatialSobolevOn.mono_grade {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {region : Set Point} {gain lower grade : ℝ}
    {state : 𝓢'(Point, Value)} (le : lower ≤ grade)
    (held : SpatialSobolevOn basis timeIndex region gain grade state) :
    SpatialSobolevOn basis timeIndex region gain lower state :=
  fun bump supported => (held bump supported).mono_grade le

omit [DecidableEq Index] in
theorem spatialSobolevOn_zero_iff {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)} :
    SpatialSobolevOn basis timeIndex region 0 grade state ↔ SobolevOn region grade state := by
  constructor
  · exact fun held bump supported => memSpatialSobolev_zero_iff.mp (held bump supported)
  · exact fun held bump supported => memSpatialSobolev_zero_iff.mpr (held bump supported)

/-- Isotropic regularity on a window is spatial regularity on that window: a
spatial frequency is part of the full frequency, so nothing has to be proved
beyond the multiplier comparison. -/
theorem spatialSobolevOn_of_sobolevOn {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {region : Set Point} {gain grade : ℝ} (gain_nonneg : 0 ≤ gain)
    {state : 𝓢'(Point, Value)} (held : SobolevOn region (grade + gain) state) :
    SpatialSobolevOn basis timeIndex region gain grade state :=
  fun bump supported => memSpatialSobolev_of_memSobolev gain_nonneg (held bump supported)

/-- **The local one-step gain.**  A state at spatial order `gain` on a window,
whose spatial Laplacian is at spatial order `gain − 1` there, sits at spatial
order `gain + 1`.

One spatial derivative per step: the operator supplies two and the cutoff
commutator spends one, exactly as in the elliptic bootstrap of
`InteriorRegularity`.  The isotropic grade is carried along unchanged, which is
the most that can be true. -/
theorem spatialSobolevOn_add_one (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {gain grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SpatialSobolevOn basis timeIndex region gain grade state)
    (source_held : SpatialSobolevOn basis timeIndex region (gain - 1) grade
      (spatialLaplacian basis timeIndex state)) :
    SpatialSobolevOn basis timeIndex region (gain + 1) grade state := by
  intro bump supported
  have deriv_supported : ∀ index : Index,
      tsupport (bump.deriv (basis index)).weight ⊆ region :=
    fun index => (bump.tsupport_deriv_subset (basis index)).trans supported
  have deriv_two_supported : ∀ index : Index,
      tsupport ((bump.deriv (basis index)).deriv (basis index)).weight ⊆ region :=
    fun index => (Bump.tsupport_deriv_subset _ _).trans (deriv_supported index)
  refine memSpatialSobolev_add_one_of_split basis timeIndex
    (source := localize bump (shiftedSpatialLaplacian basis timeIndex state) +
      ∑ index ∈ Finset.univ.erase timeIndex,
        localize ((bump.deriv (basis index)).deriv (basis index)) state)
    (flux := fun index => (-(2 : ℂ)) • localize (bump.deriv (basis index)) state)
    (shiftedSpatialLaplacian_localize basis timeIndex bump state) ?_ ?_
  · refine MemSpatialSobolev.add ?_ (MemSpatialSobolev.sum fun index _ => ?_)
    · rw [shiftedSpatialLaplacian, localize_sub]
      exact MemSpatialSobolev.sub ((state_held bump supported).mono_gain (by linarith))
        (source_held bump supported)
    · exact (state_held _ (deriv_two_supported index)).mono_gain (by linarith)
  · exact fun index _ =>
      MemSpatialSobolev.smul _ (state_held _ (deriv_supported index))

/-- **The iteration.**  One spatial derivative per step reaches every whole
number of spatial derivatives, at the isotropic grade the state started with. -/
theorem spatialSobolevOn_natCast (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_smooth : SmoothOn region (spatialLaplacian basis timeIndex state)) :
    ∀ step : ℕ, SpatialSobolevOn basis timeIndex region step grade state := by
  intro step
  induction step with
  | zero =>
      have started : SpatialSobolevOn basis timeIndex region 0 grade state :=
        spatialSobolevOn_zero_iff.mpr state_held
      simpa using started
  | succ previous gained =>
      have source_held : SpatialSobolevOn basis timeIndex region ((previous : ℝ) - 1) grade
          (spatialLaplacian basis timeIndex state) :=
        SpatialSobolevOn.mono_gain (by linarith)
          (spatialSobolevOn_of_sobolevOn (Nat.cast_nonneg previous)
            (source_smooth (grade + previous)))
      have advanced := spatialSobolevOn_add_one basis timeIndex gained source_held
      have rewrite : (previous : ℝ) + 1 = ((previous + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rwa [rewrite] at advanced

/-- **Spatially smooth on a window**: every spatial order, at a fixed isotropic
grade.  This is the strongest conclusion a purely spatial operator can deliver
on a space–time window, and `exists_norm_sq_gt_mul_spatialSymbol` is the reason
it is strongest. -/
def SpatialSmoothOn (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (region : Set Point) (grade : ℝ) (state : 𝓢'(Point, Value)) : Prop :=
  ∀ gain : ℝ, SpatialSobolevOn basis timeIndex region gain grade state

omit [DecidableEq Index] in
theorem SpatialSmoothOn.mono_region {basis : OrthonormalBasis Index ℝ Point}
    {timeIndex : Index} {smaller larger : Set Point} {grade : ℝ}
    {state : 𝓢'(Point, Value)} (subset : smaller ⊆ larger)
    (smooth : SpatialSmoothOn basis timeIndex larger grade state) :
    SpatialSmoothOn basis timeIndex smaller grade state :=
  fun gain => (smooth gain).mono_region subset

/-- **The payoff.**  A state at *some* grade on a window whose **spatial**
Laplacian is smooth there has every spatial derivative there, at that grade.

This is the statement an elliptic recovery in the spatial variables consumes:
there one has `-Δ_x v` expressed through data that is smooth on the window, and
this theorem returns the spatial regularity of `v`.  No time regularity is
claimed, and none can be. -/
theorem spatialSmoothOn_of_spatialLaplacian_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_smooth : SmoothOn region (spatialLaplacian basis timeIndex state)) :
    SpatialSmoothOn basis timeIndex region grade state := by
  intro gain
  obtain ⟨step, step_ge⟩ := exists_nat_ge gain
  exact SpatialSobolevOn.mono_gain step_ge
    (spatialSobolevOn_natCast basis timeIndex state_held source_smooth step)

/-- **The payoff on nested windows**, in the shape a residual carrying a nested
pair of balls can consume. -/
theorem spatialSmoothOn_ball_of_spatialLaplacian_smoothOn
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (center : Point)
    {innerRadius outerRadius : ℝ} (nested : innerRadius ≤ outerRadius) {grade : ℝ}
    {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outerRadius) grade state)
    (source_smooth : SmoothOn (ball center outerRadius)
      (spatialLaplacian basis timeIndex state)) :
    SpatialSmoothOn basis timeIndex (ball center innerRadius) grade state :=
  (spatialSmoothOn_of_spatialLaplacian_smoothOn basis timeIndex state_held
    source_smooth).mono_region (ball_subset_ball nested)

/-- **Space–time smoothness restricts to the slices' scale.**  A state smooth on
a space–time window has every spatial derivative there, at every grade.

This is the half of "slice restriction" that is unconditional: no restriction
operator is needed, because the spatial scale is *weaker* than the isotropic
one.  The other half — recovering a distribution on an individual slice — is not
proved here; see the module docstring. -/
theorem spatialSmoothOn_of_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} (grade : ℝ) {state : 𝓢'(Point, Value)}
    (smooth : SmoothOn region state) :
    SpatialSmoothOn basis timeIndex region grade state := by
  intro gain
  refine SpatialSobolevOn.mono_gain (le_max_left gain 0) ?_
  exact spatialSobolevOn_of_sobolevOn (le_max_right gain 0)
    (smooth (grade + max gain 0))

/-- **The bootstrap on the framework's chain of shrinking windows.**  The
one-step gain, run along `HeatSmoothing.chainRadius`, delivers every spatial
order on the closed inner ball. -/
theorem spatialSobolevOn_chain (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (center : Point) {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outerRadius) grade state)
    (source_smooth : SmoothOn (ball center outerRadius)
      (spatialLaplacian basis timeIndex state)) :
    ∀ step : ℕ,
      SpatialSobolevOn basis timeIndex (closedBall center innerRadius) step grade state := by
  refine Hypostructure.PDE.HeatSmoothing.regular_closedBall_of_chain center nested
    (regular := fun step region => SpatialSobolevOn basis timeIndex region step grade state)
    (fun _ _ _ subset held => held.mono_region subset) ?_ ?_
  · have started : SpatialSobolevOn basis timeIndex (ball center outerRadius) 0 grade state :=
      spatialSobolevOn_zero_iff.mpr state_held
    simpa using started
  · intro step held
    have source_here :
        SpatialSobolevOn basis timeIndex
          (ball center
            (Hypostructure.PDE.HeatSmoothing.chainRadius innerRadius outerRadius step))
          ((step : ℝ) - 1) grade (spatialLaplacian basis timeIndex state) :=
      SpatialSobolevOn.mono_gain (by linarith)
        (spatialSobolevOn_of_sobolevOn (Nat.cast_nonneg step)
          ((source_smooth (grade + step)).mono_region
            (ball_subset_ball (chainRadius_le_outer nested step))))
    have advanced := spatialSobolevOn_add_one basis timeIndex held source_here
    have shrunk := advanced.mono_region (ball_subset_ball
      (Hypostructure.PDE.HeatSmoothing.chainRadius_succ_lt nested step).le)
    have rewrite : (step : ℝ) + 1 = ((step + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rwa [rewrite] at shrunk

end LocalGain

/-! ## Recombining the two scales

The module's opening records that the spatial symbol alone gains nothing
isotropically.  The converse bookkeeping is what a consumer needs to *leave*
the spatial scale: the isotropic symbol is dominated by the spatial one **times
a time factor**, so spatial regularity together with one time derivative buys an
isotropic grade.

The inequality is Pythagoras and nothing else.  Writing `A` for the squared
spatial frequency and `B` for the squared time frequency, `‖ξ‖² = A + B` and

> `1 + A + B ≤ (1 + cA)(1 + cB) = 1 + cA + cB + c²AB`

for any `c ≥ 1`, because the cross term is nonnegative.  Here `c = (2π)²`.
-/

section Recombination

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The symbol of `1 − ∂_t∂_t`, the time-direction companion of
`spatialSymbol`. -/
noncomputable def timeSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℝ :=
  1 + (2 * π) ^ 2 * (inner ℝ place (basis timeIndex) : ℝ) ^ 2

omit [DecidableEq Index] in
theorem one_le_timeSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    1 ≤ timeSymbol basis timeIndex place := by
  have nonneg : (0 : ℝ) ≤ (2 * π) ^ 2 * (inner ℝ place (basis timeIndex) : ℝ) ^ 2 := by
    positivity
  rw [timeSymbol]
  linarith

omit [DecidableEq Index] in
theorem timeSymbol_pos (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    0 < timeSymbol basis timeIndex place :=
  lt_of_lt_of_le zero_lt_one (one_le_timeSymbol basis timeIndex place)

/--
**The two scales recombine into the isotropic one.**

`1 + ‖ξ‖²` is dominated by the spatial symbol times the time symbol, with
constant one.  This is the exact converse of
`exists_norm_sq_gt_mul_spatialSymbol`: the spatial symbol alone is not enough,
but the spatial symbol *with* the time direction is, and no constant is lost.

It is what lets a consumer that has bootstrapped `1 − Δ_x` on the spatial scale
convert its conclusion back to the isotropic scale once the equation supplies a
time derivative.
-/
theorem besselSymbol_le_spatialSymbol_mul_timeSymbol
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (place : Point) :
    1 + ‖place‖ ^ 2 ≤
      spatialSymbol basis timeIndex place * timeSymbol basis timeIndex place := by
  have decomposition := norm_sq_eq_spaceFrequencySq_add basis timeIndex place
  have spatial_nonneg := spaceFrequencySq_nonneg basis timeIndex place
  have time_nonneg : (0 : ℝ) ≤ (inner ℝ place (basis timeIndex) : ℝ) ^ 2 :=
    sq_nonneg _
  have scale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  rw [spatialSymbol_eq, timeSymbol, decomposition]
  nlinarith [mul_nonneg spatial_nonneg time_nonneg,
    mul_nonneg (mul_nonneg spatial_nonneg time_nonneg) (sq_nonneg (2 * π))]

end Recombination

end Hypostructure.PDE.Solution.SliceRestriction
