import Hypostructure.PDE.Solution.InteriorRegularity

/-!
# Interior regularity for the heat operator, obtained purely locally

`PDE/Solution/InteriorRegularity.lean` runs the elliptic bootstrap on a window:
cut the state off, apply a whole-space gain to the cut-off state, read the
conclusion back.  This module runs the same argument for `∂_t − Δ_x`, where the
bookkeeping is tighter and one extra idea is needed.

## Why the naive account fails, and what replaces it

The heat symbol is `iτ + ‖ξ_x‖²`.  Shifted so that it never vanishes it becomes
`σ(ξ) = 1 + iτ + (2π)²‖ξ_x‖²`, and the honest isotropic estimate is

> `1 + ‖ξ‖² ≤ |σ(ξ)|²`,

with constant one — `one_add_norm_sq_le_norm_shiftedHeatSymbol_sq`.  So the heat
operator gains **one** isotropic Sobolev derivative, and no more: at `ξ_x = 0`
the symbol is only of size `|τ| ≈ ‖ξ‖`.  That is not an artefact of the proof,
it is the reason a *parabolic* scale exists at all.

One derivative is not enough for the elliptic argument's accounting.  There the
whole-space gain is two and the cutoff commutator spends one, leaving `+1` per
step.  Here the gain is one and the elliptic-style commutator
`2 ∑ᵢ (∂ᵢχ)(∂ᵢu)` would spend one as well, leaving **nothing**.  A previous
attempt concluded from this that the anisotropic scale was unavoidable.

It is not.  The commutator's middle term is rewritten so that the derivative
sits *outside* a plain localization,

> `∂ᵢ∂ᵢ(χ u) = χ ∂ᵢ∂ᵢu + 2 ∂ᵢ((∂ᵢχ) u) − (∂ᵢ∂ᵢχ) u`,

which is `lineDerivOp_two_localize`.  Now the question is no longer how much
regularity `∂ᵢ u` has, but how large the multiplier `⟪ξ,eᵢ⟫ · (gain)/σ(ξ)` is —
and along a **spatial** direction the symbol has size `1 + ‖ξ_x‖²`, which
absorbs one power of `‖ξ_x‖` with room to spare.  Quantitatively:

> `(1 + ‖ξ‖²)^{1/4} · |⟪ξ,eᵢ⟫| ≤ |σ(ξ)|` for `eᵢ` spatial,

again with constant one —
`besselWeight_half_mul_abs_inner_le_norm_shiftedHeatSymbol`.
The exponent `1/4` is exactly borderline: it is `1/2` of the half derivative
`besselPotential (1/2)` supplies, and both extreme regimes `|τ| ≈ ‖ξ_x‖²` and
`‖ξ_x‖ ≈ |τ|^{1/2}` saturate it.  So the localized bootstrap gains **half** a
grade per step, honestly, and half a grade per step still reaches every grade.

## Avoiding the reciprocal symbol

Applying `σ⁻¹` would require `σ⁻¹` to be of temperate growth, which mathlib does
not supply and which is a Faà-di-Bruno-shaped nuisance to prove.  It is never
needed.  Writing `W = 1 + |σ|²` — a quantity whose reciprocal *is* available,
because `(1 + ‖·‖²)^r` is temperate on `ℂ` viewed as a real inner product space —
the algebraic identity

> `bessel = (bessel · conj σ · W⁻¹) · σ + (bessel · W⁻¹)`

splits the Bessel weight into a multiple of the symbol plus a remainder, with
both cofactors bounded by one.  That is
`shiftedHeatSymbol_mul_solvedMultiplier_add_remainderMultiplier`, and it is what
lets `MemSobolev.fourierMultiplierCLM_of_bounded` do all the analytic work.

## What is proved

* `heatOperator` — `∂_t − Δ_x` on tempered distributions, built from `lineDerivOp`
  in a distinguished direction of an orthonormal basis and the sum of the pure
  second derivatives in the remaining ones;
* `shifted_heatOperator_eq_fourierMultiplierCLM` — its symbol identity;
* `one_add_norm_sq_le_norm_shiftedHeatSymbol_sq`,
  `besselWeight_half_mul_abs_inner_le_norm_shiftedHeatSymbol` — the two symbol
  estimates, each with an explicit constant of one;
* `memSobolev_add_one_of_heat` — **the whole-space gain**: a state and its heat
  image both at `grade` put the state at `grade + 1`;
* `memSobolev_add_half_of_split` — **the whole-space gain in localizable form**:
  a state whose shifted heat image is a state at `grade` plus spatial
  derivatives of states at `grade` lies at `grade + 1/2`;
* `shifted_heatOperator_localize` — the heat commutator, with every derivative
  kept outside a localization and every term carrying a derivative of the cutoff;
* `sobolevOn_add_half` — **the local one-step gain**, half a grade on a window;
* `sobolevOn_add_half_natCast`, `sobolevOn_chain_of_heat` — the iteration, the
  latter over the shrinking chain of windows of `PDE/HeatSmoothing.lean`;
* `smoothOn_of_heat_smoothOn`, `smoothOn_ball_of_heat_smoothOn` — **the payoff**:
  a state whose heat image is smooth on a window is smooth on every window
  contained in it.

`SobolevOn`, `SmoothOn`, `Bump`, `localize` and `lineDerivOp_localize` are reused
verbatim from `PDE/Solution/InteriorRegularity.lean`; nothing is duplicated.

Nothing here names a dimension, a boundary condition or a physical quantity.
-/

namespace Hypostructure.PDE.Solution.ParabolicRegularity

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.Solution.InteriorRegularity
open scoped SchwartzMap ENNReal Real LineDeriv Laplacian ContDiff

universe uPoint uValue uIndex

section Frequencies

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The squared spatial frequency. -/
noncomputable def spaceFrequencySq (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℝ :=
  ∑ index ∈ Finset.univ.erase timeIndex, inner ℝ place (basis index) ^ 2

/-- The time frequency. -/
noncomputable def timeFrequency (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℝ :=
  2 * π * inner ℝ place (basis timeIndex)

theorem spaceFrequencySq_nonneg (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    0 ≤ spaceFrequencySq basis timeIndex place :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_eq_spaceFrequencySq_add (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    ‖place‖ ^ 2 =
      spaceFrequencySq basis timeIndex place + inner ℝ place (basis timeIndex) ^ 2 := by
  rw [spaceFrequencySq, ← basis.sum_sq_inner_left place,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ timeIndex)]

theorem sq_inner_le_spaceFrequencySq (basis : OrthonormalBasis Index ℝ Point)
    {timeIndex index : Index} (different : index ≠ timeIndex) (place : Point) :
    inner ℝ place (basis index) ^ 2 ≤ spaceFrequencySq basis timeIndex place :=
  Finset.single_le_sum (f := fun index => inner ℝ place (basis index) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩)

/-! ## The symbol of the shifted heat operator -/

/-- The symbol of `∂_t − Δ_x`. -/
noncomputable def heatSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℂ :=
  (((2 * π) ^ 2 * spaceFrequencySq basis timeIndex place : ℝ) : ℂ) +
    ((timeFrequency basis timeIndex place : ℝ) : ℂ) * Complex.I

/-- The symbol of `1 + ∂_t − Δ_x`. -/
noncomputable def shiftedHeatSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℂ :=
  1 + heatSymbol basis timeIndex place

theorem norm_shiftedHeatSymbol_sq (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 =
      (1 + (2 * π) ^ 2 * spaceFrequencySq basis timeIndex place) ^ 2 +
        timeFrequency basis timeIndex place ^ 2 := by
  have decomposition : shiftedHeatSymbol basis timeIndex place =
      ((1 + (2 * π) ^ 2 * spaceFrequencySq basis timeIndex place : ℝ) : ℂ) +
        ((timeFrequency basis timeIndex place : ℝ) : ℂ) * Complex.I := by
    simp only [shiftedHeatSymbol, heatSymbol]
    push_cast
    ring
  rw [decomposition, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

theorem one_le_norm_shiftedHeatSymbol_sq (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    1 ≤ ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 := by
  rw [norm_shiftedHeatSymbol_sq]
  have nonneg := spaceFrequencySq_nonneg basis timeIndex place
  nlinarith [sq_nonneg (timeFrequency basis timeIndex place),
    sq_nonneg ((2 * π) ^ 2 * spaceFrequencySq basis timeIndex place), Real.pi_gt_three]

/-- The shifted symbol, split into the pieces the operator identity produces: the
constant `1`, the time derivative's symbol, and one summand per spatial direction. -/
theorem shiftedHeatSymbol_eq_sum (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    shiftedHeatSymbol basis timeIndex = fun place =>
      (1 + 2 * π * Complex.I * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ)) +
        ∑ index ∈ Finset.univ.erase timeIndex,
          (2 * (π : ℂ)) ^ 2 * ((inner ℝ place (basis index) : ℝ) : ℂ) ^ 2 := by
  funext place
  simp only [shiftedHeatSymbol, heatSymbol, spaceFrequencySq, timeFrequency]
  push_cast
  rw [Finset.mul_sum]
  ring

theorem shiftedHeatSymbol_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    (shiftedHeatSymbol basis timeIndex).HasTemperateGrowth := by
  have head : (fun place : Point =>
      1 + 2 * π * Complex.I * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have tail : ∀ index ∈ Finset.univ.erase timeIndex,
      (fun place : Point =>
        (2 * (π : ℂ)) ^ 2 * ((inner ℝ place (basis index) : ℝ) : ℂ) ^ 2).HasTemperateGrowth := by
    intro index _
    fun_prop
  rw [shiftedHeatSymbol_eq_sum]
  exact head.add (Function.HasTemperateGrowth.sum tail)

theorem one_add_norm_sq_le_norm_shiftedHeatSymbol_sq
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (place : Point) :
    1 + ‖place‖ ^ 2 ≤ ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 := by
  rw [norm_shiftedHeatSymbol_sq, norm_sq_eq_spaceFrequencySq_add basis timeIndex place,
    timeFrequency]
  have nonneg := spaceFrequencySq_nonneg basis timeIndex place
  have scale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_nonneg (sub_nonneg.mpr scale) nonneg,
    mul_nonneg (sub_nonneg.mpr scale) (sq_nonneg (inner ℝ place (basis timeIndex) : ℝ)),
    sq_nonneg ((2 * π) ^ 2 * spaceFrequencySq basis timeIndex place),
    sq_nonneg (inner ℝ place (basis timeIndex) : ℝ)]

theorem sqrt_one_add_norm_sq_mul_sq_inner_le
    (basis : OrthonormalBasis Index ℝ Point) {timeIndex index : Index}
    (different : index ≠ timeIndex) (place : Point) :
    Real.sqrt (1 + ‖place‖ ^ 2) * inner ℝ place (basis index) ^ 2 ≤
      ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 := by
  set dominant := ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 with dominant_def
  have dominant_nonneg : 0 ≤ dominant := by positivity
  have root_nonneg : 0 ≤ Real.sqrt dominant := Real.sqrt_nonneg _
  have root_sq : Real.sqrt dominant ^ 2 = dominant := Real.sq_sqrt dominant_nonneg
  have root_mono : Real.sqrt (1 + ‖place‖ ^ 2) ≤ Real.sqrt dominant :=
    Real.sqrt_le_sqrt (one_add_norm_sq_le_norm_shiftedHeatSymbol_sq basis timeIndex place)
  have spatial_le : (2 * π) ^ 2 * inner ℝ place (basis index) ^ 2 ≤ Real.sqrt dominant := by
    have step : (1 + (2 * π) ^ 2 * spaceFrequencySq basis timeIndex place) ^ 2 ≤ dominant := by
      rw [dominant_def, norm_shiftedHeatSymbol_sq]
      nlinarith [sq_nonneg (timeFrequency basis timeIndex place)]
    have bounded := Real.sqrt_le_sqrt step
    rw [Real.sqrt_sq (by nlinarith [spaceFrequencySq_nonneg basis timeIndex place,
      Real.pi_pos])] at bounded
    nlinarith [sq_inner_le_spaceFrequencySq basis different place, Real.pi_pos]
  have scale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_le_mul_of_nonneg_right root_mono (sq_nonneg (inner ℝ place (basis index) : ℝ)),
    mul_le_mul_of_nonneg_left spatial_le root_nonneg,
    mul_nonneg (mul_nonneg root_nonneg (sub_nonneg.mpr scale))
      (sq_nonneg (inner ℝ place (basis index) : ℝ))]

/-! ## The two bounded multipliers

Both are built from a *gain* parameter: `gain = 1` is the whole-space statement
(the heat operator gains one isotropic derivative), `gain = 1/2` is what survives
localization.  Everything below the two symbol estimates is uniform in the gain.
-/

/-- The symbol of `besselPotential gain`. -/
noncomputable def besselWeight (gain : ℝ) (place : Point) : ℝ :=
  (1 + ‖place‖ ^ 2) ^ (gain / 2)

/-- The regularized reciprocal of `|1 + i τ + (2π)²‖ξ_x‖²|²`.

Regularized, because `1 + |σ|²` is a quantity whose reciprocal is *available*:
it is `(1 + ‖·‖²)^{-1}` composed with the symbol, and mathlib proves that
`(1 + ‖·‖²)^r` has temperate growth on any real inner product space, `ℂ`
included.  The bare reciprocal `σ⁻¹` would need a temperate-growth estimate that
mathlib does not supply — and, as the identity below shows, never needs to. -/
noncomputable def resolventWeight (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℝ :=
  (1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2) ^ (-1 : ℝ)

/-- The multiplier applied to the shifted heat image. -/
noncomputable def solvedMultiplier (gain : ℝ) (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℂ :=
  (besselWeight gain place : ℂ) *
    (starRingEnd ℂ) (shiftedHeatSymbol basis timeIndex place) *
    (resolventWeight basis timeIndex place : ℂ)

/-- The multiplier applied to the state itself. -/
noncomputable def remainderMultiplier (gain : ℝ) (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) : ℂ :=
  (besselWeight gain place : ℂ) * (resolventWeight basis timeIndex place : ℂ)

omit [InnerProductSpace ℝ Point] in
theorem besselWeight_nonneg (gain : ℝ) (place : Point) : 0 ≤ besselWeight gain place :=
  Real.rpow_nonneg (by positivity) _

omit [InnerProductSpace ℝ Point] in
/-- The gain parameter is monotone: a smaller gain is a smaller weight, because
the base `1 + ‖ξ‖²` is at least one. -/
theorem besselWeight_mono {lower upper : ℝ} (le : lower ≤ upper) (place : Point) :
    besselWeight lower place ≤ besselWeight upper place :=
  Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖place‖]) (by linarith)

omit [InnerProductSpace ℝ Point] in
theorem besselWeight_one_sq (place : Point) :
    besselWeight 1 place ^ 2 = 1 + ‖place‖ ^ 2 := by
  rw [besselWeight, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

omit [InnerProductSpace ℝ Point] in
theorem besselWeight_half_sq (place : Point) :
    besselWeight (1 / 2) place ^ 2 = Real.sqrt (1 + ‖place‖ ^ 2) := by
  rw [besselWeight, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
    Real.sqrt_eq_rpow]
  norm_num

theorem resolventWeight_eq_inv (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    resolventWeight basis timeIndex place =
      (1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ := by
  rw [resolventWeight, Real.rpow_neg_one]

theorem resolventWeight_nonneg (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    0 ≤ resolventWeight basis timeIndex place :=
  Real.rpow_nonneg (by positivity) _

theorem one_le_norm_shiftedHeatSymbol (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    1 ≤ ‖shiftedHeatSymbol basis timeIndex place‖ := by
  nlinarith [one_le_norm_shiftedHeatSymbol_sq basis timeIndex place,
    norm_nonneg (shiftedHeatSymbol basis timeIndex place)]

/-- **A whole derivative is dominated by the shifted symbol.**  This is the
isotropic gain of the heat operator, with constant one, and it is sharp: at zero
spatial frequency the symbol is only of size `|τ| ≈ ‖ξ‖`. -/
theorem besselWeight_one_le_norm_shiftedHeatSymbol
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (place : Point) :
    besselWeight 1 place ≤ ‖shiftedHeatSymbol basis timeIndex place‖ := by
  have squares : besselWeight 1 place ^ 2 ≤ ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 := by
    rw [besselWeight_one_sq]
    exact one_add_norm_sq_le_norm_shiftedHeatSymbol_sq basis timeIndex place
  nlinarith [besselWeight_nonneg 1 place,
    norm_nonneg (shiftedHeatSymbol basis timeIndex place)]

theorem besselWeight_le_norm_shiftedHeatSymbol {gain : ℝ} (gain_le : gain ≤ 1)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (place : Point) :
    besselWeight gain place ≤ ‖shiftedHeatSymbol basis timeIndex place‖ :=
  (besselWeight_mono gain_le place).trans
    (besselWeight_one_le_norm_shiftedHeatSymbol basis timeIndex place)

/-- **One spatial derivative is still affordable at gain one half.**  This is the
estimate that makes the *localized* bootstrap gain, and `1/2` is exactly the
borderline exponent: both regimes `|τ| ≈ ‖ξ_x‖²` and `‖ξ_x‖ ≈ |τ|^{1/2}` saturate
it. -/
theorem besselWeight_half_mul_abs_inner_le_norm_shiftedHeatSymbol
    (basis : OrthonormalBasis Index ℝ Point) {timeIndex index : Index}
    (different : index ≠ timeIndex) (place : Point) :
    besselWeight (1 / 2) place * |inner ℝ place (basis index)| ≤
      ‖shiftedHeatSymbol basis timeIndex place‖ := by
  have squares : (besselWeight (1 / 2) place * |inner ℝ place (basis index)|) ^ 2 ≤
      ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 := by
    rw [mul_pow, besselWeight_half_sq, sq_abs]
    exact sqrt_one_add_norm_sq_mul_sq_inner_le basis different place
  nlinarith [mul_nonneg (besselWeight_nonneg (1 / 2) place)
      (abs_nonneg (inner ℝ place (basis index) : ℝ)),
    norm_nonneg (shiftedHeatSymbol basis timeIndex place)]

theorem besselWeight_hasTemperateGrowth (gain : ℝ) :
    (fun place : Point => ((besselWeight gain place : ℝ) : ℂ)).HasTemperateGrowth := by
  simp only [besselWeight]
  fun_prop

theorem resolventWeight_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    (fun place : Point =>
      ((resolventWeight basis timeIndex place : ℝ) : ℂ)).HasTemperateGrowth := by
  have base : (fun value : ℂ => (1 + ‖value‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow ℂ (-1)
  exact Function.Complex.hasTemperateGrowth_ofReal.comp
    (base.comp (shiftedHeatSymbol_hasTemperateGrowth basis timeIndex))

theorem conj_shiftedHeatSymbol_hasTemperateGrowth (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    (fun place : Point =>
      (starRingEnd ℂ) (shiftedHeatSymbol basis timeIndex place)).HasTemperateGrowth := by
  have conjugation : (fun value : ℂ => (starRingEnd ℂ) value).HasTemperateGrowth := by
    have equivalence := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasTemperateGrowth
    convert equivalence using 1
    funext value
    simp
  exact conjugation.comp (shiftedHeatSymbol_hasTemperateGrowth basis timeIndex)

theorem solvedMultiplier_hasTemperateGrowth (gain : ℝ)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    (solvedMultiplier gain basis timeIndex).HasTemperateGrowth :=
  (((besselWeight_hasTemperateGrowth gain).mul
      (conj_shiftedHeatSymbol_hasTemperateGrowth basis timeIndex)).mul
    (resolventWeight_hasTemperateGrowth basis timeIndex))

theorem remainderMultiplier_hasTemperateGrowth (gain : ℝ)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    (remainderMultiplier gain basis timeIndex).HasTemperateGrowth :=
  (besselWeight_hasTemperateGrowth gain).mul
    (resolventWeight_hasTemperateGrowth basis timeIndex)

theorem norm_solvedMultiplier_eq (gain : ℝ) (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (place : Point) :
    ‖solvedMultiplier gain basis timeIndex place‖ =
      besselWeight gain place * ‖shiftedHeatSymbol basis timeIndex place‖ *
        resolventWeight basis timeIndex place := by
  simp [solvedMultiplier, abs_of_nonneg (besselWeight_nonneg gain place),
    abs_of_nonneg (resolventWeight_nonneg basis timeIndex place)]

theorem norm_solvedMultiplier_le_one {gain : ℝ} (gain_le : gain ≤ 1)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (place : Point) :
    ‖solvedMultiplier gain basis timeIndex place‖ ≤ 1 := by
  rw [norm_solvedMultiplier_eq, resolventWeight_eq_inv, ← div_eq_mul_inv,
    div_le_one (by positivity)]
  nlinarith [besselWeight_le_norm_shiftedHeatSymbol gain_le basis timeIndex place,
    besselWeight_nonneg gain place, norm_nonneg (shiftedHeatSymbol basis timeIndex place)]

theorem norm_remainderMultiplier_le_one {gain : ℝ} (gain_le : gain ≤ 1)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (place : Point) :
    ‖remainderMultiplier gain basis timeIndex place‖ ≤ 1 := by
  have expand : ‖remainderMultiplier gain basis timeIndex place‖ =
      besselWeight gain place * resolventWeight basis timeIndex place := by
    simp [remainderMultiplier, abs_of_nonneg (besselWeight_nonneg gain place),
      abs_of_nonneg (resolventWeight_nonneg basis timeIndex place)]
  rw [expand, resolventWeight_eq_inv, ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [besselWeight_le_norm_shiftedHeatSymbol gain_le basis timeIndex place,
    one_le_norm_shiftedHeatSymbol basis timeIndex place]

/-- The bound behind the localized gain: at gain one half a spatial derivative
may be spent and the multiplier is still bounded by one. -/
theorem norm_inner_mul_solvedMultiplier_le_one (basis : OrthonormalBasis Index ℝ Point)
    {timeIndex index : Index} (different : index ≠ timeIndex) (place : Point) :
    ‖((inner ℝ place (basis index) : ℝ) : ℂ) *
      solvedMultiplier (1 / 2) basis timeIndex place‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_solvedMultiplier_eq,
    resolventWeight_eq_inv]
  rw [show |inner ℝ place (basis index)| *
      (besselWeight (1 / 2) place * ‖shiftedHeatSymbol basis timeIndex place‖ *
        (1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹) =
      (besselWeight (1 / 2) place * |inner ℝ place (basis index)| *
        ‖shiftedHeatSymbol basis timeIndex place‖) /
        (1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2) by
    field_simp]
  rw [div_le_one (by positivity)]
  nlinarith [besselWeight_half_mul_abs_inner_le_norm_shiftedHeatSymbol basis different place,
    mul_nonneg (besselWeight_nonneg (1 / 2) place)
      (abs_nonneg (inner ℝ place (basis index) : ℝ)),
    norm_nonneg (shiftedHeatSymbol basis timeIndex place)]

/-- **The algebraic identity behind the gain.**  The Bessel weight factors
through the shifted heat symbol with two cofactors — and the point is that no
division by the symbol is ever performed, so no temperate-growth estimate for a
reciprocal is needed.  The identity holds for every gain; only the *bounds* on
the cofactors care what the gain is. -/
theorem shiftedHeatSymbol_mul_solvedMultiplier_add_remainderMultiplier (gain : ℝ)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) :
    (fun place : Point => shiftedHeatSymbol basis timeIndex place *
        solvedMultiplier gain basis timeIndex place +
      remainderMultiplier gain basis timeIndex place) =
      fun place : Point => ((besselWeight gain place : ℝ) : ℂ) := by
  funext place
  have conjugation : shiftedHeatSymbol basis timeIndex place *
      (starRingEnd ℂ) (shiftedHeatSymbol basis timeIndex place) =
        ((‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [solvedMultiplier, remainderMultiplier, resolventWeight_eq_inv]
  calc shiftedHeatSymbol basis timeIndex place *
        ((besselWeight gain place : ℂ) *
          (starRingEnd ℂ) (shiftedHeatSymbol basis timeIndex place) *
          (((1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ : ℝ) : ℂ)) +
        (besselWeight gain place : ℂ) *
          (((1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ : ℝ) : ℂ)
      = (besselWeight gain place : ℂ) *
          (((1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ : ℝ) : ℂ) *
          (shiftedHeatSymbol basis timeIndex place *
            (starRingEnd ℂ) (shiftedHeatSymbol basis timeIndex place)) +
          (besselWeight gain place : ℂ) *
          (((1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ : ℝ) : ℂ) := by ring
    _ = ((besselWeight gain place * (1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ *
          ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 +
          besselWeight gain place *
            (1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
        rw [conjugation]
        push_cast
        ring
    _ = ((besselWeight gain place : ℝ) : ℂ) := by
        norm_cast
        have positive : (0 : ℝ) < 1 + ‖shiftedHeatSymbol basis timeIndex place‖ ^ 2 := by
          positivity
        field_simp
        ring


end Frequencies

section Operator

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The spatial Laplacian. -/
noncomputable def spatialLaplacian (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (state : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  ∑ index ∈ Finset.univ.erase timeIndex, ∂_{basis index} (∂_{basis index} state)

/-- The heat operator `∂_t − Δ_x`. -/
noncomputable def heatOperator (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (state : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  ∂_{basis timeIndex} state - spatialLaplacian basis timeIndex state

theorem lineDerivOp_eq_fourierMultiplierCLM (direction : Point) (state : 𝓢'(Point, Value)) :
    ∂_{direction} state =
      fourierMultiplierCLM Value
        (fun place => 2 * π * Complex.I * ((inner ℝ place direction : ℝ) : ℂ)) state := by
  have temperate : (fun place : Point => ((inner ℝ place direction : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [lineDeriv_eq_fourierMultiplierCLM,
    show (fun place : Point => 2 * π * Complex.I * ((inner ℝ place direction : ℝ) : ℂ)) =
      (2 * π * Complex.I : ℂ) • (fun place : Point => ((inner ℝ place direction : ℝ) : ℂ)) from rfl,
    fourierMultiplierCLM_smul (F := Value) temperate]
  rfl

theorem lineDerivOp_two_eq_fourierMultiplierCLM (direction : Point)
    (state : 𝓢'(Point, Value)) :
    ∂_{direction} (∂_{direction} state) =
      fourierMultiplierCLM Value
        (fun place => -(2 * (π : ℂ)) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2)
        state := by
  have temperate :
      (fun place : Point => 2 * π * Complex.I *
        ((inner ℝ place direction : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have multiplier :
      (fun place : Point => 2 * π * Complex.I * ((inner ℝ place direction : ℝ) : ℂ)) *
          (fun place : Point => 2 * π * Complex.I * ((inner ℝ place direction : ℝ) : ℂ)) =
        fun place : Point => -(2 * (π : ℂ)) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2 := by
    funext place
    simp only [Pi.mul_apply]
    linear_combination
      (4 * (π : ℂ) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2) * Complex.I_sq
  rw [lineDerivOp_eq_fourierMultiplierCLM direction state,
    lineDerivOp_eq_fourierMultiplierCLM direction,
    fourierMultiplierCLM_fourierMultiplierCLM_apply temperate temperate, multiplier]

theorem neg_lineDerivOp_two_eq_fourierMultiplierCLM (direction : Point)
    (state : 𝓢'(Point, Value)) :
    -(∂_{direction} (∂_{direction} state)) =
      fourierMultiplierCLM Value
        (fun place => (2 * (π : ℂ)) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2) state := by
  have temperate :
      (fun place : Point =>
        (2 * (π : ℂ)) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2).HasTemperateGrowth := by
    fun_prop
  rw [lineDerivOp_two_eq_fourierMultiplierCLM,
    show (fun place : Point => -(2 * (π : ℂ)) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2) =
      (-1 : ℂ) • (fun place : Point =>
        (2 * (π : ℂ)) ^ 2 * ((inner ℝ place direction : ℝ) : ℂ) ^ 2) by
      funext place
      simp only [Pi.smul_apply, smul_eq_mul]
      ring,
    fourierMultiplierCLM_smul (F := Value) temperate]
  simp

/-- **The symbol of the shifted heat operator.**  `1 + ∂_t − Δ_x` is the Fourier
multiplier with symbol `1 + 2πi⟪ξ,e_t⟫ + (2π)²‖ξ_x‖²`. -/
theorem shifted_heatOperator_eq_fourierMultiplierCLM
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index) (state : 𝓢'(Point, Value)) :
    state + heatOperator basis timeIndex state =
      fourierMultiplierCLM Value (shiftedHeatSymbol basis timeIndex) state := by
  classical
  set spacePart : Index → Point → ℂ := fun index place =>
    (2 * (π : ℂ)) ^ 2 * ((inner ℝ place (basis index) : ℝ) : ℂ) ^ 2 with spacePart_def
  set timePart : Point → ℂ := fun place =>
    2 * π * Complex.I * ((inner ℝ place (basis timeIndex) : ℝ) : ℂ) with timePart_def
  have temperate_const : (fun _ : Point => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  have temperate_time : timePart.HasTemperateGrowth := by rw [timePart_def]; fun_prop
  have temperate_space :
      ∀ index ∈ Finset.univ.erase timeIndex, (spacePart index).HasTemperateGrowth := by
    intro index _
    rw [spacePart_def]
    fun_prop
  have temperate_sum :
      (fun place : Point => ∑ index ∈ Finset.univ.erase timeIndex,
        spacePart index place).HasTemperateGrowth :=
    Function.HasTemperateGrowth.sum temperate_space
  have symbol_eq : shiftedHeatSymbol basis timeIndex =
      fun place => ((1 : ℂ) + timePart place) +
        ∑ index ∈ Finset.univ.erase timeIndex, spacePart index place :=
    shiftedHeatSymbol_eq_sum basis timeIndex
  have temperate_head :
      (fun place : Point => (1 : ℂ) + timePart place).HasTemperateGrowth :=
    temperate_const.add temperate_time
  rw [symbol_eq,
    Bessel.fourierMultiplier_add temperate_head temperate_sum state,
    Bessel.fourierMultiplier_add temperate_const temperate_time state,
    ← lineDerivOp_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_sum Value temperate_space]
  simp only [fourierMultiplierCLM_const, sum_apply, ContinuousLinearMap.id_apply, one_smul]
  simp only [← neg_lineDerivOp_two_eq_fourierMultiplierCLM, spacePart_def]
  rw [heatOperator, spatialLaplacian, Finset.sum_neg_distrib]
  abel

end Operator

/-! ## Commutation, read in frequency

Every operator this file builds — a directional derivative, the spatial
Laplacian, the heat operator — is a Fourier multiplier, and multipliers commute
because multiplication of their symbols does.  That single observation gives all
the commutation facts a consumer needs, and it gives them *without side
conditions*: the symbol of the other multiplier is arbitrary of temperate
growth, and in particular nothing is asked of how it depends on the frequency in
the distinguished direction.

The route through `PDE/Distribution/CurlCalculus.lean`'s `lineDerivOp_comm`
proves the same commutations for operators assembled out of `lineDerivOp`s; the
multiplier route is taken here because it also covers operators that are *not*
such an assembly — an arbitrary multiplier, in particular a solution operator
handed to the framework as a symbol and nothing else.
-/

section Multipliers

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- A directional derivative distributes over a finite sum of states: it is the
application of the continuous linear map that
`lineDerivOp_eq_fourierMultiplierCLM` exhibits. -/
theorem lineDerivOp_finset_sum {Element : Type*} (direction : Point)
    (family : Finset Element) (states : Element → 𝓢'(Point, Value)) :
    ∂_{direction} (∑ item ∈ family, states item) =
      ∑ item ∈ family, ∂_{direction} (states item) := by
  simp only [lineDerivOp_eq_fourierMultiplierCLM, map_sum]

/-- The heat operator distributes over a finite sum of states. -/
theorem heatOperator_finset_sum {Element : Type*}
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (family : Finset Element) (states : Element → 𝓢'(Point, Value)) :
    heatOperator basis timeIndex (∑ item ∈ family, states item) =
      ∑ item ∈ family, heatOperator basis timeIndex (states item) := by
  simp only [heatOperator, spatialLaplacian, lineDerivOp_finset_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/--
**A Fourier multiplier commutes with every directional derivative.**

`∂_{v}` is the Fourier multiplier with symbol `2πi⟪ξ,v⟫`
(`lineDerivOp_eq_fourierMultiplierCLM`), composing two multipliers is the
multiplier of the product of their symbols
(`TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`), and
multiplication of functions is commutative.  There is no side condition: the
symbol is arbitrary of temperate growth.
-/
theorem lineDerivOp_fourierMultiplierCLM_comm {symbol : Point → ℂ}
    (temperate : symbol.HasTemperateGrowth) (direction : Point)
    (state : 𝓢'(Point, Value)) :
    ∂_{direction} (fourierMultiplierCLM Value symbol state) =
      fourierMultiplierCLM Value symbol (∂_{direction} state) := by
  have temperateDeriv : (fun place : Point =>
      2 * (π : ℂ) * Complex.I * ((inner ℝ place direction : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [lineDerivOp_eq_fourierMultiplierCLM, lineDerivOp_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply temperate temperateDeriv,
    fourierMultiplierCLM_fourierMultiplierCLM_apply temperateDeriv temperate, mul_comm]

/-- **A Fourier multiplier commutes with the heat operator.**  `∂_t − Δ_x` is a
difference of iterated directional derivatives, so this is the previous theorem
applied once per direction. -/
theorem fourierMultiplierCLM_heatOperator_comm {symbol : Point → ℂ}
    (temperate : symbol.HasTemperateGrowth) (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (state : 𝓢'(Point, Value)) :
    heatOperator basis timeIndex (fourierMultiplierCLM Value symbol state) =
      fourierMultiplierCLM Value symbol (heatOperator basis timeIndex state) := by
  rw [heatOperator, heatOperator, spatialLaplacian, spatialLaplacian, map_sub, map_sum]
  simp only [lineDerivOp_fourierMultiplierCLM_comm temperate]

/-- **The heat operator commutes with every directional derivative**, in
particular with `∂_t` itself: a derivative is a Fourier multiplier too. -/
theorem heatOperator_lineDerivOp_comm (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (direction : Point) (state : 𝓢'(Point, Value)) :
    heatOperator basis timeIndex (∂_{direction} state) =
      ∂_{direction} (heatOperator basis timeIndex state) := by
  have temperate : (fun place : Point =>
      2 * (π : ℂ) * Complex.I * ((inner ℝ place direction : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [lineDerivOp_eq_fourierMultiplierCLM, lineDerivOp_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_heatOperator_comm temperate]

end Multipliers

section Gain

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

omit [CompleteSpace Value] in
/-- **The factorization.**  The Bessel potential of a state is a multiplier
applied to its shifted heat image, plus a multiplier applied to the state itself.
Pure algebra: it holds for every gain, and only the bounds care what the gain is. -/
theorem besselPotential_eq_solved_add_remainder (gain : ℝ)
    (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (state : 𝓢'(Point, Value)) :
    besselPotential Point Value gain state =
      fourierMultiplierCLM Value (solvedMultiplier gain basis timeIndex)
          (state + heatOperator basis timeIndex state) +
        fourierMultiplierCLM Value (remainderMultiplier gain basis timeIndex) state := by
  have symbol_temperate := shiftedHeatSymbol_hasTemperateGrowth basis timeIndex
  have solved_temperate := solvedMultiplier_hasTemperateGrowth gain basis timeIndex
  have remainder_temperate := remainderMultiplier_hasTemperateGrowth gain basis timeIndex
  have combine : (fun place : Point =>
      (shiftedHeatSymbol basis timeIndex * solvedMultiplier gain basis timeIndex) place +
        remainderMultiplier gain basis timeIndex place) =
      fun place : Point => ((besselWeight gain place : ℝ) : ℂ) :=
    shiftedHeatSymbol_mul_solvedMultiplier_add_remainderMultiplier gain basis timeIndex
  have bessel_eq : besselPotential Point Value gain state =
      fourierMultiplierCLM Value
        (fun place : Point => ((besselWeight gain place : ℝ) : ℂ)) state :=
    rfl
  rw [bessel_eq, ← combine,
    Bessel.fourierMultiplier_add (symbol_temperate.mul solved_temperate) remainder_temperate state,
    ← fourierMultiplierCLM_fourierMultiplierCLM_apply symbol_temperate solved_temperate,
    ← shifted_heatOperator_eq_fourierMultiplierCLM]

/-- **The whole-space gain.**  A state and its heat image both at `grade` put the
state at `grade + 1`: the heat operator gains one full isotropic derivative.

This is the statement the naive localization would consume — and cannot, because
the cutoff commutator spends the whole of it.  `memSobolev_add_half_of_split`
below is what a localization can actually use. -/
theorem memSobolev_add_one_of_heat (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_member : MemSobolev grade 2 state)
    (source_member : MemSobolev grade 2 (heatOperator basis timeIndex state)) :
    MemSobolev (grade + 1) 2 state := by
  have image_member : MemSobolev grade 2 (besselPotential Point Value 1 state) := by
    rw [besselPotential_eq_solved_add_remainder 1 basis timeIndex]
    refine MemSobolev.add
      ((state_member.add source_member).fourierMultiplierCLM_of_bounded
        (solvedMultiplier_hasTemperateGrowth 1 basis timeIndex)
        ⟨1, norm_solvedMultiplier_le_one le_rfl basis timeIndex⟩)
      (state_member.fourierMultiplierCLM_of_bounded
        (remainderMultiplier_hasTemperateGrowth 1 basis timeIndex)
        ⟨1, norm_remainderMultiplier_le_one le_rfl basis timeIndex⟩)
  have gained := memSobolev_besselPotential_iff.mp image_member
  rwa [show (1 : ℝ) + grade = grade + 1 by ring] at gained

/-- **The one-step gain, in the form the localization needs.**

The heat operator gains one full isotropic derivative, but a cutoff spends one
derivative on the state, so a naive localization would gain nothing.  The way out
is to keep the commutator's derivative *outside*: the shifted heat image is
allowed to be a state at `grade` plus **spatial** derivatives of states at
`grade`.  A spatial frequency costs only half of the available gain — that is
`besselWeight_half_mul_abs_inner_le_norm_shiftedHeatSymbol` — so half a
derivative survives, and half a derivative per step is all an iteration needs. -/
theorem memSobolev_add_half_of_split (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {grade : ℝ} {state source : 𝓢'(Point, Value)}
    {flux : Index → 𝓢'(Point, Value)}
    (identity : state + heatOperator basis timeIndex state =
      source + ∑ index ∈ Finset.univ.erase timeIndex, ∂_{basis index} (flux index))
    (state_member : MemSobolev grade 2 state)
    (source_member : MemSobolev grade 2 source)
    (flux_member : ∀ index ∈ Finset.univ.erase timeIndex, MemSobolev grade 2 (flux index)) :
    MemSobolev (grade + 1 / 2) 2 state := by
  have half_le_one : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have solved_temperate := solvedMultiplier_hasTemperateGrowth (1 / 2) basis timeIndex
  have solved_bounded : ∃ bound, ∀ place : Point,
      ‖solvedMultiplier (1 / 2) basis timeIndex place‖ ≤ bound :=
    ⟨1, norm_solvedMultiplier_le_one half_le_one basis timeIndex⟩
  have remainder_image : MemSobolev grade 2
      (fourierMultiplierCLM Value (remainderMultiplier (1 / 2) basis timeIndex) state) :=
    state_member.fourierMultiplierCLM_of_bounded
      (remainderMultiplier_hasTemperateGrowth (1 / 2) basis timeIndex)
      ⟨1, norm_remainderMultiplier_le_one half_le_one basis timeIndex⟩
  have source_image : MemSobolev grade 2
      (fourierMultiplierCLM Value (solvedMultiplier (1 / 2) basis timeIndex) source) :=
    source_member.fourierMultiplierCLM_of_bounded solved_temperate solved_bounded
  have flux_image : ∀ index ∈ Finset.univ.erase timeIndex, MemSobolev grade 2
      (fourierMultiplierCLM Value (solvedMultiplier (1 / 2) basis timeIndex)
        (∂_{basis index} (flux index))) := by
    intro index member
    have different : index ≠ timeIndex := (Finset.mem_erase.mp member).1
    have line_temperate : (fun place : Point =>
        2 * π * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)).HasTemperateGrowth := by
      fun_prop
    rw [lineDerivOp_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_fourierMultiplierCLM_apply line_temperate solved_temperate]
    refine (flux_member index member).fourierMultiplierCLM_of_bounded
      (line_temperate.mul solved_temperate) ⟨2 * π, fun place => ?_⟩
    have factored : ((fun place : Point =>
          2 * π * Complex.I * ((inner ℝ place (basis index) : ℝ) : ℂ)) *
          solvedMultiplier (1 / 2) basis timeIndex) place =
        (2 * (π : ℂ) * Complex.I) *
          (((inner ℝ place (basis index) : ℝ) : ℂ) *
            solvedMultiplier (1 / 2) basis timeIndex place) := by
      simp only [Pi.mul_apply]
      ring
    have head : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
      simp [abs_of_nonneg Real.pi_pos.le]
    rw [factored, norm_mul, head]
    nlinarith [norm_inner_mul_solvedMultiplier_le_one basis different place, Real.pi_pos]
  have image_member : MemSobolev grade 2 (besselPotential Point Value (1 / 2) state) := by
    rw [besselPotential_eq_solved_add_remainder (1 / 2) basis timeIndex, identity,
      map_add, map_sum]
    refine MemSobolev.add (MemSobolev.add source_image ?_) remainder_image
    exact Bessel.mem_sobolev.mp (AddSubgroup.sum_mem _ fun index member =>
      Bessel.mem_sobolev.mpr (flux_image index member))
  have gained := memSobolev_besselPotential_iff.mp image_member
  rwa [show (1 : ℝ) / 2 + grade = grade + 1 / 2 by ring] at gained

end Gain

section Localization

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

-- Subtractivity of localization is proved once, where `localize` is defined
-- (`InteriorRegularity.localize_sub`); it is re-exported here because the
-- localized heat identities below and their consumers reach for it under this
-- namespace.
export Hypostructure.PDE.Solution.InteriorRegularity (localize_sub)

theorem localize_finset_sum {Element : Type uIndex} (bump : Bump Point)
    (family : Element → 𝓢'(Point, Value)) (support : Finset Element) :
    localize bump (∑ index ∈ support, family index) =
      ∑ index ∈ support, localize bump (family index) :=
  map_sum _ _ _

/-- **The second-order Leibniz rule, with the surviving derivative kept outside.**

The usual form `∂ᵢ∂ᵢ(χ u) = χ ∂ᵢ∂ᵢu + 2 (∂ᵢχ)(∂ᵢu) + (∂ᵢ∂ᵢχ) u` has a middle
term that differentiates the *state*.  Rewriting that term as
`∂ᵢ((∂ᵢχ) u) − (∂ᵢ∂ᵢχ) u` moves the derivative onto the outside of a plain
localization.  This is what makes the parabolic bootstrap gain: a derivative
sitting outside costs only the half grade the heat operator can spare in a
spatial direction, whereas a derivative applied to the state would cost the
whole grade the operator gains. -/
theorem lineDerivOp_two_localize (direction : Point) (bump : Bump Point)
    (state : 𝓢'(Point, Value)) :
    ∂_{direction} (∂_{direction} (localize bump state)) =
      localize bump (∂_{direction} (∂_{direction} state)) +
        ((2 : ℂ) • ∂_{direction} (localize (bump.deriv direction) state) -
          localize ((bump.deriv direction).deriv direction) state) := by
  have inner_identity : localize (bump.deriv direction) (∂_{direction} state) =
      ∂_{direction} (localize (bump.deriv direction) state) -
        localize ((bump.deriv direction).deriv direction) state := by
    rw [lineDerivOp_localize direction (bump.deriv direction) state]
    abel
  rw [lineDerivOp_localize direction bump state, LineDerivAdd.lineDerivOp_add,
    lineDerivOp_localize direction bump (∂_{direction} state), inner_identity, two_smul]
  abel

theorem spatialLaplacian_localize (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    spatialLaplacian basis timeIndex (localize bump state) =
      localize bump (spatialLaplacian basis timeIndex state) +
        ∑ index ∈ Finset.univ.erase timeIndex,
          ((2 : ℂ) • ∂_{basis index} (localize (bump.deriv (basis index)) state) -
            localize ((bump.deriv (basis index)).deriv (basis index)) state) := by
  simp only [spatialLaplacian, lineDerivOp_two_localize]
  rw [localize_finset_sum, Finset.sum_add_distrib]

/-- **The heat commutator, localized.**

`(∂_t − Δ_x)(χ u)` is `χ (∂_t − Δ_x) u` plus terms every one of which carries a
derivative of the cutoff, and the only terms that carry a derivative at all
carry it *outside* a localization of `u`, along a **spatial** direction. -/
theorem shifted_heatOperator_localize (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    localize bump state + heatOperator basis timeIndex (localize bump state) =
      (localize bump state + localize bump (heatOperator basis timeIndex state) +
          localize (bump.deriv (basis timeIndex)) state +
          ∑ index ∈ Finset.univ.erase timeIndex,
            localize ((bump.deriv (basis index)).deriv (basis index)) state) +
        ∑ index ∈ Finset.univ.erase timeIndex,
          ∂_{basis index}
            ((-(2 : ℂ)) • localize (bump.deriv (basis index)) state) := by
  have derivative_smul : ∀ index : Index,
      ∂_{basis index} ((-(2 : ℂ)) • localize (bump.deriv (basis index)) state) =
        -((2 : ℂ) • ∂_{basis index} (localize (bump.deriv (basis index)) state)) := by
    intro index
    rw [LineDerivSMul.lineDerivOp_smul, neg_smul]
  simp only [heatOperator]
  rw [lineDerivOp_localize, spatialLaplacian_localize, localize_sub]
  simp only [derivative_smul]
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  abel

end Localization

section LocalGain

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- **The local one-step gain.**  A state and its heat image both at `grade` on a
window put the state at `grade + 1/2` there.

Half a grade, not a whole one: the heat operator gains one isotropic derivative,
and localizing spends half of it on the single spatial derivative the commutator
leaves outside. -/
theorem sobolevOn_add_half (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_held : SobolevOn region grade (heatOperator basis timeIndex state)) :
    SobolevOn region (grade + 1 / 2) state := by
  intro bump supported
  have deriv_supported : ∀ index : Index,
      tsupport (bump.deriv (basis index)).weight ⊆ region :=
    fun index => (bump.tsupport_deriv_subset (basis index)).trans supported
  have deriv_two_supported : ∀ index : Index,
      tsupport ((bump.deriv (basis index)).deriv (basis index)).weight ⊆ region :=
    fun index =>
      (Bump.tsupport_deriv_subset _ _).trans (deriv_supported index)
  refine memSobolev_add_half_of_split basis timeIndex
    (source := localize bump state + localize bump (heatOperator basis timeIndex state) +
      localize (bump.deriv (basis timeIndex)) state +
      ∑ index ∈ Finset.univ.erase timeIndex,
        localize ((bump.deriv (basis index)).deriv (basis index)) state)
    (flux := fun index => (-(2 : ℂ)) • localize (bump.deriv (basis index)) state)
    (shifted_heatOperator_localize basis timeIndex bump state)
    (state_held bump supported) ?_ ?_
  · refine MemSobolev.add (MemSobolev.add (MemSobolev.add (state_held bump supported)
      (source_held bump supported)) (state_held _ (deriv_supported timeIndex))) ?_
    exact Bessel.mem_sobolev.mp (AddSubgroup.sum_mem _ fun index _ =>
      Bessel.mem_sobolev.mpr (state_held _ (deriv_two_supported index)))
  · exact fun index _ => MemSobolev.smul _ (state_held _ (deriv_supported index))

/-- **The iteration.**  Half a grade per step reaches every whole multiple of a
half grade, and that is every grade. -/
theorem sobolevOn_add_half_natCast (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_smooth : SmoothOn region (heatOperator basis timeIndex state)) :
    ∀ step : ℕ, SobolevOn region (grade + step / 2) state := by
  intro step
  induction step with
  | zero => simpa using state_held
  | succ previous gained =>
      have advanced := sobolevOn_add_half basis timeIndex gained
        (source_smooth (grade + previous / 2))
      have rewrite : grade + (previous : ℝ) / 2 + 1 / 2 =
          grade + ((previous + 1 : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      rwa [rewrite] at advanced

/-- **The payoff.**  A state whose heat image is smooth on a window is itself
smooth there, once it sits at *some* grade there to start from. -/
theorem smoothOn_of_heat_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_smooth : SmoothOn region (heatOperator basis timeIndex state)) :
    SmoothOn region state := by
  intro target
  obtain ⟨step, step_ge⟩ := exists_nat_ge (2 * (target - grade))
  refine SobolevOn.mono_grade ?_
    (sobolevOn_add_half_natCast basis timeIndex state_held source_smooth step)
  linarith

/-- **The payoff on nested windows.** -/
theorem smoothOn_ball_of_heat_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (center : Point) {inner outer : ℝ} (nested : inner ≤ outer)
    {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outer) grade state)
    (source_smooth : SmoothOn (ball center outer) (heatOperator basis timeIndex state)) :
    SmoothOn (ball center inner) state :=
  (smoothOn_of_heat_smoothOn basis timeIndex state_held source_smooth).mono_region
    (ball_subset_ball nested)

/-- **The bootstrap on the framework's chain of shrinking windows.** -/
theorem sobolevOn_chain_of_heat (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (center : Point) {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outerRadius) grade state)
    (source_smooth : SmoothOn (ball center outerRadius)
      (heatOperator basis timeIndex state)) :
    ∀ step : ℕ,
      SobolevOn (closedBall center innerRadius) (grade + step / 2) state := by
  refine Hypostructure.PDE.HeatSmoothing.regular_closedBall_of_chain center nested
    (regular := fun step region => SobolevOn region (grade + step / 2) state)
    (fun _ _ _ subset held => held.mono_region subset) (by simpa using state_held) ?_
  intro step held
  have source_here :
      SobolevOn (ball center
        (Hypostructure.PDE.HeatSmoothing.chainRadius innerRadius outerRadius step))
        (grade + step / 2) (heatOperator basis timeIndex state) :=
    (source_smooth (grade + step / 2)).mono_region
      (ball_subset_ball (chainRadius_le_outer nested step))
  have advanced := sobolevOn_add_half basis timeIndex held source_here
  have shrunk := advanced.mono_region (ball_subset_ball
    (Hypostructure.PDE.HeatSmoothing.chainRadius_succ_lt nested step).le)
  have rewrite : grade + (step : ℝ) / 2 + 1 / 2 = grade + ((step + 1 : ℕ) : ℝ) / 2 := by
    push_cast
    ring
  rwa [rewrite] at shrunk

end LocalGain

end Hypostructure.PDE.Solution.ParabolicRegularity
