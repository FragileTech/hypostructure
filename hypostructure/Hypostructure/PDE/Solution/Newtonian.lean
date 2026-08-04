import Hypostructure.PDE.Solution.Potential
import Hypostructure.PDE.Solution.RadialKernel

/-!
# The Newtonian kernel in three dimensions

`RadialKernel` proves the dimension-generic half of every classical
fundamental solution — the radial power `‖x‖^{2-n}` is locally integrable.
This module specialises that to the case the framework actually names, the
Laplacian on a three-dimensional real inner-product space, where the kernel is
the Newtonian potential

```text
newtonianKernel x = -(4 π ‖x‖)⁻¹.
```

Three-dimensional inner-product spaces carry a canonical `volume`
(`measureSpaceOfInnerProductSpace`: the additive Haar measure giving the
parallelepiped of an orthonormal basis mass one), so the normalisation
constant `4 π` is not a convention here but a computed number, and this file
computes it: `volume.toSphere univ = 4 π` is the total surface measure of the
unit sphere, obtained from `Measure.toSphere_apply_univ` and the closed-form
volume of a ball in an inner-product space.  That is exactly the constant the
excision argument produces in the limit, which is why the kernel carries its
reciprocal.

Both halves of the classical fundamental-solution statement are proved here.

The homogeneous half is `laplacian_newtonianKernel`: the kernel is **harmonic
away from the origin**, `Δ E = 0` on `{x ≠ 0}`.  That is the calculation which
singles out the exponent `2 - n`, and it is carried out at the level of
Fréchet derivatives, so no coordinates are ever chosen.

The inhomogeneous half is `newtonianKernel_inverts`, `E ⋆ Δφ = φ` for smooth
compactly supported `φ`, and with it the registered
`newtonianFundamentalSolution`.  The classical route to it — excision on an
annulus and Green's identity — is not available, because mathlib's divergence
theorem is stated for boxes in `Fin n → ℝ` and not for annuli in an abstract
inner-product space.  So the singularity is *mollified* instead of excised:

* `mollifiedKernel w x = -(4π)⁻¹ (‖x‖² + w²)^{-1/2}` rounds the origin off and
  is smooth everywhere, with the closed-form Laplacian
  `mollifiedDensity w x = 3 w² (4π)⁻¹ (‖x‖² + w²)^{-5/2}`;
* `integral_mul_laplacian` is Green's identity `∫ f Δg = ∫ (Δf) g` for a
  compactly supported `g`, obtained by summing mathlib's *line-derivative*
  integration by parts (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`,
  which needs no boundary at all) over an orthonormal basis — the compact
  support of `g`, not a boundary term, is what makes it work;
* `convolution_mollifiedKernel` combines the two into the exact identity
  `E_w ⋆ Δφ = (Δ E_w) ⋆ φ`, valid at every rounding scale;
* `integral_mollifiedDensity` computes the mass of `Δ E_w` to be exactly one —
  this is where the `4 π` of the kernel is spent — so that
  `tendsto_convolution_mollifiedDensity` identifies the family as an
  approximate identity, while `tendsto_convolution_mollifiedKernel` sends the
  other side to `E ⋆ Δφ` by dominated convergence, the singular kernel
  dominating all of its own roundings.

Letting the scale go to zero along `1/(n+1)` and comparing the two limits of
one and the same sequence is the whole of `newtonianKernel_inverts`.
-/

namespace Hypostructure.PDE.Solution

open MeasureTheory Metric Set Module
open scoped Real Convolution ENNReal RealInnerProductSpace Laplacian

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point]

/-!
## The kernel
-/

/--
The Newtonian kernel `x ↦ -(4 π ‖x‖)⁻¹`.

The sign is fixed by the convention `Δ` (not `-Δ`) is the operator being
inverted, and the constant by the surface measure of the unit sphere computed
below.  At the origin the junk value `0` is taken, which is harmless: the
origin is a null set, and it is also the value the radial power kernel takes
there, as `newtonianKernel_eq_radialKernel` records.
-/
noncomputable def newtonianKernel (place : Point) : ℝ := -(4 * π * ‖place‖)⁻¹

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
@[simp] theorem newtonianKernel_zero : newtonianKernel (0 : Point) = 0 := by
  simp [newtonianKernel]

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
/--
The Newtonian kernel is a constant multiple of the real power `‖x‖^{-1}`.

This is the form every differentiation below uses, because `Real.rpow` is
where mathlib's derivative lemmas for powers of the norm live.  The identity
holds at the origin as well: `Real.rpow` sends `0 ^ (-1)` to `0`, and
`(4 π · 0)⁻¹` is `0` too, so no excision is needed to state it.
-/
theorem newtonianKernel_eq_rpow :
    (newtonianKernel : Point → ℝ) = fun place => -(4 * π)⁻¹ * ‖place‖ ^ (-1 : ℝ) := by
  funext place
  rcases eq_or_ne place 0 with origin | away
  · simp [newtonianKernel, origin, Real.zero_rpow]
  · show -(4 * π * ‖place‖)⁻¹ = -(4 * π)⁻¹ * ‖place‖ ^ (-1 : ℝ)
    rw [Real.rpow_neg_one, mul_inv]
    ring

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/--
The Newtonian kernel is a constant multiple of the radial power kernel of
`RadialKernel`, at the exponent `n - 2` that the Laplacian selects.

In dimension three that exponent is `1`, so the radial power is `‖x‖⁻¹`.  The
identity holds at the origin too, for the same reason as above: neither side
needs excising.
-/
theorem newtonianKernel_eq_radialKernel (dimension : finrank ℝ Point = 3) :
    (newtonianKernel : Point → ℝ) =
      fun place => -(4 * π)⁻¹ * radialKernel ((finrank ℝ Point : ℝ) - 2) place := by
  rw [newtonianKernel_eq_rpow, dimension]
  funext place
  show -(4 * π)⁻¹ * ‖place‖ ^ (-1 : ℝ) = -(4 * π)⁻¹ * ‖place‖ ^ (-((3 : ℝ) - 2))
  norm_num

/--
The Newtonian kernel is locally integrable, which is the hypothesis
`FundamentalSolution` asks for.

Nothing is reproved: this is `locallyIntegrable_newtonianKernel` of
`RadialKernel` — polar coordinates against the `r^{n-1}` Jacobian — rescaled
by the normalising constant.
-/
theorem newtonianKernel_locallyIntegrable (dimension : finrank ℝ Point = 3) :
    LocallyIntegrable (newtonianKernel : Point → ℝ) volume := by
  haveI : Nontrivial Point :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [dimension]; norm_num)
  rw [newtonianKernel_eq_radialKernel dimension]
  exact (locallyIntegrable_newtonianKernel (Point := Point) volume).smul (-(4 * π)⁻¹)

/-!
## The normalising constant

The `4 π` in the kernel is the total surface measure of the unit sphere.
Mathlib supplies both halves: `Measure.toSphere_apply_univ` states that the
sphere measure of the whole sphere is the dimension times the volume of the
unit ball, and `InnerProductSpace.volume_ball_of_dim_odd` evaluates that
volume in closed form.
-/

/--
The volume of the unit ball in a three-dimensional inner-product space is
`4 π / 3`.

This is `InnerProductSpace.volume_ball_of_dim_odd` at `n = 2 · 1 + 1`, where
the double factorial `3‼` is `3`.  It is the only place a dimension-specific
number enters.
-/
theorem volume_unit_ball (dimension : finrank ℝ Point = 3) :
    volume (ball (0 : Point) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by rw [dimension]), dimension]
  norm_num [Nat.doubleFactorial]
  ring_nf

/--
**The surface measure of the unit sphere is `4 π`.**

This is where the constant in `newtonianKernel` comes from: the excision
argument produces the source value at the centre multiplied by the total
surface measure of the sphere, so the kernel has to carry its reciprocal for
the fundamental-solution identity to hold with no leftover factor.

The proof is one mathlib identity — `Measure.toSphere_apply_univ`, the polar
decomposition's statement that the sphere measure of the whole sphere is the
dimension times the volume of the unit ball — applied to the ball volume
computed above.
-/
theorem toSphere_univ (dimension : finrank ℝ Point = 3) :
    (volume : Measure Point).toSphere univ = ENNReal.ofReal (4 * π) := by
  rw [Measure.toSphere_apply_univ, volume_unit_ball dimension, dimension]
  rw [show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-!
## Harmonicity away from the origin

The second half of the classical statement "`E` is a fundamental solution for
`Δ`" is that `E` solves the *homogeneous* equation everywhere except at the
singularity.  That is a pure calculation, and it is done here in full.

The route is the obvious one, carried out at the level of Fréchet
derivatives so that no coordinates are ever chosen:

* `hasFDerivAt_rpow_norm` differentiates `‖x‖^t` away from the origin, giving
  the radial gradient `t ‖x‖^{t-2} ⟪x, ·⟫`;
* `hasFDerivAt_newtonianGradient` differentiates that once more, by the
  product rule for a scalar field times the (linear, hence self-derivative)
  field `x ↦ ⟪x, ·⟫`;
* `laplacian_newtonianKernel` traces the resulting Hessian against an
  orthonormal basis.  The trace of `⟪·,·⟫` is the dimension and the trace of
  `⟪x, ·⟫ ⟪x, ·⟫` is `‖x‖²`, so the two terms are `3 ‖x‖^{-3}` and
  `-3 ‖x‖^{-5} ‖x‖²`.  They cancel — and they cancel *because* the dimension
  is three, which is exactly the reason the exponent `2 - n` is the right one.
-/

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/--
Away from the origin every real power of the norm is differentiable, with the
radial gradient `t ‖x‖^{t-2} ⟪x, ·⟫`.

Mathlib proves this for `1 < t` only (`hasFDerivAt_norm_rpow`), because there
it also holds *at* the origin; away from the origin the same one-line
composition of `hasStrictFDerivAt_norm_sq` with `rpow_const` works for every
exponent, and negative exponents are the ones a fundamental solution needs.
-/
theorem hasFDerivAt_rpow_norm {place : Point} (nonzero : place ≠ 0) (exponent : ℝ) :
    HasFDerivAt (fun spot : Point => ‖spot‖ ^ exponent)
      ((exponent * ‖place‖ ^ (exponent - 2)) • innerSL ℝ place) place := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq place).rpow_const (p := exponent / 2)
    (by simp [nonzero]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/--
The inner product read as a genuinely `ℝ`-linear map into the dual,
`v ↦ ⟪v, ·⟫`.

Mathlib types `innerSL` as *conjugate*-linear in its first slot, which is the
right general statement but leaves the real case with an arrow `→L⋆[ℝ]` that
will not add to the honestly linear maps produced by the product rule.  Over
`ℝ` conjugation is the identity, so the same map is linear; naming it once
here is what lets the Hessian below be written as a sum.
-/
noncomputable def innerBilinear : Point →L[ℝ] Point →L[ℝ] ℝ := innerSL ℝ

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
@[simp] theorem innerBilinear_apply (first second : Point) :
    innerBilinear first second = ⟪first, second⟫ := rfl

/--
The gradient field of the Newtonian kernel, `x ↦ (4 π)⁻¹ ‖x‖^{-3} ⟪x, ·⟫`.

Naming it is what makes the second differentiation a product rule rather than
an exercise in rewriting under a binder.
-/
noncomputable def newtonianGradient (place : Point) : Point →L[ℝ] ℝ :=
  ((4 * π)⁻¹ * ‖place‖ ^ (-3 : ℝ)) • innerBilinear place

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- Away from the origin the Newtonian kernel is differentiable, with
derivative `newtonianGradient`. -/
theorem hasFDerivAt_newtonianKernel {place : Point} (nonzero : place ≠ 0) :
    HasFDerivAt (newtonianKernel : Point → ℝ) (newtonianGradient place) place := by
  rw [newtonianKernel_eq_rpow]
  refine ((hasFDerivAt_rpow_norm nonzero (-1 : ℝ)).const_mul (-(4 * π)⁻¹)).congr_fderiv ?_
  show (-(4 * π)⁻¹ : ℝ) • (((-1 : ℝ) * ‖place‖ ^ ((-1 : ℝ) - 2)) • innerSL ℝ place) =
    newtonianGradient place
  rw [smul_smul]
  show _ = ((4 * π)⁻¹ * ‖place‖ ^ (-3 : ℝ)) • innerSL ℝ place
  norm_num

/--
The Hessian field of the Newtonian kernel:

```text
D²E(x)(v, w) = (4 π)⁻¹ ‖x‖^{-3} ⟪v, w⟫ - 3 (4 π)⁻¹ ‖x‖^{-5} ⟪x, v⟫ ⟪x, w⟫.
```

The first summand comes from differentiating the *direction* of the radial
gradient, the second from differentiating its *size*; their traces are what
cancel.
-/
noncomputable def newtonianHessian (place : Point) : Point →L[ℝ] Point →L[ℝ] ℝ :=
  ((4 * π)⁻¹ * ‖place‖ ^ (-3 : ℝ)) • innerBilinear +
    (((4 * π)⁻¹ * (-3 * ‖place‖ ^ (-5 : ℝ))) • innerBilinear place).smulRight
      (innerBilinear place)

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/--
Away from the origin the gradient field is itself differentiable, with
derivative `newtonianHessian`.

This is the product rule `HasFDerivAt.smul` applied to the scalar field
`(4 π)⁻¹ ‖x‖^{-3}` and the field `v ↦ ⟪v, ·⟫`, the latter being a continuous
linear map and so its own derivative.
-/
theorem hasFDerivAt_newtonianGradient {place : Point} (nonzero : place ≠ 0) :
    HasFDerivAt (newtonianGradient : Point → Point →L[ℝ] ℝ)
      (newtonianHessian place) place := by
  have radial : HasFDerivAt (fun spot : Point => (4 * π)⁻¹ * ‖spot‖ ^ (-3 : ℝ))
      (((4 * π)⁻¹ * (-3 * ‖place‖ ^ (-5 : ℝ))) • innerBilinear place) place := by
    refine ((hasFDerivAt_rpow_norm nonzero (-3 : ℝ)).const_mul ((4 * π)⁻¹)).congr_fderiv ?_
    show ((4 * π)⁻¹ : ℝ) • (((-3 : ℝ) * ‖place‖ ^ ((-3 : ℝ) - 2)) • innerSL ℝ place) = _
    rw [smul_smul]
    show _ = ((4 * π)⁻¹ * (-3 * ‖place‖ ^ (-5 : ℝ))) • innerSL ℝ place
    norm_num
  exact radial.smul (innerBilinear : Point →L[ℝ] Point →L[ℝ] ℝ).hasFDerivAt

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/--
The second Fréchet derivative of the Newtonian kernel away from the origin.

Passing from `hasFDerivAt_newtonianGradient` to a statement about
`fderiv (fderiv E)` needs the gradient identity on a whole *neighbourhood*,
not just at the point — and it holds on the complement of the origin, which
is open.
-/
theorem fderiv_fderiv_newtonianKernel {place : Point} (nonzero : place ≠ 0) :
    fderiv ℝ (fderiv ℝ (newtonianKernel : Point → ℝ)) place = newtonianHessian place := by
  have nearby : fderiv ℝ (newtonianKernel : Point → ℝ) =ᶠ[nhds place] newtonianGradient :=
    (eventually_ne_nhds nonzero).mono fun _ away =>
      (hasFDerivAt_newtonianKernel away).fderiv
  rw [nearby.fderiv_eq]
  exact (hasFDerivAt_newtonianGradient nonzero).fderiv

omit [MeasurableSpace Point] [BorelSpace Point] in
/--
**The Newtonian kernel is harmonic away from the origin.**

Tracing `newtonianHessian` against an orthonormal basis gives
`3 (4 π)⁻¹ ‖x‖^{-3}` from the first summand — the trace of the inner product
is the dimension — and `-3 (4 π)⁻¹ ‖x‖^{-5} ‖x‖²` from the second, since
`∑ ⟪x, e i⟫² = ‖x‖²`.  In dimension three the two agree and cancel.

This is the homogeneous half of the fundamental-solution property; the
inhomogeneous half is the excision limit at the origin, which is where the
constant `4 π` computed above enters.
-/
theorem laplacian_newtonianKernel (dimension : finrank ℝ Point = 3) {place : Point}
    (nonzero : place ≠ 0) : Δ (newtonianKernel : Point → ℝ) place = 0 := by
  classical
  have positive : 0 < ‖place‖ := norm_pos_iff.mpr nonzero
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (newtonianKernel : Point → ℝ) (stdOrthonormalBasis ℝ Point)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_newtonianKernel nonzero, newtonianHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerBilinear_apply, smul_eq_mul]
  have direction : ∀ index : Fin (finrank ℝ Point),
      ⟪stdOrthonormalBasis ℝ Point index, stdOrthonormalBasis ℝ Point index⟫ = (1 : ℝ) := by
    intro index
    rw [real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ Point).orthonormal.1 index, one_pow]
  have size : ∑ index, ⟪place, stdOrthonormalBasis ℝ Point index⟫ *
      ⟪place, stdOrthonormalBasis ℝ Point index⟫ = ‖place‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      ← (stdOrthonormalBasis ℝ Point).sum_inner_mul_inner place place]
    exact Finset.sum_congr rfl fun index _ => by
      rw [real_inner_comm (stdOrthonormalBasis ℝ Point index) place]
  have power : ‖place‖ ^ (-5 : ℝ) * ‖place‖ ^ 2 = ‖place‖ ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast ‖place‖ 2, ← Real.rpow_add positive]
    norm_num
  have second : ∑ index, (4 * π)⁻¹ * (-3 * ‖place‖ ^ (-5 : ℝ)) *
        ⟪place, stdOrthonormalBasis ℝ Point index⟫ *
        ⟪place, stdOrthonormalBasis ℝ Point index⟫
      = (4 * π)⁻¹ * (-3 * ‖place‖ ^ (-5 : ℝ)) * ‖place‖ ^ 2 := by
    rw [← size, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [direction, mul_one]
  rw [Finset.sum_add_distrib, second, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    dimension, nsmul_eq_mul]
  push_cast
  linear_combination (-3 * (4 * π)⁻¹) * power

/-!
## The potential

With the kernel registered as locally integrable, its convolution against a
compactly supported smooth source is defined and smooth.  This is the half of
the solution operator that needs no inversion law, and it is what
`FundamentalSolution.potential` and `FundamentalSolution.contDiff_potential`
would specialise to once the inversion law is available.
-/

/-- The Newtonian potential of a source: convolution with the Newtonian kernel. -/
noncomputable def newtonianPotential (source : Point → ℝ) : Point → ℝ :=
  newtonianKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source

/--
The Newtonian potential of a compactly supported smooth source is smooth.

This is `HasCompactSupport.contDiff_convolution_right` fed with the local
integrability proved above: differentiation passes onto the source, which is
as smooth as one likes, and the kernel is only ever integrated against.
-/
theorem contDiff_newtonianPotential (dimension : finrank ℝ Point = 3) {source : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent source) (compact : HasCompactSupport source) :
    ContDiff ℝ smoothExponent (newtonianPotential source) :=
  compact.contDiff_convolution_right _ (newtonianKernel_locallyIntegrable dimension) smooth


/-!
## Integration by parts

The inhomogeneous half of the fundamental-solution property is Green's
identity `∫ E Δφ = ∫ (ΔE) φ`, valid whenever one of the two factors has
compact support so that no boundary term survives.

Mathlib proves the one-directional version of this
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`: `∫ f ∂ᵥg = -∫ (∂ᵥf) g`
for a Haar measure on any finite-dimensional real normed space, under
integrability of the three products involved).  Applying it twice in each
coordinate direction of an orthonormal basis and summing turns it into
Green's identity, because the Laplacian *is* that sum of second directional
derivatives.  No divergence theorem and no annulus is needed: the compact
support of the test function is what kills the boundary.
-/

/-- The derivative of a scalar field in a fixed direction, as a scalar field.

Naming it is what lets the two integrations by parts below be stated as one
lemma applied twice: the second application takes the output of the first as
its input. -/
noncomputable def derivAlong (field : Point → ℝ) (direction : Point) : Point → ℝ :=
  fun place => fderiv ℝ field place direction

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- One directional derivative costs no smoothness at the `C^∞` grade. -/
theorem contDiff_derivAlong {field : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent field) (direction : Point) :
    ContDiff ℝ smoothExponent (derivAlong field direction) :=
  (ContinuousLinearMap.apply ℝ ℝ direction).contDiff.comp
    (smooth.fderiv_right (by simp [smoothExponent]))

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- Differentiating does not enlarge the support. -/
theorem hasCompactSupport_derivAlong {field : Point → ℝ}
    (compact : HasCompactSupport field) (direction : Point) :
    HasCompactSupport (derivAlong field direction) :=
  HasCompactSupport.comp_left (g := fun linear : Point →L[ℝ] ℝ => linear direction)
    (compact.fderiv ℝ) rfl

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The second directional derivative is the Hessian evaluated twice in the
same direction. -/
theorem derivAlong_derivAlong {field : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent field) (direction place : Point) :
    derivAlong (derivAlong field direction) direction place
      = fderiv ℝ (fderiv ℝ field) place direction direction := by
  have differentiable : DifferentiableAt ℝ (fderiv ℝ field) place :=
    ((smooth.fderiv_right (m := smoothExponent) (by simp [smoothExponent])).differentiable
      (by simp [smoothExponent])).differentiableAt
  have chain : HasFDerivAt (derivAlong field direction)
      ((ContinuousLinearMap.apply ℝ ℝ direction).comp
        (fderiv ℝ (fderiv ℝ field) place)) place :=
    (ContinuousLinearMap.apply ℝ ℝ direction).hasFDerivAt.comp place
      differentiable.hasFDerivAt
  show fderiv ℝ (derivAlong field direction) place direction = _
  rw [chain.fderiv]
  rfl

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- The Laplacian is the sum of the second directional derivatives along an
orthonormal basis.  This is mathlib's definition, rewritten in the notation
the integration by parts below uses. -/
theorem laplacian_eq_sum_derivAlong {field : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent field) (place : Point) :
    Δ field place = ∑ index : Fin (finrank ℝ Point),
      derivAlong (derivAlong field (stdOrthonormalBasis ℝ Point index))
        (stdOrthonormalBasis ℝ Point index) place := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis field
    (stdOrthonormalBasis ℝ Point)]
  refine Finset.sum_congr rfl fun index _ => ?_
  rw [derivAlong_derivAlong smooth, iteratedFDeriv_two_apply]
  rfl

/-- A continuous field times a compactly supported continuous field is
integrable: the product is continuous and compactly supported. -/
theorem integrable_mul_of_hasCompactSupport {left right : Point → ℝ}
    (continuousLeft : Continuous left) (continuousRight : Continuous right)
    (compactRight : HasCompactSupport right) :
    Integrable (fun place => left place * right place) volume :=
  (continuousLeft.mul continuousRight).integrable_of_hasCompactSupport
    compactRight.mul_left

/--
**Integration by parts twice, in one direction.**

`∫ f ∂ᵥ∂ᵥ g = ∫ (∂ᵥ∂ᵥ f) g` when `g` has compact support: the first
application of mathlib's `∫ f ∂ᵥg = -∫ (∂ᵥf) g` moves one derivative onto
`f`, the second moves the other, and the two sign changes cancel.  Only `g`
needs compact support; `f` is arbitrary smooth, which is what lets the
mollified Newtonian kernel — which decays but is not compactly supported —
play the role of `f`.
-/
theorem integral_mul_derivAlong_derivAlong {outer test : Point → ℝ}
    (smoothOuter : ContDiff ℝ smoothExponent outer)
    (smoothTest : ContDiff ℝ smoothExponent test)
    (compactTest : HasCompactSupport test) (direction : Point) :
    (∫ place, outer place * derivAlong (derivAlong test direction) direction place)
      = ∫ place, derivAlong (derivAlong outer direction) direction place * test place := by
  have continuousOuter : Continuous outer := smoothOuter.continuous
  have continuousTest : Continuous test := smoothTest.continuous
  have smoothOuterFirst := contDiff_derivAlong smoothOuter direction
  have smoothOuterSecond := contDiff_derivAlong smoothOuterFirst direction
  have smoothTestFirst := contDiff_derivAlong smoothTest direction
  have smoothTestSecond := contDiff_derivAlong smoothTestFirst direction
  have compactTestFirst := hasCompactSupport_derivAlong compactTest direction
  have compactTestSecond := hasCompactSupport_derivAlong compactTestFirst direction
  have differentiableOuter : ∀ place : Point, DifferentiableAt ℝ outer place := fun place =>
    (smoothOuter.differentiable (by simp [smoothExponent])).differentiableAt
  have differentiableOuterFirst :
      ∀ place : Point, DifferentiableAt ℝ (derivAlong outer direction) place := fun place =>
    (smoothOuterFirst.differentiable (by simp [smoothExponent])).differentiableAt
  have differentiableTest : ∀ place : Point, DifferentiableAt ℝ test place := fun place =>
    (smoothTest.differentiable (by simp [smoothExponent])).differentiableAt
  have differentiableTestFirst :
      ∀ place : Point, DifferentiableAt ℝ (derivAlong test direction) place := fun place =>
    (smoothTestFirst.differentiable (by simp [smoothExponent])).differentiableAt
  have first := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Point)) (f := outer) (g := derivAlong test direction) (v := direction)
    (integrable_mul_of_hasCompactSupport smoothOuterFirst.continuous
      smoothTestFirst.continuous compactTestFirst)
    (integrable_mul_of_hasCompactSupport continuousOuter
      smoothTestSecond.continuous compactTestSecond)
    (integrable_mul_of_hasCompactSupport continuousOuter
      smoothTestFirst.continuous compactTestFirst)
    (fun place _ => differentiableOuter place) (fun place _ => differentiableTestFirst place)
  have second := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Point)) (f := derivAlong outer direction) (g := test) (v := direction)
    (integrable_mul_of_hasCompactSupport smoothOuterSecond.continuous
      continuousTest compactTest)
    (integrable_mul_of_hasCompactSupport smoothOuterFirst.continuous
      smoothTestFirst.continuous compactTestFirst)
    (integrable_mul_of_hasCompactSupport smoothOuterFirst.continuous
      continuousTest compactTest)
    (fun place _ => differentiableOuterFirst place) (fun place _ => differentiableTest place)
  simp only [derivAlong] at first second ⊢
  rw [first, second, neg_neg]

/--
**Green's identity for a compactly supported test function.**

`∫ E Δφ = ∫ (ΔE) φ`.  Summing the two-fold integration by parts over an
orthonormal basis is exactly this, because the Laplacian is by definition
the trace of the Hessian.
-/
theorem integral_mul_laplacian {outer test : Point → ℝ}
    (smoothOuter : ContDiff ℝ smoothExponent outer)
    (smoothTest : ContDiff ℝ smoothExponent test) (compactTest : HasCompactSupport test) :
    (∫ place, outer place * Δ test place) = ∫ place, Δ outer place * test place := by
  have leftSum : ∀ place : Point, outer place * Δ test place
      = ∑ index : Fin (finrank ℝ Point), outer place *
        derivAlong (derivAlong test (stdOrthonormalBasis ℝ Point index))
          (stdOrthonormalBasis ℝ Point index) place := fun place => by
    rw [laplacian_eq_sum_derivAlong smoothTest, Finset.mul_sum]
  have rightSum : ∀ place : Point, Δ outer place * test place
      = ∑ index : Fin (finrank ℝ Point),
        derivAlong (derivAlong outer (stdOrthonormalBasis ℝ Point index))
          (stdOrthonormalBasis ℝ Point index) place * test place := fun place => by
    rw [laplacian_eq_sum_derivAlong smoothOuter, Finset.sum_mul]
  simp_rw [leftSum, rightSum]
  rw [integral_finsetSum _ fun index _ =>
      integrable_mul_of_hasCompactSupport smoothOuter.continuous
        (contDiff_derivAlong (contDiff_derivAlong smoothTest _) _).continuous
        (hasCompactSupport_derivAlong (hasCompactSupport_derivAlong compactTest _) _),
    integral_finsetSum _ fun index _ =>
      integrable_mul_of_hasCompactSupport
        (contDiff_derivAlong (contDiff_derivAlong smoothOuter _) _).continuous
        smoothTest.continuous compactTest]
  exact Finset.sum_congr rfl fun index _ =>
    integral_mul_derivAlong_derivAlong smoothOuter smoothTest compactTest _

/-!
## The mollified kernel

Green's identity needs a *smooth* kernel, and the Newtonian kernel is not
smooth at the origin — that singularity is the whole point.  So the origin is
rounded off:

```text
E_w x = -(4 π)⁻¹ (‖x‖² + w²)^{-1/2},
```

which is smooth everywhere for `w ≠ 0`, agrees with `E` in the limit `w → 0`,
and — this is the reason for this particular rounding — has a Laplacian in
closed form,

```text
Δ E_w x = 3 w² (4 π)⁻¹ (‖x‖² + w²)^{-5/2},
```

a nonnegative bump of total mass one which concentrates at the origin as
`w → 0`.  In other words `Δ E_w` is an approximate identity, and it is one
for which every constant is explicit rather than obtained from a compactness
argument.
-/

/-- The Newtonian kernel with its singularity rounded off at scale `width`. -/
noncomputable def mollifiedKernel (width : ℝ) (place : Point) : ℝ :=
  -(4 * π)⁻¹ * (‖place‖ ^ 2 + width ^ 2) ^ (-(1 : ℝ) / 2)

/-- The Laplacian of the mollified kernel: a nonnegative bump of mass one. -/
noncomputable def mollifiedDensity (width : ℝ) (place : Point) : ℝ :=
  3 * width ^ 2 * (4 * π)⁻¹ * (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
/-- The rounded-off radius is positive, which is what makes every power of it
below smooth. -/
theorem mollifiedRadius_pos {width : ℝ} (nonzero : width ≠ 0) (place : Point) :
    0 < ‖place‖ ^ 2 + width ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (abs_pos.mpr nonzero) 2 |>.trans_le
    (le_of_eq (sq_abs width)))

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The rounded radius is differentiable, with the derivative of a square. -/
theorem hasFDerivAt_mollifiedRadius (width : ℝ) (place : Point) :
    HasFDerivAt (fun spot : Point => ‖spot‖ ^ 2 + width ^ 2)
      ((2 : ℕ) • innerSL ℝ place) place :=
  (hasStrictFDerivAt_norm_sq place).hasFDerivAt.add_const _

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The mollified kernel is smooth: it is a negative power of a function that
never vanishes. -/
theorem contDiff_mollifiedKernel {width : ℝ} (nonzero : width ≠ 0) :
    ContDiff ℝ smoothExponent (mollifiedKernel (Point := Point) width) := by
  have radius : ContDiff ℝ smoothExponent (fun spot : Point => ‖spot‖ ^ 2 + width ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  refine contDiff_iff_contDiffAt.2 fun place => contDiffAt_const.mul ?_
  exact (Real.contDiffAt_rpow_const_of_ne (p := -(1 : ℝ) / 2)
    (mollifiedRadius_pos nonzero place).ne').comp place radius.contDiffAt

/-- The gradient field of the mollified kernel. -/
noncomputable def mollifiedGradient (width : ℝ) (place : Point) : Point →L[ℝ] ℝ :=
  ((4 * π)⁻¹ * (‖place‖ ^ 2 + width ^ 2) ^ (-(3 : ℝ) / 2)) • innerBilinear place

/-- The Hessian field of the mollified kernel. -/
noncomputable def mollifiedHessian (width : ℝ) (place : Point) : Point →L[ℝ] Point →L[ℝ] ℝ :=
  ((4 * π)⁻¹ * (‖place‖ ^ 2 + width ^ 2) ^ (-(3 : ℝ) / 2)) • innerBilinear +
    (((4 * π)⁻¹ * (-3 * (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2))) •
      innerBilinear place).smulRight (innerBilinear place)

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The mollified kernel is differentiable everywhere, with the rounded
analogue of the Newtonian gradient. -/
theorem hasFDerivAt_mollifiedKernel {width : ℝ} (nonzero : width ≠ 0) (place : Point) :
    HasFDerivAt (mollifiedKernel width) (mollifiedGradient width place) place := by
  refine (((hasFDerivAt_mollifiedRadius width place).rpow_const
    (Or.inl (mollifiedRadius_pos nonzero place).ne')).const_mul
      (-(4 * π)⁻¹)).congr_fderiv ?_
  ext direction
  simp only [smul_apply, smul_eq_mul, mollifiedGradient, innerBilinear_apply, nsmul_eq_mul,
    innerSL_apply_apply, Nat.cast_ofNat]
  rw [show (-(1 : ℝ) / 2 - 1) = -(3 : ℝ) / 2 by norm_num]
  ring

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The gradient field of the mollified kernel is itself differentiable. -/
theorem hasFDerivAt_mollifiedGradient {width : ℝ} (nonzero : width ≠ 0) (place : Point) :
    HasFDerivAt (mollifiedGradient width) (mollifiedHessian width place) place := by
  have radial : HasFDerivAt
      (fun spot : Point => (4 * π)⁻¹ * (‖spot‖ ^ 2 + width ^ 2) ^ (-(3 : ℝ) / 2))
      (((4 * π)⁻¹ * (-3 * (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2))) •
        innerBilinear place) place := by
    refine (((hasFDerivAt_mollifiedRadius width place).rpow_const
      (Or.inl (mollifiedRadius_pos nonzero place).ne')).const_mul ((4 * π)⁻¹)).congr_fderiv ?_
    ext direction
    simp only [smul_apply, smul_eq_mul, innerBilinear_apply, nsmul_eq_mul,
      innerSL_apply_apply, Nat.cast_ofNat]
    rw [show (-(3 : ℝ) / 2 - 1) = -(5 : ℝ) / 2 by norm_num]
    ring
  exact radial.smul (innerBilinear : Point →L[ℝ] Point →L[ℝ] ℝ).hasFDerivAt

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The second Fréchet derivative of the mollified kernel, everywhere. -/
theorem fderiv_fderiv_mollifiedKernel {width : ℝ} (nonzero : width ≠ 0) (place : Point) :
    fderiv ℝ (fderiv ℝ (mollifiedKernel width)) place = mollifiedHessian (Point := Point) width
      place := by
  have nearby : fderiv ℝ (mollifiedKernel (Point := Point) width) = mollifiedGradient width :=
    funext fun spot => (hasFDerivAt_mollifiedKernel nonzero spot).fderiv
  rw [nearby]
  exact (hasFDerivAt_mollifiedGradient nonzero place).fderiv

omit [MeasurableSpace Point] [BorelSpace Point] in
/--
**The Laplacian of the mollified kernel is the explicit bump.**

The trace of the Hessian is `3 (4π)⁻¹ b^{-3/2} - 3 (4π)⁻¹ b^{-5/2} ‖x‖²`
with `b = ‖x‖² + w²`, and `b^{-3/2} = b^{-5/2} b`, so the two terms combine
into `3 w² (4π)⁻¹ b^{-5/2}`.  For `w = 0` this is zero, which is
`laplacian_newtonianKernel` again; for `w ≠ 0` it is a positive bump whose
mass is computed below.
-/
theorem laplacian_mollifiedKernel (dimension : finrank ℝ Point = 3) {width : ℝ}
    (nonzero : width ≠ 0) (place : Point) :
    Δ (mollifiedKernel width : Point → ℝ) place = mollifiedDensity width place := by
  classical
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (mollifiedKernel (Point := Point) width) (stdOrthonormalBasis ℝ Point)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_mollifiedKernel nonzero, mollifiedHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerBilinear_apply, smul_eq_mul]
  have direction : ∀ index : Fin (finrank ℝ Point),
      ⟪stdOrthonormalBasis ℝ Point index, stdOrthonormalBasis ℝ Point index⟫ = (1 : ℝ) := by
    intro index
    rw [real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ Point).orthonormal.1 index, one_pow]
  have size : ∑ index, ⟪place, stdOrthonormalBasis ℝ Point index⟫ *
      ⟪place, stdOrthonormalBasis ℝ Point index⟫ = ‖place‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      ← (stdOrthonormalBasis ℝ Point).sum_inner_mul_inner place place]
    exact Finset.sum_congr rfl fun index _ => by
      rw [real_inner_comm (stdOrthonormalBasis ℝ Point index) place]
  have power : (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2) * (‖place‖ ^ 2 + width ^ 2)
      = (‖place‖ ^ 2 + width ^ 2) ^ (-(3 : ℝ) / 2) := by
    nth_rewrite 2 [show (‖place‖ ^ 2 + width ^ 2)
      = (‖place‖ ^ 2 + width ^ 2) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add (mollifiedRadius_pos nonzero place)]
    norm_num
  have second : ∑ index, (4 * π)⁻¹ * (-3 * (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)) *
        ⟪place, stdOrthonormalBasis ℝ Point index⟫ *
        ⟪place, stdOrthonormalBasis ℝ Point index⟫
      = (4 * π)⁻¹ * (-3 * (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)) * ‖place‖ ^ 2 := by
    rw [← size, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [direction, mul_one]
  rw [Finset.sum_add_distrib, second, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    dimension, nsmul_eq_mul, mollifiedDensity]
  push_cast
  linear_combination (-3 * (4 * π)⁻¹) * power

omit [MeasurableSpace Point] [BorelSpace Point] in
/--
The Laplacian is invariant under the point reflection `spot ↦ center - spot`.

Convolution evaluates the source at `place - spot`, so Green's identity — which
differentiates in the integration variable — only applies after this has been
recognised.  The reason it holds is that the reflection is linear with
derivative `-id`, so the two sign changes in the second derivative cancel.
-/
theorem laplacian_comp_sub {field : Point → ℝ} (smooth : ContDiff ℝ smoothExponent field)
    (center place : Point) :
    Δ (fun spot => field (center - spot)) place = Δ field (center - place) := by
  have differentiableField : Differentiable ℝ field :=
    smooth.differentiable (by simp [smoothExponent])
  have differentiableGradient : Differentiable ℝ (fderiv ℝ field) :=
    (smooth.fderiv_right (m := smoothExponent) (by simp [smoothExponent])).differentiable
      (by simp [smoothExponent])
  have reflection : ∀ spot : Point,
      HasFDerivAt (fun other : Point => center - other) (-ContinuousLinearMap.id ℝ Point) spot :=
    fun spot => (hasFDerivAt_id spot).const_sub center
  have firstDerivative : ∀ spot : Point, HasFDerivAt (fun other => field (center - other))
      (-(fderiv ℝ field (center - spot))) spot := fun spot => by
    have chain := (differentiableField (center - spot)).hasFDerivAt.comp spot (reflection spot)
    rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] at chain
    exact chain
  have gradientEq : fderiv ℝ (fun other => field (center - other))
      = fun spot => -(fderiv ℝ field (center - spot)) :=
    funext fun spot => (firstDerivative spot).fderiv
  have secondDerivative : ∀ spot : Point,
      HasFDerivAt (fun other : Point => -(fderiv ℝ field (center - other)))
        (fderiv ℝ (fderiv ℝ field) (center - spot)) spot := fun spot => by
    have chain := (differentiableGradient (center - spot)).hasFDerivAt.comp spot (reflection spot)
    rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] at chain
    have negated := chain.neg
    rw [neg_neg] at negated
    exact negated
  have hessianEq : fderiv ℝ (fderiv ℝ (fun other => field (center - other))) place
      = fderiv ℝ (fderiv ℝ field) (center - place) := by
    rw [gradientEq]
    exact (secondDerivative place).fderiv
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun other => field (center - other)) (stdOrthonormalBasis ℝ Point),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis field
      (stdOrthonormalBasis ℝ Point)]
  simp only [iteratedFDeriv_two_apply, hessianEq]

/--
**The mollified kernel inverts the Laplacian exactly, at every scale.**

`E_w ⋆ Δφ = (Δ E_w) ⋆ φ`: Green's identity applied inside the convolution
integral, with the compactly supported reflected source as the test function.
No limit has been taken yet; this is an exact identity for every `w ≠ 0`, and
it is where the smoothness of the mollified kernel is spent.
-/
theorem convolution_mollifiedKernel (dimension : finrank ℝ Point = 3) {width : ℝ}
    (nonzero : width ≠ 0) {source : Point → ℝ} (smooth : ContDiff ℝ smoothExponent source)
    (compact : HasCompactSupport source) (place : Point) :
    (mollifiedKernel width ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Δ source)) place
      = (mollifiedDensity width ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) place := by
  have reflectedSmooth : ContDiff ℝ smoothExponent (fun spot : Point => source (place - spot)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have reflectedCompact : HasCompactSupport (fun spot : Point => source (place - spot)) :=
    compact.comp_homeomorph (Homeomorph.subLeft place)
  rw [convolution_def, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have reflectLaplacian : ∀ spot : Point,
      mollifiedKernel width spot * Δ source (place - spot)
        = mollifiedKernel width spot * Δ (fun other : Point => source (place - other)) spot :=
    fun spot => by rw [laplacian_comp_sub smooth place spot]
  simp_rw [reflectLaplacian]
  rw [integral_mul_laplacian (contDiff_mollifiedKernel nonzero) reflectedSmooth reflectedCompact]
  refine integral_congr_ae (.of_forall fun spot => ?_)
  show Δ (mollifiedKernel width : Point → ℝ) spot * source (place - spot) = _
  rw [laplacian_mollifiedKernel dimension nonzero]

/-!
## The mass of the bump

`Δ E_w` integrates to exactly one, and this is where the constant `4 π` in the
kernel pays for itself: the surface measure of the unit sphere computed above
is precisely the factor that the polar-coordinate integration produces, and it
cancels against the `(4 π)⁻¹` carried by the kernel.

The radial integral is elementary — the integrand `w² r² (r² + w²)^{-5/2}` has
the closed-form primitive `r³ (r² + w²)^{-3/2} / 3` — so no special function
and no comparison estimate is needed, only the fundamental theorem of calculus
on `(0, ∞)`.
-/

/-- The one-dimensional primitive of the radial profile of `Δ E_w`. -/
noncomputable def massPrimitive (width radius : ℝ) : ℝ :=
  radius ^ 3 * (radius ^ 2 + width ^ 2) ^ (-(3 : ℝ) / 2) / 3

theorem radiusSquare_pos {width : ℝ} (nonzero : width ≠ 0) (radius : ℝ) :
    0 < radius ^ 2 + width ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

theorem continuous_massPrimitive {width : ℝ} (nonzero : width ≠ 0) :
    Continuous (massPrimitive width) :=
  (((continuous_pow 3).mul
    (((continuous_pow 2).add continuous_const).rpow_const fun radius =>
      Or.inl (radiusSquare_pos nonzero radius).ne')).div_const 3)

/-- The primitive differentiates to the radial profile of `Δ E_w`, times the
polar Jacobian `r²`. -/
theorem hasDerivAt_massPrimitive {width : ℝ} (nonzero : width ≠ 0) (radius : ℝ) :
    HasDerivAt (massPrimitive width)
      (width ^ 2 * radius ^ 2 * (radius ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)) radius := by
  have square : HasDerivAt (fun other : ℝ => other ^ 2 + width ^ 2) (2 * radius) radius := by
    simpa using ((hasDerivAt_pow 2 radius).add_const (width ^ 2))
  have power := square.rpow_const (p := -(3 : ℝ) / 2)
    (Or.inl (radiusSquare_pos nonzero radius).ne')
  have product := ((hasDerivAt_pow 3 radius).mul power).div_const 3
  refine product.congr_deriv ?_
  have shift : (-(3 : ℝ) / 2 - 1) = -(5 : ℝ) / 2 := by norm_num
  rw [shift]
  have descend : (radius ^ 2 + width ^ 2) ^ (-(3 : ℝ) / 2)
      = (radius ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2) * (radius ^ 2 + width ^ 2) := by
    nth_rewrite 3 [show (radius ^ 2 + width ^ 2)
      = (radius ^ 2 + width ^ 2) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add (radiusSquare_pos nonzero radius)]
    norm_num
  push_cast
  rw [descend]
  ring

/-- The primitive tends to `1/3` at infinity: the profile has finite mass. -/
theorem tendsto_massPrimitive {width : ℝ} (nonzero : width ≠ 0) :
    Filter.Tendsto (massPrimitive width) Filter.atTop (nhds (1 / 3)) := by
  have ratio : Filter.Tendsto (fun radius : ℝ => 1 + width ^ 2 / radius ^ 2)
      Filter.atTop (nhds 1) := by
    have decay : Filter.Tendsto (fun radius : ℝ => width ^ 2 / radius ^ 2)
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_pow_atTop two_ne_zero)
    simpa using tendsto_const_nhds.add decay
  have continuity : ContinuousAt (fun scalar : ℝ => scalar ^ (-(3 : ℝ) / 2)) 1 :=
    continuousAt_id.rpow_const (Or.inl one_ne_zero)
  have limit : Filter.Tendsto
      (fun radius : ℝ => 1 / 3 * (1 + width ^ 2 / radius ^ 2) ^ (-(3 : ℝ) / 2))
      Filter.atTop (nhds (1 / 3)) := by
    simpa using ((continuity.tendsto.comp ratio).const_mul (1 / 3 : ℝ))
  refine limit.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with radius positive
  have cube : (radius ^ 2 : ℝ) ^ (-(3 : ℝ) / 2) = (radius ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast radius 2, ← Real.rpow_mul positive.le,
      show ((2 : ℕ) : ℝ) * (-(3 : ℝ) / 2) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg positive.le, Real.rpow_natCast]
  have factor : radius ^ 2 + width ^ 2 = radius ^ 2 * (1 + width ^ 2 / radius ^ 2) := by
    field_simp
  rw [massPrimitive, factor, Real.mul_rpow (by positivity) (by positivity), cube]
  field_simp

/-- The radial profile is integrable on the ray. -/
theorem integrableOn_massProfile {width : ℝ} (nonzero : width ≠ 0) :
    IntegrableOn (fun radius : ℝ =>
      width ^ 2 * radius ^ 2 * (radius ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)) (Ioi 0) volume :=
  integrableOn_Ioi_deriv_of_nonneg (continuous_massPrimitive nonzero).continuousWithinAt
    (fun radius _ => hasDerivAt_massPrimitive nonzero radius)
    (fun radius _ => by positivity) (tendsto_massPrimitive nonzero)

/-- **The radial mass integral.**  `∫₀^∞ w² r² (r² + w²)^{-5/2} dr = 1/3`. -/
theorem integral_massProfile {width : ℝ} (nonzero : width ≠ 0) :
    (∫ radius in Ioi (0 : ℝ),
        width ^ 2 * radius ^ 2 * (radius ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)) = 1 / 3 := by
  have evaluate := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuous_massPrimitive nonzero).continuousWithinAt
    (fun radius _ => hasDerivAt_massPrimitive nonzero radius)
    (integrableOn_massProfile nonzero) (tendsto_massPrimitive nonzero)
  rw [evaluate, massPrimitive]
  norm_num

/-- The radial profile of `Δ E_w`, as a function of the radius alone.  Polar
coordinates only see this. -/
noncomputable def mollifiedProfile (width radius : ℝ) : ℝ :=
  3 * width ^ 2 * (4 * π)⁻¹ * (radius ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
@[simp] theorem mollifiedDensity_eq_profile (width : ℝ) (place : Point) :
    mollifiedDensity width place = mollifiedProfile width ‖place‖ := rfl

/-- The bump is integrable: in polar coordinates it is the radial profile
against the `r²` Jacobian, which is the derivative of a bounded monotone
primitive. -/
theorem integrable_mollifiedDensity (dimension : finrank ℝ Point = 3) {width : ℝ}
    (nonzero : width ≠ 0) :
    Integrable (mollifiedDensity width : Point → ℝ) volume := by
  haveI : Nontrivial Point :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [dimension]; norm_num)
  refine (integrable_fun_norm_addHaar (volume : Measure Point)
    (f := mollifiedProfile width)).2 ?_
  rw [dimension]
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).2
    ((integrableOn_massProfile nonzero).const_mul (3 * (4 * π)⁻¹))
  intro radius _
  simp only [smul_eq_mul, mollifiedProfile]
  norm_num
  ring

/--
**The bump has total mass one.**

This is the computation that fixes the constant in the kernel: polar
coordinates produce the factor `3 · vol(ball) = 4 π`, the radial integral
produces `1/3`, and the `(4 π)⁻¹` carried by the kernel makes the product
exactly one.
-/
theorem integral_mollifiedDensity (dimension : finrank ℝ Point = 3) {width : ℝ}
    (nonzero : width ≠ 0) :
    (∫ place : Point, mollifiedDensity width place) = 1 := by
  haveI : Nontrivial Point :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [dimension]; norm_num)
  have ballVolume : (volume : Measure Point).real (ball 0 1) = 4 * π / 3 := by
    unfold Measure.real
    rw [volume_unit_ball dimension, ENNReal.toReal_ofReal (by positivity)]
  have radial : (∫ radius in Ioi (0 : ℝ),
      radius ^ (3 - 1) • mollifiedProfile width radius) = (4 * π)⁻¹ := by
    have shape : ∀ radius : ℝ, radius ^ (3 - 1) • mollifiedProfile width radius
        = 3 * (4 * π)⁻¹ *
          (width ^ 2 * radius ^ 2 * (radius ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2)) := by
      intro radius
      simp only [smul_eq_mul, mollifiedProfile]
      norm_num
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi fun radius _ => shape radius,
      integral_const_mul, integral_massProfile nonzero]
    ring
  simp only [mollifiedDensity_eq_profile]
  rw [integral_fun_norm_addHaar (volume : Measure Point) (mollifiedProfile width), dimension,
    ballVolume, radial, smul_eq_mul, nsmul_eq_mul]
  have piPositive := Real.pi_pos
  field_simp
  norm_num

/-!
## Passing to the limit

Two limits remain, and they are taken along the same sequence of widths, so
the exact identity `E_w ⋆ Δφ = (Δ E_w) ⋆ φ` forces the two limits to agree:

* the left-hand side converges to `E ⋆ Δφ`, by dominated convergence with the
  dominating function `|E| |Δφ(place - ·)|` — the mollified kernel is
  *smaller* than the true one everywhere, so the singular kernel is its own
  domination;
* the right-hand side converges to `φ`, because rescaling the integration
  variable by the width turns `(Δ E_w) ⋆ φ` into an integral against the fixed
  integrable profile `Δ E_1`, whose mass is one.
-/

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- The Laplacian of a smooth field is smooth. -/
theorem contDiff_laplacian {source : Point → ℝ} (smooth : ContDiff ℝ smoothExponent source) :
    ContDiff ℝ smoothExponent (Δ source : Point → ℝ) := by
  have shape : (Δ source : Point → ℝ) = fun place => ∑ index : Fin (finrank ℝ Point),
      derivAlong (derivAlong source (stdOrthonormalBasis ℝ Point index))
        (stdOrthonormalBasis ℝ Point index) place :=
    funext fun place => laplacian_eq_sum_derivAlong smooth place
  rw [shape]
  exact ContDiff.sum fun index _ =>
    contDiff_derivAlong (contDiff_derivAlong smooth _) _

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- The Laplacian is a local operator, so it does not enlarge the support. -/
theorem hasCompactSupport_laplacian {source : Point → ℝ}
    (compact : HasCompactSupport source) : HasCompactSupport (Δ source : Point → ℝ) := by
  refine HasCompactSupport.intro compact fun place outside => ?_
  have vanish : source =ᶠ[nhds place] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport source).isOpen_compl.mem_nhds outside] with spot away
    exact Function.notMem_support.1 fun member => away (subset_tsupport source member)
  rw [(InnerProductSpace.laplacian_congr_nhds vanish).self_of_nhds]
  simp

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
/-- The Newtonian kernel is the same negative half-power of `‖x‖²` that the
mollified kernel is a perturbation of.  Writing it this way is what lets the
two be compared. -/
theorem newtonianKernel_eq_rpow_sq (place : Point) :
    newtonianKernel place = -(4 * π)⁻¹ * (‖place‖ ^ 2) ^ (-(1 : ℝ) / 2) := by
  have exponent : ((‖place‖ ^ 2 : ℝ)) ^ (-(1 : ℝ) / 2) = ‖place‖ ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast ‖place‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [newtonianKernel_eq_rpow, exponent]

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
/-- **The mollified kernel is dominated by the true one.**  Rounding off the
singularity can only decrease the size of the kernel, which is what makes the
dominated convergence theorem applicable with the singular kernel itself as
the dominating function. -/
theorem abs_mollifiedKernel_le {width : ℝ} {place : Point} (nonzero : place ≠ 0) :
    |mollifiedKernel width place| ≤ |newtonianKernel place| := by
  have normPositive : 0 < ‖place‖ ^ 2 := by
    have := norm_pos_iff.mpr nonzero
    positivity
  have compare : (‖place‖ ^ 2 + width ^ 2) ^ (-(1 : ℝ) / 2)
      ≤ (‖place‖ ^ 2) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos normPositive (by nlinarith [sq_nonneg width]) (by norm_num)
  have nonnegative : ∀ radius : ℝ, 0 ≤ radius → (0 : ℝ) ≤ radius ^ (-(1 : ℝ) / 2) :=
    fun radius hradius => Real.rpow_nonneg hradius _
  rw [newtonianKernel_eq_rpow_sq, mollifiedKernel, abs_mul, abs_mul,
    abs_of_nonneg (nonnegative _ (by positivity)),
    abs_of_nonneg (nonnegative _ normPositive.le)]
  have positive : (0 : ℝ) ≤ |-(4 * π)⁻¹| := abs_nonneg _
  exact mul_le_mul_of_nonneg_left compare positive

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The mollified kernel is continuous, hence measurable, at every width. -/
theorem continuous_mollifiedKernel {width : ℝ} (nonzero : width ≠ 0) :
    Continuous (mollifiedKernel (Point := Point) width) :=
  (contDiff_mollifiedKernel nonzero).continuous

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The bump is continuous, hence measurable. -/
theorem continuous_mollifiedDensity {width : ℝ} (nonzero : width ≠ 0) :
    Continuous (mollifiedDensity (Point := Point) width) :=
  continuous_const.mul
    (((contDiff_norm_sq ℝ (n := smoothExponent)).continuous.add continuous_const).rpow_const
      fun place => Or.inl (mollifiedRadius_pos nonzero place).ne')

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
/-- The bump is nonnegative. -/
theorem mollifiedDensity_nonneg {width : ℝ} (place : Point) :
    0 ≤ mollifiedDensity width place := by
  have : (0 : ℝ) ≤ (‖place‖ ^ 2 + width ^ 2) ^ (-(5 : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have piPositive := Real.pi_pos
  unfold mollifiedDensity
  positivity

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The bump at width `w` is the width-one bump rescaled: `Δ E_w` is
`w⁻ⁿ (Δ E_1)(·/w)`.  This is the homogeneity that makes the family an
approximate identity. -/
theorem mollifiedDensity_smul {width : ℝ} (positive : 0 < width) (place : Point) :
    mollifiedDensity width (width • place) = (width ^ 3)⁻¹ * mollifiedDensity 1 place := by
  have normEq : ‖width • place‖ ^ 2 = width ^ 2 * ‖place‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have factor : ‖width • place‖ ^ 2 + width ^ 2 = width ^ 2 * (‖place‖ ^ 2 + 1 ^ 2) := by
    rw [normEq]; ring
  have splitting : (width ^ 2 * (‖place‖ ^ 2 + 1 ^ 2)) ^ (-(5 : ℝ) / 2)
      = (width ^ 2) ^ (-(5 : ℝ) / 2) * (‖place‖ ^ 2 + 1 ^ 2) ^ (-(5 : ℝ) / 2) :=
    Real.mul_rpow (by positivity) (by positivity)
  have widthPower : ((width ^ 2 : ℝ)) ^ (-(5 : ℝ) / 2) = (width ^ 5)⁻¹ := by
    rw [← Real.rpow_natCast width 2, ← Real.rpow_mul positive.le,
      show ((2 : ℕ) : ℝ) * (-(5 : ℝ) / 2) = -((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg positive.le, Real.rpow_natCast]
  unfold mollifiedDensity
  rw [factor, splitting, widthPower]
  have nonzero : width ≠ 0 := positive.ne'
  field_simp

/--
**The rescaling identity.**

`(Δ E_w) ⋆ φ` evaluated at `x` is an integral of `φ(x - w s)` against the
*fixed* profile `Δ E_1`.  All the `w`-dependence has been moved out of the
weight and into the argument of `φ`, which is what makes the limit `w → 0` a
single application of dominated convergence with a `w`-independent dominating
function.
-/
theorem convolution_mollifiedDensity_scaled (dimension : finrank ℝ Point = 3) {width : ℝ}
    (positive : 0 < width) (source : Point → ℝ) (place : Point) :
    (mollifiedDensity width ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) place
      = ∫ spot : Point, mollifiedDensity 1 spot * source (place - width • spot) := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have scaling := Measure.integral_comp_smul (volume : Measure Point)
    (fun spot : Point => mollifiedDensity width spot * source (place - spot)) width
  rw [dimension] at scaling
  have rewritten : (∫ spot : Point,
        mollifiedDensity width (width • spot) * source (place - width • spot))
      = (width ^ 3)⁻¹ *
        ∫ spot : Point, mollifiedDensity 1 spot * source (place - width • spot) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun spot => ?_)
    show mollifiedDensity width (width • spot) * source (place - width • spot) = _
    rw [mollifiedDensity_smul positive]
    ring
  rw [rewritten, abs_of_pos (by positivity), smul_eq_mul] at scaling
  exact (mul_left_cancel₀ (a := ((width ^ 3)⁻¹ : ℝ)) (by positivity) scaling).symm

/--
**The bumps form an approximate identity.**

`(Δ E_{1/(n+1)}) ⋆ φ → φ` pointwise.  After the rescaling above this is
dominated convergence against `‖φ‖_∞ Δ E_1`, and the limit is `φ(x)` because
the profile has mass one.
-/
theorem tendsto_convolution_mollifiedDensity (dimension : finrank ℝ Point = 3)
    {source : Point → ℝ} (continuousSource : Continuous source)
    (compact : HasCompactSupport source) (place : Point) :
    Filter.Tendsto (fun index : ℕ =>
        (mollifiedDensity (1 / ((index : ℝ) + 1)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source)
          place)
      Filter.atTop (nhds (source place)) := by
  obtain ⟨bound, boundLe⟩ := compact.exists_bound_of_continuous continuousSource
  have widthPositive : ∀ index : ℕ, (0 : ℝ) < 1 / ((index : ℝ) + 1) := fun index => by positivity
  have widthLimit : Filter.Tendsto (fun index : ℕ => 1 / ((index : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine Filter.Tendsto.congr (fun index =>
    (convolution_mollifiedDensity_scaled dimension (widthPositive index) source place).symm) ?_
  have limitValue : (∫ spot : Point, mollifiedDensity 1 spot * source place) = source place := by
    rw [integral_mul_const, integral_mollifiedDensity dimension one_ne_zero, one_mul]
  rw [← limitValue]
  refine tendsto_integral_of_dominated_convergence
    (fun spot : Point => mollifiedDensity 1 spot * bound) (fun index => ?_)
    ((integrable_mollifiedDensity dimension one_ne_zero).mul_const bound)
    (fun index => .of_forall fun spot => ?_) (.of_forall fun spot => ?_)
  · exact ((continuous_mollifiedDensity one_ne_zero).mul (continuousSource.comp
      (continuous_const.sub (continuous_const_smul _)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifiedDensity_nonneg spot)]
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _)
      (by simpa using boundLe (place - (1 / ((index : ℝ) + 1)) • spot)))
      (mollifiedDensity_nonneg spot)
  · refine Filter.Tendsto.const_mul _ (continuousSource.continuousAt.tendsto.comp ?_)
    have shift : Filter.Tendsto (fun index : ℕ => place - (1 / ((index : ℝ) + 1)) • spot)
        Filter.atTop (nhds (place - (0 : ℝ) • spot)) :=
      tendsto_const_nhds.sub (widthLimit.smul_const spot)
    simpa using shift

omit [InnerProductSpace ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point] in
/-- Away from the origin the mollified kernels converge to the Newtonian
kernel as the rounding scale goes to zero. -/
theorem tendsto_mollifiedKernel {place : Point} (nonzero : place ≠ 0) :
    Filter.Tendsto (fun index : ℕ => mollifiedKernel (1 / ((index : ℝ) + 1)) place)
      Filter.atTop (nhds (newtonianKernel place)) := by
  have normPositive : (0 : ℝ) < ‖place‖ ^ 2 := by
    have := norm_pos_iff.mpr nonzero
    positivity
  have radius : Filter.Tendsto
      (fun index : ℕ => ‖place‖ ^ 2 + (1 / ((index : ℝ) + 1)) ^ 2)
      Filter.atTop (nhds (‖place‖ ^ 2)) := by
    have decay := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simpa using tendsto_const_nhds.add decay
  have power := (Real.continuousAt_rpow_const (‖place‖ ^ 2) (-(1 : ℝ) / 2)
    (Or.inl normPositive.ne')).tendsto.comp radius
  have scaled := power.const_mul (-(4 * π)⁻¹)
  rw [← newtonianKernel_eq_rpow_sq place] at scaled
  exact scaled

/--
**The singular kernel is the limit of the mollified ones, inside the
convolution.**

Dominated convergence, with the *singular* kernel providing its own
dominating function: `|E_w| ≤ |E|` pointwise away from the origin, and
`|E| |Δφ(x - ·)|` is integrable precisely because `E` is locally integrable
and `Δφ` has compact support.
-/
theorem tendsto_convolution_mollifiedKernel (dimension : finrank ℝ Point = 3)
    {source : Point → ℝ} (smooth : ContDiff ℝ smoothExponent source)
    (compact : HasCompactSupport source) (place : Point) :
    Filter.Tendsto (fun index : ℕ =>
        (mollifiedKernel (1 / ((index : ℝ) + 1)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Δ source)) place)
      Filter.atTop (nhds ((newtonianKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (Δ source)) place)) := by
  haveI : Nontrivial Point :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [dimension]; norm_num)
  have continuousLaplacian : Continuous (Δ source : Point → ℝ) :=
    (contDiff_laplacian smooth).continuous
  have compactLaplacian : HasCompactSupport (Δ source : Point → ℝ) :=
    hasCompactSupport_laplacian compact
  have widthPositive : ∀ index : ℕ, (0 : ℝ) < 1 / ((index : ℝ) + 1) := fun index => by positivity
  have limitIntegrable : Integrable
      (fun spot : Point => newtonianKernel spot * Δ source (place - spot)) volume :=
    compactLaplacian.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (newtonianKernel_locallyIntegrable dimension) continuousLaplacian place
  have almostAll : ∀ᵐ spot : Point ∂(volume : Measure Point), spot ≠ 0 := by
    rw [ae_iff]
    simp
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine tendsto_integral_of_dominated_convergence
    (fun spot : Point => ‖newtonianKernel spot * Δ source (place - spot)‖)
    (fun index => ?_) limitIntegrable.norm (fun index => ?_) ?_
  · exact ((continuous_mollifiedKernel (widthPositive index).ne').mul
      (continuousLaplacian.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards [almostAll] with spot away
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_mollifiedKernel_le away) (abs_nonneg _)
  · filter_upwards [almostAll] with spot away
    exact (tendsto_mollifiedKernel away).mul_const _

/--
**The Newtonian kernel inverts the Laplacian.**

This is the inhomogeneous half of the fundamental-solution property, and the
last thing this file needed.  The proof is the classical one with the
excision replaced by a mollification: for every rounding scale `w` one has the
*exact* identity `E_w ⋆ Δφ = (Δ E_w) ⋆ φ`, and letting `w → 0` along
`1/(n+1)` the left side converges to `E ⋆ Δφ` while the right side converges
to `φ`, because `Δ E_w` is an approximate identity of mass one.
-/
theorem newtonianKernel_inverts (dimension : finrank ℝ Point = 3) {source : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent source) (compact : HasCompactSupport source) :
    (newtonianKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Δ source)) = source := by
  funext place
  have widthPositive : ∀ index : ℕ, (0 : ℝ) < 1 / ((index : ℝ) + 1) := fun index => by positivity
  have left := tendsto_convolution_mollifiedKernel dimension smooth compact place
  have right := tendsto_convolution_mollifiedDensity dimension smooth.continuous compact place
  exact tendsto_nhds_unique (Filter.Tendsto.congr (fun index =>
    convolution_mollifiedKernel dimension (widthPositive index).ne' smooth compact place) left)
    right

/--
**The Newtonian fundamental solution of the Laplacian in dimension three.**

Everything the graded interface asks of a fundamental solution is now
available: the kernel is locally integrable (from the radial-power estimate)
and its convolution inverts the Laplacian on compactly supported smooth data
(from the mollification argument above).  Registering it here is what gives
every model naming the Laplacian a solution operator with nothing further to
supply.
-/
noncomputable def newtonianFundamentalSolution (dimension : finrank ℝ Point = 3) :
    FundamentalSolution (Point := Point) (fun field => Δ field) where
  kernel := newtonianKernel
  locallyIntegrable := newtonianKernel_locallyIntegrable dimension
  inverts _ smooth compact := newtonianKernel_inverts dimension smooth compact

end Hypostructure.PDE.Solution
