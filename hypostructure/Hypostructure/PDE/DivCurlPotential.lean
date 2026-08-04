import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Hypostructure.PDE.Solution.QuotientRecoveryData

/-!
# The Poincaré lemma on a ball, and the lifting of the window's harmonic part

`PDE/DivCurl.lean` builds the orthogonal projection onto the harmonic kernel of a
window **without ever representing its elements**.  That is deliberate — the
projection needs only continuity of the two first-order operators — but it leaves
one statement out of reach of the framework, and
`PDE/Solution/QuotientRecoveryData.lean` records the gap by name: the hypothesis

> `lifts : restrict harmonicField = harmonicSlicePart field`

of `NormalizedRecovery.ofLifting`, "the discarded component of the splitting *is*
the projection on the window".  The classical argument for it is the Poincaré
lemma: on a ball a curl-free field is a gradient, so the projection — which is
curl-free and divergence-free by construction — is the gradient of a harmonic
potential, and a potential is something the state space can carry.

Mathlib has no Poincaré lemma for vector fields and no existence theorem for the
potential of a conservative field, so this module proves one.

## What is proved

* `hasFDerivAt_radialPotential` — **the Poincaré lemma on a ball, for one-forms.**
  If `form : Domain → Domain →L[ℝ] ℝ` is `C¹` and its derivative is symmetric at
  every point of `ball center radius`, then the radial homotopy potential

  > `radialPotential center form place = ∫ t in 0..1, form (center + t • (place - center)) (place - center)`

  has `form place` as its Fréchet derivative at every `place` of the ball.  The
  domain is an arbitrary real normed space, asked only to be proper — properness
  is used exactly once, to bound the integrand and its derivative on a compact
  ball slightly smaller than the window, which is what differentiation under the
  integral sign consumes.  The symmetry of the derivative is consumed exactly
  once as well, in `integral_radialIntegrandDeriv_apply`, where it turns the
  differentiated integrand into an exact `t`-derivative and the fundamental
  theorem of calculus applies.

* `exists_potential_of_curl_eq_zero` — **the same statement in the coordinates of
  `PDE/DivCurl.lean`.**  A smooth `VectorField` whose `curl` vanishes on a ball is
  `gradient weight` there, and `scalarLaplacian weight` is `divergence field`
  there.  So a field that is curl-free *and* divergence-free on the ball — a
  member of the ball's harmonic kernel — is the gradient of a **harmonic**
  potential.  The bridge from `curl field place = 0` to the symmetry hypothesis
  of the abstract statement is `symm_fderiv_coordinateOneForm`: the three cyclic
  components of the curl are the three off-diagonal symmetries of the matrix
  `∂ᵢ Fⱼ`, and bilinearity does the rest.

## Where the lifting is proved

`lifts` is not a statement about `LocalNormalization` in the abstract.  A
localization the framework produces comes from a *window*: `restrict` is
restriction to that window, and the two slice operators are the coordinate
operators read there.  `BallWindow` is exactly that — a `LocalNormalization`
together with the readings that exhibit it as the localization to a ball — and
against it the three facts a bare interface would have to assume are **theorems**:

| statement | proved by |
| --- | --- |
| a member of the harmonic kernel is curl-free on the window | `BallWindow.curl_represent_eq_zero`, from `sliceCurl_represent` |
| a member of the harmonic kernel is divergence-free on the window | `BallWindow.divergence_represent_eq_zero`, from `sliceDivergence_represent` |
| a slice element which is a gradient on the window is the restriction of the gradient of a state | `BallWindow.restrict_gradient_eq`, from `represent_restrict`, `represent_injective` and `exists_potentialState` |

so that `BallWindow.exists_potential_restrict_eq_harmonicSlicePart` is `lifts`
with the harmonic component **constructed** rather than supplied, and
`BallWindow.normalizedRecovery` runs `NormalizedRecovery.ofLifting` on it: the
caller supplies subtractivity of the restriction and the vanishing of the
source's projection, and neither a gauge condition nor a lifting.

## The one analytic input that is not proved here

`BallWindow.harmonicKernel_smooth`: a slice element annihilated by both window
operators is a *smooth* field on the window.  This is interior regularity for the
pair `(div, curl)`, and it is genuinely needed rather than an artefact of the
packaging: `harmonicSlicePart` is an orthogonal projection, so the window's slice
has to be complete, and a complete slice contains elements that are not smooth —
it is exactly membership of the harmonic kernel that upgrades them.  It is
confined to that kernel, it is the only field of `BallWindow` that is not a
reading or a locality statement, and a localization that cannot supply it is not
a window localization and is to be rejected as an input rather than accommodated
by weakening `lifts`.
-/

namespace Hypostructure.PDE.DivCurl

open MeasureTheory Metric Set

open scoped Interval

section RadialPotential

variable {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]

/-- The radial homotopy potential of a one-form about a centre. -/
noncomputable def radialPotential (center : Domain) (form : Domain → Domain →L[ℝ] ℝ) :
    Domain → ℝ :=
  fun place => ∫ time in (0:ℝ)..1, form (center + time • (place - center)) (place - center)

/-- The derivative in the base point of the integrand of `radialPotential`. -/
noncomputable def radialIntegrandDeriv (center : Domain) (form : Domain → Domain →L[ℝ] ℝ)
    (place : Domain) (time : ℝ) : Domain →L[ℝ] ℝ :=
  form (center + time • (place - center)) +
    time • ((ContinuousLinearMap.apply ℝ ℝ (place - center)).comp
      (fderiv ℝ form (center + time • (place - center))))

variable (center : Domain) (form : Domain → Domain →L[ℝ] ℝ)

@[simp] theorem radialIntegrandDeriv_apply (place : Domain) (time : ℝ) (direction : Domain) :
    radialIntegrandDeriv center form place time direction =
      form (center + time • (place - center)) direction
        + time * fderiv ℝ form (center + time • (place - center)) direction
            (place - center) := by
  simp [radialIntegrandDeriv]

theorem hasFDerivAt_radialIntegrand (diff : Differentiable ℝ form) (place : Domain) (time : ℝ) :
    HasFDerivAt (fun point => form (center + time • (point - center)) (point - center))
      (radialIntegrandDeriv center form place time) place := by
  have inner : HasFDerivAt (fun point : Domain => center + time • (point - center))
      (time • ContinuousLinearMap.id ℝ Domain) place := by
    have base : HasFDerivAt (fun point : Domain => point - center)
        (ContinuousLinearMap.id ℝ Domain) place := (hasFDerivAt_id place).sub_const center
    simpa using (base.const_smul time).const_add center
  have outer : HasFDerivAt form (fderiv ℝ form (center + time • (place - center)))
      (center + time • (place - center)) := (diff _).hasFDerivAt
  have composite : HasFDerivAt (fun point => form (center + time • (point - center)))
      ((fderiv ℝ form (center + time • (place - center))).comp
        (time • ContinuousLinearMap.id ℝ Domain)) place := outer.comp place inner
  have argument : HasFDerivAt (fun point : Domain => point - center)
      (ContinuousLinearMap.id ℝ Domain) place := (hasFDerivAt_id place).sub_const center
  have shape : radialIntegrandDeriv center form place time =
      (form (center + time • (place - center))).comp (ContinuousLinearMap.id ℝ Domain) +
        (((fderiv ℝ form (center + time • (place - center))).comp
          (time • ContinuousLinearMap.id ℝ Domain)).flip (place - center)) := by
    ext direction
    simp [radialIntegrandDeriv]
  rw [shape]
  exact composite.clm_apply argument

/-- The ray from the centre to a point of a ball stays in the ball. -/
theorem mem_ball_of_mem_segment {radius : ℝ} {place : Domain} (mem : place ∈ ball center radius)
    {time : ℝ} (lower : 0 ≤ time) (upper : time ≤ 1) :
    center + time • (place - center) ∈ ball center radius := by
  have distance : ‖place - center‖ < radius := by
    simpa [dist_eq_norm] using mem
  have scaled : ‖time • (place - center)‖ ≤ ‖place - center‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg lower]
    calc time * ‖place - center‖ ≤ 1 * ‖place - center‖ :=
          mul_le_mul_of_nonneg_right upper (norm_nonneg _)
      _ = ‖place - center‖ := one_mul _
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_left]
  exact lt_of_le_of_lt scaled distance

/-- Continuity along the ray of the one-form evaluated at a fixed direction. -/
theorem continuous_form_along_ray (diff : Differentiable ℝ form) (place direction : Domain) :
    Continuous fun time : ℝ => form (center + time • (place - center)) direction := by
  have curve : Continuous fun time : ℝ => center + time • (place - center) := by fun_prop
  exact (diff.continuous.comp curve).clm_apply continuous_const

/-- Continuity along the ray of the derivative of the one-form, at two fixed directions. -/
theorem continuous_fderiv_along_ray (smooth : ContDiff ℝ 1 form)
    (place first second : Domain) :
    Continuous fun time : ℝ =>
      fderiv ℝ form (center + time • (place - center)) first second := by
  have contDeriv := smooth.continuous_fderiv (n := 1) (by simp)
  have curve : Continuous fun time : ℝ => center + time • (place - center) := by fun_prop
  exact (((contDeriv.comp curve).clm_apply continuous_const).clm_apply continuous_const)

/--
**The fundamental theorem of calculus along the ray.**

For a one-form whose derivative is symmetric on the ball, the integral along the
ray of the base-point derivative of the integrand is the one-form itself.  The
integrand is, after the symmetry has been used, exactly the `t`-derivative of
`t ↦ t · form (center + t · (place - center)) direction`.
-/
theorem integral_radialIntegrandDeriv_apply (smooth : ContDiff ℝ 1 form) {radius : ℝ}
    (symmetric : ∀ point ∈ ball center radius, ∀ first second : Domain,
      fderiv ℝ form point first second = fderiv ℝ form point second first)
    {place : Domain} (mem : place ∈ ball center radius) (direction : Domain) :
    (∫ time in (0:ℝ)..1, radialIntegrandDeriv center form place time direction)
      = form place direction := by
  have diff : Differentiable ℝ form := smooth.differentiable (by simp)
  set ray : ℝ → Domain := fun time => center + time • (place - center) with rayDef
  set primitive : ℝ → ℝ := fun time => time * form (ray time) direction with primitiveDef
  set derivative : ℝ → ℝ := fun time =>
    form (ray time) direction
      + time * fderiv ℝ form (ray time) (place - center) direction with derivativeDef
  have hasDeriv : ∀ time : ℝ, HasDerivAt primitive (derivative time) time := by
    intro time
    have rayDeriv : HasDerivAt ray (place - center) time := by
      simpa [rayDef] using ((hasDerivAt_id time).smul_const (place - center)).const_add center
    have formDeriv : HasDerivAt (fun other : ℝ => form (ray other) direction)
        (fderiv ℝ form (ray time) (place - center) direction) time := by
      have composed : HasDerivAt (fun other : ℝ => form (ray other))
          (fderiv ℝ form (ray time) (place - center)) time :=
        ((diff (ray time)).hasFDerivAt).comp_hasDerivAt time rayDeriv
      exact (ContinuousLinearMap.apply ℝ ℝ direction).hasFDerivAt.comp_hasDerivAt time composed
    have product : HasDerivAt primitive
        (1 * form (ray time) direction
          + time * fderiv ℝ form (ray time) (place - center) direction) time :=
      (hasDerivAt_id time).mul formDeriv
    rw [one_mul] at product
    exact product
  have derivativeContinuous : Continuous derivative :=
    (continuous_form_along_ray center form diff place direction).add
      (continuous_id.mul (continuous_fderiv_along_ray center form smooth place
        (place - center) direction))
  have congruence : EqOn (fun time => radialIntegrandDeriv center form place time direction)
      derivative (uIcc (0:ℝ) 1) := by
    intro time membership
    rw [uIcc_of_le (zero_le_one' ℝ)] at membership
    have inBall : ray time ∈ ball center radius :=
      mem_ball_of_mem_segment center mem membership.1 membership.2
    simp only [radialIntegrandDeriv_apply, derivativeDef]
    rw [symmetric (ray time) inBall direction (place - center)]
  rw [intervalIntegral.integral_congr congruence,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => hasDeriv time)
      (derivativeContinuous.intervalIntegrable 0 1)]
  simp [primitiveDef, rayDef]

/-- Continuity in the ray parameter of the base-point derivative of the integrand. -/
theorem continuous_radialIntegrandDeriv (smooth : ContDiff ℝ 1 form) (place : Domain) :
    Continuous fun time : ℝ => radialIntegrandDeriv center form place time := by
  have diff : Differentiable ℝ form := smooth.differentiable (by simp)
  have contDeriv := smooth.continuous_fderiv (n := 1) (by simp)
  have curve : Continuous fun time : ℝ => center + time • (place - center) := by fun_prop
  exact (diff.continuous.comp curve).add
    (continuous_id.smul (continuous_const.clm_comp (contDeriv.comp curve)))

/--
**The Poincaré lemma on a ball, for one-forms.**

A one-form which is `C¹` and whose derivative is symmetric on a ball is exact
there: the radial homotopy potential has it as its Fréchet derivative at every
point of the ball.

The two analytic inputs are differentiation under the integral sign — the ray
integrand is dominated uniformly on a slightly smaller ball, which is where
properness of the domain is used — and the fundamental theorem of calculus along
the ray, which is where the symmetry of the derivative is consumed.
-/
theorem hasFDerivAt_radialPotential [ProperSpace Domain]
    (smooth : ContDiff ℝ 1 form) {radius : ℝ}
    (symmetric : ∀ point ∈ ball center radius, ∀ first second : Domain,
      fderiv ℝ form point first second = fderiv ℝ form point second first)
    {place : Domain} (mem : place ∈ ball center radius) :
    HasFDerivAt (radialPotential center form) (form place) place := by
  have diff : Differentiable ℝ form := smooth.differentiable (by simp)
  have contDeriv := smooth.continuous_fderiv (n := 1) (by simp)
  have distance : ‖place - center‖ < radius := by
    simpa [dist_eq_norm] using mem
  set shrunk := (‖place - center‖ + radius) / 2 with shrunkDef
  have innerBound : ‖place - center‖ < shrunk := by rw [shrunkDef]; linarith
  have positive : 0 < shrunk := lt_of_le_of_lt (norm_nonneg _) innerBound
  obtain ⟨formBound, formBounded⟩ :=
    (isCompact_closedBall center shrunk).exists_bound_of_continuousOn
      diff.continuous.continuousOn
  obtain ⟨derivBound, derivBounded⟩ :=
    (isCompact_closedBall center shrunk).exists_bound_of_continuousOn contDeriv.continuousOn
  have centerMem : center ∈ closedBall center shrunk := mem_closedBall_self positive.le
  have formNonneg : 0 ≤ formBound := le_trans (norm_nonneg _) (formBounded center centerMem)
  have derivNonneg : 0 ≤ derivBound := le_trans (norm_nonneg _) (derivBounded center centerMem)
  -- the ray of any point of the shrunken ball stays in the compact ball carrying the bounds
  have rayMem : ∀ point ∈ ball center shrunk, ∀ time ∈ Ι (0:ℝ) 1,
      center + time • (point - center) ∈ closedBall center shrunk := by
    intro point pointMem time timeMem
    rw [uIoc_of_le (zero_le_one' ℝ)] at timeMem
    have pointDistance : ‖point - center‖ ≤ shrunk := le_of_lt (by
      simpa [dist_eq_norm] using pointMem)
    have scaled : ‖time • (point - center)‖ ≤ shrunk := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg timeMem.1.le]
      calc time * ‖point - center‖ ≤ 1 * ‖point - center‖ :=
            mul_le_mul_of_nonneg_right timeMem.2 (norm_nonneg _)
        _ ≤ shrunk := by rw [one_mul]; exact pointDistance
    simpa [dist_eq_norm] using scaled
  -- the uniform domination
  have domination : ∀ᵐ time ∂(volume.restrict (Ι (0:ℝ) 1)), ∀ point ∈ ball center shrunk,
      ‖radialIntegrandDeriv center form point time‖ ≤ formBound + derivBound * shrunk := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with time timeMem point pointMem
    have rayInside := rayMem point pointMem time timeMem
    have timeRange : time ∈ Ioc (0:ℝ) 1 := by rwa [uIoc_of_le (zero_le_one' ℝ)] at timeMem
    have pointDistance : ‖point - center‖ ≤ shrunk := le_of_lt (by
      simpa [dist_eq_norm] using pointMem)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun direction => ?_
    set ray := center + time • (point - center) with rayDef
    have formStep : |form ray direction| ≤ formBound * ‖direction‖ :=
      le_trans ((form ray).le_opNorm direction)
        (mul_le_mul_of_nonneg_right (formBounded ray rayInside) (norm_nonneg _))
    have derivStep : |time * fderiv ℝ form ray direction (point - center)|
        ≤ derivBound * shrunk * ‖direction‖ := by
      rw [abs_mul, abs_of_nonneg timeRange.1.le]
      have interior : |fderiv ℝ form ray direction (point - center)|
          ≤ derivBound * ‖direction‖ * shrunk := by
        refine le_trans ((fderiv ℝ form ray direction).le_opNorm (point - center)) ?_
        exact mul_le_mul (le_trans ((fderiv ℝ form ray).le_opNorm direction)
          (mul_le_mul_of_nonneg_right (derivBounded ray rayInside) (norm_nonneg _)))
          pointDistance (norm_nonneg _) (by positivity)
      calc time * |fderiv ℝ form ray direction (point - center)|
          ≤ 1 * (derivBound * ‖direction‖ * shrunk) :=
            mul_le_mul timeRange.2 interior (abs_nonneg _) zero_le_one
        _ = derivBound * shrunk * ‖direction‖ := by ring
    calc |radialIntegrandDeriv center form point time direction|
        = |form ray direction + time * fderiv ℝ form ray direction (point - center)| := by
          rw [radialIntegrandDeriv_apply]
      _ ≤ |form ray direction| + |time * fderiv ℝ form ray direction (point - center)| :=
          abs_add_le _ _
      _ ≤ formBound * ‖direction‖ + derivBound * shrunk * ‖direction‖ :=
          add_le_add formStep derivStep
      _ = (formBound + derivBound * shrunk) * ‖direction‖ := by ring
  have neighbourhood : ball center shrunk ∈ nhds place :=
    isOpen_ball.mem_nhds (by simpa [mem_ball, dist_eq_norm] using innerBound)
  have derivative := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun point time => form (center + time • (point - center)) (point - center))
    (F' := fun point time => radialIntegrandDeriv center form point time)
    (bound := fun _ => formBound + derivBound * shrunk) neighbourhood
    (Filter.Eventually.of_forall fun point =>
      (continuous_form_along_ray center form diff point (point - center)).aestronglyMeasurable)
    ((continuous_form_along_ray center form diff place (place - center)).intervalIntegrable 0 1)
    (continuous_radialIntegrandDeriv center form smooth place).aestronglyMeasurable
    domination intervalIntegrable_const
    (Filter.Eventually.of_forall fun time point _ =>
      hasFDerivAt_radialIntegrand center form diff point time)
  have value : (∫ time in (0:ℝ)..1, radialIntegrandDeriv center form place time) = form place := by
    refine ContinuousLinearMap.ext fun direction => ?_
    rw [ContinuousLinearMap.intervalIntegral_apply
      ((continuous_radialIntegrandDeriv center form smooth place).intervalIntegrable 0 1)]
    exact integral_radialIntegrandDeriv_apply center form smooth symmetric mem direction
  rw [value] at derivative
  exact derivative

end RadialPotential

section CoordinateFields

open scoped ContDiff

/-- The one-form of a coordinate vector field: contraction against the field. -/
noncomputable def coordinateOneForm (field : VectorField) : Space → Space →L[ℝ] ℝ :=
  fun place => ∑ index : Fin 3, component index field place • EuclideanSpace.proj index

@[simp] theorem coordinateOneForm_apply (field : VectorField) (place direction : Space) :
    coordinateOneForm field place direction =
      ∑ index : Fin 3, field place index * direction index := by
  simp [coordinateOneForm, component]

theorem coordinateOneForm_axisDirection (field : VectorField) (place : Space) (axis : Fin 3) :
    coordinateOneForm field place (axisDirection axis) = field place axis := by
  simp [coordinateOneForm_apply, axisDirection]

theorem contDiff_coordinateOneForm {field : VectorField} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (coordinateOneForm field) :=
  ContDiff.sum fun index _ => (contDiff_component smooth index).smul contDiff_const

theorem hasFDerivAt_coordinateOneForm {field : VectorField} (smooth : ContDiff ℝ ∞ field)
    (place : Space) :
    HasFDerivAt (coordinateOneForm field)
      (∑ index : Fin 3, (fderiv ℝ (component index field) place).smulRight
        (EuclideanSpace.proj index)) place := by
  have shape : coordinateOneForm field =
      ∑ index : Fin 3, fun point : Space =>
        component index field point • (EuclideanSpace.proj index : Space →L[ℝ] ℝ) := by
    funext point
    simp [coordinateOneForm, Finset.sum_apply]
  rw [shape]
  exact HasFDerivAt.sum fun index _ =>
    ((differentiable_of_contDiff (contDiff_component smooth index)) place).hasFDerivAt.smul_const (EuclideanSpace.proj index : Space →L[ℝ] ℝ)

theorem fderiv_coordinateOneForm_apply {field : VectorField} (smooth : ContDiff ℝ ∞ field)
    (place first second : Space) :
    fderiv ℝ (coordinateOneForm field) place first second =
      ∑ index : Fin 3, fderiv ℝ (component index field) place first * second index := by
  rw [(hasFDerivAt_coordinateOneForm smooth place).fderiv]
  simp

/-- The Fréchet derivative of a smooth weight, expanded in the coordinate frame. -/
theorem fderiv_eq_sum_coordinateDeriv (weight : ScalarField) (place direction : Space) :
    fderiv ℝ weight place direction =
      ∑ axis : Fin 3, direction axis * coordinateDeriv axis weight place := by
  have expansion : direction = ∑ axis : Fin 3, direction axis • axisDirection axis := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr direction
    simpa [EuclideanSpace.basisFun_apply, axisDirection] using this.symm
  conv_lhs => rw [expansion]
  rw [map_sum]
  refine Finset.sum_congr rfl fun axis _ => ?_
  rw [map_smul]
  simp [coordinateDeriv, directionalDeriv, smul_eq_mul]

/--
**Curl-freeness at a point is symmetry of the derivative of the one-form there.**
-/
theorem symm_fderiv_coordinateOneForm {field : VectorField} (smooth : ContDiff ℝ ∞ field)
    {place : Space} (curl_free : curl field place = 0) (first second : Space) :
    fderiv ℝ (coordinateOneForm field) place first second =
      fderiv ℝ (coordinateOneForm field) place second first := by
  have components : ∀ index : Fin 3,
      coordinateDeriv (index + 1) (component (index + 2) field) place =
        coordinateDeriv (index + 2) (component (index + 1) field) place := by
    intro index
    have vanishes := congrFun curl_free index
    simp only [Pi.zero_apply] at vanishes
    have expand : curl field place index =
        coordinateDeriv (index + 1) (component (index + 2) field) place
          - coordinateDeriv (index + 2) (component (index + 1) field) place := rfl
    rw [expand] at vanishes
    linarith
  have crossOne : coordinateDeriv 1 (component 2 field) place =
      coordinateDeriv 2 (component 1 field) place := by simpa using components 0
  have crossTwo : coordinateDeriv 2 (component 0 field) place =
      coordinateDeriv 0 (component 2 field) place := by simpa using components 1
  have crossZero : coordinateDeriv 0 (component 1 field) place =
      coordinateDeriv 1 (component 0 field) place := by simpa using components 2
  rw [fderiv_coordinateOneForm_apply smooth, fderiv_coordinateOneForm_apply smooth]
  simp only [fderiv_eq_sum_coordinateDeriv, Fin.sum_univ_three]
  rw [crossOne, crossTwo, crossZero]
  ring

/--
**The Poincaré lemma on a ball, in the coordinates of `PDE/DivCurl.lean`.**

A smooth field whose rotational datum vanishes on a ball is a `gradient` there,
and the Laplacian of the potential is the divergence of the field.  In
particular a field that is *both* curl-free and divergence-free on the ball —
that is, a member of the harmonic kernel of the ball — is the gradient of a
harmonic potential.

This is the representation theorem `PDE/DivCurl.lean` does not have: it builds
the projection onto the harmonic kernel without ever representing its elements.
-/
theorem exists_potential_of_curl_eq_zero {field : VectorField} (smooth : ContDiff ℝ ∞ field)
    (center : Space) {radius : ℝ}
    (curl_free : ∀ place ∈ ball center radius, curl field place = 0) :
    ∃ weight : ScalarField,
      (∀ place ∈ ball center radius, gradient weight place = field place) ∧
      (∀ place ∈ ball center radius, scalarLaplacian weight place = divergence field place) := by
  set weight := radialPotential center (coordinateOneForm field) with weightDef
  have derivative : ∀ place ∈ ball center radius,
      HasFDerivAt weight (coordinateOneForm field place) place := by
    intro place mem
    exact hasFDerivAt_radialPotential center (coordinateOneForm field)
      ((contDiff_coordinateOneForm smooth).of_le (by simp))
      (fun point pointMem => symm_fderiv_coordinateOneForm smooth (curl_free point pointMem)) mem
  have gradientEq : ∀ place ∈ ball center radius, gradient weight place = field place := by
    intro place mem
    funext index
    show fderiv ℝ weight place (axisDirection index) = field place index
    rw [(derivative place mem).fderiv, coordinateOneForm_axisDirection]
  refine ⟨weight, gradientEq, ?_⟩
  intro place mem
  have second : ∀ index : Fin 3,
      coordinateDeriv index (coordinateDeriv index weight) place =
        coordinateDeriv index (component index field) place := by
    intro index
    have agree : coordinateDeriv index weight =ᶠ[nhds place] component index field := by
      filter_upwards [isOpen_ball.mem_nhds mem] with point pointMem
      show fderiv ℝ weight point (axisDirection index) = field point index
      rw [(derivative point pointMem).fderiv, coordinateOneForm_axisDirection]
    show fderiv ℝ (coordinateDeriv index weight) place (axisDirection index) = _
    rw [agree.fderiv_eq]
    rfl
  show (coordinateDeriv 0 (coordinateDeriv 0 weight) + coordinateDeriv 1 (coordinateDeriv 1 weight)
      + coordinateDeriv 2 (coordinateDeriv 2 weight)) place = divergence field place
  simp only [Pi.add_apply, divergence]
  rw [second 0, second 1, second 2]

end CoordinateFields

/-! ## The lifting of the window's harmonic part -/

section Lifting

open scoped ContDiff

variable {Field ScalarState : Type*} [AddCommGroup Field] [Zero ScalarState]
  {calculus : CurlDivergenceCalculus Field ScalarState}
  {Slice DivergenceValue CurlValue : Type*}
  [NormedAddCommGroup Slice] [InnerProductSpace ℝ Slice]
  [NormedAddCommGroup DivergenceValue] [NormedSpace ℝ DivergenceValue]
  [NormedAddCommGroup CurlValue] [NormedSpace ℝ CurlValue]

/--
**A `LocalNormalization` exhibited as the localization to a genuine window.**

`LocalNormalization` says only that there is *some* inner product space with two
continuous operators.  This structure says which one: the window is a ball of the
three-dimensional domain, every object in sight is read as a field or a weight on
that domain, and the abstract operators are the coordinate operators of
`PDE/DivCurl.lean` read there.  Nothing here is an interface clause about the
harmonic kernel; each field is a statement that the localization is the
localization to a window.

* `embed`, `represent`, `representDivergence`, `representCurl` — the four
  readings: of a state, of a slice element, and of the two operator targets.
* `sliceDivergence_represent`, `sliceCurl_represent` — the window's operators
  *are* the coordinate operators, read through those readings.  This is what
  makes "annihilated by `sliceCurl`" mean "curl-free on the window".
* `represent_restrict` — the restriction restricts: on the window it reads the
  state and nothing else.
* `represent_injective` — a slice element is determined by its values on the
  window.  A window `L²` has no other elements to be.
* `exists_potentialState` — the scalar states carry the window's potentials: a
  slice element which is *already* a gradient on the window is the gradient of a
  scalar state there.

The single analytic field is `harmonicKernel_smooth`, and it is confined to the
harmonic kernel: a slice element annihilated by both operators is a smooth field
on the window.  That is interior regularity for the pair `(div, curl)`, and it is
the one input this module does not prove.
-/
structure BallWindow (normalization : LocalNormalization calculus Slice DivergenceValue CurlValue)
    where
  /-- The centre of the window. -/
  center : Space
  /-- The radius of the window. -/
  radius : ℝ
  /-- A state, read as a field of the domain. -/
  embed : Field → VectorField
  /-- A slice element, read as a field of the domain. -/
  represent : Slice → VectorField
  /-- The divergence target, read as a weight of the domain. -/
  representDivergence : DivergenceValue → ScalarField
  /-- The curl target, read as a field of the domain. -/
  representCurl : CurlValue → VectorField
  /-- The reading of the absent divergence is the absent weight. -/
  representDivergence_zero : representDivergence 0 = 0
  /-- The reading of the absent rotational datum is the absent field. -/
  representCurl_zero : representCurl 0 = 0
  /-- **The window's divergence is the coordinate divergence.** -/
  sliceDivergence_represent : ∀ point : Slice, ∀ place ∈ Metric.ball center radius,
    representDivergence (normalization.sliceDivergence point) place =
      divergence (represent point) place
  /-- **The window's rotational operator is the coordinate curl.** -/
  sliceCurl_represent : ∀ point : Slice, ∀ place ∈ Metric.ball center radius,
    representCurl (normalization.sliceCurl point) place = curl (represent point) place
  /-- **The restriction restricts**: on the window it reads the state. -/
  represent_restrict : ∀ state : Field, ∀ place ∈ Metric.ball center radius,
    represent (normalization.restrict state) place = embed state place
  /-- **A slice element is its values on the window.** -/
  represent_injective : ∀ first second : Slice,
    (∀ place ∈ Metric.ball center radius, represent first place = represent second place) →
      first = second
  /-- **The scalar states carry the window's potentials.**  A slice element which
  is already a gradient on the window is the gradient of a scalar state there.
  The clause consumes a potential; producing one is
  `exists_potential_of_curl_eq_zero`. -/
  exists_potentialState : ∀ (weight : ScalarField) (point : Slice),
    (∀ place ∈ Metric.ball center radius, gradient weight place = represent point place) →
    ∃ potential : ScalarState, ∀ place ∈ Metric.ball center radius,
      embed (calculus.gradient potential) place = gradient weight place
  /-- **Interior regularity for the pair `(div, curl)`**: a slice element carrying
  neither datum is a smooth field on the window. -/
  harmonicKernel_smooth :
    ∀ point ∈ harmonicKernel normalization.sliceDivergence normalization.sliceCurl,
      ContDiff ℝ ∞ (represent point)

namespace BallWindow

variable {normalization : LocalNormalization calculus Slice DivergenceValue CurlValue}

/--
**A member of the window's harmonic kernel carries no rotational datum on the
window.**  A theorem, not a clause: the kernel condition `sliceCurl point = 0`
becomes the coordinate statement through `sliceCurl_represent`.
-/
theorem curl_represent_eq_zero (window : BallWindow normalization) {point : Slice}
    (mem : point ∈ harmonicKernel normalization.sliceDivergence normalization.sliceCurl)
    {place : Space} (placeMem : place ∈ Metric.ball window.center window.radius) :
    curl (window.represent point) place = 0 := by
  rw [← window.sliceCurl_represent point place placeMem, curl_eq_zero_of_mem mem,
    window.representCurl_zero]
  rfl

/--
**A member of the window's harmonic kernel carries no divergence on the window.**
-/
theorem divergence_represent_eq_zero (window : BallWindow normalization) {point : Slice}
    (mem : point ∈ harmonicKernel normalization.sliceDivergence normalization.sliceCurl)
    {place : Space} (placeMem : place ∈ Metric.ball window.center window.radius) :
    divergence (window.represent point) place = 0 := by
  rw [← window.sliceDivergence_represent point place placeMem, divergence_eq_zero_of_mem mem,
    window.representDivergence_zero]
  rfl

/--
**A slice element that is a gradient on the window is the restriction of the
gradient of a state.**

A theorem, not a clause: the scalar state exists by `exists_potentialState`, its
gradient reads on the window as the given one by `represent_restrict`, and a
slice element is its values on the window.
-/
theorem restrict_gradient_eq (window : BallWindow normalization) (weight : ScalarField)
    (point : Slice)
    (agrees : ∀ place ∈ Metric.ball window.center window.radius,
      gradient weight place = window.represent point place) :
    ∃ potential : ScalarState,
      normalization.restrict (calculus.gradient potential) = point := by
  obtain ⟨potential, gradientEq⟩ := window.exists_potentialState weight point agrees
  refine ⟨potential, window.represent_injective _ _ fun place placeMem => ?_⟩
  rw [window.represent_restrict _ place placeMem, gradientEq place placeMem,
    agrees place placeMem]

/--
**A member of the window's harmonic kernel is the gradient of a harmonic
potential on the window.**

This is `exists_potential_of_curl_eq_zero` at the reading of the element:
curl-freeness on the window gives the potential, divergence-freeness makes it
harmonic.  Both are the theorems above.
-/
theorem exists_harmonic_potential (window : BallWindow normalization) {point : Slice}
    (mem : point ∈ harmonicKernel normalization.sliceDivergence normalization.sliceCurl) :
    ∃ weight : ScalarField,
      (∀ place ∈ Metric.ball window.center window.radius,
        gradient weight place = window.represent point place) ∧
      (∀ place ∈ Metric.ball window.center window.radius, scalarLaplacian weight place = 0) := by
  obtain ⟨weight, gradientEq, laplacianEq⟩ :=
    exists_potential_of_curl_eq_zero (window.harmonicKernel_smooth point mem) window.center
      (fun place placeMem => window.curl_represent_eq_zero mem placeMem)
  exact ⟨weight, gradientEq, fun place placeMem =>
    (laplacianEq place placeMem).trans (window.divergence_represent_eq_zero mem placeMem)⟩

variable [CompleteSpace Slice]

/--
**The lifting, supplied by the framework.**

For *every* state, the harmonic part of its restriction to the window is the
restriction of the gradient of a scalar state.  Nothing about the state enters:
the harmonic part is a member of the window's harmonic kernel by construction,
hence curl-free on the window by `curl_represent_eq_zero`, hence a gradient there
by the Poincaré lemma.

This is the statement `PDE/Solution/QuotientRecoveryData.lean` calls `lifts` and
takes as an input of `NormalizedRecovery.ofLifting`.
-/
theorem exists_potential_restrict_eq_harmonicSlicePart (window : BallWindow normalization)
    (field : Field) :
    ∃ potential : ScalarState,
      normalization.restrict (calculus.gradient potential) =
        normalization.harmonicSlicePart field := by
  have mem : normalization.harmonicSlicePart field ∈
      harmonicKernel normalization.sliceDivergence normalization.sliceCurl :=
    Submodule.starProjection_apply_mem _ _
  obtain ⟨weight, gradientEq, _⟩ := window.exists_harmonic_potential mem
  exact window.restrict_gradient_eq weight _ gradientEq

/--
**The recovery relation with no lifting input.**

`NormalizedRecovery.ofLifting` asks for a splitting of the state whose discarded
component restricts to the projection on the window.  Here the discarded
component is *constructed*: it is the gradient of the potential supplied by the
Poincaré lemma, the splitting is the tautological one, and the lifting is the
theorem above.

What remains as input is subtractivity of the restriction — a property of the
realization, carried explicitly for the same reason `LocalNormalization` carries
additivity explicitly — and the vanishing of the source's projection on the
window.  No gauge condition, and no lifting, is asked of the caller.
-/
theorem normalizedRecovery (window : BallWindow normalization)
    (data : QuotientRecoveryData normalization)
    (restrict_sub : ∀ first second : Field,
      normalization.restrict (first - second) =
        normalization.restrict first - normalization.restrict second)
    (field forcing : Field)
    (forcing_harmonic_free : normalization.harmonicSlicePart forcing = 0) :
    ∃ potential : ScalarState,
      NormalizedRecovery data field (field - calculus.gradient potential) forcing := by
  obtain ⟨potential, lifts⟩ := window.exists_potential_restrict_eq_harmonicSlicePart field
  refine ⟨potential, NormalizedRecovery.ofLifting data restrict_sub ?_ lifts
    forcing_harmonic_free⟩
  abel

end BallWindow

end Lifting

end Hypostructure.PDE.DivCurl
