import Hypostructure.PDE.Localization.Cutoff

/-!
# The cutoff commutator of a heat-type operator, and the bootstrap it feeds

Interior smoothing for a heat-type operator is proved by a cutoff/parametrix
bootstrap.  One writes the operator as `L = ∂_time − Δ`, multiplies the
solution by a cutoff `weight` that is one on an inner window and supported in
an outer one, and observes that

> `L (weight • field) = weight • L field + [L, weight] field`,

where the commutator `[L, weight] field` involves **only first derivatives of
the field**, each multiplied by a derivative of the cutoff.  Two facts then
drive the whole argument:

* the commutator is one order *cheaper* in the field than `L (weight • field)`
  is, so a parametrix estimate for `L` on the cut-off field converts
  regularity already available into regularity two orders higher;
* every term of the commutator carries a derivative of the cutoff, so it
  **vanishes wherever the cutoff is locally constant** — in particular on the
  inner window, where nothing outside the outer window can contaminate the
  gain.

Iterating over a finite chain of shrinking windows raises the order without
limit, and a Sobolev embedding at the end converts the order into smoothness.

## What this module contains, and what it does not

This module owns the *algebraic and geometric* half of that argument, which is
unconditional and fully proved here:

* `directionalDeriv` and its Leibniz rules, including the second-order rule
  `directionalDeriv_two_smul`, which is where the factor `2` on the mixed term
  comes from;
* `heatOperator`, a constant-coefficient operator of heat type: one
  distinguished direction differentiated once, minus a finite family of
  directions differentiated twice.  The ordinary heat operator is the case
  where the family is an orthonormal basis of the space directions and the
  distinguished direction is time; nothing here names an equation, a
  dimension, or a physical quantity;
* `heatOperator_smul`, the commutator identity itself;
* `heatCommutator_eq_zero_of_eventuallyEq_one`, the support fact: the
  commutator vanishes at every point where the cutoff is locally one.  Applied
  to the framework's bump cutoff (`Hypostructure.PDE.Localization.cutoff`) this
  gives `heatOperator_cutoffSmul_eq`: on the inner window the cut-off field
  solves *exactly the same equation* as the field;
* `regular_of_shrinking_chain` and `regular_target_of_shrinking_chain`, the
  bootstrap skeleton: given a one-step gain as a hypothesis, an induction over
  a chain of shrinking windows delivers every order on the innermost window;
* `chainRadius`, a concrete chain of radii strictly between an inner and an
  outer one, so that the skeleton is instantiated at an honestly nonempty
  geometry rather than left abstract.

What is not here is the *quantitative* input: the local parametrix estimate
that bounds a cut-off field in a parabolic Sobolev norm two orders up by the
source plus a negative norm of the field.  mathlib has no parabolic
(anisotropic) Sobolev scale — its Sobolev spaces
(`TemperedDistribution.MemSobolev`) are isotropic Bessel potential spaces on a
single normed space, with no time direction weighted at half order.  That
estimate is therefore taken as the hypothesis `gain` of the bootstrap theorems
below, and it is what a *sharp* local estimate with parabolic orders `2j + k`
needs.

**It is not what smoothness needs, and smoothness is not assumed anywhere.**
The qualitative half of interior heat smoothing is proved outright, on the
isotropic scale, in `PDE/Solution/ParabolicRegularity.lean`:
`memSobolev_add_half_of_split` is a Fourier-multiplier argument — the symbol
`i tau + |xi|^2` dominates the isotropic weight, so `solvedMultiplier (1/2)`
and `remainderMultiplier (1/2)` both have temperate growth and norm at most one
— giving half an isotropic derivative per step with no estimate imported.
`sobolevOn_add_half_natCast` iterates that with no ceiling and
`smoothOn_of_heat_smoothOn` reaches every grade, hence `SmoothOn`.

So a caller who needs `w` to be `C^infinity` on the inner window uses
`smoothOn_ball_of_heat_smoothOn` and imports nothing; the `gain` hypothesis
here is required only by a caller who needs the estimate itself.

The commutator identity is stated for a smooth field.  In the bootstrap this
is not a loss: each step applies the identity to the regularity already gained
on the previous window, and the identity is the algebra of that step.  Making
it distributional would require a distributional product rule against a smooth
multiplier, which is a separate development.
-/

namespace Hypostructure.PDE.HeatSmoothing

open Metric
open scoped ContDiff

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/-! ## Directional derivatives and their Leibniz rules

Everything below is built from a single primitive: the derivative of a field
along a fixed direction.  Working with directions rather than with coordinates
keeps the operator problem-agnostic — the "space" directions are an arbitrary
finite family — and keeps the Leibniz rules one-dimensional, which is why the
second-order rule can be proved by applying the first-order one three times.
-/

/-- The derivative of `field` along `direction`, as a field again.

This is `fderiv` evaluated at a fixed vector.  Iterating it is what produces
the second-order part of a heat-type operator. -/
noncomputable def directionalDeriv (direction : Point) (field : Point → Value) :
    Point → Value :=
  fun place => fderiv ℝ field place direction

/-- Differentiating along a direction preserves smoothness, so the second
derivative appearing in a heat-type operator is again smooth and the Leibniz
rules may be iterated. -/
theorem contDiff_directionalDeriv (direction : Point) {field : Point → Value}
    (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (directionalDeriv direction field) :=
  (smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- A directional derivative is additive. -/
theorem directionalDeriv_add (direction : Point) {first second : Point → Value}
    (first_differentiable : Differentiable ℝ first)
    (second_differentiable : Differentiable ℝ second) :
    directionalDeriv direction (fun place => first place + second place) =
      fun place => directionalDeriv direction first place +
        directionalDeriv direction second place := by
  funext place
  rw [directionalDeriv, directionalDeriv, directionalDeriv,
    fderiv_fun_add (first_differentiable place) (second_differentiable place)]
  rfl

/-- **First-order Leibniz rule.**  Differentiating a cut-off field along a
direction produces the cut-off derivative plus the derivative of the cutoff
times the field: the second term is the whole of the commutator at first
order, and it already carries a derivative of the cutoff. -/
theorem directionalDeriv_smul (direction : Point) {weight : Point → ℝ}
    {field : Point → Value} (weight_differentiable : Differentiable ℝ weight)
    (field_differentiable : Differentiable ℝ field) :
    directionalDeriv direction (fun place => weight place • field place) =
      fun place => weight place • directionalDeriv direction field place +
        directionalDeriv direction weight place • field place := by
  funext place
  simp [directionalDeriv,
    fderiv_fun_smul (weight_differentiable place) (field_differentiable place)]

/-- **Second-order Leibniz rule.**  The mixed term carries the factor `2`
because the first-order rule is applied to both summands it produces.

This is the identity that makes the bootstrap work: on the right-hand side the
field is differentiated *at most twice*, but every term that is not
`weight • (second derivative of the field)` costs a derivative of the cutoff
and spends at most **one** derivative on the field. -/
theorem directionalDeriv_two_smul (direction : Point) {weight : Point → ℝ}
    {field : Point → Value} (weight_smooth : ContDiff ℝ ∞ weight)
    (field_smooth : ContDiff ℝ ∞ field) :
    directionalDeriv direction
        (directionalDeriv direction (fun place => weight place • field place)) =
      fun place =>
        weight place •
            directionalDeriv direction (directionalDeriv direction field) place +
          (2 : ℝ) • (directionalDeriv direction weight place •
            directionalDeriv direction field place) +
          directionalDeriv direction (directionalDeriv direction weight) place •
            field place := by
  have weight_differentiable : Differentiable ℝ weight :=
    weight_smooth.differentiable (by simp)
  have field_differentiable : Differentiable ℝ field :=
    field_smooth.differentiable (by simp)
  have weight_deriv_differentiable :
      Differentiable ℝ (directionalDeriv direction weight) :=
    (contDiff_directionalDeriv direction weight_smooth).differentiable (by simp)
  have field_deriv_differentiable :
      Differentiable ℝ (directionalDeriv direction field) :=
    (contDiff_directionalDeriv direction field_smooth).differentiable (by simp)
  have cutoff_part_differentiable : Differentiable ℝ
      (fun place => weight place • directionalDeriv direction field place) :=
    fun place => (weight_differentiable place).smul (field_deriv_differentiable place)
  have commutator_part_differentiable : Differentiable ℝ
      (fun place => directionalDeriv direction weight place • field place) :=
    fun place => (weight_deriv_differentiable place).smul (field_differentiable place)
  rw [directionalDeriv_smul direction weight_differentiable field_differentiable,
    directionalDeriv_add direction cutoff_part_differentiable
      commutator_part_differentiable,
    directionalDeriv_smul direction weight_differentiable
      field_deriv_differentiable,
    directionalDeriv_smul direction weight_deriv_differentiable
      field_differentiable]
  funext place
  module

/-! ## The heat-type operator and its cutoff commutator -/

variable {Index : Type uIndex} [Fintype Index]

/-- A constant-coefficient operator of heat type: one derivative along
`timeDirection`, minus the sum of second derivatives along a finite family of
`spaceDirections`.

The classical heat operator `∂_t − Δ` is the case where `spaceDirections` is an
orthonormal basis of the space factor; degenerate families are allowed, and no
relation between the time direction and the space directions is imposed,
because none is needed for the algebra below. -/
noncomputable def heatOperator (timeDirection : Point)
    (spaceDirections : Index → Point) (field : Point → Value) : Point → Value :=
  fun place => directionalDeriv timeDirection field place -
    ∑ index, directionalDeriv (spaceDirections index)
      (directionalDeriv (spaceDirections index) field) place

/-- The commutator `[heatOperator, weight]` applied to a field.

Every summand carries a derivative of `weight`, and the field is
differentiated at most once.  Both features are essential: the first makes the
commutator vanish on the inner window, the second is what makes the bootstrap
gain rather than merely recycle. -/
noncomputable def heatCommutator (timeDirection : Point)
    (spaceDirections : Index → Point) (weight : Point → ℝ)
    (field : Point → Value) : Point → Value :=
  fun place => directionalDeriv timeDirection weight place • field place -
    ∑ index,
      (directionalDeriv (spaceDirections index)
          (directionalDeriv (spaceDirections index) weight) place • field place +
        (2 : ℝ) • (directionalDeriv (spaceDirections index) weight place •
          directionalDeriv (spaceDirections index) field place))

/-- **The commutator identity.**  Applying a heat-type operator to a cut-off
field gives the cut-off image plus a commutator that costs a derivative of the
cutoff and spends at most one derivative on the field.

This is the algebraic heart of the interior smoothing argument: it is what
lets a parametrix estimate for the operator, applied to `weight • field`, be
fed by data (`heatOperator field`, which is the source) together with strictly
lower-order information about `field` on the support of the cutoff. -/
theorem heatOperator_smul (timeDirection : Point)
    (spaceDirections : Index → Point) {weight : Point → ℝ}
    {field : Point → Value} (weight_smooth : ContDiff ℝ ∞ weight)
    (field_smooth : ContDiff ℝ ∞ field) :
    heatOperator timeDirection spaceDirections
        (fun place => weight place • field place) =
      fun place => weight place •
          heatOperator timeDirection spaceDirections field place +
        heatCommutator timeDirection spaceDirections weight field place := by
  have weight_differentiable : Differentiable ℝ weight :=
    weight_smooth.differentiable (by simp)
  have field_differentiable : Differentiable ℝ field :=
    field_smooth.differentiable (by simp)
  funext place
  simp only [heatOperator, heatCommutator,
    directionalDeriv_smul timeDirection weight_differentiable field_differentiable,
    fun index => directionalDeriv_two_smul (spaceDirections index) weight_smooth
      field_smooth]
  rw [smul_sub, Finset.smul_sum, sub_add_sub_comm, ← Finset.sum_add_distrib]
  refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun index _ => ?_)
  module

/-! ## The support fact

Every term of the commutator carries a derivative of the cutoff, so the
commutator vanishes wherever the cutoff is *locally* constant — not merely
where it takes the value one.  This is the precise sense in which "no value of
the field outside the outer window enters" the gain on the inner window.
-/

/-- A field that is locally constant at a point has vanishing directional
derivative there. -/
theorem directionalDeriv_eq_zero_of_eventuallyEq_const (direction : Point)
    {weight : Point → ℝ} {place : Point} {value : ℝ}
    (locally_constant : weight =ᶠ[nhds place] fun _ => value) :
    directionalDeriv direction weight place = 0 := by
  simp [directionalDeriv, locally_constant.fderiv_eq]

/-- A field that is locally constant at a point has vanishing *second*
directional derivative there: local constancy propagates to a neighbourhood,
where the first derivative vanishes identically. -/
theorem directionalDeriv_two_eq_zero_of_eventuallyEq_const
    (first second : Point) {weight : Point → ℝ} {place : Point} {value : ℝ}
    (locally_constant : weight =ᶠ[nhds place] fun _ => value) :
    directionalDeriv second (directionalDeriv first weight) place = 0 := by
  have derivative_locally_zero :
      directionalDeriv first weight =ᶠ[nhds place] fun _ => (0 : ℝ) :=
    locally_constant.eventuallyEq_nhds.mono fun _ nearby =>
      directionalDeriv_eq_zero_of_eventuallyEq_const first nearby
  exact directionalDeriv_eq_zero_of_eventuallyEq_const second derivative_locally_zero

/-- **The support fact.**  Where the cutoff is locally one, the commutator
vanishes outright.

Combined with `heatOperator_smul` this says that on the inner window the
cut-off field solves the very same equation as the field: the localization has
cost nothing there, which is what allows the gain to be iterated. -/
theorem heatCommutator_eq_zero_of_eventuallyEq_one (timeDirection : Point)
    (spaceDirections : Index → Point) {weight : Point → ℝ}
    (field : Point → Value) {place : Point}
    (locally_one : weight =ᶠ[nhds place] fun _ => (1 : ℝ)) :
    heatCommutator timeDirection spaceDirections weight field place = 0 := by
  simp [heatCommutator,
    directionalDeriv_eq_zero_of_eventuallyEq_const _ locally_one,
    directionalDeriv_two_eq_zero_of_eventuallyEq_const _ _ locally_one]

/-- On the inner window, the heat-type operator commutes with the cutoff: the
localized field carries exactly the localized source. -/
theorem heatOperator_smul_eq_of_eventuallyEq_one (timeDirection : Point)
    (spaceDirections : Index → Point) {weight : Point → ℝ}
    {field : Point → Value} (weight_smooth : ContDiff ℝ ∞ weight)
    (field_smooth : ContDiff ℝ ∞ field) {place : Point}
    (locally_one : weight =ᶠ[nhds place] fun _ => (1 : ℝ)) :
    heatOperator timeDirection spaceDirections
        (fun other => weight other • field other) place =
      heatOperator timeDirection spaceDirections field place := by
  have identity := congrFun
    (heatOperator_smul timeDirection spaceDirections weight_smooth field_smooth)
    place
  have value_one : weight place = 1 := locally_one.eq_of_nhds
  rw [identity, heatCommutator_eq_zero_of_eventuallyEq_one timeDirection
    spaceDirections field locally_one, value_one, one_smul, add_zero]

/-! ## The framework's cutoff

The bump cutoff of `Hypostructure.PDE.Localization` is one on the inner window
and supported in the outer one, so it is locally one at every point of the
open inner window and the support fact applies there verbatim.  This is the
statement the localization step actually consumes.
-/

section Cutoff

variable [HasContDiffBump Point]

/-- The framework cutoff is *locally* one on the open inner window, which is
the hypothesis the support fact wants: equality at a point is not enough,
since the commutator sees derivatives. -/
theorem cutoff_eventuallyEq_one (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {place : Point}
    (mem : place ∈ ball center inner) :
    Localization.cutoff center inner_pos nested =ᶠ[nhds place] fun _ => (1 : ℝ) :=
  Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds mem) fun _ nearby =>
    Localization.cutoff_eq_one center inner_pos nested (ball_subset_closedBall nearby)

/-- The framework cutoff is smooth, in the exponent the Leibniz rules above
are stated at. -/
theorem cutoff_contDiff_infty (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) :
    ContDiff ℝ ∞ (Localization.cutoff center inner_pos nested) :=
  Localization.cutoff_contDiff center inner_pos nested

/-- **Localization costs nothing on the inner window.**  Cutting a field off
with the framework's bump changes neither the field nor its heat-type image
anywhere on the open inner window, while making the cut-off field compactly
supported — which is what a whole-space parametrix requires.

This is the exact statement the paper uses when it says the commutator
`[∂_t − Δ, χ₀]w` is supported in `{χ₁ = 1} \ Q_{σ₀}` and so never contaminates
the gain on the inner cylinder. -/
theorem heatOperator_cutoffSmul_eq (timeDirection : Point)
    (spaceDirections : Index → Point) (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {field : Point → Value}
    (field_smooth : ContDiff ℝ ∞ field) {place : Point}
    (mem : place ∈ ball center inner) :
    heatOperator timeDirection spaceDirections
        (fun other => Localization.cutoff center inner_pos nested other • field other)
        place =
      heatOperator timeDirection spaceDirections field place :=
  heatOperator_smul_eq_of_eventuallyEq_one timeDirection spaceDirections
    (cutoff_contDiff_infty center inner_pos nested) field_smooth
    (cutoff_eventuallyEq_one center inner_pos nested mem)

end Cutoff

/-! ## The bootstrap skeleton

The paper's iteration is: choose a finite chain of windows shrinking from the
outer one down to the inner one; apply the parametrix estimate on the first,
gaining regularity; apply it again on the second, where the commutator only
uses the regularity just gained; and so on.  After `grade` steps the field has
gained `grade` orders on the `grade`-th window, and since the target window is
contained in *every* window of the chain, it has gained every order there.

The induction is stated with the one-step gain as a hypothesis.  That is the
honest division of labour: the gain is the parametrix estimate, which needs a
parabolic Sobolev scale that mathlib does not have; everything else — that
finitely many gains compose, and that the innermost window inherits all of
them — is proved.
-/

omit [NormedAddCommGroup Point] [NormedSpace ℝ Point] in
/-- **The bootstrap.**  A one-step gain along a chain of windows delivers every
order, each on its own window. -/
theorem regular_of_shrinking_chain {window : ℕ → Set Point}
    {regular : ℕ → Set Point → Prop} (base : regular 0 (window 0))
    (gain : ∀ grade : ℕ, regular grade (window grade) →
      regular (grade + 1) (window (grade + 1))) :
    ∀ grade : ℕ, regular grade (window grade) := by
  intro grade
  induction grade with
  | zero => exact base
  | succ previous gained => exact gain previous gained

omit [NormedAddCommGroup Point] [NormedSpace ℝ Point] in
/-- **The bootstrap, read on the target window.**  If the target sits inside
every window of the chain and regularity restricts to smaller windows, the
target carries every order — which is the finite-order half of "the field is
smooth on the inner window". -/
theorem regular_target_of_shrinking_chain {window : ℕ → Set Point}
    {target : Set Point} {regular : ℕ → Set Point → Prop}
    (restricts : ∀ (grade : ℕ) (larger smaller : Set Point), smaller ⊆ larger →
      regular grade larger → regular grade smaller)
    (target_inside : ∀ grade : ℕ, target ⊆ window grade)
    (base : regular 0 (window 0))
    (gain : ∀ grade : ℕ, regular grade (window grade) →
      regular (grade + 1) (window (grade + 1))) :
    ∀ grade : ℕ, regular grade target := fun grade =>
  restricts grade (window grade) target (target_inside grade)
    (regular_of_shrinking_chain base gain grade)

/-! ## A concrete chain of windows

The skeleton above is worth nothing if no chain exists, so here is one: radii
decreasing strictly from the outer radius to the inner one, never reaching it.
Each window strictly contains the next — which is exactly the hypothesis the
framework cutoff needs in order to be built between two consecutive windows —
and every window contains the target.
-/

/-- The `step`-th radius of a chain interpolating from `outerRadius` down
towards `innerRadius`.  Step `0` is the outer radius; no step ever reaches the
inner one, leaving room for a cutoff at every stage. -/
noncomputable def chainRadius (innerRadius outerRadius : ℝ) (step : ℕ) : ℝ :=
  innerRadius + (outerRadius - innerRadius) / (step + 1)

/-- The chain starts at the outer radius. -/
theorem chainRadius_zero (innerRadius outerRadius : ℝ) :
    chainRadius innerRadius outerRadius 0 = outerRadius := by
  simp [chainRadius]

/-- Every radius of the chain is strictly above the inner one, so a cutoff
between the target and any window of the chain exists. -/
theorem inner_lt_chainRadius {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) (step : ℕ) :
    innerRadius < chainRadius innerRadius outerRadius step := by
  have positive : (0 : ℝ) < (step : ℝ) + 1 := by positivity
  have gap : 0 < (outerRadius - innerRadius) / ((step : ℝ) + 1) :=
    div_pos (by linarith) positive
  simpa [chainRadius] using gap

/-- Consecutive windows of the chain are strictly nested, which is the
hypothesis a bump cutoff between them requires. -/
theorem chainRadius_succ_lt {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) (step : ℕ) :
    chainRadius innerRadius outerRadius (step + 1) <
      chainRadius innerRadius outerRadius step := by
  have positive : (0 : ℝ) < (step : ℝ) + 1 := by positivity
  have positive_succ : (0 : ℝ) < (step : ℝ) + 1 + 1 := by positivity
  have gap : 0 < outerRadius - innerRadius := by linarith
  have compare : (outerRadius - innerRadius) / ((step : ℝ) + 1 + 1) <
      (outerRadius - innerRadius) / ((step : ℝ) + 1) := by
    apply div_lt_div_of_pos_left gap positive
    linarith
  simpa [chainRadius, add_assoc] using compare

omit [NormedSpace ℝ Point] in
/-- The target window sits inside every window of the chain. -/
theorem closedBall_subset_chainWindow (center : Point) {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) (step : ℕ) :
    closedBall center innerRadius ⊆
      ball center (chainRadius innerRadius outerRadius step) :=
  closedBall_subset_ball (inner_lt_chainRadius nested step)

omit [NormedSpace ℝ Point] in
/-- **The bootstrap on the concrete chain.**  Feeding the chain of shrinking
balls into the skeleton: a one-step gain between consecutive balls delivers
every order on the inner ball.

This is the shape of the paper's conclusion, with the analytic content — the
one-step gain, i.e. the local parametrix estimate for the heat-type operator —
isolated as the hypothesis `gain`. -/
theorem regular_closedBall_of_chain (center : Point) {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) {regular : ℕ → Set Point → Prop}
    (restricts : ∀ (grade : ℕ) (larger smaller : Set Point), smaller ⊆ larger →
      regular grade larger → regular grade smaller)
    (base : regular 0 (ball center outerRadius))
    (gain : ∀ grade : ℕ,
      regular grade (ball center (chainRadius innerRadius outerRadius grade)) →
      regular (grade + 1)
        (ball center (chainRadius innerRadius outerRadius (grade + 1)))) :
    ∀ grade : ℕ, regular grade (closedBall center innerRadius) := by
  refine regular_target_of_shrinking_chain
    (window := fun step => ball center (chainRadius innerRadius outerRadius step))
    restricts (fun step => closedBall_subset_chainWindow center nested step)
    ?_ gain
  simpa [chainRadius_zero] using base

end Hypostructure.PDE.HeatSmoothing
