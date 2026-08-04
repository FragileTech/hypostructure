import Hypostructure.PDE.HeatSmoothing
import Hypostructure.PDE.Localization.Tempered

/-!
# Interior elliptic regularity, obtained purely locally

A residual knows its state only on its own window.  The whole-space bootstrap
of `PDE/Solution/EllipticRegularity.lean` — *if a state and its Laplacian both
sit at grade `s`, the state sits at grade `s + 2`* — is therefore not directly
applicable: the state need not be a tempered distribution of any global grade,
and no boundary condition is available to make it one.

The classical fix is the one this module carries out, and it is purely local:

> cut the state off, apply the whole-space bootstrap to the cut-off state, and
> read the conclusion back on the inner window.

Two facts make it work, and both are proved here rather than assumed:

* **the elliptic commutator spends at most one derivative on the state.**
  `Δ (χ u) = χ (Δ u) + 2 ∑ᵢ (∂ᵢ χ)(∂ᵢ u) + (Δ χ) u`.  Everything on the right
  except `χ (Δ u)` carries a derivative of the cutoff, and the worst of them
  differentiates `u` only once.  That is why the bootstrap *gains* instead of
  merely recycling: fed at grade `s − 1` it returns grade `s + 1`.
* **the commutator vanishes where the cutoff is locally one.**  Every summand
  of it carries a derivative of `χ`, so nothing outside the outer window can
  contaminate the conclusion on the inner one.

## The carrier: `SobolevOn`, i.e. `H^s` on a window

The predicate this module works with is the standard local Sobolev space:

> `SobolevOn region grade state` — *every* smooth compactly supported bump
> supported in `region` carries `state` into the global `H^grade`.

Quantifying over *all* bumps rather than fixing one is what makes the argument
go through without a multiplication theorem for `H^s`.  A single fixed cutoff
would force one to know that `(Δ χ) u` is still at grade `s` — a genuine
symbol estimate that mathlib does not prove.  With the local space, `(Δ χ) u`
is *by definition* the localization of `u` by another admissible bump, and the
estimate is free.  This is not a weakening: `SobolevOn` is exactly
`H^s_loc(region)`, and it is the statement an interior regularity theorem is
supposed to produce.

## What is proved

* `laplacian_localize` — the elliptic commutator identity, at the level of
  tempered distributions (so the state is *not* assumed to be a function);
* `ellipticCommutator_vanishesOn_ball` — the commutator vanishes on the inner
  window of the framework's bump cutoff;
* `sobolevOn_add_one` — **the one-step gain**: state at grade `s` on a window
  and Laplacian at grade `s` on that window give the state grade `s + 1`
  there.  One grade per step, honestly: the commutator costs a derivative;
* `sobolevOn_add_natCast` and `sobolevOn_chain` — the iteration, the latter run
  over the shrinking chain of windows of `PDE/HeatSmoothing.lean`;
* `smoothOn_of_laplacian_smoothOn` — **the payoff**: a state whose Laplacian is
  smooth on a window is smooth on every window contained in it.

The payoff is stated so that a div–curl step consumes it directly: there one
has `-Δ v = curl (curl v)` with the right-hand side smooth on a window, and
the theorem returns smoothness of `v` on the smaller window.

Nothing here names an equation, a dimension, a boundary condition or a
physical quantity.
-/

namespace Hypostructure.PDE.Solution.InteriorRegularity

open MeasureTheory Metric TemperedDistribution
open Hypostructure.PDE.HeatSmoothing (directionalDeriv contDiff_directionalDeriv)
open scoped SchwartzMap ENNReal ContDiff LineDeriv Laplacian

universe uPoint uValue uIndex

/-! ## Bumps: the smooth compactly supported multipliers

A localization is performed by multiplying by a smooth compactly supported
function.  Bundling the two properties keeps every statement below free of
repeated side conditions, and — more importantly — makes the *closure*
properties usable: the derivative of a bump is a bump, and so is its classical
Laplacian, which is exactly what the commutator identity produces.
-/

section Bump

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point]

/-- A smooth, compactly supported complex multiplier: the cutoff a
localization argument multiplies by. -/
structure Bump (Point : Type uPoint) [NormedAddCommGroup Point]
    [InnerProductSpace ℝ Point] where
  /-- The multiplier itself. -/
  weight : Point → ℂ
  /-- Smoothness, needed because the commutator differentiates the multiplier
  twice. -/
  smooth : ContDiff ℝ ∞ weight
  /-- Compact support, which is what makes the multiplier temperate and hence
  admissible as a multiplier on tempered distributions. -/
  compactSupport : HasCompactSupport weight

/-- A bump is of temperate growth, so it multiplies tempered distributions.
This is the only reason compact support is demanded. -/
theorem Bump.hasTemperateGrowth (bump : Bump Point) :
    bump.weight.HasTemperateGrowth :=
  bump.compactSupport.hasTemperateGrowth bump.smooth

/-- The derivative of a bump along a direction is again a bump: smoothness is
preserved, and differentiating cannot enlarge the support. -/
noncomputable def Bump.deriv (direction : Point) (bump : Bump Point) :
    Bump Point where
  weight := directionalDeriv direction bump.weight
  smooth := contDiff_directionalDeriv direction bump.smooth
  compactSupport := bump.compactSupport.fderiv_apply (𝕜 := ℝ) direction

@[simp]
theorem Bump.deriv_weight (direction : Point) (bump : Bump Point) :
    (bump.deriv direction).weight = directionalDeriv direction bump.weight :=
  rfl

/-- Differentiating a bump does not enlarge its support.  This is what keeps
every term of the commutator supported inside the same window, and hence
admissible for the *same* local Sobolev space. -/
theorem Bump.tsupport_deriv_subset (direction : Point) (bump : Bump Point) :
    tsupport (bump.deriv direction).weight ⊆ tsupport bump.weight :=
  tsupport_fderiv_apply_subset ℝ direction

variable {Index : Type uIndex} [Fintype Index]

/-- The sum of the pure second derivatives of a bump is still supported in the
bump's own window: differentiating cannot enlarge a support, and a finite sum
vanishes wherever all its summands do.  This is what keeps the zeroth-order
term of the elliptic commutator inside the window it started in. -/
theorem tsupport_sum_deriv_two_subset (basis : OrthonormalBasis Index ℝ Point)
    (bump : Bump Point) :
    tsupport (fun place => ∑ index,
        ((bump.deriv (basis index)).deriv (basis index)).weight place) ⊆
      tsupport bump.weight := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro place nonzero
  by_contra outside
  refine nonzero (Finset.sum_eq_zero fun index _ => ?_)
  refine image_eq_zero_of_notMem_tsupport fun mem => outside ?_
  exact Bump.tsupport_deriv_subset _ _ (Bump.tsupport_deriv_subset _ _ mem)

/-- The classical Laplacian of a bump, along an orthonormal family of
directions.  It is the coefficient of the zeroth-order term of the elliptic
commutator, and it is again a bump — which is precisely what allows that term
to be absorbed into the same local Sobolev space. -/
noncomputable def Bump.laplacian (basis : OrthonormalBasis Index ℝ Point)
    (bump : Bump Point) : Bump Point where
  weight := fun place => ∑ index,
    ((bump.deriv (basis index)).deriv (basis index)).weight place
  smooth := ContDiff.sum fun index _ =>
    ((bump.deriv (basis index)).deriv (basis index)).smooth
  compactSupport :=
    bump.compactSupport.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_sum_deriv_two_subset basis bump)

@[simp]
theorem Bump.laplacian_weight (basis : OrthonormalBasis Index ℝ Point)
    (bump : Bump Point) :
    (bump.laplacian basis).weight = fun place => ∑ index,
      ((bump.deriv (basis index)).deriv (basis index)).weight place :=
  rfl

/-- The classical Laplacian of a bump lives in the bump's own window. -/
theorem Bump.tsupport_laplacian_subset (basis : OrthonormalBasis Index ℝ Point)
    (bump : Bump Point) :
    tsupport (bump.laplacian basis).weight ⊆ tsupport bump.weight :=
  tsupport_sum_deriv_two_subset basis bump

end Bump

/-! ## Localization of a tempered distribution

Multiplication of a tempered distribution by a temperate multiplier is
mathlib's `smulLeftCLM`; naming it `localize` records what it is used for.
-/

section Localize

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

/-- The cut-off state: the state multiplied by a bump.  Everything the residual
knew on the bump's window is retained; everything outside it is discarded. -/
noncomputable def localize (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    𝓢'(Point, Value) :=
  smulLeftCLM Value bump.weight state

theorem localize_eq (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    localize bump state = smulLeftCLM Value bump.weight state := rfl

theorem localize_add (bump : Bump Point) (first second : 𝓢'(Point, Value)) :
    localize bump (first + second) = localize bump first + localize bump second :=
  map_add _ _ _

/-- Localization by a bump is subtractive: it is the application of a
continuous linear map. -/
theorem localize_sub (bump : Bump Point) (first second : 𝓢'(Point, Value)) :
    localize bump (first - second) = localize bump first - localize bump second :=
  map_sub _ _ _

/-- Localization by a bump commutes with negation. -/
theorem localize_neg (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    localize bump (-state) = -localize bump state :=
  map_neg _ _

theorem localize_sum {Index : Type uIndex} [Fintype Index] (bump : Bump Point)
    (family : Index → 𝓢'(Point, Value)) :
    localize bump (∑ index, family index) = ∑ index, localize bump (family index) :=
  map_sum _ _ _

end Localize

/-! ## The Leibniz rule, and the elliptic commutator

The commutator identity is the algebraic heart of the argument.  It is proved
first for Schwartz test functions — where it is the ordinary product rule —
and then transposed to tempered distributions, so that the *state* is never
assumed to be a function.  That matters: a residual arriving at grade `s` is
genuinely only a distribution, and an identity stated for smooth states would
be unusable at the first step of the bootstrap.
-/

section Leibniz

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

/-- **The Leibniz rule on test functions.**  Multiplying by a bump and
differentiating along a direction commute up to the term in which the
derivative falls on the bump. -/
theorem lineDerivOp_smulLeftCLM_schwartz (direction : Point) (bump : Bump Point)
    (test : 𝓢(Point, ℂ)) :
    ∂_{direction} (SchwartzMap.smulLeftCLM ℂ bump.weight test) =
      SchwartzMap.smulLeftCLM ℂ bump.weight (∂_{direction} test) +
        SchwartzMap.smulLeftCLM ℂ (bump.deriv direction).weight test := by
  have temperate := bump.hasTemperateGrowth
  have temperate_deriv :
      (directionalDeriv direction bump.weight).HasTemperateGrowth :=
    (bump.deriv direction).hasTemperateGrowth
  ext place
  have bump_differentiable : DifferentiableAt ℝ bump.weight place :=
    (bump.smooth.differentiable (by simp)).differentiableAt
  have test_differentiable : DifferentiableAt ℝ (⇑test) place :=
    test.differentiableAt
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply temperate]
  rw [fderiv_fun_smul bump_differentiable test_differentiable]
  simp [SchwartzMap.smulLeftCLM_apply_apply temperate,
    SchwartzMap.smulLeftCLM_apply_apply temperate_deriv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, directionalDeriv, smul_eq_mul]

/-- **The Leibniz rule on tempered distributions.**  Transposing the rule for
test functions: differentiating a cut-off state produces the cut-off
derivative plus the state multiplied by the derivative of the bump.

The second term is the whole of the first-order commutator, and it already
carries a derivative of the bump — the feature that later makes the commutator
vanish on the inner window. -/
theorem lineDerivOp_localize (direction : Point) (bump : Bump Point)
    (state : 𝓢'(Point, Value)) :
    ∂_{direction} (localize bump state) =
      localize bump (∂_{direction} state) +
        localize (bump.deriv direction) state := by
  ext test
  simp only [localize, TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply]
  rw [lineDerivOp_smulLeftCLM_schwartz direction bump test]
  simp [map_add, map_neg]

variable {Index : Type uIndex} [Fintype Index]

/-- The elliptic commutator `[Δ, χ]`, applied to a state.

Every summand carries a derivative of the bump, and the state is
differentiated **at most once**.  Both features are indispensable: the first
makes the commutator vanish on the inner window, the second makes the
bootstrap gain a grade rather than merely return what it was given. -/
noncomputable def ellipticCommutator (basis : OrthonormalBasis Index ℝ Point)
    (bump : Bump Point) (state : 𝓢'(Point, Value)) : 𝓢'(Point, Value) :=
  (2 : ℂ) • (∑ index, localize (bump.deriv (basis index))
      (∂_{basis index} state)) +
    localize (bump.laplacian basis) state

variable [FiniteDimensional ℝ Point]

/-- **The elliptic commutator identity.**
`Δ (χ u) = χ (Δ u) + 2 ∑ᵢ (∂ᵢ χ)(∂ᵢ u) + (Δ χ) u`.

The factor `2` appears because the first-order Leibniz rule is applied to both
summands it produced at the previous step, exactly as in the heat-type
commutator of `PDE/HeatSmoothing.lean`; here the identity is distributional,
so no smoothness of the state is assumed. -/
theorem laplacian_localize (basis : OrthonormalBasis Index ℝ Point)
    (bump : Bump Point) (state : 𝓢'(Point, Value)) :
    Δ (localize bump state) =
      localize bump (Δ state) + ellipticCommutator basis bump state := by
  have step : ∀ index : Index,
      ∂_{basis index} (∂_{basis index} (localize bump state)) =
        localize bump (∂_{basis index} (∂_{basis index} state)) +
          ((2 : ℂ) • localize (bump.deriv (basis index)) (∂_{basis index} state) +
            localize ((bump.deriv (basis index)).deriv (basis index)) state) := by
    intro index
    rw [lineDerivOp_localize, LineDerivAdd.lineDerivOp_add, lineDerivOp_localize,
      lineDerivOp_localize, two_smul]
    abel
  have collapse : ∑ index : Index,
      localize ((bump.deriv (basis index)).deriv (basis index)) state =
        localize (bump.laplacian basis) state := by
    have temperate : ∀ index ∈ (Finset.univ : Finset Index),
        (((bump.deriv (basis index)).deriv (basis index)).weight).HasTemperateGrowth :=
      fun index _ => ((bump.deriv (basis index)).deriv (basis index)).hasTemperateGrowth
    simp only [localize, Bump.laplacian_weight]
    rw [TemperedDistribution.smulLeftCLM_sum temperate]
    simp
  rw [TemperedDistribution.laplacian_eq_sum basis (localize bump state),
    TemperedDistribution.laplacian_eq_sum basis state, ellipticCommutator,
    localize_sum]
  simp only [step]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, collapse]

end Leibniz

/-! ## The commutator vanishes where the bump is locally one

This is the geometric half.  A tempered distribution "vanishes on a region"
when it annihilates every test function supported there; the commutator does,
because each of its summands is a localization by a multiplier that is
identically zero on the region.
-/

section Vanishing

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

/-- A tempered distribution vanishes on a region when it annihilates every
test function whose support lies in the region.  This is the distributional
reading of "nothing outside the outer window enters here". -/
def VanishesOn (region : Set Point) (state : 𝓢'(Point, Value)) : Prop :=
  ∀ test : 𝓢(Point, ℂ), tsupport (⇑test) ⊆ region → state test = 0

/-- Multiplying a test function by a multiplier that vanishes on the test
function's support annihilates it outright. -/
theorem smulLeftCLM_schwartz_eq_zero {bump : Bump Point} {region : Set Point}
    (vanishing : ∀ place ∈ region, bump.weight place = 0)
    (test : 𝓢(Point, ℂ)) (supported : tsupport (⇑test) ⊆ region) :
    SchwartzMap.smulLeftCLM ℂ bump.weight test = 0 := by
  have temperate := bump.hasTemperateGrowth
  ext place
  by_cases mem : place ∈ tsupport (⇑test)
  · simp [SchwartzMap.smulLeftCLM_apply_apply temperate,
      vanishing place (supported mem)]
  · simp [SchwartzMap.smulLeftCLM_apply_apply temperate,
      image_eq_zero_of_notMem_tsupport mem]

/-- **The support fact.**  A localization by a multiplier that vanishes on a
region vanishes on that region, whatever the state is. -/
theorem localize_vanishesOn {bump : Bump Point} {region : Set Point}
    (vanishing : ∀ place ∈ region, bump.weight place = 0)
    (state : 𝓢'(Point, Value)) :
    VanishesOn region (localize bump state) := by
  intro test supported
  have annihilated : SchwartzMap.smulLeftCLM ℂ bump.weight test = 0 :=
    smulLeftCLM_schwartz_eq_zero vanishing test supported
  simp [localize, annihilated]

theorem VanishesOn.add {region : Set Point} {first second : 𝓢'(Point, Value)}
    (first_vanishes : VanishesOn region first)
    (second_vanishes : VanishesOn region second) :
    VanishesOn region (first + second) := by
  intro test supported
  simp [first_vanishes test supported, second_vanishes test supported]

theorem VanishesOn.smul {region : Set Point} {state : 𝓢'(Point, Value)}
    (scalar : ℂ) (vanishes : VanishesOn region state) :
    VanishesOn region (scalar • state) := by
  intro test supported
  simp [vanishes test supported]

theorem VanishesOn.sum {Index : Type uIndex} [Fintype Index] {region : Set Point}
    {family : Index → 𝓢'(Point, Value)}
    (vanishes : ∀ index, VanishesOn region (family index)) :
    VanishesOn region (∑ index, family index) := by
  intro test supported
  simp [fun index => vanishes index test supported]

/-! ### The framework's bump cutoff

`Hypostructure.PDE.Localization.cutoff` is one on the inner window and
supported in the outer one.  Complexifying it gives a `Bump`, and its
derivatives vanish on the *open* inner window, because there the cutoff is
locally — not merely pointwise — constant.
-/

/-- A locally constant multiplier has vanishing directional derivative.  This
is the complex-valued restatement of
`HeatSmoothing.directionalDeriv_eq_zero_of_eventuallyEq_const`, whose proof it
copies verbatim; the original is stated for real multipliers only. -/
theorem directionalDeriv_eq_zero_of_eventuallyEq_const (direction : Point)
    {weight : Point → ℂ} {place : Point} {value : ℂ}
    (locally_constant : weight =ᶠ[nhds place] fun _ => value) :
    directionalDeriv direction weight place = 0 := by
  simp [directionalDeriv, locally_constant.fderiv_eq]

/-- Local constancy propagates to a neighbourhood, so the *second* directional
derivative vanishes too.  Complex-valued restatement of
`HeatSmoothing.directionalDeriv_two_eq_zero_of_eventuallyEq_const`. -/
theorem directionalDeriv_two_eq_zero_of_eventuallyEq_const
    (first second : Point) {weight : Point → ℂ} {place : Point} {value : ℂ}
    (locally_constant : weight =ᶠ[nhds place] fun _ => value) :
    directionalDeriv second (directionalDeriv first weight) place = 0 :=
  directionalDeriv_eq_zero_of_eventuallyEq_const second
    (locally_constant.eventuallyEq_nhds.mono fun _ nearby =>
      directionalDeriv_eq_zero_of_eventuallyEq_const first nearby)

section FrameworkCutoff

variable [HasContDiffBump Point] [FiniteDimensional ℝ Point]

/-- The framework's bump cutoff, complexified so that it multiplies tempered
distributions. -/
noncomputable def cutoffBumpMultiplier (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) : Bump Point where
  weight := fun place =>
    (Localization.cutoff center inner_pos nested place : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp
    (Hypostructure.PDE.HeatSmoothing.cutoff_contDiff_infty center inner_pos nested)
  compactSupport :=
    HasCompactSupport.comp_left
      (g := Complex.ofReal)
      (Localization.cutoff_hasCompactSupport center inner_pos nested)
      Complex.ofReal_zero

/-- The complexified cutoff is *locally* one on the open inner window — the
hypothesis the support fact needs, since the commutator sees derivatives. -/
theorem cutoffBumpMultiplier_eventuallyEq_one (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {place : Point}
    (mem : place ∈ ball center inner) :
    (cutoffBumpMultiplier center inner_pos nested).weight =ᶠ[nhds place]
      fun _ => (1 : ℂ) :=
  (Hypostructure.PDE.HeatSmoothing.cutoff_eventuallyEq_one center inner_pos
    nested mem).fun_comp Complex.ofReal

variable {Index : Type uIndex} [Fintype Index]

/-- **The commutator is annihilated on the inner window.**  Every summand
carries a derivative of the cutoff, and the cutoff is locally one there.

This is the precise sense in which the localization costs nothing where it
matters: the gain obtained for the cut-off state is a gain for the state
itself on the inner window. -/
theorem ellipticCommutator_vanishesOn_ball
    (basis : OrthonormalBasis Index ℝ Point) (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer)
    (state : 𝓢'(Point, Value)) :
    VanishesOn (ball center inner)
      (ellipticCommutator basis (cutoffBumpMultiplier center inner_pos nested)
        state) := by
  refine VanishesOn.add (VanishesOn.smul _ (VanishesOn.sum fun index => ?_)) ?_
  · refine localize_vanishesOn (fun place mem => ?_) _
    exact directionalDeriv_eq_zero_of_eventuallyEq_const _
      (cutoffBumpMultiplier_eventuallyEq_one center inner_pos nested mem)
  · refine localize_vanishesOn (fun place mem => ?_) _
    refine Finset.sum_eq_zero fun index _ => ?_
    exact directionalDeriv_two_eq_zero_of_eventuallyEq_const _ _
      (cutoffBumpMultiplier_eventuallyEq_one center inner_pos nested mem)

end FrameworkCutoff

end Vanishing

/-! ## The local Sobolev scale, and the one-step gain -/

section Gain

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]

/-- **`H^grade` on a window.**  A state sits at `grade` on `region` when every
bump supported in `region` carries it into the global Sobolev space of that
grade.

Quantifying over all bumps is what makes the predicate usable: the elliptic
commutator produces new multipliers (`∂ᵢ χ`, `Δ χ`), and each of them is again
an admissible bump for the *same* region, so no multiplication theorem for
`H^s` is ever needed. -/
def SobolevOn (region : Set Point) (grade : ℝ) (state : 𝓢'(Point, Value)) :
    Prop :=
  ∀ bump : Bump Point, tsupport bump.weight ⊆ region →
    MemSobolev grade 2 (localize bump state)

/-- **Cutting an `L²` state off keeps it `L²`.**  A bump is continuous with
compact support, hence bounded, and `L^∞ · L² ⊆ L²`; the passage from the
product of `Lp` functions to the multiplied distribution is mathlib's
`Lp.toTemperedDistribution_smul_eq`. -/
theorem memSobolev_zero_localize (bump : Bump Point) {state : 𝓢'(Point, Value)}
    (square : MemSobolev 0 2 state) :
    MemSobolev 0 2 (localize bump state) := by
  obtain ⟨representative, agrees⟩ := memSobolev_zero_iff.mp square
  have bounded : MemLp bump.weight ∞ (volume : Measure Point) :=
    bump.smooth.continuous.memLp_top_of_hasCompactSupport bump.compactSupport _
  refine memSobolev_zero_iff.mpr ⟨(bounded.toLp _) • representative, ?_⟩
  rw [localize_eq, agrees,
    MeasureTheory.Lp.toTemperedDistribution_smul_eq bump.hasTemperateGrowth
      bounded representative]

/-- **A state that is globally `L²` sits at grade zero on every region.**  This
is what makes the local `L²` bound of a placement enough to start the interior
bootstrap: no decay of the Fourier transform, and so no Paley--Wiener, is
needed. -/
theorem sobolevOn_of_memSobolev_zero {region : Set Point} {state : 𝓢'(Point, Value)}
    (square : MemSobolev 0 2 state) : SobolevOn region 0 state :=
  fun bump _ => memSobolev_zero_localize bump square

/-- A window inherits every grade held by a larger one. -/
theorem SobolevOn.mono_region {smaller larger : Set Point} {grade : ℝ}
    {state : 𝓢'(Point, Value)} (subset : smaller ⊆ larger)
    (held : SobolevOn larger grade state) : SobolevOn smaller grade state :=
  fun bump supported => held bump (supported.trans subset)

/-- Grades are inherited downwards, since Sobolev spaces are nested. -/
theorem SobolevOn.mono_grade {region : Set Point} {lower grade : ℝ}
    {state : 𝓢'(Point, Value)} (le : lower ≤ grade)
    (held : SobolevOn region grade state) : SobolevOn region lower state :=
  fun bump supported => (held bump supported).mono le

/-- **A grade held by two states on a window is held by their sum.**

Localizing is linear and the Sobolev class of a fixed grade is a subgroup, so
the sum of the two cut-off states is the cut-off sum and stays in the class.
This is what lets a consumer split a state into pieces, prove the grade for each
and recombine, without ever leaving the local predicate. -/
theorem SobolevOn.add {region : Set Point} {grade : ℝ}
    {first second : 𝓢'(Point, Value)} (first_held : SobolevOn region grade first)
    (second_held : SobolevOn region grade second) :
    SobolevOn region grade (first + second) := fun bump supported => by
  rw [localize_add]
  exact (first_held bump supported).add (second_held bump supported)

/-- A grade held by two states on a window is held by their difference, for the
same reason as `SobolevOn.add`. -/
theorem SobolevOn.sub {region : Set Point} {grade : ℝ}
    {first second : 𝓢'(Point, Value)} (first_held : SobolevOn region grade first)
    (second_held : SobolevOn region grade second) :
    SobolevOn region grade (first - second) := fun bump supported => by
  rw [localize_sub]
  exact (first_held bump supported).sub (second_held bump supported)

/-- A grade held by a state on a window is held by its negative. -/
theorem SobolevOn.neg {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (held : SobolevOn region grade state) : SobolevOn region grade (-state) :=
  fun bump supported => by
    rw [localize_neg]
    exact (held bump supported).neg

/-- Differentiating costs exactly one grade, locally as well as globally.  The
proof is the Leibniz rule: the derivative of the cut-off state is the cut-off
derivative plus a strictly lower-order error, and the error is a localization
by another admissible bump. -/
theorem SobolevOn.lineDerivOp {region : Set Point} {grade : ℝ}
    {state : 𝓢'(Point, Value)} (held : SobolevOn region grade state)
    (direction : Point) :
    SobolevOn region (grade - 1) (∂_{direction} state) := by
  intro bump supported
  have identity : localize bump (∂_{direction} state) =
      ∂_{direction} (localize bump state) - localize (bump.deriv direction) state := by
    rw [lineDerivOp_localize]
    abel
  rw [identity]
  refine MemSobolev.sub (held bump supported).lineDerivOp ?_
  refine (held (bump.deriv direction) ?_).mono (by linarith)
  exact (bump.tsupport_deriv_subset direction).trans supported

variable {Index : Type uIndex} [Fintype Index]

/-- **The one-step gain.**  If a state and its Laplacian both sit at `grade` on
a window, the state sits at `grade + 1` there.

The bookkeeping is the whole point.  Feeding the whole-space bootstrap
(`memSobolev_add_two_of_laplacian`, which gains *two*) at the reduced grade
`grade - 1` returns `grade + 1`: the commutator term `2 ∑ᵢ (∂ᵢ χ)(∂ᵢ u)`
differentiates the state once and therefore only lies at `grade - 1`, which is
the honest cost of localizing.  One grade per step, and one grade per step is
all the iteration needs. -/
theorem sobolevOn_add_one (basis : OrthonormalBasis Index ℝ Point)
    {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_held : SobolevOn region grade (Δ state)) :
    SobolevOn region (grade + 1) state := by
  intro bump supported
  have commutator_member :
      MemSobolev (grade - 1) 2 (ellipticCommutator basis bump state) := by
    refine MemSobolev.add (MemSobolev.smul _ ?_) ?_
    · refine Bessel.mem_sobolev.mp
        (AddSubgroup.sum_mem _ fun index _ => Bessel.mem_sobolev.mpr ?_)
      refine (state_held.lineDerivOp (basis index)) (bump.deriv (basis index)) ?_
      exact (bump.tsupport_deriv_subset (basis index)).trans supported
    · refine (state_held (bump.laplacian basis) ?_).mono (by linarith)
      exact (bump.tsupport_laplacian_subset basis).trans supported
  have laplacian_member :
      MemSobolev (grade - 1) 2 (Δ (localize bump state)) := by
    rw [laplacian_localize basis]
    exact MemSobolev.add ((source_held bump supported).mono (by linarith))
      commutator_member
  have state_member : MemSobolev (grade - 1) 2 (localize bump state) :=
    (state_held bump supported).mono (by linarith)
  have gained :=
    Bessel.memSobolev_add_two_of_laplacian state_member laplacian_member
  rwa [show grade - 1 + 2 = grade + 1 by ring] at gained

end Gain

/-! ## Iteration, and the payoff

Once the gain is available the iteration is a bare induction: each step feeds
the grade just obtained back into the gain, and the Laplacian — assumed smooth
on the window — supplies whatever grade the next step asks for.

Two forms of the iteration are recorded.  The direct one needs no shrinking of
the window at all, because `SobolevOn` already quantifies over every bump
supported in it.  The second runs the same induction over the shrinking chain
of windows of `PDE/HeatSmoothing.lean`, which is the geometry the paper
argument uses and the one a caller with only nested balls in hand will have.
-/

section Payoff

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index]

/-- **Smooth on a window**: at every grade there.  This is the `H^∞_loc`
reading of smoothness, and it is what an elliptic bootstrap can deliver. -/
def SmoothOn (region : Set Point) (state : 𝓢'(Point, Value)) : Prop :=
  ∀ grade : ℝ, SobolevOn region grade state

/-! ### Agreement on a window

Both predicates read a state *only* through bumps supported in the region, so
two states that are indistinguishable to those bumps are indistinguishable to
the predicates.  This is what makes an equation that holds only on a window
usable: the cut-off state and the state it agrees with there have the same local
regularity, and nothing outside the window is ever consulted.

The hypothesis is deliberately the localized one --- equality of `localize bump`
for bumps supported in the region --- rather than equality of the states, which
would be a global statement and is never available for a residual. -/
theorem SobolevOn.congr_localize {region : Set Point} {grade : ℝ}
    {first second : 𝓢'(Point, Value)}
    (agree : ∀ bump : Bump Point, tsupport bump.weight ⊆ region →
      localize bump first = localize bump second)
    (held : SobolevOn region grade second) : SobolevOn region grade first :=
  fun bump supported => (agree bump supported) ▸ held bump supported

theorem SmoothOn.congr_localize {region : Set Point}
    {first second : 𝓢'(Point, Value)}
    (agree : ∀ bump : Bump Point, tsupport bump.weight ⊆ region →
      localize bump first = localize bump second)
    (smooth : SmoothOn region second) : SmoothOn region first :=
  fun grade => SobolevOn.congr_localize agree (smooth grade)

/-- The form the transported equation actually takes: the two states differ by
something the region's bumps annihilate. -/
theorem SmoothOn.congr_sub {region : Set Point} {first second : 𝓢'(Point, Value)}
    (agree : ∀ bump : Bump Point, tsupport bump.weight ⊆ region →
      localize bump (first - second) = 0)
    (smooth : SmoothOn region second) : SmoothOn region first :=
  SmoothOn.congr_localize
    (fun bump supported => by
      have difference := agree bump supported
      rw [localize_sub] at difference
      exact sub_eq_zero.mp difference)
    smooth

theorem SmoothOn.mono_region {smaller larger : Set Point}
    {state : 𝓢'(Point, Value)} (subset : smaller ⊆ larger)
    (smooth : SmoothOn larger state) : SmoothOn smaller state :=
  fun grade => (smooth grade).mono_region subset

/-- **Smoothness on a window is additive.**  Smoothness is every grade at once
and each grade is additive, so the sum is smooth grade by grade. -/
theorem SmoothOn.add {region : Set Point} {first second : 𝓢'(Point, Value)}
    (first_smooth : SmoothOn region first) (second_smooth : SmoothOn region second) :
    SmoothOn region (first + second) :=
  fun grade => SobolevOn.add (first_smooth grade) (second_smooth grade)

/-- Smoothness on a window is subtractive. -/
theorem SmoothOn.sub {region : Set Point} {first second : 𝓢'(Point, Value)}
    (first_smooth : SmoothOn region first) (second_smooth : SmoothOn region second) :
    SmoothOn region (first - second) :=
  fun grade => SobolevOn.sub (first_smooth grade) (second_smooth grade)

/-- Smoothness on a window survives negation. -/
theorem SmoothOn.neg {region : Set Point} {state : 𝓢'(Point, Value)}
    (smooth : SmoothOn region state) : SmoothOn region (-state) :=
  fun grade => SobolevOn.neg (smooth grade)

/-- **Smoothness on a window survives differentiation.**  A first-order operator
costs one grade — `SobolevOn.lineDerivOp` — and smoothness is *every* grade, so
the cost is paid out of the grade one higher and is invisible.  This is what
makes a directional derivative harmless once the direction in question is part
of the ambient `Point`, and it is the fact a consumer of the local theory needs
in order to differentiate a smooth-on-a-window state without doing grade
bookkeeping at the call site. -/
theorem SmoothOn.lineDerivOp {region : Set Point} {state : 𝓢'(Point, Value)}
    (smooth : SmoothOn region state) (direction : Point) :
    SmoothOn region (∂_{direction} state) := fun grade => by
  have gained := (smooth (grade + 1)).lineDerivOp direction
  rwa [add_sub_cancel_right] at gained

/-- **The iteration.**  A state at `grade` on a window, whose Laplacian is
smooth there, gains every whole number of grades. -/
theorem sobolevOn_add_natCast (basis : OrthonormalBasis Index ℝ Point)
    {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source_smooth : SmoothOn region (Δ state)) :
    ∀ step : ℕ, SobolevOn region (grade + step) state := by
  intro step
  induction step with
  | zero => simpa using state_held
  | succ previous gained =>
      have advanced := sobolevOn_add_one basis gained
        (source_smooth (grade + previous))
      have rewrite : grade + (previous : ℝ) + 1 = grade + ((previous + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rwa [rewrite] at advanced

/-- **The payoff.**  A state whose Laplacian is smooth on a window is itself
smooth on that window, provided it sits at *some* grade there to start from.

The starting grade is not a restriction: it is what the residual already knows
about itself, and any local `L²` bound supplies grade `0`.

This is the statement a div–curl step consumes.  There one has
`-Δ v = curl (curl v)` with the right-hand side smooth on the window, so the
hypothesis `source` is discharged by the curl computation and the conclusion
is smoothness of `v`. -/
theorem smoothOn_of_laplacian_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    {region : Set Point} {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn region grade state)
    (source : SmoothOn region (Δ state)) : SmoothOn region state := by
  intro target
  obtain ⟨step, step_ge⟩ := exists_nat_ge (target - grade)
  refine SobolevOn.mono_grade ?_
    (sobolevOn_add_natCast basis state_held source step)
  linarith

/-- **The payoff on nested windows.**  A state whose Laplacian is smooth on the
outer window is smooth on every window contained in it — in particular on the
inner window of a nested pair of balls, which is the geometry a residual
actually carries. -/
theorem smoothOn_ball_of_laplacian_smoothOn (basis : OrthonormalBasis Index ℝ Point)
    (center : Point) {inner outer : ℝ} (nested : inner ≤ outer) {grade : ℝ}
    {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outer) grade state)
    (source : SmoothOn (ball center outer) (Δ state)) :
    SmoothOn (ball center inner) state :=
  (smoothOn_of_laplacian_smoothOn basis state_held source).mono_region
    (ball_subset_ball nested)

/-! ### The same iteration, run over a shrinking chain of windows

`PDE/HeatSmoothing.lean` builds a concrete chain of balls decreasing strictly
from an outer radius towards an inner one, and an induction skeleton that
turns a one-step gain along such a chain into every grade on the inner window.
Instantiating the skeleton at the gain proved above is the shape the paper
argument has, and it shows the gain composes along genuinely shrinking
windows, not only along a fixed one.
-/

/-- Every radius of the chain of `PDE/HeatSmoothing.lean` stays inside the outer
one, so the smoothness of the source assumed on the outer window is available
at every stage of the chain.  The chain's own lemmas record that the radii
decrease and stay above the inner radius; that they never exceed the outer one
is the remaining comparison, and it is elementary. -/
theorem chainRadius_le_outer {innerRadius outerRadius : ℝ}
    (nested : innerRadius < outerRadius) (step : ℕ) :
    Hypostructure.PDE.HeatSmoothing.chainRadius innerRadius outerRadius step ≤
      outerRadius := by
  have positive : (0 : ℝ) < (step : ℝ) + 1 := by positivity
  have nonneg : (0 : ℝ) ≤ (step : ℝ) := Nat.cast_nonneg step
  have gap : (0 : ℝ) ≤ outerRadius - innerRadius := by linarith
  have bound : (outerRadius - innerRadius) / ((step : ℝ) + 1) ≤
      outerRadius - innerRadius := by
    rw [div_le_iff₀ positive]
    nlinarith
  simp only [Hypostructure.PDE.HeatSmoothing.chainRadius]
  linarith

/-- **The bootstrap on the framework's chain of shrinking windows.**  The
one-step gain, run along `HeatSmoothing.chainRadius`, delivers every whole
grade on the closed inner ball. -/
theorem sobolevOn_chain (basis : OrthonormalBasis Index ℝ Point) (center : Point)
    {innerRadius outerRadius : ℝ} (nested : innerRadius < outerRadius)
    {grade : ℝ} {state : 𝓢'(Point, Value)}
    (state_held : SobolevOn (ball center outerRadius) grade state)
    (source_smooth : SmoothOn (ball center outerRadius) (Δ state)) :
    ∀ step : ℕ, SobolevOn (closedBall center innerRadius) (grade + step) state := by
  refine Hypostructure.PDE.HeatSmoothing.regular_closedBall_of_chain center nested
    (regular := fun step region => SobolevOn region (grade + step) state)
    (fun _ _ _ subset held => held.mono_region subset) (by simpa using state_held) ?_
  intro step held
  have source_here :
      SobolevOn (ball center
        (Hypostructure.PDE.HeatSmoothing.chainRadius innerRadius outerRadius step))
        (grade + step) (Δ state) :=
    (source_smooth (grade + step)).mono_region
      (ball_subset_ball (chainRadius_le_outer nested step))
  have advanced := sobolevOn_add_one basis held source_here
  have shrunk := advanced.mono_region (ball_subset_ball
    (Hypostructure.PDE.HeatSmoothing.chainRadius_succ_lt nested step).le)
  have rewrite : grade + (step : ℝ) + 1 = grade + ((step + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rwa [rewrite] at shrunk

end Payoff

end Hypostructure.PDE.Solution.InteriorRegularity
