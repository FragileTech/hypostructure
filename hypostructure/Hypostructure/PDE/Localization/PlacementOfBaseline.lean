import Hypostructure.PDE.Localization.Tempered
import Hypostructure.PDE.Model.Bessel

/-!
# Placing a locally represented baseline at the model's grade

`PDE/Model/Bessel.lean` ends at `Bessel.Object.ofSquareIntegrableResidual`: a
distribution on a window, a window, an `L²` element of the whole space, and the
*equation* saying that the framework's cutoff carries the first to the last.
That equation is the only thing left over, and until now an application had to
hand it over as data --- which is exactly the wrong place for it, because it is
not a fact about any one equation: it is the generic statement

> a distribution that is represented, **on its own window**, by a locally square
> integrable function becomes, after the window's own cutoff, a genuine `L²`
> tempered state.

Everything that statement needs is already proved:

* `Localization.memLp_cutoffSmul` --- a source that is `L^p` on its own window is
  globally `L^p` once cut off (`Localization/Tempered.lean`);
* `Localization.cutoffSmul_eq_zero` --- the cut-off source vanishes off the outer
  ball, which is what turns the global `L²` bound into a global `L¹` one on a
  ball of finite measure;
* `Localization.temperedOfLocal` and `temperedOfLocal_apply` --- the cutoff
  bridge and its value on a Schwartz function (`Localization/TemperedBridge.lean`);
* mathlib's `MeasureTheory.Lp.toTemperedDistribution_apply` --- the value of the
  `L²` side on the same Schwartz function.

The junction between the two sides is `temperedOfLocal_eq_toTemperedDistribution`
below: both are integrals against the same cut-off weight, and the only
computation is the complexification `φ = Re φ + i · Im φ` that the bridge itself
performs on the test function.

What a caller supplies is therefore what a caller actually knows --- a window, a
distribution on it, a function representing that distribution, and the local `L²`
bound on the function.  `SquareIntegrablePlacement.agrees` is then a *theorem of
the construction*, not a field an application fills, and
`SquareIntegrablePlacement.object` hands the result to the graded model with no
further provision.

Nothing here names an equation, a dimension or a problem.
-/

namespace Hypostructure.PDE.Localization

open MeasureTheory Metric TopologicalSpace
open scoped Distributions SchwartzMap ENNReal

variable {Point : Type} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [HasContDiffBump Point]
  {Value : Type} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]

/-! ## The cut-off weight of a window

A `Bessel.Window` is a centre and two radii, which is exactly what
`Localization/Cutoff.lean` consumes, so the window's own cutoff is the one
`cutoffSmul` uses.  These three lemmas are `Localization/Tempered.lean`'s
statements read at that cutoff; no new analysis appears.
-/

/-- A weight, cut off by the window's own smooth bump.  This is `cutoffSmul` with
the window supplying the centre and the radii. -/
noncomputable def windowSmul (window : Bessel.Window Point) (weight : Point → Value) :
    Point → Value :=
  cutoffSmul window.centre window.innerRadius_pos window.innerRadius_lt_outerRadius weight

omit [MeasurableSpace Point] [BorelSpace Point] [CompleteSpace Value] in
theorem windowSmul_apply (window : Bessel.Window Point) (weight : Point → Value)
    (place : Point) :
    windowSmul window weight place =
      (window.cutoff : Point → ℝ) place • weight place :=
  rfl

omit [CompleteSpace Value] in
/-- Cutting off preserves measurability: the cutoff is smooth, hence continuous. -/
theorem aestronglyMeasurable_windowSmul (window : Bessel.Window Point)
    {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point)) :
    AEStronglyMeasurable (windowSmul window weight) (volume : Measure Point) :=
  (window.cutoff.contDiff.continuous.aestronglyMeasurable).smul measurable

omit [CompleteSpace Value] in
/-- **The local `L²` bound becomes a global one.**  This is
`Localization.memLp_cutoffSmul` at the window's own cutoff. -/
theorem memLp_windowSmul (window : Bessel.Window Point) {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius))) :
    MemLp (windowSmul window weight) 2 (volume : Measure Point) :=
  memLp_cutoffSmul window.centre window.innerRadius_pos
    window.innerRadius_lt_outerRadius windowed
    (aestronglyMeasurable_windowSmul window measurable)

omit [CompleteSpace Value] in
/-- **The cut-off weight is integrable.**  It is square integrable and it vanishes
off a ball of finite measure (`cutoffSmul_eq_zero`), so the exponent may be
lowered.  This is what lets a Schwartz factor be paired against it. -/
theorem integrable_windowSmul (window : Bessel.Window Point) {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius))) :
    Integrable (windowSmul window weight) (volume : Measure Point) := by
  refine memLp_one_iff_integrable.mp ?_
  refine (memLp_windowSmul window measurable windowed).mono_exponent_of_measure_support_ne_top
    (s := ball window.centre window.outerRadius) (fun place notMem => ?_)
    (measure_ball_lt_top).ne one_le_two
  exact cutoffSmul_eq_zero window.centre window.innerRadius_pos
    window.innerRadius_lt_outerRadius weight notMem

/-- The `L²` element the cut-off weight determines.  This is the representative
`Bessel.Object.ofSquareIntegrableResidual` asks for, and it is *constructed*, not
supplied. -/
noncomputable def windowRepresentative (window : Bessel.Window Point)
    {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius))) :
    Lp Value 2 (volume : Measure Point) :=
  (memLp_windowSmul window measurable windowed).toLp _

omit [CompleteSpace Value] in
theorem coeFn_windowRepresentative (window : Bessel.Window Point)
    {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius))) :
    (windowRepresentative window measurable windowed : Point → Value) =ᵐ[volume]
      windowSmul window weight :=
  MemLp.coeFn_toLp _

/-! ## The junction

The bridge evaluates a local object on the cut-off real and imaginary parts of a
Schwartz function; the `L²` side integrates the same Schwartz function against
the cut-off weight.  If the local object *is* integration against the weight,
the two sides are the same number, and the only step is the pointwise splitting
`φ = Re φ + i · Im φ` --- the same splitting the bridge performs.
-/

omit [CompleteSpace Value] in
/-- A real Schwartz factor is integrable against the cut-off weight: the weight
is `L¹` and the Schwartz function is bounded by its own zeroth seminorm. -/
theorem integrable_schwartzSmul_windowSmul (window : Bessel.Window Point)
    {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius)))
    (profile : 𝓢(Point, ℝ)) :
    Integrable (fun place => profile place • windowSmul window weight place)
      (volume : Measure Point) := by
  have bounded := (integrable_windowSmul window measurable windowed).bdd_smul
    (φ := (profile : Point → ℝ)) (SchwartzMap.seminorm ℝ 0 0 profile)
    profile.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun place => SchwartzMap.norm_le_seminorm ℝ profile place)
  exact bounded

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [CompleteSpace Value] in
/-- The complexification the bridge performs, read on the integrand:
`φ · g = Re φ · g + i · (Im φ · g)`. -/
theorem schwartzSmul_split (window : Bessel.Window Point) (weight : Point → Value)
    (test : 𝓢(Point, ℂ)) (place : Point) :
    test place • windowSmul window weight place =
      (schwartzRealPart test) place • windowSmul window weight place +
        Complex.I •
          ((schwartzImagPart test) place • windowSmul window weight place) := by
  rw [schwartzRealPart_apply, schwartzImagPart_apply]
  conv_lhs => rw [← Complex.re_add_im (test place)]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, smul_comm]

/--
**The provision is a theorem.**

A distribution on a window that is represented there by a weight which is square
integrable on the window becomes, after the window's own cutoff, exactly the
tempered distribution of the `L²` element `windowRepresentative`.

This is the equation `Bessel.Object.ofSquareIntegrableResidual` consumes.  No
application supplies it any more, and nothing about any equation enters: both
sides are integrals against the same cut-off weight, and the only computation is
the splitting the bridge already performs on its test function.
-/
theorem temperedOfLocal_eq_toTemperedDistribution {domain : Opens Point}
    (window : Bessel.Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value)) {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius)))
    (represents : ∀ test : 𝓓(domain, ℝ),
      datum test = ∫ place, test place • weight place ∂(volume : Measure Point)) :
    temperedOfLocal window.cutoff inside datum =
      Lp.toTemperedDistribution (windowRepresentative window measurable windowed) := by
  ext test
  have cutoffPairing : ∀ profile : 𝓢(Point, ℝ),
      datum (cutoffTestCLM window.cutoff inside profile) =
        ∫ place, profile place • windowSmul window weight place
          ∂(volume : Measure Point) := by
    intro profile
    rw [represents]
    refine integral_congr_ae (Filter.Eventually.of_forall fun place => ?_)
    show ((window.cutoff : Point → ℝ) place * profile place) • weight place =
      profile place • windowSmul window weight place
    rw [windowSmul_apply, smul_smul, mul_comm]
  have leftSide :
      temperedOfLocal window.cutoff inside datum test =
        (∫ place, (schwartzRealPart test) place • windowSmul window weight place
          ∂(volume : Measure Point)) +
          Complex.I •
            ∫ place, (schwartzImagPart test) place • windowSmul window weight place
              ∂(volume : Measure Point) := by
    rw [temperedOfLocal_apply, cutoffPairing, cutoffPairing]
  have rightSide :
      Lp.toTemperedDistribution (windowRepresentative window measurable windowed) test =
        ∫ place, test place • windowSmul window weight place
          ∂(volume : Measure Point) := by
    rw [Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_windowRepresentative window measurable windowed] with place value
    rw [value]
  rw [leftSide, rightSide]
  symm
  calc ∫ place, test place • windowSmul window weight place ∂(volume : Measure Point)
      = ∫ place, ((schwartzRealPart test) place • windowSmul window weight place +
            Complex.I • ((schwartzImagPart test) place •
              windowSmul window weight place)) ∂(volume : Measure Point) :=
        integral_congr_ae (Filter.Eventually.of_forall
          (schwartzSmul_split window weight test))
    _ = (∫ place, (schwartzRealPart test) place • windowSmul window weight place
            ∂(volume : Measure Point)) +
          ∫ place, Complex.I • ((schwartzImagPart test) place •
            windowSmul window weight place) ∂(volume : Measure Point) :=
        integral_add (integrable_schwartzSmul_windowSmul window measurable windowed _)
          ((integrable_schwartzSmul_windowSmul window measurable windowed _).smul Complex.I)
    _ = _ := by rw [integral_smul]

/-! ## The placement itself

The structure below is the analytic content of a placement and nothing else: a
window, a distribution on a domain containing the window's support, and the `L²`
identification of its cut-off form.  It carries no lift, no reading of any
particular object, and no equation --- those belong to whatever application owns
the object being placed.
-/

variable (Point Value) in
/--
**A square integrable placement.**

Exactly the arguments of `Bessel.Object.ofSquareIntegrableResidual`, bundled.  It
is problem agnostic: nothing here refers to a field, a pressure, a velocity or a
balance.

The point of bundling is `SquareIntegrablePlacement.ofRepresentative`, which
builds one from data a caller actually has --- and in particular *proves*
`agrees` rather than asking for it.
-/
structure SquareIntegrablePlacement where
  /-- The open set the local reading lives on. -/
  domain : Opens Point
  /-- The local reading itself. -/
  datum : 𝓓'(domain, Value)
  /-- The window of the graded model: a centre and a concentric pair of radii,
  which is what the framework's cutoff consumes. -/
  window : Bessel.Window Point
  /-- The cutoff's compact support sits inside the reading's own domain. -/
  inside : (window.support : Set Point) ⊆ domain
  /-- The `L²` representative of the cut-off reading. -/
  representative : Lp Value 2 (volume : Measure Point)
  /-- The local `L²` bound: a single equation of tempered distributions, not a
  statement about every frequency. -/
  agrees : temperedOfLocal window.cutoff inside datum =
    Lp.toTemperedDistribution representative

/--
**The constructor.**

From a distribution on an open set, a function representing it there, and the
square integrability of that function on the window's outer ball, the placement
is built --- `agrees` included, by
`temperedOfLocal_eq_toTemperedDistribution`.

The hypotheses are the ones a caller can meet without knowing anything about the
framework's cutoff: measurability of the weight, its local `L²` bound, and the
representation identity that says the distribution *is* integration against it.
-/
noncomputable def SquareIntegrablePlacement.ofRepresentative {domain : Opens Point}
    (window : Bessel.Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value)) {weight : Point → Value}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius)))
    (represents : ∀ test : 𝓓(domain, ℝ),
      datum test = ∫ place, test place • weight place ∂(volume : Measure Point)) :
    SquareIntegrablePlacement Point Value where
  domain := domain
  datum := datum
  window := window
  inside := inside
  representative := windowRepresentative window measurable windowed
  agrees :=
    temperedOfLocal_eq_toTemperedDistribution window inside datum measurable windowed
      represents

/-- The graded ambient object of a placement: the framework's own consumer, fed
the placement's own fields.  No membership is assumed and no grade is chosen. -/
noncomputable def SquareIntegrablePlacement.object
    (placement : SquareIntegrablePlacement Point Value) (order : ℕ) :
    Bessel.Object Point Value order :=
  Bessel.Object.ofSquareIntegrableResidual placement.window placement.inside
    placement.datum placement.representative placement.agrees

/-- The state of a placement's object is exactly its cut-off reading. -/
@[simp] theorem SquareIntegrablePlacement.state_object
    (placement : SquareIntegrablePlacement Point Value) (order : ℕ) :
    (placement.object order).state =
      temperedOfLocal placement.window.cutoff placement.inside placement.datum :=
  rfl

/-! ## The placement as a tempered state at a grade

`Object.ofSquareIntegrableResidual` already turns the `L²` representative into
`MemSobolev 0 2` through mathlib's `memSobolev_zero_iff` and then walks down to
the model's negative placement grade.  The two declarations below expose that
same passage without going through the graded object, because a consumer that
wants to run the interior bootstrap needs the *state* and its grade, not the
`Bessel.Object` wrapper.

Neither is new analysis: `memSobolev_zero` is `memSobolev_zero_iff` read at the
placement's own `agrees` field, which is itself a theorem of the construction.
No Paley--Wiener is involved --- the grade comes from the local `L²` bound, not
from a decay property of the Fourier transform.
-/

/-- The tempered state of a placement: its local reading, cut off by the
window's own bump. -/
noncomputable def SquareIntegrablePlacement.state
    (placement : SquareIntegrablePlacement Point Value) : 𝓢'(Point, Value) :=
  temperedOfLocal placement.window.cutoff placement.inside placement.datum

@[simp] theorem SquareIntegrablePlacement.state_eq
    (placement : SquareIntegrablePlacement Point Value) (order : ℕ) :
    (placement.object order).state = placement.state :=
  rfl

/-- **The cut-off reading is an `L²` tempered state**, so it sits at Sobolev
grade zero.  This is the whole content of "a local `L²` bound supplies the
grade". -/
theorem SquareIntegrablePlacement.memSobolev_zero
    (placement : SquareIntegrablePlacement Point Value) :
    TemperedDistribution.MemSobolev 0 2 placement.state :=
  TemperedDistribution.memSobolev_zero_iff.mpr
    ⟨placement.representative, placement.agrees⟩

end Hypostructure.PDE.Localization
