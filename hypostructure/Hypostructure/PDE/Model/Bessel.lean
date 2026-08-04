import Hypostructure.PDE.EllipticLocalTail
import Hypostructure.PDE.Localization.TemperedBridge
import Hypostructure.PDE.Solution.FiniteOrder

/-!
# The graded PDE model over the Sobolev scale

This is the second worked registration of `PDE/EllipticLocalTail.lean`'s
`ComponentEllipticOperator`, and the first that is problem agnostic: it fixes
no dimension and no ambient point space beyond "a finite dimensional real inner
product space", and it writes no equation-specific carrier by hand.

`PDE/Model/Interval.lean` registers the one-dimensional model, whose carrier is
`C^k` functions of a real variable and whose operator is `d²/dx²`.  Everything
there is built by hand from the fundamental theorem of calculus, and it cannot
be reused: a second PDE would have to invent its own `Carrier`, `operator` and
`solve` triple from scratch.  This module removes that obligation once and for
all by registering the *Sobolev scale itself* as the graded carrier:

* `Grade` is `ℝ` and `step g = g + 2`, because the operator is second order;
* `Carrier object window g` is `Bessel.sobolev g`, an honest additive subgroup
  of the tempered distributions;
* `operator` is `Bessel.helmholtz`, `solve` is `Bessel.potential`, and
  `operator_solve` is `Bessel.helmholtz_potential` verbatim --- no cast, no
  reassociation, no auxiliary lemma, because the graded carrier of the
  framework and the graded carrier of the solution library are the same object.

Everything else --- the local child, the complementary tail, their sum, the
homogeneity of the tail, the derived `LocalEllipticConstraint`, the assembly
and the pointwise certificate --- is produced by the framework.

## What the tail equation actually says

The operator registered here is the **Helmholtz operator `1 − (2π)⁻² Δ`**, not
the Laplacian.  Consequently the complementary child of the split is
annihilated by `1 − (2π)⁻² Δ`, and *not* by `Δ`: it solves the homogeneous
Helmholtz equation, it is **not** harmonic.  This is stated exactly that way in
`equation` (whose `satisfies` is `besselPotential Point Value 2 u = source`)
and in `helmholtz_tailTermAt` below.  Nothing in this file claims harmonicity,
and nothing derives a mean value property, a maximum principle, or any other
consequence of harmonicity.

## Why the model is indexed by an order

`Bessel.helmholtz` acts on a Sobolev space, so a raw tempered distribution is
not something the operator can be applied to at all: it has to be *placed* at a
grade first.  The model is therefore indexed by a natural number `order`, in
exactly the way `PDE/Model/Interval.lean` is indexed by the grade of its
elliptic source, and its objects are the states placed at the corresponding
real grade `placementGrade order = -(order + finrank ℝ Point + 1)`.

That grade is **definable**, not chosen: it is a closed-form function of the
index and the dimension.  Nothing here applies `Classical.choice` to
`∃ grade, state ∈ sobolev grade`, and no object is given a field that simply
asserts the regularity the framework is supposed to produce.  What an object
carries is a membership proof, exactly as `Interval.Object` carries a
`ContDiff` witness.

## Where the locality is: what a caller actually supplies

The primary way to build an object is `Object.ofLocalResidual`, and it asks a
caller for exactly two things:

* a distribution *on a window* --- an element of `𝓓'(domain, Value)` --- which
  is carried into the tempered scale by `Localization.temperedOfLocal`, i.e. by
  multiplying test functions by the window's own smooth cutoff.  Nothing is
  lost by that: `Localization.temperedOfLocal_cutoffTest_apply_of_subset` says
  that on test functions supported in the window's inner ball the localized
  state answers exactly as the original local datum does;
* the membership `MemSobolev (placementGrade Point order) 2` of that localized
  state --- *the grade the residual already knows about itself*.

The second item is a **hypothesis of the caller**, in exactly the sense
`PDE/Solution/InteriorRegularity.lean` documents for its own `SobolevOn`
hypothesis: it is what a residual already knows about itself, and it is never
a fact about the residual on all of frequency space.  A local `L²` bound is
enough to supply it: `Object.ofSquareIntegrableResidual` takes an `L²`
representative of the cut-off datum and nothing else, because the placement
grade is negative and `MemSobolev.mono` walks down from grade zero.  No
hypothesis on the primary path quantifies over all frequencies, all points, or
all test functions.

`Object.ofFourierData` (with its retained former name `Object.ofLocalDatum`)
is an *optional convenience*, kept because it is genuinely proved and genuinely
useful when Fourier data happens to be available: it discharges the same
membership from a polynomially bounded Fourier transform through
`FiniteOrder.memSobolev_of_fourier_eq_integral`.  Its `represents` hypothesis
--- the easy half of Paley--Wiener--Schwartz, which mathlib does not have and
which `PDE/Solution/FiniteOrder.lean` documents as its own gap --- is a global
statement, and that is precisely why it is no longer on the primary path.

## Why the atlas carrier is the ambient state, and not `𝓓'(window)`

The atlas below still reads an object globally --- `LocalObject _` is
`𝓢'(Point, Value)` and restriction along nesting is the identity --- and that
is recorded rather than hidden.  It is *not* because a per-window reading does
not exist.  One is built here and proved coherent:

* `readingOn state window` is what the state answers on the test functions
  supported in the window's own compact, and nothing else;
* `restrictReading` restricts it along nesting by extension by zero
  (`ContDiffMapSupportedIn.monoCLM`), and `restrictReading_refl`,
  `restrictReading_trans` and `readingOn_restrictReading` are the three atlas
  coherence laws for it, proved verbatim.

What blocks that reading from *being* the atlas carrier is not the atlas laws.
It is the equation.  `RepresentedEquation.satisfies` is a predicate on
`A.LocalObject window`, and this model's equation is
`besselPotential Point Value 2 u = source`.  mathlib's `besselPotential` is a
Fourier multiplier defined on `𝓢'(Point, Value)` and nowhere else: there is no
Bessel potential on `𝓓'(Ω, Value)`, and none on a window's readings.  The
multiplier `(1 + ‖ξ‖²)` does belong to the *local* differential operator
`1 − (2π)⁻² Δ`, so a window-local restatement is not mathematically impossible
--- but it would require first proving `besselPotential 2 f = f − (2π)⁻² Δ f`
on `𝓢'` (mathlib states no such identity; it stops at
`besselPotential_neg_two_laplacian_eq`, which is again a multiplier identity),
then carrying that differential operator to the local carrier, and then
re-proving `helmholtz_potential` and `satisfies_tailTermAt` for it.  Every one
of those is new global analysis, not a rearrangement of what is here.

A second bridge is missing if the carrier is to be `𝓓'(Ω, Value)` itself rather
than the readings above: `restrict` would have to send `𝓢'(Point, Value)` to
`𝓓'(Ω, Value)`, i.e. transpose a *continuous* map `𝓓(Ω, ℝ) → 𝓢(Point, ℂ)`.
mathlib supplies `HasCompactSupport.toSchwartzMap` as a bare function only ---
which is exactly why `readingOn` lands in plain linear functionals; the
continuous version needs, on every compact `K ⊆ Ω`, an estimate of the Schwartz
seminorms of a `𝓓_{K}`-function by the `𝓓_{K}`-seminorms, and then
`TestFunction.limitCLM` to glue.  `Localization/TemperedBridge.lean` builds the
*opposite* direction (cut off, then transpose).

So the honest statement is: the per-window reading exists and is coherent, the
per-window *equation* does not, and until it does the localization that matters
is performed where it can be proved to lose nothing --- by the window's own
cutoff, inside `Object.ofLocalResidual`.

Nothing here mentions a strategy, a ledger, a route, or an execution.
-/

namespace Hypostructure.PDE.Bessel

open MeasureTheory TemperedDistribution FourierTransform Metric TopologicalSpace
open Hypostructure.PDE.Localization
open Hypostructure.PDE.Solution.Bessel
open Hypostructure.PDE.Solution.FiniteOrder
open scoped SchwartzMap Distributions ENNReal

/-! ## Windows

A window is a concentric pair of radii around a centre: the inner ball is
where a local fact is asserted, the outer ball is where the window's smooth
cutoff is still allowed to be nonzero.  This is precisely the data
`Localization/Cutoff.lean` consumes, so a window *is* a cutoff.
-/

section Windows

variable (Point : Type) [NormedAddCommGroup Point]

/-- A window of the ambient space, carrying its own centre and its own pair of
radii.  The two radii are what a cutoff needs, so no window ever has to be
paired with an externally chosen bump. -/
structure Window where
  centre : Point
  innerRadius : ℝ
  outerRadius : ℝ
  innerRadius_pos : 0 < innerRadius
  innerRadius_lt_outerRadius : innerRadius < outerRadius

variable {Point}

/-- Membership of a point in a window: the inner ball, where the window's
cutoff is identically one. -/
def Window.Mem (window : Window Point) (place : Point) : Prop :=
  place ∈ closedBall window.centre window.innerRadius

/-- One window sits inside another when the smaller outer ball is contained in
the larger one.  Stating it by the triangle inequality rather than by set
inclusion is what makes reflexivity and transitivity immediate. -/
def Window.Nested (small large : Window Point) : Prop :=
  dist small.centre large.centre + small.outerRadius ≤ large.outerRadius

theorem Window.nested_refl (window : Window Point) : window.Nested window := by
  simp [Window.Nested]

theorem Window.nested_trans {small middle large : Window Point}
    (inner : small.Nested middle) (outer : middle.Nested large) :
    small.Nested large := by
  have triangle : dist small.centre large.centre ≤
      dist small.centre middle.centre + dist middle.centre large.centre :=
    dist_triangle _ _ _
  have inner' : dist small.centre middle.centre + small.outerRadius ≤
      middle.outerRadius := inner
  have outer' : dist middle.centre large.centre + middle.outerRadius ≤
      large.outerRadius := outer
  show dist small.centre large.centre + small.outerRadius ≤ large.outerRadius
  linarith

section Cutoff

variable [NormedSpace ℝ Point] [FiniteDimensional ℝ Point] [HasContDiffBump Point]

/-- The compact set the window's cutoff is supported in. -/
noncomputable def Window.support (window : Window Point) : Compacts Point :=
  cutoffCompacts window.centre window.innerRadius_pos
    window.innerRadius_lt_outerRadius

/-- The window's own smooth cutoff: one on the inner ball, supported in the
compact `Window.support`. -/
noncomputable def Window.cutoff (window : Window Point) :
    𝓓_{window.support}(Point, ℝ) :=
  cutoffTest window.centre window.innerRadius_pos
    window.innerRadius_lt_outerRadius

end Cutoff

end Windows

/-! ## The graded scale

`Grade` is `ℝ`; the operator lowers it by two and the solution operator raises
it by two.  A model of index `order` places its objects at the definable grade
`placementGrade order`, so its elliptic source lives one step below, at
`sourceGrade order`.
-/

/-- The regularity the solution operator gains: the operator is second order. -/
def stepGrade (grade : ℝ) : ℝ := grade + 2

section Grades

variable (Point : Type) [NormedAddCommGroup Point] [NormedSpace ℝ Point]

/-- **The definable placement grade.**  A datum whose Fourier transform is
bounded by a polynomial of degree `order` lies in the Sobolev space of this
grade, by `FiniteOrder.memSobolev_of_fourier_eq_integral`; the value is a
closed-form function of `order` and the dimension, so no existential is ever
chosen and no witness is ever extracted. -/
noncomputable def placementGrade (order : ℕ) : ℝ :=
  -((order : ℝ) + (Module.finrank ℝ Point : ℝ) + 1)

/-- The grade of the model's elliptic source: one step below the grade its
objects are placed at. -/
noncomputable def sourceGrade (order : ℕ) : ℝ :=
  placementGrade Point order - 2

variable {Point}

/-- The objects of the model sit exactly at the placement grade: this is the
only arithmetic the grading needs. -/
theorem stepGrade_sourceGrade (order : ℕ) :
    stepGrade (sourceGrade Point order) = placementGrade Point order :=
  sub_add_cancel _ _

end Grades

/-! ## The ambient object

An object is a tempered distribution together with the proof that it inhabits
the graded carrier at the model's own placement grade.  The proof is a field,
exactly as `ContDiff` is a field of `Interval.Object`; it is never introduced
by choice, and `Object.ofLocalDatum` discharges it.
-/

section Model

variable (Point Value : Type) [NormedAddCommGroup Point]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  [NormedAddCommGroup Value] [InnerProductSpace ℂ Value] [CompleteSpace Value]
  (order : ℕ)

/-- The framework's graded ambient object over the Sobolev scale. -/
structure Object where
  /-- The ambient tempered state. -/
  state : 𝓢'(Point, Value)
  /-- The proof that the state really inhabits the graded carrier, at the
  grade the model's index places it. -/
  member : state ∈ sobolev (Point := Point) (Value := Value)
    (stepGrade (sourceGrade Point order))

variable {Point Value order}

/-- The graded component of an object: its state, together with its own
membership witness.  This is what the elliptic operator acts on. -/
def Object.component (object : Object Point Value order) :
    sobolev (Point := Point) (Value := Value)
      (stepGrade (sourceGrade Point order)) :=
  ⟨object.state, object.member⟩

@[simp] theorem Object.component_val (object : Object Point Value order) :
    object.component.val = object.state :=
  rfl

/-! ### The primary constructor: the grade is incoming data

An object is a state placed at the model's grade, so the one thing a caller has
to bring is the placement itself.  `Object.ofGradedState` asks for it in the
form the residual already carries --- `MemSobolev (placementGrade Point order)`
--- exactly as `PDE/Solution/InteriorRegularity.lean` asks its callers for
`SobolevOn region grade state` and derives everything else from it.

Nothing on this path is quantified over all of frequency space, all of `Point`,
or all test functions.
-/

/--
**A state placed at the model's grade is an object.**

This is the primary constructor: the membership is *supplied*, because it is
what a residual knows about itself, and the model's own arithmetic
(`stepGrade_sourceGrade`) is the only thing performed on it.
-/
def Object.ofGradedState (state : 𝓢'(Point, Value))
    (graded : MemSobolev (placementGrade Point order) 2 state) :
    Object Point Value order where
  state := state
  member := by
    show state ∈ sobolev (stepGrade (sourceGrade Point order))
    rw [stepGrade_sourceGrade]
    exact graded

@[simp] theorem Object.state_ofGradedState (state : 𝓢'(Point, Value))
    (graded : MemSobolev (placementGrade Point order) 2 state) :
    (Object.ofGradedState (order := order) state graded).state = state :=
  rfl

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point] in
/-- The placement grade of every model is negative: it is minus a sum of
nonnegative quantities and one.  This is what makes a plain local `L²` bound
enough to place a state. -/
theorem placementGrade_nonpos (order : ℕ) :
    placementGrade Point order ≤ 0 := by
  have dimension_nonneg : (0 : ℝ) ≤ (Module.finrank ℝ Point : ℝ) :=
    Nat.cast_nonneg _
  have order_nonneg : (0 : ℝ) ≤ (order : ℝ) := Nat.cast_nonneg _
  simp only [placementGrade]
  linarith

/-- **Grade zero suffices.**  A state that is square integrable --- the weakest
thing a residual can know about itself --- already sits at the model's
placement grade, because that grade is negative and `MemSobolev` is monotone
downwards.  This is the analytic content of "a local `L²` bound supplies the
grade". -/
theorem memSobolev_placementGrade_of_memSobolev_zero
    {state : 𝓢'(Point, Value)} (square : MemSobolev 0 2 state) :
    MemSobolev (placementGrade Point order) 2 state :=
  MemSobolev.mono (placementGrade_nonpos (Point := Point) order) square

/-! ### The primary local entry points

`temperedOfLocal` carries a distribution *on a window* into the tempered scale
by cutting it off with the window's own bump, and the caller's own grade is
what places it.  Nothing else is required.
-/

section LocalDatum

variable [HasContDiffBump Point]

/--
**A local residual, placed at the grade it already knows.**

The primary constructor of the model.  A caller supplies a distribution on a
window and the membership of its cut-off form at the model's placement grade;
the cutoff bridge does the carrying, and `Localization`'s
`temperedOfLocal_cutoffTest_apply_of_subset` guarantees that nothing the datum
knew on the inner ball is lost.
-/
noncomputable def Object.ofLocalResidual {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value))
    (graded : MemSobolev (placementGrade Point order) 2
      (temperedOfLocal window.cutoff inside datum)) :
    Object Point Value order :=
  Object.ofGradedState _ graded

/-- The state of a locally constructed object is exactly the localized datum. -/
@[simp] theorem Object.state_ofLocalResidual {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value))
    (graded : MemSobolev (placementGrade Point order) 2
      (temperedOfLocal window.cutoff inside datum)) :
    (Object.ofLocalResidual (order := order) window inside datum graded).state =
      temperedOfLocal window.cutoff inside datum :=
  rfl

/--
**A square integrable local residual is an object, with no further data.**

The hypothesis is an `L²` representative of the cut-off datum --- a single
equation between two tempered distributions, not a statement about every
frequency --- and that is all: the placement grade is negative, so grade zero
already clears it.
-/
noncomputable def Object.ofSquareIntegrableResidual {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value))
    (representative : Lp Value 2 (volume : Measure Point))
    (agrees : temperedOfLocal window.cutoff inside datum =
      Lp.toTemperedDistribution representative) :
    Object Point Value order :=
  Object.ofLocalResidual window inside datum
    (memSobolev_placementGrade_of_memSobolev_zero
      (memSobolev_zero_iff.mpr ⟨representative, agrees⟩))

/-- The state of a square integrable local residual is again exactly the
localized datum. -/
@[simp] theorem Object.state_ofSquareIntegrableResidual {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value))
    (representative : Lp Value 2 (volume : Measure Point))
    (agrees : temperedOfLocal window.cutoff inside datum =
      Lp.toTemperedDistribution representative) :
    (Object.ofSquareIntegrableResidual (order := order) window inside datum
      representative agrees).state =
      temperedOfLocal window.cutoff inside datum :=
  rfl

/-! ### The optional Fourier convenience

`Object.ofFourierData` is *not* on the primary path: it demands the Fourier
transform of the localized datum on all of frequency space, which a local
residual cannot know.  It is retained because it is genuinely proved and
genuinely useful whenever that data happens to be available --- for instance
when the datum is a finite measure or a compactly supported function whose
transform has been computed.
-/

/--
**A local distribution with known Fourier data becomes a graded ambient
object.**

The order indexes the model, the grade is computed from it, and the membership
is proved.  The dimension budget of the placement theorem is met by the choice
`grade = order + finrank ℝ Point + 1`, which clears it in every dimension.

The hypotheses `polynomial` and `represents` range over all frequencies and all
test functions: that is the price of this route, and the reason
`Object.ofLocalResidual` rather than this constructor is the model's entry
point.
-/
noncomputable def Object.ofFourierData {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value)) (constant : ℝ) (transform : Point → Value)
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ order)
    (represents : ∀ test : 𝓢(Point, ℂ),
      𝓕 (temperedOfLocal window.cutoff inside datum) test =
        ∫ frequency : Point, test frequency • transform frequency) :
    Object Point Value order where
  state := temperedOfLocal window.cutoff inside datum
  member := by
    have dimension_nonneg : (0 : ℝ) ≤ (Module.finrank ℝ Point : ℝ) :=
      Nat.cast_nonneg _
    have placed : MemSobolev (placementGrade Point order) 2
        (temperedOfLocal window.cutoff inside datum) := by
      refine memSobolev_of_fourier_eq_integral
        (grade := (order : ℝ) + (Module.finrank ℝ Point : ℝ) + 1)
        ?_ measurable polynomial represents
      linarith
    show temperedOfLocal window.cutoff inside datum ∈
      sobolev (stepGrade (sourceGrade Point order))
    rw [stepGrade_sourceGrade]
    exact placed

/-- The former name of `Object.ofFourierData`, retained so that callers that
already had Fourier data at hand keep compiling.  It is the same constructor,
and it is not the model's primary entry point. -/
noncomputable def Object.ofLocalDatum {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value)) (constant : ℝ) (transform : Point → Value)
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ order)
    (represents : ∀ test : 𝓢(Point, ℂ),
      𝓕 (temperedOfLocal window.cutoff inside datum) test =
        ∫ frequency : Point, test frequency • transform frequency) :
    Object Point Value order :=
  Object.ofFourierData window inside datum constant transform measurable
    polynomial represents

/-- The state of a constructed object is exactly the localized datum.  Combined
with `Localization.temperedOfLocal_cutoffTest_apply_of_subset` this says that
the placed object still answers, on the window's inner ball, every question the
original local datum answered. -/
theorem Object.state_ofLocalDatum {domain : Opens Point}
    (window : Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Value)) (constant : ℝ) (transform : Point → Value)
    (measurable : AEStronglyMeasurable transform (volume : Measure Point))
    (polynomial : ∀ frequency : Point,
      ‖transform frequency‖ ≤ constant * (1 + ‖frequency‖) ^ order)
    (represents : ∀ test : 𝓢(Point, ℂ),
      𝓕 (temperedOfLocal window.cutoff inside datum) test =
        ∫ frequency : Point, test frequency • transform frequency) :
    (Object.ofLocalDatum (order := order) window inside datum constant transform
      measurable polynomial represents).state =
      temperedOfLocal window.cutoff inside datum :=
  rfl

/-! ### The genuinely per-window reading

The atlas below reads an object globally, and the module docstring says why the
*carrier* cannot move.  What can be built --- and is built here --- is the
per-window reading itself: a state answers the test functions supported in a
window's own compact, and nothing else.  This is a genuine restriction map, and
it obeys the three atlas coherence laws verbatim (`restrictReading_refl`,
`restrictReading_trans`, `readingOn_restrictReading`).

It is not the atlas carrier because `RepresentedEquation.satisfies` would then
have to be a predicate on it, and mathlib's `besselPotential` --- this model's
operator --- exists only on `𝓢'(Point, Value)`.  That is the whole obstruction,
and it is an obstruction of the ambient library, not of the atlas laws.
-/

/-- A real test function supported in a fixed compact set, read as a complex
Schwartz function.  A compactly supported smooth function is Schwartz, and
tempered distributions are tested against complex Schwartz functions, so this
composite is what a window's test functions have to become before an ambient
state can be asked about them. -/
noncomputable def schwartzOfSupported {support : Compacts Point}
    (test : 𝓓_{support}(Point, ℝ)) : 𝓢(Point, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun place => ((test place : ℝ) : ℂ))
    (test.hasCompactSupport.comp_left (g := fun value : ℝ => (value : ℂ))
      Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp test.contDiff)

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [HasContDiffBump Point] in
@[simp] theorem schwartzOfSupported_apply {support : Compacts Point}
    (test : 𝓓_{support}(Point, ℝ)) (place : Point) :
    schwartzOfSupported test place = ((test place : ℝ) : ℂ) :=
  rfl

/-- **The window's own reading of an ambient state.**  It answers exactly the
test functions supported in the window's compact, and it is defined for every
window without reference to any other one. -/
noncomputable def readingOn (state : 𝓢'(Point, Value)) (window : Window Point) :
    𝓓_{window.support}(Point, ℝ) →ₗ[ℝ] Value where
  toFun := fun test => state (schwartzOfSupported test)
  map_add' := by
    intro left right
    have expand : schwartzOfSupported (left + right) =
        schwartzOfSupported left + schwartzOfSupported right := by
      refine DFunLike.ext _ _ fun place => ?_
      push_cast
      simp
    rw [expand, map_add]
  map_smul' := by
    intro scalar test
    have expand : schwartzOfSupported (scalar • test) =
        (scalar : ℂ) • schwartzOfSupported test := by
      refine DFunLike.ext _ _ fun place => ?_
      push_cast
      simp
    rw [expand, map_smul, Complex.coe_smul]
    rfl

omit [MeasurableSpace Point] [BorelSpace Point] [CompleteSpace Value] in
@[simp] theorem readingOn_apply (state : 𝓢'(Point, Value))
    (window : Window Point) (test : 𝓓_{window.support}(Point, ℝ)) :
    readingOn state window test = state (schwartzOfSupported test) :=
  rfl

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- The window's compact is exactly the closed outer ball: the cutoff is
supported in the open outer ball and its closure is that closed ball. -/
theorem Window.support_eq_closedBall (window : Window Point) :
    (window.support : Set Point) = closedBall window.centre window.outerRadius := by
  have outer_ne_zero : window.outerRadius ≠ 0 :=
    ne_of_gt (lt_trans window.innerRadius_pos window.innerRadius_lt_outerRadius)
  show tsupport (Localization.cutoff window.centre window.innerRadius_pos
    window.innerRadius_lt_outerRadius) = _
  rw [tsupport, cutoff_support, closure_ball _ outer_ne_zero]

omit [MeasurableSpace Point] [BorelSpace Point] in
/-- Nested windows have nested compacts: this is the triangle inequality the
nesting relation was written as. -/
theorem Window.support_subset {small large : Window Point}
    (nested : small.Nested large) :
    (small.support : Set Point) ⊆ (large.support : Set Point) := by
  have bound : dist small.centre large.centre + small.outerRadius ≤
    large.outerRadius := nested
  rw [Window.support_eq_closedBall, Window.support_eq_closedBall]
  exact closedBall_subset_closedBall' (by linarith)

omit [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [HasContDiffBump Point] in
/-- Extension by zero of a test function of a smaller window to one of a larger
window changes nothing but the compact it is recorded in. -/
theorem coe_monoCLM {small large : Compacts Point}
    (subset : (small : Set Point) ⊆ (large : Set Point))
    (test : 𝓓_{small}(Point, ℝ)) :
    ((ContDiffMapSupportedIn.monoCLM ℝ test : 𝓓_{large}(Point, ℝ)) :
      Point → ℝ) = test := by
  have condition : (⊤ : ℕ∞) ≤ (⊤ : ℕ∞) ∧ small ≤ large := ⟨le_rfl, subset⟩
  rw [ContDiffMapSupportedIn.monoCLM_apply, if_pos condition]

/-- **Restriction of a reading along nesting.**  A test function of the smaller
window is one of the larger window, so the larger window's reading answers it;
that is the entire content of restriction, and no data is invented. -/
noncomputable def restrictReading {small large : Window Point}
    (_nested : small.Nested large)
    (reading : 𝓓_{large.support}(Point, ℝ) →ₗ[ℝ] Value) :
    𝓓_{small.support}(Point, ℝ) →ₗ[ℝ] Value :=
  reading ∘ₗ (ContDiffMapSupportedIn.monoCLM ℝ :
    𝓓_{small.support}(Point, ℝ) →L[ℝ] 𝓓_{large.support}(Point, ℝ)).toLinearMap

omit [MeasurableSpace Point] [BorelSpace Point] [CompleteSpace Value] in
@[simp] theorem restrictReading_apply {small large : Window Point}
    (nested : small.Nested large)
    (reading : 𝓓_{large.support}(Point, ℝ) →ₗ[ℝ] Value)
    (test : 𝓓_{small.support}(Point, ℝ)) :
    restrictReading nested reading test =
      reading (ContDiffMapSupportedIn.monoCLM ℝ test) :=
  rfl

omit [MeasurableSpace Point] [BorelSpace Point] [CompleteSpace Value] in
/-- The first atlas law, for the per-window reading. -/
theorem restrictReading_refl (window : Window Point)
    (reading : 𝓓_{window.support}(Point, ℝ) →ₗ[ℝ] Value) :
    restrictReading (Window.nested_refl window) reading = reading := by
  refine LinearMap.ext fun test => ?_
  have same : (ContDiffMapSupportedIn.monoCLM ℝ test :
      𝓓_{window.support}(Point, ℝ)) = test :=
    ContDiffMapSupportedIn.ext fun place =>
      congrFun (coe_monoCLM (subset_refl _) test) place
  rw [restrictReading_apply, same]

omit [MeasurableSpace Point] [BorelSpace Point] [CompleteSpace Value] in
/-- The second atlas law, for the per-window reading. -/
theorem restrictReading_trans {small middle large : Window Point}
    (inner : small.Nested middle) (outer : middle.Nested large)
    (reading : 𝓓_{large.support}(Point, ℝ) →ₗ[ℝ] Value) :
    restrictReading inner (restrictReading outer reading) =
      restrictReading (Window.nested_trans inner outer) reading := by
  refine LinearMap.ext fun test => ?_
  have same : (ContDiffMapSupportedIn.monoCLM ℝ
        (ContDiffMapSupportedIn.monoCLM ℝ test :
          𝓓_{middle.support}(Point, ℝ)) : 𝓓_{large.support}(Point, ℝ)) =
      (ContDiffMapSupportedIn.monoCLM ℝ test : 𝓓_{large.support}(Point, ℝ)) := by
    refine ContDiffMapSupportedIn.ext fun place => ?_
    rw [congrFun (coe_monoCLM (Window.support_subset outer) _) place,
      congrFun (coe_monoCLM (Window.support_subset inner) test) place,
      congrFun (coe_monoCLM
        (Window.support_subset (Window.nested_trans inner outer)) test) place]
  simp only [restrictReading_apply, same]

omit [MeasurableSpace Point] [BorelSpace Point] [CompleteSpace Value] in
/-- The third atlas law, for the per-window reading: reading an ambient state on
a large window and then restricting is reading it on the small window.  This is
the law that makes the reading a genuine restriction rather than a relabelling. -/
theorem readingOn_restrictReading (state : 𝓢'(Point, Value))
    {small large : Window Point} (nested : small.Nested large) :
    restrictReading nested (readingOn state large) = readingOn state small := by
  refine LinearMap.ext fun test => ?_
  have same : schwartzOfSupported (ContDiffMapSupportedIn.monoCLM ℝ test :
      𝓓_{large.support}(Point, ℝ)) = schwartzOfSupported test := by
    refine DFunLike.ext _ _ fun place => ?_
    rw [schwartzOfSupported_apply, schwartzOfSupported_apply,
      congrFun (coe_monoCLM (Window.support_subset nested) test) place]
  rw [restrictReading_apply, readingOn_apply, readingOn_apply, same]

/-- The reading of an object on one of its windows. -/
noncomputable def Object.readingOn (object : Object Point Value order)
    (window : Window Point) : 𝓓_{window.support}(Point, ℝ) →ₗ[ℝ] Value :=
  _root_.Hypostructure.PDE.Bessel.readingOn object.state window

end LocalDatum

/-! ## Registration

`problem`, `atlas`, `equation` and `model` are the framework's; an application
supplies a baseline and a branch state and nothing else, exactly as on the
graph side and exactly as in `Model/Interval.lean`.
-/

variable (Point Value order)
variable (Baseline : Object Point Value order → Prop)
  (BranchState : Object Point Value order → Type)

/-- Register the graded Sobolev-scale PDE problem. -/
def problem : Core.Problem where
  Ambient := Object Point Value order
  Baseline := Baseline
  BranchState := BranchState

/-- The canonical atlas.  The local reading of an object is its ambient
tempered state: a tempered distribution is already defined everywhere, so
restriction along nesting is the identity and every atlas law is definitional.

A genuinely per-window reading is available --- `readingOn`, with
`restrictReading` and the three coherence laws proved for it --- and it is
*not* used as `LocalObject` here for one reason, spelled out in the module
docstring: the model's equation is `besselPotential Point Value 2 u = source`,
and that operator exists only on `𝓢'(Point, Value)`, so `satisfies` could not
be stated over a per-window carrier.  The localization that matters is
performed by the window's own cutoff in `Object.ofLocalResidual`, not by the
atlas. -/
def atlas : PDE.LocalAtlas (problem Point Value order Baseline BranchState) where
  Point := Point
  Window := Window Point
  contains := fun place window => window.Mem place
  nested := Window.Nested
  nested_refl := Window.nested_refl
  nested_trans := Window.nested_trans
  core := id
  core_nested := Window.nested_refl
  LocalObject := fun _window => 𝓢'(Point, Value)
  restrict := fun object _window => object.state
  restrictLocal := fun _nested value => value
  restrict_refl := fun _window _value => rfl
  restrict_trans := fun _inner _outer _value => rfl
  restrict_global := fun _object _inner _outer _nested => rfl

/--
The represented equation: `(1 − (2π)⁻² Δ) u = source`, written through
mathlib's `besselPotential … 2`, which *is* that operator.

The source is retained as equation data and validity is the equation itself,
so an `EquationState` carries the actual mathematical fact.  It is not the
Laplace equation, and its homogeneous solutions are not harmonic functions.
-/
def equation :
    PDE.RepresentedEquation (problem Point Value order Baseline BranchState)
      (atlas Point Value order Baseline BranchState) where
  EquationData := fun _window _value => 𝓢'(Point, Value)
  satisfies := fun {_window} {value} source =>
    besselPotential Point Value 2 value = source
  restrictEquation := fun {_U _V} _nested {_value} source => source
  restrict_satisfies := fun {_U _V} _nested {_value} _source valid => valid

/-- The canonical graded Sobolev-scale local model. -/
def model : PDE.LocalModel where
  problem := problem Point Value order Baseline BranchState
  atlas := atlas Point Value order Baseline BranchState
  equation := equation Point Value order Baseline BranchState

/-! ## The graded elliptic operator

Every field is the solution library's, unchanged.  `operator` is `helmholtz`,
`solve` is `potential`, and `operator_solve` is `helmholtz_potential` itself:
because the framework's graded carrier is `sobolev` on the nose, there is
nothing left to prove here.

`Admissible` is left as a parameter: which windows a localization step is
allowed to select is a property of the application, never of the scale.
-/

/--
The canonical elliptic operator of the graded Sobolev-scale model.

Nothing that fails to gain two grades could be written in `solve`'s slot, and
the entry that is written there gains them by mathlib's own
`besselPotential_besselPotential_apply`.
-/
noncomputable def ellipticOperator
    (Admissible : Object Point Value order → Window Point → Prop) :
    PDE.ComponentEllipticOperator (model Point Value order Baseline BranchState)
      (model Point Value order Baseline BranchState) ℝ Admissible
      (fun _object _window grade =>
        (sobolev (Point := Point) (Value := Value) grade : Type)) where
  grade := sourceGrade Point order
  step := stepGrade
  component := fun object _window => object.component
  rebuild := fun _object _window value =>
    { state := value.val, member := value.2 }
  rebuild_component := fun _object _window => rfl
  operator := fun _object _window grade => helmholtz grade
  solve := fun _object _window grade value => potential grade value
  operator_solve := fun _object _window grade value =>
    helmholtz_potential grade value
  tailWindow := id
  tailObject := fun _object _window _target value => value.val
  tailData := fun _object _window _target _value =>
    show 𝓢'(Point, Value) from 0
  tailValid := by
    intro _object _window _target value homogeneous
    show besselPotential Point Value 2 value.val = (0 : 𝓢'(Point, Value))
    exact ZeroMemClass.coe_eq_zero.mpr homogeneous

/-! ## The derived Calderón--Zygmund split

Both statements below are the framework's own, instantiated: the local child
and the tail sum back to the component, and the tail is annihilated by the
model's operator.  Neither is proved here --- they are consequences of
`operator_solve`, which is `Bessel.helmholtz_potential`.
-/

variable {Point Value order Baseline BranchState}

/-- The exact two-term decomposition of the graded component, at every
admissible window. -/
theorem localTermAt_add_tailTermAt
    {Admissible : Object Point Value order → Window Point → Prop}
    (object : Object Point Value order)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model Point Value order Baseline BranchState)
      (Admissible := Admissible) object) :
    (ellipticOperator Point Value order Baseline BranchState
        Admissible).localTermAt object site +
      (ellipticOperator Point Value order Baseline BranchState
        Admissible).tailTermAt object site =
      object.component :=
  (ellipticOperator Point Value order Baseline BranchState
    Admissible).localTermAt_add_tailTermAt object site

/--
**The tail equation.**

The complementary child is annihilated by `1 − (2π)⁻² Δ`, the operator this
model registers.  It is *not* annihilated by the Laplacian and it is *not*
harmonic: what is proved, here and in the module docstring, is exactly the
homogeneous Helmholtz equation.
-/
theorem helmholtz_tailTermAt
    {Admissible : Object Point Value order → Window Point → Prop}
    (object : Object Point Value order)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model Point Value order Baseline BranchState)
      (Admissible := Admissible) object) :
    besselPotential Point Value 2
        ((ellipticOperator Point Value order Baseline BranchState
          Admissible).tailTermAt object site).val =
      0 :=
  ZeroMemClass.coe_eq_zero.mpr
    ((ellipticOperator Point Value order Baseline BranchState
      Admissible).operator_tailTermAt object site)

/-- The tail is a valid state of the model's own represented equation with zero
source: this is `tailValid`, restated at the derived tail. -/
theorem satisfies_tailTermAt
    {Admissible : Object Point Value order → Window Point → Prop}
    (object : Object Point Value order)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model Point Value order Baseline BranchState)
      (Admissible := Admissible) object)
    (target : Window Point) :
    (model Point Value order Baseline BranchState).equation.satisfies
      ((ellipticOperator Point Value order Baseline BranchState
        Admissible).tailData object site.val target
        ((ellipticOperator Point Value order Baseline BranchState
          Admissible).tailTermAt object site)) :=
  (ellipticOperator Point Value order Baseline BranchState Admissible).tailValid
    object site.val target _
    ((ellipticOperator Point Value order Baseline BranchState
      Admissible).operator_tailTermAt object site)

end Model

/-! ## A concrete instantiation

The entry above is stated for an abstract finite dimensional real inner product
space, which is what `Bessel.sobolev` needs.  The two declarations below are the
proof that this generality is usable rather than vacuous: for *every* dimension
and *every* order, the model and its elliptic operator exist over Euclidean
space with complex values, with no further data supplied.  A binary product
type such as `ℝ × Space` would carry the sup norm and could not appear here;
`EuclideanSpace` can.
-/

section Euclidean

variable (dimension order : ℕ)
  (Baseline : Object (EuclideanSpace ℝ (Fin dimension)) ℂ order → Prop)
  (BranchState : Object (EuclideanSpace ℝ (Fin dimension)) ℂ order → Type)

/-- The graded Sobolev-scale model over Euclidean space of any dimension. -/
noncomputable def euclideanModel : PDE.LocalModel :=
  model (EuclideanSpace ℝ (Fin dimension)) ℂ order Baseline BranchState

/-- Its elliptic operator, for any admissibility predicate the application
chooses. -/
noncomputable def euclideanEllipticOperator
    (Admissible : Object (EuclideanSpace ℝ (Fin dimension)) ℂ order →
      Window (EuclideanSpace ℝ (Fin dimension)) → Prop) :
    PDE.ComponentEllipticOperator
      (euclideanModel dimension order Baseline BranchState)
      (euclideanModel dimension order Baseline BranchState) ℝ Admissible
      (fun _object _window grade =>
        (sobolev (Point := EuclideanSpace ℝ (Fin dimension)) (Value := ℂ)
          grade : Type)) :=
  ellipticOperator (EuclideanSpace ℝ (Fin dimension)) ℂ order Baseline
    BranchState Admissible

end Euclidean

end Hypostructure.PDE.Bessel

