import Mathlib
import Hypostructure.PDE.Distribution.OfFunction

/-!
# Distributional derivatives of a smoothly represented distribution

`OfFunction.lean` builds a distribution *from* a function.  This module reads
the derivative of one *back*: if a distribution is represented on its domain by
a function that is smooth there, then each of its distributional line
derivatives is represented by the corresponding classical derivative.

That is the only thing standing between a represented balance and the
representative its remaining term names.  In `∂_t u - Δ u + ∇p = f`, once the
velocity is smooth on the domain the first two terms are classical, so the
pressure gradient is represented by `f - ∂_t u + Δ u` --- a function, written
down, not glued together from window data.  No partition of unity, no sheaf
step, and no statement about a witness on a whole object appears anywhere: each
lemma below is integration by parts against one compactly supported test
function.

The mechanism is the same throughout.  A test function of `domain` vanishes on
a neighbourhood of every point outside `domain`, so its product with a weight
that is only defined --- or only regular --- on `domain` is globally as regular
as the weight is there.  `integral_lineDeriv_eq_zero`, already proved in
`OfFunction.lean`, then turns the product rule into integration by parts.
-/

namespace Hypostructure.PDE.Distribution

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point] [NormedSpace ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point]
  {domain : Opens Point} {μ : Measure Point}

/-! ## Space-time volume

The parabolic space-times of `ParabolicAtlas.lean` are products `ℝ × Space`,
and integration by parts needs their volume to be a Haar measure.  It is, for
the only reason available: it is the product of two Haar measures.  Mathlib
declares the same instance for `ℝ × ℝ` by hand; this is that statement for a
general spatial factor.
-/

instance instIsAddHaarMeasureVolumeProd (Space : Type*) [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] [MeasureSpace Space] [BorelSpace Space]
    [(volume : Measure Space).IsAddHaarMeasure]
    [SFinite (volume : Measure Space)] :
    (volume : Measure (ℝ × Space)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-! ## A test function times a weight defined on the domain -/

/-- Outside the domain a test function vanishes on a whole neighbourhood, so its
product with any weight does too.  This is the only fact used to transfer
regularity of the weight *on the domain* to regularity of the product
*everywhere*. -/
theorem testMul_eventuallyEq_zero (test : 𝓓(domain, ℝ)) (weight : Point → ℝ)
    {place : Point} (notMem : place ∉ domain) :
    (fun position => test position * weight position) =ᶠ[nhds place]
      fun _ => (0 : ℝ) := by
  have notSupport : place ∉ tsupport (⇑test) := fun mem =>
    notMem (test.tsupport_subset mem)
  filter_upwards [(isClosed_tsupport (⇑test)).isOpen_compl.mem_nhds notSupport]
    with position outside
  simp [image_eq_zero_of_notMem_tsupport outside]

/-- The product of a test function with a weight continuous on the domain is
continuous everywhere. -/
theorem continuous_testMul (test : 𝓓(domain, ℝ)) {weight : Point → ℝ}
    (regular : ContinuousOn weight domain) :
    Continuous fun place => test place * weight place := by
  rw [continuous_iff_continuousAt]
  intro place
  by_cases mem : place ∈ domain
  · exact test.continuous.continuousAt.mul
      (regular.continuousAt (domain.isOpen.mem_nhds mem))
  · exact continuousAt_const.congr
      (testMul_eventuallyEq_zero test weight mem).symm

/-- The product of a test function with a weight smooth on the domain is smooth
everywhere. -/
theorem contDiff_testMul (test : 𝓓(domain, ℝ)) {weight : Point → ℝ}
    (smooth : ContDiffOn ℝ ∞ weight domain) :
    ContDiff ℝ ∞ fun place => test place * weight place := by
  rw [contDiff_iff_contDiffAt]
  intro place
  by_cases mem : place ∈ domain
  · exact test.contDiff.contDiffAt.mul
      (smooth.contDiffAt (domain.isOpen.mem_nhds mem))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (testMul_eventuallyEq_zero test weight mem)

/-- The product inherits the test function's compact support. -/
theorem hasCompactSupport_testMul (test : 𝓓(domain, ℝ)) (weight : Point → ℝ) :
    HasCompactSupport fun place => test place * weight place :=
  test.hasCompactSupport.mul_right

/-- Hence the product is integrable: continuous with compact support. -/
theorem integrable_testMul [IsFiniteMeasureOnCompacts μ] (test : 𝓓(domain, ℝ))
    {weight : Point → ℝ} (regular : ContinuousOn weight domain) :
    Integrable (fun place => test place * weight place) μ :=
  (continuous_testMul test regular).integrable_of_hasCompactSupport
    (hasCompactSupport_testMul test weight)

/-! ## The classical derivative of the weight -/

/-- On the open domain the line derivative of a smooth weight is its Fréchet
derivative read in the given direction. -/
theorem lineDeriv_eq_fderiv_of_mem {weight : Point → ℝ}
    (smooth : ContDiffOn ℝ ∞ weight domain) (direction : Point) {place : Point}
    (mem : place ∈ domain) :
    lineDeriv ℝ weight place direction = fderiv ℝ weight place direction :=
  DifferentiableAt.lineDeriv_eq_fderiv
    ((smooth.differentiableOn (by simp)).differentiableAt
      (domain.isOpen.mem_nhds mem))

/-- The line derivative of a smooth weight is continuous on the domain. -/
theorem continuousOn_lineDeriv {weight : Point → ℝ}
    (smooth : ContDiffOn ℝ ∞ weight domain) (direction : Point) :
    ContinuousOn (fun place => lineDeriv ℝ weight place direction) domain := by
  have fderivContinuous : ContinuousOn (fun place => fderiv ℝ weight place) domain :=
    smooth.continuousOn_fderiv_of_isOpen domain.isOpen (by simp)
  have evaluated :
      ContinuousOn (fun place => fderiv ℝ weight place direction) domain :=
    (ContinuousLinearMap.apply ℝ ℝ direction).continuous.comp_continuousOn
      fderivContinuous
  exact evaluated.congr fun place mem =>
    lineDeriv_eq_fderiv_of_mem smooth direction mem

/-- The line derivative of a smooth weight is smooth on the domain: this is
what lets the classical derivative be fed back into the same lemmas. -/
theorem contDiffOn_lineDeriv {weight : Point → ℝ}
    (smooth : ContDiffOn ℝ ∞ weight domain) (direction : Point) :
    ContDiffOn ℝ ∞ (fun place => lineDeriv ℝ weight place direction) domain := by
  have fderivSmooth : ContDiffOn ℝ ∞ (fun place => fderiv ℝ weight place) domain :=
    (smooth.fderivWithin domain.isOpen.uniqueDiffOn (by simp)).congr
      fun place mem => (fderivWithin_of_isOpen domain.isOpen mem).symm
  have evaluated :
      ContDiffOn ℝ ∞ (fun place => fderiv ℝ weight place direction) domain :=
    (ContinuousLinearMap.apply ℝ ℝ direction).contDiff.comp_contDiffOn fderivSmooth
  exact evaluated.congr fun place mem =>
    lineDeriv_eq_fderiv_of_mem smooth direction mem

/-! ## Integration by parts -/

/-- The product rule for a test function against a weight smooth on the domain,
valid at *every* point: inside the domain it is the ordinary product rule, and
outside it both sides vanish because the test function does. -/
theorem lineDeriv_testMul (test : 𝓓(domain, ℝ)) {weight : Point → ℝ}
    (smooth : ContDiffOn ℝ ∞ weight domain) (direction place : Point) :
    lineDeriv ℝ (fun position => test position * weight position) place direction =
      lineDeriv ℝ (⇑test) place direction * weight place +
        test place * lineDeriv ℝ weight place direction := by
  by_cases mem : place ∈ domain
  · have testDiff : DifferentiableAt ℝ (⇑test) place :=
      test.contDiff.differentiable (by simp) place
    have weightDiff : DifferentiableAt ℝ weight place :=
      (smooth.differentiableOn (by simp)).differentiableAt
        (domain.isOpen.mem_nhds mem)
    have productHas :
        HasFDerivAt (fun position => test position * weight position)
          (test place • fderiv ℝ weight place +
            weight place • fderiv ℝ (⇑test) place) place :=
      testDiff.hasFDerivAt.mul weightDiff.hasFDerivAt
    rw [(productHas.hasLineDerivAt direction).lineDeriv,
      testDiff.lineDeriv_eq_fderiv, weightDiff.lineDeriv_eq_fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    ring
  · have notSupport : place ∉ tsupport (⇑test) := fun support =>
      mem (test.tsupport_subset support)
    have vanishesNear : (⇑test) =ᶠ[nhds place] fun _ => (0 : ℝ) := by
      filter_upwards
        [(isClosed_tsupport (⇑test)).isOpen_compl.mem_nhds notSupport]
        with position outside
      exact image_eq_zero_of_notMem_tsupport outside
    have productZero :
        lineDeriv ℝ (fun position => test position * weight position) place
            direction = 0 := by
      rw [(testMul_eventuallyEq_zero test weight mem).lineDeriv_eq]
      simp [lineDeriv]
    have testZero : lineDeriv ℝ (⇑test) place direction = 0 := by
      rw [vanishesNear.lineDeriv_eq]
      simp [lineDeriv]
    rw [productZero, testZero, image_eq_zero_of_notMem_tsupport notSupport]
    simp

variable [μ.IsAddHaarMeasure]

/-- **Integration by parts against a test function.**

The boundary term is absent because the test function has compact support
inside the domain; this is `integral_lineDeriv_eq_zero` applied to the product.
-/
theorem integral_lineDeriv_testMul (test : 𝓓(domain, ℝ)) {weight : Point → ℝ}
    (smooth : ContDiffOn ℝ ∞ weight domain) (direction : Point) :
    ∫ place, lineDeriv ℝ (⇑test) place direction * weight place ∂μ =
      -∫ place, test place * lineDeriv ℝ weight place direction ∂μ := by
  have total :
      ∫ place,
          lineDeriv ℝ (fun position => test position * weight position) place
            direction ∂μ = 0 :=
    integral_lineDeriv_eq_zero (contDiff_testMul test smooth)
      (hasCompactSupport_testMul test weight) direction
  have derivative : (TestFunction.lineDerivCLM ℝ direction test : 𝓓(domain, ℝ)) =
      fun place => lineDeriv ℝ (⇑test) place direction :=
    funext fun place => TestFunction.lineDerivCLM_apply_of_le le_top
  have leftIntegrable :
      Integrable (fun place => lineDeriv ℝ (⇑test) place direction * weight place)
        μ := by
    have := integrable_testMul (μ := μ)
      (TestFunction.lineDerivCLM ℝ direction test) smooth.continuousOn
    rwa [derivative] at this
  have rightIntegrable :
      Integrable
        (fun place => test place * lineDeriv ℝ weight place direction) μ :=
    integrable_testMul test (continuousOn_lineDeriv smooth direction)
  rw [funext (lineDeriv_testMul test smooth direction),
    integral_add leftIntegrable rightIntegrable] at total
  linarith [total]

/-! ## The derivative of a smoothly represented distribution -/

/--
**The distributional line derivative of a smoothly represented distribution is
represented by the classical one.**

Nothing is inverted, estimated or glued: the identity is integration by parts
against one test function at a time.
-/
theorem represents_lineDeriv (state : 𝓓'(domain, ℝ)) {weight : Point → ℝ}
    (represents : ∀ test : 𝓓(domain, ℝ),
      state test = ∫ place, test place * weight place ∂μ)
    (smooth : ContDiffOn ℝ ∞ weight domain) (direction : Point)
    (test : 𝓓(domain, ℝ)) :
    (Distribution.lineDerivCLM direction state : 𝓓'(domain, ℝ)) test =
      ∫ place, test place * lineDeriv ℝ weight place direction ∂μ := by
  have expand :
      (Distribution.lineDerivCLM direction state : 𝓓'(domain, ℝ)) test =
        -state (TestFunction.lineDerivCLM ℝ direction test) :=
    Distribution.lineDerivCLM_apply
  have derivative : (TestFunction.lineDerivCLM ℝ direction test : 𝓓(domain, ℝ)) =
      fun place => lineDeriv ℝ (⇑test) place direction :=
    funext fun place => TestFunction.lineDerivCLM_apply_of_le le_top
  rw [expand, represents, derivative,
    integral_lineDeriv_testMul (μ := μ) test smooth direction, neg_neg]

/-! ## Reading one scalar component of a vector-valued state

A represented balance is stated on a vector-valued distribution, while the
lemmas above are scalar.  The two are connected by `Distribution.mapCLM`, which
commutes with the distributional derivative for the trivial reason that both are
linear: reading a component of a derivative is the derivative of the component.
So a vector-valued balance is a family of scalar ones and nothing else is
needed.
-/

section Component

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]

/-- The vector-valued form of `testMul_eventuallyEq_zero`. -/
theorem testSmul_eventuallyEq_zero (test : 𝓓(domain, ℝ)) (field : Point → Value)
    {place : Point} (notMem : place ∉ domain) :
    (fun position => test position • field position) =ᶠ[nhds place]
      fun _ => (0 : Value) := by
  have notSupport : place ∉ tsupport (⇑test) := fun mem =>
    notMem (test.tsupport_subset mem)
  filter_upwards [(isClosed_tsupport (⇑test)).isOpen_compl.mem_nhds notSupport]
    with position outside
  simp [image_eq_zero_of_notMem_tsupport outside]

/-- The vector-valued form of `continuous_testMul`. -/
theorem continuous_testSmul (test : 𝓓(domain, ℝ)) {field : Point → Value}
    (regular : ContinuousOn field domain) :
    Continuous fun place => test place • field place := by
  rw [continuous_iff_continuousAt]
  intro place
  by_cases mem : place ∈ domain
  · exact test.continuous.continuousAt.smul
      (regular.continuousAt (domain.isOpen.mem_nhds mem))
  · exact continuousAt_const.congr
      (testSmul_eventuallyEq_zero test field mem).symm

/-- The vector-valued form of `integrable_testMul`. -/
theorem integrable_testSmul [IsFiniteMeasureOnCompacts μ] (test : 𝓓(domain, ℝ))
    {field : Point → Value} (regular : ContinuousOn field domain) :
    Integrable (fun place => test place • field place) μ :=
  (continuous_testSmul test regular).integrable_of_hasCompactSupport
    (test.hasCompactSupport.smul_right)

/-- Reading a component commutes with differentiating: both operations are
linear, so this is `map_neg`. -/
theorem mapCLM_lineDerivCLM (reader : Value →L[ℝ] ℝ) (state : 𝓓'(domain, Value))
    (direction : Point) (test : 𝓓(domain, ℝ)) :
    (Distribution.mapCLM reader
        (Distribution.lineDerivCLM direction state) : 𝓓'(domain, ℝ)) test =
      (Distribution.lineDerivCLM direction
        (Distribution.mapCLM reader state) : 𝓓'(domain, ℝ)) test := by
  simp [Distribution.mapCLM_apply, Distribution.lineDerivCLM_apply]

/-- A component of a represented vector-valued state is represented by that
component of the representing field. -/
theorem represents_mapCLM [IsFiniteMeasureOnCompacts μ] (reader : Value →L[ℝ] ℝ)
    (state : 𝓓'(domain, Value)) {field : Point → Value}
    (regular : ContinuousOn field domain)
    (represents : ∀ test : 𝓓(domain, ℝ),
      state test = ∫ place, test place • field place ∂μ)
    (test : 𝓓(domain, ℝ)) :
    (Distribution.mapCLM reader state : 𝓓'(domain, ℝ)) test =
      ∫ place, test place * reader (field place) ∂μ := by
  rw [Distribution.mapCLM_apply, represents,
    ← ContinuousLinearMap.integral_comp_comm reader
      (integrable_testSmul test regular)]
  simp

end Component

/-! ## The balance names its remaining term

Everything above assembles into the one statement a local-closure vertex needs
from a represented equation.  In a balance

> `∂_t u − Δ u + ∇p = f`

the pressure gradient is not an unknown to be produced: once the velocity is
smooth on the domain, the first two terms are classical derivatives and `∇p` is
their difference with the forcing --- a function, written down.

No window, residual, ledger, route or target appears here, and nothing is
glued: the identity below is proved one test function at a time.
-/

section Balance

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value] {Index : Type*} [Fintype Index] [μ.IsAddHaarMeasure]

/-- Integrals against a test function add up inside the integral. -/
theorem integral_testMul_finsetSum {Coordinate : Type*}
    (test : 𝓓(domain, ℝ)) (weights : Coordinate → Point → ℝ)
    (indices : Finset Coordinate)
    (regular : ∀ coordinate, ContinuousOn (weights coordinate) domain) :
    ∑ coordinate ∈ indices,
        ∫ place, test place * weights coordinate place ∂μ =
      ∫ place, test place * (∑ coordinate ∈ indices, weights coordinate place) ∂μ := by
  rw [← integral_finset_sum indices fun coordinate _ =>
    integrable_testMul test (regular coordinate)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun place => by
    simp [Finset.mul_sum])

/--
**The balance names the pressure gradient.**

`state` is the scalar whose gradient the balance leaves over --- the pressure.
Reading the balance in the coordinate `coordinate` and integrating by parts in
each derivative turns it into a representation of `∂ p` by an explicit function
of the velocity and the forcing.

Every hypothesis is either the equation itself or regularity of the velocity on
the domain.  Nothing is inverted, estimated, or assembled from windows.
-/
theorem represents_lineDeriv_of_balance
    (velocity forcing : 𝓓'(domain, Value)) (state : 𝓓'(domain, ℝ))
    {velocityField forcingField : Point → Value}
    (reader : Index → (Value →L[ℝ] ℝ))
    (timeDirection : Point) (spatialDirection : Index → Point)
    (velocityRepresents : ∀ test : 𝓓(domain, ℝ),
      velocity test = ∫ place, test place • velocityField place ∂μ)
    (forcingRepresents : ∀ test : 𝓓(domain, ℝ),
      forcing test = ∫ place, test place • forcingField place ∂μ)
    (velocitySmooth : ContDiffOn ℝ ∞ velocityField domain)
    (forcingContinuous : ContinuousOn forcingField domain)
    (momentum : ∀ (test : 𝓓(domain, ℝ)) (coordinate : Index),
      reader coordinate
          ((Distribution.lineDerivCLM timeDirection velocity :
            𝓓'(domain, Value)) test) -
          reader coordinate
            ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
                𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
                  ((Distribution.lineDerivCLM (spatialDirection axis) :
                    𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity)) test) +
          (Distribution.lineDerivCLM (spatialDirection coordinate) state :
            𝓓'(domain, ℝ)) test =
        reader coordinate (forcing test))
    (test : 𝓓(domain, ℝ)) (coordinate : Index) :
    (Distribution.lineDerivCLM (spatialDirection coordinate) state :
        𝓓'(domain, ℝ)) test =
      ∫ place, test place *
        (reader coordinate (forcingField place) -
          lineDeriv ℝ (fun position => reader coordinate (velocityField position))
            place timeDirection +
          ∑ axis : Index,
            lineDeriv ℝ (fun position =>
                lineDeriv ℝ (fun origin => reader coordinate (velocityField origin))
                  position (spatialDirection axis))
              place (spatialDirection axis)) ∂μ := by
  classical
  -- The coordinate of the velocity, and its regularity.
  set component : Point → ℝ :=
    fun position => reader coordinate (velocityField position) with component_def
  have componentSmooth : ContDiffOn ℝ ∞ component domain :=
    (reader coordinate).contDiff.comp_contDiffOn velocitySmooth
  have componentContinuous : ContinuousOn component domain :=
    componentSmooth.continuousOn
  have componentRepresents : ∀ test : 𝓓(domain, ℝ),
      (Distribution.mapCLM (reader coordinate) velocity : 𝓓'(domain, ℝ)) test =
        ∫ place, test place * component place ∂μ := fun test =>
    represents_mapCLM (reader coordinate) velocity velocitySmooth.continuousOn
      velocityRepresents test
  -- The time derivative, read in this coordinate.
  have timeTerm : ∀ test : 𝓓(domain, ℝ),
      reader coordinate
          ((Distribution.lineDerivCLM timeDirection velocity :
            𝓓'(domain, Value)) test) =
        ∫ place, test place * lineDeriv ℝ component place timeDirection ∂μ := by
    intro test
    have commute := mapCLM_lineDerivCLM (reader coordinate) velocity timeDirection test
    rw [Distribution.mapCLM_apply] at commute
    rw [commute]
    exact represents_lineDeriv (μ := μ) _ componentRepresents componentSmooth
      timeDirection test
  -- Each second spatial derivative, read in this coordinate.
  have spatialTerm : ∀ (test : 𝓓(domain, ℝ)) (axis : Index),
      reader coordinate
          ((Distribution.lineDerivCLM (spatialDirection axis) :
              𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
            ((Distribution.lineDerivCLM (spatialDirection axis) :
              𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity) test) =
        ∫ place, test place *
          lineDeriv ℝ (fun position =>
              lineDeriv ℝ component position (spatialDirection axis))
            place (spatialDirection axis) ∂μ := by
    intro test axis
    have firstRepresents : ∀ test : 𝓓(domain, ℝ),
        (Distribution.mapCLM (reader coordinate)
            ((Distribution.lineDerivCLM (spatialDirection axis) :
              𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity) :
              𝓓'(domain, ℝ)) test =
          ∫ place, test place *
            lineDeriv ℝ component place (spatialDirection axis) ∂μ := by
      intro test
      have commute :=
        mapCLM_lineDerivCLM (reader coordinate) velocity (spatialDirection axis) test
      rw [Distribution.mapCLM_apply] at commute
      rw [Distribution.mapCLM_apply, commute]
      exact represents_lineDeriv (μ := μ) _ componentRepresents componentSmooth
        (spatialDirection axis) test
    have commute :=
      mapCLM_lineDerivCLM (reader coordinate)
        ((Distribution.lineDerivCLM (spatialDirection axis) :
          𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity)
        (spatialDirection axis) test
    rw [Distribution.mapCLM_apply] at commute
    rw [commute]
    exact represents_lineDeriv (μ := μ) _ firstRepresents
      (contDiffOn_lineDeriv componentSmooth (spatialDirection axis))
      (spatialDirection axis) test
  -- The forcing, read in this coordinate.
  have forcingTerm :
      reader coordinate (forcing test) =
        ∫ place, test place * reader coordinate (forcingField place) ∂μ := by
    have := represents_mapCLM (reader coordinate) forcing forcingContinuous
      forcingRepresents test
    rwa [Distribution.mapCLM_apply] at this
  -- The Laplacian is the sum of its coordinates.
  have laplacianTerm :
      reader coordinate
          ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
              𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
                ((Distribution.lineDerivCLM (spatialDirection axis) :
                  𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity)) test) =
        ∫ place, test place *
          (∑ axis : Index,
            lineDeriv ℝ (fun position =>
                lineDeriv ℝ component position (spatialDirection axis))
              place (spatialDirection axis)) ∂μ := by
    rw [← integral_testMul_finsetSum (μ := μ) test _ Finset.univ fun axis =>
      (contDiffOn_lineDeriv
        (contDiffOn_lineDeriv componentSmooth (spatialDirection axis))
        (spatialDirection axis)).continuousOn]
    have expand :
        ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
            𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
              ((Distribution.lineDerivCLM (spatialDirection axis) :
                𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity)) test) =
          ∑ axis : Index,
            ((Distribution.lineDerivCLM (spatialDirection axis) :
              𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
                ((Distribution.lineDerivCLM (spatialDirection axis) :
                  𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity) test) := by
      simp
    rw [expand, map_sum]
    exact Finset.sum_congr rfl fun axis _ => spatialTerm test axis
  -- Solve the balance for the pressure term.
  have balance := momentum test coordinate
  rw [timeTerm test, laplacianTerm, forcingTerm] at balance
  have integrableForcing :
      Integrable
        (fun place => test place * reader coordinate (forcingField place)) μ :=
    integrable_testMul test
      ((reader coordinate).continuous.comp_continuousOn forcingContinuous)
  have integrableTime :
      Integrable
        (fun place => test place * lineDeriv ℝ component place timeDirection) μ :=
    integrable_testMul test (continuousOn_lineDeriv componentSmooth timeDirection)
  have integrableLaplacian :
      Integrable
        (fun place => test place *
          (∑ axis : Index,
            lineDeriv ℝ (fun position =>
                lineDeriv ℝ component position (spatialDirection axis))
              place (spatialDirection axis))) μ := by
    refine integrable_testMul test (continuousOn_finset_sum _ fun axis _ => ?_)
    exact (contDiffOn_lineDeriv
      (contDiffOn_lineDeriv componentSmooth (spatialDirection axis))
      (spatialDirection axis)).continuousOn
  have combine :
      ∫ place, test place *
          (reader coordinate (forcingField place) -
            lineDeriv ℝ component place timeDirection +
            ∑ axis : Index,
              lineDeriv ℝ (fun position =>
                  lineDeriv ℝ component position (spatialDirection axis))
                place (spatialDirection axis)) ∂μ =
        ∫ place, test place * reader coordinate (forcingField place) ∂μ -
            ∫ place, test place * lineDeriv ℝ component place timeDirection ∂μ +
          ∫ place, test place *
            (∑ axis : Index,
              lineDeriv ℝ (fun position =>
                  lineDeriv ℝ component position (spatialDirection axis))
                place (spatialDirection axis)) ∂μ := by
    have split :
        ∫ place, test place *
            (reader coordinate (forcingField place) -
              lineDeriv ℝ component place timeDirection +
              ∑ axis : Index,
                lineDeriv ℝ (fun position =>
                    lineDeriv ℝ component position (spatialDirection axis))
                  place (spatialDirection axis)) ∂μ =
          ∫ place,
            (test place * reader coordinate (forcingField place) -
                test place * lineDeriv ℝ component place timeDirection) +
              test place *
                (∑ axis : Index,
                  lineDeriv ℝ (fun position =>
                      lineDeriv ℝ component position (spatialDirection axis))
                    place (spatialDirection axis)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun place => by ring)
    have integrableDifference :
        Integrable (fun place =>
          test place * reader coordinate (forcingField place) -
            test place * lineDeriv ℝ component place timeDirection) μ :=
      integrableForcing.sub integrableTime
    rw [split, integral_add integrableDifference integrableLaplacian,
      integral_sub integrableForcing integrableTime]
  rw [combine]
  linarith [balance]

/-- Two weights that agree on the domain pair identically with every test
function of that domain: outside the domain the test function vanishes. -/
theorem integral_testMul_congr (test : 𝓓(domain, ℝ)) {left right : Point → ℝ}
    (agree : ∀ place ∈ domain, left place = right place) :
    ∫ place, test place * left place ∂μ =
      ∫ place, test place * right place ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun place => ?_)
  show test place * left place = test place * right place
  by_cases mem : place ∈ domain
  · rw [agree place mem]
  · have notSupport : place ∉ tsupport (⇑test) := fun support =>
      mem (test.tsupport_subset support)
    rw [image_eq_zero_of_notMem_tsupport notSupport]
    simp

/--
**The admissibility discharge of a represented balance.**

The form the exhaustive local closure consumes: any witness that agrees with the
balance's own gradient *on the domain* represents the remaining term.  The
agreement hypothesis is exactly what `LocalAdmissibility.ofGerm` produces from
germ agreement at the relevant points, so an application supplies no proof and
no global fact --- only the equation it already carries.
-/
theorem represents_lineDeriv_of_balance_of_eqOn
    (velocity forcing : 𝓓'(domain, Value)) (state : 𝓓'(domain, ℝ))
    {velocityField forcingField gradientField witness : Point → Value}
    (reader : Index → (Value →L[ℝ] ℝ))
    (timeDirection : Point) (spatialDirection : Index → Point)
    (velocityRepresents : ∀ test : 𝓓(domain, ℝ),
      velocity test = ∫ place, test place • velocityField place ∂μ)
    (forcingRepresents : ∀ test : 𝓓(domain, ℝ),
      forcing test = ∫ place, test place • forcingField place ∂μ)
    (velocitySmooth : ContDiffOn ℝ ∞ velocityField domain)
    (forcingContinuous : ContinuousOn forcingField domain)
    (momentum : ∀ (test : 𝓓(domain, ℝ)) (coordinate : Index),
      reader coordinate
          ((Distribution.lineDerivCLM timeDirection velocity :
            𝓓'(domain, Value)) test) -
          reader coordinate
            ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
                𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
                  ((Distribution.lineDerivCLM (spatialDirection axis) :
                    𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity)) test) +
          (Distribution.lineDerivCLM (spatialDirection coordinate) state :
            𝓓'(domain, ℝ)) test =
        reader coordinate (forcing test))
    (gradient : ∀ (place : Point) (coordinate : Index),
      reader coordinate (gradientField place) =
        reader coordinate (forcingField place) -
          lineDeriv ℝ (fun position => reader coordinate (velocityField position))
            place timeDirection +
          ∑ axis : Index,
            lineDeriv ℝ (fun position =>
                lineDeriv ℝ (fun origin => reader coordinate (velocityField origin))
                  position (spatialDirection axis))
              place (spatialDirection axis))
    (agree : ∀ place ∈ domain, witness place = gradientField place)
    (test : 𝓓(domain, ℝ)) (coordinate : Index) :
    (Distribution.lineDerivCLM (spatialDirection coordinate) state :
        𝓓'(domain, ℝ)) test =
      ∫ place, test place * reader coordinate (witness place) ∂μ := by
  rw [represents_lineDeriv_of_balance velocity forcing state reader timeDirection
    spatialDirection velocityRepresents forcingRepresents velocitySmooth
    forcingContinuous momentum test coordinate]
  refine (integral_testMul_congr test fun place mem => ?_).symm
  rw [agree place mem, gradient place coordinate]

/-! ## The balance-named gradient is smooth

`represents_lineDeriv_of_balance` says *which* function represents the pressure
gradient; this section says that function is smooth whenever the velocity and
the forcing are.  Together they are the whole of
`stokes:lem:pressure-normalization` in the distributional setting: the equation
determines the gradient, and the regularity of the data is inherited by it,
because everything the balance leaves over is a line derivative of something
already smooth.
-/

/-- **The field the balance names**, `f − ∂_t u + Δ_x u`, read in one
coordinate.  It is a definition, not a claim: this is the expression the
momentum identity leaves over. -/
noncomputable def balanceGradient
    (reader : Index → (Value →L[ℝ] ℝ)) (timeDirection : Point)
    (spatialDirection : Index → Point)
    (velocityField forcingField : Point → Value)
    (place : Point) (coordinate : Index) : ℝ :=
  reader coordinate (forcingField place) -
    lineDeriv ℝ (fun position => reader coordinate (velocityField position))
      place timeDirection +
    ∑ axis : Index,
      lineDeriv ℝ (fun position =>
          lineDeriv ℝ (fun origin => reader coordinate (velocityField origin))
            position (spatialDirection axis))
        place (spatialDirection axis)

/--
**The balance-named gradient is smooth on the domain.**

Each summand is a line derivative of a smooth function, so
`contDiffOn_lineDeriv` applies twice; the finite sum and the difference are
closure properties of `ContDiffOn`.  Nothing is estimated.
-/
theorem contDiffOn_balanceGradient
    (reader : Index → (Value →L[ℝ] ℝ)) (timeDirection : Point)
    (spatialDirection : Index → Point)
    {velocityField forcingField : Point → Value}
    (velocitySmooth : ContDiffOn ℝ ∞ velocityField domain)
    (forcingSmooth : ContDiffOn ℝ ∞ forcingField domain)
    (coordinate : Index) :
    ContDiffOn ℝ ∞ (fun place =>
      balanceGradient reader timeDirection spatialDirection velocityField
        forcingField place coordinate) domain := by
  have component : ContDiffOn ℝ ∞
      (fun position => reader coordinate (velocityField position)) domain :=
    (reader coordinate).contDiff.comp_contDiffOn velocitySmooth
  have source : ContDiffOn ℝ ∞
      (fun place => reader coordinate (forcingField place)) domain :=
    (reader coordinate).contDiff.comp_contDiffOn forcingSmooth
  have timePart : ContDiffOn ℝ ∞
      (fun place => lineDeriv ℝ
        (fun position => reader coordinate (velocityField position))
        place timeDirection) domain :=
    contDiffOn_lineDeriv component timeDirection
  have spatialPart : ∀ axis : Index, ContDiffOn ℝ ∞
      (fun place => lineDeriv ℝ (fun position =>
          lineDeriv ℝ (fun origin => reader coordinate (velocityField origin))
            position (spatialDirection axis))
        place (spatialDirection axis)) domain := fun axis =>
    contDiffOn_lineDeriv
      (contDiffOn_lineDeriv component (spatialDirection axis))
      (spatialDirection axis)
  exact (source.sub timePart).add
    (ContDiffOn.sum fun axis _ => spatialPart axis)

/--
**The pressure gradient of a balanced system is represented by a smooth
field.**

This is the bridge a localization needs: from the equation and regularity of
the data alone, the gradient the balance names both *represents* the
distributional gradient and *is smooth*.  It is the exact shape a registered
regularity target asks for, and it is proved once here rather than by every
application.
-/
theorem exists_contDiffOn_representative_of_balance
    [IsFiniteMeasureOnCompacts μ]
    (velocity forcing : 𝓓'(domain, Value)) (state : 𝓓'(domain, ℝ))
    {velocityField forcingField : Point → Value}
    (reader : Index → (Value →L[ℝ] ℝ))
    (timeDirection : Point) (spatialDirection : Index → Point)
    (velocityRepresents : ∀ test : 𝓓(domain, ℝ),
      velocity test = ∫ place, test place • velocityField place ∂μ)
    (forcingRepresents : ∀ test : 𝓓(domain, ℝ),
      forcing test = ∫ place, test place • forcingField place ∂μ)
    (velocitySmooth : ContDiffOn ℝ ∞ velocityField domain)
    (forcingSmooth : ContDiffOn ℝ ∞ forcingField domain)
    (momentum : ∀ (test : 𝓓(domain, ℝ)) (coordinate : Index),
      reader coordinate
          ((Distribution.lineDerivCLM timeDirection velocity :
            𝓓'(domain, Value)) test) -
          reader coordinate
            ((∑ axis : Index, (Distribution.lineDerivCLM (spatialDirection axis) :
                𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value))
                  ((Distribution.lineDerivCLM (spatialDirection axis) :
                    𝓓'(domain, Value) →L[ℝ] 𝓓'(domain, Value)) velocity)) test) +
          (Distribution.lineDerivCLM (spatialDirection coordinate) state :
            𝓓'(domain, ℝ)) test =
        reader coordinate (forcing test)) :
    ∃ gradientField : Point → Index → ℝ,
      (∀ coordinate : Index,
        ContDiffOn ℝ ∞ (fun place => gradientField place coordinate) domain) ∧
      ∀ (test : 𝓓(domain, ℝ)) (coordinate : Index),
        (Distribution.lineDerivCLM (spatialDirection coordinate) state :
            𝓓'(domain, ℝ)) test =
          ∫ place, test place * gradientField place coordinate ∂μ :=
  ⟨balanceGradient reader timeDirection spatialDirection velocityField forcingField,
    fun coordinate =>
      contDiffOn_balanceGradient reader timeDirection spatialDirection
        velocitySmooth forcingSmooth coordinate,
    fun test coordinate =>
      represents_lineDeriv_of_balance velocity forcing state reader timeDirection
        spatialDirection velocityRepresents forcingRepresents velocitySmooth
        forcingSmooth.continuousOn momentum test coordinate⟩

end Balance

end Hypostructure.PDE.Distribution
