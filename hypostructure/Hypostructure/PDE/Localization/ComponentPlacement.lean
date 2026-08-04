import Hypostructure.PDE.Localization.PlacementOfBaseline
import Hypostructure.PDE.Solution.InteriorRegularity

/-!
# Placing the scalar components of a vector-valued local reading

A local regularity problem carries its field as **one** vector-valued reading,
`𝓓'(domain, Vector)`.  The framework's interior bootstrap carries **three**
scalar readings, `Fin 3 → 𝓢'(Point, ℂ)`, because that is the shape the
rotational operator and the heat operator are written in.

This module is the passage between the two, and it is entirely plumbing:

* `componentDatum` reads one real coordinate through the problem's own `reader`
  and complexifies it, so no new geometry and no choice of basis appears;
* `componentPlacement` hands that scalar reading to
  `SquareIntegrablePlacement.ofRepresentative`, whose `MemLp … 2` hypothesis is
  the local `L²` bound the baseline already pins;
* `sobolevOn_componentPlacement` reads off the Sobolev grade through
  `sobolevOn_of_memSobolev_zero`, so the grade comes from the local `L²` bound
  and never from a decay property of a Fourier transform.

Nothing here is global.  Every statement is about one window inside the
reading's own domain, and no equation, dimension or problem is named.
-/

namespace Hypostructure.PDE.Localization

open MeasureTheory Metric TopologicalSpace TemperedDistribution
open Hypostructure.PDE.Solution.InteriorRegularity
open scoped Distributions SchwartzMap ENNReal

variable {Point : Type} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [HasContDiffBump Point]
  {Vector : Type} [NormedAddCommGroup Vector] [NormedSpace ℝ Vector]
  [CompleteSpace Vector]
  {domain : Opens Point}

/-- One real coordinate of a vector value, complexified.  The real part is the
problem's own `reader`; the complexification is forced by the bootstrap, whose
Sobolev scale is built on the Fourier transform. -/
noncomputable def componentReader (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (index : Fin 3) : Vector →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (reader index)

@[simp] theorem componentReader_apply (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (index : Fin 3) (value : Vector) :
    componentReader reader index value = (reader index value : ℂ) := rfl

/-- The `index`-th scalar component of a vector-valued local reading. -/
noncomputable def componentDatum (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (datum : 𝓓'(domain, Vector)) (index : Fin 3) : 𝓓'(domain, ℂ) :=
  Distribution.mapCLM (componentReader reader index) datum

@[simp] theorem componentDatum_apply (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (datum : 𝓓'(domain, Vector)) (index : Fin 3) (test : 𝓓(domain, ℝ)) :
    componentDatum reader datum index test =
      (reader index (datum test) : ℂ) := rfl

/-- The `index`-th scalar component of a vector-valued weight. -/
noncomputable def componentWeight (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (weight : Point → Vector) (index : Fin 3) : Point → ℂ :=
  fun place => (reader index (weight place) : ℂ)

theorem aestronglyMeasurable_componentWeight
    (reader : Fin 3 → (Vector →L[ℝ] ℝ)) {weight : Point → Vector} {μ : Measure Point}
    (measurable : AEStronglyMeasurable weight μ) (index : Fin 3) :
    AEStronglyMeasurable (componentWeight reader weight index) μ :=
  (componentReader reader index).continuous.comp_aestronglyMeasurable measurable

/-- Reading a coordinate is a bounded operation, so it cannot leave `L²`.  This
is what lets the baseline's single vector-valued `L²` bound serve all three
scalar components. -/
theorem memLp_componentWeight (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    {weight : Point → Vector} {μ : Measure Point}
    (windowed : MemLp weight 2 μ) (index : Fin 3) :
    MemLp (componentWeight reader weight index) 2 μ := by
  refine MemLp.mono' (g := fun place => ‖componentReader reader index‖ * ‖weight place‖)
    (windowed.norm.const_mul _)
    (aestronglyMeasurable_componentWeight reader windowed.1 index)
    (Filter.Eventually.of_forall fun place => ?_)
  exact (componentReader reader index).le_opNorm (weight place)

/-- Reading a coordinate commutes with the representing integral.  The only
content is `ContinuousLinearMap.integral_comp_comm`; the integrability it needs
is the one the representation already presupposes. -/
theorem represents_componentWeight (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    {datum : 𝓓'(domain, Vector)} {weight : Point → Vector}
    (integrable : ∀ test : 𝓓(domain, ℝ),
      Integrable (fun place => test place • weight place) (volume : Measure Point))
    (represents : ∀ test : 𝓓(domain, ℝ),
      datum test = ∫ place, test place • weight place ∂(volume : Measure Point))
    (index : Fin 3) (test : 𝓓(domain, ℝ)) :
    componentDatum reader datum index test =
      ∫ place, test place • componentWeight reader weight index place
        ∂(volume : Measure Point) := by
  have unfold : componentDatum reader datum index test =
      componentReader reader index (datum test) := rfl
  rw [unfold, represents test,
    ← ContinuousLinearMap.integral_comp_comm (componentReader reader index)
      (integrable test)]
  congr 1
  funext place
  simp [componentWeight]

/-- **The placement of one scalar component of a vector-valued local reading.**

Zero new analysis: the window, the containment and the representation are the
caller's own, and the `L²` bound is the vector-valued one read through a bounded
coordinate map. -/
noncomputable def componentPlacement (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (window : Bessel.Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Vector)) {weight : Point → Vector}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius)))
    (integrable : ∀ test : 𝓓(domain, ℝ),
      Integrable (fun place => test place • weight place) (volume : Measure Point))
    (represents : ∀ test : 𝓓(domain, ℝ),
      datum test = ∫ place, test place • weight place ∂(volume : Measure Point))
    (index : Fin 3) : SquareIntegrablePlacement Point ℂ :=
  SquareIntegrablePlacement.ofRepresentative window inside
    (componentDatum reader datum index)
    (aestronglyMeasurable_componentWeight reader measurable index)
    (memLp_componentWeight reader windowed index)
    (represents_componentWeight reader integrable represents index)

/-- **The component's placed state sits at Sobolev grade zero on every region.**

This is the input the interior bootstrap asks for, obtained from the local `L²`
bound alone.  It is the last link between a problem's vector-valued reading and
`ParabolicRegularity`'s scalar machinery. -/
theorem sobolevOn_componentPlacement (reader : Fin 3 → (Vector →L[ℝ] ℝ))
    (window : Bessel.Window Point) (inside : (window.support : Set Point) ⊆ domain)
    (datum : 𝓓'(domain, Vector)) {weight : Point → Vector}
    (measurable : AEStronglyMeasurable weight (volume : Measure Point))
    (windowed : MemLp weight 2
      ((volume : Measure Point).restrict (ball window.centre window.outerRadius)))
    (integrable : ∀ test : 𝓓(domain, ℝ),
      Integrable (fun place => test place • weight place) (volume : Measure Point))
    (represents : ∀ test : 𝓓(domain, ℝ),
      datum test = ∫ place, test place • weight place ∂(volume : Measure Point))
    (index : Fin 3) (region : Set Point) :
    Hypostructure.PDE.Solution.InteriorRegularity.SobolevOn region 0
      (componentPlacement reader window inside datum measurable windowed integrable
        represents index).state :=
  Hypostructure.PDE.Solution.InteriorRegularity.sobolevOn_of_memSobolev_zero
    (SquareIntegrablePlacement.memSobolev_zero _)

end Hypostructure.PDE.Localization
