import Hypostructure.PDE.Localization.Cutoff
import Hypostructure.PDE.Solution.EllipticRegularity

/-!
# Carrying a local residual into the tempered distributions

This is the `ζ` step of a Calderón--Zygmund decomposition, done once for the
framework.

A local residual knows its source only on its own window.  The solution
operator that produces the local term is a whole-space operator, so before it
can be applied the source has to be cut off and carried out of the window.
That is exactly what the classical statement does:

> `P_loc = (-Δ)^{-1} ∂_i∂_j(ζ V_i V_j)` in `ℝ³`, where `ζ ∈ C_c^∞(B_R)` equals
> one on `B_r`

and it is the reason the decomposition needs no boundary condition and no
inverse on the window: the solve happens on the whole space, against a source
that has been made compactly supported.

The two facts that make the argument work are proved here, generically:

* `memLp_cutoffSmul` — a source that is `L^p` *on its own window* becomes
  globally `L^p` once cut off, so it defines a tempered distribution.  This is
  the step the classical proof records as "since `ζ V_i V_j ∈ L^{3/2}(ℝ³)`".
* `cutoffSmul_eq_of_mem` — on the inner window the cut-off source **is** the
  original source.  This is what makes the complementary term annihilated
  there, since the two sources agree wherever `ζ ≡ 1`.

Nothing here names an equation, a dimension or a problem.
-/

namespace Hypostructure.PDE.Localization

open MeasureTheory Metric
open scoped ENNReal SchwartzMap

universe uPoint

variable {Point : Type*} {Value : Type*}
  [NormedAddCommGroup Point] [NormedSpace ℝ Point] [HasContDiffBump Point]
  [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/-- The cut-off source: the residual's own source, multiplied by the window's
cutoff.  This is `ζ V` of the classical statement. -/
noncomputable def cutoffSmul (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → Value) :
    Point → Value :=
  fun place => cutoff center inner_pos nested place • weight place

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- On the inner window the cut-off source is the original source: the cutoff
is one there.  Nothing the residual knew about its own source is lost. -/
theorem cutoffSmul_eq_of_mem (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → Value)
    {place : Point} (mem : place ∈ closedBall center inner) :
    cutoffSmul center inner_pos nested weight place = weight place := by
  simp [cutoffSmul, cutoff_eq_one center inner_pos nested mem]

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The cut-off source vanishes off the outer window. -/
theorem cutoffSmul_eq_zero (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → Value)
    {place : Point} (outside : place ∉ ball center outer) :
    cutoffSmul center inner_pos nested weight place = 0 := by
  have vanishes : cutoff center inner_pos nested place = 0 := by
    by_contra nonzero
    exact outside (by
      rw [← cutoff_support center inner_pos nested]
      exact nonzero)
  simp [cutoffSmul, vanishes]

omit [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point] in
/-- The cut-off source is dominated by the source restricted to the window.
This is the pointwise bound behind the `L^p` statement below. -/
theorem norm_cutoffSmul_le (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → Value)
    (place : Point) :
    ‖cutoffSmul center inner_pos nested weight place‖ ≤
      ‖(ball center outer).indicator weight place‖ := by
  by_cases mem : place ∈ ball center outer
  · rw [Set.indicator_of_mem mem]
    have nonneg : 0 ≤ cutoff center inner_pos nested place :=
      (cutoffBump center inner_pos nested).nonneg
    have le_one : cutoff center inner_pos nested place ≤ 1 :=
      (cutoffBump center inner_pos nested).le_one
    have bound : ‖cutoff center inner_pos nested place‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg nonneg]
      exact le_one
    calc ‖cutoffSmul center inner_pos nested weight place‖
        = ‖cutoff center inner_pos nested place‖ * ‖weight place‖ := by
          simp [cutoffSmul, norm_smul]
      _ ≤ 1 * ‖weight place‖ := by gcongr
      _ = ‖weight place‖ := one_mul _
  · rw [Set.indicator_of_notMem mem,
      cutoffSmul_eq_zero center inner_pos nested weight mem]

/-! ## The residual becomes a global `L^p` source

This is the step the classical argument states in one clause.  A residual that
controls its source only on its own window controls the cut-off source
everywhere, because the cutoff kills whatever lies outside.
-/

variable {μ : Measure Point} {exponent : ℝ≥0∞}

omit [FiniteDimensional ℝ Point] in
/--
A source that is `L^p` on its own window is globally `L^p` once cut off.

This is what lets a *local* residual be handed to a *whole-space* solution
operator, which is the whole mechanism of the classical decomposition.
-/
theorem memLp_cutoffSmul (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {weight : Point → Value}
    (windowed : MemLp weight exponent (μ.restrict (ball center outer)))
    (measurable :
      AEStronglyMeasurable (cutoffSmul center inner_pos nested weight) μ) :
    MemLp (cutoffSmul center inner_pos nested weight) exponent μ := by
  have indicator_memLp :
      MemLp ((ball center outer).indicator weight) exponent μ :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr windowed
  refine indicator_memLp.of_le measurable (.of_forall ?_)
  exact norm_cutoffSmul_le center inner_pos nested weight

/-! ## The complementary term is annihilated on the inner window

This is the engine of a localized Calderon--Zygmund decomposition, and it is
the whole proof of the classical lemma:

> `Delta(p - p_CZ) = div f - div(chi f) = div((1 - chi) f)`, and the right side
> vanishes on the inner window because `chi = 1` there.

Nothing is inverted and nothing is estimated.  The local term is *defined* as
a solve against the cut-off source; the complementary term is then annihilated
wherever the cutoff is one, because there the two sources are the same
function.  That is `cutoffSmul_eq_of_mem` and nothing else.
-/

section Annihilation

variable {Point : Type*} {Value : Type*}
  [NormedAddCommGroup Point] [NormedSpace ℝ Point] [HasContDiffBump Point]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/--
**The complementary term is annihilated on the inner window.**

`component` satisfies the equation with source `source`; `localTerm` is a
solve against the *cut-off* source.  On the inner window the two sources
agree, so the operator kills the difference there.

This is stated for any additive operator, so it applies to the spatial
Laplacian of a pressure decomposition, to a heat operator, or to anything else
a model names.  No problem supplies a proof: it hands over its equation and
its solve, and the annihilation is derived.
-/
theorem sub_annihilated_of_mem
    {operator : (Point → Value) → (Point → Value)}
    (subtractive : ∀ first second,
      operator (first - second) = operator first - operator second)
    {component localTerm source : Point → Value}
    (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer)
    (equation : operator component = source)
    (solved :
      operator localTerm = cutoffSmul center inner_pos nested source)
    {place : Point} (mem : place ∈ closedBall center inner) :
    operator (component - localTerm) place = 0 := by
  rw [subtractive, equation, solved]
  simp [cutoffSmul_eq_of_mem center inner_pos nested source mem]

omit [NormedAddCommGroup Point] [NormedSpace ℝ Point] [HasContDiffBump Point]
  [NormedSpace ℝ Value] in
/--
The split itself: the component is the local term plus the complementary term,
by construction.  Together with `sub_annihilated_of_mem` this is the local
pressure decomposition `p = p_CZ + p_har`, with `p_har` annihilated on the
inner window.
-/
theorem add_sub_cancel_split (component localTerm : Point → Value) :
    localTerm + (component - localTerm) = component :=
  add_sub_cancel _ _

/--
**Pressure closure, read forwards.**

Once the other terms of the equation are known, the remaining term is
determined by the equation itself — no inversion, no estimate, no potential.
This is the step

> `grad p = f - d_t u + Laplacian u`

of the classical local Stokes argument: the equation that was used to *derive*
the decomposition is then read in the other direction to close it.

It is stated for an arbitrary balance of terms, so any model that names an
equation gets the closure of its last term for free.
-/
theorem closure_of_balance {Term : Type*} [AddCommGroup Term]
    {forcing evolution diffusion gradient : Term}
    (equation : evolution - diffusion + gradient = forcing) :
    gradient = forcing - evolution + diffusion := by
  rw [← equation]
  abel

end Annihilation

/-! ## The local residual as a tempered distribution

With the source made globally `L^p`, mathlib's `Lp.toTemperedDistributionCLM`
carries it into `𝓢'`, which is where the framework's solution library — the
exact graded inverse of `PDE/Solution/Bessel.lean` — acts.  This completes the
handover: a residual that knew its source only on a window is now an argument
the whole-space solve accepts.
-/

section Tempered

open TemperedDistribution

variable {Point : Type*} {Value : Type*}
  [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [HasContDiffBump Point]
  [MeasurableSpace Point] [BorelSpace Point] [FiniteDimensional ℝ Point]
  [SecondCountableTopology Point]
  [NormedAddCommGroup Value] [NormedSpace ℂ Value] [CompleteSpace Value]
  {μ : Measure Point} [μ.HasTemperateGrowth]
  {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]

/--
The cut-off source as a tempered distribution.

This is the framework's handover point.  The application names a window and a
source; the framework cuts the source off, checks it is globally `L^p`, and
produces the tempered distribution the solution library consumes.  No problem
supplies anything beyond its own source.
-/
noncomputable def temperedSource (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {weight : Point → Value}
    (windowed : MemLp weight exponent (μ.restrict (ball center outer)))
    (measurable :
      AEStronglyMeasurable (cutoffSmul center inner_pos nested weight) μ) :
    𝓢'(Point, Value) :=
  Lp.toTemperedDistributionCLM Value μ exponent
    ((memLp_cutoffSmul center inner_pos nested windowed measurable).toLp _)

end Tempered

end Hypostructure.PDE.Localization
