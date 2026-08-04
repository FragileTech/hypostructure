import Hypostructure.PDE.Distribution.OfFunction

/-!
# Smooth cutoffs on nested windows

Cutting a local quantity off is the other half of the localization plumbing.
A solution operator, a potential, or an integration by parts wants a
*compactly supported* source; what the residual hands over is a quantity
defined on a window.  The standard fix is to multiply by a smooth cutoff that
is one on the inner window and vanishes outside the outer one.

mathlib supplies the bump function (`ContDiffBump`); this module packages it
for the framework, and — the part that is actually reusable — records the
three consequences every localization argument then needs:

* the cut-off weight is still locally integrable;
* it is compactly supported;
* so it defines a distribution through `ofLocallyIntegrable`, and pairs
  integrably against any test function.

Nothing here is equation specific and nothing is assumed.
-/

namespace Hypostructure.PDE.Localization

open MeasureTheory Metric

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [NormedSpace ℝ Point] [HasContDiffBump Point]

/-- The smooth cutoff of a nested pair of concentric windows: one on the
inner ball, supported in the outer. -/
noncomputable def cutoffBump (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) : ContDiffBump center :=
  { rIn := inner, rOut := outer, rIn_pos := inner_pos, rIn_lt_rOut := nested }

/-- The cutoff as a plain function. -/
noncomputable def cutoff (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) : Point → ℝ :=
  ⇑(cutoffBump center inner_pos nested)

theorem cutoff_contDiff (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (cutoff center inner_pos nested) :=
  (cutoffBump center inner_pos nested).contDiff

/-- The cutoff is one on the inner window: a fact stated there survives
being cut off. -/
theorem cutoff_eq_one (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {place : Point}
    (mem : place ∈ closedBall center inner) :
    cutoff center inner_pos nested place = 1 :=
  (cutoffBump center inner_pos nested).one_of_mem_closedBall mem

/-- The cutoff vanishes off the outer window. -/
theorem cutoff_support (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) :
    Function.support (cutoff center inner_pos nested) = ball center outer :=
  (cutoffBump center inner_pos nested).support_eq

theorem cutoff_hasCompactSupport [FiniteDimensional ℝ Point]
    (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) :
    HasCompactSupport (cutoff center inner_pos nested) :=
  (cutoffBump center inner_pos nested).hasCompactSupport

/-! ## Cutting off a weight

This is what the plumbing is for: whatever the residual hands over, the
cut-off version is compactly supported and still locally integrable, so every
downstream tool applies to it without further hypotheses.
-/

variable [MeasurableSpace Point] [OpensMeasurableSpace Point]
  {μ : Measure Point}

/-- The cut-off weight. -/
noncomputable def cutoffWeight (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → ℝ) :
    Point → ℝ :=
  fun place => cutoff center inner_pos nested place * weight place

/-- The cut-off weight is integrable outright, not merely locally: this is
the hypothesis a potential or an integration by parts wants. -/
theorem integrable_cutoffWeight [FiniteDimensional ℝ Point]
    (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {weight : Point → ℝ}
    (locallyIntegrable : LocallyIntegrable weight μ) :
    Integrable (cutoffWeight center inner_pos nested weight) μ :=
  locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    (cutoff_contDiff center inner_pos nested).continuous
    (cutoff_hasCompactSupport center inner_pos nested)

/-- Cutting off preserves local integrability. -/
theorem locallyIntegrable_cutoffWeight [FiniteDimensional ℝ Point]
    (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) {weight : Point → ℝ}
    (locallyIntegrable : LocallyIntegrable weight μ) :
    LocallyIntegrable (cutoffWeight center inner_pos nested weight) μ :=
  (integrable_cutoffWeight center inner_pos nested
    locallyIntegrable).locallyIntegrable

/-- Cutting off makes a weight compactly supported. -/
theorem hasCompactSupport_cutoffWeight [FiniteDimensional ℝ Point]
    (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → ℝ) :
    HasCompactSupport (cutoffWeight center inner_pos nested weight) :=
  (cutoff_hasCompactSupport center inner_pos nested).mul_right

/-- On the inner window the cut-off weight is the original one, so nothing a
residual knew about its own source is lost by cutting off. -/
theorem cutoffWeight_eq_of_mem (center : Point) {inner outer : ℝ}
    (inner_pos : 0 < inner) (nested : inner < outer) (weight : Point → ℝ)
    {place : Point} (mem : place ∈ closedBall center inner) :
    cutoffWeight center inner_pos nested weight place = weight place := by
  simp [cutoffWeight, cutoff_eq_one center inner_pos nested mem]

end Hypostructure.PDE.Localization
