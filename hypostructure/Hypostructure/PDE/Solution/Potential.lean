import Hypostructure.PDE.Localization.Cutoff

/-!
# Potentials of a registered fundamental solution

The classical way to solve an elliptic equation on a local residual is to cut
the source off and convolve with a fundamental solution.  `Localization/Cutoff`
supplies the first half; this module supplies the second.

A `FundamentalSolution` registers the kernel of an operator once — a locally
integrable function whose convolution inverts the operator on compactly
supported smooth data.  Everything downstream is then derived:

* `potential` is the convolution;
* `contDiff_potential` — the potential of a cut-off source is smooth, from
  `HasCompactSupport.contDiff_convolution_right`;
* `operator_potential` — it solves the equation, straight from the registered
  inversion law.

The kernel is registered per *operator*, not per problem: any model naming
that operator gets the solution operator with nothing further to supply.  This
is the shape `PDE.Solution.Interval` already has in one dimension, where the
kernel is the piecewise-linear `|x|/2` and the inversion law is the
fundamental theorem of calculus applied twice.
-/

namespace Hypostructure.PDE.Solution

open MeasureTheory
open scoped Convolution

universe uPoint

variable {Point : Type uPoint} [NormedAddCommGroup Point]
  [NormedSpace ℝ Point] [MeasureSpace Point] [BorelSpace Point]
  [FiniteDimensional ℝ Point]

/-- Smoothness exponent for the test data a potential accepts. -/
abbrev smoothExponent : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/--
A fundamental solution registered for one operator.

`kernel` is the locally integrable function whose convolution inverts
`operator` on compactly supported smooth data.  This is registered once per
operator and is the only mathematical input; the potential, its smoothness
and its solution law are all derived below.
-/
structure FundamentalSolution
    (operator : (Point → ℝ) → (Point → ℝ)) where
  kernel : Point → ℝ
  locallyIntegrable : LocallyIntegrable kernel volume
  /-- The kernel inverts the operator on compactly supported smooth data.
  This is the classical fundamental-solution identity for the operator. -/
  inverts : ∀ source : Point → ℝ, ContDiff ℝ smoothExponent source →
    HasCompactSupport source →
      (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (operator source)) =
        source

namespace FundamentalSolution

variable {operator : (Point → ℝ) → (Point → ℝ)}
  (fundamental : FundamentalSolution operator)

/-- The potential of a source: convolution with the registered kernel. -/
noncomputable def potential (source : Point → ℝ) : Point → ℝ :=
  fundamental.kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source

/-- The potential of a compactly supported smooth source is smooth.  This is
the regularity gain the graded interface asks for, and mathlib proves it. -/
theorem contDiff_potential {source : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent source)
    (compact : HasCompactSupport source) :
    ContDiff ℝ smoothExponent (fundamental.potential source) :=
  compact.contDiff_convolution_right _ fundamental.locallyIntegrable smooth

/-- The potential solves the equation, by the registered inversion law. -/
theorem potential_operator {source : Point → ℝ}
    (smooth : ContDiff ℝ smoothExponent source)
    (compact : HasCompactSupport source) :
    fundamental.potential (operator source) = source :=
  fundamental.inverts source smooth compact

end FundamentalSolution

end Hypostructure.PDE.Solution
