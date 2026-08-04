import Mathlib.Analysis.SpecialFunctions.Log.Base
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics

/-!
# The entropy/rank packing budget, as formulas

This is the numerical boundary of the entropy block: the real-valued budget
algebra that a strategy compares, with every coefficient carried by typed
presentation data and the window rate read off the framework's own derived
barrier summary.

No rounded decimal occurs here.  The definitions below are the literal
formulas of the packing-density accounting: a skeleton budget per
`log₂ n`, a per-remainder high-entropy share, a packed window order, and an
already-forced curvature cost per remainder vertex.

The window rate is *not* a presentation coefficient: it is
`log₂(safeProduct / flatProduct)` of the certified barrier table Core already
derives in `Core.Strategy.FiniteBarrierEnumeration.Summary`.  A registration
therefore has no numeric table parameter to fill, and the integral floor that
executable strategies consume stays `Summary.binaryRateFloor`.
-/

namespace Hypostructure.Core.Strategy.FiniteBarrierEnumeration.Summary

/-- The exact finite-table window rate.  Both products are fields of the
single derived `Summary`, so no exponent or product is repeated here, and the
integral floor that executable strategies consume stays `binaryRateFloor` of
the very same summary. -/
noncomputable def windowRate (summary : Summary) : ℝ :=
  Real.logb 2 ((summary.safeProduct : ℝ) / (summary.flatProduct : ℝ))

@[simp] theorem ofRows_windowRate (rows : List (Nat × Nat)) :
    (ofRows rows).windowRate =
      Real.logb 2 (((rows.map Prod.fst).prod : ℝ) /
        ((rows.map Prod.snd).prod : ℝ)) :=
  rfl

end Hypostructure.Core.Strategy.FiniteBarrierEnumeration.Summary

namespace Hypostructure.Core.EntropyPackingBudget

/-- Problem-owned coefficients consumed by the entropy/rank budget
calculation.  A problem presentation must prove these values; strategy code
does not choose them.

`skeletonBudget` is the coefficient of `n log₂ n`, `remainderEntropyShare`
is the high-entropy contribution per remainder vertex, `windowOrder` is the
number of vertices removed by one packed window, and `forcedCurvatureCost` is
the already rank-forced cost per remainder vertex. -/
structure Presentation where
  skeletonBudget : ℝ
  remainderEntropyShare : ℝ
  windowOrder : ℕ
  forcedCurvatureCost : ℝ
  skeletonBudget_nonneg : 0 ≤ skeletonBudget
  remainderEntropyShare_nonneg : 0 ≤ remainderEntropyShare
  windowOrder_pos : 0 < windowOrder
  forcedCurvatureCost_nonneg : 0 ≤ forcedCurvatureCost

variable (windowRate : ℝ) (presentation : Presentation)

/-- Coefficient of the packing density after the remainder contribution is
expanded: `share * (1 - order * θ) + windowRate * θ`. -/
def packingCoefficient : ℝ :=
  windowRate - presentation.windowOrder * presentation.remainderEntropyShare

/-- Constant part of the remaining non-curvature budget. -/
def remainingBudgetIntercept : ℝ :=
  presentation.skeletonBudget - presentation.remainderEntropyShare

/-- Window-only packing-density cap. -/
noncomputable def windowOnlyDensityCap : ℝ :=
  presentation.skeletonBudget / windowRate

/-- High-entropy packing-density cap obtained by solving the feasibility
inequality. -/
noncomputable def highEntropyDensityCap : ℝ :=
  remainingBudgetIntercept presentation / packingCoefficient windowRate presentation

/-- Size of the unpacked remainder as a fraction of the ambient order. -/
def remainderFraction (packingDensity : ℝ) : ℝ :=
  1 - presentation.windowOrder * packingDensity

/-- Remaining non-curvature budget at packing density `packingDensity`. -/
def remainingBudget (packingDensity logOrder : ℝ) : ℝ :=
  (remainingBudgetIntercept presentation -
      packingCoefficient windowRate presentation * packingDensity) * logOrder

/-- Rank-forced curvature demand at packing density `packingDensity`. -/
def forcedCurvatureDemand (packingDensity : ℝ) : ℝ :=
  presentation.forcedCurvatureCost *
    remainderFraction presentation packingDensity

/-- The finite-size packing threshold, expressed using the table-derived rate
and the problem-owned coefficients. -/
noncomputable def finiteSizePackingThreshold (logOrder : ℝ) : ℝ :=
  (remainingBudgetIntercept presentation -
      presentation.forcedCurvatureCost / logOrder) /
    (packingCoefficient windowRate presentation -
      presentation.windowOrder * presentation.forcedCurvatureCost / logOrder)

/-- The exact high-packing entropy-cap condition, without a rounded threshold
or a manually embedded outcome. -/
def EntropyCapCondition (packingDensity logOrder : ℝ) : Prop :=
  remainingBudget windowRate presentation packingDensity logOrder <
    forcedCurvatureDemand presentation packingDensity

/-! ## Audit: the public quantities really are formula projections

The identities below pin the accounting: the derived table supplies the
window rate, the presentation supplies every remaining coefficient, and no
step introduces a constant of its own.
-/

/-- Expanding the remainder contribution really produces
`packingCoefficient`. -/
theorem packing_accounting_expansion (packingDensity : ℝ) :
    presentation.remainderEntropyShare *
          remainderFraction presentation packingDensity +
        windowRate * packingDensity =
      presentation.remainderEntropyShare +
        packingCoefficient windowRate presentation * packingDensity := by
  simp only [remainderFraction, packingCoefficient]
  ring

/-- The remaining budget is the skeleton budget minus the expanded packing
accounting, scaled by `logOrder`. -/
theorem remaining_budget_formula (packingDensity logOrder : ℝ) :
    remainingBudget windowRate presentation packingDensity logOrder =
      (presentation.skeletonBudget -
        (presentation.remainderEntropyShare +
          packingCoefficient windowRate presentation * packingDensity)) *
        logOrder := by
  simp only [remainingBudget, remainingBudgetIntercept]
  ring

/-- The entropy cap condition is exactly the feasibility inequality it is
meant to be; nothing is rounded on the way. -/
theorem entropy_cap_condition_formula (packingDensity logOrder : ℝ) :
    EntropyCapCondition windowRate presentation packingDensity logOrder ↔
      (remainingBudgetIntercept presentation -
          packingCoefficient windowRate presentation * packingDensity) *
          logOrder <
        presentation.forcedCurvatureCost *
          (1 - presentation.windowOrder * packingDensity) := by
  rfl

end Hypostructure.Core.EntropyPackingBudget
