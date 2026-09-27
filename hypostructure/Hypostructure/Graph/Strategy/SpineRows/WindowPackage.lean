import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineWindows

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[158]`**, the exact finite form of the realization sentence of
`lem:p13-window-package`/`prop:p13-density`: is the joint window package of
the fixed maximal packing realized by the labelled skeleton class?  The yes arm
continues at `[22]`; the no arm is the dense-packing residual `[159]`. -/
noncomputable def windowPackageRealizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .skeletonDominates) known]
    (realizedFresh : K .windowPackageRealized ∉ known)
    (unrealizedFresh : K .windowPackageUnrealized ∉ known) :
    Decision (K .windowPackageRealized) (K .windowPackageUnrealized) previous := by
  classical
  exact Decision.run previous (K .windowPackageRealized) (K .windowPackageUnrealized)
    `Hypostructure.Graph.Strategy.Spine.windowPackageRealizationDichotomy
    (if realized : WindowPackageRealizedStatement data.toParameters current.object then
      .inl ⟨realized⟩
    else
      .inr ⟨Nat.lt_of_not_le realized⟩)
    realizedFresh unrealizedFresh

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[21]`: the separated window package

`lem:p13-window-package`.  For every selected dyadic scale, the complete
certified table contributes the ratio between the products of its safe and
flat columns.  The package compounds that exact ratio across all scales and
only then takes the integer logarithm.  This is the manuscript's
`(c₁₃ - o(1)) p₁₃ log₂ n` exponent; taking the integer floor before
scale aggregation would incorrectly replace `c₁₃` by `118`.

The scale factor is not decorative: without it the demand grows a whole
`log₂ n` slower than the manuscript's, and the cap node `[22]`--`[24]` derives
from it degrades to `θ ≲ 1.5·log₂ n / rate`, which bounds nothing as `n` grows.

The cap arm carries `lem:variable-edge-budget` with it: the budget the arm
retained is stable when the edge count is only known to lie in an admissible
family, because the exact stratum is one of the family's and the family's own
union bound dominates it (`sum_edgeStratumCount_le_variableEdgeBudget` is the
summed form of the same count).  That is what makes the retained cap survive
`rem:budget-robustness` rather than depending on the exact `m`.

`lem:p13-window-package` is proved on the literal near-cubic residual.  The
label-injectivity clauses are refuted through the ledger's `lem:replacement`
fact (`K .replacementExclusion`) and the selection's minimality, exactly as
`DeclaredQuotient.localize` splits them. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def windowPackageRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.windowPackage
    { Requires := [K .replacementExclusion, K .selection, K .cubicBaseline]
      Produces := [K .windowPackageSeparated]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowPackageSeparated)
        ⟨Contracts.Spine.windowPackageSeparated_of_maximalPacking data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.2.2.2
          (inputs.get (K .replacementExclusion)).down
          (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
