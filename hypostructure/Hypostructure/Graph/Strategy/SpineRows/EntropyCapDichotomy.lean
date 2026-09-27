import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[53]`: the admissible entropy cap, and its terminal `[54]`

`eq:entropy-cap` (tex 9898): "the remaining non-obstruction budget is strictly
smaller than the forced obstruction cost", `K|R| − o(|R|)` of
`cor:forced-curvature-cost`.  In exact integer form, with the forced cost read
at `P₀` as node `[48]` publishes it (`forcedObstructionBits`): the joint
window/remainder package of node `[52]` times `2^{K|R|−o(|R|)}` against the
labelled skeleton budget of `lem:near-cubic-budget`.  The decision reads its two
predecessors `[48]` and `[52]`.

The comparison is a `Nat` trichotomy, so the two arms are exact complements.
The yes arm is the manuscript's node `[54]`; the no arm is node `[55]`,
Residual C. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def entropyCapDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .forcedCurvatureCost) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .entropyPackageDemand) known]
    (activeFresh : K .entropyCapActive ∉ known)
    (boundFresh : K .entropyCapBound ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .entropyCapActive) (K .entropyCapBound) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .entropyCapActive) (K .entropyCapBound)
    `Hypostructure.Graph.Strategy.Spine.entropyCapDichotomy
    (by
      classical
      -- `[48]` and `[52]` → `[53]`: the forced obstruction cost and the joint
      -- window/remainder account are the two predecessors of the test.
      let _cost := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .forcedCurvatureCost)).down
      let _package := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .entropyPackageDemand)).down
      by_cases active :
          Graph.skeletonBudget current.object <
            jointPackageDemand data.toParameters current.object *
              2 ^ forcedObstructionBits data.toParameters current.object
      · exact .inl ⟨active⟩
      · exact .inr ⟨Nat.le_of_not_lt active⟩)
    activeFresh boundFresh

end Hypostructure.Graph.Strategy.Spine
