import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[146]`: decide the route-8 threshold on node `[145]`'s residual. -/
noncomputable def coldRoute8Dichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (belowFresh : K .coldRoute8Below ∉ known)
    (atOrAboveFresh : K .coldRoute8AtOrAbove ∉ known) :
    Decision (K .coldRoute8Below) (K .coldRoute8AtOrAbove) previous := by
  classical
  let _split := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .coldRoute8Below) (K .coldRoute8AtOrAbove)
    `Hypostructure.Graph.Strategy.Spine.coldRoute8Dichotomy
    (if below : ColdRoute8BelowStatement data current.object then
      .inl ⟨below⟩
    else
      .inr ⟨below⟩)
    belowFresh atOrAboveFresh

/-- Node `[148]`: decide the live-hot entropy comparison on `[146]`'s no arm. -/
noncomputable def coldHotEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (overflowFresh : K .coldHotEntropyOverflow ∉ known)
    (capFresh : K .coldHotEntropyCap ∉ known) :
    Decision (K .coldHotEntropyOverflow) (K .coldHotEntropyCap) previous := by
  classical
  let _split := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .coldHotEntropyOverflow) (K .coldHotEntropyCap)
    `Hypostructure.Graph.Strategy.Spine.coldHotEntropyDichotomy
    (if overflow : ColdHotEntropyOverflowStatement data current.object then
      .inl ⟨overflow⟩
    else
      .inr ⟨Nat.le_of_not_lt overflow⟩)
    overflowFresh capFresh

end Hypostructure.Graph.Strategy.Spine
