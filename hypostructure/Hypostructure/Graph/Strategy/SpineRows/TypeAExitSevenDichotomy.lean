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

/-! ## Node `[107]`: exit `(7)`, the decorated handoff fan

`def:typeA-saturated-exits` (7): is a high-degree decorated handoff fan
envelope produced at the selected residual after exits `(4)`--`(6)` have
failed?  The yes arm is reclassified at node `[108]` and leaves the Type A
charge calculation for Type B (`lem:typeA-exits-discharged`); the no arm is
node `[109]`, the route-8 residual of Part IX. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitSixFree) known]
    (producedFresh : K .typeAExitSevenProduced ∉ known)
    (freeFresh : K .typeAExitSevenFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSevenProduced) (K .typeAExitSevenFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitSixFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases produced : HandoffProduced data current.object packing piece
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, noDelocalization, produced⟩⟩⟩)
    producedFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
