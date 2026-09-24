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

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- Exit `(7)` on the exact silent-origin state. -/
noncomputable def typeASilentExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASilentExitSixFree) known]
    (producedFresh : K .typeAExitSevenProduced ∉ known)
    (freeFresh : K .typeASilentExitSevenFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSevenProduced) (K .typeASilentExitSevenFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSevenProduced) (K .typeASilentExitSevenFree)
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative,
        zero, receiver, isReceiver, peeled, peeledSubset, saturated,
        noExitFour, noCompression, noDelocalization, origin⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASilentExitSixFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases produced : HandoffProduced data current.object packing piece
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          noExitFour, noCompression, noDelocalization, origin, produced⟩⟩⟩)
    producedFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
