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
/-- Exit `(6)` on the exact silent-origin state. -/
noncomputable def typeASilentExitSixDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASilentExitFiveFree) known]
    (exitFresh : K .typeAExitSix ∉ known)
    (freeFresh : K .typeASilentExitSixFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSix) (K .typeASilentExitSixFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSix) (K .typeASilentExitSixFree)
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitSixDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative,
        zero, receiver, isReceiver, origin, peeled, peeledSubset, saturated,
        noExitFour, noCompression⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASilentExitFiveFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases delocalizes :
          ExitSixDelocalizes data current.object piece receiver peeled
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          noExitFour, noCompression, delocalizes⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          noExitFour, noCompression, delocalizes, origin⟩⟩⟩)
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
