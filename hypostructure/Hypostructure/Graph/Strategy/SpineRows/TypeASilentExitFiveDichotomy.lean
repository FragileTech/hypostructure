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
/-- Exit `(5)` on the exact silent-origin state. -/
noncomputable def typeASilentExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASilentExitFourFree) known]
    (exitFresh : K .typeAExitFive ∉ known)
    (freeFresh : K .typeASilentExitFiveFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitFive) (K .typeASilentExitFiveFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitFive) (K .typeASilentExitFiveFree)
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitFiveDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative,
        zero, receiver, isReceiver, origin, peeled, peeledSubset, saturated,
        noExitFour⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASilentExitFourFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases compression : ExitFiveAt data current.object piece receiver peeled
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          compression⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, origin, peeled, peeledSubset,
          saturated, noExitFour, compression⟩⟩⟩)
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
