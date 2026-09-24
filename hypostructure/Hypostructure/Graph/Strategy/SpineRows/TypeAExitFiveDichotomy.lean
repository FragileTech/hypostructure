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

/-! ## Node `[103]`: exit `(5)`, target-complete response compression

`def:typeA-saturated-exits` (5): at the selected saturated-handoff state after
exit `(4)` is absent, does an eligible visible or silent load have a selected
trace basin with a nontrivial target-complete quotient of its declared
`u`-supported response coordinates?  Alternative (b) itself records whether
the quotient has a smaller proper connected realization or exists only at the
trace-response level.  The no arm is the hypothesis exit `(6)` is asked under. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASaturatedHandoffExitFourFree) known]
    (exitFresh : K .typeAExitFive ∉ known)
    (freeFresh : K .typeAExitFiveFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitFive) (K .typeAExitFiveFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitFive) (K .typeAExitFiveFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASaturatedHandoffExitFourFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      let exitFiveAt : Prop :=
        ∃ load : current.object.Vertex,
          (((∃ package :
                Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                  data.dischargeScale receiver peeled,
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver package.outside
                    peeled,
                  witness.load = selected) ∧
                load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled) ∨
            (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                data.dischargeScale receiver peeled ∧
              (¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                  data.dischargeScale receiver peeled) ∧
              load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled)) ∧
            ∃ basin : Finset current.object.Vertex,
              Graph.Route8.TraceBasin.select? current.object piece data.threshold
                  receiver load = some basin ∧
                Graph.Route8.TraceBasin.TraceTargetCompleteCompression
                  current.object piece data.threshold data.LengthOK receiver load
                  basin)
      by_cases compression : exitFiveAt
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, compression⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          compression⟩⟩⟩)
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
