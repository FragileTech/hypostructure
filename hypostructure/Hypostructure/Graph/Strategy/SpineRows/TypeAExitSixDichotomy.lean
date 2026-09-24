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

/-! ## Nodes `[105]`--`[106]`: exit `(6)`, delocalization

`def:typeA-saturated-exits` (6): does the selected saturated-handoff state,
after exits `(4)` and `(5)` have failed, carry a declared response equality that
becomes target-complete only after adjoining a larger connected support?  Node
`[106]` then localizes it: a proper enlarging support gives the
proper-smearing replacement (`lem:proper-smearing`, forbidden by
`K .replacementExclusion`), the whole graph gives the strictly smaller closed
representative of `lem:no-silent-global-smearing` (forbidden by the selection's
minimality). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitSixDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitFiveFree) known]
    (exitFresh : K .typeAExitSix ∉ known)
    (freeFresh : K .typeAExitSixFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSix) (K .typeAExitSixFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSix) (K .typeAExitSixFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitFiveFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases delocalizes : ExitSixDelocalizes data current.object piece receiver peeled
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, delocalizes⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, delocalizes⟩⟩⟩)
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
