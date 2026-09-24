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
/-- Node `[106]`: the scope of the committed exit-`(6)` delocalization —
`Delocalization.localize` at the presented entry: proper (a replacement of the
enlarging support) or global (a strictly smaller closed representative). -/
noncomputable def typeAExitSixScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitSix) known]
    (properFresh : K .typeAExitSixProper ∉ known)
    (globalFresh : K .typeAExitSixGlobal ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSixProper) (K .typeAExitSixGlobal) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _canonical, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _load, _eligible, _basin, _selected,
        delocalizes⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    properFresh globalFresh

end Hypostructure.Graph.Strategy.Spine
