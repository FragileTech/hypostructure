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

/-! ## Node `[62]`: the Type A / Type B split

The selected negative support either carries assigned high-degree surplus or it
does not.  The no arm is node `[63]`, the Type A low-deficiency atom branch; the
yes arm is node `[64]`, the Type B high-degree fan-safe support branch.

The split is decided on the *selected* support's own assigned surplus, which is
what `def:canonical-decomp`'s assignment credits to it -- not on the whole
remainder's.  Both arms carry the support's existence forward with the clause
that distinguishes them, so a consumer of either arm reads a support of the kind
its branch is about and cannot read the other. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeSplitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .negativeSupport) known]
    (typeAFresh : K .typeALowSurplus ∉ known)
    (typeBFresh : K .typeBHighSurplus ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeALowSurplus) (K .typeBHighSurplus) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeALowSurplus) (K .typeBHighSurplus)
    `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy
    (by
      classical
      have support :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .negativeSupport)).down
      let packing := Classical.choose support
      have packingSpec := Classical.choose_spec support
      have canonical := packingSpec.1
      have valid := packingSpec.2.1
      have maximal := packingSpec.2.2.1
      let component := Classical.choose packingSpec.2.2.2
      have componentSpec := Classical.choose_spec packingSpec.2.2.2
      have present := componentSpec.1
      have charge := componentSpec.2
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases zero : current.object.ambientSurplus piece data.threshold = 0
      · exact .inl
          ⟨packing, canonical, valid, maximal, component, present, charge, zero⟩
      · exact .inr ⟨packing, valid, maximal, component, present, charge,
          Nat.pos_of_ne_zero zero⟩)
    typeAFresh typeBFresh

end Hypostructure.Graph.Strategy.Spine
