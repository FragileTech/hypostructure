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

/-! ## Node `[89]`: is some receiver of the Type A support saturated?

`L(w) ≥ s·q(w)?`  The yes arm is node `[93]`, where the saturated receiver's
completion ports are examined; the no arm is node `[90]`, the unsaturated
capacity `L(w) ≤ s·q(w) − 1` that node `[91]`'s discharging spends.

The split is taken on a `Prop`, so no receiver is extracted to build the
branch: the arm not taken supplies the other arm's clause.  The no arm is
committed in the positive, subtraction-free form node `[90]` states —
`1 + L(w) ≤ s·q(w)` — which is `lem:typeA-threshold-algebra`'s "if the
saturated branch has been eliminated" clause and, at the manuscript's own
values, the surviving capacities `3`, `7`, `11`.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so no Type A row downstream can read the other alternative. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeASaturationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeALowSurplus) known]
    (saturatedFresh : K .typeASaturatedReceiver ∉ known)
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
    `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeALowSurplus)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases saturated :
          ∃ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver ∧
              current.object.Saturated piece data.threshold
                data.dischargeScale receiver
      · exact ⟨.inl ⟨⟨packing, canonical, valid, maximal, component, present, negative, zero,
          saturated⟩⟩⟩
      · refine ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative, zero, ?_⟩⟩⟩
        intro receiver isReceiver
        refine (current.object.not_saturated_iff piece data.threshold
          data.dischargeScale receiver).mp ?_
        exact fun full => saturated ⟨receiver, isReceiver, full⟩)
    saturatedFresh unsaturatedFresh

end Hypostructure.Graph.Strategy.Spine
