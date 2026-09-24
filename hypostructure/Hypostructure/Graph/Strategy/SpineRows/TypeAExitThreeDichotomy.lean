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

/-! ## Node `[99]`: exit `(3)`, the `P₁₃` label collision

`def:typeA-saturated-exits` (3): *"a shared `P₁₃` window violates the
corresponding legal-label relation `C_s`"*.  `lem:typeA-visible-entry` states
the test it is: *"if two traces pass through a common `P₁₃` window, their labels
are governed by the relations `C_s` of `lem:labels`; failure of the
corresponding `C_s` test is the stated label collision, which is exit (3)"*, and
`lem:typeA-exits-discharged` discharges it as *"precisely failure of the legal
`P₁₃` label relation from `lem:labels`; by definition of the relation, it
creates a target event"*.

As at nodes `[95]` and `[97]`, the configuration is node `[93]`'s, so the visible
port rides with it on both arms and the packing the windows come from is that
configuration's own.  The exit itself is the manuscript's *local label test*:
two outside vertices attach to one packed window, the simple path joining them
avoids that window, and the cycle their attachment coordinates close through the
window has accepted length.
`Graph.WindowLabelCollision.labelCollision_iff_not_safe` is the statement that
this last clause *is* `¬ C_s(S(x), S(y))` at the registered dyadic target, so
the alternative is exactly `lem:labels`' relation.

The yes arm closes.  `Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision`
*builds* the cycle `x p_i P p_j y Q x`, whose length is the manuscript's
`s + 2 + |i − j|` and which the collision's own side condition declares
accepted; the selected object avoids every accepted length, so the branch that
commits this fact is uninhabited.  The closure is the framework's, read off the
selection and this fact by `Incompatible`, and no row of this block performs it.
The one thing the construction asks of the target is that the degenerate closure
be rejected -- one attachment counted twice with no connector -- and that is
`Data.degenerateClosureRejected`, the registered analogue of
`Data.quadrilateralAccepted`; nothing here writes `2`, `4`, `8`, or `{2, 6}`.

The no arm is the manuscript's *"assume exits (1)--(3) do not occur"* at its
third clause: every shared window of the packing satisfies its legal-label
relation at every outside connector.  It is the hypothesis the exit-`(4)` family
of `def:typeA-exit4-family` is built under at node `[101]`.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so nothing downstream of node `[101]` can read the collision and the
closed arm cannot read the exit-`(3)`-free hypothesis. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitThreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleEntry) known]
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (freeFresh : K .typeAExitThreeFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitThreeCollision) (K .typeAExitThreeFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitThreeCollision) (K .typeAExitThreeFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleEntry)).down
      obtain ⟨package⟩ := packageExists
      by_cases realized : Graph.WindowLabelCollision.LabelCollision
          current.object data.windowOrder data.LengthOK packing
      · exact ⟨.inl ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩
      · exact ⟨.inr ⟨
          ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩)
    collisionFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
