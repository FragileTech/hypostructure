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

/-! ## Node `[97]`: exit `(2)`, the common-port theta

`def:typeA-saturated-exits` (2): *"two anchored receiver-entry returns through
one completion port are internally vertex-disjoint as anchored paths and their
lengths sum to a power of two"*.  As at node `[95]`, the port is the one node
`[93]` fixed, so the visible-count clause rides with the configuration on both
arms and the two returns are asked of that port.

Both returns are `def:typeA-visible-load`'s *receiver-entry* returns
`P = Γ ∘ Q`, not arbitrary paths of the object: the alternative names them
through `Graph.VisibleEntry.ReceiverEntryReturn` at the receiver's own
completion port, and `Graph.VisibleEntry.ExitTwoThrough` is that pair together
with the exit's two side conditions -- internal disjointness of the underlying
anchored paths, and acceptance of `|P₁| + |P₂|`.

The yes arm closes.  `lem:typeA-common-port-return-cycle`: two anchored returns
through one port share both endpoints, so internal disjointness makes their
union a simple cycle of length `|P₁| + |P₂|`, and the exit's own side condition
says that length is accepted.  `lem:typeA-exits-discharged` lists exit `(2)`
among the closed exits for exactly this reason.  That cycle is denied by the
return-avoidance invariant nodes `[5]`--`[7]` committed, so the branch that
commits this fact is uninhabited; the closure is the framework's, read off the
two facts by `Incompatible`, and no row of this block performs it.

The no arm is the hypothesis exit `(3)` is asked under at node `[99]`: no two
receiver-entry returns through one completion port are internally disjoint with accepted
total length.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so nothing downstream of node `[99]` can read the theta pair and the
closed arm cannot read the exit-`(2)`-free hypothesis. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitTwoDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleEntry) known]
    (thetaFresh : K .typeAExitTwoTheta ∉ known)
    (freeFresh : K .typeAExitTwoFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitTwoTheta) (K .typeAExitTwoFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitTwoTheta) (K .typeAExitTwoFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleEntry)).down
      obtain ⟨package⟩ := packageExists
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases realized : Graph.VisibleEntry.ExitTwoThrough current.object piece
          data.LengthOK receiver package.outside
      · exact ⟨.inl ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩
      · exact ⟨.inr ⟨
          ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩)
    thetaFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
