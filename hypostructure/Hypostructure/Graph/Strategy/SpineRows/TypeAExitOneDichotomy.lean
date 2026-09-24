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

/-! ## Node `[95]`: exit `(1)`, the Mersenne anchored return

`def:typeA-saturated-exits` (1): *"an anchored return through a completion port
of `w` has length in `Mers`"*, where `w` is a saturated receiver in a Type A
support.  That clause is stated at the receiver and quantifies *anchored*
returns through *any* of its completion ports: unlike clause (2) it carries no
visibility condition and does not restrict to receiver-entry returns, and
neither restriction is written here.  Node `[93]`'s visible-entry hypothesis is
read off the ledger by exact key — it is what puts the branch on the exit list —
but it is not conjoined into the alternative, because conjoining it would
strengthen the yes arm and weaken the no arm this row hands to node `[97]`.

Both arms are the receiver's, not the object's: the alternative names the
receiver's own completion ports through `Graph.VisibleEntry.completionPorts` and
the return through `Graph.VisibleEntry.AnchoredReturn`, so nothing here is a
search for a cycle anywhere in the object.

The yes arm closes.  `lem:typeA-exits-discharged`: *"Exit (1) gives an
edge-rooted Mersenne return, hence a power-of-two cycle by
`lem:return-equivalence`."*  That cycle is denied by the return-avoidance
invariant nodes `[5]`--`[7]` committed, so the branch that commits this fact is
uninhabited; the closure itself is the framework's, read off the two facts by
`Incompatible`, and no row of this block performs it.

The no arm is the hypothesis exit `(2)` is asked under at node `[97]`: no
anchored return through any completion port of any saturated receiver has
accepted length.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so nothing downstream of node `[97]` can read the Mersenne return and the
closed arm cannot read the exit-`(1)`-free hypothesis. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitOneDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleEntry) known]
    (returnFresh : K .typeAExitOneReturn ∉ known)
    (freeFresh : K .typeAExitOneFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitOneReturn) (K .typeAExitOneFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitOneReturn) (K .typeAExitOneFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleEntry)).down
      obtain ⟨package⟩ := packageExists
      by_cases realized :
          ∃ return' : Graph.VisibleEntry.AnchoredReturn current.object receiver
              package.outside,
            Graph.ShiftedCycleLength data.LengthOK return'.path.length
      · exact ⟨.inl ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩
      · exact ⟨.inr ⟨
          ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package,
            fun return' accepted => realized ⟨return', accepted⟩⟩⟩⟩)
    returnFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
