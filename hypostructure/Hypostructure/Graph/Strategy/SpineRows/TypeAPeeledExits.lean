import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # The second pass of nodes `[93]`--`[101]` after peeling

On the yes arm of the recompute-`L₄` retest (`K .typeAPeeledSaturatedReceiver`)
the terminal receiver `w` of `X₀` is saturated at its terminal set `P₄(w)`, and
the paper re-enters node `[93]` (tex 1095; `lem:typeA-exit4-residual-routing`):

* node `[93]`: does a completion port of `w` carry `s` visible receiver-entry
  returns from unpeeled loads?  Yes (`K .typeAPeeledVisibleEntry`): exits
  `(1)`--`(3)` are asked at the overloaded port of `P₄(w)`
  (`lem:typeA-unpeeled-visible-routing`), and close at nodes `[96]`, `[98]`,
  `[100]`.  No (`K .typeAPeeledNoVisibleEntry`): node `[94]`, the residual excess
  `E₄(w)` is nonempty and silent (`lem:typeA-unpeeled-silent-routing`);
* node `[101]` on either lane: the terminal set is exit-`(4)`-free
  (`K .typeASaturatedHandoffExitFourFree`), and exits `(5)`--`(8)` follow. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[93]` after peeling, decided at the terminal state. -/
noncomputable def typeAPeeledVisibleEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAPeeledSaturatedReceiver) known]
    (visibleFresh : K .typeAPeeledVisibleEntry ∉ known)
    (silentFresh : K .typeAPeeledNoVisibleEntry ∉ known) :
    Decision (K .typeAPeeledVisibleEntry) (K .typeAPeeledNoVisibleEntry)
      previous :=
  Decision.run previous (K .typeAPeeledVisibleEntry)
    (K .typeAPeeledNoVisibleEntry)
    `Hypostructure.Graph.Strategy.Spine.typeAPeeledVisibleEntryDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAPeeledVisibleEntry).At current ⊕
          (K .typeAPeeledNoVisibleEntry).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, _saturated⟩ :=
        (previous.get (K .typeAPeeledSaturatedReceiver)).down
      by_cases visible : Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece
          data.threshold data.dischargeScale receiver
          (canonicalTerminalPeeled data.toParameters current.object piece
            receiver))
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, visible⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, visible⟩⟩⟩))
    visibleFresh silentFresh

/-- Node `[94]` after peeling (`lem:typeA-unpeeled-silent-routing`). -/
@[reducible] noncomputable def typeAPeeledSilentExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPeeledSilentExcess
    { Requires := [K .typeALowSurplus, K .typeAPeeledNoVisibleEntry]
      Produces := [K .typeAPeeledSilentExcess]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAPeeledSilentExcess)
        ⟨Graph.Contracts.TypeA.typeAPeeledSilentExcess data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeAPeeledNoVisibleEntry)).down⟩
        .nil)

/-- Node `[95]` after peeling: exit `(1)` at the overloaded port of the
terminal state, read from node `[93]`'s visible arm. -/
noncomputable def typeAPeeledExitOneDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAPeeledVisibleEntry) known]
    (returnFresh : K .typeAPeeledExitOneReturn ∉ known)
    (freeFresh : K .typeAPeeledExitOneFree ∉ known) :
    Decision (K .typeAPeeledExitOneReturn) (K .typeAPeeledExitOneFree)
      previous :=
  Decision.run previous (K .typeAPeeledExitOneReturn) (K .typeAPeeledExitOneFree)
    `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitOneDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAPeeledExitOneReturn).At current ⊕
          (K .typeAPeeledExitOneFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, ⟨package⟩⟩ :=
        (previous.get (K .typeAPeeledVisibleEntry)).down
      have portPinned :=
        VisibleFourUnpeeledPackage.outside_eq_canonicalOverloadedPortAt
          (data := data.toParameters) (object := current.object) package
      by_cases realized : ∃ return' : Graph.VisibleEntry.AnchoredReturn
            current.object receiver package.outside,
          Graph.ShiftedCycleLength data.LengthOK return'.path.length
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, package.outside,
          portPinned, realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, package.outside,
          portPinned, fun return' accepted => realized ⟨return', accepted⟩⟩⟩⟩))
    returnFresh freeFresh

/-- Node `[97]` after peeling: exit `(2)` at the same port, read from node
`[95]`'s no arm. -/
noncomputable def typeAPeeledExitTwoDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAPeeledExitOneFree) known]
    (thetaFresh : K .typeAPeeledExitTwoTheta ∉ known)
    (freeFresh : K .typeAPeeledExitTwoFree ∉ known) :
    Decision (K .typeAPeeledExitTwoTheta) (K .typeAPeeledExitTwoFree)
      previous :=
  Decision.run previous (K .typeAPeeledExitTwoTheta) (K .typeAPeeledExitTwoFree)
    `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitTwoDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAPeeledExitTwoTheta).At current ⊕
          (K .typeAPeeledExitTwoFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, port, portPinned, _oneFree⟩ :=
        (previous.get (K .typeAPeeledExitOneFree)).down
      by_cases realized : Graph.VisibleEntry.ExitTwoThrough current.object piece
          data.LengthOK receiver port
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩))
    thetaFresh freeFresh

/-- Node `[99]` after peeling: exit `(3)` at the same port, read from node
`[97]`'s no arm. -/
noncomputable def typeAPeeledExitThreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAPeeledExitTwoFree) known]
    (collisionFresh : K .typeAPeeledExitThreeCollision ∉ known)
    (freeFresh : K .typeAPeeledExitThreeFree ∉ known) :
    Decision (K .typeAPeeledExitThreeCollision) (K .typeAPeeledExitThreeFree)
      previous :=
  Decision.run previous (K .typeAPeeledExitThreeCollision)
    (K .typeAPeeledExitThreeFree)
    `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitThreeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAPeeledExitThreeCollision).At current ⊕
          (K .typeAPeeledExitThreeFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, port, portPinned, _twoFree⟩ :=
        (previous.get (K .typeAPeeledExitTwoFree)).down
      by_cases realized : ExitThreeThrough data.toParameters current.object piece
          receiver port
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩))
    collisionFresh freeFresh

/-- Node `[100]` after peeling: the collision closes an accepted cycle of `G`. -/
@[reducible] noncomputable def typeAPeeledExitThreeCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitThreeCycle
    { Requires := [K .typeAPeeledExitThreeCollision, K .cubicBaseline]
      Produces := [K .typeAExitThreeCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitThreeCycle)
        ⟨Graph.Contracts.TypeA.typeAPeeledExitThreeCycle data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.2.2.1
          (inputs.get (K .typeAPeeledExitThreeCollision)).down⟩
        .nil)

/-- Node `[101]` after peeling, visible lane: the terminal set is
exit-`(4)`-free. -/
@[reducible] noncomputable def typeAPeeledVisibleExitFourFreeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPeeledVisibleExitFourFree
    { Requires := [K .typeALowSurplus, K .typeAPeeledExitThreeFree]
      Produces := [K .typeASaturatedHandoffExitFourFree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedHandoffExitFourFree)
        ⟨Graph.Contracts.TypeA.typeASaturatedHandoffExitFourFree_of_peeledExitThreeFree
          data.toParameters inputs.current.object inputs.current.baseline
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeAPeeledExitThreeFree)).down⟩
        .nil)

/-- Node `[101]` after peeling, silent lane: the terminal set is
exit-`(4)`-free. -/
@[reducible] noncomputable def typeAPeeledSilentExitFourFreeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPeeledSilentExitFourFree
    { Requires := [K .typeALowSurplus, K .typeAPeeledSilentExcess]
      Produces := [K .typeASaturatedHandoffExitFourFree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedHandoffExitFourFree)
        ⟨Graph.Contracts.TypeA.typeASaturatedHandoffExitFourFree_of_peeledSilentExcess
          data.toParameters inputs.current.object inputs.current.baseline
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeAPeeledSilentExcess)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
