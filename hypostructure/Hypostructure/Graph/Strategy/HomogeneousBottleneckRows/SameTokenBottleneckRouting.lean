import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.Routing

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[144]`: same-token bottleneck routing

The selected proof belongs here, inside one Type-A `factOnly` executor.  Its
inputs are the exact current-object facts already published by the branch; no
route, separator, label map, profile callback, or handoff object is accepted as
an argument.  The executor publishes the paper lemma and then its survivor
specialization monotonically.

The row reads exactly the earlier manuscript facts used by the routing
argument: the sealed active-demand value (activation and the two-shoulder
description), the node-`[125]` sparse-exit survival of G's declared family,
target avoidance from the selection, the cubic baseline (with the rejected
degenerate closure), and the sealed capacity/token presentation with its
connectedness proof.  It routes G's canonical same-token routing
(`Statements/CanonicalSameToken.lean`): the parallel and cubic-first-separator
cases read the two pattern coordinates on G's piece at their canonical support
`Z`; a separating context there is exit (b), and the remaining profile-crossing
or context-equivalent readings are the unresolved pair of the paper error at
`[144]`; a high-degree first separator gives the handoff envelope.  The row
publishes `exit ∨ handoff ∨ unresolved` (`BottleneckRoutingStatement`) and
constructs no quotient.  No selector, callback, route record, or side carrier
is postulated. -/

@[reducible] noncomputable def sameTokenBottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenBottleneckRouting
    { Requires := [K .homogeneousBottleneckPattern, K .activeSurplusDemands,
        K .cubicBaseline, K .capacityTokenLedger, K .bridgeless,
        K .highCentreNormalForm, K .selection, K .sparseSurplusSurvivor]
      Produces := [K .bottleneckRouting]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routed := Graph.Contracts.SurplusPair.sameTokenTypeBHandoff_of_pattern
        (inputs.get (K .homogeneousBottleneckPattern)).down
        (inputs.get (K .activeSurplusDemands)).down
        (inputs.get (K .cubicBaseline)).down.1
        (inputs.get (K .capacityTokenLedger)).down
        (inputs.get (K .bridgeless)).down
        (inputs.get (K .highCentreNormalForm)).down
        inputs.current.baseline
        (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
        (inputs.get (K .cubicBaseline)).down.1.2.2.1
        (inputs.get (K .selection)).down.1
        (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .bottleneckRouting) ⟨routed.1⟩ .nil)

/-- Node `[144]`, handoff test: the routed pattern does or does not produce the
decorated same-token Type B handoff.  The decision reads its predecessor
`K .bottleneckRouting` (the routed canonical pattern of G) and splits the
handoff at G's canonical first separator and envelope
(`SameTokenHandoffAt`); the no arm is its literal negation. -/
noncomputable def sameTokenHandoffDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .bottleneckRouting) known]
    (handoffFresh : K .typeBHandoff ∉ known)
    (failsFresh : K .typeBHandoffFails ∉ known) :
    Decision (K .typeBHandoff) (K .typeBHandoffFails) previous :=
  Decision.run previous (K .typeBHandoff) (K .typeBHandoffFails)
    `Hypostructure.Graph.Strategy.Spine.sameTokenHandoffDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBHandoff).At current ⊕
          (K .typeBHandoffFails).At current) from by
      classical
      have _routed := (previous.get (K .bottleneckRouting)).down
      by_cases handoff : Holds BranchState Presentation presentation data
          .typeBHandoff current.object
      · exact ⟨.inl ⟨handoff⟩⟩
      · exact ⟨.inr ⟨handoff⟩⟩))
    handoffFresh failsFresh

/-- Node `[144a]`, no-handoff arm: by `lem:same-token-bottleneck-routing` on
the survivor, the routed pattern's two same-label coordinates are the
unresolved pair that the paper error at `[144]` leaves to the open leaf
`[144a]`. -/
@[reducible] noncomputable def sameTokenPatternUnresolvedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenPatternUnresolved
    { Requires := [K .homogeneousBottleneckPattern, K .activeSurplusDemands,
        K .cubicBaseline, K .capacityTokenLedger, K .bridgeless,
        K .highCentreNormalForm, K .selection, K .sparseSurplusSurvivor,
        K .typeBHandoffFails]
      Produces := [K .sameTokenPatternUnresolved]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routed := Graph.Contracts.SurplusPair.sameTokenTypeBHandoff_of_pattern
        (inputs.get (K .homogeneousBottleneckPattern)).down
        (inputs.get (K .activeSurplusDemands)).down
        (inputs.get (K .cubicBaseline)).down.1
        (inputs.get (K .capacityTokenLedger)).down
        (inputs.get (K .bridgeless)).down
        (inputs.get (K .highCentreNormalForm)).down
        inputs.current.baseline
        (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
        (inputs.get (K .cubicBaseline)).down.1.2.2.1
        (inputs.get (K .selection)).down.1
        (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .sameTokenPatternUnresolved)
        ⟨routed.2.resolve_left (inputs.get (K .typeBHandoffFails)).down⟩ .nil)

/-- Node `[144a]`: the explicit replacement candidates of tex 5594 at G.  Read
the unresolved pattern pair (its canonical routing and support `Z`) and the
survivor: no reading of G's piece at `Z` is a replacement representative of
`Z`, since one would be G's compression exit (c). -/
@[reducible] noncomputable def sameTokenReadingsNotReplacementRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenReadingsNotReplacement
    { Requires := [K .sameTokenPatternUnresolved, K .sparseSurplusSurvivor]
      Produces := [K .sameTokenReadingsNotReplacement]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sameTokenReadingsNotReplacement)
        ⟨Graph.Contracts.SurplusPair.sameTokenReadingsNotReplacement_of_unresolved
          (inputs.get (K .sameTokenPatternUnresolved)).down
          (inputs.get (K .sparseSurplusSurvivor)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
