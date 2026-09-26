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
target avoidance from the selection, cubic baseline, and
the sealed capacity/token presentation with its connectedness proof.  The
parallel and cubic-switch cases construct their attempted declared quotient
locally on the connected support already proved in the case, and route it
through the framework's target-defect/compression/delocalization alternatives.
The row publishes only the paper's literal sparse-exit-or-Type-B conclusion.
No selector, callback, route record, or side carrier is postulated. -/

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
        (inputs.get (K .cubicBaseline)).down
        (inputs.get (K .capacityTokenLedger)).down
        (inputs.get (K .bridgeless)).down
        (inputs.get (K .highCentreNormalForm)).down
        inputs.current.baseline data.three_le_threshold
        data.quadrilateralAccepted data.degenerateClosureRejected
        (inputs.get (K .selection)).down.1
        (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .bottleneckRouting) ⟨routed.1⟩ .nil)

/-- Node `[144]`, handoff test: the routed pattern does or does not produce the
decorated same-token Type B handoff.  Exact classical case analysis on the
handoff statement; the no arm is its literal negation. -/
noncomputable def sameTokenHandoffDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (handoffFresh : K .typeBHandoff ∉ known)
    (failsFresh : K .typeBHandoffFails ∉ known) :
    Decision (K .typeBHandoff) (K .typeBHandoffFails) previous :=
  Decision.run previous (K .typeBHandoff) (K .typeBHandoffFails)
    `Hypostructure.Graph.Strategy.Spine.sameTokenHandoffDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBHandoff).At current ⊕
          (K .typeBHandoffFails).At current) from by
      classical
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
        (inputs.get (K .cubicBaseline)).down
        (inputs.get (K .capacityTokenLedger)).down
        (inputs.get (K .bridgeless)).down
        (inputs.get (K .highCentreNormalForm)).down
        inputs.current.baseline data.three_le_threshold
        data.quadrilateralAccepted data.degenerateClosureRejected
        (inputs.get (K .selection)).down.1
        (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .sameTokenPatternUnresolved)
        ⟨routed.2.resolve_left (inputs.get (K .typeBHandoffFails)).down⟩ .nil)

end Hypostructure.Graph.Strategy.Spine
