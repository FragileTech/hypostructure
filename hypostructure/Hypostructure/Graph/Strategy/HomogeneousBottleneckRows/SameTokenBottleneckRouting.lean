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
argument: the sealed active-demand value (which already contains activation,
the two-shoulder description, and sparse-exit survival), cubic baseline, and
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
        K .highCentreNormalForm]
      Produces := [K .bottleneckRouting, K .typeBHandoff]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
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
      .cons (key := K .bottleneckRouting) ⟨routed.1⟩
        (.cons (key := K .typeBHandoff) ⟨routed.2⟩ .nil))

end Hypostructure.Graph.Strategy.Spine
