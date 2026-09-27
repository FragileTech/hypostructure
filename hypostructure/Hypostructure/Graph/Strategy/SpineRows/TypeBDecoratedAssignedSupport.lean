import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Entry

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[66]` → `[65]`: the exit-`(7)` decorated envelope is admissible Type B
fan-envelope data (`lem:decorated-fan-admissibility`) and enters the common
Type B entry. -/
@[reducible] noncomputable def typeBDecoratedAssignedSupportRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBDecoratedAssignedSupport
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .netChargeCap, K .typeAExitSevenEnvelope, K .cubicBaseline]
      Produces := [K .typeBDecoratedAssignedSupport]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBDecoratedAssignedSupport)
        ⟨Contracts.TypeB.typeBDecoratedAssignedSupport_of_handoff
          (inputs.get (K .netChargeCap)).down (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.1.1
            (inputs.get (K .cubicBaseline)).down.1.2.2.1
          (inputs.get (K .uncompressible)).down (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .typeAExitSevenEnvelope)).down⟩
        .nil)

/-- Node `[65]`, the decorated entry: the Type B entry read from the decorated
assigned support (`K .typeBDecoratedAssignedSupport`). -/
@[reducible] noncomputable def typeBDecoratedEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBDecoratedEntry
    { Requires := [K .typeBDecoratedAssignedSupport]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_decoratedAssignedSupport
          (inputs.get (K .typeBDecoratedAssignedSupport)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
