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

/-- Node `[177]` → `[65]`, `lem:absorbed-germ-fan-data` (ii): the decorated handoff
fan data at the first high centre of every retained corridor. -/
@[reducible] noncomputable def absorbedGermFanEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanEnvelope
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .absorbedGermFanData, K .exactCollisionFails, K .cubicBaseline]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_absorbedGermFanData
          (inputs.get (K .exactCollisionFails)).down
          (inputs.get (K .absorbedGermFanData)).down
          (Contracts.TypeB.absorbedGermDecoratedAssignedSupport
            (inputs.get (K .selection)).down.1
            (inputs.get (K .uncompressible)).down
            (inputs.get (K .remainderNormalized)).down
            (inputs.get (K .absorbedGermFanData)).down
            (by have := (inputs.get (K .cubicBaseline)).down.1; omega)
            (inputs.get (K .cubicBaseline)).down.2.2.1)⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
