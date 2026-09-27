import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Certificate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[73]` → `[75]`, `[83]` → `[84]`: B2 failures charged to assigned surplus. -/
@[reducible] noncomputable def typeBOverlapObstructionMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstructionMass
    { Requires := [K .typeBGlobalLocalBridge, K .cubicBaseline]
      Produces := [K .typeBOverlapObstructionMass]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBOverlapObstructionMass)
        ⟨Contracts.TypeB.typeBOverlapObstructionMass
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.2
          (inputs.get (K .typeBGlobalLocalBridge)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
