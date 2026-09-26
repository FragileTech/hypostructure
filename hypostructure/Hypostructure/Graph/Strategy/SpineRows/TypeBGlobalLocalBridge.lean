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

/-- Nodes `[73]`/`[83]`, `prop:typeB-global-local-bridge` on the B2-failure arm. -/
@[reducible] noncomputable def typeBGlobalLocalBridgeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBGlobalLocalBridge
    { Requires := [K .selection, K .highCentreNormalForm]
      Produces := [K .typeBGlobalLocalBridge]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBGlobalLocalBridge)
        ⟨Contracts.TypeB.typeBGlobalLocalBridge (inputs.get (K .selection)).down.1
          (inputs.get (K .highCentreNormalForm)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
