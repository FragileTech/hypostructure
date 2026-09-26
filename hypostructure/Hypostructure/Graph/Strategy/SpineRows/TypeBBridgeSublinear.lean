import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Bridge

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[76]`, `prop:typeB-bridge-sublinear`. -/
@[reducible] noncomputable def typeBBridgeSublinearRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBBridgeSublinear
    { Requires := [K .typeBBridgeMass, K .surplusAtOrBelow]
      Produces := [K .typeBBridgeSublinear]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBBridgeSublinear)
        ⟨Contracts.TypeB.typeBBridgeSublinear (inputs.get (K .typeBBridgeMass)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
