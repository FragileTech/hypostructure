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

/-- Nodes `[75]`/`[84]`: `def:typeB-residual-mass`, `lem:typeB-bridge-deficit-bound`,
`lem:typeB-bridge-with-route8-core`, `lem:decorated-envelope-with-route8-core`. -/
@[reducible] noncomputable def bridgeFanMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.bridgeFanMass
    { Requires := [K .cubicBaseline]
      Produces := [K .typeBBridgeMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBBridgeMass)
        ⟨Contracts.TypeB.typeBBridgeMass (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.2⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
