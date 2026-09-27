import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Local

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[69]`, `def:fan-closed-port`, with clause (c) derived. -/
@[reducible] noncomputable def fanClosedPortRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fanClosedPort
    { Requires := [K .typeBFanEntry, K .surplusAtOrBelow]
      Produces := [K .fanClosedPort]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanClosedPort)
        ⟨Contracts.TypeB.fanClosedPort (inputs.get (K .typeBFanEntry)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
