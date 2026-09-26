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

/-- Node `[69]`, `prop:fan-closed-port-typeB-routing` (a)--(b). -/
@[reducible] noncomputable def fanClosedPortTypeBRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fanClosedPortTypeBRouting
    { Requires := [K .fanClosedPort]
      Produces := [K .fanClosedPortTypeBRouting]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanClosedPortTypeBRouting)
        ⟨Contracts.TypeB.fanClosedPortTypeBRouting (data := data.toParameters) (inputs.get (K .fanClosedPort)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
