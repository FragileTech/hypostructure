import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[88]`: receiver routing and the threshold algebra

`lem:typeA-receiver-loads` and `lem:typeA-threshold-algebra` at every
zero-surplus subregion of a maximal packing's remainder, from node `[27]`'s
empty internal baseline core.  Thin adapter of
`Contracts.TypeA.typeAReceiverRouting`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}

@[reducible] noncomputable def typeAReceiverRoutingRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAReceiverRouting
    { Requires := [K .remainderNormalized]
      Produces := [K .typeAReceiverRouting]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAReceiverRouting)
        ⟨Graph.Contracts.TypeA.typeAReceiverRouting data.toParameters
          inputs.current.object (inputs.get (K .remainderNormalized)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
