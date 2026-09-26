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

/-- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap` at every
negative positive-surplus canonical piece. -/
@[reducible] noncomputable def typeBBridgeReductionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBBridgeReduction
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized]
      Produces := [K .typeBBridgeReduction]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBBridgeReduction)
        ⟨Contracts.TypeB.typeBBridgeReduction (inputs.get (K .selection)).down.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))
          (inputs.get (K .uncompressible)).down (inputs.get (K .remainderNormalized)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
