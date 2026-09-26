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

/-- Node `[69]`, `cor:compatible-pair-typeB-routing`. -/
@[reducible] noncomputable def compatiblePairTypeBRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.compatiblePairTypeBRouting
    { Requires := [K .compatiblePairFanClosure, K .fanClosedPortTypeBRouting]
      Produces := [K .compatiblePairTypeBRouting]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .compatiblePairTypeBRouting)
        ⟨Contracts.TypeB.compatiblePairTypeBRouting (data := data.toParameters) (inputs.get (K .compatiblePairFanClosure)).down
          (inputs.get (K .fanClosedPortTypeBRouting)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
