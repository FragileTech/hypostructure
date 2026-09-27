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

/-- Node `[69]`, `prop:triangular-port-typeB-routing`: the heavy triangular
alternative routes to fan-closed ports with
`D_B ≥ ((s+1)k - (s(δ+2) - 1))/s`, the manuscript's `(5k - 19)/4`. -/
@[reducible] noncomputable def triangularPortTypeBRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.triangularPortTypeBRouting
    { Requires := [K .fanClosedPortTypeBRouting, K .cubicBaseline]
      Produces := [K .triangularPortTypeBRouting]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .triangularPortTypeBRouting)
        ⟨Contracts.TypeB.triangularPortTypeBRouting (data := data.toParameters)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.1.2.1
          (inputs.get (K .fanClosedPortTypeBRouting)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
