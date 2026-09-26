import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineRemainder

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! Node `[29]`, `lem:stub-positive`.  This is deliberately a second ledger
append after node `[28]`: it reads the registered boundary-demand chain and the
near-cubic surplus ceiling from that literal residual, then publishes only the
finite external-incidence supply bound. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def stubSupplyRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.stubSupply
    { Requires := [K .boundaryDemand, K .surplusAtOrBelow]
      Produces := [K .stubSupply]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .stubSupply)
        ⟨Contracts.Spine.stubSupply_of_boundaryDemand data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .boundaryDemand)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
