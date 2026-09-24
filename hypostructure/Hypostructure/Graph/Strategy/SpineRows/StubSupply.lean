import Hypostructure.Graph.Strategy.SpineVocabulary

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
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let baseline : ∀ vertex : inputs.current.object.Vertex,
          data.threshold ≤ inputs.current.object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (inputs.current.object.minDegree_le_degree vertex)
      let demand := (inputs.get (K .boundaryDemand)).down
      let ceiling := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .stubSupply)
        (show Value BranchState Presentation presentation data
            .stubSupply inputs.current from
          ⟨fun packing valid => by
          have links := demand packing valid
          have windowSurplus :=
            inputs.current.object.ambientSurplus_le_degreeSurplus
              (Graph.FiniteObject.windowSupport packing) data.threshold baseline
          have globalSurplus :
              inputs.current.object.degreeSurplus data.threshold ≤
                data.surplusThreshold inputs.current.object.vertexCount := ceiling
          omega⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
