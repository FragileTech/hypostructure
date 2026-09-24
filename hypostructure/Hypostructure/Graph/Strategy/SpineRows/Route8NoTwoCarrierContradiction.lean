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

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8NoTwoCarrierContradictionRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.route8NoTwoCarrierContradiction
    { Requires := [K .route8Census, K .route8PrivateCarrierBudget]
      Produces := [K .route8NoTwoCarrierContradiction]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let census := inputs.get (K .route8Census)
      let budget := inputs.get (K .route8PrivateCarrierBudget)
      .cons (key := K .route8NoTwoCarrierContradiction)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let routeEight :=
            (inputs.current.object.canonicalPieces support).filter
              (Route8Survives data inputs.current.object packing)
          let entries := Graph.Route8Census.entriesOfComponents
            inputs.current.object packing routeEight data.threshold
              data.dischargeScale
          let supply := Graph.Route8Census.supply inputs.current.object packing
          have thresholdPos : 1 ≤ data.threshold :=
            le_trans (by norm_num) data.three_le_threshold
          obtain ⟨deficit, rate⟩ := Graph.Route8Census.ambient_of_readings
            thresholdPos census.down.1 census.down.2
          have budget' : (data.threshold - 1 + 1) * entries.card ≤ supply.card := by
            have budgetFact := budget.down
            change Route8PrivateCarrierBudget data inputs.current.object at budgetFact
            dsimp only [Route8PrivateCarrierBudget] at budgetFact
            simpa [Nat.sub_add_cancel thresholdPos] using budgetFact
          change False
          exact Graph.Route8.privateCarrierCensus_contradiction deficit budget'
            rate⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
