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
@[reducible] noncomputable def route8PrivateCarrierBudgetRow
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
    `Hypostructure.Graph.Strategy.Spine.route8PrivateCarrierBudget
    { Requires := [K .route8NoTwoCarrierEntry]
      Produces := [K .route8PrivateCarrierBudget]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let noTwo := inputs.get (K .route8NoTwoCarrierEntry)
      .cons (key := K .route8PrivateCarrierBudget)
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
          let core := Graph.Route8Census.core inputs.current.object data.threshold
            data.LengthOK
          let supply := Graph.Route8Census.supply inputs.current.object packing
          have coresSubset :
              ∀ index ∈ entries, core index ⊆ supply := by
            intro index member
            rcases index with ⟨piece, receiver, load⟩
            simp only [entries, Graph.Route8Census.entriesOfComponents,
              Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq] at member
            obtain ⟨component, _componentMem, receiver', _receiverMem, load',
                _loadMem, rfl, rfl, rfl⟩ := member
            refine (Graph.Route8Census.core_subset_cutEdges inputs.current.object
              data.threshold data.LengthOK _).trans ?_
            exact Graph.Route8Census.cutEdges_piece_subset inputs.current.object
              packing component
          have budget := Graph.Route8.privateCarrierBudget_of_noTwoCarrier
            entries core supply coresSubset noTwo.down
          have thresholdPos : 1 ≤ data.threshold :=
            le_trans (by norm_num) data.three_le_threshold
          change Route8PrivateCarrierBudget data inputs.current.object
          dsimp only [Route8PrivateCarrierBudget]
          simpa [Nat.sub_add_cancel thresholdPos] using budget⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
