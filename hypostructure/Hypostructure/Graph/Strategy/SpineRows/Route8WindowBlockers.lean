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
set_option maxHeartbeats 1000000 in
@[reducible] noncomputable def route8WindowBlockersRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8WindowBlockers
    { Requires := [K .route8UnifiedEntryCensus,
        K .route8DemandAbsorption, K .route8DemandLedger]
      Produces := [K .route8WindowBlockers]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let census := (inputs.get (K .route8UnifiedEntryCensus)).down
      let _absorption := inputs.get (K .route8DemandAbsorption)
      let _ledger := inputs.get (K .route8DemandLedger)
      .cons (key := K .route8WindowBlockers)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          show Route8WindowBlockersStatement data inputs.current.object
          unfold Route8WindowBlockersStatement
          refine fun P _pinnedP _maximalP _raw _defect A dep _absorbedUnits
            _absorberSupplied _depUnits _depDisjoint => ?_
          let packing := canonicalWindowPacking data inputs.current.object
          let remainder := inputs.current.object.remainderSupport packing
          let entries := route8UnifiedEntries data inputs.current.object
          let core := route8DemandCore data inputs.current.object
          let openUnits := P.demandUnits \ (A.absorbed ∪ dep)
          have blockerAt : ∀ υ :
              Graph.Route8Census.Index inputs.current.object × Nat,
              ∃ carrier : Sym2 inputs.current.object.Vertex,
                ∃ window : Finset inputs.current.object.Vertex,
                  υ ∈ openUnits →
                    carrier ∈ core υ.1 ∧
                      ∃ inside ∈ carrier, ∃ outside ∈ carrier,
                        inside ∈ remainder ∧ outside ∉ remainder ∧
                          outside ∈ window ∧ window ∈ packing := by
            intro υ
            by_cases υMem : υ ∈ openUnits
            · have unitMem : υ ∈ P.demandUnits :=
                (Finset.mem_sdiff.mp υMem).1
              have fstMem :=
                Graph.DemandPartition.Partition.fst_mem_of_mem_demandUnits
                  unitMem
              have entryMem : υ.1 ∈ entries := by
                rcases Finset.mem_union.mp fstMem with mem | mem
                · exact P.two_subset_entries mem
                · exact P.residual_subset_entries mem
              have alphaAtLeast := (census υ.1 entryMem).2.1
              have coreNonempty : (core υ.1).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro empty
                have zero : (core υ.1).card = 0 := by rw [empty]; simp
                change 2 ≤ (core υ.1).card at alphaAtLeast
                omega
              obtain ⟨carrier, carrierMem⟩ := coreNonempty
              have entryMem' : υ.1 ∈
                  Graph.Route8Census.entriesOfComponents
                    inputs.current.object packing
                    (route8UnifiedComponents data inputs.current.object)
                    data.threshold data.dischargeScale := by
                simpa only [entries, route8UnifiedEntries] using entryMem
              have carrierSupply : carrier ∈
                  Graph.Route8Census.supply inputs.current.object packing :=
                Graph.Route8Census.core_subset_supply_ofComponents
                  inputs.current.object packing
                  (route8UnifiedComponents data inputs.current.object)
                  data.threshold data.dischargeScale data.LengthOK υ.1
                  entryMem' carrierMem
              change carrier ∈ Graph.Route8.cutEdges inputs.current.object
                remainder at carrierSupply
              rw [Graph.Route8.mem_cutEdges] at carrierSupply
              obtain ⟨_edgeMem, inside, insideMem, outside, outsideMem,
                insideRemainder, outsideRemainder⟩ := carrierSupply
              obtain ⟨window, windowMem, outsideWindow⟩ :=
                inputs.current.object.exists_mem_packing_of_notMem_remainderSupport
                  outsideRemainder
              exact ⟨carrier, window, fun _ =>
                ⟨carrierMem, inside, insideMem, outside, outsideMem,
                  insideRemainder, outsideRemainder, outsideWindow,
                  windowMem⟩⟩
            · refine ⟨s(υ.1.2.1, υ.1.2.1), ∅, ?_⟩
              intro present
              exact (υMem present).elim
          choose carrier blocker blockerSpec using blockerAt
          have assigned : ∀ υ ∈ openUnits,
              carrier υ ∈ core υ.1 ∧
                ∃ inside ∈ carrier υ, ∃ outside ∈ carrier υ,
                  inside ∈ remainder ∧ outside ∉ remainder ∧
                    outside ∈ blocker υ ∧ blocker υ ∈ packing := by
            intro υ υMem
            exact blockerSpec υ υMem
          have assignedWindow : ∀ υ ∈ openUnits,
              blocker υ ∈ packing := by
            intro υ υMem
            obtain ⟨_carrierMem, inside, _insideMem, outside, _outsideMem,
              _insideRemainder, _outsideRemainder, _outsideWindow,
              windowMem⟩ := assigned υ υMem
            exact windowMem
          exact ⟨carrier, blocker, assigned,
            Graph.DemandPartition.card_eq_sum_fibres openUnits packing blocker
              assignedWindow⟩
        ⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
