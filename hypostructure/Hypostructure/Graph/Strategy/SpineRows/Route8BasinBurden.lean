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
@[reducible] noncomputable def route8BasinBurdenRow
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
    `Hypostructure.Graph.Strategy.Spine.route8BasinBurden
    { Requires := [K .route8GlobalSqueeze, K .typeAReceiverRouting]
      Produces := [K .route8BasinBurden]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let global := inputs.get (K .route8GlobalSqueeze)
      let routing := inputs.get (K .typeAReceiverRouting)
      let burden : Route8BasinBurden data inputs.current.object := by
        classical
        letI : DecidableEq inputs.current.object.Vertex :=
          inputs.current.object.vertices.decEq
        obtain ⟨_collection, _collection_eq, scaledDeficit,
          scaledDeficit_eq⟩ := global.down
        let packing := canonicalWindowPacking data inputs.current.object
        have packingSpec := Classical.choose_spec
          (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
        have valid : inputs.current.object.IsWindowPacking data.windowOrder
            packing := packingSpec.1
        have maximal : ∀ window : Finset inputs.current.object.Vertex,
            inputs.current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member :=
          fun window induces =>
            inputs.current.object.exists_mem_not_disjoint_of_card_eq
              data.windowOrder_pos valid packingSpec.2 induces
        let support := inputs.current.object.remainderSupport packing
        let routeEight := (inputs.current.object.canonicalPieces support).filter
          (Route8Survives data inputs.current.object packing)
        let basinCount :=
          ∑ component ∈ routeEight,
            ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                inputs.current.object
                (inputs.current.object.pieceSupport support component)
                data.threshold data.dischargeScale,
              (Graph.VisibleEntry.silentExcess inputs.current.object
                (inputs.current.object.pieceSupport support component)
                data.threshold data.dischargeScale receiver).card
        have scaledDeficit_eq' : scaledDeficit =
            Graph.TypeBEnvelopeCharge.route8Deficit inputs.current.object support
              data.threshold data.dischargeScale routeEight := by
          simpa [packing, support, routeEight] using scaledDeficit_eq
        refine ⟨basinCount, rfl, scaledDeficit, scaledDeficit_eq', ?_⟩
        dsimp only [basinCount]
        rw [scaledDeficit_eq', Graph.TypeBEnvelopeCharge.route8Deficit]
        refine Finset.sum_le_sum ?_
        intro component component_mem
        have survives := (Finset.mem_filter.mp component_mem).2
        let piece := inputs.current.object.pieceSupport support component
        change inputs.current.object.NegativeNetCharge piece data.threshold
              data.dischargeScale ∧
            inputs.current.object.ambientSurplus piece data.threshold = 0 ∧
            Graph.Route8Deficit.SilentFirst inputs.current.object piece
              data.threshold data.dischargeScale ∧
            _ at survives
        obtain ⟨_negative, zero, silentFirst, _entries⟩ := survives
        have inside : piece ⊆ inputs.current.object.remainderSupport packing := by
          simpa [piece, support] using
            inputs.current.object.pieceSupport_subset
              (inputs.current.object.remainderSupport packing) component
        have routed := routing.down packing valid maximal piece inside zero
        have exactDegree : ∀ vertex ∈ piece,
            inputs.current.object.degree vertex = data.threshold := by
          intro vertex member
          have lower : data.threshold ≤ inputs.current.object.degree vertex :=
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
          have summand :
              inputs.current.object.degree vertex - data.threshold = 0 :=
            Nat.eq_zero_of_le_zero
              (zero ▸ Finset.single_le_sum
                (f := fun other =>
                  inputs.current.object.degree other - data.threshold)
                (fun _ _ => Nat.zero_le _) member)
          omega
        have capped : ∀ vertex ∈ piece,
            inputs.current.object.internalDegree piece vertex ≤ data.threshold :=
          fun vertex member => (exactDegree vertex member) ▸
            inputs.current.object.internalDegree_le_degree piece vertex
        have count :=
          Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency
            inputs.current.object piece data.threshold data.dischargeScale
            data.dischargeScale_pos exactDegree capped routed.1 silentFirst
        have saturatedSum :
            (∑ receiver ∈ inputs.current.object.receivers piece data.threshold,
                (Graph.VisibleEntry.silentExcess inputs.current.object piece
                  data.threshold data.dischargeScale receiver).card) =
              ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                  inputs.current.object piece data.threshold data.dischargeScale,
                (Graph.VisibleEntry.silentExcess inputs.current.object piece
                  data.threshold data.dischargeScale receiver).card := by
          classical
          unfold Graph.VisibleEntry.saturatedReceivers
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro receiver receiverMem
          by_cases saturated : inputs.current.object.Saturated piece
              data.threshold data.dischargeScale receiver
          · simp [saturated]
          · rw [if_neg saturated]
            have loadBound :
                (inputs.current.object.routedLoads piece data.threshold
                    receiver).card ≤
                  data.dischargeScale *
                      inputs.current.object.missingPorts piece data.threshold
                        receiver - 1 := by
              have bound := (inputs.current.object.not_saturated_iff piece
                data.threshold data.dischargeScale receiver).mp saturated
              rw [inputs.current.object.routedLoad_eq_card] at bound
              omega
            have orderFinset :
                (Graph.VisibleEntry.visibleFirstOrder inputs.current.object piece
                    data.threshold receiver).toFinset =
                  inputs.current.object.routedLoads piece data.threshold receiver := by
              ext vertex
              simp only [Graph.VisibleEntry.visibleFirstOrder,
                List.toFinset_append, List.mem_toFinset, List.mem_filter,
                decide_eq_true_eq, Finset.mem_union,
                inputs.current.object.mem_orderedVertices]
              constructor
              · rintro (⟨_, visible⟩ | ⟨_, routedLoad, _⟩)
                · exact Graph.VisibleEntry.visibleLoads_subset
                    inputs.current.object piece data.threshold receiver visible
                · exact routedLoad
              · intro routedLoad
                by_cases visible : vertex ∈ Graph.VisibleEntry.visibleLoads
                    inputs.current.object piece data.threshold receiver
                · exact Or.inl ⟨trivial, visible⟩
                · exact Or.inr ⟨trivial, routedLoad, visible⟩
            have orderNodup :
                (Graph.VisibleEntry.visibleFirstOrder inputs.current.object piece
                    data.threshold receiver).Nodup := by
              unfold Graph.VisibleEntry.visibleFirstOrder
              rw [List.nodup_append]
              refine ⟨inputs.current.object.orderedVertices_nodup.filter _,
                inputs.current.object.orderedVertices_nodup.filter _, ?_⟩
              intro first firstMem second secondMem equal
              subst second
              simp only [List.mem_filter, decide_eq_true_eq] at firstMem secondMem
              exact secondMem.2.2 firstMem.2
            have orderLength :
                (Graph.VisibleEntry.visibleFirstOrder inputs.current.object piece
                    data.threshold receiver).length =
                  (inputs.current.object.routedLoads piece data.threshold
                    receiver).card := by
              rw [← orderFinset, List.toFinset_card_of_nodup orderNodup]
            have takeAll :
                (Graph.VisibleEntry.visibleFirstOrder inputs.current.object piece
                    data.threshold receiver).take
                    (data.dischargeScale *
                        inputs.current.object.missingPorts piece data.threshold
                          receiver - 1) =
                  Graph.VisibleEntry.visibleFirstOrder inputs.current.object piece
                    data.threshold receiver :=
              List.take_of_length_le (by omega)
            have payable : Graph.VisibleEntry.payableSet inputs.current.object piece
                data.threshold data.dischargeScale receiver =
                inputs.current.object.routedLoads piece data.threshold receiver := by
              unfold Graph.VisibleEntry.payableSet
              rw [takeAll, orderFinset]
            have silentEmpty :
                Graph.VisibleEntry.silentExcess inputs.current.object piece
                    data.threshold data.dischargeScale receiver = ∅ := by
              unfold Graph.VisibleEntry.silentExcess
                Graph.VisibleEntry.excessBasin
              rw [payable]
              ext load
              simp
            rw [silentEmpty]
            simp
        rw [saturatedSum] at count
        dsimp only [piece, support, packing] at count ⊢
        omega
      .cons (key := K .route8BasinBurden) ⟨burden⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
