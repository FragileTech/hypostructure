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

/-! Nodes `[111]`--`[113]`, `[120]`: the exact route-`8` census is its basin
count/large-budget consequence and the boundary rate on one ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8CensusRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8Census
    { Requires := [K .route8BasinBurden, K .route8LargeBudgetDeficit,
        K .route8Rate]
      Produces := [K .route8Census]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let burden := (inputs.get (K .route8BasinBurden)).down
      let largeBudget := (inputs.get (K .route8LargeBudgetDeficit)).down
      let rate := (inputs.get (K .route8Rate)).down
      .cons (key := K .route8Census)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let routeEight :=
            (inputs.current.object.canonicalPieces support).filter
              (Route8Survives data inputs.current.object packing)
          obtain ⟨basinCount, basinCountEq, scaledDeficit,
            scaledDeficitEq, burdenBound⟩ := burden
          have canonical : routeEight ⊆
              inputs.current.object.canonicalPieces support := by
            intro component componentMem
            exact (Finset.mem_filter.mp componentMem).1
          have entryCount :
              (Graph.Route8Census.entriesOfComponents inputs.current.object
                packing routeEight data.threshold data.dischargeScale).card =
                ∑ component ∈ routeEight,
                  ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                      inputs.current.object
                      (inputs.current.object.pieceSupport support component)
                      data.threshold data.dischargeScale,
                    (Graph.VisibleEntry.excessBasin inputs.current.object
                      (inputs.current.object.pieceSupport support component)
                      data.threshold data.dischargeScale receiver).card := by
            unfold Graph.Route8Census.entriesOfComponents
            rw [Finset.card_biUnion]
            · refine Finset.sum_congr rfl fun component _ => ?_
              rw [Finset.card_biUnion]
              · refine Finset.sum_congr rfl fun receiver _ => ?_
                rw [Finset.card_image_of_injective]
                intro left right equal
                simpa using equal
              · intro left _ right _ different
                rw [Function.onFun, Finset.disjoint_left]
                intro index leftMem rightMem
                rw [Finset.mem_image] at leftMem rightMem
                obtain ⟨_, _, rfl⟩ := leftMem
                obtain ⟨_, _, equal⟩ := rightMem
                exact different (Eq.symm (by
                  simpa using (congrArg (fun entry => entry.2.1) equal)))
            · intro left leftMem right rightMem different
              rw [Function.onFun, Finset.disjoint_left]
              intro index leftIndex rightIndex
              rw [Finset.mem_biUnion] at leftIndex rightIndex
              obtain ⟨_, _, leftIndex⟩ := leftIndex
              obtain ⟨_, _, rightIndex⟩ := rightIndex
              rw [Finset.mem_image] at leftIndex rightIndex
              obtain ⟨_, _, rfl⟩ := leftIndex
              obtain ⟨_, _, equal⟩ := rightIndex
              have pieceEq :
                  inputs.current.object.pieceSupport support left =
                    inputs.current.object.pieceSupport support right := by
                simpa using (congrArg (fun entry => entry.1) equal).symm
              have disjoint :=
                Graph.SupportComponents.Connected.disjoint_members
                  inputs.current.object support different
              have nonempty :=
                Graph.SupportComponents.Connected.member_nonempty
                  inputs.current.object support
                    ((inputs.current.object.mem_canonicalPieces support).mp
                      (canonical leftMem))
              obtain ⟨vertex, vertexMem⟩ := nonempty
              have rightMem' : vertex ∈ inputs.current.object.pieceSupport
                  support right := pieceEq ▸ vertexMem
              exact Finset.disjoint_left.mp disjoint vertexMem rightMem'
          have exactDegreeAt : ∀ component ∈ routeEight,
              ∀ vertex ∈ inputs.current.object.pieceSupport support component,
              inputs.current.object.degree vertex = data.threshold := by
            intro component componentMem vertex vertexMem
            have surplusZero := ((Finset.mem_filter.mp componentMem).2).2.1
            have nonneg := le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
            have summand : inputs.current.object.degree vertex -
                data.threshold = 0 :=
              Nat.eq_zero_of_le_zero
                (surplusZero ▸ Finset.single_le_sum
                  (f := fun other =>
                    inputs.current.object.degree other - data.threshold)
                  (fun _ _ => Nat.zero_le _) vertexMem)
            omega
          have bridge :
              (∑ component ∈ routeEight,
                ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                    inputs.current.object
                    (inputs.current.object.pieceSupport support component)
                    data.threshold data.dischargeScale,
                  (Graph.VisibleEntry.silentExcess inputs.current.object
                    (inputs.current.object.pieceSupport support component)
                    data.threshold data.dischargeScale receiver).card) =
              ∑ component ∈ routeEight,
                ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                    inputs.current.object
                    (inputs.current.object.pieceSupport support component)
                    data.threshold data.dischargeScale,
                  (Graph.VisibleEntry.excessBasin inputs.current.object
                    (inputs.current.object.pieceSupport support component)
                    data.threshold data.dischargeScale receiver).card := by
            refine Finset.sum_congr rfl fun component componentMem => ?_
            refine Finset.sum_congr rfl fun receiver receiverMem => ?_
            have survives := (Finset.mem_filter.mp componentMem).2
            have isReceiver := FiniteObject.mem_receivers.mp
              (Finset.mem_filter.mp receiverMem).1
            rw [Graph.VisibleEntry.silentExcess_eq_excessBasin
              inputs.current.object _ data.threshold data.dischargeScale
              (exactDegreeAt component componentMem receiver isReceiver.1)
              isReceiver data.dischargeScale_pos
              (fun saturated => survives.2.2.1 receiver isReceiver saturated)]
          have supplyCount := Graph.Route8Census.card_supply
            inputs.current.object packing
          refine ⟨?_, rate⟩
          change support.card ≤
            (Graph.Route8Census.entriesOfComponents inputs.current.object packing
                routeEight data.threshold data.dischargeScale).card +
              data.dischargeScale *
                (Graph.Route8Census.supply inputs.current.object packing).card +
              data.bridgeMassFactor * data.dischargeScale *
                data.surplusThreshold inputs.current.object.vertexCount
          rw [entryCount, supplyCount]
          change support.card ≤
            (∑ component ∈ routeEight,
              ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                  inputs.current.object
                  (inputs.current.object.pieceSupport support component)
                  data.threshold data.dischargeScale,
                (Graph.VisibleEntry.excessBasin inputs.current.object
                  (inputs.current.object.pieceSupport support component)
                  data.threshold data.dischargeScale receiver).card) +
              data.dischargeScale * inputs.current.object.boundaryIncidence support +
              data.bridgeMassFactor * data.dischargeScale *
                data.surplusThreshold inputs.current.object.vertexCount
          change support.card ≤
              Graph.TypeBEnvelopeCharge.route8Deficit inputs.current.object support
                  data.threshold data.dischargeScale routeEight +
                data.dischargeScale *
                    inputs.current.object.boundaryIncidence support +
                data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold inputs.current.object.vertexCount at largeBudget
          change basinCount =
              ∑ component ∈ routeEight,
                ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                    inputs.current.object
                    (inputs.current.object.pieceSupport support component)
                    data.threshold data.dischargeScale,
                  (Graph.VisibleEntry.silentExcess inputs.current.object
                    (inputs.current.object.pieceSupport support component)
                    data.threshold data.dischargeScale receiver).card at basinCountEq
          change scaledDeficit =
              Graph.TypeBEnvelopeCharge.route8Deficit inputs.current.object support
                data.threshold data.dischargeScale routeEight at scaledDeficitEq
          omega⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
