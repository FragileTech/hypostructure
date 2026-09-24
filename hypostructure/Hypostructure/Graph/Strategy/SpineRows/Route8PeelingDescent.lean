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

set_option maxHeartbeats 1000000 in
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8PeelingDescentRow
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
    `Hypostructure.Graph.Strategy.Spine.route8PeelingDescent
    { Requires := [K .route8UnifiedDeficit, K .typeAReceiverRouting]
      Produces := [K .route8PeelingDescent]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let census := inputs.get (K .route8UnifiedDeficit)
      let receiverRouting := inputs.get (K .typeAReceiverRouting)
      .cons (key := K .route8PeelingDescent)
        (show Value BranchState Presentation presentation data
            .route8PeelingDescent inputs.current from
          ⟨by
            classical
            letI : DecidableEq inputs.current.object.Vertex :=
              inputs.current.object.vertices.decEq
            let packing := canonicalWindowPacking data inputs.current.object
            let support := inputs.current.object.remainderSupport packing
            let components := route8UnifiedComponents data inputs.current.object
            let entries := route8UnifiedEntries data inputs.current.object
            let scaledDeficit := Graph.TypeBEnvelopeCharge.route8Deficit
              inputs.current.object support data.threshold data.dischargeScale
                components
            let slack := 2 * (data.bridgeMassFactor * data.dischargeScale *
              data.surplusThreshold inputs.current.object.vertexCount)
            have thresholdPos : 1 ≤ data.threshold :=
              le_trans (by norm_num) data.three_le_threshold
            have dischargePos : 1 ≤ data.dischargeScale := data.dischargeScale_pos
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex := fun vertex =>
              le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have packingSpec := Classical.choose_spec
              (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
            have valid : inputs.current.object.IsWindowPacking data.windowOrder
                packing := packingSpec.1
            have maximal : ∀ window : Finset inputs.current.object.Vertex,
                inputs.current.object.InducesWindow data.windowOrder window →
                ∃ member ∈ packing, ¬ Disjoint window member := fun window induces =>
              inputs.current.object.exists_mem_not_disjoint_of_card_eq
                data.windowOrder_pos valid packingSpec.2 induces
            have componentsSub : components ⊆
                inputs.current.object.canonicalPieces support :=
              Finset.filter_subset _ _
            have surplusZero : ∀ component ∈ components,
                inputs.current.object.ambientSurplus
                  (inputs.current.object.pieceSupport support component)
                  data.threshold = 0 := fun component componentMem =>
              ((Finset.mem_filter.1 componentMem).2).1
            have routedFact : ∀ piece : Finset inputs.current.object.Vertex,
                piece ⊆ support →
                inputs.current.object.ambientSurplus piece data.threshold = 0 →
                ∀ vertex ∈ piece,
                  inputs.current.object.internalDegree piece vertex =
                    data.threshold →
                  ∃ receiver : inputs.current.object.Vertex,
                    inputs.current.object.traceReceiver? piece data.threshold
                        vertex = some receiver ∧
                      inputs.current.object.IsReceiver piece data.threshold
                        receiver := fun piece sub zero =>
              (receiverRouting.down packing valid maximal piece sub zero).1
            have entriesSubset : entries ⊆
                Graph.Route8Census.entries inputs.current.object packing
                  data.threshold data.dischargeScale := by
              intro index member
              rcases index with ⟨piece, receiver, load⟩
              simp only [entries, route8UnifiedEntries,
                Graph.Route8Census.entriesOfComponents, Finset.mem_biUnion,
                Finset.mem_image, Prod.mk.injEq] at member
              obtain ⟨component, componentMem, receiver', receiverMem, load',
                loadMem, rfl, rfl, rfl⟩ := member
              apply (Graph.Route8Census.mem_entries inputs.current.object).2
              refine ⟨?_, (Finset.mem_filter.1 receiverMem).1, loadMem⟩
              simp only [Graph.Route8Census.typeAPieces, Finset.mem_filter,
                Finset.mem_image]
              have selected := (Finset.mem_filter.1 componentMem).2
              exact ⟨⟨component, (Finset.mem_filter.1 componentMem).1, rfl⟩,
                selected.2.1, selected.1⟩
            have unifiedDeficit : support.card ≤
                scaledDeficit + data.dischargeScale *
                    (Graph.Route8Census.supply inputs.current.object packing).card +
                  slack := by
              have raw : Route8UnifiedDeficitFact data inputs.current.object :=
                census.down
              have strong : support.card ≤
                  scaledDeficit + data.dischargeScale *
                      (Graph.Route8Census.supply inputs.current.object packing).card +
                    data.bridgeMassFactor * data.dischargeScale *
                      data.surplusThreshold
                        inputs.current.object.vertexCount := by
                simpa [Route8UnifiedDeficitFact, support, components,
                  scaledDeficit] using raw
              simp only [slack]
              omega
            show ∃ final : List (Graph.Route8Census.Index inputs.current.object),
              Graph.Route8Pressure.StageOutcome inputs.current.object packing entries
                components data.threshold data.dischargeScale slack data.LengthOK
                final
            suffices key : ∀ n : Nat,
                ∀ chain : List (Graph.Route8Census.Index inputs.current.object),
                  Graph.Route8Pressure.PeelChain inputs.current.object packing entries
                      data.threshold data.dischargeScale slack data.LengthOK chain →
                    chain.toFinset ⊆ entries →
                    (entries \ chain.toFinset).card = n →
                    ∃ final,
                      Graph.Route8Pressure.StageOutcome inputs.current.object packing entries
                        components data.threshold data.dischargeScale slack data.LengthOK
                        final from
              key _ [] Graph.Route8Pressure.PeelChain.nil (by simp) rfl
            intro n
            induction n using Nat.strong_induction_on with
            | _ n ih =>
              intro chain valid' chainSub cardEq
              -- The stage-local four-class accounting is independent of the
              -- rate test.  In particular it remains available on the failed
              -- arm routed to node `[181]`.
              have burden := Graph.Route8Pressure.stage_burden
                inputs.current.object packing components data.threshold
                data.dischargeScale dischargePos baseline componentsSub
                surplusZero routedFact chain.toFinset
              have burden' : scaledDeficit ≤
                  (Graph.Route8Pressure.peeledEntries inputs.current.object
                      entries chain.toFinset).card + chain.toFinset.card := by
                simpa [scaledDeficit, support, entries, route8UnifiedEntries]
                  using burden
              have stageDeficit : support.card ≤
                  (Graph.Route8Pressure.peeledEntries inputs.current.object
                      entries chain.toFinset).card + chain.toFinset.card +
                    data.dischargeScale *
                      (Graph.Route8Census.supply inputs.current.object
                        packing).card +
                    slack := by
                omega
              have partition : entries =
                  Graph.Route8Pressure.peeledEntries inputs.current.object
                      entries chain.toFinset ∪ chain.toFinset := by
                ext index
                simp only [Graph.Route8Pressure.peeledEntries,
                  Finset.mem_union, Finset.mem_sdiff]
                constructor
                · intro indexMem
                  by_cases peeledMem : index ∈ chain.toFinset
                  · exact Or.inr peeledMem
                  · exact Or.inl ⟨indexMem, peeledMem⟩
                · rintro (⟨indexMem, _⟩ | peeledMem)
                  · exact indexMem
                  · exact chainSub peeledMem
              have reducedDisjoint : Disjoint
                  (Graph.Route8Pressure.peeledEntries inputs.current.object
                    entries chain.toFinset) chain.toFinset := by
                rw [Finset.disjoint_left]
                intro index reducedMem peeledMem
                exact (Finset.mem_sdiff.1 reducedMem).2 peeledMem
              have peeledLeDeficit : chain.toFinset.card ≤ scaledDeficit := by
                induction valid' with
                | nil => simp
                | @cons previousChain index previous previousRate member _ _ ih =>
                    have fresh : index ∉ previousChain.toFinset :=
                      (Finset.mem_sdiff.1 member).2
                    have rateRaw :
                        (data.threshold * data.dischargeScale + 1) *
                            (Graph.Route8Census.supply inputs.current.object
                              packing).card +
                            data.threshold * slack +
                            data.threshold * previousChain.toFinset.card <
                          data.threshold * support.card := by
                      simpa only [Graph.Route8Pressure.StageRate, support] using
                        previousRate
                    have scaledBudget := Nat.mul_le_mul_left data.threshold
                      unifiedDeficit
                    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at scaledBudget
                    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at rateRaw
                    have scaledPeel :
                        data.threshold * previousChain.toFinset.card <
                          data.threshold * scaledDeficit := by
                      omega
                    have previousLt : previousChain.toFinset.card <
                        scaledDeficit := Nat.lt_of_mul_lt_mul_left scaledPeel
                    rw [List.toFinset_cons,
                      Finset.card_insert_of_notMem fresh]
                    omega
              have exactReduced : scaledDeficit =
                  scaledDeficit - chain.toFinset.card + chain.toFinset.card :=
                (Nat.sub_add_cancel peeledLeDeficit).symm
              have reducedBurden : scaledDeficit - chain.toFinset.card ≤
                  (Graph.Route8Pressure.peeledEntries inputs.current.object
                    entries chain.toFinset).card := by
                omega
              have accounting : Graph.Route8Pressure.StageAccounting
                  inputs.current.object packing entries components data.threshold
                    data.dischargeScale slack chain := by
                exact ⟨chainSub, partition, reducedDisjoint, peeledLeDeficit,
                  exactReduced, burden', reducedBurden, stageDeficit⟩
              by_cases rate : Graph.Route8Pressure.StageRate
                  inputs.current.object packing data.threshold data.dischargeScale
                  slack chain.toFinset
              ·
                obtain ⟨index, member, two⟩ :=
                  Graph.Route8Pressure.exists_twoCarrierEntry_staged
                    inputs.current.object packing entries data.threshold
                    data.dischargeScale slack data.LengthOK thresholdPos
                    entriesSubset chain.toFinset stageDeficit rate
                by_cases targetDefect : Graph.Route8Pressure.TargetDefectAt
                    inputs.current.object data.threshold data.dischargeScale
                    (Graph.HasCycleWithLength data.LengthOK) chain.toFinset index
                · have valid'' := Graph.Route8Pressure.PeelChain.cons
                    (object := inputs.current.object) valid' rate member two
                    targetDefect
                  have fresh : index ∉ chain.toFinset :=
                    (Finset.mem_sdiff.1 member).2
                  have idxAll : index ∈ entries :=
                    Graph.Route8Pressure.peeledEntries_subset
                      inputs.current.object entries chain.toFinset member
                  have smaller :
                      (entries \ (index :: chain).toFinset).card < n := by
                    rw [← cardEq]
                    apply Finset.card_lt_card
                    rw [Finset.ssubset_iff_of_subset]
                    · refine ⟨index, Finset.mem_sdiff.2 ⟨idxAll, fresh⟩, ?_⟩
                      simp [List.toFinset_cons]
                    · intro other otherMem
                      simp only [List.toFinset_cons, Finset.mem_sdiff,
                        Finset.mem_insert, not_or] at otherMem ⊢
                      exact ⟨otherMem.1, otherMem.2.2⟩
                  refine ih _ smaller (index :: chain) valid'' ?_ rfl
                  rw [List.toFinset_cons]
                  exact Finset.insert_subset idxAll chainSub
                · exact ⟨chain, valid', accounting,
                    Or.inl ⟨rate, index, member, two, targetDefect⟩⟩
              · exact ⟨chain, valid', accounting, Or.inr rate⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
