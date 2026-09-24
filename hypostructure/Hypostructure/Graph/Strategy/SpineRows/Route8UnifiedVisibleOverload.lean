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

/-! ## Node `[185]`: visible-first prefix exhaustion

The selected entries are still the literal members of the unified
visible-first excess basins.  Node `[184]` makes each such load visible.  If
its receiver had no overloaded completion port, the standard port-cap count
would put every visible load in the payable prefix, contradicting membership
in the excess basin.  Hence every entry retains the canonical actual
visible-four package, and the non-overloaded subfamily is empty. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
set_option maxHeartbeats 1000000 in
@[reducible] noncomputable def route8UnifiedVisibleOverloadRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8UnifiedVisibleOverload
    { Requires := [K .route8UnifiedVisibleResidual,
        K .route8PeeledDemandResidual]
      Produces := [K .route8UnifiedVisibleOverload]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let visible := (inputs.get (K .route8UnifiedVisibleResidual)).down
      let peeledResidual :=
        (inputs.get (K .route8PeeledDemandResidual)).down
      have overloadStatement : Route8UnifiedVisibleOverloadStatement data
          inputs.current.object := by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let entries := route8UnifiedEntries data inputs.current.object
          have overloaded : ∀ index ∈ entries,
              Graph.ExitFour.VisibleFourUnpeeledAt index.1 data.threshold
                data.dischargeScale index.2.1 ∅ := by
            intro index indexMem
            have indexSpec := indexMem
            simp only [entries, route8UnifiedEntries,
              Graph.Route8Census.entriesOfComponents, Finset.mem_biUnion,
              Finset.mem_image] at indexSpec
            obtain ⟨component, componentMem, receiver, receiverMem, load,
              loadMem, rfl, rfl, rfl⟩ := indexSpec
            let piece := inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)) component
            have selected := (Finset.mem_filter.mp componentMem).2
            have zeroSurplus : inputs.current.object.ambientSurplus piece
                data.threshold = 0 := selected.1
            have exactDegree : ∀ vertex ∈ piece,
                inputs.current.object.degree vertex = data.threshold := by
              intro vertex vertexMem
              have lower : data.threshold ≤
                  inputs.current.object.degree vertex :=
                le_trans inputs.current.baseline
                  (inputs.current.object.minDegree_le_degree vertex)
              have summand : inputs.current.object.degree vertex -
                  data.threshold = 0 :=
                Nat.eq_zero_of_le_zero
                  (zeroSurplus ▸ Finset.single_le_sum
                    (f := fun other =>
                      inputs.current.object.degree other - data.threshold)
                    (fun _ _ => Nat.zero_le _) vertexMem)
              omega
            have receiverFacts :
                receiver ∈ inputs.current.object.receivers piece data.threshold ∧
                  inputs.current.object.Saturated piece data.threshold
                    data.dischargeScale receiver := by
              simpa [Graph.VisibleEntry.saturatedReceivers] using receiverMem
            have isReceiver :=
              inputs.current.object.mem_receivers.mp receiverFacts.1
            have loadVisible : load ∈ Graph.VisibleEntry.visibleLoads
                inputs.current.object piece data.threshold receiver := by
              exact visible.1 (piece, receiver, load) indexMem
            by_contra noOverload
            have portCap : ∀ outside ∈
                Graph.VisibleEntry.completionPorts inputs.current.object piece
                  receiver,
                (Graph.VisibleEntry.visibleLoadsAt inputs.current.object piece
                    data.threshold receiver outside).card + 1 ≤
                  data.dischargeScale := by
              intro outside port
              have notLarge : ¬ data.dischargeScale ≤
                  (Graph.VisibleEntry.visibleLoadsAt inputs.current.object piece
                    data.threshold receiver outside).card := by
                intro large
                have atEmpty :
                    Graph.ExitFour.unpeeledVisibleLoadsAt piece data.threshold
                        receiver outside ∅ =
                      Graph.VisibleEntry.visibleLoadsAt inputs.current.object
                        piece data.threshold receiver outside := by
                  ext candidate
                  constructor
                  · intro member
                    exact (Finset.mem_inter.mp member).1
                  · intro member
                    exact Finset.mem_inter.mpr ⟨member, by
                      simp [Graph.ExitFour.unpeeledLoads,
                        Graph.VisibleEntry.visibleLoadsAt_subset
                          inputs.current.object piece data.threshold receiver
                            outside member]⟩
                exact noOverload ⟨outside, port, atEmpty.symm ▸ large⟩
              omega
            have visibleBound := Graph.VisibleEntry.card_visibleLoads_le
              inputs.current.object piece data.threshold data.dischargeScale
              (exactDegree receiver isReceiver.1) portCap
            have receiverStrict :
                inputs.current.object.internalDegree piece receiver <
                  data.threshold :=
              isReceiver.2
            have missingPositive : 1 ≤
                inputs.current.object.missingPorts piece data.threshold
                  receiver := by
              unfold Graph.FiniteObject.missingPorts
              omega
            have paid :
                (Graph.VisibleEntry.visibleLoads inputs.current.object piece
                    data.threshold receiver).card ≤
                  data.dischargeScale *
                      inputs.current.object.missingPorts piece data.threshold
                        receiver - 1 := by
              have positiveBound :
                  (Graph.VisibleEntry.visibleLoads inputs.current.object piece
                      data.threshold receiver).card + 1 ≤
                    data.dischargeScale *
                      inputs.current.object.missingPorts piece data.threshold
                        receiver :=
                le_trans (Nat.add_le_add_left missingPositive _) visibleBound
              omega
            have paidVisible :=
              Graph.VisibleEntry.visibleLoads_subset_payableSet
                inputs.current.object piece data.threshold data.dischargeScale
                receiver paid loadVisible
            exact (Finset.mem_sdiff.mp loadMem).2 paidVisible
          show Route8UnifiedVisibleOverloadStatement data
            inputs.current.object
          unfold Route8UnifiedVisibleOverloadStatement
          refine ⟨?_, ?_⟩
          · intro index indexMem
            exact Graph.ExitFour.visibleFourUnpeeledPackage index.1
              data.threshold data.dischargeScale index.2.1 ∅
              (overloaded index indexMem)
          · rw [Finset.card_eq_zero]
            apply Finset.filter_eq_empty_iff.mpr
            intro index indexMem noOverload
            exact noOverload (overloaded index indexMem)
      .cons (key := K .route8UnifiedVisibleOverload)
        ⟨overloadStatement⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
