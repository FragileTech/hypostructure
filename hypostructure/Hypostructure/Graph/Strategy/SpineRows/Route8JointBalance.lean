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

/-! ## Node `[186]`: joint accounting on the visible-overload residual

This row does not restart the demand construction.  It reads the exact peel
chain, unified deficit, committed maximal partition, and the already committed
empty-dependence maximal absorption simultaneously.  The resulting equalities
account for every entry and demand unit, while the four inequalities retain
the peel, boundary, bridge, and open-unit costs without subtraction. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
set_option maxHeartbeats 2000000 in
@[reducible] noncomputable def route8JointBalanceRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8JointBalance
    { Requires := [K .route8UnifiedVisibleOverload,
        K .route8UnifiedVisibleResidual, K .route8PeeledDemandResidual,
        K .route8UnifiedDeficit, K .route8DemandUnitCount]
      Produces := [K .route8JointBalance]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let overload := inputs.get (K .route8UnifiedVisibleOverload)
      let visibleResidual := inputs.get (K .route8UnifiedVisibleResidual)
      let residual := inputs.get (K .route8PeeledDemandResidual)
      let unifiedDeficit := inputs.get (K .route8UnifiedDeficit)
      .cons (key := K .route8JointBalance)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let entries := route8UnifiedEntries data inputs.current.object
          let components := route8UnifiedComponents data inputs.current.object
          let core := route8DemandCore data inputs.current.object
          let supply := Graph.Route8Census.supply inputs.current.object packing
          let bridgeAllowance := data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold inputs.current.object.vertexCount
          have entriesEq : entries =
              Graph.Route8Census.entriesOfComponents inputs.current.object
                packing components data.threshold data.dischargeScale := rfl
          have visibleEntries : ∀ index ∈ entries,
              index.2.2 ∈ Graph.VisibleEntry.visibleLoads
                inputs.current.object index.1 data.threshold index.2.1 :=
            (show Route8UnifiedVisibleResidualStatement data
                inputs.current.object from visibleResidual.down).1
          have allSaturatedVisible :
              ∀ component ∈ components,
                let piece := inputs.current.object.pieceSupport support component
                ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                    inputs.current.object piece data.threshold
                      data.dischargeScale,
                  inputs.current.object.routedLoads piece data.threshold receiver ⊆
                    Graph.VisibleEntry.visibleLoads inputs.current.object piece
                      data.threshold receiver := by
            intro component componentMem
            let piece := inputs.current.object.pieceSupport support component
            change ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                inputs.current.object piece data.threshold data.dischargeScale,
              inputs.current.object.routedLoads piece data.threshold receiver ⊆
                Graph.VisibleEntry.visibleLoads inputs.current.object piece
                  data.threshold receiver
            intro receiver receiverMem load loadMem
            by_contra loadSilent
            let capacity := data.dischargeScale *
                inputs.current.object.missingPorts
                  piece data.threshold receiver - 1
            have saturated : inputs.current.object.Saturated
                piece data.threshold data.dischargeScale receiver :=
              (Finset.mem_filter.mp receiverMem).2
            have routedPositive : 0 <
                (inputs.current.object.routedLoads
                  piece data.threshold receiver).card :=
              Finset.card_pos.mpr ⟨load, loadMem⟩
            have capacityLt : capacity <
                (inputs.current.object.routedLoads
                  piece data.threshold receiver).card := by
              dsimp only [capacity]
              unfold Graph.FiniteObject.Saturated at saturated
              change data.dischargeScale *
                  inputs.current.object.missingPorts
                    piece data.threshold receiver ≤
                (inputs.current.object.routedLoads
                  piece data.threshold receiver).card at saturated
              omega
            have excessVisible : ∀ candidate,
                candidate ∈ Graph.VisibleEntry.excessBasin
                    inputs.current.object piece
                    data.threshold data.dischargeScale receiver →
                  candidate ∈ Graph.VisibleEntry.visibleLoads
                    inputs.current.object piece
                    data.threshold receiver := by
              intro candidate candidateMem
              have indexMem : (piece, receiver, candidate) ∈ entries := by
                rw [entriesEq]
                simp only [Graph.Route8Census.entriesOfComponents,
                  Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
                exact ⟨component, componentMem, receiver, receiverMem,
                  candidate, candidateMem, rfl, rfl, rfl⟩
              exact visibleEntries (piece, receiver, candidate) indexMem
            by_cases visibleFits :
                (Graph.VisibleEntry.visibleLoads inputs.current.object
                  piece data.threshold receiver).card ≤ capacity
            · have visiblePaid :=
                Graph.VisibleEntry.visibleLoads_subset_payableSet
                  inputs.current.object
                  piece data.threshold data.dischargeScale receiver (by
                    simpa only [capacity] using visibleFits)
              have payableCard := Graph.VisibleEntry.card_payableSet_le
                inputs.current.object
                piece data.threshold data.dischargeScale receiver
              have payableLt :
                  (Graph.VisibleEntry.payableSet inputs.current.object
                    piece data.threshold data.dischargeScale receiver).card <
                    (inputs.current.object.routedLoads
                      piece data.threshold receiver).card := by
                dsimp only [capacity] at capacityLt
                exact lt_of_le_of_lt payableCard capacityLt
              obtain ⟨candidate, candidateRouted, candidateUnpaid⟩ :=
                Finset.exists_mem_notMem_of_card_lt_card payableLt
              have candidateExcess : candidate ∈
                  Graph.VisibleEntry.excessBasin inputs.current.object
                    piece data.threshold data.dischargeScale receiver :=
                Finset.mem_sdiff.mpr ⟨candidateRouted, candidateUnpaid⟩
              exact candidateUnpaid (visiblePaid
                (excessVisible candidate candidateExcess))
            · have capacityLeVisible : capacity ≤
                  (Graph.VisibleEntry.visibleLoads inputs.current.object
                    piece data.threshold receiver).card := by
                omega
              let visibleBlock :=
                inputs.current.object.orderedVertices.filter fun vertex =>
                  decide (vertex ∈ Graph.VisibleEntry.visibleLoads
                    inputs.current.object
                    piece data.threshold receiver)
              have blockFinset : visibleBlock.toFinset =
                  Graph.VisibleEntry.visibleLoads inputs.current.object
                    piece data.threshold receiver := by
                ext vertex
                simp [visibleBlock, List.mem_toFinset,
                  inputs.current.object.mem_orderedVertices vertex]
              have blockLength : visibleBlock.length =
                  (Graph.VisibleEntry.visibleLoads inputs.current.object
                    piece data.threshold receiver).card := by
                rw [← blockFinset, List.toFinset_card_of_nodup]
                exact inputs.current.object.orderedVertices_nodup.filter _
              have capacityLeLength : capacity ≤ visibleBlock.length := by
                rw [blockLength]
                exact capacityLeVisible
              have payableVisible :
                  Graph.VisibleEntry.payableSet inputs.current.object
                      piece data.threshold data.dischargeScale receiver ⊆
                    Graph.VisibleEntry.visibleLoads inputs.current.object
                      piece data.threshold receiver := by
                intro candidate candidateMem
                change candidate ∈
                  ((Graph.VisibleEntry.visibleFirstOrder inputs.current.object
                    piece data.threshold receiver).take capacity).toFinset at candidateMem
                rw [List.mem_toFinset] at candidateMem
                change candidate ∈
                    (visibleBlock ++
                      inputs.current.object.orderedVertices.filter fun vertex =>
                        decide (vertex ∈
                          inputs.current.object.routedLoads
                            piece data.threshold receiver ∧
                          vertex ∉ Graph.VisibleEntry.visibleLoads
                            inputs.current.object piece
                            data.threshold receiver)).take capacity at candidateMem
                rw [List.take_append_of_le_length capacityLeLength] at candidateMem
                have inBlock := List.mem_of_mem_take candidateMem
                rw [← blockFinset, List.mem_toFinset]
                exact inBlock
              have loadUnpaid : load ∉
                  Graph.VisibleEntry.payableSet inputs.current.object
                    piece data.threshold data.dischargeScale receiver :=
                fun paid => loadSilent (payableVisible paid)
              exact loadSilent (excessVisible load
                (Finset.mem_sdiff.mpr ⟨loadMem, loadUnpaid⟩))
          have residualFact : Route8PeeledDemandResidualStatement data
              inputs.current.object := residual.down
          obtain ⟨stage, ledger, absorption, _blockers⟩ := residualFact
          obtain ⟨chain, chainValid, accounting, rateFailed⟩ := stage
          obtain ⟨record⟩ := ledger
          obtain ⟨A, dep, absorbedUnits, absorberSupplied,
              absorberSameSupport, depUnits, depDisjoint, depEmpty, maximalA,
              display⟩ :=
            absorption record.partition record.pinned record.maximal
              record.rawNoOvercount record.defectNoOvercount
          subst dep
          have supplied : ∀ index ∈
              record.partition.three ∪ record.partition.two,
              record.partition.assigned index ⊆ supply := by
            intro index memUnion
            have memEntries : index ∈
                Graph.Route8Census.entriesOfComponents inputs.current.object
                  packing components data.threshold data.dischargeScale := by
              have memUnified : index ∈ entries := by
                rcases Finset.mem_union.mp memUnion with mem | mem
                · exact record.partition.three_subset_entries mem
                · exact record.partition.two_subset_entries mem
              simpa only [entries, route8UnifiedEntries] using memUnified
            exact (record.partition.assigned_available index memUnion).trans
              (Graph.Route8Census.core_subset_supply_ofComponents
                inputs.current.object packing components data.threshold
                data.dischargeScale data.LengthOK index memEntries)
          have maximalEmpty : ∀ B : Graph.DemandPartition.Absorption
                record.partition
                (Graph.Route8Census.Index inputs.current.object × Nat),
              B.absorbed ⊆ record.partition.demandUnits →
                (∀ unit ∈ B.absorbed, B.absorber unit ∈ supply) →
                (∀ unit ∈ B.absorbed,
                  B.absorber unit ∈ Graph.Route8.cutEdges
                    inputs.current.object unit.1.1) →
                B.absorbed.card ≤ A.absorbed.card := by
            intro B units suppliedB sameSupportB
            exact maximalA B units suppliedB sameSupportB (by simp)
          have rawCapacity :=
            A.three_mul_add_two_mul_add_card_le supply supplied
              absorberSupplied
          have classes := record.partition.card_entries_eq
          change entries.card = record.partition.three.card +
            record.partition.two.card + record.partition.residual.card at classes
          have unitsCard := (inputs.get (K .route8DemandUnitCount)).down record.partition
          change record.partition.demandUnits.card =
            record.partition.two.card +
              3 * record.partition.residual.card at unitsCard
          have entryDemandIdentity : 3 * entries.card =
              (3 * record.partition.three.card +
                2 * record.partition.two.card) +
                record.partition.demandUnits.card := by
            omega
          let openUnits := record.partition.demandUnits \ A.absorbed
          have unitSplitRaw :=
            Finset.card_sdiff_add_card_eq_card absorbedUnits
          have unitSplit : record.partition.demandUnits.card =
              A.absorbed.card + openUnits.card := by
            dsimp only [openUnits]
            calc
              record.partition.demandUnits.card =
                  (record.partition.demandUnits \ A.absorbed).card +
                    A.absorbed.card := unitSplitRaw.symm
              _ = A.absorbed.card +
                  (record.partition.demandUnits \ A.absorbed).card :=
                Nat.add_comm _ _
          have pressureBalance : 3 * entries.card ≤
              supply.card + openUnits.card := by
            omega
          let peeled := chain.toFinset
          let reduced := Graph.Route8Pressure.peeledEntries
            inputs.current.object entries peeled
          let deficit := Graph.TypeBEnvelopeCharge.route8Deficit
            inputs.current.object support data.threshold data.dischargeScale
              components
          have accountingOut := accounting
          change peeled ⊆ entries ∧
              entries = reduced ∪ peeled ∧
              Disjoint reduced peeled ∧
              peeled.card ≤ deficit ∧
              deficit = deficit - peeled.card + peeled.card ∧
              deficit ≤ reduced.card + peeled.card ∧
              deficit - peeled.card ≤ reduced.card ∧
              support.card ≤ reduced.card + peeled.card +
                data.dischargeScale * supply.card +
                  2 * bridgeAllowance at accounting
          obtain ⟨_peeledEntries, entriesUnion, entriesDisjoint, peeledLe,
            _deficitExact, deficitLeParts, _reducedDeficit, _stageBound⟩ :=
            accounting
          have entriesCard : entries.card = reduced.card + peeled.card := by
            rw [entriesUnion,
              Finset.card_union_of_disjoint entriesDisjoint]
          have deficitLeEntries : deficit ≤ entries.card := by omega
          let unused := entries.card - deficit
          have entriesSplit : entries.card = deficit + unused := by
            dsimp only [unused]
            omega
          have ambientRaw : Route8UnifiedDeficitFact data
              inputs.current.object := unifiedDeficit.down
          have ambientBalance : support.card ≤
              deficit + data.dischargeScale * supply.card +
                bridgeAllowance := by
            change support.card ≤
                deficit + data.dischargeScale * supply.card +
                  bridgeAllowance at ambientRaw
            exact ambientRaw
          change ¬ ((data.threshold * data.dischargeScale + 1) *
                supply.card + data.threshold * (2 * bridgeAllowance) +
                data.threshold * peeled.card <
              data.threshold * support.card) at rateFailed
          have failedRateBalance : data.threshold * support.card ≤
              (data.threshold * data.dischargeScale + 1) * supply.card +
                data.threshold * (2 * bridgeAllowance) +
                data.threshold * peeled.card :=
            Nat.le_of_not_gt rateFailed
          have jointPressureBalance : 3 * support.card ≤
              (3 * data.dischargeScale + 1) * supply.card +
                3 * bridgeAllowance + openUnits.card := by
            have scaledAmbient : 3 * support.card ≤
                3 * deficit + 3 * (data.dischargeScale * supply.card) +
                  3 * bridgeAllowance := by
              simpa only [Nat.mul_add] using
                Nat.mul_le_mul_left 3 ambientBalance
            have deficitPressure : 3 * deficit ≤
                supply.card + openUnits.card :=
              (Nat.mul_le_mul_left 3 deficitLeEntries).trans pressureBalance
            simp only [Nat.add_mul, Nat.mul_assoc, one_mul]
            omega
          have noSilentTerminal :
              ∀ component ∈ components,
                let piece := inputs.current.object.pieceSupport support component
                ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers
                    inputs.current.object piece data.threshold
                      data.dischargeScale,
                  ∀ peeled : Finset inputs.current.object.Vertex,
                    ¬ Graph.ExitFour.SilentUnpeeledExcessAt piece
                      data.threshold data.dischargeScale receiver peeled := by
            intro component componentMem
            dsimp only
            intro receiver receiverMem peeled silent
            unfold Graph.ExitFour.SilentUnpeeledExcessAt at silent
            obtain ⟨load, loadMem⟩ := silent.2.1
            have silentMem := Finset.mem_sdiff.mp (silent.2.2 loadMem)
            have routed :=
              ((Graph.ExitFour.mem_unpeeledLoads
                (object := inputs.current.object)
                (inputs.current.object.pieceSupport support component)
                data.threshold receiver).mp silentMem.1).1
            exact silentMem.2
              (allSaturatedVisible component componentMem receiver receiverMem
                routed)
          show Route8JointBalanceStatement data inputs.current.object
          unfold Route8JointBalanceStatement
          refine ⟨overload.down, allSaturatedVisible, noSilentTerminal,
            chain, ?_, ?_,
            record.partition, ?_, ?_, A,
            absorbedUnits, ?_, absorberSameSupport, maximalEmpty, unused, ?_⟩
          · exact chainValid
          · exact accountingOut
          · exact record.pinned
          · exact record.maximal
          · exact absorberSupplied
          · exact ⟨peeledLe, deficitLeEntries, entriesSplit, ambientBalance,
              pressureBalance, jointPressureBalance, failedRateBalance,
              entryDemandIdentity,
              unitSplit, rawCapacity⟩
        ⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
