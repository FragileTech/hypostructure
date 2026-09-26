import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: the demand ledger and node `[181]`

* `def:typeA-pressure-ledger` with `lem:typeA-pressure-ledger-no-overcount`
  and `lem:typeA-pressure-records-canonical` on the unified collection
  (`route8DemandLedger`);
* `thm:typeA-unpaid-exit4-reduction` at the committed ledger `P₀`: the
  one-entry augmentation (168.1) (`route8UnpaidTwoCarrier`), the exact
  node-`[181]` dichotomy (`unpaidExitFour_of_not_witnessFree`), and the
  identification of outcome (i) with the terminal entry `ξ*` of
  `thm:typeA-two-carrier-nogo` (`route8UnpaidTrueEntry`).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

attribute [local instance] Route8.vertexDecEq

/-- **`def:typeA-pressure-ledger`** on the unified collection `Ξ̃`, with
`lem:typeA-pressure-ledger-no-overcount` and
`lem:typeA-pressure-records-canonical`: pinning every minimal entry with at
least `δ ≥ 3` private essential incidences, a maximal `2/3`-demand ledger
exists; its assignments satisfy the raw and defect no-overcount inequalities;
and, since the selected object has no target cycle, every unpaid
target-defect entry carries its canonical demand record. -/
theorem route8DemandLedger (data : Parameters) (object : FiniteObject.{u})
    (threeLe : 3 ≤ data.threshold)
    (avoids : ¬ HasCycleWithLength data.LengthOK object) :
    Route8DemandLedgerStatement data object := by
  classical
  letI : DecidableEq object.Vertex := Route8.vertexDecEq object
  obtain ⟨P, pinnedP, maximalP⟩ :=
    Route8Census.exists_maximal_demandLedger object
      (route8UnifiedEntries data object) data.threshold data.LengthOK
      (route8DemandPinned data object)
      (fun index memPinned =>
        ((mem_route8DemandPinned data object index).mp memPinned).1)
      (fun index memPinned => by
        have bound :=
          ((mem_route8DemandPinned data object index).mp memPinned).2.2
        unfold Route8.indexedPrivateCoreCount at bound
        exact le_trans threeLe bound)
  have counts := Route8Census.demandLedger_no_overcount object
    (canonicalWindowPacking data object) (route8UnifiedComponents data object)
    data.threshold data.dischargeScale data.LengthOK P
  refine ⟨⟨P, pinnedP, maximalP, counts.1, counts.2, ?_⟩⟩
  intro index _memUnion defect
  exact Route8.TraceBasin.exists_record_of_traceLocalTargetDefect defect avoids

/-- The committed ledger `[349]` fixes the partition `P₀`. -/
theorem canonicalRoute8Partition_exists (data : Parameters)
    (object : FiniteObject.{u})
    (ledger : Route8DemandLedgerStatement data object) :
    ∃ P, canonicalRoute8Partition data object = some P := by
  obtain ⟨record, pin⟩ := canonicalRoute8DemandRecord_spec data object ledger
  exact ⟨record.partition, by simp [canonicalRoute8Partition, pin]⟩

/-- **(168.1) of `thm:typeA-unpaid-exit4-reduction`**: in a maximal ledger an
unpaid entry with three private essential incidences could be moved to `Ξ₃`
with those incidences, contradicting the first maximality coordinate.  Hence
every unpaid entry has at most two, i.e. at most `δ − 1`, private essential
incidences. -/
theorem unpaid_twoCarrier_of_maximal (data : Parameters)
    (object : FiniteObject.{u}) (threeLe : 3 ≤ data.threshold)
    (P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (maximal : Route8MaximalDemandPartition data object P) :
    ∀ index ∈ P.two ∪ P.residual,
      Route8.IndexedTwoCarrierCore
        (route8UnifiedEntries data object) (route8DemandCore data object)
        (data.threshold - 1) index := by
  classical
  letI : DecidableEq object.Vertex := Route8.vertexDecEq object
  intro index unpaid
  let entries := route8UnifiedEntries data object
  let core := route8DemandCore data object
  have privateLe :=
    DemandPartition.Partition.privateAvailable_card_le_two_of_mem_unpaid_of_maximal
      P (Route8.indexedPrivateCoreCarriers entries core) maximal.1 maximal.2
      unpaid (Route8.indexedPrivateCoreCarriers_subset_core entries core index)
      (by
        intro other otherMem otherNe
        rw [Finset.disjoint_left]
        intro carrier inPrivate inOther
        exact (Finset.mem_filter.mp inPrivate).2 other otherMem otherNe inOther)
  change Route8.indexedPrivateCoreCount entries core index ≤ data.threshold - 1
  unfold Route8.indexedPrivateCoreCount
  omega

/-- **(168.1) at the committed ledger `P₀`** (node `[181]`). -/
theorem route8UnpaidTwoCarrier (data : Parameters) (object : FiniteObject.{u})
    (threeLe : 3 ≤ data.threshold)
    (ledger : Route8DemandLedgerStatement data object) :
    Route8UnpaidTwoCarrierStatement data object := by
  obtain ⟨P, pin⟩ := canonicalRoute8Partition_exists data object ledger
  exact ⟨P, pin, unpaid_twoCarrier_of_maximal data object threeLe P
    (canonicalRoute8Partition_spec_of_eq_some data object pin)⟩

/-- **Node `[181]` is an exact dichotomy at a ledger partition**: the negation
of outcome (i) is outcome (ii), (168.2). -/
theorem unpaidExitFour_of_not_witnessFree (data : Parameters)
    (object : FiniteObject.{u})
    (P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (none : ¬ ∃ index, Route8UnpaidWitnessFreeSpec data object P index) :
    ∀ index ∈ P.two ∪ P.residual,
      ∃ witness : ExitFour.Witness
          (HasCycleWithLength data.LengthOK) index.1 data.threshold
          data.dischargeScale index.2.1 ∅,
        witness.load = index.2.2 := by
  classical
  intro index unpaid
  by_contra absent
  exact none ⟨index, unpaid, absent⟩

/-- **Outcome (i) of `thm:typeA-unpaid-exit4-reduction` is the terminal input
of `thm:typeA-two-carrier-nogo`**: an unpaid entry without an exit-`(4)`
witness cannot be target-defective (the census attaches the witness to that
alternative), so its basin is target-complete-minimal; with (168.1) and the
census bound `α ≥ 2` it is a true two-support route-`8` entry. -/
theorem unpaidTrueEntry_at (data : Parameters) (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object)
    {P : DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)}
    (twoCarrier : ∀ index ∈ P.two ∪ P.residual,
      Route8.IndexedTwoCarrierCore
        (route8UnifiedEntries data object) (route8DemandCore data object)
        (data.threshold - 1) index)
    {index : Route8Census.Index object}
    (witnessFree : Route8UnpaidWitnessFreeSpec data object P index) :
    Route8TerminalTrueEntry data object index := by
  classical
  obtain ⟨unpaid, noExitFour⟩ := witnessFree
  have indexMem : index ∈ route8UnifiedEntries data object := by
    rcases Finset.mem_union.mp unpaid with inTwo | inResidual
    · exact P.two_subset_entries inTwo
    · exact P.residual_subset_entries inResidual
  have facts := census index indexMem
  have minimal :
      Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Route8Census.basin object data.threshold index) := by
    rcases facts.2.2 with targetComplete | targetDefect
    · exact targetComplete
    · exact False.elim (noExitFour targetDefect.2.2.2.2)
  exact ⟨indexMem, twoCarrier index unpaid, facts, minimal, noExitFour⟩

/-- **Node `[181]`, yes → node `[334]`**: on the rate-failed arm the terminal
entry `ξ` is the witness-free unpaid entry `ξ*` of `P₀`, and it is a true
two-support route-`8` entry. -/
theorem route8UnpaidTrueEntry (data : Parameters) (object : FiniteObject.{u})
    (witnessFree : Route8UnpaidWitnessFreeStatement data object)
    (twoCarrier : Route8UnpaidTwoCarrierStatement data object)
    (census : Route8UnifiedEntryCensusFact data object)
    (failed : Route8StageRateFailedFact data object) :
    Route8UnifiedTrueTwoCarrierEntryStatement data object := by
  obtain ⟨P, pin, exists_⟩ := witnessFree
  obtain ⟨P', pin', two⟩ := twoCarrier
  obtain rfl : P' = P := Option.some.inj (pin'.symm.trans pin)
  obtain ⟨index, indexPin, spec⟩ :=
    canonicalRoute8UnpaidEntry_spec data object P' exists_
  refine ⟨index, ?_, unpaidTrueEntry_at data object census two spec⟩
  rw [canonicalRoute8TerminalEntry_eq_of_rateFailed data object failed, pin']
  exact indexPin

end Hypostructure.Graph.Contracts.RouteEight
