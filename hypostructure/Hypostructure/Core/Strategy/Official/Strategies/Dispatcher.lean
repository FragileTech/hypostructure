import Hypostructure.Core.Strategy.Official.Availability
import Hypostructure.Core.Strategy.Official.Strategies

/-! Closed Core dispatcher for the canonical finite strategies and CT
compositions.

The dispatcher resolves a closed `OfficialRegistry.Id` to an exact dependent
output.  Unsupported IDs are rejected with `none`; there is no residual or
generic fallback constructor.  Feature strategies (predecessor-capability
driven) are resolved through their required typed producers rather than
through a static problem slot.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.Dispatcher

open OfficialRegistry

/-- Core support is a closed equation, not an extensible registration map. -/
def supports : Id → Bool
  | .orderedExhaustion
  | .responseClassification
  | .capacityAccounting
  | .supportLocalization
  | .rankBudget
  | .closedCodeExhaustion
  | .strictReplacement
  | .measuredFinitePeel
  | .defectiveLoadPeeling
  | .finiteResponseCapacity
  | .finiteEligibleTokenLedger
  | .finiteStateBudget
  | .finiteTraceSeparator
  | .finiteContextQuotient
  | .finiteObstructionAccounting
  | .finiteErrorCoefficientSchedule
  | .multiplicativeRateTable
  | .orderedReceiverPressure
  | .finiteReplacementClassification
  | .finiteObservationRank
  | .finiteOverloadGeometry
  | .finiteRankCarrierCompression
  | .finiteRankEntropySupportComposition
  | .canonicalReplacementSearch
  | .receiverExhaustion => true
  | _ => false

/-- Exact dependent output of a Core-owned invocation. -/
inductive Result (schema : ProblemSchema) (ref : Ref) where
  | ordered (slot : ScheduleSlot)
      (slot_eq : schema.core.schedules[ref.slot]? = some slot)
      (terminal : OrderedExhaustion.Terminal slot)
  | responses (slot : FunctionTableSlot)
      (slot_eq : schema.core.responseTables[ref.slot]? = some slot)
      (terminal : ResponseClassification.Terminal slot)
  | capacities (slot : NatTableSlot)
      (slot_eq : schema.core.capacityTables[ref.slot]? = some slot)
      (terminal : CapacityAccounting.Terminal slot)
  | support (slot : RelationSlot)
      (slot_eq : schema.core.supportRelations[ref.slot]? = some slot)
      (terminal : SupportLocalization.Terminal slot)
  | ranks (slot : NatTableSlot)
      (slot_eq : schema.core.rankTables[ref.slot]? = some slot)
      (terminal : RankBudget.Terminal slot)
  | codes (slot : FunctionTableSlot)
      (slot_eq : schema.core.closedCodeTables[ref.slot]? = some slot)
      (terminal : ClosedCodeExhaustion.Terminal slot)
  | strictReplacement (slot : FunctionTableSlot)
      (slot_eq : schema.core.responseTables[ref.slot]? = some slot)
      (terminal : StrictReplacement.Terminal slot)
  | measuredFinitePeel (slot : ScheduleSlot)
      (slot_eq : schema.core.schedules[ref.slot]? = some slot)
      (terminal : MeasuredFinitePeel.Terminal slot)
  | defectiveLoadPeeling (slot : ScheduleSlot)
      (slot_eq : schema.core.schedules[ref.slot]? = some slot)
      (terminal : DefectiveLoadPeeling.Terminal slot)
  | finiteResponseCapacity
      (terminal : FiniteResponseCapacity.Terminal)
  | finiteEligibleTokenLedger
      (terminal : FiniteEligibleTokenLedger.Terminal)
  | finiteStateBudget
      (terminal : FiniteStateBudget.Terminal)
  | finiteTraceSeparator
      (terminal : FiniteTraceSeparator.Terminal)
  | finiteContextQuotient
      (terminal : FiniteContextQuotient.Terminal)
  | finiteObstructionAccounting
      (terminal : FiniteObstructionAccounting.Terminal)
  | finiteErrorCoefficientSchedule
      (terminal : FiniteErrorCoefficientSchedule.Terminal)
  | multiplicativeRateTable
      (terminal : MultiplicativeRateTable.Terminal)
  | orderedReceiverPressure
      (terminal : OrderedReceiverPressure.Terminal)
  | finiteReplacementClassification
      (terminal : FiniteReplacementClassification.Terminal)
  | finiteObservationRank
      (terminal : FiniteObservationRank.Terminal)
  | finiteOverloadGeometry
      (terminal : FiniteOverloadGeometry.Terminal)
  | finiteRankCarrierCompression
      (terminal : FiniteRankCarrierCompression.Terminal)
  | finiteRankEntropySupportComposition
      (terminal : FiniteRankEntropySupportComposition.Terminal)
  | finiteHomogeneousFibrePressure
      (terminal : FiniteHomogeneousFibrePressure.Terminal)
  | canonicalReplacementSearch
      (mode : CanonicalReplacementSearch.Mode)
      (terminal : CanonicalReplacementSearch.Terminal)
  | receiverExhaustion (slot : ScheduleSlot)
      (slot_eq : schema.core.schedules[ref.slot]? = some slot)
      (terminal : ReceiverExhaustion.Terminal slot)

/-- Closed semantic resolution. Unsupported IDs are rejected with `none`;
there is no residual or generic fallback constructor. -/
def resolve (schema : ProblemSchema) (ref : Ref) :
    Option (Result schema ref) := by
  match ref.id with
  | .orderedExhaustion =>
      if hs : ref.slot < schema.core.schedules.length then
        let slot := schema.core.schedules[ref.slot]
        have heq : schema.core.schedules[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.ordered slot heq (OrderedExhaustion.execute slot))
      else exact none
  | .responseClassification =>
      if hs : ref.slot < schema.core.responseTables.length then
        let slot := schema.core.responseTables[ref.slot]
        have heq : schema.core.responseTables[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.responses slot heq (ResponseClassification.execute slot))
      else exact none
  | .capacityAccounting =>
      if hs : ref.slot < schema.core.capacityTables.length then
        let slot := schema.core.capacityTables[ref.slot]
        have heq : schema.core.capacityTables[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.capacities slot heq (CapacityAccounting.execute slot))
      else exact none
  | .supportLocalization =>
      if hs : ref.slot < schema.core.supportRelations.length then
        let slot := schema.core.supportRelations[ref.slot]
        have heq : schema.core.supportRelations[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.support slot heq (SupportLocalization.execute slot))
      else exact none
  | .rankBudget =>
      if hs : ref.slot < schema.core.rankTables.length then
        let slot := schema.core.rankTables[ref.slot]
        have heq : schema.core.rankTables[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.ranks slot heq (RankBudget.execute slot))
      else exact none
  | .closedCodeExhaustion =>
      if hs : ref.slot < schema.core.closedCodeTables.length then
        let slot := schema.core.closedCodeTables[ref.slot]
        have heq : schema.core.closedCodeTables[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.codes slot heq (ClosedCodeExhaustion.execute slot))
      else exact none
  | .strictReplacement =>
      if hs : ref.slot < schema.core.responseTables.length then
        let slot := schema.core.responseTables[ref.slot]
        have heq : schema.core.responseTables[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.strictReplacement slot heq (StrictReplacement.execute slot))
      else exact none
  | .measuredFinitePeel =>
      if hs : ref.slot < schema.core.schedules.length then
        let slot := schema.core.schedules[ref.slot]
        have heq : schema.core.schedules[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.measuredFinitePeel slot heq (MeasuredFinitePeel.execute slot))
      else exact none
  | .defectiveLoadPeeling =>
      if hs : ref.slot < schema.core.schedules.length then
        let slot := schema.core.schedules[ref.slot]
        have heq : schema.core.schedules[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.defectiveLoadPeeling slot heq (DefectiveLoadPeeling.execute slot))
      else exact none
  | .canonicalReplacementSearch =>
      if hs : ref.slot < schema.core.schedules.length then
        let slot := schema.core.schedules[ref.slot]
        exact some (.canonicalReplacementSearch (.ordered slot)
          (CanonicalReplacementSearch.execute (.ordered slot)))
      else exact none
  | .receiverExhaustion =>
      if hs : ref.slot < schema.core.schedules.length then
        let slot := schema.core.schedules[ref.slot]
        have heq : schema.core.schedules[ref.slot]? = some slot :=
          List.getElem?_eq_getElem hs
        exact some (.receiverExhaustion slot heq (ReceiverExhaustion.execute slot))
      else exact none
  | _ => exact none

theorem rejects_unsupported (schema : ProblemSchema) (ref : Ref)
    (h : supports ref.id = false) : resolve schema ref = none := by
  rcases ref with ⟨id, slot⟩
  cases id <;> simp_all [supports, resolve]

end Hypostructure.Core.Strategy.Official.Strategies.Dispatcher
