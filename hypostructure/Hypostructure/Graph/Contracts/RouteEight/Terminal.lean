import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: route-8 terminals

Proof-agnostic contract lemmas for the terminal nodes of Part IX:

* node `[124]`, `lem:typeA-carrier-deletion-exit` with
  `lem:typeA-two-carrier-deletion-canonical`: a two-support entry of a canonical
  negative zero-surplus component collection carries its canonical Q5
  exit-`(4)` witness (`twoCarrier_exitFour`), instantiated on the route-`8`
  collection `𝒳_A` and on the unified collection;
* `thm:typeA-two-carrier-nogo`: that witness contradicts the absent exit `(4)`
  of a true two-support entry;
* nodes `[119]`--`[122]`: the private-carrier budget contradicts the census;

Every lemma is stated over `Graph.FiniteObject` and the registered
`Parameters`; the paper's assumptions are explicit hypotheses.  This module
imports no vocabulary, row, or strategy module.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[124]`: `lem:typeA-carrier-deletion-exit` with
`lem:typeA-essential-deletion-witness`, `lem:typeA-deletion-witness-declared`
and `lem:typeA-two-carrier-deletion-canonical`.**

Let `𝒳` be a canonical collection of negative zero-surplus components and
`ξ = (X,w,u,B_u)` an indexed entry of `Ξ(𝒳)` whose trace basin is selected
and whose essential core has `α(ξ) ≥ 2`.  If `ξ` has at most `δ − 1` private
essential incidences in `Ξ(𝒳)`, then deleting any essential incidence is a
target-defective quotient with a declared forgotten coordinate, so it is the
Q5 member of the canonical family `𝒬₄(w)` and the load `u` has its canonical
exit-`(4)` witness at the empty peeling. -/
theorem twoCarrier_exitFour (LengthOK : Nat → Prop)
    (object : FiniteObject.{u}) (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold scale : Nat)
    (canonical : components ⊆
      object.canonicalPieces (object.remainderSupport packing))
    (negative : ∀ component ∈ components,
      object.NegativeNetCharge
          (object.pieceSupport (object.remainderSupport packing) component)
          threshold scale ∧
        object.ambientSurplus
          (object.pieceSupport (object.remainderSupport packing) component)
          threshold = 0)
    {index : Route8Census.Index object}
    (indexMem : index ∈ Route8Census.entriesOfComponents object packing
      components threshold scale)
    (twoCarrier : letI := Route8.vertexDecEq object
      Route8.IndexedTwoCarrierCore
        (Route8Census.entriesOfComponents object packing components threshold
          scale)
        (Route8Census.core object threshold LengthOK) (threshold - 1) index)
    (selected : Route8.TraceBasin.select? object index.1 threshold index.2.1
        index.2.2 = some (Route8Census.basin object threshold index))
    (alphaAtLeast : letI := Route8.vertexDecEq object
      2 ≤ ((Route8Census.presented object threshold LengthOK index).toEntry
        (HasCycleWithLength LengthOK)).alpha) :
    ∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) index.1
        threshold scale index.2.1 ∅,
      witness.load = index.2.2 := by
  classical
  letI : DecidableEq object.Vertex := Route8.vertexDecEq object
  obtain ⟨piece, receiver, load⟩ := index
  let entries := Route8Census.entriesOfComponents object packing components
    threshold scale
  let index : Route8Census.Index object := (piece, receiver, load)
  let basin := Route8Census.basin object threshold index
  let presented := Route8Census.presented object threshold LengthOK index
  let entry := presented.toEntry (HasCycleWithLength LengthOK)
  obtain ⟨_component, _componentMem, _pieceEq, _receiverMem, loadMem⟩ :=
    mem_entriesOfComponents.mp indexMem
  have coreNonempty : entry.essentialCore.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro empty
    have zero : entry.essentialCore.card = 0 := by rw [empty]; simp
    change 2 ≤ entry.essentialCore.card at alphaAtLeast
    omega
  obtain ⟨carrier, carrierMem⟩ := coreNonempty
  have deletionWitnesses := Route8.twoCarrierDeletionWitnesses
    (Target := HasCycleWithLength LengthOK) entry.carriers
    entry.coordinates entry.car entry.car_subset entry.state entries
    (Route8Census.core object threshold LengthOK) twoCarrier rfl
  obtain ⟨targetDefect, coordinate, coordinateMem, coordinateCore,
    carrierCoordinate⟩ := deletionWitnesses.2 carrier carrierMem
  have loadRouted : load ∈ object.routedLoads piece threshold receiver :=
    (Finset.mem_sdiff.mp loadMem).1
  have unpeeled : load ∈ ExitFour.unpeeledLoads piece threshold receiver ∅ := by
    rw [ExitFour.mem_unpeeledLoads]
    exact ⟨loadRouted, by simp⟩
  have sameBoundaryProfile :
      (entry.restriction (entry.essentialCore.erase carrier)).boundaryDegreeProfile =
        (entry.restriction entry.essentialCore).boundaryDegreeProfile := by
    change (presented.state
        (entry.retained (entry.essentialCore.erase carrier))).boundaryDegreeProfile =
      (presented.state (entry.retained entry.essentialCore)).boundaryDegreeProfile
    exact Route8.PresentedEntry.ofTraceBasin_boundaryDegreeProfile
      object piece basin threshold LengthOK receiver load _ _
  have canonicalCollection :
      ExitFour.Q5CanonicalCollection object packing threshold scale entries :=
    Or.inr ⟨components, canonical, negative, rfl⟩
  have q5 : ExitFour.Q5TargetDefect (HasCycleWithLength LengthOK) piece
      threshold scale receiver load := by
    refine ⟨packing, entries, canonicalCollection, (piece, receiver, load),
      indexMem, rfl, rfl, rfl, LengthOK, rfl, selected, twoCarrier,
      carrier, carrierMem, ?_, ?_, ?_⟩
    · change Response.TargetDefect (HasCycleWithLength LengthOK)
        (entry.restriction (entry.essentialCore.erase carrier))
        (entry.restriction entry.essentialCore)
      exact targetDefect
    · change (entry.restriction
            (entry.essentialCore.erase carrier)).boundaryDegreeProfile =
          (entry.restriction entry.essentialCore).boundaryDegreeProfile
      exact sameBoundaryProfile
    · refine ⟨coordinate, ?_, ?_, carrierCoordinate⟩
      · change coordinate ∈ entry.coordinates
        exact coordinateMem
      · change entry.car coordinate ⊆ entry.essentialCore
        exact coordinateCore
  exact ⟨ExitFour.Witness.ofCarrierDeletion unpeeled q5, rfl⟩

/-- The unified collection is a canonical collection of negative zero-surplus
components (`def:typeA-unified-negative`). -/
theorem route8UnifiedComponents_canonical (data : Parameters)
    (object : FiniteObject.{u}) :
    route8UnifiedComponents data object ⊆
        object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object)) ∧
      ∀ component ∈ route8UnifiedComponents data object,
        object.NegativeNetCharge
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component)
            data.threshold data.dischargeScale ∧
          object.ambientSurplus
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component)
            data.threshold = 0 := by
  classical
  refine ⟨fun component member => (Finset.mem_filter.mp member).1, ?_⟩
  intro component member
  have selected := (Finset.mem_filter.mp member).2
  exact ⟨selected.2.1, selected.1⟩

/-- The route-`8` collection `𝒳_A` is a canonical collection of negative
zero-surplus components (`def:typeA-large-budget-deficit`). -/
theorem route8SurvivorComponents_canonical (data : Parameters)
    (object : FiniteObject.{u}) :
    route8SurvivorComponents data object ⊆
        object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object)) ∧
      ∀ component ∈ route8SurvivorComponents data object,
        object.NegativeNetCharge
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component)
            data.threshold data.dischargeScale ∧
          object.ambientSurplus
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component)
            data.threshold = 0 := by
  classical
  refine ⟨fun component member => (Finset.mem_filter.mp member).1, ?_⟩
  intro component member
  have survives := (Finset.mem_filter.mp member).2
  exact ⟨survives.1, survives.2.1⟩

/-- **Node `[124]` on the unified collection.**  The unified entry census
(`lem:typeA-unified-carriers`) supplies the selected basin and `α ≥ 2` of every
unified entry, so every two-support unified entry carries its canonical
exit-`(4)` witness. -/
theorem route8UnifiedTwoCarrierExit (data : Parameters)
    (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object) :
    Route8TwoCarrierExitStatement data object
      (route8UnifiedComponents data object) := by
  intro index indexMem twoCarrier
  have facts := census index indexMem
  obtain ⟨canonical, negative⟩ := route8UnifiedComponents_canonical data object
  exact twoCarrier_exitFour data.LengthOK object
    (canonicalWindowPacking data object) (route8UnifiedComponents data object)
    data.threshold data.dischargeScale canonical negative indexMem twoCarrier
    facts.1 facts.2.1

/-- On a silent-first zero-surplus piece every excess load of a saturated
receiver is a silent excess load (`lem:typeA-silent-excess-count`), because the
zero ambient surplus and the minimum-degree baseline make the piece exactly
`δ`-regular in the ambient graph. -/
theorem route8Survivor_silentExcess (data : Parameters)
    (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (dischargePos : 0 < data.dischargeScale)
    (trueResidual : Route8TrueResidual data object)
    {component : SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))}
    (componentMem : component ∈ route8SurvivorComponents data object)
    {receiver load : object.Vertex}
    (receiverMem : receiver ∈ VisibleEntry.saturatedReceivers object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
      data.threshold data.dischargeScale)
    (loadMem : load ∈ VisibleEntry.excessBasin object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
      data.threshold data.dischargeScale receiver) :
    load ∈ VisibleEntry.silentExcess object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
      data.threshold data.dischargeScale receiver := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let support := object.remainderSupport (canonicalWindowPacking data object)
  have survives := (Finset.mem_filter.mp componentMem).2
  have trueFacts := trueResidual.2 component componentMem
  have receiverFacts := trueFacts.2 receiver receiverMem
  have exactDegree : ∀ vertex ∈ object.pieceSupport support component,
      object.degree vertex = data.threshold := by
    intro vertex vertexMem
    have nonneg := degree_ge_of_minDegree data object baseline vertex
    have summand : object.degree vertex - data.threshold = 0 :=
      Nat.eq_zero_of_le_zero
        (survives.2.1 ▸ Finset.single_le_sum
          (f := fun other => object.degree other - data.threshold)
          (fun _ _ => Nat.zero_le _) vertexMem)
    omega
  rw [VisibleEntry.silentExcess_eq_excessBasin object _ data.threshold
    data.dischargeScale (exactDegree receiver receiverFacts.1.1)
    receiverFacts.1 dischargePos
    (fun saturated => trueFacts.1 receiver receiverFacts.1 saturated)]
  exact loadMem

/-- **Node `[124]` on the route-`8` collection `𝒳_A`.**  The true route-`8`
residual supplies the selected basin of every silent entry, the node-`[115]`
no-arm supplies `α ≥ 2`, and on `𝒳_A` every excess load is silent; hence every
two-support entry of `Ξ(𝒳_A)` carries its canonical exit-`(4)` witness. -/
theorem route8SurvivorTwoCarrierExit (data : Parameters)
    (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (dischargePos : 0 < data.dischargeScale)
    (trueResidual : Route8TrueResidual data object)
    (noSmall : Route8NoSmallCoreEntry data object) :
    Route8TwoCarrierExitStatement data object
      (route8SurvivorComponents data object) := by
  classical
  intro index indexMem twoCarrier
  obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
    mem_entriesOfComponents.mp indexMem
  obtain ⟨piece, receiver, load⟩ := index
  simp only at pieceEq receiverMem loadMem
  subst pieceEq
  have silent := route8Survivor_silentExcess data object baseline dischargePos
    trueResidual componentMem receiverMem loadMem
  have entryFacts :=
    ((trueResidual.2 component componentMem).2 receiver receiverMem).2.2 load
      silent
  have notSmall := noSmall component componentMem receiver receiverMem load
    silent
  obtain ⟨canonical, negative⟩ := route8SurvivorComponents_canonical data object
  exact twoCarrier_exitFour data.LengthOK object
    (canonicalWindowPacking data object) (route8SurvivorComponents data object)
    data.threshold data.dischargeScale canonical negative indexMem twoCarrier
    entryFacts.1 (by
      change ¬ _ ≤ 1 at notSmall
      omega)

/-- **`thm:typeA-two-carrier-nogo` on the unified collection** (node `[124]`):
the terminal two-support entry has no exit-`(4)` witness, while node `[124]`
supplies one. -/
theorem route8UnifiedTrueTwoCarrierEntry_false (data : Parameters)
    (object : FiniteObject.{u})
    (trueEntry : Route8UnifiedTrueTwoCarrierEntryStatement data object)
    (exit : Route8TwoCarrierExitStatement data object
      (route8UnifiedComponents data object)) : False := by
  obtain ⟨index, indexMem, twoCarrier, _entryFacts, _minimal, noExitFour⟩ :=
    Classical.choice trueEntry
  exact noExitFour (exit index indexMem twoCarrier)

/-- **`thm:typeA-two-carrier-nogo` on `𝒳_A`** (nodes `[118]`, `[124]`): the
selected true two-support entry has no exit-`(4)` witness, while node `[124]`
supplies one. -/
theorem route8TrueTwoCarrierEntry_false (data : Parameters)
    (object : FiniteObject.{u})
    (trueEntry : Route8TrueTwoCarrierEntryStatement data object)
    (exit : Route8TwoCarrierExitStatement data object
      (route8SurvivorComponents data object)) : False := by
  obtain ⟨index, indexMem, twoCarrier, noExitFour⟩ := trueEntry
  exact noExitFour (exit index indexMem twoCarrier)

/-- **Nodes `[119]`--`[120]`** (`prop:typeA-route8-carrier-reduction`): when
no entry of `Ξ(𝒳_A)` is two-support, every entry holds at least `δ` private
essential incidences, all inside the cut of the remainder, so
`δ·|Ξ(𝒳_A)| ≤ |∂R|`. -/
theorem route8PrivateCarrierBudget_of_noTwoCarrier (data : Parameters)
    (object : FiniteObject.{u})
    (thresholdPos : 1 ≤ data.threshold)
    (noTwo : Route8NoTwoCarrierEntryStatement data object) :
    Route8PrivateCarrierBudget data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight :=
    (object.canonicalPieces support).filter (Route8Survives data object packing)
  let entries := Route8Census.entriesOfComponents object packing routeEight
    data.threshold data.dischargeScale
  let core := Route8Census.core object data.threshold data.LengthOK
  let supply := Route8Census.supply object packing
  have coresSubset : ∀ index ∈ entries, core index ⊆ supply := by
    intro index member
    obtain ⟨component, _componentMem, pieceEq, _receiverMem, _loadMem⟩ :=
      mem_entriesOfComponents.mp member
    rw [show core index = Route8Census.core object data.threshold data.LengthOK
      index from rfl]
    refine (Route8Census.core_subset_cutEdges object data.threshold
      data.LengthOK _).trans ?_
    rw [pieceEq]
    exact Route8Census.cutEdges_piece_subset object packing component
  have budget := Route8.privateCarrierBudget_of_noTwoCarrier entries core supply
    coresSubset noTwo
  change Route8PrivateCarrierBudget data object
  dsimp only [Route8PrivateCarrierBudget]
  simpa [Nat.sub_add_cancel thresholdPos] using budget

/-- **Nodes `[119]`--`[122]`** (`rem:route8-carrier-margin`): the
private-support budget `δ·|Ξ(𝒳_A)| ≤ |∂R|` contradicts the census deficit and
rate readings, since `τ_win < 3/13`. -/
theorem route8Census_privateCarrierBudget_false (data : Parameters)
    (object : FiniteObject.{u})
    (thresholdPos : 1 ≤ data.threshold)
    (census : Route8CensusStatement data object)
    (budget : Route8PrivateCarrierBudget data object) : False := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight :=
    (object.canonicalPieces support).filter (Route8Survives data object packing)
  let entries := Route8Census.entriesOfComponents object packing routeEight
    data.threshold data.dischargeScale
  let supply := Route8Census.supply object packing
  obtain ⟨deficit, rate⟩ := Route8Census.ambient_of_readings thresholdPos
    census.1 census.2
  have budget' : (data.threshold - 1 + 1) * entries.card ≤ supply.card := by
    change Route8PrivateCarrierBudget data object at budget
    dsimp only [Route8PrivateCarrierBudget] at budget
    simpa [Nat.sub_add_cancel thresholdPos] using budget
  exact Route8.privateCarrierCensus_contradiction deficit budget' rate

end Hypostructure.Graph.Contracts.RouteEight
