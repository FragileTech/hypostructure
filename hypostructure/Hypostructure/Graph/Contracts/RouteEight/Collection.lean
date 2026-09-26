import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: the route-8 collection, its burden, census and carrier facts

Proof-agnostic contract lemmas for Part IX nodes `[110]`--`[114]`, `[120]` and
`[123]`:

* node `[110]`: the silent-core residual profile (`route8ResidualProfile`);
* node `[111]`: the exact route-`8` collection `𝒳_A` and its cleared deficit
  (`route8GlobalSqueeze`);
* node `[112]`, `lem:typeA-route8-burden` (`route8BasinBurden`);
* nodes `[111]`--`[113]`, `[120]`: the route-`8` census (`route8Census`);
* node `[114]`: the true residual, the carrier core and the carrier cut parity
  (`route8TrueResidual`, `route8CarrierCore`, `route8CarrierCutParity`);
* node `[123]`, `def:typeA-unified-negative` (`route8UnifiedNegative`).

Every lemma is stated over `Graph.FiniteObject` and the registered
`Parameters`; the paper's assumptions are explicit hypotheses.  This module
imports no vocabulary, row, or strategy module.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[110]`**: the selected route-8 residual satisfies the silent-core
residual profile.  It is the node-`[107]` no-arm residual (no decorated
handoff) with the selected receiver and peeling set exposed. -/
theorem route8ResidualProfile (data : Parameters) (object : FiniteObject.{u})
    (exitSevenFree : TypeAExitSevenFreeStatement data object) :
    SilentCoreResidualProfile data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, peeledSubset, saturated, routing,
    noCompression, noDelocalization, noHandoff⟩ := exitSevenFree
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, peeledSubset, saturated, routing,
    noCompression, noDelocalization, noHandoff⟩

/-- **Node `[111]`**: the exact route-`8` Type A collection `𝒳_A` on the
canonical packing and the cleared defining sum `s·D_A(𝒳_A)`.  This is a
definition-level fact: it reads no upstream fact. -/
theorem route8GlobalSqueeze (data : Parameters) (object : FiniteObject.{u}) :
    Route8GlobalSqueeze data object :=
  ⟨_, rfl, _, rfl⟩

/-- A zero-surplus piece at the degree baseline has every vertex of degree
exactly the baseline. -/
theorem degree_eq_threshold_of_ambientSurplus_eq_zero (data : Parameters)
    (object : FiniteObject.{u}) (baseline : data.threshold ≤ object.minDegree)
    {piece : Finset object.Vertex}
    (zero : object.ambientSurplus piece data.threshold = 0) :
    ∀ vertex ∈ piece, object.degree vertex = data.threshold := by
  intro vertex member
  have lower := degree_ge_of_minDegree data object baseline vertex
  have summand : object.degree vertex - data.threshold = 0 :=
    Nat.eq_zero_of_le_zero
      (zero ▸ Finset.single_le_sum
        (f := fun other => object.degree other - data.threshold)
        (fun _ _ => Nat.zero_le _) member)
  omega

/-- **Node `[112]`, `lem:typeA-route8-burden`**, cleared by the registered
scale: `s·D_A(𝒳_A) ≤ N_basin(𝒳_A)`. -/
theorem route8BasinBurden (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (scalePos : 0 < data.dischargeScale)
    (routing : TypeAReceiverRoutingStatement data object) :
    Route8BasinBurden data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  obtain ⟨valid, maximal⟩ := canonicalWindowPacking_valid_maximal data object
  let support := object.remainderSupport packing
  let routeEight := (object.canonicalPieces support).filter
    (Route8Survives data object packing)
  refine ⟨_, rfl, Graph.TypeBEnvelopeCharge.route8Deficit object support
    data.threshold data.dischargeScale routeEight, rfl, ?_⟩
  rw [Graph.TypeBEnvelopeCharge.route8Deficit]
  refine Finset.sum_le_sum ?_
  intro component component_mem
  have survives := (Finset.mem_filter.mp component_mem).2
  let piece := object.pieceSupport support component
  change object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      object.ambientSurplus piece data.threshold = 0 ∧
      Graph.Route8Deficit.SilentFirst object piece data.threshold
        data.dischargeScale ∧ _ at survives
  obtain ⟨_negative, zero, silentFirst, _entries⟩ := survives
  have inside : piece ⊆ object.remainderSupport packing :=
    object.pieceSupport_subset (object.remainderSupport packing) component
  have routed := routing packing valid maximal piece inside zero
  have exactDegree :=
    degree_eq_threshold_of_ambientSurplus_eq_zero data object baseline zero
  have capped : ∀ vertex ∈ piece,
      object.internalDegree piece vertex ≤ data.threshold :=
    fun vertex member => (exactDegree vertex member) ▸
      object.internalDegree_le_degree piece vertex
  have count :=
    Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency
      object piece data.threshold data.dischargeScale
      scalePos exactDegree capped routed.1 silentFirst
  have saturatedSum :
      (∑ receiver ∈ object.receivers piece data.threshold,
          (Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver).card) =
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers
            object piece data.threshold data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver).card := by
    unfold Graph.VisibleEntry.saturatedReceivers
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro receiver _receiverMem
    by_cases saturated : object.Saturated piece
        data.threshold data.dischargeScale receiver
    · simp [saturated]
    · rw [if_neg saturated]
      have loadBound :
          (object.routedLoads piece data.threshold receiver).card ≤
            data.dischargeScale *
                object.missingPorts piece data.threshold receiver - 1 := by
        have bound := (object.not_saturated_iff piece
          data.threshold data.dischargeScale receiver).mp saturated
        rw [object.routedLoad_eq_card] at bound
        omega
      have orderFinset :
          (Graph.VisibleEntry.visibleFirstOrder object piece
              data.threshold receiver).toFinset =
            object.routedLoads piece data.threshold receiver := by
        ext vertex
        simp only [Graph.VisibleEntry.visibleFirstOrder,
          List.toFinset_append, List.mem_toFinset, List.mem_filter,
          decide_eq_true_eq, Finset.mem_union, object.mem_orderedVertices]
        constructor
        · rintro (⟨_, visible⟩ | ⟨_, routedLoad, _⟩)
          · exact Graph.VisibleEntry.visibleLoads_subset
              object piece data.threshold receiver visible
          · exact routedLoad
        · intro routedLoad
          by_cases visible : vertex ∈ Graph.VisibleEntry.visibleLoads
              object piece data.threshold receiver
          · exact Or.inl ⟨trivial, visible⟩
          · exact Or.inr ⟨trivial, routedLoad, visible⟩
      have orderNodup :
          (Graph.VisibleEntry.visibleFirstOrder object piece
              data.threshold receiver).Nodup := by
        unfold Graph.VisibleEntry.visibleFirstOrder
        rw [List.nodup_append]
        refine ⟨object.orderedVertices_nodup.filter _,
          object.orderedVertices_nodup.filter _, ?_⟩
        intro first firstMem second secondMem equal
        subst second
        simp only [List.mem_filter, decide_eq_true_eq] at firstMem secondMem
        exact secondMem.2.2 firstMem.2
      have orderLength :
          (Graph.VisibleEntry.visibleFirstOrder object piece
              data.threshold receiver).length =
            (object.routedLoads piece data.threshold receiver).card := by
        rw [← orderFinset, List.toFinset_card_of_nodup orderNodup]
      have takeAll :
          (Graph.VisibleEntry.visibleFirstOrder object piece
              data.threshold receiver).take
              (data.dischargeScale *
                  object.missingPorts piece data.threshold receiver - 1) =
            Graph.VisibleEntry.visibleFirstOrder object piece
              data.threshold receiver :=
        List.take_of_length_le (by omega)
      have payable : Graph.VisibleEntry.payableSet object piece
          data.threshold data.dischargeScale receiver =
          object.routedLoads piece data.threshold receiver := by
        unfold Graph.VisibleEntry.payableSet
        rw [takeAll, orderFinset]
      have silentEmpty :
          Graph.VisibleEntry.silentExcess object piece
              data.threshold data.dischargeScale receiver = ∅ := by
        unfold Graph.VisibleEntry.silentExcess Graph.VisibleEntry.excessBasin
        rw [payable]
        ext load
        simp
      rw [silentEmpty]
      simp
  rw [saturatedSum] at count
  dsimp only [piece, support, packing] at count ⊢
  omega

/-- **Nodes `[111]`--`[113]`, `[120]`: the route-`8` census.**  The basin
burden `[112]` and the large-budget deficit `[113]` give the collection
deficit `|R| ≤ #entries + s·|supply| + F·s·T(n)`; the rate `[120]` is carried
alongside. -/
theorem route8Census (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (scalePos : 0 < data.dischargeScale)
    (burden : Route8BasinBurden data object)
    (largeBudget : Route8LargeBudgetDeficit data object)
    (rate : Route8RateStatement data object) :
    Route8CensusStatement data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight :=
    (object.canonicalPieces support).filter (Route8Survives data object packing)
  obtain ⟨basinCount, basinCountEq, scaledDeficit,
    scaledDeficitEq, burdenBound⟩ := burden
  have canonical : routeEight ⊆ object.canonicalPieces support := by
    intro component componentMem
    exact (Finset.mem_filter.mp componentMem).1
  have entryCount :
      (Graph.Route8Census.entriesOfComponents object
        packing routeEight data.threshold data.dischargeScale).card =
        ∑ component ∈ routeEight,
          ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
              (object.pieceSupport support component)
              data.threshold data.dischargeScale,
            (Graph.VisibleEntry.excessBasin object
              (object.pieceSupport support component)
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
    · intro left leftMem right _rightMem different
      rw [Function.onFun, Finset.disjoint_left]
      intro index leftIndex rightIndex
      rw [Finset.mem_biUnion] at leftIndex rightIndex
      obtain ⟨_, _, leftIndex⟩ := leftIndex
      obtain ⟨_, _, rightIndex⟩ := rightIndex
      rw [Finset.mem_image] at leftIndex rightIndex
      obtain ⟨_, _, rfl⟩ := leftIndex
      obtain ⟨_, _, equal⟩ := rightIndex
      have pieceEq :
          object.pieceSupport support left =
            object.pieceSupport support right := by
        simpa using (congrArg (fun entry => entry.1) equal).symm
      have disjoint :=
        Graph.SupportComponents.Connected.disjoint_members object support different
      obtain ⟨vertex, vertexMem⟩ :=
        Graph.SupportComponents.Connected.member_nonempty object support
          ((object.mem_canonicalPieces support).mp (canonical leftMem))
      have rightMem' : vertex ∈ object.pieceSupport support right :=
        pieceEq ▸ vertexMem
      exact Finset.disjoint_left.mp disjoint vertexMem rightMem'
  have bridge :
      (∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component)
            data.threshold data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object
            (object.pieceSupport support component)
            data.threshold data.dischargeScale receiver).card) =
      ∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component)
            data.threshold data.dischargeScale,
          (Graph.VisibleEntry.excessBasin object
            (object.pieceSupport support component)
            data.threshold data.dischargeScale receiver).card := by
    refine Finset.sum_congr rfl fun component componentMem => ?_
    refine Finset.sum_congr rfl fun receiver receiverMem => ?_
    have survives := (Finset.mem_filter.mp componentMem).2
    have isReceiver := FiniteObject.mem_receivers.mp
      (Finset.mem_filter.mp receiverMem).1
    rw [Graph.VisibleEntry.silentExcess_eq_excessBasin object _ data.threshold
      data.dischargeScale
      (degree_eq_threshold_of_ambientSurplus_eq_zero data object baseline
        survives.2.1 receiver isReceiver.1)
      isReceiver scalePos
      (fun saturated => survives.2.2.1 receiver isReceiver saturated)]
  have supplyCount := Graph.Route8Census.card_supply object packing
  refine ⟨?_, rate⟩
  change support.card ≤
    (Graph.Route8Census.entriesOfComponents object packing
        routeEight data.threshold data.dischargeScale).card +
      data.dischargeScale * (Graph.Route8Census.supply object packing).card +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount
  rw [entryCount, supplyCount]
  change support.card ≤
    (∑ component ∈ routeEight,
      ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
          (object.pieceSupport support component)
          data.threshold data.dischargeScale,
        (Graph.VisibleEntry.excessBasin object
          (object.pieceSupport support component)
          data.threshold data.dischargeScale receiver).card) +
      data.dischargeScale * object.boundaryIncidence support +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount
  change support.card ≤
      Graph.TypeBEnvelopeCharge.route8Deficit object support
          data.threshold data.dischargeScale routeEight +
        data.dischargeScale * object.boundaryIncidence support +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount at largeBudget
  change basinCount =
      ∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component)
            data.threshold data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object
            (object.pieceSupport support component)
            data.threshold data.dischargeScale receiver).card at basinCountEq
  change scaledDeficit =
      Graph.TypeBEnvelopeCharge.route8Deficit object support
        data.threshold data.dischargeScale routeEight at scaledDeficitEq
  omega

/-- **Node `[114]`, `def:typeA-true-route8-residual`**: clauses (R1)--(R4) for
every actual indexed entry of the route-`8` collection selected at `[111]`,
with clause (R3) the node-`[110]` residual profile. -/
theorem route8TrueResidual (data : Parameters) (object : FiniteObject.{u})
    (profile : SilentCoreResidualProfile data object) :
    Route8TrueResidual data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  refine ⟨profile, ?_⟩
  intro component componentMem
  let piece := object.pieceSupport support component
  have survives : Route8Survives data object packing component :=
    (Finset.mem_filter.mp componentMem).2
  obtain ⟨_negative, _zero, silentFirst, entries⟩ := survives
  refine ⟨silentFirst, ?_⟩
  intro receiver receiverMem
  have receiverFacts :
      receiver ∈ object.receivers piece data.threshold ∧
        object.Saturated piece data.threshold data.dischargeScale receiver := by
    simpa [Graph.VisibleEntry.saturatedReceivers] using receiverMem
  refine ⟨object.mem_receivers.mp receiverFacts.1, receiverFacts.2, ?_⟩
  intro load loadMem
  let index : Graph.Route8Census.Index object := (piece, receiver, load)
  let basin := Graph.Route8Census.basin object data.threshold index
  obtain ⟨⟨selectedBasin, selectedEq, minimal⟩, noExitFour⟩ :=
    entries receiver receiverMem load loadMem
  have basinEq : basin = selectedBasin := by
    change (Graph.Route8.TraceBasin.select? object piece
      data.threshold receiver load).getD ∅ = selectedBasin
    rw [selectedEq]
    rfl
  refine ⟨?_, ?_, noExitFour⟩
  · change Graph.Route8.TraceBasin.select? object piece
      data.threshold receiver load = some basin
    rw [basinEq]
    exact selectedEq
  · change Graph.Route8.TraceBasin.TargetCompleteMinimal
      object piece data.threshold data.LengthOK receiver load basin
    rw [basinEq]
    exact minimal

/-- **Node `[114]`**: every indexed entry of the route-`8` collection passes
to the essential carrier core of its graph-derived trace-basin reading.  This
is a definition-level fact: it reads no upstream fact. -/
theorem route8CarrierCore (data : Parameters) (object : FiniteObject.{u}) :
    Route8CarrierCore data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  dsimp only [Route8CarrierCore]
  intro component _componentMem receiver _receiverMem load _loadMem
  let piece := object.pieceSupport
    (object.remainderSupport (canonicalWindowPacking data object)) component
  let index : Graph.Route8Census.Index object := (piece, receiver, load)
  exact ((Graph.Route8Census.presented object data.threshold data.LengthOK
    index).toEntry (Graph.HasCycleWithLength data.LengthOK)).carrierCoreFacts

/-- **Node `[114]`, `lem:typeA-carrier-cut-parity`**: a surviving mixed event
of a retained essential-core coordinate records at least two essential
boundary incidences.  The only upstream input is (R4)'s basin containment
`B_u ⊆ X` from the true residual. -/
theorem route8CarrierCutParity (data : Parameters) (object : FiniteObject.{u})
    (trueResidual : Route8TrueResidual data object) :
    Route8CarrierCutParity data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  dsimp only [Route8CarrierCutParity]
  intro component componentMem receiver receiverMem load loadMem
    coordinate retained event eventEq internalEdge outsideEdge
  let piece := object.pieceSupport
    (object.remainderSupport (canonicalWindowPacking data object)) component
  let index : Graph.Route8Census.Index object := (piece, receiver, load)
  let presented := Graph.Route8Census.presented object data.threshold
    data.LengthOK index
  let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
  have minimal := (((trueResidual.2 component componentMem).2 receiver
    receiverMem).2.2 load loadMem).2.1
  have basinSubset :
      Graph.Route8Census.basin object data.threshold index ⊆ piece :=
    minimal.1.1
  obtain ⟨insideLeft, _insideRight, insideEdgeMem,
    insideLeftBasin, _insideRightBasin⟩ := internalEdge
  obtain ⟨outsideLeft, outsideRight, outsideEdgeMem, outsidePiece⟩ := outsideEdge
  have outsideWitness : ∃ outside,
      outside ∈ event.walk.support ∧ outside ∉ piece := by
    rcases outsidePiece with outsideLeftPiece | outsideRightPiece
    · exact ⟨outsideLeft,
        event.walk.fst_mem_support_of_mem_edges outsideEdgeMem, outsideLeftPiece⟩
    · exact ⟨outsideRight,
        event.walk.snd_mem_support_of_mem_edges outsideEdgeMem, outsideRightPiece⟩
  obtain ⟨outside, outsideWalk, outsidePiece⟩ := outsideWitness
  have crossing : presented.Crossing coordinate :=
    ⟨event, eventEq, ⟨insideLeft,
        event.walk.fst_mem_support_of_mem_edges insideEdgeMem,
        basinSubset insideLeftBasin⟩,
      outside, outsideWalk, outsidePiece⟩
  have retainedSubset : entry.car coordinate ⊆ entry.essentialCore :=
    (entry.mem_retained.mp retained).2
  rw [Finset.inter_eq_left.mpr retainedSubset]
  exact presented.two_le_card_car crossing

/-- **Node `[123]`, `def:typeA-unified-negative`**: the canonical supports with
`σ(X) = 0`, `N₀(X) < 0` and no decorated Type B handoff, each with positive
cleared summand `s·δ(X) = |V(X)| - s·def⁺(X)`, and their sum `s·\tilde D_A`.
This is a definition-level fact: it reads no upstream fact. -/
theorem route8UnifiedNegative (data : Parameters) (object : FiniteObject.{u}) :
    Route8UnifiedNegative data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let support := object.remainderSupport (canonicalWindowPacking data object)
  refine ⟨_, rfl, ?_, _, rfl⟩
  intro piece pieceMem
  rw [Finset.mem_image] at pieceMem
  obtain ⟨component, componentMem, rfl⟩ := pieceMem
  obtain ⟨zero, negative, noHandoff⟩ := (Finset.mem_filter.mp componentMem).2
  refine ⟨zero, negative, noHandoff, ?_⟩
  have deficitPositive :
      data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport support component) data.threshold <
        (object.pieceSupport support component).card := by
    simpa [Graph.FiniteObject.NegativeNetCharge, zero] using negative
  exact Nat.sub_pos_iff_lt.mpr deficitPositive

end Hypostructure.Graph.Contracts.RouteEight
