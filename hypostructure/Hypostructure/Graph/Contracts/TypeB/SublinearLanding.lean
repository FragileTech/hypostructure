import Hypostructure.Graph.Contracts.TypeB.SublinearFlow
import Hypostructure.Graph.Statements.TypeBSublinearLanding

/-!
# Contracts: where the canonical trace lands, and the corrected mass bound
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

open scoped Classical in
theorem bridgePieceMassDichotomy
    (normalized : RemainderNormalizedStatement data object) :
    BridgePieceMassDichotomyStatement data object := by
  classical
  intro component present
  by_cases hA1 : BridgeTraceIntoCentre data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
  · exact Or.inl hA1
  by_cases hA2 : BridgeLoadFails data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
  · exact Or.inr (Or.inl hA2)
  refine Or.inr (Or.inr ?_)
  set piece := object.pieceSupport
    (object.remainderSupport (canonicalWindowPacking data object)) component with hpiece
  set cen := Graph.TypeBRefinedSupport.centres object data.threshold piece with hcen
  have route := pieceRoutingTotal normalized component present
  have flow := loadFlowValue (data := data) (object := object) piece cen
    (fun v hv full => by
      obtain ⟨found, routed, isRec⟩ := route v (Finset.mem_sdiff.mp hv).1 full
      exact ⟨found, routed, isRec, fun inC => hA1 ⟨v, hv, full, found, inC, routed⟩⟩)
    (fun r hr => by
      by_contra h
      exact hA2 ⟨r, hr, Nat.lt_of_not_le h⟩)
  have ports := (receiverPortsAreWindowStubs (data := data) (object := object)
    component present).2
  have portSub : ∑ r ∈ object.receivers piece data.threshold \ cen,
      object.missingPorts piece data.threshold r ≤
      object.positiveDeficiency piece data.threshold := by
    rw [ports]
    exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have cover : piece ⊆ (piece \ cen).filter
        (fun v => object.internalDegree piece v = data.threshold) ∪
      (object.receivers piece data.threshold \ cen) ∪ cen := by
    intro v hv
    by_cases inC : v ∈ cen
    · exact Finset.mem_union_right _ inC
    · apply Finset.mem_union_left
      have hle := object.internalDegree_le_degree piece v
      rcases Nat.lt_trichotomy (object.internalDegree piece v) data.threshold with
        lt | eq | gt
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Graph.FiniteObject.mem_receivers.mpr ⟨hv, lt⟩, inC⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hv, inC⟩, eq⟩)
      · exact absurd (Graph.TypeBRefinedSupport.mem_centres.mpr
          ⟨hv, show data.threshold < object.degree v by omega⟩) inC
  have cenBound : cen.card ≤ object.ambientSurplus piece data.threshold := by
    calc cen.card = ∑ _v ∈ cen, 1 := by simp
      _ ≤ ∑ v ∈ cen, (object.degree v - data.threshold) :=
        Finset.sum_le_sum fun v hv => by
          have := (Graph.TypeBRefinedSupport.mem_centres.mp hv).2
          have : data.threshold < object.degree v := this
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset (fun v hv =>
        (Graph.TypeBRefinedSupport.mem_centres.mp hv).1)
  have card1 := Finset.card_le_card cover
  have card2 := Finset.card_union_le
    ((piece \ cen).filter (fun v => object.internalDegree piece v = data.threshold) ∪
      (object.receivers piece data.threshold \ cen)) cen
  have card3 := Finset.card_union_le
    ((piece \ cen).filter (fun v => object.internalDegree piece v = data.threshold))
    (object.receivers piece data.threshold \ cen)
  have mul : data.dischargeScale *
      ∑ r ∈ object.receivers piece data.threshold \ cen,
        object.missingPorts piece data.threshold r ≤
      data.dischargeScale * object.positiveDeficiency piece data.threshold :=
    Nat.mul_le_mul_left _ portSub
  omega

/-- A vertex outside the remainder is in the packed windows. -/
theorem mem_windowSupport_of_not_mem_remainder {vertex : object.Vertex}
    (h : vertex ∉ object.remainderSupport (canonicalWindowPacking data object)) :
    vertex ∈ Graph.FiniteObject.windowSupport (canonicalWindowPacking data object) := by
  classical
  by_contra notWindow
  apply h
  unfold Graph.FiniteObject.remainderSupport
  simp [notWindow]

/-- A vertex with two more incidences than internal neighbours in a support has
two distinct neighbours outside it. -/
theorem two_outside_neighbours (support : Finset object.Vertex) (centre : object.Vertex)
    (gap : 2 ≤ object.degree centre - object.internalDegree support centre) :
    ∃ first second : object.Vertex, first ≠ second ∧
      object.graph.Adj centre first ∧ object.graph.Adj centre second ∧
      first ∉ support ∧ second ∉ support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have hd : object.degree centre = (object.graph.neighborFinset centre).card := by
    simp [Graph.FiniteObject.degree]
  have hi : object.internalDegree support centre =
      (object.graph.neighborFinset centre ∩ support).card := by
    simp [Graph.FiniteObject.internalDegree]
  have split := Finset.card_sdiff_add_card_inter (object.graph.neighborFinset centre)
    support
  have two : 1 < (object.graph.neighborFinset centre \ support).card := by omega
  obtain ⟨first, firstMem, second, secondMem, different⟩ := Finset.one_lt_card.mp two
  obtain ⟨firstNb, firstOut⟩ := Finset.mem_sdiff.mp firstMem
  obtain ⟨secondNb, secondOut⟩ := Finset.mem_sdiff.mp secondMem
  exact ⟨first, second, different, (SimpleGraph.mem_neighborFinset _ _ _).mp firstNb,
    (SimpleGraph.mem_neighborFinset _ _ _).mp secondNb, firstOut, secondOut⟩

theorem traceIntoCentreStructure
    (normal : HighCentreNormalFormStatement data object) :
    TraceIntoCentreStructureStatement data object := by
  classical
  intro component _present vertex _full centre hcentre routed
  have member := Graph.TypeBRefinedSupport.mem_centres.mp hcentre
  have trace := object.traceTo_of_traceReceiver?_eq_some routed
  have isReceiver := object.isReceiver_of_traceTo trace
  have high : data.threshold < object.degree centre := member.2
  refine ⟨high, isReceiver.2, trace, ?_⟩
  have same := object.internalDegree_pieceSupport
    (object.remainderSupport (canonicalWindowPacking data object)) component member.1
  obtain ⟨first, second, different, adjFirst, adjSecond, firstOut, secondOut⟩ :=
    two_outside_neighbours (object.remainderSupport (canonicalWindowPacking data object))
      centre (by have := isReceiver.2; omega)
  have form := normal centre high
  exact ⟨first, second, different, adjFirst, adjSecond,
    mem_windowSupport_of_not_mem_remainder firstOut,
    mem_windowSupport_of_not_mem_remainder secondOut,
    form.neighbourTight adjFirst, form.neighbourTight adjSecond⟩

open scoped Classical in
theorem traceIntoAbsorbedStructure (cubic : data.threshold = 3)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex) :
    TraceIntoAbsorbedStructureStatement data object := by
  classical
  intro component present handoff vertex _full receiver inCore routed
  have trace := object.traceTo_of_traceReceiver?_eq_some routed
  obtain ⟨inPiece, centre, separatorMem, shape⟩ := absorbedCore_shape inCore
  have zero := handoff.2.1
  have degreeLe : object.degree receiver ≤ data.threshold := by
    unfold Graph.FiniteObject.ambientSurplus at zero
    have := (Finset.sum_eq_zero_iff.mp zero) receiver inPiece
    omega
  have outside := separator_outside_handoffPiece cubic present handoff centre separatorMem
  have centreMem : centre ∈ canonicalGroupedCentres data object := by
    unfold canonicalGroupedCentres
    exact Finset.mem_biUnion.mpr ⟨component, Finset.mem_filter.mpr ⟨present, handoff⟩,
      separatorMem⟩
  have adjacent : object.graph.Adj centre receiver := by
    rcases shape with rfl | adj
    · exact absurd inPiece outside
    · exact adj
  have notRemainder : centre ∉ object.remainderSupport
      (canonicalWindowPacking data object) := by
    intro inRemainder
    exact outside (SupportComponents.Connected.neighbor_mem_vertices object
      (object.remainderSupport (canonicalWindowPacking data object)) component
      inPiece inRemainder adjacent.symm)
  exact ⟨inPiece, le_antisymm degreeLe (baseline receiver), trace, centre, centreMem,
    adjacent, groupedCentresHigh (object := object) cubic centre centreMem, outside,
    mem_windowSupport_of_not_mem_remainder notRemainder⟩

end Hypostructure.Graph.Contracts.TypeB
