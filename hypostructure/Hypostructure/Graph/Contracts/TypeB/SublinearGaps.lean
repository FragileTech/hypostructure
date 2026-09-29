import Hypostructure.Graph.Contracts.TypeB.SublinearCanonical
import Hypostructure.Graph.Statements.TypeBSublinearGaps

/-!
# Contracts: the load and cover gaps of the Type B sublinear failure
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

open scoped Classical in
theorem restrictedLoad_le_routedLoad (piece excluded : Finset object.Vertex)
    (receiver : object.Vertex) :
    object.restrictedLoad piece excluded data.threshold receiver ≤
      object.routedLoad piece data.threshold receiver := by
  classical
  unfold Graph.FiniteObject.restrictedLoad Graph.FiniteObject.routedLoad
    Graph.FiniteObject.routedLoads
  apply Finset.card_le_card
  intro source member
  obtain ⟨sdiff, rest⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp sdiff).1, rest⟩

open scoped Classical in
/-- A load failure is a saturated receiver. -/
theorem loadFailureSaturated :
    LoadFailureSaturatedStatement data object := by
  classical
  intro piece
  constructor
  · rintro ⟨receiver, member, fails⟩
    refine ⟨receiver, member, ?_⟩
    have le := restrictedLoad_le_routedLoad (data := data) piece
      (Graph.TypeBRefinedSupport.centres object data.threshold piece) receiver
    unfold Graph.FiniteObject.Saturated
    omega
  · rintro ⟨receiver, member, fails⟩
    refine ⟨receiver, member, ?_⟩
    have le := restrictedLoad_le_routedLoad (data := data) piece
      (canonicalGroupedAbsorbedCore data object piece) receiver
    unfold Graph.FiniteObject.Saturated
    omega

/-- The decorations of a canonical handoff envelope are the separator of the
canonical separation. -/
theorem canonicalHandoffEnvelopeAt_decorations
    {piece : Finset object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    {envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK HighDegree
      Absorbing}
    (h : canonicalHandoffEnvelopeAt data object piece HighDegree Absorbing =
      some envelope) :
    ∃ separated, canonicalHandoffSeparationAt data object piece = some separated ∧
      envelope.decorations = {separated.2.separation.separator} := by
  classical
  unfold canonicalHandoffEnvelopeAt at h
  split at h
  · obtain ⟨separated, hsep, built⟩ := Option.bind_eq_some_iff.mp h
    split at built
    · cases built
      exact ⟨separated, hsep, rfl⟩
    · cases built
  · cases h

/-- Shape of the canonical absorbed core: an absorbed vertex is the canonical
separator or one of its neighbours. -/
theorem absorbedCore_shape {piece : Finset object.Vertex} {vertex : object.Vertex}
    (member : vertex ∈ canonicalGroupedAbsorbedCore data object piece) :
    vertex ∈ piece ∧ ∃ centre ∈ (canonicalHandoffSeparatorAt data object piece).toFinset,
      vertex = centre ∨ object.graph.Adj centre vertex := by
  classical
  unfold canonicalGroupedAbsorbedCore at member
  split at member
  · next envelope hEnv =>
      obtain ⟨inPiece, rest⟩ := Finset.mem_inter.mp member
      refine ⟨inPiece, ?_⟩
      obtain ⟨separated, hsep, hdec⟩ := canonicalHandoffEnvelopeAt_decorations hEnv
      have hz : separated.2.separation.separator ∈
          (canonicalHandoffSeparatorAt data object piece).toFinset := by
        unfold canonicalHandoffSeparatorAt
        simp [hsep]
      refine ⟨_, hz, ?_⟩
      rcases Finset.mem_union.mp rest with dec | assigned
      · rw [hdec, Finset.mem_singleton] at dec
        exact Or.inl dec
      · obtain ⟨h, hh, ha⟩ := Finset.mem_biUnion.mp assigned
        rw [hdec, Finset.mem_singleton] at hh
        subst hh
        exact Or.inr (envelope.assigned_adj _ (by rw [hdec]; simp) _ ha)
  · simp at member

/-- The Hall violator of the cover network is a window port. -/
theorem unpaidAbsorbedWindowPort
    (cubic : data.threshold = 3)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex) :
    UnpaidAbsorbedWindowPortStatement data object := by
  classical
  intro component present handoff vertex unpaid
  obtain ⟨inCore, notClosed⟩ := unpaid
  obtain ⟨inPiece, centre, separatorMem, shape⟩ := absorbedCore_shape inCore
  have zero := handoff.2.1
  have degreeLe : object.degree vertex ≤ data.threshold := by
    unfold Graph.FiniteObject.ambientSurplus at zero
    have := (Finset.sum_eq_zero_iff.mp zero) vertex inPiece
    omega
  have centreMem : centre ∈ canonicalGroupedCentres data object := by
    unfold canonicalGroupedCentres
    exact Finset.mem_biUnion.mpr ⟨component, Finset.mem_filter.mpr ⟨present, handoff⟩,
      separatorMem⟩
  have highCentre := groupedCentresHigh (object := object) cubic centre centreMem
  have adjacent : object.graph.Adj centre vertex := by
    rcases shape with rfl | adj
    · omega
    · exact adj
  refine ⟨centre, centreMem, adjacent, ?_⟩
  by_contra none
  apply notClosed centre centreMem
  rw [Graph.TypeBFanIncidence.mem_closedNeighbours_iff]
  refine ⟨adjacent, by have := baseline vertex; omega, fun other adj differs => ?_⟩
  have notWindow : other ∉ Graph.FiniteObject.windowSupport
      (canonicalWindowPacking data object) := fun w => none ⟨other, adj, differs, w⟩
  have inRemainder : other ∈ object.remainderSupport
      (canonicalWindowPacking data object) := by
    unfold Graph.FiniteObject.remainderSupport
    simp [notWindow]
  have inSame := SupportComponents.Connected.neighbor_mem_vertices object
    (object.remainderSupport (canonicalWindowPacking data object)) component
    inPiece inRemainder adj
  unfold typeBFanEnvelope Graph.TypeBRefinedSupport.fanEnvelope
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))
  unfold canonicalGroupedBridgeUnion
  exact Finset.mem_biUnion.mpr ⟨component, Finset.mem_filter.mpr ⟨present, handoff⟩,
    inSame⟩

end Hypostructure.Graph.Contracts.TypeB
