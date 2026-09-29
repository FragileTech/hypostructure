import Hypostructure.Graph.Contracts.TypeB.Bridge
import Hypostructure.Graph.Statements.TypeBSublinearCanonical

/-!
# Contracts: the Type B sublinear hypotheses at G, in canonical form

G audit of `TypeBSublinearOutcome`.  Every existential of
`TypeBSublinearHypotheses` is pinned to a canonical object of G, so the
hypotheses are equivalent to three explicit arms, the absorbed-core inclusion is
decided at G, and the failure splits exactly.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The canonical absorbed core of a piece lies in the piece. -/
theorem groupedAbsorbedCoreSubset :
    GroupedAbsorbedCoreSubsetStatement data object := by
  classical
  intro piece
  unfold canonicalGroupedAbsorbedCore
  split
  · exact Finset.inter_subset_left
  · exact Finset.empty_subset _

open scoped Classical in
/-- The hypotheses are the conjunction of the three explicit arms. -/
theorem typeBSublinearCanonicalForm :
    TypeBSublinearCanonicalFormStatement data object := by
  classical
  have subset := groupedAbsorbedCoreSubset (data := data) (object := object)
  constructor
  · rintro ⟨bridge, handoffPieces, hpieces, centres, hcentres, high, fanEnvelope,
      hfan, absorbedAt, habsorbed, hclauses, hsum⟩
    subst hcentres hfan habsorbed
    have hset : handoffPieces =
        (object.canonicalPieces (object.remainderSupport
          (canonicalWindowPacking data object))).filter
          (TypeBGroupedHandoffPiece data object) := by
      ext component
      rw [hpieces component, Finset.mem_filter]
    refine ⟨bridge, high, ?_, ?_⟩
    · intro component hmem hhand
      have := hclauses component ((hpieces component).2 ⟨hmem, hhand⟩)
      exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
    · unfold TypeBSublinearCoverArm
      rw [← hset]
      exact hsum
  · rintro ⟨bridge, high, handoff, cover⟩
    refine ⟨bridge,
      (object.canonicalPieces (object.remainderSupport
        (canonicalWindowPacking data object))).filter
        (TypeBGroupedHandoffPiece data object), ?_, canonicalGroupedCentres data object,
      rfl, high, typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
        (canonicalGroupedCentres data object), rfl,
      canonicalGroupedAbsorbedCore data object, rfl, ?_, cover⟩
    · intro component
      rw [Finset.mem_filter]
    · intro component hmem
      have hm := Finset.mem_filter.mp hmem
      have := handoff component hm.1 hm.2
      exact ⟨subset _, this.1, this.2.1, this.2.2⟩

/-- The grouped centres of G are high. -/
theorem groupedCentresHigh (cubic : data.threshold = 3) :
    GroupedCentresHighStatement data object := by
  classical
  intro centre member
  unfold canonicalGroupedCentres at member
  simp only [Finset.mem_biUnion, Finset.mem_filter] at member
  obtain ⟨component, _present, separatorMember⟩ := member
  unfold canonicalHandoffSeparatorAt at separatorMember
  cases separation : canonicalHandoffSeparationAt data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component) with
  | none => simp [separation] at separatorMember
  | some separated =>
      simp only [separation, Option.map_some, Option.toFinset_some,
        Finset.mem_singleton] at separatorMember
      subst separatorMember
      have four := Graph.DecoratedHandoff.four_le_degree_of_surviving
        separated.2.surviving
      omega

/-- A decorated handoff piece has zero ambient surplus, so no vertex of it spends
more than the baseline inside it. -/
theorem handoffDegreeClauseEmpty :
    HandoffDegreeClauseEmptyStatement data object := by
  classical
  intro component _present handoff vertex member
  have zero := handoff.2.1
  unfold Graph.FiniteObject.ambientSurplus at zero
  have term := (Finset.sum_eq_zero_iff.mp zero) vertex member
  have bound := object.internalDegree_le_degree
    (object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) component) vertex
  omega

/-- The canonical routing is total on the pieces of the remainder. -/
theorem pieceRoutingTotal
    (normalized : RemainderNormalizedStatement data object) :
    PieceRoutingTotalStatement data object := by
  classical
  intro component _present vertex member full
  have inside := object.pieceSupport_subset
    (object.remainderSupport (canonicalWindowPacking data object)) component
  have noCore : ∀ inner : Finset object.Vertex,
      inner ⊆ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component →
      ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce inner) :=
    fun inner contained => (normalized inner (contained.trans inside)).2
  obtain ⟨_target, trace⟩ :=
    object.exists_traceTo_of_no_baseline_subsupport _ data.threshold
      noCore member (le_of_eq full.symm)
  obtain ⟨found, routed⟩ :=
    Option.isSome_iff_exists.mp (object.isSome_traceReceiver?_of_traceTo trace)
  exact ⟨found, routed,
    object.isReceiver_of_traceTo (object.traceTo_of_traceReceiver?_eq_some routed)⟩

open scoped Classical in
/-- The cover count: paying every absorbed vertex by a closed neighbour of a
grouped centre bounds the absorbed cardinalities by the closed counts. -/
theorem coverPayment :
    CoverPaymentStatement data object := by
  classical
  intro failed
  by_contra none
  apply failed
  have paid : ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
      TypeBGroupedHandoffPiece data object component →
      ∀ vertex ∈ canonicalGroupedAbsorbedCore data object
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component),
      ∃ centre ∈ canonicalGroupedCentres data object,
        vertex ∈ Graph.TypeBFanIncidence.closedNeighbours object data.threshold
          (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
            (canonicalGroupedCentres data object) centre) centre := by
    intro component present handoff vertex member
    by_contra unpaid
    exact none ⟨component, present, handoff, vertex, member,
      fun centre centreMem closed => unpaid ⟨centre, centreMem, closed⟩⟩
  set handoffPieces := (object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object))).filter
      (TypeBGroupedHandoffPiece data object) with hset
  set absorbed : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object)) →
      Finset object.Vertex := fun component =>
    canonicalGroupedAbsorbedCore data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
    with habsorbed
  have subset := groupedAbsorbedCoreSubset (data := data) (object := object)
  have disjoint : (handoffPieces : Set _).PairwiseDisjoint absorbed := by
    intro left leftMem right rightMem different
    have leftPresent := (Finset.mem_filter.mp leftMem).1
    have rightPresent := (Finset.mem_filter.mp rightMem).1
    exact Finset.disjoint_of_subset_left (subset _)
      (Finset.disjoint_of_subset_right (subset _)
        (Graph.SupportComponents.Connected.disjoint_members object _ different))
  unfold TypeBSublinearCoverArm
  calc ∑ component ∈ handoffPieces, (absorbed component).card
      = (handoffPieces.biUnion absorbed).card :=
        (Finset.card_biUnion disjoint).symm
    _ ≤ ((canonicalGroupedCentres data object).biUnion fun centre =>
          Graph.TypeBFanIncidence.closedNeighbours object data.threshold
            (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
              (canonicalGroupedCentres data object) centre) centre).card := by
        apply Finset.card_le_card
        intro vertex member
        obtain ⟨component, componentMem, vertexMem⟩ := Finset.mem_biUnion.mp member
        have present := Finset.mem_filter.mp componentMem
        obtain ⟨centre, centreMem, closed⟩ :=
          paid component present.1 present.2 vertex vertexMem
        exact Finset.mem_biUnion.mpr ⟨centre, centreMem, closed⟩
    _ ≤ ∑ centre ∈ canonicalGroupedCentres data object,
          Graph.TypeBFanIncidence.closedCount object data.threshold
            (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
              (canonicalGroupedCentres data object) centre) centre :=
        Finset.card_biUnion_le

open scoped Classical in
/-- Failure of `BridgeResidualComponentAt` at a canonical piece of the remainder
is failure of its load clause, or the canonical trace of a flat vertex lands on a
centre. -/
theorem bridgeFails_of_not
    (route : PieceRoutingTotalStatement data object)
    {component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))}
    (present : component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)))
    (h : ¬ Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
      data.threshold data.dischargeScale) :
    BridgeTraceIntoCentre data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component) ∨
      BridgeLoadFails data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component) := by
  by_contra hno
  apply h
  refine ⟨fun vertex hv hdeg => ?_, fun receiver hr => ?_⟩
  · obtain ⟨found, routed, isReceiver⟩ :=
      route component present vertex (Finset.mem_sdiff.mp hv).1 hdeg
    refine ⟨found, routed, isReceiver, fun inside => hno (Or.inl ?_)⟩
    exact ⟨vertex, hv, hdeg, found, inside, routed⟩
  · by_contra hcon
    exact hno (Or.inr ⟨receiver, hr, by omega⟩)

open scoped Classical in
/-- Failure of the handoff clauses at a decorated handoff piece is failure of
the load clause, or the canonical trace of a flat vertex lands in the absorbed
core (the degree clause is empty). -/
theorem handoffFails_of_not
    (route : PieceRoutingTotalStatement data object)
    (degree : HandoffDegreeClauseEmptyStatement data object)
    {component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))}
    (present : component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)))
    (handoff : TypeBGroupedHandoffPiece data object component)
    (h : ¬ TypeBHandoffPieceClauses data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)) :
    HandoffTraceIntoAbsorbed data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component) ∨
      HandoffLoadFails data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component) := by
  by_contra hno
  apply h
  refine ⟨fun vertex hv => degree component present handoff vertex
      (Finset.mem_sdiff.mp hv).1, fun vertex hv hdeg => ?_, fun receiver hr => ?_⟩
  · obtain ⟨found, routed, isReceiver⟩ :=
      route component present vertex (Finset.mem_sdiff.mp hv).1 hdeg
    refine ⟨found, routed, isReceiver, fun inside => hno (Or.inl ?_)⟩
    exact ⟨vertex, hv, hdeg, found, inside, routed⟩
  · by_contra hcon
    exact hno (Or.inr ⟨receiver, hr, by omega⟩)

open scoped Classical in
/-- Exact decomposition of the failure of the sublinear hypotheses at G. -/
theorem typeBSublinearFailureArms
    (cubic : data.threshold = 3)
    (normalized : RemainderNormalizedStatement data object)
    (failed : TypeBSublinearResidualStatement data object) :
    TypeBSublinearFailureArmsStatement data object := by
  classical
  have route := pieceRoutingTotal normalized
  have degree := handoffDegreeClauseEmpty (data := data) (object := object)
  have high := groupedCentresHigh (object := object) cubic
  by_cases bridge : TypeBSublinearBridgeArm data object
  swap
  · unfold TypeBSublinearBridgeArm at bridge
    obtain ⟨component, hmem, hnot⟩ : ∃ component ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
        ¬ (object.NegativeNetCharge (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) data.threshold data.dischargeScale →
          0 < object.ambientSurplus (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) data.threshold →
          Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) data.threshold data.dischargeScale) := by
      by_contra h
      exact bridge fun c hc => by
        by_contra hn
        exact h ⟨c, hc, hn⟩
    have hneg := by_contra fun h => hnot fun n => absurd n h
    have hpos := by_contra fun h => hnot fun _ n => absurd n h
    have hbr : ¬ Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component) data.threshold data.dischargeScale :=
      fun h => hnot fun _ _ => h
    refine Or.inl ⟨component, ?_, hneg, hpos, bridgeFails_of_not route hmem hbr⟩
    unfold canonicalBridgeRoute8Pieces
    exact Finset.mem_filter.mpr ⟨hmem, hbr⟩
  by_cases handoff : TypeBSublinearHandoffArm data object
  swap
  · unfold TypeBSublinearHandoffArm at handoff
    push Not at handoff
    obtain ⟨component, hmem, hhand, hnot⟩ := handoff
    exact Or.inr (Or.inl ⟨component, hmem, hhand,
      handoffFails_of_not route degree hmem hhand hnot⟩)
  by_cases cover : TypeBSublinearCoverArm data object
  · exact absurd ((typeBSublinearCanonicalForm (data := data)
      (object := object)).2 ⟨bridge, high, handoff, cover⟩) failed
  · obtain ⟨component, present, hhand, vertex, unpaid⟩ :=
      coverPayment (data := data) (object := object) cover
    exact Or.inr (Or.inr ⟨bridge, handoff, component, present, hhand, vertex,
      unpaid⟩)

end Hypostructure.Graph.Contracts.TypeB
