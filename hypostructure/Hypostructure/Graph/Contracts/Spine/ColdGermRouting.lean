import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Contracts.Spine.ColdSubcubicCharge
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily

/-!
# Contracts: routing the cold germs `[154]`--`[157]`, `[163]`, `[168]`--`[169]`, `[175]`--`[177]`

Proof-agnostic contract lemmas for `lem:cold-bounded-germ-trichotomy`,
`lem:cold-same-interface-table`, the window stub structure, the blocked class,
`lem:neutral-germ-symmetry`'s equal-length terminal configuration, and
`lem:absorbed-germ-fan-data`.  Each lemma is stated over a `Graph.FiniteObject`
with the registered `Parameters` as a parameter and every paper hypothesis
explicit; its conclusion is exactly the statement of the fact it proves.  This
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **(G1) never occurs** at node `[153]`'s extracted family.  A
hit-realizing germ gives an accepted cycle of the target-avoiding object. -/
theorem coldGermRealized_of_avoids (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    ColdGermRealizedStatement data object :=
  fun germ _active realizing =>
    avoids (germ.target_of_realizing
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant realizing)

/-- **(G2) is target-defective.**  A distinguishing context makes the germ's
identification not target-complete. -/
theorem coldGermDistinguished_holds (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    ColdGermDistinguishedStatement data object :=
  fun germ _active Profile profile distinguishing =>
    germ.not_targetComplete_of_distinguishing profile distinguishing

/-- **(G3) never occurs** at node `[153]`'s extracted family.  A shortening
neutral germ is a target-complete compression of a proper support, which
`cor:uncompressible` forbids. -/
theorem coldGermSilent_of_uncompressible (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (uncompressible : UncompressibleStatement data object) :
    ColdGermSilentStatement data object :=
  fun germ _active shorter neutral =>
    uncompressible germ.support
      (germ.compressibleSupport_of_not_distinguishing shorter neutral.2)

/-- **Nodes `[154]`--`[156]`: every surviving length-changing germ is (G2).**
(G1) is refuted by target avoidance and (G3) by uncompressibility, so every
shortening germ is distinguishing and routed to the target-defect ledger. -/
theorem coldGermRouted_of_uncompressible (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object) :
    ColdGermRoutedStatement data object := by
  let notRealizing : ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
      ¬ germ.Realizing :=
    fun germ realizing =>
      avoids (germ.target_of_realizing
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant realizing)
  let notSilent : ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
      germ.increment < 0 → ¬ germ.Neutral :=
    fun germ shorter neutral =>
      uncompressible germ.support
          (germ.compressibleSupport_of_not_distinguishing shorter neutral.2)
  exact fun germ _active shorter =>
    have distinguishing :=
      Graph.ColdCorridor.boundedGerm_not_survives notRealizing notSilent
        germ shorter
    ⟨distinguishing,
      fun Profile profile =>
        germ.not_targetComplete_of_distinguishing profile distinguishing,
      Or.inl distinguishing⟩

/-- **Node `[157]`, `lem:cold-same-interface-table` and
`lem:cold-short-self-return-filter`.**  No table row is realizing, and a row
is handed off or distinguishing (otherwise it compresses its own proper
support); the short self-return exceptions are routed the same way; every row
has increment `0`. -/
theorem coldSameInterfaceTable_of_uncompressible (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object) :
    ColdSameInterfaceTableStatement data object := by
  let compression := fun support compressible => uncompressible support compressible
  let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
      (Graph.HasCycleWithLength data.LengthOK) :=
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
  exact ⟨fun row =>
      Graph.ColdCorridor.row_closed targetInvariant avoids compression row,
    fun self =>
      Graph.ColdCorridor.selfReturn_closed targetInvariant avoids compression self,
    fun row => row.increment_eq_zero⟩

/-- **Node `[168]`: the stub structure of the ambient-cubic cold windows.**
The two path endpoints carry `δ - 1` external stubs each, every interior vertex
carries `δ - 2`, and the interior stubs are asymmetric single-stub attachments. -/
theorem coldWindowStubStructure_of_split (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (threeLeOrder : 3 ≤ data.windowOrder)
    (split : HotColdWindowStatement data object) :
    ColdWindowStubStructureStatement data object := by
  classical
  intro window member
  have windowMem : window ∈ canonicalWindowPacking data object :=
    Finset.sdiff_subset (Finset.mem_filter.1 member).1
  have cubic : ∀ vertex ∈ window, object.degree vertex = data.threshold :=
    (Finset.mem_filter.1 member).2
  have induces : object.InducesWindow data.windowOrder window :=
    split.1.1 window windowMem
  obtain ⟨ends, endsSubset, endsCard, interior, endpoints⟩ :=
    Graph.FiniteObject.exists_ends_externalNeighbours window
      threeLeOrder induces cubic
  exact ⟨ends, endsSubset, endsCard, interior, endpoints,
    Graph.FiniteObject.interior_stubs_le_asymmetric window
      threeLeOrder induces cubic⟩

/-- **Node `[169]`, `def:blocked-class`.**  The object's own labelled skeleton
has the baseline minimum degree, contains every packed window at its labelled
position, and -- the object having no accepted cycle -- no accepted cycle
passes through a window; the blocked class is dominated by the skeleton
budget. -/
theorem blockedClassMember_of_split (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (split : HotColdWindowStatement data object) :
    BlockedClassMemberStatement data object :=
  ⟨Graph.BlockedClass.minDegree_objectSkeleton object data.threshold baseline,
    Graph.BlockedClass.objectSkeleton_blocked object data.windowOrder
      data.LengthOK (canonicalWindowPacking data object) split.1 avoids,
    Graph.BlockedClass.card_blocked_le_skeletonBudget object
      data.threshold data.windowOrder data.LengthOK _⟩

/-- **Node `[163]`, `lem:neutral-germ-symmetry`: the equal-length terminal
configuration.**  A positive germ family has an active germ; its canonical
cut-state representative is not shorter than the corridor piece (a shorter one
would give a smaller baseline target-avoiding object, contradicting size
minimality), so it has equal length; the retained representative is the
canonical one when it refines the object, and the piece itself otherwise. -/
theorem neutralConfiguration_of_positive
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (positive : ColdGermFamilyPositiveStatement data object)
    (silent : ColdGermNoneDistinguishingStatement data object) :
    NeutralConfigurationStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  obtain ⟨extraction, extractionEq, positiveCard⟩ := positive
  obtain ⟨routing, _familyWitness⟩ :=
    coldGermExtraction?_spec_of_eq_some data object extractionEq
  obtain ⟨epsilon, epsilonMem⟩ := Finset.card_pos.mp positiveCard
  let germ := coldRoutedOccurrenceIncidence data object routing epsilon
  have active : CanonicalActiveColdGerm data object germ :=
    ⟨extraction, extractionEq, routing, epsilon, epsilonMem, rfl⟩
  let baselineInvariant :=
    Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold
  let targetInvariant :=
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
  let Reading : Graph.CanonicalPiece germ.atom.interface → Prop :=
    fun candidate =>
      Graph.CanonicalPiece.CutStateReading
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK)
          germ.piece candidate ∧
        (Graph.glue candidate.toPiece germ.atom.outside).edgeCount =
          (Graph.glue germ.piece germ.atom.outside).edgeCount
  have sourceCutState :
      Graph.CanonicalPiece.CutStateReading
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK)
        germ.piece germ.piece.toCanonical :=
    Graph.CanonicalPiece.cutStateReading_toCanonical
      baselineInvariant targetInvariant germ.piece
  have sourceEdgeCount :
      (Graph.glue germ.piece.toCanonical.toPiece germ.atom.outside).edgeCount =
        (Graph.glue germ.piece germ.atom.outside).edgeCount :=
    Graph.FiniteObject.edgeCount_eq_of_isomorphic
      (germ.piece.toCanonical_glue_isomorphic germ.atom.outside)
  have sourceReading : Reading germ.piece.toCanonical :=
    ⟨sourceCutState, sourceEdgeCount⟩
  have realizable : ∃ candidate, Reading candidate :=
    ⟨germ.piece.toCanonical, sourceReading⟩
  let canonical :=
    Graph.CanonicalPiece.canonicalRepresentative Reading realizable
  have canonicalReading : Reading canonical :=
    Graph.CanonicalPiece.canonicalRepresentative_reading Reading realizable
  have canonicalSizeLe :
      canonical.size ≤ germ.piece.internalVertexCount := by
    calc
      canonical.size ≤ germ.piece.toCanonical.size :=
        Graph.CanonicalPiece.canonicalRepresentative_size_le
          Reading realizable sourceReading
      _ = germ.piece.internalVertexCount := rfl
  have sourceAvoids :
      ¬ Graph.HasCycleWithLength data.LengthOK
          (Graph.glue germ.piece germ.atom.outside) := by
    intro hit
    exact selected.1
      ((targetInvariant.iff_of_iso
        ⟨germ.atom.reconstructionIso⟩).mp hit)
  have sourceBaseline :
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue germ.piece germ.atom.outside) :=
    (baselineInvariant.iff_of_iso
      ⟨germ.atom.reconstructionIso⟩).mpr baseline
  have canonicalNotShorter :
      ¬ canonical.size < germ.piece.internalVertexCount := by
    intro shorter
    have cutState := canonicalReading.1
    have swappedBaseline :
        Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue canonical.toPiece germ.atom.outside) :=
      cutState.2.2 germ.atom.outside sourceBaseline
    have swappedAvoids :
        ¬ Graph.HasCycleWithLength data.LengthOK
            (Graph.glue canonical.toPiece germ.atom.outside) := by
      intro hit
      exact sourceAvoids ((cutState.2.1 germ.atom.outside).mp hit)
    have swappedSmaller :
        Graph.FiniteObject.LexicographicallySmaller
          (Graph.glue canonical.toPiece germ.atom.outside) object := by
      refine (Graph.FiniteObject.lexicographicallySmaller_congr_right
        ⟨germ.atom.reconstructionIso⟩).mp ?_
      apply Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt
      have sourcePieceCount :
          germ.atom.piece.internalVertexCount =
            germ.piece.internalVertexCount := rfl
      simp only [Graph.glue_vertexCount,
        Graph.CanonicalPiece.toPiece_internalVertexCount]
      rw [sourcePieceCount]
      omega
    exact swappedAvoids
      (selected.2 (Graph.glue canonical.toPiece germ.atom.outside)
        swappedSmaller swappedBaseline)
  have canonicalEqualLength :
      canonical.size = germ.piece.internalVertexCount :=
    Nat.le_antisymm canonicalSizeLe
      (Nat.le_of_not_gt canonicalNotShorter)
  let representative :=
    if RefinedLexicographicallySmaller
        (Graph.glue canonical.toPiece germ.atom.outside) object then
      canonical
    else
      germ.piece.toCanonical
  have representativeReading : Reading representative := by
    dsimp only [representative]
    split
    · exact canonicalReading
    · exact sourceReading
  have equalLength :
      representative.size = germ.piece.internalVertexCount := by
    dsimp only [representative]
    split
    · exact canonicalEqualLength
    · rfl
  have canonicalPosition :
      representative = germ.piece.toCanonical ∨
        (Graph.CanonicalPiece.Precedes representative
            germ.piece.toCanonical ∧
          RefinedLexicographicallySmaller
            (Graph.glue representative.toPiece germ.atom.outside)
            object) := by
    classical
    dsimp only [representative]
    split <;> rename_i decrease
    · by_cases same : canonical = germ.piece.toCanonical
      · exact Or.inl same
      · exact Or.inr ⟨
          Graph.CanonicalPiece.canonicalRepresentative_precedes
            Reading realizable sourceReading (Ne.symm same),
          decrease⟩
    · exact Or.inl rfl
  refine ⟨silent, germ, representative, ?_⟩
  change CanonicalActiveColdGerm data object germ ∧
    (Graph.CanonicalPiece.CutStateReading
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK)
        germ.piece representative ∧
      (Graph.glue representative.toPiece germ.atom.outside).edgeCount =
        (Graph.glue germ.piece germ.atom.outside).edgeCount) ∧
    representative.size = germ.piece.internalVertexCount ∧
    (representative = germ.piece.toCanonical ∨
      (Graph.CanonicalPiece.Precedes representative
          germ.piece.toCanonical ∧
        RefinedLexicographicallySmaller
          (Graph.glue representative.toPiece germ.atom.outside)
          object)) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue germ.piece germ.atom.outside)
  exact ⟨active, representativeReading, equalLength,
    canonicalPosition, sourceAvoids⟩

/-- **Node `[163]` on the dense residual** (`def:neutral-equal-length-germ`):
node `[162]`'s terminality together with the silent family's neutral
configuration. -/
theorem neutralEqualLengthTerminal_of_positive
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (positive : ColdGermFamilyPositiveStatement data object)
    (silent : ColdGermNoneDistinguishingStatement data object)
    (terminal : DenseColdCorridorsTerminalStatement data object) :
    NeutralEqualLengthTerminalConfigurationStatement data object :=
  ⟨terminal, neutralConfiguration_of_positive data object baseline selected positive
    silent⟩

/-- **Node `[175]`: every cross-window occurrence is a candidate.**  A
selected stub whose foot lies in the ambient-cubic cold-window union joins a
vertex of one ambient-cubic cold window to a vertex of another (node `[30]`'s
cross-window clause); its immediate exchange germ is supported on those two
vertices, both at the baseline degree, so it meets no high vertex. -/
theorem coldCrossWindow_mem_candidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    ∀ epsilon : ColdCrossWindowHalfEdge data object,
      Sum.inr epsilon ∈ coldRoutedCandidates data object routing := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  intro epsilon
  let classified := coldRoutedClassified data object routing
  let state := classified.state
  change ColdCorridorStateStatement data object at state
  let stateOne := Classical.choose_spec state
  let stateTwo := Classical.choose_spec (Classical.choose_spec stateOne)
  let stateBundle := Classical.choose_spec (Classical.choose_spec stateTwo)
  have supportEq := (Classical.choose_spec stateBundle.2.2.2.1 epsilon).1
  obtain ⟨sourceWindow, sourceMem, targetWindow, targetMem, sourceIn, targetIn,
    _adjacent⟩ := stateBundle.2.2.1 ⟨epsilon.1, epsilon.property.1⟩
      epsilon.property.2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  change ∀ vertex ∈ (coldRoutedCrossIncidence data object routing epsilon).support,
    object.degree vertex ≤ data.threshold
  intro vertex member
  have member' : vertex ∈ ({epsilon.1.1, epsilon.1.2} : Finset object.Vertex) := by
    rw [← supportEq]; exact member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member'
  rcases member' with rfl | rfl
  · exact le_of_eq ((Finset.mem_filter.1 sourceMem).2 _ sourceIn)
  · exact le_of_eq ((Finset.mem_filter.1 targetMem).2 _ targetIn)

set_option maxHeartbeats 4000000 in
/-- **Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy.**
Every selected half-edge's first-failure germ is either subcubic (a candidate
of `lem:cold-germ-extraction`) or has a first high-degree head all of whose
neighbours sit exactly at the threshold (the slack-independence of node `[10]`
and the baseline). -/
theorem absorbedGermSplit_of_handoff (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (family : ColdGermCandidatesStatement data object)
    (handoff : ColdFirstHighHandoffStatement data object)
    (independent : SlackIndependentStatement data object) :
    AbsorbedGermSplitStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : Fintype (ColdEligibleHalfEdge data object) :=
    coldEligibleHalfEdgeFintype data object
  change ColdGermCandidatesStatement data object at family
  rcases family with
    ⟨routing, _incidence, _candidates, _disjointFamily, _corridorLoss,
      _familyWitness⟩
  change AbsorbedGermSplitStatement data object
  simp only [AbsorbedGermSplitStatement]
  refine ⟨routing, ?_, coldCrossWindow_mem_candidates data object routing⟩
  intro epsilon
  let classified := coldRoutedClassified data object routing
  let state := classified.state
  rcases handoff state epsilon with subcubic | high
  · apply Or.inl
    exact Finset.mem_filter.2
      ⟨Finset.mem_univ _,
        coldSubcubicFirstFailureGerm data object routing epsilon subcubic,
        subcubic⟩
  · rcases high with
      ⟨first, firstBound, firstHigh, earlierBound, _root⟩
    refine Or.inr ⟨first, firstBound, firstHigh, earlierBound,
      fun neighbour adjacent => ?_⟩
    apply le_antisymm
    · by_contra above
      push Not at above
      exact independent ((coldOccurrenceCorridorAt data object classified
        epsilon).head first) neighbour firstHigh above adjacent
    · exact le_trans baseline (object.minDegree_le_degree neighbour)

/-- **Node `[177]`: the case-(ii) fan data.**  The node-`[153]` package carries
the exact candidate/loss identity and the `B_cold·σ(G)` loss bound; the
per-half-edge split supplies the least-high witness on every non-candidate. -/
theorem absorbedGermFanData_of_split (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (split : AbsorbedGermSplitStatement data object) :
    AbsorbedGermFanDataStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  change AbsorbedGermSplitStatement data object at split
  simp only [AbsorbedGermSplitStatement] at split
  obtain ⟨routing, alternatives⟩ := split
  change AbsorbedGermFanDataStatement data object
  simp only [AbsorbedGermFanDataStatement]
  refine ⟨routing, ?_⟩
  intro epsilon notCandidate
  rcases alternatives.1 epsilon with candidate | high
  · exact (notCandidate candidate).elim
  · exact high

/-- **Node `[176]`: the positive class is nonempty after extraction.**  The
positive class is the exact candidate set of the retained extraction, so the
greedy disjoint family is nonempty. -/
theorem coldGermFamilyPositive_of_positiveGerm (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (positive : ColdPositiveGermStatement data object)
    (family : ColdGermCandidatesStatement data object) :
    ColdGermFamilyPositiveStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  change ColdPositiveGermStatement data object at positive
  rcases positive with ⟨positiveRouting, positiveCard⟩
  obtain ⟨extraction, extractionEq, routing, familyWitness⟩ :=
    coldGermExtraction?_spec_of_candidates data object family
  have routingEq : positiveRouting = routing := Subsingleton.elim _ _
  subst positiveRouting
  simp only [ColdGermFamilyWitness] at familyWitness
  obtain ⟨_incidenceEq, _candidatesEq, _candidateFamily, extracted,
    _rest⟩ := familyWitness
  exact ⟨extraction, extractionEq,
    Graph.ColdCorridor.coldGerm_nonempty extracted.2.2 positiveCard⟩

end Hypostructure.Graph.Contracts.Spine
