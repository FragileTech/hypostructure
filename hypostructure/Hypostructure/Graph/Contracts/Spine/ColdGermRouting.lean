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

/-- **(G1) never occurs.**  A hit-realizing germ gives an accepted cycle of the
target-avoiding object; every germ of the retained family satisfies the
trichotomy. -/
theorem coldGermRealized_of_candidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (candidates : ColdGermCandidatesStatement data object) :
    ColdGermRealizedStatement data object :=
  ⟨candidates,
    fun germ realizing =>
      avoids (germ.target_of_realizing
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant realizing),
    fun germ => germ.trichotomy⟩

/-- **(G2) is target-defective.**  A distinguishing context makes the germ's
identification not target-complete. -/
theorem coldGermDistinguished_of_candidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (candidates : ColdGermCandidatesStatement data object) :
    ColdGermDistinguishedStatement data object :=
  ⟨candidates, fun germ Profile profile distinguishing =>
    germ.not_targetComplete_of_distinguishing profile distinguishing⟩

/-- **(G3) never occurs, with the increment arithmetic.**  A shortening
neutral germ is a target-complete compression of a proper support, which
`cor:uncompressible` forbids; the increment clauses are
`lem:cold-increment-arithmetic`. -/
theorem coldGermSilent_of_uncompressible (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (uncompressible : UncompressibleStatement data object) :
    ColdGermSilentStatement data object :=
  ⟨fun germ shorter neutral =>
      uncompressible germ.support
          (germ.compressibleSupport_of_not_distinguishing shorter neutral.2),
    fun germ => germ.not_lengthChanging_iff,
    fun increment base copies length positive overlapping lower upper
        accepted =>
      Graph.ColdCorridor.exists_not_survivesSmear_of_mem_interval
        positive overlapping lower upper accepted,
    fun increment base exponent residue positive small reached congruent
        accepted =>
      Graph.ColdCorridor.exists_not_survivesSmear_of_pow_congruent
        positive small reached congruent accepted,
    fun increment base _ wide criterion =>
      Graph.ColdCorridor.exists_hit_of_orderOf_lt (base := base) wide criterion,
    fun transient exponent odd past =>
      Graph.ColdCorridor.pow_mod_of_le past⟩

/-- **Nodes `[154]`--`[156]`: every surviving length-changing germ is (G2).**
(G1) is refuted by target avoidance and (G3) by uncompressibility, so every
shortening germ is distinguishing and routed to the target-defect ledger. -/
theorem coldGermRouted_of_candidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (candidates : ColdGermCandidatesStatement data object) :
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
  exact ⟨candidates, fun germ shorter =>
    have distinguishing :=
      Graph.ColdCorridor.boundedGerm_not_survives notRealizing notSilent
        germ shorter
    ⟨distinguishing,
      fun Profile profile =>
        germ.not_targetComplete_of_distinguishing profile distinguishing,
      Or.inl distinguishing⟩⟩

/-- **Node `[157]`, `lem:cold-same-interface-table` and
`lem:cold-short-self-return-filter`.**  No table row is realizing, and a row
is handed off or distinguishing (otherwise it compresses its own proper
support); the short self-return exceptions are routed the same way; the table
is finite. -/
theorem coldSameInterfaceTable_of_candidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (uncompressible : UncompressibleStatement data object)
    (candidates : ColdGermCandidatesStatement data object) :
    ColdSameInterfaceTableStatement data object := by
  let compression := fun support compressible => uncompressible support compressible
  let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
      (Graph.HasCycleWithLength data.LengthOK) :=
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
  exact ⟨candidates, fun Handoff row =>
      Graph.ColdCorridor.row_closed targetInvariant avoids compression row,
    fun Handoff self =>
      Graph.ColdCorridor.selfReturn_closed targetInvariant avoids compression self,
    fun length failed =>
      Graph.ColdCorridor.exists_accepted_of_not_survivesSmear failed,
    rfl,
    fun Handoff row => row.increment_eq_zero⟩

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
theorem neutralEqualLengthTerminal_of_positive
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (positive : ColdGermFamilyPositiveStatement data object)
    (terminal : DenseColdCorridorsTerminalStatement data object) :
    NeutralEqualLengthTerminalConfigurationStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  change ColdGermFamilyPositiveStatement data object at positive
  rcases positive with
    ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
      familyWitness, positiveCard⟩
  obtain ⟨epsilon, epsilonMem⟩ := Finset.card_pos.mp positiveCard
  let germ := incidence epsilon
  have active : ActiveColdGermStatement data object germ := by
    refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
      familyWitness, ?_⟩
    exact ⟨epsilon, epsilonMem, rfl⟩
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
  refine ⟨terminal, germ, representative, ?_⟩
  change ActiveColdGermStatement data object germ ∧
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
  refine ⟨routing, ?_⟩
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
    (split : AbsorbedGermSplitStatement data object)
    (family : ColdGermCandidatesStatement data object) :
    AbsorbedGermFanDataStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  change AbsorbedGermSplitStatement data object at split
  change ColdGermCandidatesStatement data object at family
  simp only [AbsorbedGermSplitStatement] at split
  obtain ⟨splitRouting, alternatives⟩ := split
  obtain ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
      familyWitness⟩ := family
  have routingEq : splitRouting = routing := Subsingleton.elim _ _
  subst splitRouting
  change AbsorbedGermFanDataStatement data object
  simp only [AbsorbedGermFanDataStatement]
  refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
    familyWitness, ?_⟩
  intro epsilon notCandidate
  rcases alternatives epsilon with candidate | high
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
  change ColdGermCandidatesStatement data object at family
  rcases positive with ⟨positiveRouting, positiveCard⟩
  rcases family with
    ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
      familyWitness⟩
  have routingEq : positiveRouting = routing := Subsingleton.elim _ _
  subst positiveRouting
  simp only [ColdGermFamilyWitness] at familyWitness
  rcases familyWitness with
    ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
      noncandidateClassified, occurrenceCount, selectedCount,
      lossBound, quantitative⟩
  have candidatePositive : 0 < candidates.card := by
    rw [candidatesEq]
    exact positiveCard
  have disjointPositive : 0 < disjointFamily.card :=
    Graph.ColdCorridor.coldGerm_nonempty extracted.2.2 candidatePositive
  change ColdGermFamilyPositiveStatement data object
  refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
    ?_, disjointPositive⟩
  simp only [ColdGermFamilyWitness]
  exact ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
    noncandidateClassified, occurrenceCount, selectedCount,
    lossBound, quantitative⟩

end Hypostructure.Graph.Contracts.Spine
