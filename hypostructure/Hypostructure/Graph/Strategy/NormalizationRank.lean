import Hypostructure.Core.Strategy.SupportComplementNormalization
import Hypostructure.Core.Strategy.BoundaryDemandAccounting
import Hypostructure.Core.Strategy.BoundaryDemandAccountingSemantics
import Hypostructure.Core.Strategy.LocalSupplyLowerBound
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics
import Hypostructure.Core.Strategy.TargetRelativeRankDichotomySemantics
import Hypostructure.Graph.Finite
import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.NegativeSupport
import Hypostructure.Graph.Induced
import Hypostructure.Graph.WedgeLowerBound
import Hypostructure.Graph.Strategy.Official.Features.SupportIncidenceLedger
import Hypostructure.Graph.Strategy
import Hypostructure.Graph.Strategy.ObstructionPackingClosure
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# Graph presentations for normalization and rank accounting

These adapters derive the four normalization/rank presentations from the
current finite graph and a caller-supplied baseline degree:

* the ambient support is the residual-owned finite vertex schedule;
* the selected part of that support is the surplus-degree part, so CT9's
  complementary fibre is exactly the baseline-degree part;
* boundary demand is degree deficiency against the baseline and payers are
  the incident vertices carrying the observed degree;
* local supply is the observed incidence degree together with its exact
  deficiency correction;
* rank data are the vertex coordinates, their observed charge, and the
  whole-support code.

They select no outcome and own no execution, routing, ledger, or closure.
-/

namespace Hypostructure.Graph.Strategy.NormalizationRank

open Hypostructure
open Hypostructure.Core.Residual

universe u v w uPiece uBoundary

private noncomputable def vertices (object : Graph.FiniteObject.{v}) :
    Core.Finite.Enumeration object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Core.Finite.Enumeration.ofNodupList object.orderedVertices
    object.orderedVertices_nodup

private noncomputable def liftedVertices (object : Graph.FiniteObject.{v}) :
    Core.Finite.Enumeration (ULift.{w} object.Vertex) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Core.Finite.Enumeration.ofNodupList
    ((vertices object).values.map ULift.up)
    (((vertices object).nodup).map fun _ _ equal => by
      simpa using congrArg ULift.down equal)

theorem liftedVertices_adjacency_count
    (object : Graph.FiniteObject.{v}) (vertex : object.Vertex) :
    ((liftedVertices object :
      Core.Finite.Enumeration (ULift.{u} object.Vertex))).values.countP
        (fun other => decide (object.graph.Adj vertex other.down)) =
      object.degree vertex := by
  rw [← object.orderedNeighbors_length vertex]
  change (object.orderedVertices.map ULift.up).countP
      (fun other => decide (object.graph.Adj vertex other.down)) =
    (object.orderedVertices.filter fun other =>
      decide (object.graph.Adj vertex other)).length
  induction object.orderedVertices with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.countP_cons, List.filter_cons,
        ULift.down_up]
      split <;> simp_all

/-- Interpret CT9's exact complementary enumeration as the corresponding
vertex support.  The support is a view of the CT output, not a second search
or a reconstruction from the ambient graph. -/
noncomputable def supportOfComplement
    (object : Graph.FiniteObject.{v})
    (complement : Core.Finite.Enumeration (ULift.{u} object.Vertex)) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact complement.toFinset.image ULift.down

@[simp] theorem mem_supportOfComplement_iff
    (object : Graph.FiniteObject.{v})
    (complement : Core.Finite.Enumeration (ULift.{u} object.Vertex))
    (vertex : object.Vertex) :
    vertex ∈ supportOfComplement object complement ↔
      ULift.up vertex ∈ complement.values := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [supportOfComplement]

def HasInternalCore (object : Graph.FiniteObject.{v}) (baseline : Nat)
    (support : Finset object.Vertex) : Prop :=
  ∃ core : Finset object.Vertex,
    core ⊆ support ∧ core.Nonempty ∧
      baseline ≤ (object.induce core).minDegree

def HasInternalCoreGraph {Vertex : Type v}
    (graph : SimpleGraph Vertex) (baseline : Nat)
    (support : Finset Vertex) : Prop :=
  ∃ core : Finset Vertex,
    core ⊆ support ∧ core.Nonempty ∧
      ∀ vertex ∈ core, ∃ neighbours : Finset Vertex,
        neighbours ⊆ core ∧ baseline ≤ neighbours.card ∧
          ∀ other ∈ neighbours, graph.Adj vertex other

/-- A support with no internal core and a nonempty subset has, on that subset,
a vertex whose internal degree falls below the baseline.  This is the
pointwise reading of `def:internal-3-core` used by the ledger consumers. -/
theorem exists_degree_lt_of_minDegree_lt
    (object : Graph.FiniteObject.{v}) (baseline : Nat)
    (support : Finset object.Vertex)
    (support_nonempty : support.Nonempty)
    (minimumDegreeLt : (object.induce support).minDegree < baseline) :
    ∃ vertex : object.Vertex, ∃ member : vertex ∈ support,
      (object.induce support).degree ⟨vertex, member⟩ < baseline := by
  classical
  by_contra noLowDegree
  push Not at noLowDegree
  letI : Nonempty (object.induce support).Vertex := by
    rcases support_nonempty with ⟨vertex, member⟩
    exact ⟨⟨vertex, member⟩⟩
  have minimumDegreeLower : baseline ≤ (object.induce support).minDegree := by
    apply (object.induce support).le_minDegree_of_forall_le_degree baseline
    intro vertex
    exact noLowDegree vertex.1 vertex.2
  exact (Nat.not_le_of_lt minimumDegreeLt) minimumDegreeLower

/-- The exact Core packing projection of the shared Graph presentation. -/
noncomputable def inducedPathPackingSemantics
    {Residual : Type u} {Target : Residual → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target) :
    Core.Strategy.ObstructionPackingClosure.Semantics.{u, max u v}
      Residual Target :=
  Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
    presentation

/-- Inert support-complement registration derived from the same presentation
as `inducedPathPackingSemantics`.  Its local carriers are indexed by CT9's
literal complement enumeration. -/
noncomputable def inducedPathSupportComplementRegistration
    {Residual : Type u} {Target : Residual → Prop}
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target) :
    Core.Strategy.SupportComplementNormalization.Registration.{
      u, max u v, max u v, max u v, max u v}
      Residual Target (inducedPathPackingSemantics presentation) := by
  let windowCover : (residual : Residual) →
      Graph.InducedPathMaximalPacking.Window
        (presentation.object residual)
        (presentation.order residual) →
        List (ULift.{u} (presentation.object residual).Vertex) :=
    fun residual window =>
      ((Graph.InducedPathMaximalPacking.support
        (presentation.object residual)
        (presentation.order residual) window).toList).map ULift.up
  let cover : (residual : Residual) →
      (inducedPathPackingSemantics presentation).Occurrence residual →
        List (ULift.{u} (presentation.object residual).Vertex) :=
    fun residual window =>
      windowCover residual
        (_root_.Hypostructure.Graph.Strategy.ObstructionPackingClosure.inducedPathOccurrenceEquiv
          presentation residual window)
  let cover_ne : ∀ residual occurrence, cover residual occurrence ≠ [] := by
    intro residual window nil
    let literalWindow :=
      _root_.Hypostructure.Graph.Strategy.ObstructionPackingClosure.inducedPathOccurrenceEquiv
        presentation residual window
    have nonempty : (Graph.InducedPathMaximalPacking.support
        (presentation.object residual)
        (presentation.order residual) literalWindow).Nonempty := by
      letI : DecidableEq (presentation.object residual).Vertex :=
        (presentation.object residual).vertices.decEq
      refine ⟨literalWindow ⟨0, presentation.order_pos residual⟩, ?_⟩
      exact Finset.mem_image.mpr
        ⟨⟨0, presentation.order_pos residual⟩, Finset.mem_univ _, rfl⟩
    change windowCover residual literalWindow = [] at nil
    unfold windowCover at nil
    have supportNil :
        (Graph.InducedPathMaximalPacking.support
          (presentation.object residual)
          (presentation.order residual) literalWindow).toList = [] :=
      List.map_eq_nil_iff.mp nil
    have empty :
        Graph.InducedPathMaximalPacking.support
          (presentation.object residual)
          (presentation.order residual) literalWindow = ∅ :=
      Finset.toList_eq_nil.mp supportNil
    exact nonempty.ne_empty empty
  let conflict_iff_shared_item : ∀ (residual : Residual)
      (left right :
        (inducedPathPackingSemantics presentation).Occurrence residual),
        (inducedPathPackingSemantics presentation).conflict residual left right ↔
          ∃ item, item ∈ cover residual left ∧
            item ∈ cover residual right := by
    intro residual left right
    change (¬ Disjoint
      (Graph.InducedPathMaximalPacking.support
        (presentation.object residual)
        (presentation.order residual) left.down)
      (Graph.InducedPathMaximalPacking.support
        (presentation.object residual)
        (presentation.order residual) right.down)) ↔ _
    constructor
    · intro overlap
      rw [Finset.not_disjoint_iff] at overlap
      rcases overlap with ⟨vertex, leftMem, rightMem⟩
      refine ⟨ULift.up vertex, ?_, ?_⟩
      · exact List.mem_map.mpr
          ⟨vertex, Finset.mem_toList.mpr leftMem, rfl⟩
      · exact List.mem_map.mpr
          ⟨vertex, Finset.mem_toList.mpr rightMem, rfl⟩
    · rintro ⟨item, leftMem, rightMem⟩
      rcases List.mem_map.mp leftMem with ⟨leftVertex, leftFinset, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨rightVertex, rightFinset, equal⟩
      have same : leftVertex = rightVertex := ULift.up_injective equal.symm
      subst rightVertex
      exact Finset.not_disjoint_iff.mpr
        ⟨leftVertex, Finset.mem_toList.mp leftFinset,
          Finset.mem_toList.mp rightFinset⟩
  exact {
    AmbientItem := fun residual =>
      ULift.{u} (presentation.object residual).Vertex
    ambientSupport := fun residual =>
      liftedVertices (presentation.object residual)
    cover := cover
    coverNodup := by
      intro residual occurrence
      exact (Finset.nodup_toList _).map fun _ _ equal =>
        ULift.up_injective equal
    coverSupported := by
      intro residual occurrence item member
      rcases List.mem_map.mp member with ⟨vertex, _, rfl⟩
      exact List.mem_map.mpr
        ⟨vertex,
          (presentation.object residual).mem_orderedVertices vertex, rfl⟩
    coverCard := fun residual => presentation.order residual
    cover_card := by
      intro residual occurrence
      rw [List.length_map, Finset.length_toList,
        Graph.InducedPathMaximalPacking.support_card]
    conflict_iff_shared_item := conflict_iff_shared_item
    cover_ne := cover_ne
    LocalPiece := fun residual exactComplement =>
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object residual)
          (supportOfComplement
            (presentation.object residual) exactComplement))
    localPieces := fun residual exactComplement =>
      (_root_.Hypostructure.Graph.Strategy.componentSchedule
        (presentation.object residual)
        (supportOfComplement
          (presentation.object residual) exactComplement)).map
          ULift.up ULift.up_injective (Classical.decEq _)
    FailureData := fun residual exactComplement piece =>
      ULift.{max u v}
        (PLift (HasInternalCore (presentation.object residual)
          (presentation.baselineDegree residual)
          (Graph.SupportComponents.Connected.members
            (presentation.object residual)
            (supportOfComplement
              (presentation.object residual) exactComplement)
            piece.down)))
    -- A piece fails when it carries a nonempty internal baseline core.
    Failure := fun residual exactComplement piece =>
      HasInternalCore (presentation.object residual)
        (presentation.baselineDegree residual)
        (Graph.SupportComponents.Connected.members
          (presentation.object residual)
          (supportOfComplement
            (presentation.object residual) exactComplement)
          piece.down)
    failureData := fun _residual _complement _piece failure =>
      ULift.up (PLift.up failure)
    failureDecidable := fun _residual _complement _piece => Classical.dec _
    contribution := fun residual exactComplement piece =>
      (Graph.SupportComponents.Connected.members
        (presentation.object residual)
        (supportOfComplement
          (presentation.object residual) exactComplement)
        piece.down).card
    failureForcesTarget := by
      intro residual exactComplement piece failure avoiding
      classical
      letI : DecidableEq (presentation.object residual).Vertex :=
        (presentation.object residual).vertices.decEq
      obtain ⟨core, core_subset, _core_nonempty, core_minDegree⟩ := failure
      let support :=
        supportOfComplement
          (presentation.object residual) exactComplement
      let members :=
        Graph.SupportComponents.Connected.members
          (presentation.object residual) support piece.down
      have member_in_exactComplement :
          ∀ vertex ∈ members,
            ULift.up vertex ∈ exactComplement.values := by
        intro vertex vertexMem
        apply (mem_supportOfComplement_iff
          (presentation.object residual) exactComplement _).mp
        exact
          ((Graph.SupportComponents.Connected.mem_members_iff
            (presentation.object residual) support piece.down _).mp
              vertexMem).1
      have core_in_exactComplement :
          ∀ vertex ∈ core,
            ULift.up vertex ∈ exactComplement.values := by
        intro vertex vertexMem
        exact member_in_exactComplement vertex (core_subset vertexMem)
      apply presentation.componentFreeForcesTarget residual core core_minDegree
      rintro ⟨window⟩
      let ambientWindow :
          Graph.InducedPathMaximalPacking.Window
            (presentation.object residual)
            (presentation.order residual) :=
        window.trans
          ((presentation.object residual).induceEmbedding core)
      have absent := avoiding (ULift.up ambientWindow) (by
        intro item itemMem
        rcases List.mem_map.mp itemMem with
          ⟨vertex, vertexMem, rfl⟩
        rcases Finset.mem_image.mp (Finset.mem_toList.mp vertexMem) with
          ⟨index, _indexMem, rfl⟩
        exact core_in_exactComplement _ (window index).property)
      exact absent
        (_root_.Hypostructure.Graph.Strategy.ObstructionPackingClosure.inducedPathOccurrence_mem
          presentation residual ambientWindow)
  }

/-- Dependent CT9 → CT14 → CT1 → CT6 profile at the compiler-owned stage,
derived from the shared induced-path presentation and the exact earlier
packing query. -/
noncomputable def inducedPathSupportComplement
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous))) :
    Core.Strategy.SupportComplementNormalization.Profile Previous Residual :=
  Core.Strategy.SupportComplementNormalization.Profile.ofRegistration
    (inducedPathSupportComplementRegistration presentation) packingQuery

/-- CT9's exact complementary enumeration, read from the literal composed
normalization output. -/
noncomputable def exactInducedPathComplement
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous) :
    Core.Finite.Enumeration
      (ULift.{u} (presentation.object (residualOf previous)).Vertex) :=
  let profile := inducedPathSupportComplement presentation packingQuery
  profile.partition.complementAtPrevious previous exact.output.fst.fst.fst

/-- Graph support carried by CT9's exact complementary output. -/
noncomputable def exactInducedPathComplementSupport
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous) :
    Finset (presentation.object (residualOf previous)).Vertex :=
  supportOfComplement
    (presentation.object (residualOf previous))
    (exactInducedPathComplement presentation packingQuery exact)

/-- CT6's exact component schedule over the complementary support retained by
the same composed output. -/
noncomputable def exactInducedPathComponents
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous) :
    Core.Finite.Enumeration
      (ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact))) :=
  let profile := inducedPathSupportComplement presentation packingQuery
  profile.core.localPieces previous exact.output.fst

theorem exactInducedPathComponents_values
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous) :
    (exactInducedPathComponents presentation packingQuery exact).values =
      (Graph.SupportComponents.Connected.order
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)).map
          ULift.up := by
  rfl

theorem exactInducedPathComponent_mem_order
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values) :
    piece.down ∈ Graph.SupportComponents.Connected.order
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact) := by
  rw [exactInducedPathComponents_values] at member
  rcases List.mem_map.mp member with
    ⟨component, componentMember, componentEqual⟩
  have equal : component = piece.down := congrArg ULift.down componentEqual
  simpa [equal] using componentMember

theorem exactInducedPathComponent_nonempty
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values) :
    (Graph.SupportComponents.Connected.members
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact)
      piece.down).Nonempty :=
  Graph.SupportComponents.Connected.member_nonempty _ _
    (exactInducedPathComponent_mem_order presentation packingQuery exact
      piece member)

/-- Baseline deficiency of the literal induced component. -/
noncomputable def exactInducedPathComponentDeficiency
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact))) : Nat :=
  ((presentation.object (residualOf previous)).induce
    (Graph.SupportComponents.Connected.members
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact)
      piece.down)).deficiencyAt
        (presentation.baselineDegree (residualOf previous))

theorem exactInducedPathComponent_connected
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values) :
    Graph.SupportComponents.Connected.ConnectedOn
      (presentation.object (residualOf previous))
      (Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down) :=
  Graph.SupportComponents.Connected.connectedOn_of_mem_order _ _
    (exactInducedPathComponent_mem_order presentation packingQuery exact
      piece member)

theorem exactInducedPathComponent_subset_complement
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact))) :
    Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down ⊆
      exactInducedPathComplementSupport presentation packingQuery exact := by
  intro vertex vertexMember
  exact ((Graph.SupportComponents.Connected.mem_members_iff
    (presentation.object (residualOf previous))
    (exactInducedPathComplementSupport presentation packingQuery exact)
    piece.down vertex).mp vertexMember).1

/-- CT1's exact avoidance ledger proves that every support contained in the
retained complement is induced-path-free at the presentation order. -/
theorem exactInducedPathSubset_free
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (obstructionSelected : exact.output.fst.snd.terminal = .avoiding)
    (support : Finset
      (presentation.object (residualOf previous)).Vertex)
    (support_subset : support ⊆
      exactInducedPathComplementSupport presentation packingQuery exact) :
    Graph.InducedPathFree
      ((presentation.object (residualOf previous)).induce
        support)
      (presentation.order (residualOf previous)) := by
  rintro ⟨window⟩
  classical
  letI : DecidableEq
      (presentation.object (residualOf previous)).Vertex :=
    (presentation.object (residualOf previous)).vertices.decEq
  let object := presentation.object (residualOf previous)
  let ambientWindow : Graph.InducedPathMaximalPacking.Window object
      (presentation.order (residualOf previous)) :=
    window.trans (object.induceEmbedding support)
  have scheduled : ULift.up ambientWindow ∈
      ((inducedPathPackingSemantics presentation).occurrences
        (residualOf previous)).values :=
    Graph.Strategy.ObstructionPackingClosure.inducedPathOccurrence_mem
      presentation (residualOf previous) ambientWindow
  have supported : ∀ item ∈
      (inducedPathSupportComplementRegistration presentation).cover
        (residualOf previous) (ULift.up ambientWindow),
      item ∈ (exactInducedPathComplement presentation packingQuery exact).values := by
    intro item itemMember
    rcases List.mem_map.mp itemMember with ⟨vertex, vertexMember, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_toList.mp vertexMember) with
      ⟨index, _indexMember, rfl⟩
    apply (mem_supportOfComplement_iff object
      (exactInducedPathComplement presentation packingQuery exact) _).mp
    exact support_subset (window index).property
  exact Core.Strategy.SupportComplementNormalization.Profile.ExactOutput.noObstructionAt
    (profile := inducedPathSupportComplement presentation packingQuery)
    exact obstructionSelected (ULift.up ambientWindow) scheduled supported
    scheduled

/-- Component specialization of `exactInducedPathSubset_free`. -/
theorem exactInducedPathComponent_free
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (obstructionSelected : exact.output.fst.snd.terminal = .avoiding)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact))) :
    Graph.InducedPathFree
      ((presentation.object (residualOf previous)).induce
        (Graph.SupportComponents.Connected.members
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery exact)
          piece.down))
      (presentation.order (residualOf previous)) :=
  exactInducedPathSubset_free presentation packingQuery exact
    obstructionSelected _
    (exactInducedPathComponent_subset_complement
      presentation packingQuery exact piece)

/-- Any support inside the exact complement has minimum degree below the
baseline while the registered target remains avoided. -/
theorem exactInducedPathSubset_minDegree_lt
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (obstructionSelected : exact.output.fst.snd.terminal = .avoiding)
    (targetAvoiding : ¬ Target (residualOf previous))
    (support : Finset
      (presentation.object (residualOf previous)).Vertex)
    (support_subset : support ⊆
      exactInducedPathComplementSupport presentation packingQuery exact) :
    ((presentation.object (residualOf previous)).induce support).minDegree <
      presentation.baselineDegree (residualOf previous) := by
  apply Nat.lt_of_not_ge
  intro baseline
  apply targetAvoiding
  exact presentation.componentFreeForcesTarget (residualOf previous)
    support baseline
    (exactInducedPathSubset_free presentation packingQuery exact
      obstructionSelected support support_subset)

/-- Every induced sub-support of a retained component satisfies the same
baseline drop.  This is the reusable empty-internal-core statement. -/
theorem exactInducedPathComponent_allSubsets_minDegree_lt
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (obstructionSelected : exact.output.fst.snd.terminal = .avoiding)
    (targetAvoiding : ¬ Target (residualOf previous))
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (support : Finset
      (presentation.object (residualOf previous)).Vertex)
    (support_subset : support ⊆
      Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down) :
    ((presentation.object (residualOf previous)).induce support).minDegree <
      presentation.baselineDegree (residualOf previous) :=
  exactInducedPathSubset_minDegree_lt presentation packingQuery exact
    obstructionSelected targetAvoiding support
    (support_subset.trans
      (exactInducedPathComponent_subset_complement
        presentation packingQuery exact piece))

/-- Pointwise form of the empty internal core conclusion.  It is derived
from the exact CT1 avoidance output: every nonempty induced sub-support of a
retained component contains a vertex below the presentation baseline. -/
theorem exactInducedPathComponent_exists_degree_lt
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (obstructionSelected : exact.output.fst.snd.terminal = .avoiding)
    (targetAvoiding : ¬ Target (residualOf previous))
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (support : Finset
      (presentation.object (residualOf previous)).Vertex)
    (support_nonempty : support.Nonempty)
    (support_subset : support ⊆
      Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down) :
    ∃ vertex : (presentation.object
        (residualOf previous)).Vertex,
      ∃ member : vertex ∈ support,
        ((presentation.object (residualOf previous)).induce support).degree
            ⟨vertex, member⟩ <
          presentation.baselineDegree (residualOf previous) := by
  classical
  let object := presentation.object (residualOf previous)
  let baseline := presentation.baselineDegree (residualOf previous)
  have minimumDegreeLt : (object.induce support).minDegree < baseline :=
    exactInducedPathComponent_allSubsets_minDegree_lt presentation packingQuery
      exact obstructionSelected targetAvoiding piece support support_subset
  by_contra noLowDegree
  push Not at noLowDegree
  letI : Nonempty (object.induce support).Vertex := by
    rcases support_nonempty with ⟨vertex, member⟩
    exact ⟨⟨vertex, member⟩⟩
  have minimumDegreeLower : baseline ≤ (object.induce support).minDegree := by
    apply (object.induce support).le_minDegree_of_forall_le_degree baseline
    intro vertex
    exact noLowDegree vertex.1 vertex.2
  exact (Nat.not_le_of_lt minimumDegreeLt) minimumDegreeLower

/-- **The registered no-internal-core ledger fact.**

The normalization node's own CT6 check *is* `def:internal-3-core` read at the
residual-owned baseline (see the `Failure` field of
`inducedPathSupportComplementRegistration`).  On the active-ledger terminal
Core publishes the outcome through
`SupportComplementNormalization.ExactLedger.active`; this theorem is the
Graph reading of that published query.  Nothing is recomputed here and no
target-avoidance side condition is needed: the only hypotheses are the ledger
terminal and the scheduled piece. -/
theorem exactInducedPathComponent_emptyInternalCore
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (selected : exact.output.snd.terminal = .activeLedger)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values) :
    ¬ HasInternalCore (presentation.object (residualOf previous))
        (presentation.baselineDegree (residualOf previous))
        (Graph.SupportComponents.Connected.members
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery exact)
          piece.down) := by
  let profile := inducedPathSupportComplement presentation packingQuery
  exact Core.Strategy.SupportComplementNormalization.Profile.ExactOutput.noFailureAt
    (profile := profile) exact selected piece member

/-- Subset form of the published no-internal-core fact: on the active-ledger
terminal every nonempty sub-support of a retained complementary component
induces a subgraph whose minimum internal degree is strictly below the
residual-owned baseline. -/
theorem exactInducedPathComponent_subset_minDegree_lt_of_active
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (selected : exact.output.snd.terminal = .activeLedger)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values)
    (core : Finset (presentation.object (residualOf previous)).Vertex)
    (core_nonempty : core.Nonempty)
    (core_subset : core ⊆
      Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down) :
    ((presentation.object (residualOf previous)).induce core).minDegree <
      presentation.baselineDegree (residualOf previous) := by
  by_contra notBelow
  exact exactInducedPathComponent_emptyInternalCore presentation packingQuery
    exact selected piece member
    ⟨core, core_subset, core_nonempty, Nat.not_lt.mp notBelow⟩

theorem exactInducedPathComponent_exists_degree_lt_of_active
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (selected : exact.output.snd.terminal = .activeLedger)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values)
    (core : Finset (presentation.object (residualOf previous)).Vertex)
    (core_nonempty : core.Nonempty)
    (core_subset : core ⊆
      Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down) :
    ∃ vertex : (presentation.object (residualOf previous)).Vertex,
      ∃ member : vertex ∈ core,
        ((presentation.object (residualOf previous)).induce core).degree
            ⟨vertex, member⟩ <
          presentation.baselineDegree (residualOf previous) :=
  exists_degree_lt_of_minDegree_lt
    (presentation.object (residualOf previous))
    (presentation.baselineDegree (residualOf previous))
    core core_nonempty
    (exactInducedPathComponent_subset_minDegree_lt_of_active presentation
      packingQuery exact selected piece member core core_nonempty core_subset)

/-- On CT6's active-ledger terminal, every retained complementary component
has induced minimum degree strictly below the presentation baseline.  This is
the whole-piece instance of the published no-internal-core fact. -/
theorem exactInducedPathComponent_minDegree_lt
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (selected : exact.output.snd.terminal = .activeLedger)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (member : piece ∈
      (exactInducedPathComponents presentation packingQuery exact).values) :
    ((presentation.object (residualOf previous)).induce
      (Graph.SupportComponents.Connected.members
        (presentation.object (residualOf previous))
        (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down)).minDegree <
      presentation.baselineDegree (residualOf previous) :=
  exactInducedPathComponent_subset_minDegree_lt_of_active presentation
    packingQuery exact selected piece member
    (Graph.SupportComponents.Connected.members
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact)
      piece.down)
    (exactInducedPathComponent_nonempty presentation packingQuery exact piece
      member)
    (Finset.Subset.refl _)

/-- The unique Core semantics for the exact dependent profile above.  Target
routing remains implemented by Core's registered four-CT interpreter. -/
noncomputable def inducedPathSupportComplementSemantics
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous))) :
    (inducedPathSupportComplement presentation packingQuery).Semantics :=
  Core.Strategy.SupportComplementNormalization.Profile.semanticsOfRegistration
    (inducedPathSupportComplementRegistration presentation) packingQuery

/-- Ambient minimum degree supplies every baseline deficiency inside an
arbitrary support through literal outside incidences. -/
theorem supportDeficiency_le_boundaryIncidence
    (object : Graph.FiniteObject.{v}) [DecidableEq object.Vertex]
    (baseline : Nat)
    (minimumDegree : baseline ≤ object.minDegree)
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    baseline -
        (Graph.Strategy.Official.Features.SupportIncidenceLedger.insideNeighbors
          object support vertex).length ≤
      (Graph.Strategy.Official.Features.SupportIncidenceLedger.outsideNeighbors
        object support vertex).length := by
  classical
  have degreeLower : baseline ≤ object.degree vertex :=
    minimumDegree.trans (object.minDegree_le_degree vertex)
  have split :=
    Graph.Strategy.Official.Features.SupportIncidenceLedger.inside_outside_length
      object support vertex
  omega

/-- Component specialization of `supportDeficiency_le_boundaryIncidence`.
The support is the literal CT9 complement component; no component or
incidence information is regenerated from a stable residual. -/
theorem exactInducedPathComponent_deficiency_le_boundaryIncidence
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    [DecidableEq (presentation.object
      (residualOf previous)).Vertex]
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (minimumDegree :
      presentation.baselineDegree (residualOf previous) ≤
        (presentation.object (residualOf previous)).minDegree)
    (piece :
      ULift.{u}
        (Graph.SupportComponents.Connected.Component
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery
            exact)))
    (vertex : (presentation.object
      (residualOf previous)).Vertex) :
    presentation.baselineDegree (residualOf previous) -
        (Graph.Strategy.Official.Features.SupportIncidenceLedger.insideNeighbors
          (presentation.object (residualOf previous))
          (Graph.SupportComponents.Connected.members
            (presentation.object (residualOf previous))
            (exactInducedPathComplementSupport presentation packingQuery exact)
            piece.down)
          vertex).length ≤
      (Graph.Strategy.Official.Features.SupportIncidenceLedger.outsideNeighbors
        (presentation.object (residualOf previous))
        (Graph.SupportComponents.Connected.members
          (presentation.object (residualOf previous))
          (exactInducedPathComplementSupport presentation packingQuery exact)
        piece.down)
        vertex).length := by
  exact supportDeficiency_le_boundaryIncidence
    (presentation.object (residualOf previous))
    (presentation.baselineDegree (residualOf previous))
    minimumDegree
    (Graph.SupportComponents.Connected.members
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact)
      piece.down)
    vertex

/-- CT4 → CT14 presentation.  Every vertex demands its degree deficiency
against the baseline and every incident vertex pays with its observed
degree. -/
noncomputable def boundaryDemand
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    {AmbientItem : Residual → Type w}
    {ambient : (residual : Residual) →
      Core.Finite.Enumeration (AmbientItem residual)}
    {Block : Residual → Type uPiece}
    {cover : (residual : Residual) → Block residual →
      List (AmbientItem residual)}
    (toVertex : ∀ residual, AmbientItem residual →
      (object residual).Vertex)
    (ambientLoad : ∀ residual item,
      ((ambient residual).values.countP fun other =>
        decide ((object residual).graph.Adj (toVertex residual item)
          (toVertex residual other))) =
        (object residual).degree (toVertex residual item))
    (minimumDegree : ∀ residual,
      baselineDegree residual ≤ (object residual).minDegree) :
    Core.Strategy.BoundaryDemandAccounting.Registration.{u, w, uPiece}
      Residual AmbientItem ambient Block cover where
  Interaction := fun residual left right =>
    (object residual).graph.Adj (toVertex residual left)
      (toVertex residual right)
  interactionDecidable := fun _ _ _ => inferInstance
  interactionSymmetric := fun _ _ _ adjacent => adjacent.symm
  baseline := baselineDegree
  minimumLoad := by
    intro residual item itemMem
    have lower := (minimumDegree residual).trans
      ((object residual).minDegree_le_degree (toVertex residual item))
    rw [ambientLoad]
    exact lower

/-- Incidences of a vertex that stay inside a declared support. -/
noncomputable def supportIncidence
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (vertex : object.Vertex) : Nat := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (object.orderedNeighbors vertex).countP fun neighbour =>
    decide (neighbour ∈ support)

noncomputable def boundaryIncidence
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (vertex : object.Vertex) : Nat := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (object.orderedNeighbors vertex).countP fun neighbour =>
    !decide (neighbour ∈ support)

/-- The two incidence counts partition the ambient degree. -/
theorem supportIncidence_add_boundaryIncidence
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (vertex : object.Vertex) :
    supportIncidence object support vertex +
        boundaryIncidence object support vertex = object.degree vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  show (object.orderedNeighbors vertex).countP
        (fun neighbour => decide (neighbour ∈ support)) +
      (object.orderedNeighbors vertex).countP
        (fun neighbour => !decide (neighbour ∈ support)) =
      object.degree vertex
  rw [← object.orderedNeighbors_length vertex]
  induction object.orderedNeighbors vertex with
  | nil => simp
  | cons neighbour tail ih =>
      by_cases member : neighbour ∈ support <;>
        simp only [List.countP_cons, List.length_cons, member] <;>
        simp_all <;> omega

/-- **`lem:stub-positive`'s pointwise half, in the registered CT14
observations.**

On a residual whose ambient minimum degree meets the baseline, the baseline
deficiency a vertex carries *inside* a declared support is paid in full by the
literal incidences that leave it.  This is
`supportDeficiency_le_boundaryIncidence` stated on the two incidence counts
this module actually registers (`supportIncidence`, `boundaryIncidence`)
instead of on the detached parity-oracle lists, so a consumer that reads the
CT14 presentation never has to move between the two spellings.

No hypothesis beyond the residual's own baseline is used: the two counts
partition the ambient degree (`supportIncidence_add_boundaryIncidence`). -/
theorem supportIncidence_deficiency_le_boundaryIncidence
    (object : Graph.FiniteObject.{v}) (baseline : Nat)
    (minimumDegree : baseline ≤ object.minDegree)
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    baseline - supportIncidence object support vertex ≤
      boundaryIncidence object support vertex := by
  have degreeLower : baseline ≤ object.degree vertex :=
    minimumDegree.trans (object.minDegree_le_degree vertex)
  have split := supportIncidence_add_boundaryIncidence object support vertex
  omega

/-! Framework-owned row-38 aggregate facts.  These are stated over the exact
support schedule supplied by the caller; they do not inspect an ambient
vertex enumeration or manufacture a remainder carrier. -/
theorem positiveDeficiency_sum_le_boundaryIncidence_sum
    (object : Graph.FiniteObject.{v}) (baseline : Nat)
    (minimumDegree : baseline ≤ object.minDegree)
    (support : Finset object.Vertex)
    (vertices : List object.Vertex)
    (vertices_mem : ∀ vertex ∈ vertices, vertex ∈ support) :
    (vertices.map (fun vertex =>
      baseline - supportIncidence object support vertex)).sum ≤
      (vertices.map (fun vertex =>
        boundaryIncidence object support vertex)).sum := by
  apply List.sum_le_sum
  intro vertex member
  exact supportIncidence_deficiency_le_boundaryIncidence object baseline
    minimumDegree support vertex

local instance vertexDecidableEq (object : Graph.FiniteObject.{v}) :
    DecidableEq object.Vertex := object.vertices.decEq

/-! The paper's `def⁺(R)` on the exact CT9 remainder schedule.  The schedule
is supplied by the predecessor ledger; no ambient-vertex demand schedule is
introduced or reconstructed here. -/
noncomputable def positiveDeficiencyOnExactRemainder
    (object : Graph.FiniteObject.{v}) (baseline : Nat)
    (remainder : Core.Finite.Enumeration object.Vertex) : Nat :=
  letI := object.vertices.decEq
  Core.Strategy.BoundaryDemandAccounting.FiniteInteraction.positiveDeficiency
    baseline (fun vertex =>
      supportIncidence object (remainder.values.toFinset) vertex) remainder

theorem positiveDeficiencyOnExactRemainder_le_boundary
    (object : Graph.FiniteObject.{v}) (baseline : Nat)
    (minimumDegree : baseline ≤ object.minDegree)
    (remainder : Core.Finite.Enumeration object.Vertex) :
    positiveDeficiencyOnExactRemainder object baseline remainder ≤
      (remainder.values.map (fun vertex =>
        boundaryIncidence object
          (@List.toFinset object.Vertex object.vertices.decEq remainder.values)
          vertex)).sum := by
  letI := object.vertices.decEq
  unfold positiveDeficiencyOnExactRemainder
  apply List.sum_le_sum
  intro vertex member
  exact supportIncidence_deficiency_le_boundaryIncidence object baseline
    minimumDegree remainder.values.toFinset vertex

noncomputable def localSupply
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat) :
    Core.Strategy.LocalSupplyLowerBound.Registration.{u, max u v, v, v}
      Residual (fun residual => ULift.{u} (object residual).Vertex) where
  Member := fun residual => (object residual).Vertex
  Label := fun residual => (object residual).Vertex
  members := fun _ complement =>
    complement.map ULift.down (fun left right equality =>
      ULift.ext left right equality)
      (Classical.decEq _)
  requiredMass := fun residual complement centre =>
    baselineDegree residual -
      supportIncidence (object residual)
        (supportOfComplement (object residual) complement) centre
  observedSupply := fun residual complement centre =>
    boundaryIncidence (object residual)
      (supportOfComplement (object residual) complement) centre
  defectCorrection := fun residual _ centre =>
    baselineDegree residual - (object residual).degree centre
  surplus := fun residual _ centre =>
    (object residual).degree centre - baselineDegree residual
  label := fun _ _ centre => centre
  labelDecidableEq := fun residual => (object residual).vertices.decEq
  pointwise := by
    intro residual complement centre
    have split :=
      supportIncidence_add_boundaryIncidence (object residual)
        (supportOfComplement (object residual) complement) centre
    omega

/-! Row [30] uses the same incoming complement ledger and accounts by its
literal CT6 components.  Components are represented by their member Finsets,
so the registration remains residual-indexed while the schedule remains a
dependent view of the incoming complement. -/

noncomputable def componentLocalSupply
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (baselineGe : ∀ residual, 3 ≤ baselineDegree residual) :
    Core.Strategy.LocalSupplyLowerBound.Registration.{u, max u v, v, v}
      Residual (fun residual => ULift.{u} (object residual).Vertex) where
  Member := fun residual => Finset (object residual).Vertex
  Label := fun residual => Finset (object residual).Vertex
  members := fun residual complement => by
    classical
    let support := supportOfComplement (object residual) complement
    let components :=
      _root_.Hypostructure.Graph.Strategy.componentSchedule
        (object residual) support
    exact Core.Finite.Enumeration.ofNodupList
      (components.values.map (fun component =>
        Graph.SupportComponents.Connected.members
          (object residual) support component)) (by
        refine List.Nodup.map_on (f := fun component =>
          Graph.SupportComponents.Connected.members
            (object residual) support component) ?_ components.nodup
        intro left leftMem right rightMem equal
        by_contra different
        have leftNonempty :=
          Graph.SupportComponents.Connected.member_nonempty
            (object residual) support (componentMem := leftMem)
        rcases leftNonempty with ⟨vertex, vertexMem⟩
        have rightMem' : vertex ∈
            Graph.SupportComponents.Connected.members
              (object residual) support right := by
          simpa [equal] using vertexMem
        exact (Finset.disjoint_left.mp
          (Graph.SupportComponents.Connected.disjoint_members
            (object residual) support different)) vertexMem rightMem')
  requiredMass := fun residual _ component =>
    baselineDegree residual * component.card
  observedSupply := fun residual _ component =>
    ((object residual).induce component).wedgeCount
  defectCorrection := fun residual _ component =>
    2 * (((object residual).induce component).deficiencyAt
      (baselineDegree residual))
  surplus := fun residual _ component => by
    classical
    exact (component.toList.map fun vertex =>
      (object residual).degree vertex - baselineDegree residual).sum
  label := fun _ _ component => component
  labelDecidableEq := fun residual => Classical.decEq _
  pointwise := by
    intro residual complement component
    simpa only [Graph.FiniteObject.vertexCount_induce] using
      (Graph.FiniteObject.baseline_mul_vertexCount_le_wedgeCount_add_two_mul_deficiencyAt
        ((object residual).induce component) (baselineDegree residual)
        (baselineGe residual))

theorem localSupply_defectCorrection_eq
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (residual : Residual)
    (complement :
      Core.Finite.Enumeration (ULift.{u} (object residual).Vertex))
    (centre : (object residual).Vertex) :
    (localSupply object baselineDegree).defectCorrection residual complement
        centre =
      (localSupply object baselineDegree).requiredMass residual complement
          centre -
        (localSupply object baselineDegree).observedSupply residual complement
          centre := by
  have split :=
    supportIncidence_add_boundaryIncidence (object residual)
      (supportOfComplement (object residual) complement) centre
  show baselineDegree residual - (object residual).degree centre =
    (baselineDegree residual -
        supportIncidence (object residual)
          (supportOfComplement (object residual) complement) centre) -
      boundaryIncidence (object residual)
        (supportOfComplement (object residual) complement) centre
  omega

theorem localSupply_surplus_eq_zero_iff
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (residual : Residual)
    (complement :
      Core.Finite.Enumeration (ULift.{u} (object residual).Vertex))
    (centre : (object residual).Vertex) :
    (localSupply object baselineDegree).surplus residual complement centre =
        0 ↔
      (object residual).degree centre ≤ baselineDegree residual := by
  show (object residual).degree centre - baselineDegree residual = 0 ↔
    (object residual).degree centre ≤ baselineDegree residual
  omega

/-- Ambient form of subcubicity on the atom part: a vertex of the normalized
support with vanishing registered surplus is subcubic against the registered
baseline. -/
theorem localSupply_degree_le_baselineDegree_of_surplus_eq_zero
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (residual : Residual)
    (complement :
      Core.Finite.Enumeration (ULift.{u} (object residual).Vertex))
    (centre : (object residual).Vertex)
    (atom :
      (localSupply object baselineDegree).surplus residual complement centre =
        0) :
    (object residual).degree centre ≤ baselineDegree residual :=
  (localSupply_surplus_eq_zero_iff object baselineDegree residual complement
    centre).mp atom

theorem localSupply_supportIncidence_le_baselineDegree_of_surplus_eq_zero
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (residual : Residual)
    (complement :
      Core.Finite.Enumeration (ULift.{u} (object residual).Vertex))
    (centre : (object residual).Vertex)
    (atom :
      (localSupply object baselineDegree).surplus residual complement centre =
        0) :
    supportIncidence (object residual)
        (supportOfComplement (object residual) complement) centre ≤
      baselineDegree residual := by
  have split :=
    supportIncidence_add_boundaryIncidence (object residual)
      (supportOfComplement (object residual) complement) centre
  have ambient :=
    localSupply_degree_le_baselineDegree_of_surplus_eq_zero object
      baselineDegree residual complement centre atom
  omega

/-- The registered surplus and the registered required mass never both bite:
on the atom part the required baseline mass is the honest internal deficiency
`baselineDegree - d_R(v)`, and off it the vertex pays surplus.  Stated as the
exact pointwise complement of subcubicity, so a consumer needs neither a
degree recomputation nor a case split of its own. -/
theorem localSupply_baselineDegree_le_degree_of_surplus_ne_zero
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (residual : Residual)
    (complement :
      Core.Finite.Enumeration (ULift.{u} (object residual).Vertex))
    (centre : (object residual).Vertex)
    (excess :
      (localSupply object baselineDegree).surplus residual complement centre ≠
        0) :
    baselineDegree residual < (object residual).degree centre := by
  have value :
      (localSupply object baselineDegree).surplus residual complement centre =
        (object residual).degree centre - baselineDegree residual := rfl
  omega

/-- **Downstream recovery of subcubicity from the ledger.**

A consumer that holds the published local-supply `Summary` learns, without
touching the graph again, that all but `assignedSurplus` members of the
normalized support satisfy the subcubicity constraint of
`def:remainder-entropy`: they lie in the atom part, where
`localSupply_supportIncidence_le_baselineDegree_of_surplus_eq_zero` bounds the
internal degree by the registered baseline.  Nothing here is recomputed from
the residual — both numbers are published ledger fields. -/
theorem subcubicAtomCard_of_localSupplySummary
    (summary : Core.Strategy.LocalSupplyLowerBound.Summary) :
    summary.netDeficiency.remainder - summary.assignedSurplus ≤
      summary.subcubicAtomCard :=
  summary.remainder_sub_assignedSurplus_le_subcubicAtomCard

/-! ## The local-supply tie: CT14's schedule *is* CT9's normalized support

The local-supply Strategy folds a `List` (its own `Enumeration` schedule) and
publishes numbers; a consumer states its certificate as a `Finset` sum over the
support CT9 selected.  Core already published the schedule-side half in
`Finset` coordinates
(`LocalSupplyLowerBound.Profile.lowerMass_eq_sum_toFinset` and its two
siblings, all of which are `List.sum_toFinset` on the duplicate-free
`Enumeration`).  The graph-side half is the identity below: the underlying
finite set of the registered member schedule is literally
`supportOfComplement`, the view of CT9's complementary output this module
already uses everywhere else.

Nothing is recomputed and no support is rebuilt.  In particular the consumer
never re-derives a maximal packing: the `Finset` on the right of every
statement here is CT9's own selected complement. -/

/-- **The registered member schedule enumerates exactly CT9's normalized
support.**  `localSupply.members` is `complement.map ULift.down` and
`supportOfComplement` is `complement.toFinset.image ULift.down`; both sides
therefore have the same members, and `ULift.down` is injective so no
multiplicity is lost. -/
theorem localSupply_members_toFinset
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (residual : Residual)
    (complement :
      Core.Finite.Enumeration (ULift.{u} (object residual).Vertex)) :
    ((localSupply object baselineDegree).members residual complement).toFinset =
      supportOfComplement (object residual) complement := by
  classical
  ext vertex
  constructor
  · intro member
    have listMember :
        vertex ∈
          ((localSupply object baselineDegree).members residual
            complement).values :=
      (Core.Finite.Enumeration.mem_toFinset _ _).mp member
    rcases (Core.Finite.Enumeration.mem_map_values complement ULift.down
      (fun left right equality => ULift.ext left right equality)
      (Classical.decEq _) vertex).mp listMember with
      ⟨source, sourceMem, sourceEq⟩
    refine (mem_supportOfComplement_iff (object residual) complement
      vertex).mpr ?_
    cases source
    cases sourceEq
    exact sourceMem
  · intro member
    have upMember :=
      (mem_supportOfComplement_iff (object residual) complement vertex).mp
        member
    refine (Core.Finite.Enumeration.mem_toFinset _ _).mpr ?_
    exact (Core.Finite.Enumeration.mem_map_values complement ULift.down
      (fun left right equality => ULift.ext left right equality)
      (Classical.decEq _) vertex).mpr ⟨ULift.up vertex, upMember, rfl⟩

/-- The same identity on the composed Strategy profile, where the complement
is the one the compiler supplies as an exact ledger query.  The proof is the
theorem above: `Profile.localCells` *is* the registered `members` read at the
inherited complement. -/
theorem localSupply_localCells_toFinset
    {Residual : Type u} {Previous : Type w}
    [Core.Residual.HasResidual Previous Residual]
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        u, w, max u v, uPiece}
        Previous Residual
        (fun previous => ULift.{u} (object (current previous)).Vertex))
    (accounting : Core.Residual.Query Previous fun _ =>
      ULift.{uBoundary} Core.Strategy.BoundaryDemandAccounting.Summary)
    (previous : Previous) :
    ((Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).localCells previous).toFinset =
      supportOfComplement (object (current previous))
        (normalizedSupport.complement previous) :=
  localSupply_members_toFinset object baselineDegree _ _

/-- **Tie equation 1.**  The published member count is `|R|`, the cardinality
of CT9's own normalized support. -/
theorem localSupply_summary_remainder_eq_card
    {Residual : Type u} {Previous : Type w}
    [Core.Residual.HasResidual Previous Residual]
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        u, w, max u v, uPiece}
        Previous Residual
        (fun previous => ULift.{u} (object (current previous)).Vertex))
    (accounting : Core.Residual.Query Previous fun _ =>
      ULift.{uBoundary} Core.Strategy.BoundaryDemandAccounting.Summary)
    {previous : Previous}
    (capacity :
      (Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).CapacityResidual previous) :
    ((Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).summaryOfResidual
      capacity).netDeficiency.remainder =
      (supportOfComplement
        (object (current capacity.result.stage.previous))
        (normalizedSupport.complement
          capacity.result.stage.previous)).card := by
  rw [Core.Strategy.LocalSupplyLowerBound.Profile.summaryOfResidual_remainder_eq_card,
    localSupply_localCells_toFinset object baselineDegree current
      normalizedSupport accounting]
  rfl

theorem localSupply_summary_requiredMass_eq_sum
    {Residual : Type u} {Previous : Type w}
    [Core.Residual.HasResidual Previous Residual]
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        u, w, max u v, uPiece}
        Previous Residual
        (fun previous => ULift.{u} (object (current previous)).Vertex))
    (accounting : Core.Residual.Query Previous fun _ =>
      ULift.{uBoundary} Core.Strategy.BoundaryDemandAccounting.Summary)
    {previous : Previous}
    (capacity :
      (Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).CapacityResidual previous) :
    ((Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).summaryOfResidual capacity).requiredMass =
      ∑ vertex ∈
        supportOfComplement
          (object (current capacity.result.stage.previous))
          (normalizedSupport.complement capacity.result.stage.previous),
        (baselineDegree (current capacity.result.stage.previous) -
          supportIncidence
            (object (current capacity.result.stage.previous))
            (supportOfComplement
              (object (current capacity.result.stage.previous))
              (normalizedSupport.complement
                capacity.result.stage.previous))
            vertex) := by
  rw [Core.Strategy.LocalSupplyLowerBound.Profile.summaryOfResidual_requiredMass_eq_sum,
    localSupply_localCells_toFinset object baselineDegree current
      normalizedSupport accounting]
  rfl

/-- **Tie equation 3.**  The published assigned surplus is `σ_R`: the sum,
over the same support, of the *registered* CT14 surplus observation
`degree - baselineDegree`. -/
theorem localSupply_summary_assignedSurplus_eq_sum
    {Residual : Type u} {Previous : Type w}
    [Core.Residual.HasResidual Previous Residual]
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        u, w, max u v, uPiece}
        Previous Residual
        (fun previous => ULift.{u} (object (current previous)).Vertex))
    (accounting : Core.Residual.Query Previous fun _ =>
      ULift.{uBoundary} Core.Strategy.BoundaryDemandAccounting.Summary)
    {previous : Previous}
    (capacity :
      (Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).CapacityResidual previous) :
    ((Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (localSupply object baselineDegree) current normalizedSupport
        accounting).summaryOfResidual capacity).assignedSurplus =
      ∑ vertex ∈
        supportOfComplement
          (object (current capacity.result.stage.previous))
          (normalizedSupport.complement capacity.result.stage.previous),
        ((object (current capacity.result.stage.previous)).degree vertex -
          baselineDegree (current capacity.result.stage.previous)) := by
  rw [Core.Strategy.LocalSupplyLowerBound.Profile.summaryOfResidual_assignedSurplus_eq_sum,
    localSupply_localCells_toFinset object baselineDegree current
      normalizedSupport accounting]
  rfl


set_option maxHeartbeats 1000000 in
open Hypostructure.Graph.SupportComponents.Connected in
/-- **Every vertex observation adds over CT6's component schedule.**  This is
the partition half of `lem:netcharge-superadd`, stated once for an arbitrary
commutative-monoid observation so that the member count and the ambient
surplus are two instances of it rather than two proofs. -/
theorem sum_support_eq_sum_components {M : Type w} [AddCommMonoid M]
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (f : object.Vertex → M) :
    ∑ vertex ∈ support, f vertex =
      ((order object support).map fun component =>
        ∑ vertex ∈ members object support component, f vertex).sum := by
  classical
  have cover :
      support =
        (order object support).toFinset.biUnion (members object support) := by
    ext vertex
    constructor
    · intro member
      rcases (mem_support_iff_mem_component object support vertex).mp member
        with ⟨component, componentMem, vertexMem⟩
      exact Finset.mem_biUnion.mpr
        ⟨component, List.mem_toFinset.mpr componentMem, vertexMem⟩
    · intro member
      rcases Finset.mem_biUnion.mp member with
        ⟨component, componentMem, vertexMem⟩
      exact (mem_support_iff_mem_component object support vertex).mpr
        ⟨component, List.mem_toFinset.mp componentMem, vertexMem⟩
  have pairwise :
      Set.PairwiseDisjoint ((order object support).toFinset : Finset _)
        (members object support) := by
    intro left _ right _ different
    exact disjoint_members object support different
  conv_lhs => rw [cover]
  rw [Finset.sum_biUnion (f := f) pairwise]
  exact List.sum_toFinset
    (fun component => ∑ vertex ∈ members object support component, f vertex)
    (order_nodup object support)

open Hypostructure.Graph.SupportComponents.Connected in
theorem supportIncidence_component_eq
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (component : Component object support) (vertex : object.Vertex)
    (member : vertex ∈ members object support component) :
    supportIncidence object (members object support component) vertex =
      supportIncidence object support vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  show (object.orderedNeighbors vertex).countP
      (fun neighbour => decide (neighbour ∈ members object support component)) =
    (object.orderedNeighbors vertex).countP
      (fun neighbour => decide (neighbour ∈ support))
  apply List.countP_congr
  intro neighbour neighbourMem
  have adjacent :=
    (object.mem_orderedNeighbors_iff vertex neighbour).mp neighbourMem
  simp only [decide_eq_true_eq]
  constructor
  · intro inComponent
    exact ((mem_members_iff object support component neighbour).mp inComponent).1
  · intro inSupport
    exact neighbor_mem_vertices object support component member inSupport
      adjacent

/-- A finite integer schedule with negative total carries a negative entry.
This is the pigeonhole step of `prop:negative-net-charge`, on the list CT6
already scheduled. -/
private theorem exists_neg_of_sum_neg {Item : Type w} (items : List Item)
    (value : Item → Int) (negative : (items.map value).sum < 0) :
    ∃ item ∈ items, value item < 0 := by
  by_contra none
  push Not at none
  have nonneg : 0 ≤ (items.map value).sum := by
    apply List.sum_nonneg
    intro entry entryMem
    rcases List.mem_map.mp entryMem with ⟨item, itemMem, rfl⟩
    exact none item itemMem
  omega

set_option maxHeartbeats 1000000 in
open Hypostructure.Graph.SupportComponents.Connected in
/-- **`lem:netcharge-superadd`.**  The net charge of the remainder is the sum
of the net charges of its connected components.

The charge is written in the registered observations and in the presentation's
own two parameters: `baseline` is `baselineDegree`, and `multiplier` is the
reciprocal of the domain's discharging rate `α`
(`ReceiverLoad.LoadCapacityProfile.loadMultiplier`).  At the Erdős–Gyárfás
values this display is `4 · N₀`, i.e.
`4 def⁺(X) - 4 σ(X) - |X|` of `def:net-charge`; no numeral occurs.

The identity holds because the deficiency term is component-local
(`supportIncidence_component_eq`) while the surplus and the per-vertex unit are
ambient, so all three add over the partition (`sum_support_eq_sum_components`).
-/
theorem netCharge_eq_sum_components
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (baseline multiplier : Nat) :
    ∑ vertex ∈ support,
        ((multiplier : Int) *
              (baseline - supportIncidence object support vertex : Nat) -
            (multiplier : Int) *
              ((object.degree vertex - baseline : Nat) : Int) - 1) =
      ((order object support).map fun component =>
        ∑ vertex ∈ members object support component,
          ((multiplier : Int) *
                (baseline -
                  supportIncidence object
                    (members object support component) vertex : Nat) -
              (multiplier : Int) *
                ((object.degree vertex - baseline : Nat) : Int) - 1)).sum := by
  classical
  rw [sum_support_eq_sum_components object support
    (fun vertex =>
      ((multiplier : Int) *
            (baseline - supportIncidence object support vertex : Nat) -
          (multiplier : Int) *
            ((object.degree vertex - baseline : Nat) : Int) - 1))]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro component _componentMem
  refine Finset.sum_congr rfl ?_
  intro vertex vertexMem
  rw [supportIncidence_component_eq object support component vertex vertexMem]

set_option maxHeartbeats 1000000 in
open Hypostructure.Graph.SupportComponents.Connected in
theorem exists_component_negative_netCharge
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (baseline multiplier : Nat)
    (negative :
      ∑ vertex ∈ support,
        ((multiplier : Int) *
              (baseline - supportIncidence object support vertex : Nat) -
            (multiplier : Int) *
              ((object.degree vertex - baseline : Nat) : Int) - 1) < 0) :
    ∃ component ∈ order object support,
      ∑ vertex ∈ members object support component,
        ((multiplier : Int) *
              (baseline -
                supportIncidence object
                  (members object support component) vertex : Nat) -
            (multiplier : Int) *
              ((object.degree vertex - baseline : Nat) : Int) - 1) < 0 := by
  classical
  rw [netCharge_eq_sum_components object support baseline multiplier] at negative
  exact exists_neg_of_sum_neg _ _ negative

set_option maxHeartbeats 1000000 in
open Hypostructure.Graph.SupportComponents.Connected in
theorem exists_negativeSupport_of_component_negative
    (object : Graph.FiniteObject.{v}) (support : Finset object.Vertex)
    (charge : object.Vertex → Int)
    (component : Component object support)
    (componentMem : component ∈ order object support)
    (negative :
      ∑ vertex ∈ members object support component, charge vertex < 0) :
    ∃ negativeSupport : Graph.NegativeSupport.Support object,
      negativeSupport.core = members object support component ∧
        negativeSupport.charge = charge := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine
    ⟨{ source :=
        { core := members object support component
          cells :=
            Core.Finite.Enumeration.ofNodupList
              (members object support component).toList
              (Finset.nodup_toList _)
          cells_toFinset := ?_
          charge := charge
          negative := ?_ }
       connected := ?_ }, rfl, rfl⟩
  · show ((members object support component).toList).toFinset =
      members object support component
    exact Finset.toList_toFinset _
  · show (((members object support component).toList).map charge).sum < 0
    rw [Finset.sum_map_toList]
    exact negative
  · exact connectedOn_of_mem_order object support componentMem

set_option maxHeartbeats 1000000 in
theorem exists_exactInducedPathComponent_negativeSupport
    {Residual : Type u} {Target : Residual → Prop}
    {Previous : Type (max u v)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{u, v} Residual Target)
    (packingQuery : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((inducedPathPackingSemantics presentation).occurrences
          (residualOf previous))
        ((inducedPathPackingSemantics presentation).conflict
          (residualOf previous)))
    {previous : Previous}
    (exact :
      (inducedPathSupportComplement presentation packingQuery).ExactOutput
        previous)
    (baseline multiplier : Nat)
    (negative :
      ∑ vertex ∈
        exactInducedPathComplementSupport presentation packingQuery exact,
        ((multiplier : Int) *
              (baseline -
                supportIncidence (presentation.object (residualOf previous))
                  (exactInducedPathComplementSupport presentation packingQuery
                    exact) vertex : Nat) -
            (multiplier : Int) *
              (((presentation.object (residualOf previous)).degree vertex -
                baseline : Nat) : Int) - 1) < 0) :
    ∃ piece ∈
        (exactInducedPathComponents presentation packingQuery exact).values,
      ∃ negativeSupport :
          Graph.NegativeSupport.Support
            (presentation.object (residualOf previous)),
        negativeSupport.core =
            Graph.SupportComponents.Connected.members
              (presentation.object (residualOf previous))
              (exactInducedPathComplementSupport presentation packingQuery
                exact) piece.down ∧
          negativeSupport.charge = fun vertex =>
            (multiplier : Int) *
                (baseline -
                  supportIncidence
                    (presentation.object (residualOf previous))
                    (Graph.SupportComponents.Connected.members
                      (presentation.object (residualOf previous))
                      (exactInducedPathComplementSupport presentation
                        packingQuery exact) piece.down) vertex : Nat) -
              (multiplier : Int) *
                (((presentation.object (residualOf previous)).degree
                  vertex - baseline : Nat) : Int) - 1 := by
  classical
  obtain ⟨component, componentMem, componentNegative⟩ :=
    exists_component_negative_netCharge
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact)
      baseline multiplier negative
  obtain ⟨negativeSupport, coreEq, chargeEq⟩ :=
    exists_negativeSupport_of_component_negative
      (presentation.object (residualOf previous))
      (exactInducedPathComplementSupport presentation packingQuery exact)
      _ component componentMem componentNegative
  refine ⟨ULift.up component, ?_, negativeSupport, coreEq, chargeEq⟩
  rw [exactInducedPathComponents_values]
  exact List.mem_map.mpr ⟨component, componentMem, rfl⟩

/-- Raw wedges whose centre and both endpoints lie in CT9's exact
complement.  The schedule is a filter of the already retained graph wedge
schedule; no graph object or complement is reconstructed. -/
noncomputable def wedgeScheduleInComplement
    (object : Graph.FiniteObject.{v})
    (complement : Core.Finite.Enumeration (ULift.{u} object.Vertex)) :
    Core.Finite.Enumeration object.WedgeCoordinate := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let support := supportOfComplement object complement
  let kept := object.wedgeSchedule.values.filter fun wedge =>
    decide (wedge.fst ∈ support ∧ wedge.snd.val ⊆ support)
  exact
    { values := kept
      nodup := object.wedgeSchedule.nodup.filter _
      decEq := object.wedgeSchedule.decEq }

/-- A rank coordinate retains the exact CT9 component support that owns its
raw wedge.  The support is not recomputed after CT15 selects a dependence:
it is part of the coordinate stored in CT15's literal rank-drop certificate.
-/
abbrev SupportedWedge (object : Graph.FiniteObject.{v}) :=
  Finset object.Vertex × object.WedgeCoordinate

/-- Exact component-indexed wedge schedule obtained from CT9's retained
complement.  Each entry pairs a raw wedge with the literal member set of the
CT6 component that contains its centre and endpoints.  Deduplication is only
the canonical finite-enumeration normalization; it does not change or invent
any support. -/
noncomputable def supportedWedgeSchedule
    (object : Graph.FiniteObject.{v})
    (complement : Core.Finite.Enumeration (ULift.{u} object.Vertex)) :
    Core.Finite.Enumeration (SupportedWedge object) := by
  classical
  let support := supportOfComplement object complement
  let components :=
    _root_.Hypostructure.Graph.Strategy.componentSchedule object support
  let wedges := wedgeScheduleInComplement object complement
  let rows := components.values.flatMap fun liftedComponent =>
    let members := Graph.SupportComponents.Connected.members object support
      liftedComponent
    (wedges.values.filter fun wedge =>
      decide (wedge.fst ∈ members ∧ wedge.snd.val ⊆ members)).map
        fun wedge => (members, wedge)
  exact Core.Finite.Enumeration.ofNodupList rows.dedup rows.nodup_dedup

/-- Every retained rank coordinate comes from one literal CT9 component and
the literal wedge schedule restricted to that component.  This is the query
law used downstream to recover connectivity and carrier membership from the
CT15 hit without rebuilding either object. -/
theorem mem_supportedWedgeSchedule_iff
    (object : Graph.FiniteObject.{v})
    (complement : Core.Finite.Enumeration (ULift.{u} object.Vertex))
    (coordinate : SupportedWedge object) :
    coordinate ∈ (supportedWedgeSchedule object complement).values ↔
      ∃ component,
        component ∈ (_root_.Hypostructure.Graph.Strategy.componentSchedule
          object (supportOfComplement object complement)).values ∧
        coordinate.1 = Graph.SupportComponents.Connected.members object
          (supportOfComplement object complement) component ∧
        coordinate.2 ∈ (wedgeScheduleInComplement object complement).values ∧
        coordinate.2.fst ∈ coordinate.1 ∧
        coordinate.2.snd.val ⊆ coordinate.1 := by
  classical
  simp only [supportedWedgeSchedule, Core.Finite.Enumeration.ofNodupList,
    List.mem_dedup, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨component, componentMem, wedge,
      ⟨wedgeMem, centreMem, endpointsMem⟩, rfl⟩
    exact ⟨component, componentMem, rfl, wedgeMem, centreMem, endpointsMem⟩
  · rintro ⟨component, componentMem, supportEq, wedgeMem, centreMem,
      endpointsMem⟩
    refine ⟨component, componentMem, coordinate.2, ?_, ?_⟩
    · refine ⟨wedgeMem, ?_, ?_⟩
      · simpa [supportEq] using centreMem
      · simpa [supportEq] using endpointsMem
    · apply Prod.ext
      · exact supportEq.symm
      · rfl

/-- Connectivity of a CT15-selected support is recovered from its retained
component provenance; downstream localization never searches for it again. -/
theorem connectedOn_of_mem_supportedWedgeSchedule
    (object : Graph.FiniteObject.{v})
    (complement : Core.Finite.Enumeration (ULift.{u} object.Vertex))
    (coordinate : SupportedWedge object)
    (member : coordinate ∈ (supportedWedgeSchedule object complement).values) :
    Graph.SupportComponents.Connected.ConnectedOn object coordinate.1 := by
  rcases (mem_supportedWedgeSchedule_iff object complement coordinate).1 member with
    ⟨component, componentMem, supportEq, _⟩
  rw [supportEq]
  exact Graph.SupportComponents.Connected.connectedOn_of_mem_order object
    (supportOfComplement object complement) (by
      simpa [_root_.Hypostructure.Graph.Strategy.componentSchedule] using
        componentMem)

/-- CT10 → CT15 → CT16 presentation.  Coordinates are the exact length-two
wedges retained in CT9's complement; target dependence is tested at each
wedge centre and each retained coordinate contributes one unit of charge. -/
noncomputable def targetRelativeRankBase
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (rankSlack : Residual → Nat)
    (degreeBound : Option (PLift (∀ residual : Residual,
      baselineDegree residual ≤ (object residual).minDegree)) := none) :
    Core.Strategy.TargetRelativeRankDichotomy.BaseRegistration.{
      u, max u v, 0, v, v, v, v} Residual
      (fun residual => ULift.{u} (object residual).Vertex)
      (fun residual => SupportedWedge (object residual)) where
  Response := fun _ => Nat
  response := baselineDegree
  Datum := fun residual => (object residual).Vertex
  Class := fun residual => (object residual).Vertex
  Promotion := fun residual => (object residual).Vertex
  observationData := fun residual => vertices (object residual)
  completeClasses := fun residual =>
    Core.Finite.CompleteEnumeration.ofFinEnum (object residual).vertices
  classOf := fun _ _ datum => datum
  -- The classification's direct exit is the registered baseline read back at
  -- one vertex: a class whose ambient degree falls below the residual-owned
  -- baseline degree contradicts the standing minimum-degree hypothesis the
  -- residual itself carries, so CT10 would close on it without ever building
  -- the rank table.  Nothing here is a second numeric observation: `response`
  -- is the registered baseline and `degree` is the ambient graph.
  Direct := fun residual response cls =>
    (object residual).degree cls < response
  promote := fun _ _ cls => cls
  directDecidable := fun _ _ _ => inferInstance
  coordinates := fun residual complement =>
    supportedWedgeSchedule (object residual) complement
  charge := fun _ _ _ => Fintype.card Unit
  charge_pos := fun _ _ _ => by decide
  capacitySlack := fun residual _ => rankSlack residual
  -- The rank-drop closure of this presentation, supplied exactly when the
  -- residual publishes the standing minimum-degree hypothesis it is defined
  -- under.  Both halves are `targetRelativeRankBase_classificationExhaustive`
  -- read off the presentation itself: no class is direct because the
  -- registered baseline is at most every vertex degree, and every class is
  -- observed because the schedule is the ambient vertex list under the
  -- identity classifier.
  rankDropImpossible :=
    degreeBound.map fun bound =>
      ⟨fun residual cls =>
          Nat.not_lt.2 ((bound.down residual).trans
            ((object residual).minDegree_le_degree cls)),
        fun residual cls =>
          ⟨cls, (object residual).mem_orderedVertices cls, rfl⟩⟩

noncomputable def targetRelativeRank
    {Residual : Type u}
    (Baseline Target : Graph.FiniteObject.{v} → Prop)
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (rankSlack : Residual → Nat) :
    Core.Strategy.TargetRelativeRankDichotomy.Registration
      Residual
      (fun residual => ULift.{u} (object residual).Vertex)
      (fun residual => SupportedWedge (object residual)) where
  toBaseRegistration := targetRelativeRankBase object baselineDegree rankSlack
  TargetDependent := fun residual _response coordinate =>
    Graph.Strategy.InterfaceReplacement.CompressibleSupport
      Baseline Target (object residual) coordinate.1
  targetDependentDecidable := fun _ _ _ => Classical.dec _

/-- The graph rank presentation is classification exhaustive.

Both halves are read off the presentation itself, with the residual-owned
baseline as the only input:

* no class is direct, because the registered baseline degree is at most the
  ambient minimum degree, hence at most the degree of every vertex;
* every class is observed, because the observation schedule is the ambient
  vertex list and the classifier is the identity, so each vertex is its own
  witness.

Consequently the CT16 closed-code mismatch terminal of the composed
CT10 → CT15 → CT16 execution is unreachable for this presentation. -/
theorem targetRelativeRankBase_classificationExhaustive
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (rankSlack : Residual → Nat)
    (degreeBound : ∀ residual : Residual,
      baselineDegree residual ≤ (object residual).minDegree) :
    (targetRelativeRankBase.{u, v} object baselineDegree
      rankSlack).ClassificationExhaustive := by
  constructor
  · intro residual cls
    exact Nat.not_lt.2
      ((degreeBound residual).trans ((object residual).minDegree_le_degree cls))
  · intro residual cls
    exact ⟨cls, (object residual).mem_orderedVertices cls, rfl⟩

/-- Exact relation between a retained CT15 coordinate and the proper
interface-replacement site determined by its stored support. -/
def supportedWedgeSiteRelation
    (object : Graph.FiniteObject.{v})
    (coordinate : SupportedWedge object)
    (site : Graph.ProperBoundariedAtom object) : Prop :=
  ∃ (connected : Graph.SupportComponents.Connected.ConnectedOn
      object coordinate.1)
    (proper : ∃ vertex, vertex ∉ coordinate.1),
    site = Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom
      object coordinate.1 connected proper

/-- Fixed-predicate rank registration for a presentation-carrying graph
problem.  Applications register only this inert value; Core reads the linked
minimal-context producer and closes its dependent terminal. -/
noncomputable def compressionLinkedTargetRelativeRankWithPresentation
    {Residual : Type u}
    (Baseline : Graph.FiniteObject.{v} → Prop)
    (BranchState : Graph.FiniteObject.{v} → Type w)
    (baselineInvariant : Graph.FiniteObject.IsomorphismInvariant Baseline)
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target (Graph.problemWithPresentation
      Baseline BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation Baseline BranchState
        Presentation presentation baselineInvariant) T.Predicate)
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat)
    (rankSlack : Residual → Nat)
    (degreeBound : Option (PLift (∀ residual : Residual,
      baselineDegree residual ≤ (object residual).minDegree)) := none) :
    let base :=
      targetRelativeRankBase object baselineDegree rankSlack degreeBound
    Core.Strategy.TargetRelativeRankDichotomy.FixedRegistration base
      (fun residual _response coordinate =>
        Nonempty (Σ site : {site :
            (Graph.Strategy.InterfaceReplacement.profileWithPresentation
              Baseline BranchState baselineInvariant Presentation presentation
              targetInvariant).assembly.Site (object residual) //
              supportedWedgeSiteRelation (object residual) coordinate site},
          (Graph.Strategy.InterfaceReplacement.profileWithPresentation
            Baseline BranchState baselineInvariant Presentation presentation
            targetInvariant).CompressionCandidate (object residual) site.1)) :=
  { targetDependentDecidable := fun _ _ _ => Classical.dec _ }

end Hypostructure.Graph.Strategy.NormalizationRank
