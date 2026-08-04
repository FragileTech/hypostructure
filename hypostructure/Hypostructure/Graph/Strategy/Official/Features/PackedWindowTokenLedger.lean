/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT4 -> CT14).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Mathlib.Data.Fintype.BigOperators
import Hypostructure.Graph.Strategy.Official.Features.PackedSupportIncidence

/-!
# Exact packed-window incidences and graph-derived token supplies

Incidences are represented by their literal tail and neighbour witnesses.
Thus every element determines an actual graph dart, while its finite fibre is
exactly the fibre counted by the existing support-incidence ledger.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.PackedWindowTokenLedger

open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object)

local instance vertexFinEnum : FinEnum object.Vertex := object.vertices

def packedSupport : Finset object.Vertex :=
  PackedSupport.selected object order profile

/-- An actual oriented graph incidence with both endpoints in the packed
support. -/
abbrev InternalIncidence :=
  Σ tail : {vertex // vertex ∈ packedSupport object order profile},
    {head // head ∈ SupportIncidenceLedger.insideNeighbors object
      (packedSupport object order profile) tail.1}

/-- An actual oriented graph incidence leaving the packed support. -/
abbrev BoundaryIncidence :=
  Σ tail : {vertex // vertex ∈ packedSupport object order profile},
    {head // head ∈ SupportIncidenceLedger.outsideNeighbors object
      (packedSupport object order profile) tail.1}

def InternalIncidence.tail
    (incidence : InternalIncidence object order profile) : object.Vertex :=
  incidence.1.1

def InternalIncidence.head
    (incidence : InternalIncidence object order profile) : object.Vertex :=
  incidence.2.1

theorem InternalIncidence.adj
    (incidence : InternalIncidence object order profile) :
    object.graph.Adj incidence.tail incidence.head := by
  exact (object.mem_orderedNeighbors_iff _ _).1
    (List.mem_of_mem_filter incidence.2.2)

def BoundaryIncidence.tail
    (incidence : BoundaryIncidence object order profile) : object.Vertex :=
  incidence.1.1

def BoundaryIncidence.head
    (incidence : BoundaryIncidence object order profile) : object.Vertex :=
  incidence.2.1

theorem BoundaryIncidence.adj
    (incidence : BoundaryIncidence object order profile) :
    object.graph.Adj incidence.tail incidence.head := by
  exact (object.mem_orderedNeighbors_iff _ _).1
    (List.mem_of_mem_filter incidence.2.2)

/-- Both endpoints of an actual internal incidence occur in one selected
window.  Since every selected window is induced, this is exactly the
within-window path-incidence predicate. -/
def InOneWindow (incidence : InternalIncidence object order profile) : Prop :=
  ∃ window ∈ profile.selected,
    incidence.tail ∈ InducedPathMaximalPacking.support object order window ∧
    incidence.head ∈ InducedPathMaximalPacking.support object order window

/-- Literal internal path incidences. -/
noncomputable def pathIncidences :
    Finset (InternalIncidence object order profile) := by
  classical
  exact Finset.univ.filter (InOneWindow object order profile)

/-- Literal incidences joining distinct selected windows. -/
noncomputable def crossWindowIncidences :
    Finset (InternalIncidence object order profile) := by
  classical
  exact Finset.univ.filter fun incidence =>
    ¬ InOneWindow object order profile incidence

/-- Literal support-to-complement incidences. -/
noncomputable def boundaryIncidences :
    Finset (BoundaryIncidence object order profile) :=
  Finset.univ

/-- The two semantic classes are disjoint and exhaust every actual internal
incidence. -/
theorem internal_partition :
    (pathIncidences object order profile).card +
        (crossWindowIncidences object order profile).card =
      Fintype.card (InternalIncidence object order profile) := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext incidence
    by_cases same : InOneWindow object order profile incidence <;>
      simp [pathIncidences, crossWindowIncidences, same]
  · rw [pathIncidences, crossWindowIncidences]
    exact Finset.disjoint_filter_filter_not Finset.univ Finset.univ
      (InOneWindow object order profile)

private theorem subtype_sum_eq_filtered_sum
    (support : Finset object.Vertex) (f : object.Vertex → Nat) :
    (∑ vertex : {vertex // vertex ∈ support}, f vertex.1) =
      ((object.orderedVertices.filter fun vertex =>
        decide (vertex ∈ support)).map f).sum := by
  classical
  let selected := object.orderedVertices.filter fun vertex =>
    decide (vertex ∈ support)
  have selectedFinset : selected.toFinset = support := by
    ext vertex
    simp [selected]
  calc
    (∑ vertex : {vertex // vertex ∈ support}, f vertex.1) =
        ∑ vertex ∈ support, f vertex := by
      symm
      exact Finset.sum_subtype support (by simp) f
    _ = ∑ vertex ∈ selected.toFinset, f vertex := by rw [selectedFinset]
    _ = (selected.map f).sum :=
      List.sum_toFinset f (object.orderedVertices_nodup.filter _)

private theorem card_list_membership
    {α : Type*} [Fintype α] [DecidableEq α]
    (values : List α) (nodup : values.Nodup) :
    Fintype.card {value // value ∈ values} = values.length := by
  rw [Fintype.card_subtype]
  have filtered :
      Finset.univ.filter (fun value => value ∈ values) = values.toFinset := by
    ext value
    simp
  rw [filtered, List.toFinset_card_of_nodup nodup]

private theorem selected_subtype_card :
    Fintype.card {vertex // vertex ∈ packedSupport object order profile} =
      (PackedSupportIncidence.derive object order profile baseline).incidence.selected.length := by
  classical
  rw [Fintype.card_coe]
  change (packedSupport object order profile).card =
    (object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ packedSupport object order profile)).length
  rw [← List.toFinset_card_of_nodup
    (object.orderedVertices_nodup.filter _)]
  congr 1
  ext vertex
  simp [packedSupport]

/-- The internal-incidence subtype has exactly the cardinality counted by the
packed-support ledger. -/
theorem internal_supply_exact :
    Fintype.card (InternalIncidence object order profile) =
      (PackedSupportIncidence.derive object order profile baseline).incidence.internalIncidences := by
  classical
  have innerCard :
      ∀ tail : {vertex //
          vertex ∈ packedSupport object order profile},
        Fintype.card {head //
            head ∈ SupportIncidenceLedger.insideNeighbors object
              (packedSupport object order profile) tail.1} =
          (SupportIncidenceLedger.insideNeighbors object
            (packedSupport object order profile) tail.1).length := by
    intro tail
    apply card_list_membership
    exact (object.orderedNeighbors_nodup tail.1).filter _
  rw [Fintype.card_sigma]
  simp_rw [innerCard]
  change (∑ tail : {vertex //
      vertex ∈ packedSupport object order profile},
        (SupportIncidenceLedger.insideNeighbors object
          (packedSupport object order profile) tail.1).length) =
    _
  rw [subtype_sum_eq_filtered_sum object
    (packedSupport object order profile)
    (fun vertex => (SupportIncidenceLedger.insideNeighbors object
      (packedSupport object order profile) vertex).length)]
  rfl

/-- Exact internal path plus cross-window identity. -/
theorem internal_card_eq_path_add_cross :
    (PackedSupportIncidence.derive object order profile baseline).incidence.internalIncidences =
      (pathIncidences object order profile).card +
        (crossWindowIncidences object order profile).card := by
  rw [internal_partition object order profile,
    internal_supply_exact object order profile baseline]

/-- Exact boundary-incidence identity. -/
theorem boundary_count_exact :
    (PackedSupportIncidence.derive object order profile baseline).incidence.boundaryIncidences =
      (boundaryIncidences object order profile).card := by
  classical
  have outerCard :
      ∀ tail : {vertex //
          vertex ∈ packedSupport object order profile},
        Fintype.card {head //
            head ∈ SupportIncidenceLedger.outsideNeighbors object
              (packedSupport object order profile) tail.1} =
          (SupportIncidenceLedger.outsideNeighbors object
            (packedSupport object order profile) tail.1).length := by
    intro tail
    apply card_list_membership
    exact (object.orderedNeighbors_nodup tail.1).filter _
  rw [boundaryIncidences, Finset.card_univ, Fintype.card_sigma]
  simp_rw [outerCard]
  change _ = (∑ tail : {vertex //
      vertex ∈ packedSupport object order profile},
        (SupportIncidenceLedger.outsideNeighbors object
          (packedSupport object order profile) tail.1).length)
  rw [subtype_sum_eq_filtered_sum object
    (packedSupport object order profile)
    (fun vertex => (SupportIncidenceLedger.outsideNeighbors object
      (packedSupport object order profile) vertex).length)]
  rfl

/-- Exact degree-surplus split into path, cross-window, and boundary
incidences. -/
theorem exact_degree_surplus_split :
    baseline.degree *
          (PackedSupportIncidence.derive object order profile baseline).incidence.selected.length +
        (PackedSupportIncidence.derive object order profile baseline).selectedSurplus =
      (pathIncidences object order profile).card +
        (crossWindowIncidences object order profile).card +
        (boundaryIncidences object order profile).card := by
  rw [← internal_card_eq_path_add_cross object order profile baseline,
    ← boundary_count_exact object order profile baseline]
  have identity :=
    PackedSupportIncidence.exact_support_incidence_identity
      object order profile baseline
  omega

/-- One literal surplus unit at a graph vertex. -/
abbrev SurplusUnit :=
  Σ vertex : object.Vertex, Fin (object.degree vertex - baseline.degree)

abbrev PathToken :=
  {incidence // incidence ∈ pathIncidences object order profile}

abbrev CrossWindowToken :=
  {incidence // incidence ∈ crossWindowIncidences object order profile}

abbrev BoundaryToken :=
  BoundaryIncidence object order profile

abbrev PackedVertexToken :=
  {vertex // vertex ∈ packedSupport object order profile}

abbrev RemainderVertexToken :=
  {vertex // vertex ∉ packedSupport object order profile}

/-- The six supplies form a canonical disjoint sum. -/
abbrev Token :=
  PathToken object order profile ⊕
  CrossWindowToken object order profile ⊕
  BoundaryToken object order profile ⊕
  PackedVertexToken object order profile ⊕
  RemainderVertexToken object order profile ⊕
  SurplusUnit object baseline

theorem path_supply :
    Fintype.card (PathToken object order profile) =
      (pathIncidences object order profile).card := by
  classical exact Fintype.card_coe _

theorem cross_window_supply :
    Fintype.card (CrossWindowToken object order profile) =
      (crossWindowIncidences object order profile).card := by
  classical exact Fintype.card_coe _

theorem boundary_supply :
    Fintype.card (BoundaryToken object order profile) =
      (boundaryIncidences object order profile).card := by
  classical simp [BoundaryToken, boundaryIncidences]

theorem packed_vertex_supply :
    Fintype.card (PackedVertexToken object order profile) =
      (packedSupport object order profile).card := by
  classical exact Fintype.card_coe _

theorem remainder_vertex_supply :
    Fintype.card (RemainderVertexToken object order profile) =
      object.vertexCount - (packedSupport object order profile).card := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_coe,
    FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard]

theorem surplus_supply :
    Fintype.card (SurplusUnit object baseline) =
      (DegreeSurplusLedger.derive object baseline).total := by
  classical
  simp [SurplusUnit, Fintype.card_sigma,
    DegreeSurplusLedger.Ledger.total]

/-- Total capacity is determined by the six literal graph-derived supplies. -/
theorem total_token_supply :
    Fintype.card (Token object order profile baseline) =
      (pathIncidences object order profile).card +
      (crossWindowIncidences object order profile).card +
      (boundaryIncidences object order profile).card +
      (packedSupport object order profile).card +
      (object.vertexCount - (packedSupport object order profile).card) +
      (DegreeSurplusLedger.derive object baseline).total := by
  classical
  simp only [Token, Fintype.card_sum]
  rw [path_supply, cross_window_supply, boundary_supply,
    packed_vertex_supply, remainder_vertex_supply, surplus_supply]
  omega

end Hypostructure.Graph.Strategy.Official.Features.PackedWindowTokenLedger
