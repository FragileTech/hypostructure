/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT11 -> CT6).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Core.Finite.Search
import Hypostructure.Graph.SupportComponents

/-!
# Canonical connected support hulls

Graph exhaustively scans ambient vertex subsets, first by cardinality and then
by the inherited vertex order.  Core's sealed first-hit search therefore
selects the first minimum-cardinality connected support containing a supplied
finite seed.  Boundary vertices and all local/outside incidences are computed
from the ambient graph.

There is no application classifier, selected support, boundary declaration, or
numerical parameter in this interface.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.CanonicalConnectedSupportHull

open Hypostructure.Core.Finite
open Hypostructure.Graph
open Hypostructure.Graph.SupportComponents.Connected

universe u

namespace Presentation

variable (object : FiniteObject.{u})

/-- Every ambient subset, ordered first by cardinality and then by the
subsequence order inherited from `orderedVertices`.  `dedup` is defensive and
does not alter the first occurrence of a support. -/
noncomputable def supportValues : List (Finset object.Vertex) := by
  classical
  exact ((List.range (object.vertexCount + 1)).flatMap fun cardinality =>
    (object.orderedVertices.sublists.filter
      (fun vertices => vertices.length = cardinality)).map List.toFinset).dedup

/-- The exact framework-owned support schedule. -/
noncomputable def supports : Enumeration (Finset object.Vertex) := by
  classical
  exact {
    values := supportValues object
    nodup := List.nodup_dedup _
    decEq := inferInstance }

/-- The schedule is genuinely exhaustive over ambient supports; it is not a
declared candidate list. -/
theorem mem_supportValues (support : Finset object.Vertex) :
    support ∈ supportValues object := by
  classical
  let ordered :=
    object.orderedVertices.filter fun vertex => vertex ∈ support
  have orderedSublist : ordered.Sublist object.orderedVertices :=
    List.filter_sublist
  have orderedMem : ordered ∈ object.orderedVertices.sublists :=
    List.mem_sublists.mpr orderedSublist
  have orderedFinset : ordered.toFinset = support := by
    ext vertex
    simp [ordered]
  have lengthBound : ordered.length ≤ object.vertexCount := by
    calc
      ordered.length ≤ object.orderedVertices.length :=
        orderedSublist.length_le
      _ = object.vertexCount :=
        object.vertexCount_eq_orderedVertices_length.symm
  rw [supportValues, List.mem_dedup, List.mem_flatMap]
  refine ⟨ordered.length, ?_, ?_⟩
  · exact List.mem_range.mpr (Nat.lt_succ_iff.mpr lengthBound)
  · simp only [List.mem_map, List.mem_filter]
    exact ⟨ordered, ⟨orderedMem, by simp⟩, orderedFinset⟩

theorem mem_supports (support : Finset object.Vertex) :
    support ∈ (supports object).values :=
  mem_supportValues object support

/-- A candidate contains the seed and is connected in the ambient graph. -/
def Admissible (seed support : Finset object.Vertex) : Prop :=
  seed ⊆ support ∧ ConnectedOn object support

noncomputable def execution (seed : Finset object.Vertex) :=
  Hypostructure.Core.Finite.Search.run
    (supports object) (Admissible object seed) (fun _ => Classical.dec _)

theorem reported_sound (seed : Finset object.Vertex)
    {support : Finset object.Vertex}
    (reported : (execution object seed).value? = some support) :
    support ∈ (supports object).values ∧ Admissible object seed support :=
  Hypostructure.Core.Finite.Search.value_sound
    (supports object) (Admissible object seed) (fun _ => Classical.dec _) reported

/-- Total selected hull when the ambient graph is connected and the seed is
nonempty.  This public constructor lets downstream official strategies reuse
the same canonical support search instead of rebuilding a private fallback. -/
structure Selected
    (seed : Finset object.Vertex) where
  support : Finset object.Vertex
  reported : (execution object seed).value? = some support
  seed_subset : seed ⊆ support
  connected : ConnectedOn object support

private theorem fullSupport_connected
    (ambientConnected : object.graph.Connected) :
    ConnectedOn object object.vertexFinset := by
  refine ⟨?_, ?_⟩
  · letI : Nonempty object.Vertex := ambientConnected.nonempty
    exact ⟨Classical.choice ambientConnected.nonempty,
      object.mem_vertexFinset _⟩
  · intro left right _left _right
    obtain ⟨path, isPath⟩ := ambientConnected.exists_isPath left right
    exact ⟨path, isPath, fun vertex _ => object.mem_vertexFinset vertex⟩

noncomputable def select
    (seed : Finset object.Vertex)
    (seedNonempty : seed.Nonempty)
    (ambientConnected : object.graph.Connected) :
    Selected object seed := by
  let run := execution object seed
  have admissibleFull : Admissible object seed object.vertexFinset :=
    ⟨fun vertex _ => object.mem_vertexFinset vertex,
      fullSupport_connected object ambientConnected⟩
  have hasHit : run.HasHit :=
    Hypostructure.Core.Finite.Search.complete
      (supports object) (Admissible object seed) (fun _ => Classical.dec _)
      ⟨object.vertexFinset, mem_supports object object.vertexFinset,
        admissibleFull⟩
  let hit := run.hitOfHasHit hasHit
  let support := hit.value
  have hitReported := run.hit?_eq_some_hitOfHasHit hasHit
  have reported : run.value? = some support := by
    unfold Hypostructure.Core.Finite.Search.Execution.value?
    rw [hitReported]
    rfl
  have sound := reported_sound object seed reported
  exact
    { support := support
      reported := reported
      seed_subset := sound.2.1
      connected := sound.2.2 }

/-- Vertices of the selected support incident with its complement. -/
def boundary (support : Finset object.Vertex) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact support.filter fun vertex =>
    (object.orderedNeighbors vertex).any fun neighbor => neighbor ∉ support

/-- Number of incidences from a support vertex to another support vertex. -/
def insideDegree (support : Finset object.Vertex)
    (vertex : object.Vertex) : Nat := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ((object.orderedNeighbors vertex).filter
    (fun neighbor => decide (neighbor ∈ support))).length

/-- Number of incidences from a support vertex to the complement. -/
def outsideDegree (support : Finset object.Vertex)
    (vertex : object.Vertex) : Nat := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ((object.orderedNeighbors vertex).filter
    (fun neighbor => decide (neighbor ∉ support))).length

/-- The uncapped, ambient-derived boundary coordinate. -/
def boundaryProfile (support : Finset object.Vertex) :
    object.Vertex → Nat × Nat :=
  fun vertex => (insideDegree object support vertex,
    outsideDegree object support vertex)

@[simp] theorem mem_boundary_iff (support : Finset object.Vertex)
    (vertex : object.Vertex) :
    vertex ∈ boundary object support ↔
      vertex ∈ support ∧
        ∃ neighbor, object.graph.Adj vertex neighbor ∧ neighbor ∉ support := by
  classical
  simp [boundary, FiniteObject.mem_orderedNeighbors_iff]

theorem outsideDegree_pos_iff (support : Finset object.Vertex)
    (vertex : object.Vertex) :
    0 < outsideDegree object support vertex ↔
      ∃ neighbor, object.graph.Adj vertex neighbor ∧ neighbor ∉ support := by
  classical
  simp [outsideDegree,
    FiniteObject.mem_orderedNeighbors_iff]

@[simp] theorem mem_boundary_iff_outsideDegree_pos
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ boundary object support ↔
      vertex ∈ support ∧ 0 < outsideDegree object support vertex := by
  rw [mem_boundary_iff, outsideDegree_pos_iff]

end Presentation

end Hypostructure.Graph.Strategy.Official.Features.CanonicalConnectedSupportHull
