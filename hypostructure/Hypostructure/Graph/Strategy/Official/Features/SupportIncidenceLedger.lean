import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hypostructure.Graph.Finite

/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT11 -> CT5).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/

/-!
# Exact support/complement incidence ledgers

The construction applies to any finite selected support.  It is deliberately
independent of induced paths and of a numerical degree baseline.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.SupportIncidenceLedger

open scoped BigOperators
open Hypostructure.Graph

universe u

def insideNeighbors (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    List object.Vertex :=
  object.orderedNeighbors vertex |>.filter fun neighbor =>
    decide (neighbor ∈ support)

def outsideNeighbors (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    List object.Vertex :=
  object.orderedNeighbors vertex |>.filter fun neighbor =>
    !(decide (neighbor ∈ support))

structure Ledger (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) where
  selected : List object.Vertex
  selected_eq : selected = object.orderedVertices.filter fun vertex =>
    decide (vertex ∈ support)
  remainder : List object.Vertex
  remainder_eq : remainder = object.orderedVertices.filter fun vertex =>
    !(decide (vertex ∈ support))
  internalIncidences : Nat
  internalIncidences_eq :
    internalIncidences =
      (selected.map fun vertex =>
        (insideNeighbors object support vertex).length).sum
  boundaryIncidences : Nat
  boundaryIncidences_eq :
    boundaryIncidences =
      (selected.map fun vertex =>
        (outsideNeighbors object support vertex).length).sum

def derive (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) : Ledger object support := by
  let selected := object.orderedVertices.filter fun vertex =>
    decide (vertex ∈ support)
  let remainder := object.orderedVertices.filter fun vertex =>
    !(decide (vertex ∈ support))
  exact
    { selected := selected
      selected_eq := rfl
      remainder := remainder
      remainder_eq := rfl
      internalIncidences :=
        (selected.map fun vertex =>
          (insideNeighbors object support vertex).length).sum
      internalIncidences_eq := rfl
      boundaryIncidences :=
        (selected.map fun vertex =>
          (outsideNeighbors object support vertex).length).sum
      boundaryIncidences_eq := rfl }

theorem inside_outside_length (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    (insideNeighbors object support vertex).length +
      (outsideNeighbors object support vertex).length =
      object.degree vertex := by
  rw [← object.orderedNeighbors_length vertex]
  unfold insideNeighbors outsideNeighbors
  induction object.orderedNeighbors vertex with
  | nil => simp
  | cons neighbor tail ih =>
      by_cases member : neighbor ∈ support
      · simp only [List.filter_cons]
        simp [member] at *
        omega
      · simp only [List.filter_cons]
        simp [member] at *
        omega

/-- Exact degree-sum partition over the selected support. -/
theorem degree_sum_partition (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) :
    (derive object support).internalIncidences +
        (derive object support).boundaryIncidences =
      ((derive object support).selected.map object.degree).sum := by
  simp only [derive]
  induction (object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ support)) with
  | nil => simp
  | cons vertex tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih, ← inside_outside_length object support vertex]
      omega

theorem selected_remainder_partition (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    (support : Finset object.Vertex) :
    (derive object support).selected.length +
        (derive object support).remainder.length =
      object.vertexCount := by
  simp only [derive]
  have partitionLength :
      ∀ vertices : List object.Vertex,
        (vertices.filter fun vertex => decide (vertex ∈ support)).length +
          (vertices.filter fun vertex => !(decide (vertex ∈ support))).length =
          vertices.length := by
    intro vertices
    induction vertices with
    | nil => simp
    | cons vertex tail ih =>
        by_cases member : vertex ∈ support
        · simp only [List.filter_cons]
          simp [member] at *
          omega
        · simp only [List.filter_cons]
          simp [member] at *
          omega
  rw [object.vertexCount_eq_orderedVertices_length]
  exact partitionLength object.orderedVertices

end Hypostructure.Graph.Strategy.Official.Features.SupportIncidenceLedger
