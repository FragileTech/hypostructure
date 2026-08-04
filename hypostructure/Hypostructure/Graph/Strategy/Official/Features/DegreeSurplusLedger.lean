import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hypostructure.Graph.Finite

/-!
# Graph-derived degree-surplus ledgers

This file contains the graph-owned realization of surplus above a closed
minimum-degree baseline.  The baseline is a parameter of the strategy; all
rows and totals are read from the literal finite graph.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger

open scoped BigOperators
open Hypostructure.Graph

universe u

/-- A closed lower degree baseline.  It contains no authored surplus value. -/
structure MinimumDegreeBaseline (object : FiniteObject.{u}) where
  degree : Nat
  lower : ∀ vertex : object.Vertex, degree ≤ object.degree vertex

/-- One graph-derived row of the surplus ledger. -/
structure Row (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) where
  vertex : object.Vertex
  surplus : Nat := object.degree vertex - baseline.degree

/-- The complete degree-surplus ledger in the graph's declared vertex order. -/
structure Ledger (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) where
  rows : List (Row object baseline)
  rows_eq :
    rows = object.orderedVertices.map fun vertex =>
      { vertex := vertex
        surplus := object.degree vertex - baseline.degree }

def derive (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) :
    Ledger object baseline where
  rows := object.orderedVertices.map fun vertex =>
    { vertex := vertex
      surplus := object.degree vertex - baseline.degree }
  rows_eq := rfl

def Ledger.total {object : FiniteObject.{u}}
    {baseline : MinimumDegreeBaseline object}
    (_ledger : Ledger object baseline) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  exact ∑ vertex, (object.degree vertex - baseline.degree)

def degreeMass (object : FiniteObject.{u}) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  exact ∑ vertex, object.degree vertex

@[simp] theorem total_derive (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) :
    (derive object baseline).total =
      (object.orderedVertices.map fun vertex =>
        object.degree vertex - baseline.degree).sum := by
  letI : FinEnum object.Vertex := object.vertices
  rw [Ledger.total]
  change (Finset.univ.sum fun vertex =>
      object.degree vertex - baseline.degree) =
    (object.orderedVertices.map fun vertex =>
      object.degree vertex - baseline.degree).sum
  rw [← List.sum_toFinset _ object.orderedVertices_nodup]
  congr 1
  ext vertex
  simp

/-- Under the closed lower baseline, subtraction may be moved through the
finite degree sum. -/
theorem total_add_baseline_mass (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) :
    (derive object baseline).total +
        baseline.degree * object.vertexCount =
      degreeMass object := by
  letI : FinEnum object.Vertex := object.vertices
  rw [Ledger.total, FiniteObject.vertexCount]
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      degreeMass, FinEnum.card_eq_fintypeCard]
    rw [Nat.mul_comm baseline.degree]
    apply Nat.sub_add_cancel
    have bounded :
        (∑ _vertex : object.Vertex, baseline.degree) ≤
          ∑ vertex : object.Vertex, object.degree vertex := by
      apply Finset.sum_le_sum
      intro vertex _
      exact baseline.lower vertex
    simpa [Finset.sum_const, nsmul_eq_mul] using bounded
  · intro vertex _
    exact baseline.lower vertex

/-- The graph handshake closes the surplus ledger against literal edge and
vertex counts. -/
theorem exact_edge_count_identity (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) :
    (derive object baseline).total +
        baseline.degree * object.vertexCount =
      2 * object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [total_add_baseline_mass]
  simpa [degreeMass, FiniteObject.degree, FiniteObject.edgeCount] using
    object.graph.sum_degrees_eq_twice_card_edges

/-- Equivalent subtraction form, valid because the baseline mass is bounded
by the handshake total. -/
theorem total_eq_edge_mass_sub_baseline (object : FiniteObject.{u})
    (baseline : MinimumDegreeBaseline object) :
    (derive object baseline).total =
      2 * object.edgeCount - baseline.degree * object.vertexCount := by
  have identity := exact_edge_count_identity object baseline
  omega

end Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger
