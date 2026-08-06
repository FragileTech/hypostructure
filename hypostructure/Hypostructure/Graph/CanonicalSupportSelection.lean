import Hypostructure.Graph.SupportComponents

/-!
# Canonical selection of a minimum connected support containing a seed

The manuscript repeatedly names *"the lexicographically first connected subgraph
of `G` with the minimum possible number of vertices that contains …"*.  This
module is the framework's single implementation of that phrase.

The candidate family is every vertex subset of the object that contains the seed
and is connected.  Among those, the ones of least cardinality are the minimum
ones, and the selection is the head of the object's own enumeration of that
family.  So the result is a function of the object and the seed alone — no path,
no ordering and no witness is supplied by a caller — which is the canonicity the
manuscript's constructions claim.

Nothing here knows what a seed is for.  A pair of demand supports, a family of
pair supports, or a single window all select through the same three
declarations.
-/

namespace Hypostructure.Graph.CanonicalSupport

open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u})

/-- The candidate family: the connected vertex sets containing the seed. -/
noncomputable def candidates (seed : Finset object.Vertex) :
    Finset (Finset object.Vertex) := by
  classical
  exact object.vertexFinset.powerset.filter fun support =>
    seed ⊆ support ∧ SupportComponents.Connected.ConnectedOn object support

variable {object}

theorem mem_candidates_iff {seed support : Finset object.Vertex} :
    support ∈ candidates object seed ↔
      seed ⊆ support ∧ SupportComponents.Connected.ConnectedOn object support := by
  classical
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨_, rest⟩; exact rest
  · intro rest
    exact ⟨fun vertex _ => object.mem_vertexFinset vertex, rest⟩

/-- Every candidate of least cardinality: the manuscript's "minimum possible
number of vertices". -/
noncomputable def minimalCandidates (object : FiniteObject.{u})
    (seed : Finset object.Vertex) : Finset (Finset object.Vertex) := by
  classical
  exact (candidates object seed).filter fun support =>
    ∀ other ∈ candidates object seed, support.card ≤ other.card

/-- **The canonical minimum connected support containing the seed.**

`none` exactly when no connected set contains the seed; otherwise the head of
the object's own enumeration of the minimum-cardinality candidates.  The choice
uses only the object and the seed. -/
noncomputable def select? (object : FiniteObject.{u})
    (seed : Finset object.Vertex) : Option (Finset object.Vertex) :=
  (minimalCandidates object seed).toList.head?

/-- A selected support is a candidate: it contains the seed and is connected. -/
theorem select?_mem_candidates {seed support : Finset object.Vertex}
    (selected : select? object seed = some support) :
    support ∈ candidates object seed := by
  classical
  have member : support ∈ (minimalCandidates object seed).toList :=
    List.mem_of_mem_head? selected
  have : support ∈ minimalCandidates object seed := by
    simpa using member
  exact (Finset.mem_filter.1 this).1

/-- A selected support has the minimum possible number of vertices. -/
theorem select?_card_le {seed support other : Finset object.Vertex}
    (selected : select? object seed = some support)
    (candidate : other ∈ candidates object seed) :
    support.card ≤ other.card := by
  classical
  have member : support ∈ (minimalCandidates object seed).toList :=
    List.mem_of_mem_head? selected
  have : support ∈ minimalCandidates object seed := by
    simpa using member
  exact (Finset.mem_filter.1 this).2 other candidate

/-- The selection succeeds whenever some connected set contains the seed. -/
theorem select?_isSome {seed : Finset object.Vertex}
    (witness : (candidates object seed).Nonempty) :
    (select? object seed).isSome := by
  classical
  obtain ⟨least, member, minimal⟩ :=
    Finset.exists_min_image (candidates object seed) Finset.card witness
  have inMinimal : least ∈ minimalCandidates object seed :=
    Finset.mem_filter.2 ⟨member, minimal⟩
  have nonempty : (minimalCandidates object seed).toList ≠ [] := by
    intro empty
    have : least ∈ (minimalCandidates object seed).toList := by simpa using inMinimal
    rw [empty] at this
    exact absurd this (List.not_mem_nil)
  cases list : (minimalCandidates object seed).toList with
  | nil => exact absurd list nonempty
  | cons head tail => simp [select?, list]

/-- The whole vertex set is a candidate whenever the object is connected, so the
selection succeeds at every seed of a connected object.  This is the form the
manuscript's constructions use: `G` itself always contains the seed. -/
theorem select?_isSome_of_connected {seed : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object object.vertexFinset) :
    (select? object seed).isSome :=
  select?_isSome ⟨object.vertexFinset,
    mem_candidates_iff.2 ⟨fun vertex _ => object.mem_vertexFinset vertex, connected⟩⟩

end Hypostructure.Graph.CanonicalSupport
