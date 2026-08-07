import Hypostructure.Graph.Progress
import Hypostructure.Graph.DeletionCriticality

/-!
# Degeneracy, and `lem:sparse-upper-envelope`

The manuscript proves `m ≤ 2n − 2` from two facts it has already established:

* `lem:no-proper-core` -- no proper subgraph meets the registered baseline, so
  every proper subgraph has a vertex of degree at most `δ − 1`; that is exactly
  `(δ − 1)`-degeneracy of every proper subgraph;
* `lem:deletion-critical` -- every edge has an endpoint sitting exactly at the
  baseline, so the object carries a vertex of degree exactly `δ`.

Deleting that tight vertex leaves a `(δ − 1)`-degenerate graph, a `k`-degenerate
graph on `N ≥ k+1` vertices has at most `kN − C(k+1,2)` edges, and adding the
tight vertex's own `δ` edges back gives the envelope.

Everything here is stated at the registered baseline `δ` rather than at the
manuscript's `3`.  The manuscript's display is the case `δ = 3`:

  `m + 2 ≤ (δ − 1)·n`  becomes  `m + 2 ≤ 2n`,

and the degeneracy count `kN − C(k+1,2)` becomes `2N − 3`.  The envelope is
false above the registered baseline in the manuscript's own shape -- a
`4`-regular graph has `m = 2n` -- which is why the coefficient is `δ − 1` and
not a numeral.

The counting avoids `Sym2` and avoids division: `localIncidences` holds the
*ordered* adjacent pairs inside a support, so it counts each induced edge twice
and its total is the induced degree sum.  Nothing in this module mentions a
target, a presentation, or a paper label as data.
-/

namespace Hypostructure.Graph

namespace FiniteObject

open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

/-- The object's declared vertex equality, as an instance for this module. -/
def envelopeVertexDecEq (object : FiniteObject.{u}) : DecidableEq object.Vertex :=
  object.vertices.decEq

attribute [local instance] envelopeVertexDecEq
attribute [local instance] FiniteObject.decideAdj

/-! ## Degrees and incidences inside an explicit support -/

/-- The number of neighbours a vertex has inside an explicit support: the degree
of the induced restriction, read on the ambient object. -/
def localDegree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) : Nat :=
  (support.filter fun other => object.graph.Adj vertex other).card

/-- The ordered adjacent pairs inside a support.  Each induced edge appears
twice, once in each orientation, so the count below is the induced degree sum
and no division is introduced. -/
def localIncidences (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    Finset (object.Vertex × object.Vertex) :=
  (support ×ˢ support).filter fun pair => object.graph.Adj pair.1 pair.2

theorem mem_localIncidences_iff (support : Finset object.Vertex)
    (pair : object.Vertex × object.Vertex) :
    pair ∈ object.localIncidences support ↔
      pair.1 ∈ support ∧ pair.2 ∈ support ∧ object.graph.Adj pair.1 pair.2 := by
  rw [localIncidences, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **The handshake inside a support.**  Summing the induced degrees counts each
ordered adjacent pair once. -/
theorem card_localIncidences (support : Finset object.Vertex) :
    (object.localIncidences support).card =
      ∑ vertex ∈ support, object.localDegree support vertex := by
  rw [localIncidences, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun vertex _ => ?_
  rw [localDegree, Finset.card_filter]

/-- A vertex is not its own neighbour, so its induced degree misses at least
itself. -/
theorem localDegree_add_one_le_card (support : Finset object.Vertex)
    {vertex : object.Vertex} (member : vertex ∈ support) :
    object.localDegree support vertex + 1 ≤ support.card := by
  have subset : (support.filter fun other => object.graph.Adj vertex other) ⊆
      support.erase vertex := by
    intro other selected
    rw [Finset.mem_filter] at selected
    refine Finset.mem_erase.2 ⟨fun equality => ?_, selected.1⟩
    exact object.graph.irrefl (equality ▸ selected.2)
  have counted := Finset.card_le_card subset
  have erased := Finset.card_erase_add_one member
  rw [localDegree]
  omega

/-! ## Deleting one vertex of a support -/

/-- **The deletion identity.**  Removing a vertex from the support removes
exactly the ordered pairs in which it appears, and it appears once as a first
coordinate and once as a second coordinate of each of its induced edges. -/
theorem card_localIncidences_erase (support : Finset object.Vertex)
    {vertex : object.Vertex} (member : vertex ∈ support) :
    (object.localIncidences support).card =
      (object.localIncidences (support.erase vertex)).card +
        2 * object.localDegree support vertex := by
  set neighbours := support.filter (fun other => object.graph.Adj vertex other)
    with neighboursDef
  set outgoing := neighbours.image fun other => (vertex, other) with outgoingDef
  set incoming := neighbours.image fun other => (other, vertex) with incomingDef
  have split : object.localIncidences support =
      object.localIncidences (support.erase vertex) ∪ (outgoing ∪ incoming) := by
    ext pair
    obtain ⟨left, right⟩ := pair
    rw [Finset.mem_union, Finset.mem_union, mem_localIncidences_iff,
      mem_localIncidences_iff, outgoingDef, incomingDef]
    simp only [Finset.mem_image, neighboursDef, Finset.mem_filter,
      Finset.mem_erase, Prod.mk.injEq]
    constructor
    · rintro ⟨leftMem, rightMem, adjacent⟩
      by_cases leftIsVertex : left = vertex
      · subst leftIsVertex
        exact .inr (.inl ⟨right, ⟨rightMem, adjacent⟩, rfl, rfl⟩)
      · by_cases rightIsVertex : right = vertex
        · subst rightIsVertex
          exact .inr (.inr ⟨left, ⟨leftMem, adjacent.symm⟩, rfl, rfl⟩)
        · exact .inl ⟨⟨leftIsVertex, leftMem⟩, ⟨rightIsVertex, rightMem⟩, adjacent⟩
    · rintro (⟨⟨_, leftMem⟩, ⟨_, rightMem⟩, adjacent⟩ |
        ⟨other, ⟨inside, adjacent⟩, first, second⟩ |
        ⟨other, ⟨inside, adjacent⟩, first, second⟩)
      · exact ⟨leftMem, rightMem, adjacent⟩
      · subst first; subst second
        exact ⟨member, inside, adjacent⟩
      · subst first; subst second
        exact ⟨inside, member, adjacent.symm⟩
  have outgoingDisjoint :
      Disjoint (object.localIncidences (support.erase vertex))
        (outgoing ∪ incoming) := by
    refine Finset.disjoint_left.2 fun pair survives removed => ?_
    rw [mem_localIncidences_iff] at survives
    rw [Finset.mem_union, outgoingDef, incomingDef] at removed
    have leftNe : pair.1 ≠ vertex := (Finset.mem_erase.1 survives.1).1
    have rightNe : pair.2 ≠ vertex := (Finset.mem_erase.1 survives.2.1).1
    rcases removed with selected | selected
    · obtain ⟨_, _, first⟩ := Finset.mem_image.1 selected
      exact leftNe (congrArg Prod.fst first).symm
    · obtain ⟨_, _, second⟩ := Finset.mem_image.1 selected
      exact rightNe (congrArg Prod.snd second).symm
  have orientationDisjoint : Disjoint outgoing incoming := by
    refine Finset.disjoint_left.2 fun pair fromOut fromIn => ?_
    obtain ⟨_, _, outEq⟩ := Finset.mem_image.1 fromOut
    obtain ⟨other, selected, inEq⟩ := Finset.mem_image.1 fromIn
    have firstIsVertex : vertex = pair.1 := congrArg Prod.fst outEq
    have firstIsOther : other = pair.1 := congrArg Prod.fst inEq
    rw [neighboursDef, Finset.mem_filter] at selected
    exact object.graph.irrefl
      (show object.graph.Adj vertex vertex from
        (firstIsOther.trans firstIsVertex.symm) ▸ selected.2)
  have outgoingCard : outgoing.card = object.localDegree support vertex := by
    rw [outgoingDef, localDegree, ← neighboursDef]
    exact Finset.card_image_of_injective _ fun _ _ equality =>
      congrArg Prod.snd equality
  have incomingCard : incoming.card = object.localDegree support vertex := by
    rw [incomingDef, localDegree, ← neighboursDef]
    exact Finset.card_image_of_injective _ fun _ _ equality =>
      congrArg Prod.fst equality
  rw [split, Finset.card_union_of_disjoint outgoingDisjoint,
    Finset.card_union_of_disjoint orientationDisjoint, outgoingCard, incomingCard]
  omega

/-! ## The degeneracy bound -/

/-- **A `k`-degenerate graph on `N ≥ k+1` vertices has at most `kN − C(k+1,2)`
edges**, in the subtraction-free doubled form the ordered incidences count:

  `|localIncidences| + k(k+1) ≤ 2kN`.

The proof is the degeneracy order itself: remove a vertex of induced degree at
most `k`, which drops the ordered incidence count by at most `2k`, until only
`k+1` vertices remain, where the count is at most `(k+1)k` because no vertex is
its own neighbour. -/
theorem card_localIncidences_le_of_degenerate (bound : Nat)
    (support : Finset object.Vertex)
    (sparse : ∀ inner ⊆ support, inner.Nonempty →
      ∃ vertex ∈ inner, object.localDegree inner vertex ≤ bound)
    (large : bound + 1 ≤ support.card) :
    (object.localIncidences support).card + bound * (bound + 1) ≤
      2 * bound * support.card := by
  induction support using Finset.strongInduction with
  | _ support ih =>
      by_cases base : support.card = bound + 1
      · have summed : (object.localIncidences support).card ≤
            support.card * (support.card - 1) := by
          rw [card_localIncidences]
          calc ∑ vertex ∈ support, object.localDegree support vertex
              ≤ ∑ _vertex ∈ support, (support.card - 1) :=
                Finset.sum_le_sum fun vertex member => by
                  have := object.localDegree_add_one_le_card support member
                  omega
            _ = support.card * (support.card - 1) := by
                rw [Finset.sum_const, smul_eq_mul]
        rw [base] at summed ⊢
        rw [Nat.add_sub_cancel] at summed
        calc (object.localIncidences support).card + bound * (bound + 1)
            ≤ (bound + 1) * bound + bound * (bound + 1) :=
              Nat.add_le_add_right summed _
          _ = 2 * bound * (bound + 1) := by ring
      · obtain ⟨vertex, member, small⟩ :=
          sparse support (Finset.Subset.refl _) (Finset.card_pos.1 (by omega))
        have erasedCard : (support.erase vertex).card + 1 = support.card :=
          Finset.card_erase_add_one member
        have smaller := ih (support.erase vertex) (Finset.erase_ssubset member)
          (fun inner subset nonempty =>
            sparse inner (subset.trans (Finset.erase_subset _ _)) nonempty)
          (by omega)
        have deletion := object.card_localIncidences_erase support member
        have expand : 2 * bound * support.card =
            2 * bound * (support.erase vertex).card + 2 * bound := by
          rw [← erasedCard]; ring
        obtain ⟨cost, costDef⟩ : ∃ cost, bound * (bound + 1) = cost := ⟨_, rfl⟩
        obtain ⟨inner, innerDef⟩ :
            ∃ inner, 2 * bound * (support.erase vertex).card = inner := ⟨_, rfl⟩
        rw [costDef] at smaller ⊢
        rw [innerDef] at smaller expand
        rw [expand]
        omega

/-! ## `lem:sparse-upper-envelope` -/

/-- The full support's induced degree is the object's own degree. -/
theorem localDegree_vertexFinset (vertex : object.Vertex) :
    object.localDegree object.vertexFinset vertex = object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  rw [localDegree, degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext other
  rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun selected => selected.2,
    fun adjacent => ⟨object.mem_vertexFinset other, adjacent⟩⟩

/-- **The handshake.**  The ordered adjacent pairs of the whole vertex set are
counted twice by the edges. -/
theorem card_localIncidences_vertexFinset (object : FiniteObject.{u}) :
    (object.localIncidences object.vertexFinset).card = 2 * object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  have handshake :
      (∑ vertex : object.Vertex, object.degree vertex) = 2 * object.edgeCount := by
    simpa [FiniteObject.degree, FiniteObject.edgeCount] using
      object.graph.sum_degrees_eq_twice_card_edges
  rw [card_localIncidences, ← handshake]
  refine Finset.sum_congr ?_ fun vertex _ => object.localDegree_vertexFinset vertex
  ext vertex
  simp [vertexFinset]

/-- The induced restriction's degree is the ambient object's local degree. -/
theorem degree_induce_eq_localDegree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : (object.induce support).Vertex) :
    (object.induce support).degree vertex =
      object.localDegree support vertex.1 := by
  letI : FinEnum object.Vertex := object.vertices
  let induced := object.induce support
  letI : FinEnum induced.Vertex := induced.vertices
  rw [degree, ← SimpleGraph.card_neighborFinset_eq_degree, localDegree]
  refine Finset.card_bij (fun other _ => other.1) ?_ ?_ ?_
  · intro other member
    rw [SimpleGraph.mem_neighborFinset] at member
    exact Finset.mem_filter.2 ⟨other.2, member⟩
  · intro left _ right _ equality
    exact Subtype.ext equality
  · intro other member
    rw [Finset.mem_filter] at member
    refine ⟨⟨other, member.1⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact member.2

/-- **`lem:sparse-upper-envelope` at the registered baseline.**

`m + 2 ≤ (δ − 1)·n`, the manuscript's `m ≤ 2n − 2` at `δ = 3`.

The two hypotheses are the two facts the manuscript spends and the branch has
already committed: no proper subgraph meets the baseline, and some vertex sits
exactly at it.  Nothing else about the object is used. -/
theorem edgeCount_add_two_le_of_noProperBaseline (object : FiniteObject.{u})
    {threshold : Nat} (three : 3 ≤ threshold)
    (noProperBaseline : ∀ subgraph : ProperSubgraph object,
      ¬ MinimumDegreeAtLeast threshold subgraph.value)
    {tight : object.Vertex} (atBaseline : object.degree tight = threshold) :
    object.edgeCount + 2 ≤ (threshold - 1) * object.vertexCount := by
  set bound := threshold - 1 with boundDef
  have thresholdEq : threshold = bound + 1 := by omega
  have room : object.degree tight + 1 ≤ object.vertexCount := by
    have counted := object.localDegree_add_one_le_card object.vertexFinset
      (object.mem_vertexFinset tight)
    rw [localDegree_vertexFinset, card_vertexFinset] at counted
    exact counted
  set support := object.vertexFinset.erase tight with supportDef
  have supportCard : support.card + 1 = object.vertexCount := by
    rw [supportDef, Finset.card_erase_add_one (object.mem_vertexFinset tight),
      card_vertexFinset]
  have degenerate : ∀ inner ⊆ support, inner.Nonempty →
      ∃ vertex ∈ inner, object.localDegree inner vertex ≤ bound := by
    rintro inner subset ⟨witness, inside⟩
    have counted : inner.card ≤ support.card := Finset.card_le_card subset
    have strict : inner.card < object.vertexCount := by omega
    have failure :=
      noProperBaseline (ProperSubgraph.ofInducedSupport object inner strict)
    have nonempty : Nonempty (object.induce inner).Vertex := ⟨⟨witness, inside⟩⟩
    letI : FinEnum (object.induce inner).Vertex := (object.induce inner).vertices
    obtain ⟨minimal, attains⟩ :=
      (object.induce inner).graph.exists_minimal_degree_vertex
    refine ⟨minimal.1, minimal.2, ?_⟩
    have degreeEq : object.localDegree inner minimal.1 =
        (object.induce inner).minDegree := by
      rw [← object.degree_induce_eq_localDegree inner minimal]
      exact attains.symm
    have small : ¬ (threshold ≤ (object.induce inner).minDegree) := failure
    omega
  have large : bound + 1 ≤ support.card := by
    rw [atBaseline, thresholdEq] at room
    omega
  have degeneracy :=
    card_localIncidences_le_of_degenerate (object := object) bound support
      degenerate large
  have deletion := object.card_localIncidences_erase object.vertexFinset
    (object.mem_vertexFinset tight)
  rw [card_localIncidences_vertexFinset, localDegree_vertexFinset, atBaseline,
    ← supportDef] at deletion
  have expand : 2 * bound * support.card + 2 * bound =
      2 * bound * object.vertexCount := by
    rw [← supportCard]; ring
  have sharp : 6 ≤ bound * (bound + 1) :=
    calc (6 : Nat) = 2 * 3 := by norm_num
      _ ≤ bound * (bound + 1) := Nat.mul_le_mul (by omega) (by omega)
  have doubled : 2 * bound * object.vertexCount =
      2 * (bound * object.vertexCount) := by ring
  obtain ⟨cost, costDef⟩ : ∃ cost, bound * (bound + 1) = cost := ⟨_, rfl⟩
  obtain ⟨inner, innerDef⟩ : ∃ inner, 2 * bound * support.card = inner := ⟨_, rfl⟩
  obtain ⟨whole, wholeDef⟩ :
      ∃ whole, bound * object.vertexCount = whole := ⟨_, rfl⟩
  rw [costDef] at degeneracy sharp
  rw [innerDef] at degeneracy expand
  rw [wholeDef] at doubled
  rw [doubled] at expand
  rw [thresholdEq] at deletion
  rw [wholeDef]
  omega

/-! ## The two readings the branch spends -/

/-- A positive edge count exhibits an oriented edge, and with it a vertex. -/
theorem exists_dart_of_edgeCount_pos (object : FiniteObject.{u})
    (positive : 0 < object.edgeCount) : Nonempty object.graph.Dart := by
  letI : FinEnum object.Vertex := object.vertices
  obtain ⟨edge, member⟩ : object.graph.edgeFinset.Nonempty :=
    Finset.card_pos.1 positive
  rw [SimpleGraph.mem_edgeFinset] at member
  revert member
  induction edge using Sym2.ind with
  | _ left right => exact fun adjacent => ⟨⟨(left, right), adjacent⟩⟩

/-- A positive degree surplus is a positive edge count: `2m > δn ≥ 0`. -/
theorem edgeCount_pos_of_degreeSurplus_pos (object : FiniteObject.{u})
    {threshold : Nat} (positive : 0 < object.degreeSurplus threshold) :
    0 < object.edgeCount := by
  have surplus : object.degreeSurplus threshold =
      2 * object.edgeCount - threshold * object.vertexCount := rfl
  obtain ⟨cover, coverDef⟩ :
      ∃ cover, threshold * object.vertexCount = cover := ⟨_, rfl⟩
  rw [coverDef] at surplus
  omega

/-- Positive surplus exhibits a vertex, hence the order used by the
square-root closure is positive. -/
theorem vertexCount_pos_of_degreeSurplus_pos (object : FiniteObject.{u})
    {threshold : Nat} (positive : 0 < object.degreeSurplus threshold) :
    0 < object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  let vertex : object.Vertex :=
    (object.exists_dart_of_edgeCount_pos
      (object.edgeCount_pos_of_degreeSurplus_pos positive)).some.fst
  change 0 < object.vertices.card
  exact FinEnum.card_pos_iff.mpr ⟨vertex⟩

/-- **`lem:sparse-upper-envelope` as the branch reads it.**

The tight endpoint is not assumed: the branch's own positive surplus exhibits an
edge, and `lem:deletion-critical` puts one of its two ends exactly at the
baseline. -/
theorem edgeCount_add_two_le (object : FiniteObject.{u}) {threshold : Nat}
    (three : 3 ≤ threshold)
    (noProperBaseline : ∀ subgraph : ProperSubgraph object,
      ¬ MinimumDegreeAtLeast threshold subgraph.value)
    (tightEndpoint : ∀ dart : object.graph.Dart,
      object.degree dart.fst = threshold ∨ object.degree dart.snd = threshold)
    (positive : 0 < object.edgeCount) :
    object.edgeCount + 2 ≤ (threshold - 1) * object.vertexCount := by
  obtain ⟨dart⟩ := object.exists_dart_of_edgeCount_pos positive
  rcases tightEndpoint dart with atBaseline | atBaseline
  · exact object.edgeCount_add_two_le_of_noProperBaseline three noProperBaseline
      atBaseline
  · exact object.edgeCount_add_two_le_of_noProperBaseline three noProperBaseline
      atBaseline

end FiniteObject

end Hypostructure.Graph
