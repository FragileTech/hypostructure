import Hypostructure.Graph.RemainderEntropy
import Hypostructure.Graph.PackedWindowRealization
import Hypostructure.Graph.SkeletonBudget

/-!
# The remainder class glues into the labelled skeleton class

`def:remainder-entropy` says of `𝒢(R)`: *"Every candidate carries the same
inherited vertex set, so the density comparison is equivalently the comparison
of its net-deficiency numerator with the inherited one … only `|𝒢(R)|` is ever
consumed, which the inherited data already determines."*  The inherited data is
the object's own remainder: its vertex set and its edge count.  A candidate `H`
with that vertex set and edge count therefore *replaces* the object's remainder
inside the object — keep every window, every stub and every edge with an end
outside `R`, and put `H`'s edges inside `R` — without changing the vertex count
or the edge count.  That is an injection of `𝒢(R)` into `𝒢_{n,m}`, the labelled
skeleton class of `lem:skeleton-dominates`, so

  `|𝒢(R)| ≤ C(C(n,2), m) = skeletonBudget`

is a theorem of the glue, with no realization sentence assumed.  This is the
bound the all-cold entropy comparison of node `[54]` needs.
-/

namespace Hypostructure.Graph

open Hypostructure

universe u

namespace FiniteObject

variable (object : FiniteObject.{u})

/-- **`e(G[R])`**: the edges of the object with both ends in `support` — the
inherited edge count of the remainder, the "inherited net-deficiency numerator"
of `def:remainder-entropy`. -/
noncomputable def internalEdgeCount (support : Finset object.Vertex) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact (object.graph.edgeFinset.filter
    fun edge => ∀ vertex ∈ edge, vertex ∈ support).card

/-- The inherited edge count never exceeds the object's edge count. -/
theorem internalEdgeCount_le_edgeCount (support : Finset object.Vertex) :
    object.internalEdgeCount support ≤ object.edgeCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact Finset.card_filter_le _ _

end FiniteObject

namespace RemainderGlue

variable {object : FiniteObject.{u}}

/-- The object's own vertex labelling. -/
noncomputable def vertexLabel (object : FiniteObject.{u}) :
    object.Vertex ≃ Fin object.vertexCount :=
  object.vertices.equiv

/-- The remainder's own labelling. -/
noncomputable def supportLabel (support : Finset object.Vertex) :
    {vertex // vertex ∈ support} ≃ Fin support.card :=
  support.equivFin

/-- A remainder label, read as an object label. -/
noncomputable def embed (support : Finset object.Vertex)
    (label : Fin support.card) : Fin object.vertexCount :=
  vertexLabel object ((supportLabel support).symm label).1

theorem embed_injective (support : Finset object.Vertex) :
    Function.Injective (embed (object := object) support) := by
  intro left right same
  have := (vertexLabel object).injective same
  exact (supportLabel support).symm.injective (Subtype.ext this)

theorem embed_mem (support : Finset object.Vertex) (label : Fin support.card) :
    (vertexLabel object).symm (embed support label) ∈ support := by
  simp [embed]

/-- The outer edges of the object — those with an end outside the remainder —
read as object labels. -/
noncomputable def outerEdges (support : Finset object.Vertex) :
    Finset (Sym2 (Fin object.vertexCount)) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact (object.graph.edgeFinset.filter
    fun edge => ¬ ∀ vertex ∈ edge, vertex ∈ support).map
    ⟨Sym2.map (vertexLabel object), Sym2.map.injective (vertexLabel object).injective⟩

/-- A candidate remainder's edges, read as object labels. -/
noncomputable def innerEdges (support : Finset object.Vertex)
    (candidate : LabelledOn support.card) : Finset (Sym2 (Fin object.vertexCount)) := by
  classical
  exact candidate.graph.edgeFinset.map
    ⟨Sym2.map (embed support), Sym2.map.injective (embed_injective support)⟩

/-- Whether every end of a labelled edge lies in the remainder. -/
def Inside (support : Finset object.Vertex) (edge : Sym2 (Fin object.vertexCount)) : Prop :=
  ∀ label ∈ edge, (vertexLabel object).symm label ∈ support

open scoped Classical in
noncomputable instance instDecidableInside (support : Finset object.Vertex) :
    DecidablePred (Inside (object := object) support) :=
  fun _ => Classical.propDecidable _

theorem not_inside_of_mem_outerEdges (support : Finset object.Vertex)
    {edge : Sym2 (Fin object.vertexCount)} (member : edge ∈ outerEdges support) :
    ¬ Inside support edge := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simp only [outerEdges, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk]
    at member
  obtain ⟨original, ⟨_edge, outside⟩, rfl⟩ := member
  intro inside
  apply outside
  intro vertex vertexMem
  have := inside ((vertexLabel object) vertex) (Sym2.mem_map.2 ⟨vertex, vertexMem, rfl⟩)
  simpa using this

theorem inside_of_mem_innerEdges (support : Finset object.Vertex)
    (candidate : LabelledOn support.card)
    {edge : Sym2 (Fin object.vertexCount)} (member : edge ∈ innerEdges support candidate) :
    Inside support edge := by
  classical
  simp only [innerEdges, Finset.mem_map, Function.Embedding.coeFn_mk] at member
  obtain ⟨original, _edge, rfl⟩ := member
  intro label labelMem
  rw [Sym2.mem_map] at labelMem
  obtain ⟨source, _sourceMem, rfl⟩ := labelMem
  exact embed_mem support source

theorem outer_disjoint_inner (support : Finset object.Vertex)
    (candidate : LabelledOn support.card) :
    Disjoint (outerEdges support) (innerEdges support candidate) := by
  classical
  rw [Finset.disjoint_left]
  intro edge outer inner
  exact not_inside_of_mem_outerEdges support outer
    (inside_of_mem_innerEdges support candidate inner)

theorem not_isDiag_of_mem_outerEdges (support : Finset object.Vertex)
    {edge : Sym2 (Fin object.vertexCount)} (member : edge ∈ outerEdges support) :
    ¬ edge.IsDiag := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simp only [outerEdges, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk]
    at member
  obtain ⟨original, ⟨edgeMem, _⟩, rfl⟩ := member
  rw [Sym2.isDiag_map (vertexLabel object).injective]
  exact object.graph.not_isDiag_of_mem_edgeSet
    ((SimpleGraph.mem_edgeFinset).1 edgeMem)

theorem not_isDiag_of_mem_innerEdges (support : Finset object.Vertex)
    (candidate : LabelledOn support.card)
    {edge : Sym2 (Fin object.vertexCount)} (member : edge ∈ innerEdges support candidate) :
    ¬ edge.IsDiag := by
  classical
  simp only [innerEdges, Finset.mem_map, Function.Embedding.coeFn_mk] at member
  obtain ⟨original, edgeMem, rfl⟩ := member
  rw [Sym2.isDiag_map (embed_injective support)]
  exact candidate.graph.not_isDiag_of_mem_edgeSet
    ((SimpleGraph.mem_edgeFinset).1 edgeMem)

/-- **The glued labelled graph** `G[R := H]`: the object's outer edges together
with the candidate's edges inside the remainder. -/
noncomputable def glue (support : Finset object.Vertex)
    (candidate : LabelledOn support.card) : LabelledOn object.vertexCount :=
  ⟨SimpleGraph.fromEdgeSet ↑(outerEdges support ∪ innerEdges support candidate)⟩

theorem edgeSet_glue (support : Finset object.Vertex)
    (candidate : LabelledOn support.card) :
    (glue support candidate).graph.edgeSet =
      ↑(outerEdges support ∪ innerEdges support candidate) := by
  classical
  rw [glue, SimpleGraph.edgeSet_fromEdgeSet]
  refine Set.ext fun edge => ⟨fun member => member.1, fun member => ⟨member, ?_⟩⟩
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at member
  rcases member with outer | inner
  · exact not_isDiag_of_mem_outerEdges support outer
  · exact not_isDiag_of_mem_innerEdges support candidate inner

/-- The outer edges number `m − e(G[R])`. -/
theorem card_outerEdges (support : Finset object.Vertex) :
    (outerEdges support).card = object.edgeCount - object.internalEdgeCount support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  rw [outerEdges, Finset.card_map]
  have split := Finset.card_filter_add_card_filter_not
    (s := object.graph.edgeFinset) (p := fun edge => ∀ vertex ∈ edge, vertex ∈ support)
  change _ + (object.graph.edgeFinset.filter
    fun edge => ¬ ∀ vertex ∈ edge, vertex ∈ support).card = _ at split
  unfold FiniteObject.internalEdgeCount FiniteObject.edgeCount
  omega

/-- The candidate's edges number its own edge count. -/
theorem card_innerEdges (support : Finset object.Vertex)
    (candidate : LabelledOn support.card) :
    (innerEdges support candidate).card = Nat.card candidate.graph.edgeSet := by
  classical
  rw [innerEdges, Finset.card_map, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

/-- **The glue preserves the edge count** when the candidate carries the
inherited edge count. -/
theorem card_edgeSet_glue (support : Finset object.Vertex)
    (candidate : LabelledOn support.card)
    (inherited : Nat.card candidate.graph.edgeSet = object.internalEdgeCount support) :
    Nat.card (glue support candidate).graph.edgeSet = object.edgeCount := by
  classical
  rw [edgeSet_glue]
  simp only [Finset.coe_sort_coe, Nat.card_eq_finsetCard]
  rw [Finset.card_union_of_disjoint (outer_disjoint_inner support candidate),
    card_outerEdges, card_innerEdges, inherited]
  have := object.internalEdgeCount_le_edgeCount support
  omega

/-- The candidate is recovered from the glue: its edges are exactly the glued
edges inside the remainder. -/
theorem innerEdges_eq_filter (support : Finset object.Vertex)
    (candidate : LabelledOn support.card) :
    innerEdges support candidate =
      (outerEdges support ∪ innerEdges support candidate).filter (Inside support) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · intro inner
    exact ⟨Or.inr inner, inside_of_mem_innerEdges support candidate inner⟩
  · rintro ⟨outer | inner, inside⟩
    · exact absurd inside (not_inside_of_mem_outerEdges support outer)
    · exact inner

theorem glue_injective (support : Finset object.Vertex) :
    Function.Injective (glue (object := object) support) := by
  classical
  intro left right same
  have edges : outerEdges support ∪ innerEdges support left =
      outerEdges support ∪ innerEdges support right := by
    have leftSet := edgeSet_glue support left
    have rightSet := edgeSet_glue support right
    rw [same, rightSet] at leftSet
    exact Finset.coe_injective leftSet.symm
  have inner : innerEdges support left = innerEdges support right := by
    rw [innerEdges_eq_filter support left, innerEdges_eq_filter support right, edges]
  have finsets : left.graph.edgeFinset = right.graph.edgeFinset := by
    unfold innerEdges at inner
    exact Finset.map_injective _ inner
  exact LabelledOn.ext (SimpleGraph.edgeFinset_inj.1 finsets)

/-- **`|𝒢(R)| ≤ |𝒢_{n,m}|`**: the remainder class of the object's own remainder,
at the inherited edge count, glues injectively into the labelled skeleton class
of the object's order and size. -/
theorem remainderStateCount_le_skeletonBudget (order threshold deficiencyCap : Nat)
    (support : Finset object.Vertex) :
    remainderStateCount order threshold deficiencyCap
        (object.internalEdgeCount support) support.card ≤
      skeletonBudget object := by
  classical
  unfold remainderStateCount skeletonBudget
  refine le_trans (Nat.card_le_card_of_injective
    (fun candidate : RemainderClass order threshold deficiencyCap
        (object.internalEdgeCount support) support.card =>
      (⟨glue support candidate.val, card_edgeSet_glue support candidate.val
        candidate.property.2.2.2⟩ :
        PackedWindowRealization.Skeleton object.vertexCount object.edgeCount)) ?_)
    (le_of_eq (PackedWindowRealization.card_skeleton object.vertexCount object.edgeCount))
  intro left right same
  exact Subtype.ext (glue_injective support (congrArg Subtype.val same))

end RemainderGlue

end Hypostructure.Graph
