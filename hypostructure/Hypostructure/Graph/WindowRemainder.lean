import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.Target
import Hypostructure.Graph.DeletionCriticality

/-!
# The remainder of a maximal window packing

`sec:remainder` fixes `W = ⋃_{P∈𝒫} V(P)` for a maximal vertex-disjoint family
`𝒫` of induced windows, and `R = G − W`.  It then asserts two things about `R`
which this module proves:

* `R` contains no induced window, "since any such copy would extend `𝒫`";
* no subgraph of `R` has minimum degree at least the baseline -- because such a
  subgraph's induced closure in `G` is still window-free, so the registered
  external law would give it an accepted cycle, and a cycle of an induced
  subgraph is a cycle of `G`.

Both are stated of supports of the ambient object rather than of the packed
subgraph, which is the form the boundary-demand accounting of `[28]`--`[29]`
consumes and which avoids transporting anything through an induced-subgraph
isomorphism.

The window order and the baseline are parameters.  Nothing here knows the
manuscript's values for them.
-/

namespace Hypostructure.Graph

open Hypostructure

universe u

namespace FiniteObject

/-- `W`: the vertices covered by the packing. -/
noncomputable def windowSupport {object : FiniteObject.{u}}
    (packing : Finset (Finset object.Vertex)) : Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact packing.biUnion id

/-- `R = G − W`: the vertices the packing leaves uncovered. -/
noncomputable def remainderSupport (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact Finset.univ \ windowSupport packing

theorem mem_windowSupport {object : FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)} {member : Finset object.Vertex}
    (present : member ∈ packing) {vertex : object.Vertex}
    (inside : vertex ∈ member) : vertex ∈ windowSupport packing := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact Finset.mem_biUnion.mpr ⟨member, present, inside⟩

theorem notMem_windowSupport_of_mem_remainderSupport
    {object : FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}
    {vertex : object.Vertex}
    (inside : vertex ∈ object.remainderSupport packing) :
    vertex ∉ windowSupport packing := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact (Finset.mem_sdiff.mp inside).2

/-- **`sec:remainder`, first assertion.**  No window of the ambient object lies
inside the remainder of a maximal packing.

The manuscript's reason, exactly: such a copy is disjoint from every packed
window, so it would extend the family, contradicting maximality. -/
theorem not_inducesWindow_of_subset_remainderSupport
    (object : FiniteObject.{u}) {order : Nat}
    {packing : Finset (Finset object.Vertex)}
    (maximal : ∀ support : Finset object.Vertex,
      object.InducesWindow order support →
      ∃ member ∈ packing, ¬ Disjoint support member)
    {support : Finset object.Vertex}
    (inside : support ⊆ object.remainderSupport packing) :
    ¬ object.InducesWindow order support := by
  classical
  intro window
  obtain ⟨member, present, meets⟩ := maximal support window
  refine meets (Finset.disjoint_left.mpr fun vertex inSupport inMember => ?_)
  exact notMem_windowSupport_of_mem_remainderSupport (inside inSupport)
    (mem_windowSupport present inMember)

/-- A cycle of an induced subgraph is a cycle of the ambient object.  The
induced embedding is injective, so the certificate transports along it. -/
theorem hasCycleWithLength_of_induce (object : FiniteObject.{u})
    {LengthOK : Nat → Prop} (support : Finset object.Vertex)
    (cycle : HasCycleWithLength LengthOK (object.induce support)) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨certificate⟩ := cycle
  exact ⟨certificate.mapHom (object.induceEmbedding support).toHom
    (object.induceEmbedding support).injective⟩

/-- An induced subgraph of a window-free region is window-free.

If the restriction to `support` contained an induced window, the window's own
vertices would form a support of the ambient object, contained in `support`,
that induces one. -/
theorem inducedPathFree_induce_of_forall
    (object : FiniteObject.{u}) {order : Nat}
    {support : Finset object.Vertex}
    (empty : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ object.InducesWindow order inner) :
    InducedPathFree (object.induce support) order := by
  classical
  rintro ⟨embedding⟩
  letI : FinEnum object.Vertex := object.vertices
  have inject : Function.Injective
      fun index : Fin order => (embedding index).1 := by
    intro left right same
    exact embedding.injective (Subtype.ext same)
  refine empty (Finset.univ.image fun index : Fin order => (embedding index).1)
    (fun vertex member => ?_) ⟨?_, ?_⟩
  · obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp member
    exact (embedding index).2
  · refine ⟨⟨⟨fun index => ⟨(embedding index).1, ?_⟩, ?_⟩, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
    · intro left right same
      exact inject (congrArg Subtype.val same : _ = _)
    · intro left right
      exact embedding.map_adj_iff
  · rw [Finset.card_image_of_injective _ inject, Finset.card_univ,
      Fintype.card_fin]

/-- **`sec:remainder`, second assertion (`def:internal-3-core` is empty).**

No subgraph of the remainder meets the baseline.  The manuscript's proof, with
the cited external law at its own interface: pass to the induced closure, which
only adds edges and stays window-free; the law gives it an accepted cycle; and
that cycle is a cycle of the selected object, which avoids the target. -/
theorem not_baseline_induce_of_subset_remainderSupport
    (object : FiniteObject.{u}) {order threshold : Nat}
    {LengthOK : Nat → Prop}
    {packing : Finset (Finset object.Vertex)}
    (freeForcesTarget : ∀ inner : FiniteObject.{u},
      MinimumDegreeAtLeast threshold inner →
      InducedPathFree inner order →
      HasCycleWithLength LengthOK inner)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (maximal : ∀ support : Finset object.Vertex,
      object.InducesWindow order support →
      ∃ member ∈ packing, ¬ Disjoint support member)
    {support : Finset object.Vertex}
    (inside : support ⊆ object.remainderSupport packing) :
    ¬ MinimumDegreeAtLeast threshold (object.induce support) := by
  intro baseline
  exact avoids (object.hasCycleWithLength_of_induce support
    (freeForcesTarget (object.induce support) baseline
      (object.inducedPathFree_induce_of_forall fun inner contained =>
        object.not_inducesWindow_of_subset_remainderSupport maximal
          (contained.trans inside))))

/-- `|W| = order · p`: the packed windows are pairwise disjoint and each has
exactly the window order many vertices, so the covered support is the packing
size times the order.  This is the manuscript's `|W| = 13p₁₃`, with neither
numeral written. -/
theorem windowSupport_card_eq (object : FiniteObject.{u}) {order : Nat}
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    (windowSupport packing).card = order * packing.card := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  rw [windowSupport, Finset.card_biUnion]
  · have each : ∀ member ∈ packing, (id member).card = order :=
      fun member present => (valid.1 member present).2
    rw [Finset.sum_congr rfl each, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  · intro left leftMember right rightMember distinct
    exact valid.2 left leftMember right rightMember distinct

end FiniteObject

end Hypostructure.Graph
