import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.TargetDefectStructure
import Hypostructure.Graph.GluedCycleSides
import Hypostructure.Graph.Contraction
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.Progress
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Core.DyadicLength
import Hypostructure.Graph.AddedEdgeClosure
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.CanonicalSupportSelection

/-!
# Glued readings of a support: maps into the ambient object, sub-contexts,
# cycle sub-contexts, boundary shapes

Let `Z` be a vertex support of a finite object `G`, `∂Z` its cut boundary and
`ret_X` the piece of `Z` that keeps only the edges with both ends in `X`.

* `glue (ret_X) (G − Z)` and `ret_X` embed injectively into `G`
  (`retainedGlueHom`, `readingHom`), so both inherit every cycle obstruction of
  `G`.
* A `∂Z`-context realized inside `G − Z` (`RealizedIn`) gives an injective map
  of every gluing into `G` (`realizedGlueHom`).
* Sub-contexts (`subContext`) keep negativity; the O-part of one cycle
  (`cycleContext`) keeps that cycle and has internal degrees at most two.
* Degree bookkeeping of gluings (context-internal and piece-internal
  vertices), the two-retained-label crossing of a mixed cycle, the shape of a
  support with one boundary vertex, and the two-boundary separation.

Every statement is about an arbitrary finite object; nothing here knows a
presentation, a ledger, or a manuscript.
-/

namespace Hypostructure.Graph.GluedReadings

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section Maps

variable {object : Graph.FiniteObject.{u}}

/-- The decoding of `glue (retainedPiece Z X) (outside Z)` into G. -/
noncomputable def retainedGlueHom (Z X : Finset object.Vertex) :
    (glue (SupportAtom.retainedPiece object Z X)
        (SupportAtom.outside object Z)).graph →g object.graph where
  toFun := fun v => match v with
    | .inl b => b.1
    | .inr (.inl i) => i.1
    | .inr (.inr o) => o.1
  map_rel' := by
    intro a b h
    rcases (glueGraph_adj_iff _ _ a b).mp h with
      ⟨p, q, adj, rfl, rfl⟩ | ⟨p, q, adj, rfl, rfl⟩
    · rcases p with p | p <;> rcases q with q | q <;> exact adj.1
    · rcases p with p | p <;> rcases q with q | q <;> exact adj

theorem retainedGlueHom_injective (Z X : Finset object.Vertex) :
    Function.Injective (retainedGlueHom (object := object) Z X) := by
  intro a b h
  have bZ : ∀ x : SupportAtom.BoundaryVertex object Z, x.1 ∈ Z := fun x =>
    ((SupportAtom.mem_cutBoundary_iff object Z x.1).1 x.2).1
  rcases a with a | a | a <;> rcases b with b | b | b
  · have h' : a.1 = b.1 := h
    exact congrArg Sum.inl (Subtype.ext h')
  · have h' : a.1 = b.1 := h
    exact (b.2.2 (by rw [← h']; exact a.2)).elim
  · have h' : a.1 = b.1 := h
    exact (b.2 (by rw [← h']; exact bZ a)).elim
  · have h' : a.1 = b.1 := h
    exact (a.2.2 (by rw [h']; exact b.2)).elim
  · have h' : a.1 = b.1 := h
    exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h')
  · have h' : a.1 = b.1 := h
    exact (b.2 (by rw [← h']; exact a.2.1)).elim
  · have h' : a.1 = b.1 := h
    exact (a.2 (by rw [h']; exact bZ b)).elim
  · have h' : a.1 = b.1 := h
    exact (a.2 (by rw [h']; exact b.2.1)).elim
  · have h' : a.1 = b.1 := h
    exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h')


/-- The piece of a reading embeds in G. -/
noncomputable def readingHom (Z X : Finset object.Vertex) :
    (SupportAtom.retainedPiece object Z X).pack.graph →g object.graph where
  toFun := SupportAtom.pieceDecode object Z
  map_rel' := fun h => h.1

theorem readingHom_injective (Z X : Finset object.Vertex) :
    Function.Injective (readingHom (object := object) Z X) := by
  intro x y h
  rcases x with a | a <;> rcases y with b | b <;>
    simp [readingHom, SupportAtom.pieceDecode] at h
  · exact congrArg Sum.inl h
  · exact absurd (h ▸ a.2) b.2.2
  · exact absurd (h ▸ b.2) a.2.2
  · exact congrArg Sum.inr (Subtype.ext h)


/-- `|∂Z| ≥ 1 ⇒ Z ⊊ V(G)`: a boundary vertex has a neighbour outside `Z`. -/
theorem proper_of_boundary {Z : Finset object.Vertex}
    (nonempty : 1 ≤ (SupportAtom.cutBoundary object Z).card) :
    ∃ vertex, vertex ∉ Z := by
  obtain ⟨b, hb⟩ := Finset.card_pos.mp nonempty
  obtain ⟨_, x, _, hx⟩ := (SupportAtom.mem_cutBoundary_iff object Z b).1 hb
  exact ⟨x, hx⟩


/-! ### Route 1: a context realized inside G -/

/-- A `∂Z`-context realized inside `G − Z`: a label-fixing injective graph map
into G's actual outside context. -/
structure RealizedIn {Z : Finset object.Vertex}
    (O : OutsideContext (SupportAtom.boundary object Z)) where
  map : O.graph →g (SupportAtom.outside object Z).graph
  injective : Function.Injective map
  fixes : ∀ b, map (.inl b) = .inl b

theorem outsideDecode_injective (Z : Finset object.Vertex) :
    Function.Injective (SupportAtom.outsideDecode object Z) := by
  have bZ : ∀ x : SupportAtom.BoundaryVertex object Z, x.1 ∈ Z := fun x =>
    ((SupportAtom.mem_cutBoundary_iff object Z x.1).1 x.2).1
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [SupportAtom.outsideDecode] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact (b.2 (h ▸ bZ a)).elim
  · exact (a.2 (h ▸ bZ b)).elim
  · exact congrArg Sum.inr (Subtype.ext h)

theorem RealizedIn.map_internal {Z : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)} (r : RealizedIn O)
    (o : O.Internal) : SupportAtom.outsideDecode object Z (r.map (.inr o)) ∉ Z := by
  cases h : r.map (.inr o) with
  | inl b =>
    have := r.injective (h.trans (r.fixes b).symm)
    cases this
  | inr o' => exact o'.2

/-- Vertex decoding of `glue (ret_X) O` into G through a realization. -/
def realizedDecode {Z : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)} (r : RealizedIn O)
    (X : Finset object.Vertex) :
    GluedVertex (SupportAtom.retainedPiece object Z X) O → object.Vertex
  | .inl b => b.1
  | .inr (.inl i) => i.1
  | .inr (.inr o) => SupportAtom.outsideDecode object Z (r.map (.inr o))

theorem realizedDecode_context {Z : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)} (r : RealizedIn O)
    (X : Finset object.Vertex) (p : (SupportAtom.boundary object Z).Vertex ⊕ O.Internal) :
    realizedDecode r X (contextEmbedding (SupportAtom.retainedPiece object Z X) O p) =
      SupportAtom.outsideDecode object Z (r.map p) := by
  rcases p with p | p
  · change p.1 = SupportAtom.outsideDecode object Z (r.map (.inl p))
    rw [r.fixes]; rfl
  · rfl

/-- The realization of `glue (ret_X) O` inside G. -/
noncomputable def realizedGlueHom {Z : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)} (r : RealizedIn O)
    (X : Finset object.Vertex) :
    (glue (SupportAtom.retainedPiece object Z X) O).graph →g object.graph where
  toFun := realizedDecode r X
  map_rel' := by
    intro a b h
    rcases (glueGraph_adj_iff _ _ a b).mp h with
      ⟨p, q, adj, rfl, rfl⟩ | ⟨p, q, adj, rfl, rfl⟩
    · rcases p with p | p <;> rcases q with q | q <;> exact adj.1
    · have hadj := r.map.map_rel' adj
      show object.graph.Adj (realizedDecode r X _) (realizedDecode r X _)
      rw [realizedDecode_context, realizedDecode_context]
      exact hadj

theorem realizedGlueHom_injective {Z : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)} (r : RealizedIn O)
    (X : Finset object.Vertex) : Function.Injective (realizedGlueHom r X) := by
  have bZ : ∀ x : SupportAtom.BoundaryVertex object Z, x.1 ∈ Z := fun x =>
    ((SupportAtom.mem_cutBoundary_iff object Z x.1).1 x.2).1
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b
  · have h' : a.1 = b.1 := h
    exact congrArg Sum.inl (Subtype.ext h')
  · have h' : a.1 = b.1 := h
    exact (b.2.2 (by rw [← h']; exact a.2)).elim
  · have h' : a.1 = SupportAtom.outsideDecode object Z (r.map (.inr b)) := h
    exact (r.map_internal b (h' ▸ bZ a)).elim
  · have h' : a.1 = b.1 := h
    exact (a.2.2 (by rw [h']; exact b.2)).elim
  · have h' : a.1 = b.1 := h
    exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h')
  · have h' : a.1 = SupportAtom.outsideDecode object Z (r.map (.inr b)) := h
    exact (r.map_internal b (h' ▸ a.2.1)).elim
  · have h' : SupportAtom.outsideDecode object Z (r.map (.inr a)) = b.1 := h
    exact (r.map_internal a (h' ▸ bZ b)).elim
  · have h' : SupportAtom.outsideDecode object Z (r.map (.inr a)) = b.1 := h
    exact (r.map_internal a (h' ▸ b.2.1)).elim
  · have h' : SupportAtom.outsideDecode object Z (r.map (.inr a)) =
        SupportAtom.outsideDecode object Z (r.map (.inr b)) := h
    have := r.injective (outsideDecode_injective Z h')
    cases this
    rfl

/-- **Route 1 is closed off at G.**  Under F1.a, every reading of G's piece at
`Z` is negative in every context realized inside `G − Z`. -/
theorem realized_context_negative {LengthOK : Nat → Prop}
    (avoid : ¬ Graph.HasCycleWithLength LengthOK object)
    {Z : Finset object.Vertex} {O : OutsideContext (SupportAtom.boundary object Z)}
    (r : RealizedIn O) (X : Finset object.Vertex) :
    ¬ Graph.HasCycleWithLength LengthOK
      (glue (SupportAtom.retainedPiece object Z X) O) :=
  fun c => avoid (Graph.hasCycleWithLength_of_hom _ (realizedGlueHom_injective r X) c)

/-- `G − Z` itself is realized (identity). -/
noncomputable def RealizedIn.actual (Z : Finset object.Vertex) :
    RealizedIn (SupportAtom.outside object Z) where
  map := SimpleGraph.Hom.id
  injective := fun _ _ h => h
  fixes := fun _ => rfl

/-! ### Route 3: minimality on objects built from `O` -/

/-- A sub-context of `O`: same internal carrier, fewer edges. -/
noncomputable def subContext {boundary : Boundary.{u}} (O : OutsideContext boundary)
    (g : SimpleGraph (boundary.Vertex ⊕ O.Internal)) : OutsideContext boundary :=
  { O with graph := g, decideAdj := Classical.decRel _ }

noncomputable def subContextHom {boundary : Boundary.{u}} (P : BoundaryPiece boundary)
    (O : OutsideContext boundary) (g : SimpleGraph (boundary.Vertex ⊕ O.Internal))
    (le : g ≤ O.graph) :
    (glue P (subContext O g)).graph →g (glue P O).graph where
  toFun := id
  map_rel' := by
    intro a b h
    change (glueGraph P O).Adj a b
    rcases (glueGraph_adj_iff P (subContext O g) a b).mp h with own | ⟨p, q, adj, hp, hq⟩
    · exact (glueGraph_adj_iff P O a b).mpr (Or.inl own)
    · exact (glueGraph_adj_iff P O a b).mpr (Or.inr ⟨p, q, le adj, by cases p <;> exact hp, by cases q <;> exact hq⟩)

/-- Negative stays negative on every sub-context. -/
theorem subContext_negative {boundary : Boundary.{u}} {LengthOK : Nat → Prop}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary)
    (neg : ¬ Graph.HasCycleWithLength LengthOK (glue P O))
    (g : SimpleGraph (boundary.Vertex ⊕ O.Internal)) (le : g ≤ O.graph) :
    ¬ Graph.HasCycleWithLength LengthOK (glue P (subContext O g)) :=
  fun c => neg (Graph.hasCycleWithLength_of_hom (subContextHom P O g le)
    (fun _ _ h => h) c)


/-- A context-internal vertex has no more neighbours in the gluing than in the
context. -/
theorem glue_context_degree_le {boundary : Boundary.{u}}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary) (o : O.Internal) :
    (glue P O).degree (.inr (.inr o)) ≤ O.pack.degree (.inr o) := by
  rw [Graph.FiniteObject.degree_eq_ncard_neighborSet,
    Graph.FiniteObject.degree_eq_ncard_neighborSet]
  have sub : (glue P O).graph.neighborSet (.inr (.inr o)) ⊆
      contextEmbedding P O '' O.graph.neighborSet (.inr o) := by
    intro x hx
    rcases (glueGraph_adj_iff P O _ x).mp hx with
      ⟨p, q, _, hp, _⟩ | ⟨p, q, adj, hp, hq⟩
    · rcases p with p | p <;> cases hp
    · have : p = .inr o := by
        rcases p with p | p
        · cases hp
        · cases hp; rfl
      subst this
      exact ⟨q, adj, hq⟩
  haveI : Finite (boundary.Vertex ⊕ O.Internal) := by
    letI := boundary.vertices; letI := O.internalVertices; infer_instance
  haveI : Finite (GluedVertex P O) := by
    letI := boundary.vertices; letI := O.internalVertices; letI := P.internalVertices
    infer_instance
  calc ((glue P O).graph.neighborSet (.inr (.inr o))).ncard
      ≤ (contextEmbedding P O '' O.graph.neighborSet (.inr o)).ncard :=
        Set.ncard_le_ncard sub (Set.Finite.image _ (Set.toFinite _))
    _ ≤ (O.graph.neighborSet (.inr o)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = _ := rfl

/-- Baseline of a gluing forces baseline at every context-internal vertex. -/
theorem baseline_glue_context {boundary : Boundary.{u}} {k : Nat}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary)
    (baseline : Graph.MinimumDegreeAtLeast k (glue P O)) (o : O.Internal) :
    k ≤ O.pack.degree (.inr o) :=
  (baseline.trans ((glue P O).minDegree_le_degree _)).trans
    (glue_context_degree_le P O o)

/-! ### Route 3, refined: the cycle sub-context of a positive cycle -/

/-- **The O-part of one cycle** of `glue P O`: the sub-context keeping exactly
the context-owned edges the cycle uses. -/
noncomputable def cycleContext {boundary : Boundary.{u}} {LengthOK : Nat → Prop}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary)
    (c : Graph.CycleCertificate (glue P O) LengthOK) : OutsideContext boundary :=
  subContext O (O.graph ⊓
    SimpleGraph.comap (contextEmbedding P O) c.walk.toSubgraph.spanningCoe)

theorem cycleContext_le {boundary : Boundary.{u}} {LengthOK : Nat → Prop}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary)
    (c : Graph.CycleCertificate (glue P O) LengthOK) :
    (O.graph ⊓ SimpleGraph.comap (contextEmbedding P O) c.walk.toSubgraph.spanningCoe)
      ≤ O.graph := inf_le_left

/-- **The cycle survives on its own O-part**: `glue P (cycleContext c)` still
carries an accepted cycle (the same walk, same length). -/
theorem cycleContext_positive {boundary : Boundary.{u}} {LengthOK : Nat → Prop}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary)
    (c : Graph.CycleCertificate (glue P O) LengthOK) :
    Graph.HasCycleWithLength LengthOK (glue P (cycleContext P O c)) := by
  have hedges : ∀ e, e ∈ c.walk.edges →
      e ∈ (glue P (cycleContext P O c)).graph.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have adjG : (glue P O).graph.Adj x y := c.walk.adj_of_mem_edges he
      have inSub : c.walk.toSubgraph.Adj x y := by
        rw [← SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Walk.mem_edges_toSubgraph]
        exact he
      change (glueGraph P (cycleContext P O c)).Adj x y
      rcases (glueGraph_adj_iff P O x y).mp adjG with own | ⟨p, q, adj, hp, hq⟩
      · exact (glueGraph_adj_iff P (cycleContext P O c) x y).mpr (Or.inl
          (by obtain ⟨a, b, h1, h2, h3⟩ := own
              exact ⟨a, b, h1, by cases a <;> exact h2, by cases b <;> exact h3⟩))
      · refine (glueGraph_adj_iff P (cycleContext P O c) x y).mpr (Or.inr
          ⟨p, q, ⟨adj, ?_⟩, by cases p <;> exact hp, by cases q <;> exact hq⟩)
        change c.walk.toSubgraph.spanningCoe.Adj (contextEmbedding P O p)
          (contextEmbedding P O q)
        rw [hp, hq]
        exact inSub
  exact ⟨⟨c.vertex, c.walk.transfer _ hedges, c.isCycle.transfer hedges,
    by erw [SimpleGraph.Walk.length_transfer]; exact c.length_ok⟩⟩

/-- Every vertex has at most two neighbours on a cycle's subgraph. -/
theorem cycle_toSubgraph_ncard_le_two {V : Type*} {H : SimpleGraph V} {u : V}
    {p : H.Walk u u} (hp : p.IsCycle) (v : V) :
    (p.toSubgraph.neighborSet v).ncard ≤ 2 := by
  by_cases hv : v ∈ p.support
  · exact (hp.ncard_neighborSet_toSubgraph_eq_two hv).le
  · have : p.toSubgraph.neighborSet v = ∅ := by
      ext w
      simp only [SimpleGraph.Subgraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro adj
      exact hv (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert adj))
    rw [this, Set.ncard_empty]; omega

/-- **Every internal vertex of the cycle's O-part has degree ≤ 2.** -/
theorem cycleContext_degree_le_two {boundary : Boundary.{u}} {LengthOK : Nat → Prop}
    (P : BoundaryPiece boundary) (O : OutsideContext boundary)
    (c : Graph.CycleCertificate (glue P O) LengthOK) (o : O.Internal) :
    (cycleContext P O c).pack.degree (.inr o) ≤ 2 := by
  rw [Graph.FiniteObject.degree_eq_ncard_neighborSet]
  haveI : Finite (boundary.Vertex ⊕ O.Internal) := by
    letI := boundary.vertices; letI := O.internalVertices; infer_instance
  haveI : Finite (GluedVertex P O) := by
    letI := boundary.vertices; letI := O.internalVertices; letI := P.internalVertices
    infer_instance
  have sub : contextEmbedding P O ''
      ((cycleContext P O c).pack.graph.neighborSet (.inr o)) ⊆
      c.walk.toSubgraph.neighborSet (contextEmbedding P O (.inr o)) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hq.2
  calc ((cycleContext P O c).pack.graph.neighborSet (.inr o)).ncard
      = (contextEmbedding P O ''
          ((cycleContext P O c).pack.graph.neighborSet (.inr o))).ncard :=
        (Set.ncard_image_of_injective _ (contextEmbedding P O).injective).symm
    _ ≤ (c.walk.toSubgraph.neighborSet (contextEmbedding P O (.inr o))).ncard :=
        Set.ncard_le_ncard sub (Set.toFinite _)
    _ ≤ 2 := cycle_toSubgraph_ncard_le_two c.isCycle _

/-- Hence a baseline (`δ ≥ 3`) gluing against a cycle's O-part forces the
context to have no internal vertex (chords between labels only). -/
theorem cycleContext_baseline_chordOnly {boundary : Boundary.{u}} {LengthOK : Nat → Prop}
    (P Q : BoundaryPiece boundary) (O : OutsideContext boundary)
    (c : Graph.CycleCertificate (glue P O) LengthOK) {k : Nat} (three : 3 ≤ k)
    (baseline : Graph.MinimumDegreeAtLeast k (glue Q (cycleContext P O c))) :
    IsEmpty O.Internal :=
  ⟨fun o => by
    have h1 := baseline_glue_context Q (cycleContext P O c) baseline o
    have h2 := cycleContext_degree_le_two P O c o
    omega⟩

/-- **Chord-only contexts give lex-smaller gluings of G's readings**: with no
context-internal vertex and some vertex of G outside `Z`, `glue (ret_X) O` has
fewer vertices than G. -/
theorem chordOnly_retainedGlue_smaller {Z X : Finset object.Vertex}
    (O : OutsideContext (SupportAtom.boundary object Z)) (empty : IsEmpty O.Internal)
    (proper : ∃ v, v ∉ Z) :
    (glue (SupportAtom.retainedPiece object Z X) O).LexicographicallySmaller object := by
  classical
  apply Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt
  obtain ⟨v, hv⟩ := proper
  have bZ : ∀ x : SupportAtom.BoundaryVertex object Z, x.1 ∈ Z := fun x =>
    ((SupportAtom.mem_cutBoundary_iff object Z x.1).1 x.2).1
  let f : (glue (SupportAtom.retainedPiece object Z X) O).Vertex → object.Vertex :=
    fun x => match x with
      | .inl b => b.1
      | .inr (.inl i) => i.1
      | .inr (.inr o) => isEmptyElim o
  have fZ : ∀ x, f x ∈ Z := by
    intro x
    rcases x with b | i | o
    · exact bZ b
    · exact i.2.1
    · exact isEmptyElim o
  have finj : Function.Injective f := by
    intro a b h
    rcases a with a | a | a <;> rcases b with b | b | b
    · have h' : a.1 = b.1 := h
      exact congrArg Sum.inl (Subtype.ext h')
    · have h' : a.1 = b.1 := h
      exact (b.2.2 (by rw [← h']; exact a.2)).elim
    · exact isEmptyElim b
    · have h' : a.1 = b.1 := h
      exact (a.2.2 (by rw [h']; exact b.2)).elim
    · have h' : a.1 = b.1 := h
      exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h')
    · exact isEmptyElim b
    · exact isEmptyElim a
    · exact isEmptyElim a
    · exact isEmptyElim a
  letI := (glue (SupportAtom.retainedPiece object Z X) O).vertices
  letI := object.vertices
  unfold Graph.FiniteObject.vertexCount
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_lt_of_injective_not_surjective f finj
    (fun surj => by obtain ⟨x, hx⟩ := surj v; exact hv (hx ▸ fZ x))


/-- Every reading's gluing with `G − Z` is cycle-free when `G` is. -/
theorem retainedGlue_avoids {LengthOK : Nat → Prop}
    (avoid : ¬ Graph.HasCycleWithLength LengthOK object)
    (Z X : Finset object.Vertex) :
    ¬ Graph.HasCycleWithLength LengthOK
      (glue (SupportAtom.retainedPiece object Z X) (SupportAtom.outside object Z)) :=
  fun c => avoid (Graph.hasCycleWithLength_of_hom _ (retainedGlueHom_injective Z X) c)

/-- Every reading's piece is cycle-free when `G` is. -/
theorem retainedPiece_avoids {LengthOK : Nat → Prop}
    (avoid : ¬ Graph.HasCycleWithLength LengthOK object)
    (Z X : Finset object.Vertex) :
    ¬ Graph.HasCycleWithLength LengthOK (SupportAtom.retainedPiece object Z X).pack :=
  fun h => avoid (Graph.hasCycleWithLength_of_hom _ (readingHom_injective Z X) h)

/-- Minimality in the abstract: a gluing negative at `O` is negative at every
sub-context, so if every lexicographically smaller baseline object hits the
target, no sub-context gluing is a lexicographically smaller baseline object. -/
theorem negative_subContext_not_smaller_baseline {Baseline : Graph.FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop}
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Graph.HasCycleWithLength LengthOK H)
    {boundary : Boundary.{u}} (N : BoundaryPiece boundary) (O : OutsideContext boundary)
    (neg : ¬ Graph.HasCycleWithLength LengthOK (glue N O))
    (g : SimpleGraph (boundary.Vertex ⊕ O.Internal)) (le : g ≤ O.graph) :
    ¬ (Baseline (glue N (subContext O g)) ∧
        (glue N (subContext O g)).LexicographicallySmaller object) := by
  rintro ⟨baseline, smaller⟩
  exact subContext_negative N O neg g le (minimal _ smaller baseline)

/-- A separation at `O` together with a cycle-free ambient object gives the
bound target-defect geometry at the same `O` (whichever reading is positive). -/
theorem boundTargetDefectGeometryAt_of_separated {LengthOK : Nat → Prop}
    {Z : Finset object.Vertex}
    {left right : BoundaryPiece (SupportAtom.boundary object Z)}
    {O : OutsideContext (SupportAtom.boundary object Z)}
    (different : ¬ (Graph.HasCycleWithLength LengthOK (glue left O) ↔
      Graph.HasCycleWithLength LengthOK (glue right O)))
    (avoid : ¬ Graph.HasCycleWithLength LengthOK object) :
    Hypostructure.Graph.BoundTargetDefectGeometryAt object Z LengthOK left right O := by
  classical
  have mk : ∀ (P N : BoundaryPiece (SupportAtom.boundary object Z)),
      Graph.HasCycleWithLength LengthOK (glue P O) →
      ¬ Graph.HasCycleWithLength LengthOK (glue N O) →
      DefectGeometry.PositiveStructure object Z LengthOK P N O := by
    intro P N pos neg
    have contextFree : ¬ Graph.HasCycleWithLength LengthOK
        (OutsideContext.pack O) := fun yes =>
      neg (Graph.hasCycleWithLength_of_hom (Graph.contextHom N O)
        (Graph.contextEmbedding N O).injective yes)
    have negativeFree : ¬ Graph.HasCycleWithLength LengthOK
        (BoundaryPiece.pack N) := fun yes =>
      neg (Graph.hasCycleWithLength_of_hom (Graph.pieceHom N O)
        (Graph.pieceEmbedding N O).injective yes)
    refine ⟨pos, neg, contextFree, negativeFree, ?_, ?_, ?_, ?_⟩
    · intro c
      exact DefectGeometry.pieceExclusive c contextFree
    · intro c emptyBoundary
      exact DefectGeometry.empty_local c
        (DefectGeometry.pieceExclusive c contextFree) emptyBoundary
    · intro c realization
      have pieceFree : ¬ Graph.HasCycleWithLength LengthOK
          (BoundaryPiece.pack P) := fun yes =>
        avoid (Graph.hasCycleWithLength_of_hom realization.hom
          realization.injective yes)
      exact ⟨fun h => pieceFree (DefectGeometry.local_target c h),
        DefectGeometry.realized_mixed c
          (DefectGeometry.pieceExclusive c contextFree) pieceFree⟩
    · intro c
      rcases DefectGeometry.local_or_mixed c with localized | mixed
      · exact Or.inl localized
      · exact Or.inr ⟨mixed, DefectGeometry.twoLabels_of_exclusive c
          (DefectGeometry.pieceExclusive c contextFree) mixed⟩
  refine ⟨different, ?_⟩
  by_cases pl : Graph.HasCycleWithLength LengthOK (glue left O)
  · exact Or.inl (mk left right pl (fun pr => different ⟨fun _ => pr, fun _ => pl⟩))
  · have pr : Graph.HasCycleWithLength LengthOK (glue right O) := by
      by_contra pr
      exact different ⟨fun h => (pl h).elim, fun h => (pr h).elim⟩
    exact Or.inr (mk right left pr pl)

/-- A bound target-defect geometry between two readings of a cycle-free object
crosses the cut boundary at two distinct vertices: `2 ≤ |∂Z|`. -/
theorem two_le_cutBoundary_of_geometryAt {LengthOK : Nat → Prop} {Z A B : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)}
    (avoid : ¬ Graph.HasCycleWithLength LengthOK object)
    (geometry : Hypostructure.Graph.BoundTargetDefectGeometryAt object Z LengthOK
      (SupportAtom.retainedPiece object Z A) (SupportAtom.retainedPiece object Z B) O) :
    2 ≤ (SupportAtom.cutBoundary object Z).card := by
  classical
  obtain ⟨_, pos⟩ := geometry
  have go : ∀ (P N : BoundaryPiece (SupportAtom.boundary object Z)),
      (¬ Graph.HasCycleWithLength LengthOK P.pack) →
      DefectGeometry.PositiveStructure object Z LengthOK P N O →
      2 ≤ (SupportAtom.cutBoundary object Z).card := by
    intro P N free ps
    obtain ⟨c⟩ := ps.positive
    rcases ps.external c with loc | ⟨_, a, b, ne, _, _⟩
    · exact (free (DefectGeometry.local_target c loc)).elim
    · have sub : ({a.1, b.1} : Finset object.Vertex) ⊆ SupportAtom.cutBoundary object Z := by
        intro v hv
        simp at hv
        rcases hv with rfl | rfl
        · exact a.2
        · exact b.2
      have c2 : ({a.1, b.1} : Finset object.Vertex).card = 2 :=
        Finset.card_pair (fun h => ne (Subtype.ext h))
      exact c2 ▸ Finset.card_le_card sub
  rcases pos with ps | ps
  · exact go _ _ (fun h => avoid (Graph.hasCycleWithLength_of_hom _
      (readingHom_injective Z A) h)) ps
  · exact go _ _ (fun h => avoid (Graph.hasCycleWithLength_of_hom _
      (readingHom_injective Z B) h)) ps


open SupportAtom in
/-- Edge-monotonicity of readings on one support: `X ⊆ Y ⇒ ret_X ≤ ret_Y`. -/
theorem retainedPiece_le {Z X Y : Finset object.Vertex} (sub : X ⊆ Y) :
    (retainedPiece object Z X).graph ≤ (retainedPiece object Z Y).graph := by
  intro a b h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at h2 ⊢
  rcases h2 with ⟨ne, hh | hh⟩
  · exact ⟨ne, Or.inl ⟨sub hh.1, sub hh.2⟩⟩
  · exact ⟨ne, Or.inr ⟨sub hh.1, sub hh.2⟩⟩

open SupportAtom in
/-- Monotonicity of the response at every context `O`. -/
theorem glue_retained_mono {Z X Y : Finset object.Vertex} (sub : X ⊆ Y)
    (O : OutsideContext (boundary object Z)) {L : Nat → Prop}
    (cyc : HasCycleWithLength L (glue (retainedPiece object Z X) O)) :
    HasCycleWithLength L (glue (retainedPiece object Z Y) O) := by
  have le : glueGraph (retainedPiece object Z X) O ≤
      glueGraph (retainedPiece object Z Y) O :=
    glueGraph_mono (piece := retainedPiece object Z Y) O
      (retainedPiece object Z X).graph (retainedPiece object Z X).decideAdj
      (retainedPiece_le sub)
  exact hasCycleWithLength_of_hom (left := glue (retainedPiece object Z X) O)
    (right := glue (retainedPiece object Z Y) O) ⟨id, fun h => le h⟩
    Function.injective_id cyc


/-- Degree helpers on packed objects. -/
theorem degree_zero_of_no_adj (H : FiniteObject.{u}) (v : H.Vertex)
    (h : ∀ y, ¬ H.graph.Adj v y) : H.degree v = 0 := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have : H.graph.neighborSet v = ∅ := by
    ext y; simp [SimpleGraph.mem_neighborSet, h y]
  rw [this, Set.ncard_empty]

theorem degree_pos_of_adj (H : FiniteObject.{u}) {v y : H.Vertex}
    (h : H.graph.Adj v y) : 0 < H.degree v := by
  letI : FinEnum H.Vertex := H.vertices
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨y, h⟩


open SupportAtom in
/-- An internal vertex of `Z` outside `X` is ISOLATED in `glue(ret_X, O')` for
EVERY context `O'`: its degree deficit is the full threshold and no context can
repair it. -/
theorem internal_isolated {Z X : Finset object.Vertex}
    (i : PieceInternal object Z) (hi : i.1 ∉ X)
    (O' : OutsideContext (boundary object Z)) :
    (glue (retainedPiece object Z X) O').degree (.inr (.inl i)) = 0 := by
  apply degree_zero_of_no_adj
  intro y hy
  rcases (glueGraph_adj_iff _ _ _ _).1 hy with
    ⟨pl, pr, adj, el, _⟩ | ⟨cl, cr, _, el, _⟩
  · rcases pl with b | j
    · simp [pieceEmbedding] at el
    · simp [pieceEmbedding] at el
      subst el
      obtain ⟨-, h2⟩ := adj
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at h2
      rcases h2 with ⟨-, hh | hh⟩
      · exact hi hh.1
      · exact hi hh.2
  · rcases cl with b | j <;> simp [contextEmbedding] at el

/-- `δ ≥ k` fails (for `k ≥ 1`) at a graph with a degree-0 vertex. -/
theorem not_minDegree_of_degree_zero {H : FiniteObject.{u}} {k : Nat} (hk : 1 ≤ k)
    (v : H.Vertex) (zero : H.degree v = 0) : ¬ MinimumDegreeAtLeast k H := by
  intro base
  have := H.minDegree_le_degree v
  unfold MinimumDegreeAtLeast at base
  omega


end Maps

section PieceDegrees

/-! ### Generic graph facts (no EG vocabulary) -/

/-- A vertex of a connected support with a second vertex in it has a neighbour
inside the support. -/
theorem exists_adj_in_of_connectedOn (object : FiniteObject.{u}) {Z : Finset object.Vertex}
    (conn : SupportComponents.Connected.ConnectedOn object Z) {s t : object.Vertex}
    (hs : s ∈ Z) (ht : t ∈ Z) (ne : s ≠ t) :
    ∃ v, object.graph.Adj s v ∧ v ∈ Z := by
  obtain ⟨path, -, inZ⟩ := conn.2 hs ht
  cases path with
  | nil => exact (ne rfl).elim
  | cons h p => exact ⟨_, h, inZ _ (by simp)⟩

/-- Encoding of a support vertex as a piece vertex. -/
noncomputable def pieceEncode (object : FiniteObject.{u}) (Z : Finset object.Vertex)
    (v : object.Vertex) (hv : v ∈ Z) :
    (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z := by
  classical
  exact if hb : v ∈ SupportAtom.cutBoundary object Z then .inl ⟨v, hb⟩ else .inr ⟨v, hv, hb⟩

theorem pieceDecode_encode (object : FiniteObject.{u}) (Z : Finset object.Vertex)
    (v : object.Vertex) (hv : v ∈ Z) :
    SupportAtom.pieceDecode object Z (pieceEncode object Z v hv) = v := by
  classical
  unfold pieceEncode
  split <;> rfl

theorem pieceDecode_mem (object : FiniteObject.{u}) (Z : Finset object.Vertex)
    (a : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    SupportAtom.pieceDecode object Z a ∈ Z := by
  rcases a with b | i
  · exact ((SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2).1
  · exact i.2.1

/-- **Strict degree drop under an injective hom that misses an edge.** -/
theorem degree_lt_of_injHom_missing {H K : FiniteObject.{u}} (f : H.graph →g K.graph)
    (inj : Function.Injective f) (x : H.Vertex) (y : K.Vertex)
    (hy : K.graph.Adj (f x) y) (miss : ∀ z, H.graph.Adj x z → f z ≠ y) :
    H.degree x < K.degree (f x) := by
  letI : FinEnum K.Vertex := K.vertices
  rw [FiniteObject.degree_eq_ncard_neighborSet, FiniteObject.degree_eq_ncard_neighborSet,
    ← Set.ncard_image_of_injective _ inj]
  refine Set.ncard_lt_ncard ⟨?_, fun sub => ?_⟩ (Set.toFinite _)
  · rintro _ ⟨z, hz, rfl⟩
    exact f.map_rel hz
  · obtain ⟨z, hz, hzy⟩ := sub hy
    exact miss z hz hzy


end PieceDegrees

/-! ### 9a. Every positive cycle crosses `∂Z` at two vertices of the positive
declared support -/

section PositiveLabels

variable {G : Graph.FiniteObject.{u}} {Z X : Finset G.Vertex}
variable {O : OutsideContext (SupportAtom.boundary G Z)}

/-- An edge of the retained piece has both ends in the retained set. -/
theorem retained_adj_mem
    {p q : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z}
    (adj : (SupportAtom.retainedPiece G Z X).graph.Adj p q) :
    SupportAtom.pieceDecode G Z p ∈ X ∧ SupportAtom.pieceDecode G Z q ∈ X := by
  have h := adj.2
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact ⟨hp, hq⟩
  · exact ⟨hp, hq⟩

/-- **Leaving the piece interior through a retained edge**: a glued walk from a
piece-internal vertex to a vertex that is not piece-internal visits a boundary
label lying in the retained set `X`. -/
theorem exists_retained_label_of_walk :
    ∀ {start finish : GluedVertex (SupportAtom.retainedPiece G Z X) O}
      (walk : (glueGraph (SupportAtom.retainedPiece G Z X) O).Walk start finish),
      (∃ inner : SupportAtom.PieceInternal G Z, start = .inr (.inl inner)) →
      (∀ inner : SupportAtom.PieceInternal G Z, finish ≠ .inr (.inl inner)) →
      ∃ label : (SupportAtom.boundary G Z).Vertex,
        (Sum.inl label : GluedVertex (SupportAtom.retainedPiece G Z X) O) ∈
          walk.support ∧ label.1 ∈ X := by
  intro start finish walk
  induction walk with
  | nil =>
      rintro ⟨inner, rfl⟩ notInner
      exact absurd rfl (notInner inner)
  | @cons a b c adjacent rest ih =>
      rintro ⟨inner, rfl⟩ notInner
      rcases b with label | pieceOrContext
      · -- the step into the label is piece-owned, hence retained
        rcases (glueGraph_adj_iff _ _ _ _).mp adjacent with pieceOwn | contextOwn
        · obtain ⟨pl, pr, adj, _plEq, prEq⟩ := pieceOwn
          have prIs : pr = .inl label := by
            rcases pr with l | i
            · simp [pieceEmbedding] at prEq; rw [prEq]
            · simp [pieceEmbedding] at prEq
          subst prIs
          refine ⟨label, ?_, (retained_adj_mem adj).2⟩
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ rest.start_mem_support
        · exact (GluedCycleSides.not_contextOwns_piece_internal contextOwn).elim
      · rcases pieceOrContext with inner' | context
        · obtain ⟨label, mem, inX⟩ := ih ⟨inner', rfl⟩ notInner
          refine ⟨label, ?_, inX⟩
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ mem
        · exfalso
          rcases (glueGraph_adj_iff _ _ _ _).mp adjacent with pieceOwn | contextOwn
          · obtain ⟨_pl, pr, _adj, _plEq, prEq⟩ := pieceOwn
            rcases pr with l | i <;> simp [pieceEmbedding] at prEq
          · exact GluedCycleSides.not_contextOwns_piece_internal contextOwn

/-- The context-owned endpoints are not piece-internal. -/
theorem contextOwns_not_internal
    {x y : GluedVertex (SupportAtom.retainedPiece G Z X) O}
    (owns : ContextOwns (SupportAtom.retainedPiece G Z X) O x y) :
    (∀ inner : SupportAtom.PieceInternal G Z, x ≠ .inr (.inl inner)) ∧
      (∀ inner : SupportAtom.PieceInternal G Z, y ≠ .inr (.inl inner)) := by
  obtain ⟨cl, cr, _adj, clEq, crEq⟩ := owns
  constructor
  · intro inner h
    subst h
    rcases cl with l | i <;> simp [contextEmbedding] at clEq
  · intro inner h
    subst h
    rcases cr with l | i <;> simp [contextEmbedding] at crEq

/-- One split of the cycle at a non-piece-internal vertex `J`: either two
distinct retained labels, or `J` is itself a retained label. -/
theorem split_at
    {LengthOK : Nat → Prop}
    (c : CycleCertificate (glue (SupportAtom.retainedPiece G Z X) O) LengthOK)
    {inner : SupportAtom.PieceInternal G Z}
    (innerMem : (Sum.inr (Sum.inl inner) :
      GluedVertex (SupportAtom.retainedPiece G Z X) O) ∈ c.walk.support)
    {J : GluedVertex (SupportAtom.retainedPiece G Z X) O}
    (JMem : J ∈ c.walk.support)
    (JNot : ∀ i : SupportAtom.PieceInternal G Z, J ≠ .inr (.inl i)) :
    (∃ l₁ l₂ : (SupportAtom.boundary G Z).Vertex, l₁ ≠ l₂ ∧ l₁.1 ∈ X ∧ l₂.1 ∈ X) ∨
      (∃ l : (SupportAtom.boundary G Z).Vertex, J = .inl l ∧ l.1 ∈ X) := by
  classical
  let walk : (glueGraph (SupportAtom.retainedPiece G Z X) O).Walk c.vertex c.vertex :=
    c.walk
  have cycle : walk.IsCycle := c.isCycle
  set rotated := walk.rotate (Sum.inr (Sum.inl inner)) innerMem with rotatedDef
  have rotatedCycle : rotated.IsCycle := cycle.rotate innerMem
  have JRot : J ∈ rotated.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff walk _ innerMem).mpr JMem
  set w1 := rotated.takeUntil _ JRot with w1Def
  set w2 := rotated.dropUntil _ JRot with w2Def
  obtain ⟨l₁, l₁Mem, l₁X⟩ := exists_retained_label_of_walk w1 ⟨inner, rfl⟩ JNot
  obtain ⟨l₂, l₂Mem', l₂X⟩ := exists_retained_label_of_walk w2.reverse ⟨inner, rfl⟩ JNot
  have l₂Mem : (Sum.inl l₂ : GluedVertex (SupportAtom.retainedPiece G Z X) O) ∈
      w2.support := by
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at l₂Mem'
  by_cases h₂ : (Sum.inl l₂ : GluedVertex (SupportAtom.retainedPiece G Z X) O) = J
  · by_cases h₁ : (Sum.inl l₁ : GluedVertex (SupportAtom.retainedPiece G Z X) O) = J
    · exact Or.inr ⟨l₁, h₁.symm, l₁X⟩
    · refine Or.inl ⟨l₁, l₂, ?_, l₁X, l₂X⟩
      intro same
      subst same
      exact h₁ h₂
  · refine Or.inl ⟨l₁, l₂, ?_, l₁X, l₂X⟩
    intro same
    subst same
    have neI : (Sum.inl l₁ : GluedVertex (SupportAtom.retainedPiece G Z X) O) ≠
        .inr (.inl inner) := by simp
    have t₁ : (Sum.inl l₁ : GluedVertex (SupportAtom.retainedPiece G Z X) O) ∈
        w1.support.tail := by
      rcases (SimpleGraph.Walk.mem_support_iff w1).mp l₁Mem with headEq | tailMem
      · exact absurd headEq neI
      · exact tailMem
    have t₂ : (Sum.inl l₁ : GluedVertex (SupportAtom.retainedPiece G Z X) O) ∈
        w2.support.tail := by
      rcases (SimpleGraph.Walk.mem_support_iff w2).mp l₂Mem with headEq | tailMem
      · exact absurd headEq h₂
      · exact tailMem
    have spec := SimpleGraph.Walk.take_spec rotated JRot
    have supportSplit : rotated.support = w1.support ++ w2.support.tail := by
      conv_lhs => rw [← spec]
      exact SimpleGraph.Walk.support_append w1 w2
    have tailSplit : rotated.support.tail = w1.support.tail ++ w2.support.tail := by
      rw [supportSplit, ← SimpleGraph.Walk.cons_tail_support w1]
      rfl
    have nodup := rotatedCycle.support_nodup
    rw [tailSplit] at nodup
    exact ((List.nodup_append.mp nodup).2.2 _ t₁ _ t₂) rfl

/-- **Two retained labels**: a glued cycle with a piece-exclusive and a
context-exclusive edge crosses `∂Z` at two distinct vertices of the retained
set `X`. -/
theorem two_retained_labels
    {LengthOK : Nat → Prop}
    (c : CycleCertificate (glue (SupportAtom.retainedPiece G Z X) O) LengthOK)
    (hp : DefectGeometry.PieceExclusive c) (ho : DefectGeometry.ContextExclusive c) :
    ∃ l₁ l₂ : (SupportAtom.boundary G Z).Vertex, l₁ ≠ l₂ ∧ l₁.1 ∈ X ∧ l₂.1 ∈ X := by
  classical
  obtain ⟨x, y, he, ⟨p, q, adj, hx, hy⟩, _⟩ := hp
  have mx := c.walk.fst_mem_support_of_mem_edges he
  have my := c.walk.snd_mem_support_of_mem_edges he
  have mem := retained_adj_mem adj
  -- an internal vertex of the piece on the cycle, unless the piece edge is a
  -- label edge
  have inner : (∃ l₁ l₂ : (SupportAtom.boundary G Z).Vertex,
      l₁ ≠ l₂ ∧ l₁.1 ∈ X ∧ l₂.1 ∈ X) ∨
      ∃ i : SupportAtom.PieceInternal G Z,
        (Sum.inr (Sum.inl i) : GluedVertex (SupportAtom.retainedPiece G Z X) O) ∈
          c.walk.support := by
    rcases p with a | i
    · rcases q with b | j
      · exact Or.inl ⟨a, b, fun eq => adj.ne (congrArg Sum.inl eq), mem.1, mem.2⟩
      · rw [← hy] at my
        exact Or.inr ⟨j, my⟩
    · rw [← hx] at mx
      exact Or.inr ⟨i, mx⟩
  rcases inner with done | ⟨i, iMem⟩
  · exact done
  obtain ⟨u, v, he', owns, _⟩ := ho
  have mu := c.walk.fst_mem_support_of_mem_edges he'
  have mv := c.walk.snd_mem_support_of_mem_edges he'
  have uv : u ≠ v := (c.walk.adj_of_mem_edges he').ne
  obtain ⟨uNot, vNot⟩ := contextOwns_not_internal owns
  rcases split_at c iMem mu uNot with done | ⟨lu, uEq, luX⟩
  · exact done
  rcases split_at c iMem mv vNot with done | ⟨lv, vEq, lvX⟩
  · exact done
  refine ⟨lu, lv, ?_, luX, lvX⟩
  intro same
  exact uv (by rw [uEq, vEq, same])

end PositiveLabels

section Generic

open Classical


variable (object : Graph.FiniteObject.{u})

/-- Generic: a closed vertex of `S` (all neighbours in `S`) has full internal
degree. -/
theorem internalDegree_eq_degree_of_closed (S : Finset object.Vertex)
    (v : object.Vertex) (closed : ∀ y, object.graph.Adj v y → y ∈ S) :
    object.internalDegree S v = object.degree v := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold Graph.FiniteObject.internalDegree Graph.FiniteObject.degree
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  apply Finset.inter_eq_left.mpr
  intro y hy
  exact closed y ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)

/-- Generic: an internal degree is the number of neighbours in the support. -/
theorem internalDegree_eq_card_filter (S : Finset object.Vertex) (v : object.Vertex) :
    object.internalDegree S v =
      (object.vertexFinset.filter fun y => object.graph.Adj v y ∧ y ∈ S).card := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold Graph.FiniteObject.internalDegree
  congr 1
  ext y
  simp [Graph.FiniteObject.vertexFinset, SimpleGraph.mem_neighborFinset]

/-- Generic: the degree splits into the neighbours inside and outside `S`. -/
theorem degree_eq_inside_add_outside (S : Finset object.Vertex) (v : object.Vertex) :
    object.degree v =
      (object.vertexFinset.filter fun y => object.graph.Adj v y ∧ y ∈ S).card +
      (object.vertexFinset.filter fun y => object.graph.Adj v y ∧ y ∉ S).card := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold Graph.FiniteObject.degree
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_filter,
      Graph.FiniteObject.mem_vertexFinset, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2

/-- Generic (`no proper baseline` on an induced support): if no proper
subgraph keeps `δ ≥ k`, a nonempty support of fewer than `n` vertices has a
vertex with fewer than `k` neighbours inside it. -/
theorem exists_low_internalDegree (k : Nat)
    (noProper : ∀ sub : Graph.ProperSubgraph object,
      ¬ Graph.MinimumDegreeAtLeast k sub.value)
    (S : Finset object.Vertex) (nonempty : S.Nonempty)
    (proper : S.card < object.vertexCount) :
    ∃ v ∈ S, object.internalDegree S v < k := by
  classical
  by_contra h
  push Not at h
  let sub := Graph.ProperSubgraph.ofInducedSupport object S proper
  obtain ⟨v0, hv0⟩ := nonempty
  letI : Nonempty sub.value.Vertex := ⟨⟨v0, hv0⟩⟩
  apply noProper sub
  apply sub.value.le_minDegree_of_forall_le_degree k
  intro vertex
  change k ≤ (object.induce S).degree vertex
  rw [object.degree_induce_eq_internalDegree S vertex]
  exact h vertex.1 vertex.2

/-- Generic: a vertex of `S` with fewer internal than total neighbours is on
the cut boundary `∂S`. -/
theorem mem_cutBoundary_of_internalDegree_lt (S : Finset object.Vertex)
    {v : object.Vertex} (hv : v ∈ S)
    (low : object.internalDegree S v < object.degree v) :
    v ∈ SupportAtom.cutBoundary object S := by
  rw [SupportAtom.mem_cutBoundary_iff]
  refine ⟨hv, ?_⟩
  by_contra h
  push Not at h
  have := internalDegree_eq_degree_of_closed object S v
    (fun y hy => h y hy)
  omega

/-- **Generic (Z-side low vertex)**: under `δ ≥ k` and no proper baseline,
every nonempty proper support `S` has a boundary vertex with fewer than `k`
neighbours in `S`. -/
theorem exists_boundary_low_inside (k : Nat)
    (baseline : Graph.MinimumDegreeAtLeast k object)
    (noProper : ∀ sub : Graph.ProperSubgraph object,
      ¬ Graph.MinimumDegreeAtLeast k sub.value)
    (S : Finset object.Vertex) (nonempty : S.Nonempty)
    (proper : ∃ x, x ∉ S) :
    ∃ b ∈ SupportAtom.cutBoundary object S, object.internalDegree S b < k := by
  classical
  have lt : S.card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    obtain ⟨x, hx⟩ := proper
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => hx (h (object.mem_vertexFinset x))⟩
  obtain ⟨b, hb, low⟩ := exists_low_internalDegree object k noProper S nonempty lt
  refine ⟨b, mem_cutBoundary_of_internalDegree_lt object S hb ?_, low⟩
  exact lt_of_lt_of_le low (le_trans baseline (object.minDegree_le_degree b))

/-- **Generic (outside low vertex)**: under the same hypotheses, the outside
`V ∖ S` of a nonempty proper support has a vertex with fewer than `k`
neighbours outside `S`, hence (by `δ ≥ k`) a neighbour in `S`. -/
theorem exists_outside_low (k : Nat)
    (baseline : Graph.MinimumDegreeAtLeast k object)
    (noProper : ∀ sub : Graph.ProperSubgraph object,
      ¬ Graph.MinimumDegreeAtLeast k sub.value)
    (S : Finset object.Vertex) (nonempty : S.Nonempty)
    (proper : ∃ x, x ∉ S) :
    ∃ x, x ∉ S ∧
      (object.vertexFinset.filter fun y => object.graph.Adj x y ∧ y ∉ S).card < k ∧
      ∃ y ∈ S, object.graph.Adj x y := by
  classical
  let W := object.vertexFinset.filter fun y => y ∉ S
  have Wne : W.Nonempty := by
    obtain ⟨x, hx⟩ := proper
    exact ⟨x, by simp [W, hx]⟩
  have lt : W.card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    obtain ⟨s, hs⟩ := nonempty
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => by
          have := h (object.mem_vertexFinset s)
          simp [W] at this
          exact this hs⟩
  obtain ⟨x, hxW, low⟩ := exists_low_internalDegree object k noProper W Wne lt
  have hx : x ∉ S := by simpa [W] using hxW
  rw [internalDegree_eq_card_filter] at low
  have eqW : (object.vertexFinset.filter fun y => object.graph.Adj x y ∧ y ∈ W) =
      (object.vertexFinset.filter fun y => object.graph.Adj x y ∧ y ∉ S) := by
    ext y; simp [W]
  rw [eqW] at low
  refine ⟨x, hx, low, ?_⟩
  by_contra h
  push Not at h
  have split := degree_eq_inside_add_outside object S x
  have zero : (object.vertexFinset.filter fun y => object.graph.Adj x y ∧ y ∈ S).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ ⟨adj, mem⟩
    exact h y mem adj
  have := le_trans baseline (object.minDegree_le_degree x)
  omega

/-- **Generic (the `|∂S| = 1` shape)**.  Let `δ ≥ 3`, no proper subgraph with
`δ ≥ 3`, and no bridge.  If a support `S` has exactly one boundary vertex `b`,
another vertex `z ∈ S`, and a vertex outside, then `b` has exactly two
neighbours in `S` and exactly two outside `S` (so `deg b = 4` and `b` is a cut
vertex splitting its edges 2+2). -/
theorem single_boundary_shape
    (baseline : Graph.MinimumDegreeAtLeast 3 object)
    (noProper : ∀ sub : Graph.ProperSubgraph object,
      ¬ Graph.MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : Graph.EdgeContraction object, contraction.HasReturn)
    (S : Finset object.Vertex) (b : object.Vertex)
    (single : SupportAtom.cutBoundary object S = {b})
    {z : object.Vertex} (hz : z ∈ S) (zb : z ≠ b)
    (proper : ∃ x, x ∉ S) :
    (object.vertexFinset.filter fun y => object.graph.Adj b y ∧ y ∈ S).card = 2 ∧
      (object.vertexFinset.filter fun y => object.graph.Adj b y ∧ y ∉ S).card = 2 := by
  classical
  have bB : b ∈ SupportAtom.cutBoundary object S := by rw [single]; simp
  have bS : b ∈ S := ((SupportAtom.mem_cutBoundary_iff object S b).1 bB).1
  -- vertices of `S` other than `b` are closed in `S`
  have closedS : ∀ v ∈ S, v ≠ b → ∀ y, object.graph.Adj v y → y ∈ S := by
    intro v hv vb y adj
    by_contra hy
    have : v ∈ SupportAtom.cutBoundary object S :=
      (SupportAtom.mem_cutBoundary_iff object S v).2 ⟨hv, y, adj, hy⟩
    rw [single] at this
    exact vb (Finset.mem_singleton.1 this)
  have degGe : ∀ v, 3 ≤ object.degree v := fun v =>
    le_trans baseline (object.minDegree_le_degree v)
  have cardLt : ∀ T : Finset object.Vertex, (∃ x, x ∉ T) → T.card < object.vertexCount := by
    intro T ⟨x, hx⟩
    rw [← Graph.FiniteObject.card_vertexFinset]
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => hx (h (object.mem_vertexFinset x))⟩
  set inn := (object.vertexFinset.filter fun y => object.graph.Adj b y ∧ y ∈ S) with innDef
  set out := (object.vertexFinset.filter fun y => object.graph.Adj b y ∧ y ∉ S) with outDef
  have split := degree_eq_inside_add_outside object S b
  -- (1) at most two inside: `G[S]` would be a proper baseline
  have innLe : inn.card ≤ 2 := by
    by_contra h
    push Not at h
    obtain ⟨v, hv, low⟩ := exists_low_internalDegree object 3 noProper S ⟨b, bS⟩
      (cardLt S proper)
    by_cases vb : v = b
    · rw [vb, internalDegree_eq_card_filter, ← innDef] at low
      omega
    · rw [internalDegree_eq_degree_of_closed object S v (closedS v hv vb)] at low
      have := degGe v
      omega
  -- (2) at most two outside: `G[(V ∖ S) ∪ {b}]` would be a proper baseline
  have outLe : out.card ≤ 2 := by
    by_contra h
    push Not at h
    let T := object.vertexFinset.filter fun y => y ∉ S ∨ y = b
    have closedT : ∀ x, x ∉ S → ∀ y, object.graph.Adj x y → y ∈ T := by
      intro x hx y adj
      by_cases hy : y ∈ S
      · have : y ∈ SupportAtom.cutBoundary object S :=
          (SupportAtom.mem_cutBoundary_iff object S y).2 ⟨hy, x, adj.symm, hx⟩
        rw [single] at this
        simp [T, Finset.mem_singleton.1 this]
      · simp [T, hy]
    obtain ⟨v, hv, low⟩ := exists_low_internalDegree object 3 noProper T ⟨b, by simp [T]⟩
      (cardLt T ⟨z, by simp [T, hz, zb]⟩)
    have hv' : v ∉ S ∨ v = b := by simpa [T] using hv
    rcases hv' with vS | rfl
    · rw [internalDegree_eq_degree_of_closed object T v (closedT v vS)] at low
      have := degGe v
      omega
    · rw [internalDegree_eq_card_filter] at low
      have sub : out ⊆ (object.vertexFinset.filter fun y => object.graph.Adj v y ∧ y ∈ T) := by
        intro y hy
        simp only [outDef, Finset.mem_filter] at hy
        simp [T, hy.2.1, hy.2.2]
      have := Finset.card_le_card sub
      omega
  -- (3) at least one inside: otherwise `G[S ∖ {b}]` is a proper baseline
  have innPos : 1 ≤ inn.card := by
    by_contra h
    push Not at h
    have innEmpty : ∀ y, object.graph.Adj b y → y ∉ S := by
      intro y adj yS
      have : y ∈ inn := by simp [innDef, adj, yS]
      have e : inn = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [e] at this
      simp at this
    let S' := S.erase b
    obtain ⟨v, hv, low⟩ := exists_low_internalDegree object 3 noProper S'
      ⟨z, Finset.mem_erase.2 ⟨zb, hz⟩⟩ (cardLt S' ⟨b, by simp [S']⟩)
    have vb : v ≠ b := Finset.ne_of_mem_erase hv
    have vS : v ∈ S := Finset.mem_of_mem_erase hv
    rw [internalDegree_eq_degree_of_closed object S' v (fun y adj =>
      Finset.mem_erase.2 ⟨fun yb => innEmpty v (yb ▸ adj.symm) vS,
        closedS v vS vb y adj⟩)] at low
    have := degGe v
    omega
  -- (4) at least one outside: `b ∈ ∂S`
  have outPos : 1 ≤ out.card := by
    obtain ⟨-, y, adj, yS⟩ := (SupportAtom.mem_cutBoundary_iff object S b).1 bB
    exact Finset.card_pos.2 ⟨y, by simp [outDef, adj, yS]⟩
  -- (5) not exactly one inside: that edge would be a bridge
  have innNe1 : inn.card ≠ 1 := by
    intro one
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp one
    have z0mem : z0 ∈ inn := by rw [hz0]; simp
    simp only [innDef, Finset.mem_filter] at z0mem
    obtain ⟨-, adj0, z0S⟩ := z0mem
    obtain ⟨path⟩ := bridgeless ⟨b, z0, adj0⟩
    obtain ⟨d, -, dIn, dOut⟩ := path.1.exists_boundary_dart
      ({x | x ∉ S.erase b} : Set object.Vertex)
      (by simp) (by simp [Finset.mem_erase, (adj0.ne).symm, z0S])
    have sev := (Graph.EdgeContraction.severed_adj (object := object) ⟨b, z0, adj0⟩).1
      d.adj
    simp only [Set.mem_setOf_eq, not_not] at dIn dOut
    have sndS : d.snd ∈ S := Finset.mem_of_mem_erase dOut
    have sndB : d.snd ≠ b := Finset.ne_of_mem_erase dOut
    have fstS : d.fst ∈ S := closedS d.snd sndS sndB d.fst sev.1.symm
    have fstB : d.fst = b := by
      by_contra fb
      exact dIn (Finset.mem_erase.2 ⟨fb, fstS⟩)
    have sndIn : d.snd ∈ inn := by
      simp only [innDef, Finset.mem_filter, Graph.FiniteObject.mem_vertexFinset,
        true_and]
      exact ⟨by have a := sev.1; rw [fstB] at a; exact a, sndS⟩
    rw [hz0, Finset.mem_singleton] at sndIn
    apply sev.2
    change s(d.fst, d.snd) = s(b, z0)
    rw [fstB, sndIn]
  -- (6) not exactly one outside: that edge would be a bridge
  have outNe1 : out.card ≠ 1 := by
    intro one
    obtain ⟨y0, hy0⟩ := Finset.card_eq_one.mp one
    have y0mem : y0 ∈ out := by rw [hy0]; simp
    simp only [outDef, Finset.mem_filter] at y0mem
    obtain ⟨-, adj0, y0S⟩ := y0mem
    obtain ⟨path⟩ := bridgeless ⟨b, y0, adj0⟩
    obtain ⟨d, -, dIn, dOut⟩ := path.1.exists_boundary_dart
      ((S : Set object.Vertex)) (by simpa using bS) (by simpa using y0S)
    have sev := (Graph.EdgeContraction.severed_adj (object := object) ⟨b, y0, adj0⟩).1
      d.adj
    have fstB' : d.fst ∈ SupportAtom.cutBoundary object S :=
      (SupportAtom.mem_cutBoundary_iff object S d.fst).2 ⟨dIn, d.snd, sev.1, dOut⟩
    rw [single, Finset.mem_singleton] at fstB'
    have sndIn : d.snd ∈ out := by
      simp only [outDef, Finset.mem_filter, Graph.FiniteObject.mem_vertexFinset,
        true_and]
      exact ⟨by have a := sev.1; rw [fstB'] at a; exact a, dOut⟩
    rw [hy0, Finset.mem_singleton] at sndIn
    apply sev.2
    change s(d.fst, d.snd) = s(b, y0)
    rw [fstB', sndIn]
  omega

end Generic

section CutEdges

open Classical

/-- **Generic**: the number of boundary-to-outside edges is at least `|∂S|`
(each boundary vertex has at least one outside neighbour). -/
theorem card_cutBoundary_le_cutEdges (object : Graph.FiniteObject.{u})
    (S : Finset object.Vertex) :
    (SupportAtom.cutBoundary object S).card ≤
      ∑ v ∈ SupportAtom.cutBoundary object S,
        (object.vertexFinset.filter fun y => object.graph.Adj v y ∧ y ∉ S).card := by
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro v hv
  obtain ⟨-, y, adj, yS⟩ := (SupportAtom.mem_cutBoundary_iff object S v).1 hv
  exact Finset.card_pos.2 ⟨y, by simp [adj, yS]⟩

end CutEdges

section TwoBoundaryGeneric

open Hypostructure.Graph.Strategy.InterfaceReplacement
open Classical

variable (object : Graph.FiniteObject.{u})

/-- **Generic 2-sum closure (edge insertion on one side)**.  Let `T` be a side
of a 2-separation `{a, b}` (every vertex of `T` other than `a, b` has all its
neighbours in `T`), `|T| < n`, `a ≁ b`, and `a, b` each have at least two
neighbours in `T`.  If `G` avoids the target, `δ(G) ≥ 3`, and every
lex-smaller object with `δ ≥ 3` has a target cycle, then `G[T]` contains an
`a`–`b` path `P` with `LengthOK (|P| + 1)`. -/
theorem side_closure_path {LengthOK : Nat → Prop}
    (baseline : 3 ≤ object.minDegree)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (minimal : ∀ candidate : Graph.FiniteObject.{u},
      candidate.LexicographicallySmaller object → 3 ≤ candidate.minDegree →
        Graph.HasCycleWithLength LengthOK candidate)
    (T : Finset object.Vertex) {a b : object.Vertex} (ha : a ∈ T) (hb : b ∈ T)
    (ab : a ≠ b) (notAdj : ¬ object.graph.Adj a b)
    (small : T.card < object.vertexCount)
    (closed : ∀ v ∈ T, v ≠ a → v ≠ b → ∀ y, object.graph.Adj v y → y ∈ T)
    (da : 2 ≤ object.internalDegree T a) (db : 2 ≤ object.internalDegree T b) :
    ∃ p : object.graph.Walk a b, p.IsPath ∧ (∀ v ∈ p.support, v ∈ T) ∧
      LengthOK (p.length + 1) := by
  let a' : (object.induce T).Vertex := ⟨a, ha⟩
  let b' : (object.induce T).Vertex := ⟨b, hb⟩
  have ab' : a' ≠ b' := fun h => ab (congrArg Subtype.val h)
  have notAdj' : ¬ (object.induce T).graph.Adj a' b' := notAdj
  have sideAvoids : ¬ Graph.HasCycleWithLength LengthOK (object.induce T) :=
    fun h => avoids ((Graph.cycleProperSubgraphTargetMonotone LengthOK).map
      (Graph.ProperSubgraph.ofInducedSupport object T small) h)
  have smaller : ((object.induce T).addEdge a' b').LexicographicallySmaller object :=
    Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
      rw [Graph.FiniteObject.vertexCount_addEdge, Graph.FiniteObject.vertexCount_induce]
      exact small)
  have degSide : ∀ v : (object.induce T).Vertex,
      (object.induce T).degree v = object.internalDegree T v.1 :=
    fun v => object.degree_induce_eq_internalDegree T v
  have newBaseline : 3 ≤ ((object.induce T).addEdge a' b').minDegree := by
    letI : Nonempty ((object.induce T).addEdge a' b').Vertex := ⟨a'⟩
    apply ((object.induce T).addEdge a' b').le_minDegree_of_forall_le_degree 3
    intro v
    by_cases va : v = a'
    · rw [va, Graph.FiniteObject.degree_addEdge_left _ _ _ ab' notAdj', degSide]
      have : object.internalDegree T a'.1 = object.internalDegree T a := rfl
      omega
    by_cases vb : v = b'
    · rw [vb, Graph.FiniteObject.degree_addEdge_right _ _ _ ab' notAdj', degSide]
      have : object.internalDegree T b'.1 = object.internalDegree T b := rfl
      omega
    rw [Graph.FiniteObject.degree_addEdge_of_ne (object.induce T) a' b' v va vb, degSide,
      internalDegree_eq_degree_of_closed object T v.1
        (closed v.1 v.2 (fun h => va (Subtype.ext h)) (fun h => vb (Subtype.ext h)))]
    exact le_trans baseline (object.minDegree_le_degree v.1)
  obtain ⟨path, isPath, ok⟩ := AddedEdgeClosure.terminalPath_of_minimal_addedEdge
    object (object.induce T) a' b' ab' sideAvoids smaller newBaseline minimal
  let hom : (object.induce T).graph →g object.graph := (object.induceEmbedding T).toHom
  have homInj : Function.Injective hom := (object.induceEmbedding T).injective
  refine ⟨path.map hom, SimpleGraph.Walk.map_isPath_of_injective homInj isPath, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ path.support.map hom := by
      rw [← SimpleGraph.Walk.support_map]; exact hv
    obtain ⟨v', -, rfl⟩ := List.mem_map.mp hv'
    exact v'.2
  · have hl : (path.map hom).length = path.length := SimpleGraph.Walk.length_map hom path
    convert ok using 2
    exact hl

/-- **Generic: two internally disjoint `a`–`b` paths close a cycle**, so target
avoidance forbids the sum of their lengths. -/
theorem no_target_two_sides {LengthOK : Nat → Prop}
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (T T' : Finset object.Vertex) {a b : object.Vertex}
    (meet : ∀ v, v ∈ T → v ∈ T' → v = a ∨ v = b)
    (p : object.graph.Walk a b) (hp : p.IsPath) (pT : ∀ v ∈ p.support, v ∈ T)
    (q : object.graph.Walk b a) (hq : q.IsPath) (qT : ∀ v ∈ q.support, v ∈ T')
    (long : 1 < p.length ∨ 1 < q.length) :
    ¬ LengthOK (p.length + q.length) := by
  intro ok
  have disj : p.support.tail.Disjoint q.support.tail := by
    intro v vp vq
    have vpT := pT v (List.mem_of_mem_tail vp)
    have vqT := qT v (List.mem_of_mem_tail vq)
    rcases meet v vpT vqT with rfl | rfl
    · -- `a` is the head of `p`, so not in its tail
      have nd := hp.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support p] at nd
      exact (List.nodup_cons.mp nd).1 vp
    · have nd := hq.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support q] at nd
      exact (List.nodup_cons.mp nd).1 vq
  have cyc := hp.isCycle_append hq disj long
  exact avoids ⟨⟨a, p.append q, cyc, by rw [SimpleGraph.Walk.length_append]; exact ok⟩⟩

end TwoBoundaryGeneric

section OutsideSide

open Classical


/-- **Generic**: if `x` is the only vertex outside `S`, then `∂S = N(x)` and
`|∂S| = deg x`. -/
theorem single_outside_boundary_card (object : Graph.FiniteObject.{u})
    (S : Finset object.Vertex) {x : object.Vertex} (hx : x ∉ S)
    (only : ∀ y, y ∉ S → y = x) :
    (SupportAtom.cutBoundary object S).card = object.degree x := by
  have split := degree_eq_inside_add_outside object S x
  have zero : (object.vertexFinset.filter fun y => object.graph.Adj x y ∧ y ∉ S).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ ⟨adj, yS⟩
    exact adj.ne (only y yS).symm
  have eq : SupportAtom.cutBoundary object S =
      (object.vertexFinset.filter fun y => object.graph.Adj x y ∧ y ∈ S) := by
    ext v
    rw [SupportAtom.mem_cutBoundary_iff]
    simp only [Finset.mem_filter, Graph.FiniteObject.mem_vertexFinset, true_and]
    constructor
    · rintro ⟨vS, y, adj, yS⟩
      exact ⟨by rw [← only y yS]; exact adj.symm, vS⟩
    · rintro ⟨adj, vS⟩
      exact ⟨vS, x, adj.symm, hx⟩
  rw [eq]
  omega

/-- The outside-plus-terminals side `T' = (V ∖ Z) ∪ {a, b}`. -/
noncomputable def outsideSide (object : Graph.FiniteObject.{u}) (Z : Finset object.Vertex)
    (a b : object.Vertex) : Finset object.Vertex :=
  object.vertexFinset.filter fun y => y ∉ Z ∨ y = a ∨ y = b

theorem outsideSide_closed (object : Graph.FiniteObject.{u}) (Z : Finset object.Vertex)
    {a b : object.Vertex} (hab : SupportAtom.cutBoundary object Z = {a, b}) :
    ∀ v ∈ outsideSide object Z a b, v ≠ a → v ≠ b →
      ∀ y, object.graph.Adj v y → y ∈ outsideSide object Z a b := by
  intro v hv va vb y adj
  have vZ : v ∉ Z := by
    simp only [outsideSide, Finset.mem_filter] at hv
    rcases hv.2 with h | h | h
    · exact h
    · exact (va h).elim
    · exact (vb h).elim
  by_cases yZ : y ∈ Z
  · have : y ∈ SupportAtom.cutBoundary object Z :=
      (SupportAtom.mem_cutBoundary_iff object Z y).2 ⟨yZ, v, adj.symm, vZ⟩
    rw [hab] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    simp [outsideSide, this]
  · simp [outsideSide, yZ]

theorem closedZ_of_two (object : Graph.FiniteObject.{u}) (Z : Finset object.Vertex)
    {a b : object.Vertex} (hab : SupportAtom.cutBoundary object Z = {a, b}) :
    ∀ v ∈ Z, v ≠ a → v ≠ b → ∀ y, object.graph.Adj v y → y ∈ Z := by
  intro v hv va vb y adj
  by_contra yZ
  have : v ∈ SupportAtom.cutBoundary object Z :=
    (SupportAtom.mem_cutBoundary_iff object Z v).2 ⟨hv, y, adj, yZ⟩
  rw [hab] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact va h
  · exact vb h

end OutsideSide

section Spectrum

open SimpleGraph

variable {boundary : Boundary.{u}} {P : BoundaryPiece boundary} {O : OutsideContext boundary}

theorem pieceOwns_symm {x y : GluedVertex P O} (h : PieceOwns P O x y) :
    PieceOwns P O y x := by
  obtain ⟨r, t, adj, hr, ht⟩ := h
  exact ⟨t, r, adj.symm, ht, hr⟩

theorem contextOwns_symm {x y : GluedVertex P O} (h : ContextOwns P O x y) :
    ContextOwns P O y x := by
  obtain ⟨r, t, adj, hr, ht⟩ := h
  exact ⟨t, r, adj.symm, ht, hr⟩

/-- An edge at a piece-internal vertex is owned by the piece. -/
theorem pieceOwns_of_adj_pieceInt {x y : GluedVertex P O} (h : (glueGraph P O).Adj x y)
    (i : P.Internal) (hx : x = .inr (.inl i)) : PieceOwns P O x y := by
  rcases (glueGraph_adj_iff P O x y).mp h with own | ⟨r, t, _, hr, _⟩
  · exact own
  · subst hx; rcases r with r | r <;> cases hr

/-- An edge at a context-internal vertex is owned by the context. -/
theorem contextOwns_of_adj_contextInt {x y : GluedVertex P O} (h : (glueGraph P O).Adj x y)
    (o : O.Internal) (hx : x = .inr (.inr o)) : ContextOwns P O x y := by
  rcases (glueGraph_adj_iff P O x y).mp h with ⟨r, t, _, hr, _⟩ | own
  · subst hx; rcases r with r | r <;> cases hr
  · exact own

/-- A path starting at a piece-internal vertex, meeting no label before its
end, uses only piece-owned edges. -/
theorem walk_pieceOwned : ∀ {x y : GluedVertex P O} (w : (glueGraph P O).Walk x y),
    w.IsPath → (∃ i, x = .inr (.inl i)) →
    (∀ v ∈ w.support, v = y ∨ ∀ c, v ≠ .inl c) →
    ∀ p q, s(p, q) ∈ w.edges → PieceOwns P O p q := by
  intro x y w
  induction w with
  | nil => intro _ _ _ p q h; simp at h
  | @cons u v z h rest ih =>
    intro hp hi hs p q hpq
    obtain ⟨i, hi⟩ := hi
    have own : PieceOwns P O u v := pieceOwns_of_adj_pieceInt h i hi
    have hrest := ((Walk.cons_isPath_iff h rest).mp hp).1
    simp only [Walk.edges_cons, List.mem_cons] at hpq
    rcases hpq with e | e
    · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact own
      · exact pieceOwns_symm own
    · by_cases hvz : v = z
      · subst hvz
        have := Walk.eq_nil_iff_nil.mpr ((Walk.isPath_iff_nil).mp hrest)
        subst this
        simp at e
      · have hv : ∃ j, v = .inr (.inl j) := by
          rcases hs v (by simp) with h1 | h1
          · exact (hvz h1).elim
          · obtain ⟨r, t, _, _, ht⟩ := own
            rcases t with t | t
            · exact (h1 t ht.symm).elim
            · exact ⟨t, ht.symm⟩
        exact ih hrest hv (fun v' hv' => hs v' (by simp [hv'])) p q e

/-- The context analogue of `walk_pieceOwned`. -/
theorem walk_contextOwned : ∀ {x y : GluedVertex P O} (w : (glueGraph P O).Walk x y),
    w.IsPath → (∃ o, x = .inr (.inr o)) →
    (∀ v ∈ w.support, v = y ∨ ∀ c, v ≠ .inl c) →
    ∀ p q, s(p, q) ∈ w.edges → ContextOwns P O p q := by
  intro x y w
  induction w with
  | nil => intro _ _ _ p q h; simp at h
  | @cons u v z h rest ih =>
    intro hp hi hs p q hpq
    obtain ⟨i, hi⟩ := hi
    have own : ContextOwns P O u v := contextOwns_of_adj_contextInt h i hi
    have hrest := ((Walk.cons_isPath_iff h rest).mp hp).1
    simp only [Walk.edges_cons, List.mem_cons] at hpq
    rcases hpq with e | e
    · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact own
      · exact contextOwns_symm own
    · by_cases hvz : v = z
      · subst hvz
        have := Walk.eq_nil_iff_nil.mpr ((Walk.isPath_iff_nil).mp hrest)
        subst this
        simp at e
      · have hv : ∃ j, v = .inr (.inr j) := by
          rcases hs v (by simp) with h1 | h1
          · exact (hvz h1).elim
          · obtain ⟨r, t, _, _, ht⟩ := own
            rcases t with t | t
            · exact (h1 t ht.symm).elim
            · exact ⟨t, ht.symm⟩
        exact ih hrest hv (fun v' hv' => hs v' (by simp [hv'])) p q e

/-- **One arc between two labels is single-sided**: a path in `glue P O`
between two distinct vertices, the first a label, meeting labels only at its
ends, uses only piece-owned edges or only context-owned edges. -/
theorem arc_owned : ∀ {x y : GluedVertex P O} (w : (glueGraph P O).Walk x y),
    x ≠ y → w.IsPath → (∀ v ∈ w.support, v = x ∨ v = y ∨ ∀ c, v ≠ .inl c) →
    (∀ p q, s(p, q) ∈ w.edges → PieceOwns P O p q) ∨
      (∀ p q, s(p, q) ∈ w.edges → ContextOwns P O p q) := by
  intro x y w hxy hp hs
  cases w with
  | nil => exact (hxy rfl).elim
  | @cons _ v _ h rest =>
    have hrest := ((Walk.cons_isPath_iff h rest).mp hp).1
    have hxrest := ((Walk.cons_isPath_iff h rest).mp hp).2
    by_cases hvy : v = y
    · subst hvy
      have := Walk.eq_nil_iff_nil.mpr ((Walk.isPath_iff_nil).mp hrest)
      subst this
      rcases (glueGraph_adj_iff P O x v).mp h with own | own
      · left
        intro p q e
        simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
          or_false] at e
        rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact own
        · exact pieceOwns_symm own
      · right
        intro p q e
        simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
          or_false] at e
        rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact own
        · exact contextOwns_symm own
    · have nl : ∀ c, v ≠ .inl c := by
        rcases hs v (by simp) with h1 | h1 | h1
        · exact (h.ne h1.symm).elim
        · exact (hvy h1).elim
        · exact h1
      have restCond : ∀ z ∈ rest.support, z = y ∨ ∀ c, z ≠ .inl c := by
        intro z hz
        rcases hs z (by simp [hz]) with h1 | h1 | h1
        · exact (hxrest (h1 ▸ hz)).elim
        · exact Or.inl h1
        · exact Or.inr h1
      have split : (∃ j, v = .inr (.inl j)) ∨ (∃ o, v = .inr (.inr o)) := by
        clear hs restCond hrest hxrest
        rcases v with c | j | o
        · exact (nl c rfl).elim
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr ⟨o, rfl⟩
      rcases split with ⟨j, hj⟩ | ⟨o, ho⟩
      · left
        have own : PieceOwns P O x v := pieceOwns_symm (pieceOwns_of_adj_pieceInt h.symm j hj)
        intro p q e
        simp only [Walk.edges_cons, List.mem_cons] at e
        rcases e with e | e
        · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact own
          · exact pieceOwns_symm own
        · exact walk_pieceOwned rest hrest ⟨j, hj⟩ restCond p q e
      · right
        have own : ContextOwns P O x v :=
          contextOwns_symm (contextOwns_of_adj_contextInt h.symm o ho)
        intro p q e
        simp only [Walk.edges_cons, List.mem_cons] at e
        rcases e with e | e
        · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact own
          · exact contextOwns_symm own
        · exact walk_contextOwned rest hrest ⟨o, ho⟩ restCond p q e

theorem start_not_mem_tail {V : Type*} {G : SimpleGraph V} {x y : V} {w : G.Walk x y}
    (hw : w.IsPath) : x ∉ w.support.tail := by
  have nd := hw.support_nodup
  rw [← Walk.cons_tail_support] at nd
  exact (List.nodup_cons.mp nd).1

/-- **Closing a piece path by a context path**: an `a → b` path of the piece
and a `b → a` path of the context meeting no label other than `a, b` glue into
a cycle of `glue Q O` of length the sum of the two lengths (unless both have
length one). -/
theorem glue_cycle_of_arcs {Q : BoundaryPiece boundary} {a b : boundary.Vertex}
    (π : Q.graph.Walk (.inl a) (.inl b)) (hπ : π.IsPath)
    (σ : O.graph.Walk (.inl b) (.inl a)) (hσ : σ.IsPath)
    (lab : ∀ d, (Sum.inl d : boundary.Vertex ⊕ O.Internal) ∈ σ.support → d = a ∨ d = b)
    (hn : 1 < π.length ∨ 1 < σ.length) :
    ∃ v, ∃ W : (glueGraph Q O).Walk v v, W.IsCycle ∧ W.length = π.length + σ.length := by
  let f := pieceHom Q O
  let g := contextHom Q O
  let π' : (glueGraph Q O).Walk (.inl a) (.inl b) := π.map f
  let σ' : (glueGraph Q O).Walk (.inl b) (.inl a) := σ.map g
  have hπ' : π'.IsPath := Walk.map_isPath_of_injective (pieceEmbedding Q O).injective hπ
  have hσ' : σ'.IsPath := Walk.map_isPath_of_injective (contextEmbedding Q O).injective hσ
  have disj : π'.support.tail.Disjoint σ'.support.tail := by
    intro x hx1 hx2
    have e1 : π'.support.tail = π.support.tail.map (pieceEmbedding Q O) := by
      change (π.map f).support.tail = _
      rw [Walk.support_map, List.map_tail]; rfl
    have e2 : σ'.support.tail = σ.support.tail.map (contextEmbedding Q O) := by
      change (σ.map g).support.tail = _
      rw [Walk.support_map, List.map_tail]; rfl
    rw [e1] at hx1
    rw [e2] at hx2
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx1
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hx2
    rcases p with c | i <;> rcases q with d | o
    · have hdc : d = c := by
        have : (Sum.inl d : GluedVertex Q O) = Sum.inl c := hqe
        exact Sum.inl.inj this
      subst hdc
      rcases lab d (List.mem_of_mem_tail hq) with rfl | rfl
      · exact start_not_mem_tail hπ hp
      · exact start_not_mem_tail hσ hq
    · cases hqe
    · cases hqe
    · cases hqe
  have l1 : π'.length = π.length := Walk.length_map _ _
  have l2 : σ'.length = σ.length := Walk.length_map _ _
  refine ⟨_, π'.append σ', hπ'.isCycle_append hσ' disj ?_, ?_⟩
  · rw [l1, l2]; exact hn
  · rw [Walk.length_append, l1, l2]

/-- Lifting a piece-owned glued path to a path of the piece. -/
theorem lift_piece_path {x y : boundary.Vertex}
    (w : (glueGraph P O).Walk (.inl x) (.inl y)) (hw : w.IsPath)
    (own : ∀ p q, s(p, q) ∈ w.edges → PieceOwns P O p q) :
    ∃ l : P.graph.Walk (.inl x) (.inl y), l.IsPath ∧ l.length = w.length := by
  obtain ⟨l, hl, hs, _⟩ := DefectGeometry.liftWalk (pieceEmbedding P O) w (x := Sum.inl x) (y := Sum.inl y) rfl rfl own
  refine ⟨l, Walk.IsPath.mk' ?_, hl⟩
  have := hw.support_nodup
  rw [hs] at this
  exact this.of_map

/-- Lifting a context-owned glued path to a path of the context, keeping its
labels. -/
theorem lift_context_path {x y : boundary.Vertex}
    (w : (glueGraph P O).Walk (.inl x) (.inl y)) (hw : w.IsPath)
    (own : ∀ p q, s(p, q) ∈ w.edges → ContextOwns P O p q) :
    ∃ l : O.graph.Walk (.inl x) (.inl y), l.IsPath ∧ l.length = w.length ∧
      ∀ d, (Sum.inl d : boundary.Vertex ⊕ O.Internal) ∈ l.support →
        (Sum.inl d : GluedVertex P O) ∈ w.support := by
  obtain ⟨l, hl, hs, _⟩ := DefectGeometry.liftWalk (contextEmbedding P O) w (x := Sum.inl x) (y := Sum.inl y) rfl rfl own
  refine ⟨l, Walk.IsPath.mk' ?_, hl, fun d hd => ?_⟩
  · have := hw.support_nodup
    rw [hs] at this
    exact this.of_map
  · rw [hs]
    exact List.mem_map_of_mem hd

/-- **Two-label split of a cycle**: a cycle of `glue P O` with a piece-exclusive
and a context-exclusive edge, meeting exactly two labels `a ≠ b`, is a piece
path plus a context path between them (the context path meeting no other
label), with lengths adding to the cycle length. -/
theorem twoLabel_cycle_split {LengthOK : Nat → Prop}
    (c : Graph.CycleCertificate (glue P O) LengthOK)
    (hP : DefectGeometry.PieceExclusive c) (hO : DefectGeometry.ContextExclusive c)
    {a b : boundary.Vertex} (hab : a ≠ b)
    (ha : (Sum.inl a : GluedVertex P O) ∈ c.walk.support)
    (hb : (Sum.inl b : GluedVertex P O) ∈ c.walk.support)
    (only : ∀ d, (Sum.inl d : GluedVertex P O) ∈ c.walk.support → d = a ∨ d = b) :
    ∃ a' b' : boundary.Vertex, a' ≠ b' ∧
      ∃ π : P.graph.Walk (.inl a') (.inl b'), π.IsPath ∧
      ∃ σ : O.graph.Walk (.inl b') (.inl a'), σ.IsPath ∧
        (∀ d, (Sum.inl d : boundary.Vertex ⊕ O.Internal) ∈ σ.support → d = a' ∨ d = b') ∧
        π.length + σ.length = c.walk.length := by
  classical
  let W0 : (glueGraph P O).Walk c.vertex c.vertex := c.walk
  have hc0 : W0.IsCycle := c.isCycle
  let W := W0.rotate (.inl a) ha
  have hW : W.IsCycle := hc0.rotate ha
  have hbW : (Sum.inl b : GluedVertex P O) ∈ W.support :=
    (Walk.mem_support_rotate_iff _ _ _).mpr hb
  let p1 := W.takeUntil _ hbW
  let p2 := W.dropUntil _ hbW
  have spec : p1.append p2 = W := Walk.take_spec W hbW
  have ne : (Sum.inl a : GluedVertex P O) ≠ Sum.inl b := fun h => hab (Sum.inl.inj h)
  have hp1 : p1.IsPath := hW.isPath_takeUntil hbW
  have hp2 : p2.IsPath := by
    have h' : (p1.append p2).IsCycle := by rw [spec]; exact hW
    exact h'.isPath_of_append_right (Walk.not_nil_of_ne ne)
  have memW : ∀ v, v ∈ W.support → v ∈ c.walk.support := fun v hv =>
    (Walk.mem_support_rotate_iff _ _ _).mp hv
  have s1 : ∀ v ∈ p1.support, v ∈ c.walk.support := fun v hv =>
    memW v (Walk.support_takeUntil_subset_support _ _ hv)
  have s2 : ∀ v ∈ p2.support, v ∈ c.walk.support := fun v hv =>
    memW v (Walk.support_dropUntil_subset_support _ _ hv)
  have cond : ∀ v : GluedVertex P O, v ∈ c.walk.support →
      v = Sum.inl a ∨ v = Sum.inl b ∨ ∀ d, v ≠ Sum.inl d := by
    intro v hv
    by_cases hl : ∃ d, v = Sum.inl d
    · obtain ⟨d, rfl⟩ := hl
      rcases only d hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · push Not at hl
      exact Or.inr (Or.inr hl)
  have o1 := arc_owned p1 ne hp1 (fun v hv => cond v (s1 v hv))
  have o2 := arc_owned p2 (Ne.symm ne) hp2 (fun v hv => by
    rcases cond v (s2 v hv) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h))
  have edgesW : ∀ e, e ∈ c.walk.edges → e ∈ p1.edges ∨ e ∈ p2.edges := by
    intro e he
    have : e ∈ W.edges := (Walk.rotate_edges W0 _ ha).perm.mem_iff.mpr he
    rw [← spec, Walk.edges_append] at this
    exact List.mem_append.mp this
  have lenW : p1.length + p2.length = c.walk.length := by
    rw [← Walk.length_append, spec]
    exact Walk.length_rotate _ _ _
  rcases o1 with o1 | o1 <;> rcases o2 with o2 | o2
  · exfalso
    obtain ⟨x, y, he, _, hnp⟩ := hO
    rcases edgesW _ he with h | h
    · exact hnp (o1 x y h)
    · exact hnp (o2 x y h)
  · obtain ⟨π, hπ, lπ⟩ := lift_piece_path p1 hp1 o1
    obtain ⟨σ, hσ, lσ, labσ⟩ := lift_context_path p2 hp2 o2
    refine ⟨a, b, hab, π, hπ, σ, hσ, fun d hd => only d (s2 _ (labσ d hd)), ?_⟩
    rw [lπ, lσ, lenW]
  · obtain ⟨π, hπ, lπ⟩ := lift_piece_path p2 hp2 o2
    obtain ⟨σ, hσ, lσ, labσ⟩ := lift_context_path p1 hp1 o1
    refine ⟨b, a, Ne.symm hab, π, hπ, σ, hσ,
      fun d hd => (only d (s1 _ (labσ d hd))).symm, ?_⟩
    rw [lπ, lσ, add_comm, lenW]
  · exfalso
    obtain ⟨x, y, he, _, hnc⟩ := hP
    rcases edgesW _ he with h | h
    · exact hnc (o1 x y h)
    · exact hnc (o2 x y h)

/-- **The negative side's arc constraint**: if `glue N O` has no accepted
cycle, then for every `a → b` path of `N` and every `b → a` path of `O` meeting
no other label (not both of length one), the sum of their lengths is not
accepted. -/
theorem negative_arc_constraint {N : BoundaryPiece boundary} {LengthOK : Nat → Prop}
    (neg : ¬ Graph.HasCycleWithLength LengthOK (glue N O)) {a b : boundary.Vertex}
    (π : N.graph.Walk (.inl a) (.inl b)) (hπ : π.IsPath)
    (σ : O.graph.Walk (.inl b) (.inl a)) (hσ : σ.IsPath)
    (lab : ∀ d, (Sum.inl d : boundary.Vertex ⊕ O.Internal) ∈ σ.support → d = a ∨ d = b)
    (hn : 1 < π.length ∨ 1 < σ.length) :
    ¬ LengthOK (π.length + σ.length) := by
  intro ok
  obtain ⟨v, W, hW, hl⟩ := glue_cycle_of_arcs π hπ σ hσ lab hn
  have okW : LengthOK W.length := hl ▸ ok
  exact neg ⟨⟨v, W, hW, okW⟩⟩

/-- **The spectrum split** (generic).  Let `glue P O` carry an accepted cycle,
`glue N O` none, and `P` none on its own.  Then exactly one of:
(i) some accepted cycle is a `P`-path `π : a → b` closed by an `O`-path
`σ : b → a` meeting no other label; then `ℓ = |π|` is a path length of `P`
between `a, b` that `N` does not have, and every `a → b` path of `N` plus `|σ|`
is not accepted;
(ii) every accepted cycle of `glue P O` meets at least three distinct labels. -/
theorem spectrum_split {N : BoundaryPiece boundary} {LengthOK : Nat → Prop}
    (_pos : Graph.HasCycleWithLength LengthOK (glue P O))
    (neg : ¬ Graph.HasCycleWithLength LengthOK (glue N O))
    (pieceFree : ¬ Graph.HasCycleWithLength LengthOK P.pack) :
    (∃ a b : boundary.Vertex, a ≠ b ∧
      ∃ π : P.graph.Walk (.inl a) (.inl b), π.IsPath ∧
      ∃ σ : O.graph.Walk (.inl b) (.inl a), σ.IsPath ∧
        (∀ d, (Sum.inl d : boundary.Vertex ⊕ O.Internal) ∈ σ.support → d = a ∨ d = b) ∧
        LengthOK (π.length + σ.length) ∧ 3 ≤ π.length + σ.length ∧
        ∀ π' : N.graph.Walk (.inl a) (.inl b), π'.IsPath →
          π'.length ≠ π.length ∧
          ((1 < π'.length ∨ 1 < σ.length) → ¬ LengthOK (π'.length + σ.length))) ∨
    (∀ c : Graph.CycleCertificate (glue P O) LengthOK,
      ∃ a b d : boundary.Vertex, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        (Sum.inl a : GluedVertex P O) ∈ c.walk.support ∧
        (Sum.inl b : GluedVertex P O) ∈ c.walk.support ∧
        (Sum.inl d : GluedVertex P O) ∈ c.walk.support) := by
  classical
  have contextFree : ¬ Graph.HasCycleWithLength LengthOK (OutsideContext.pack O) :=
    fun yes => neg (Graph.hasCycleWithLength_of_hom (Graph.contextHom N O)
      (Graph.contextEmbedding N O).injective yes)
  have excl : ∀ c : Graph.CycleCertificate (glue P O) LengthOK,
      DefectGeometry.PieceExclusive c ∧ DefectGeometry.ContextExclusive c := by
    intro c
    refine ⟨DefectGeometry.pieceExclusive c contextFree, ?_⟩
    rcases DefectGeometry.local_or_mixed c with loc | mixed
    · exact (pieceFree (DefectGeometry.local_target c loc)).elim
    · exact mixed
  by_cases two : ∃ c : Graph.CycleCertificate (glue P O) LengthOK,
      ∃ a b : boundary.Vertex, a ≠ b ∧
        (Sum.inl a : GluedVertex P O) ∈ c.walk.support ∧
        (Sum.inl b : GluedVertex P O) ∈ c.walk.support ∧
        ∀ d, (Sum.inl d : GluedVertex P O) ∈ c.walk.support → d = a ∨ d = b
  · left
    obtain ⟨c, a, b, hab, ha, hb, only⟩ := two
    obtain ⟨a', b', hab', π, hπ, σ, hσ, lab, len⟩ :=
      twoLabel_cycle_split c (excl c).1 (excl c).2 hab ha hb only
    have ok : LengthOK (π.length + σ.length) := len ▸ c.length_ok
    have three : 3 ≤ π.length + σ.length := len ▸ c.isCycle.three_le_length
    refine ⟨a', b', hab', π, hπ, σ, hσ, lab, ok, three, fun π' hπ' => ?_⟩
    have cons := fun hn => negative_arc_constraint neg π' hπ' σ hσ lab hn
    refine ⟨fun eq => ?_, cons⟩
    apply cons (by omega)
    rw [eq]; exact ok
  · right
    intro c
    obtain ⟨a, b, hab, ha, hb⟩ :=
      DefectGeometry.twoLabels_of_exclusive c (excl c).1 (excl c).2
    have : ¬ ∀ d, (Sum.inl d : GluedVertex P O) ∈ c.walk.support → d = a ∨ d = b :=
      fun h => two ⟨c, a, b, hab, ha, hb, h⟩
    push Not at this
    obtain ⟨d, hd, hda, hdb⟩ := this
    exact ⟨a, b, d, hab, Ne.symm hda, Ne.symm hdb, ha, hb, hd⟩

end Spectrum

section DeletedAndKept

variable {object : Graph.FiniteObject.{u}}

/-! ## 11. Adding one edge to a cycle-free object: the exact path arithmetic
(generic, no EG vocabulary) -/

section AddEdge

variable {V : Type u} {Gr : SimpleGraph V}

/-- In a path starting at `x`, an edge through `x` is the first edge. -/
theorem path_first_edge {x y a : V} (rv : Gr.Walk x a) (hp : rv.IsPath)
    (he : s(x, y) ∈ rv.edges) :
    ∃ (hxy : Gr.Adj x y) (r : Gr.Walk y a), rv = .cons hxy r := by
  cases rv with
  | nil => simp at he
  | cons h' r =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with h1 | h1
    · have hb := (Sym2.congr_right.1 h1)
      subst hb
      exact ⟨h', r, rfl⟩
    · exact (hp.2 (r.fst_mem_support_of_mem_edges h1)).elim

/-- A cycle at `x` through the edge `xy` yields a path `y → x` avoiding `xy`
with exactly one edge fewer. -/
theorem cycle_through_edge {x y : V} (hxy : x ≠ y) (c : Gr.Walk x x) (hc : c.IsCycle)
    (he : s(x, y) ∈ c.edges) :
    ∃ q : Gr.Walk y x, q.IsPath ∧ s(x, y) ∉ q.edges ∧ q.length + 1 = c.length := by
  cases c with
  | nil => exact (hc.not_nil SimpleGraph.Walk.Nil.nil).elim
  | @cons _ a _ h p =>
    obtain ⟨pp, hnot⟩ := (SimpleGraph.Walk.cons_isCycle_iff p h).1 hc
    by_cases ha : a = y
    · subst ha
      exact ⟨p, pp, hnot, by simp⟩
    · have hep : s(x, y) ∈ p.edges := by
        rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with h1 | h1
        · exact (ha (Sym2.congr_right.1 h1).symm).elim
        · exact h1
      have hep' : s(x, y) ∈ p.reverse.edges := by
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hep
      obtain ⟨hxy', r, hr⟩ := path_first_edge p.reverse pp.reverse hep'
      have rp := pp.reverse
      rw [hr, SimpleGraph.Walk.cons_isPath_iff] at rp
      have rlen : p.reverse.length = r.length + 1 := by rw [hr]; simp
      rw [SimpleGraph.Walk.length_reverse] at rlen
      refine ⟨r.concat h.symm, rp.1.concat rp.2 h.symm, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
        rintro (h1 | h1)
        · exact rp.2 (r.fst_mem_support_of_mem_edges h1)
        · rw [Sym2.eq_iff] at h1
          rcases h1 with ⟨h2, -⟩ | ⟨-, h2⟩
          · exact (h.ne h2).elim
          · exact ha h2.symm
      · simp [SimpleGraph.Walk.length_concat, rlen]

end AddEdge

/-- The object `K + xy`. -/
noncomputable def addEdgeObj (K : FiniteObject.{u}) (x y : K.Vertex) : FiniteObject.{u} where
  Vertex := K.Vertex
  graph := K.graph ⊔ SimpleGraph.edge x y
  vertices := K.vertices
  decideAdj := Classical.decRel _

theorem mem_edgeSet_addEdge {K : FiniteObject.{u}} {x y : K.Vertex} {e : Sym2 K.Vertex}
    (he : e ∈ (addEdgeObj K x y).graph.edgeSet) : e ∈ K.graph.edgeSet ∨ e = s(x, y) := by
  classical
  change e ∈ (K.graph ⊔ SimpleGraph.edge x y).edgeSet at he
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge] at he
  rcases he with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.1 h.1)

/-- **Exact cycle constraint for one added edge.**  If `K` has no accepted
cycle and `K + xy` has one, then `K` has a simple `y → x` path of length `ℓ`
with `ℓ + 1` accepted. -/
theorem addEdge_accepted_path {L : Nat → Prop} (K : FiniteObject.{u}) {x y : K.Vertex}
    (hxy : x ≠ y) (free : ¬ HasCycleWithLength L K)
    (cyc : HasCycleWithLength L (addEdgeObj K x y)) :
    ∃ p : K.graph.Walk y x, p.IsPath ∧ L (p.length + 1) := by
  classical
  obtain ⟨⟨v, w, hw, ok⟩⟩ := cyc
  by_cases he : s(x, y) ∈ w.edges
  · have hx : x ∈ w.support := w.fst_mem_support_of_mem_edges he
    have hc' := hw.rotate hx
    have he' : s(x, y) ∈ (w.rotate x hx).edges :=
      (w.rotate_edges x hx).mem_iff.2 he
    obtain ⟨q, qp, qn, qlen⟩ := cycle_through_edge hxy _ hc' he'
    have hK : ∀ e ∈ q.edges, e ∈ K.graph.edgeSet := by
      intro e hmem
      rcases mem_edgeSet_addEdge (q.edges_subset_edgeSet hmem) with h | h
      · exact h
      · exact (qn (h ▸ hmem)).elim
    refine ⟨q.transfer K.graph hK, qp.transfer hK, ?_⟩
    rw [SimpleGraph.Walk.length_transfer, qlen, SimpleGraph.Walk.length_rotate]
    exact ok
  · have hK : ∀ e ∈ w.edges, e ∈ K.graph.edgeSet := by
      intro e hmem
      rcases mem_edgeSet_addEdge (w.edges_subset_edgeSet hmem) with h | h
      · exact h
      · exact (he (h ▸ hmem)).elim
    exact (free ⟨⟨v, w.transfer K.graph hK, hw.transfer hK, by
      convert ok using 1; exact SimpleGraph.Walk.length_transfer _ _⟩⟩).elim

/-! ## 12. The vertex-deleted graph `G − S` (generic degree bookkeeping) -/

open Classical in
/-- **Degree split.**  `deg_G v = deg_{G−S} v + d_S(v)`, where
`deg_{G−S} v = |N(v) ∖ S|` and `d_S(v) = |N(v) ∩ S|`. -/
theorem degree_split (object : FiniteObject.{u}) (S : Finset object.Vertex)
    (v : object.Vertex) :
    object.degree v = object.localDegree (object.vertexFinset \ S) v +
      object.localDegree S v := by
  classical
  rw [← FiniteObject.localDegree_vertexFinset (object := object) v]
  unfold FiniteObject.localDegree
  have sub : S.filter (fun o => object.graph.Adj v o) ⊆
      object.vertexFinset.filter (fun o => object.graph.Adj v o) :=
    Finset.filter_subset_filter _ (fun o _ => object.mem_vertexFinset o)
  have eq : (object.vertexFinset \ S).filter (fun o => object.graph.Adj v o) =
      object.vertexFinset.filter (fun o => object.graph.Adj v o) \
        S.filter (fun o => object.graph.Adj v o) := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have key := Finset.card_sdiff_add_card_eq_card sub
  rw [← eq] at key
  convert key.symm using 3 <;> (ext o; simp)

open Classical in
/-- **Per-vertex deficit in `G − S`, exact.**  For `v` with `deg_G v ≥ 3`:
`3 − deg_{G−S} v = d_S(v) − (deg_G v − 3)` (truncated subtraction). -/
theorem deleted_deficit_eq (object : FiniteObject.{u}) (S : Finset object.Vertex)
    (v : object.Vertex) (base : 3 ≤ object.degree v) :
    3 - object.localDegree (object.vertexFinset \ S) v =
      object.localDegree S v - (object.degree v - 3) := by
  have := degree_split object S v
  omega

open Classical in
/-- Deficit bounds: `3 − deg_{G−S} v ≤ d_S(v)`, with equality when
`deg_G v = 3`; and a positive deficit forces `d_S(v) ≥ 1`. -/
theorem deleted_deficit_bounds (object : FiniteObject.{u}) (S : Finset object.Vertex)
    (v : object.Vertex) (base : 3 ≤ object.degree v) :
    3 - object.localDegree (object.vertexFinset \ S) v ≤ object.localDegree S v ∧
    (object.degree v = 3 →
      3 - object.localDegree (object.vertexFinset \ S) v = object.localDegree S v) ∧
    (object.localDegree (object.vertexFinset \ S) v < 3 → 1 ≤ object.localDegree S v) := by
  have := degree_split object S v
  refine ⟨by omega, fun h => by omega, fun h => by omega⟩

open Classical in
/-- **Total deficit of `G − S`.**  With `T = V ∖ S` and every degree `≥ 3`:
`Σ_{v∈T} (3 − deg_{G−S} v) = Σ_{v∈T} (d_S(v) − (deg_G v − 3)) ≤ e(S, T)`,
where `e(S, T) = Σ_{v∈T} d_S(v)`; equality holds when every `v ∈ T` with a
neighbour in `S` has `deg_G v = 3`. -/
theorem deleted_total_deficit (object : FiniteObject.{u}) (S : Finset object.Vertex)
    (base : ∀ v, 3 ≤ object.degree v) :
    ((object.vertexFinset \ S).sum fun v =>
        3 - object.localDegree (object.vertexFinset \ S) v) =
      ((object.vertexFinset \ S).sum fun v =>
        object.localDegree S v - (object.degree v - 3)) ∧
    ((object.vertexFinset \ S).sum fun v =>
        3 - object.localDegree (object.vertexFinset \ S) v) ≤
      ((object.vertexFinset \ S).sum fun v => object.localDegree S v) ∧
    ((∀ v ∈ object.vertexFinset \ S, 0 < object.localDegree S v → object.degree v = 3) →
      ((object.vertexFinset \ S).sum fun v =>
        3 - object.localDegree (object.vertexFinset \ S) v) =
      ((object.vertexFinset \ S).sum fun v => object.localDegree S v)) := by
  refine ⟨Finset.sum_congr rfl fun v _ => deleted_deficit_eq object S v (base v),
    Finset.sum_le_sum fun v _ => (deleted_deficit_bounds object S v (base v)).1,
    fun tight3 => Finset.sum_congr rfl fun v hv => ?_⟩
  by_cases h : 0 < object.localDegree S v
  · exact (deleted_deficit_bounds object S v (base v)).2.1 (tight3 v hv h)
  · have := degree_split object S v
    have := base v
    omega

open Classical in
/-- `G − S` is a proper induced subgraph when `S` is nonempty. -/
theorem deleted_card_lt (object : FiniteObject.{u}) {S : Finset object.Vertex}
    (ne : S.Nonempty) : (object.vertexFinset \ S).card < object.vertexCount := by
  obtain ⟨s, hs⟩ := ne
  rw [← FiniteObject.card_vertexFinset]
  exact Finset.card_lt_card ⟨Finset.sdiff_subset, fun h =>
    (Finset.mem_sdiff.1 (h (object.mem_vertexFinset s))).2 hs⟩

open Classical in
/-- **Minimality at `G − S`.**  Under `NoProperBaseline` (threshold 3), for a
nonempty `S` with `V ∖ S` nonempty, some `v ∈ V ∖ S` has `deg_{G−S} v < 3`
(hence `d_S(v) ≥ 1`). -/
theorem deleted_exists_deficient (object : FiniteObject.{u}) {S : Finset object.Vertex}
    (noProper : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value)
    (ne : S.Nonempty) {t : object.Vertex} (ht : t ∉ S) :
    ∃ v ∈ object.vertexFinset \ S,
      object.localDegree (object.vertexFinset \ S) v < 3 := by
  classical
  have not3 := noProper (ProperSubgraph.ofInducedSupport object
    (object.vertexFinset \ S) (deleted_card_lt object ne))
  change ¬ MinimumDegreeAtLeast 3 (object.induce (object.vertexFinset \ S)) at not3
  by_contra hcon
  push Not at hcon
  haveI : Nonempty (object.induce (object.vertexFinset \ S)).Vertex :=
    ⟨⟨t, Finset.mem_sdiff.2 ⟨object.mem_vertexFinset t, ht⟩⟩⟩
  apply not3
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro v
  rw [FiniteObject.degree_induce_eq_localDegree]
  exact hcon v.1 v.2

/-- A general added-edge set: `K ⊔ F`. -/
noncomputable def addEdgesObj (K : FiniteObject.{u}) (F : SimpleGraph K.Vertex) :
    FiniteObject.{u} where
  Vertex := K.Vertex
  graph := K.graph ⊔ F
  vertices := K.vertices
  decideAdj := Classical.decRel _

/-- **Cycle constraint for any added-edge set.**  If `K` has no accepted
cycle, every accepted cycle of `K ⊔ F` uses an edge of `F` not in `K`. -/
theorem addEdges_cycle_uses_new {L : Nat → Prop} (K : FiniteObject.{u})
    (F : SimpleGraph K.Vertex) (free : ¬ HasCycleWithLength L K)
    (c : CycleCertificate (addEdgesObj K F) L) :
    ∃ e ∈ c.walk.edges, e ∈ F.edgeSet ∧ e ∉ K.graph.edgeSet := by
  by_contra hcon
  push Not at hcon
  have hK : ∀ e ∈ c.walk.edges, e ∈ K.graph.edgeSet := by
    intro e he
    have h := c.walk.edges_subset_edgeSet he
    change e ∈ (K.graph ⊔ F).edgeSet at h
    rw [SimpleGraph.edgeSet_sup] at h
    rcases h with h | h
    · exact h
    · by_contra hn; exact hn (hcon e he h) |>.elim
  exact free ⟨⟨c.vertex, c.walk.transfer K.graph hK, c.isCycle.transfer hK, by
    convert c.length_ok using 1; exact SimpleGraph.Walk.length_transfer _ _⟩⟩

/-! ## 13. The keeps-all split (generic over any object and support) -/

section KeepsAll

open SupportAtom

/-- `glue(ret_X, G − Z)` keeps every edge of G. -/
def KeepsAll (Z X : Finset object.Vertex) : Prop :=
  ∀ a b : (glue (retainedPiece object Z X) (outside object Z)).Vertex,
    object.graph.Adj (retainedGlueHom Z X a) (retainedGlueHom Z X b) →
    (glue (retainedPiece object Z X) (outside object Z)).graph.Adj a b

/-- Every edge of `G[Z]` not inside `X` joins two boundary vertices. -/
def DroppedAreBoundary (Z X : Finset object.Vertex) : Prop :=
  ∀ u v, u ∈ Z → v ∈ Z → object.graph.Adj u v → ¬ (u ∈ X ∧ v ∈ X) →
    u ∈ cutBoundary object Z ∧ v ∈ cutBoundary object Z

theorem retainedGlueHom_pieceEmbedding (Z X : Finset object.Vertex)
    (p : (boundary object Z).Vertex ⊕ PieceInternal object Z) :
    retainedGlueHom Z X (pieceEmbedding (retainedPiece object Z X) (outside object Z) p) =
      pieceDecode object Z p := by
  rcases p with p | p <;> rfl

theorem retainedGlueHom_contextEmbedding (Z X : Finset object.Vertex)
    (p : (boundary object Z).Vertex ⊕ OutsideInternal object Z) :
    retainedGlueHom Z X (contextEmbedding (retainedPiece object Z X) (outside object Z) p) =
      outsideDecode object Z p := by
  rcases p with p | p <;> rfl

theorem retained_adj_of {Z X : Finset object.Vertex}
    {p q : (boundary object Z).Vertex ⊕ PieceInternal object Z}
    (h : object.graph.Adj (pieceDecode object Z p) (pieceDecode object Z q))
    (hp : pieceDecode object Z p ∈ X) (hq : pieceDecode object Z q ∈ X) :
    (retainedPiece object Z X).graph.Adj p q := by
  refine ⟨h, ?_⟩
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
  exact ⟨h.ne, Or.inl ⟨hp, hq⟩⟩

theorem mem_of_retained_adj {Z X : Finset object.Vertex}
    {p q : (boundary object Z).Vertex ⊕ PieceInternal object Z}
    (h : (retainedPiece object Z X).graph.Adj p q) :
    pieceDecode object Z p ∈ X ∧ pieceDecode object Z q ∈ X := by
  obtain ⟨-, h2⟩ := h
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at h2
  rcases h2 with ⟨-, hh | hh⟩
  · exact hh
  · exact ⟨hh.2, hh.1⟩

/-- Encoding of a G-vertex into the gluing. -/
noncomputable def glueEncode (Z X : Finset object.Vertex) (v : object.Vertex) :
    (glue (retainedPiece object Z X) (outside object Z)).Vertex := by
  classical
  exact if hb : v ∈ cutBoundary object Z then .inl ⟨v, hb⟩
    else if hz : v ∈ Z then .inr (.inl ⟨v, hz, hb⟩) else .inr (.inr ⟨v, hz⟩)

theorem retainedGlueHom_encode (Z X : Finset object.Vertex) (v : object.Vertex) :
    retainedGlueHom Z X (glueEncode Z X v) = v := by
  classical
  unfold glueEncode
  split_ifs <;> rfl

/-- **The keeps-all characterization.**  `glue(ret_X, G − Z)` keeps every
G-edge iff every edge of `G[Z]` not inside `X` joins two `∂Z` vertices. -/
theorem keepsAll_iff (Z X : Finset object.Vertex) :
    KeepsAll Z X ↔ DroppedAreBoundary Z X := by
  constructor
  · intro keep u v hu hv adj notX
    have ga := keep (glueEncode Z X u) (glueEncode Z X v)
      (by rw [retainedGlueHom_encode, retainedGlueHom_encode]; exact adj)
    rcases (glueGraph_adj_iff _ _ _ _).1 ga with
      ⟨pl, pr, padj, el, er⟩ | ⟨cl, cr, _, el, er⟩
    · have eu := congrArg (retainedGlueHom Z X) el
      have ev := congrArg (retainedGlueHom Z X) er
      rw [retainedGlueHom_pieceEmbedding, retainedGlueHom_encode] at eu ev
      have := mem_of_retained_adj padj
      rw [eu, ev] at this
      exact (notX this).elim
    · have eu := congrArg (retainedGlueHom Z X) el
      have ev := congrArg (retainedGlueHom Z X) er
      rw [retainedGlueHom_contextEmbedding, retainedGlueHom_encode] at eu ev
      constructor
      · rcases cl with b | o
        · rw [← eu]; exact b.2
        · exact (o.2 (by change o.1 = u at eu; rw [eu]; exact hu)).elim
      · rcases cr with b | o
        · rw [← ev]; exact b.2
        · exact (o.2 (by change o.1 = v at ev; rw [ev]; exact hv)).elim
  · intro D a b adj
    have bZ : ∀ x : (boundary object Z).Vertex, x.1 ∈ Z := fun x =>
      ((mem_cutBoundary_iff object Z x.1).1 x.2).1
    have ctx : ∀ p q : (boundary object Z).Vertex ⊕ OutsideInternal object Z,
        object.graph.Adj (outsideDecode object Z p) (outsideDecode object Z q) →
        (glue (retainedPiece object Z X) (outside object Z)).graph.Adj
          (contextEmbedding _ _ p) (contextEmbedding _ _ q) := fun p q h =>
      (glueGraph_adj_iff _ _ _ _).2 (Or.inr ⟨p, q, h, rfl, rfl⟩)
    have pc : ∀ p q : (boundary object Z).Vertex ⊕ PieceInternal object Z,
        object.graph.Adj (pieceDecode object Z p) (pieceDecode object Z q) →
        (p.isRight ∨ q.isRight) →
        (glue (retainedPiece object Z X) (outside object Z)).graph.Adj
          (pieceEmbedding _ _ p) (pieceEmbedding _ _ q) := by
      intro p q h hint
      refine (glueGraph_adj_iff _ _ _ _).2 (Or.inl ⟨p, q, ?_, rfl, rfl⟩)
      by_cases hX : pieceDecode object Z p ∈ X ∧ pieceDecode object Z q ∈ X
      · exact retained_adj_of h hX.1 hX.2
      · have := D _ _ (pieceDecode_mem object Z p) (pieceDecode_mem object Z q) h hX
        exfalso
        rcases p with p | p <;> rcases q with q | q
        · simp at hint
        · exact q.2.2 this.2
        · exact p.2.2 this.1
        · exact p.2.2 this.1
    rcases a with a | a | a <;> rcases b with b | b | b
    · exact ctx (.inl a) (.inl b) adj
    · exact pc (.inl a) (.inr b) adj (by simp)
    · exact ctx (.inl a) (.inr b) adj
    · exact pc (.inr a) (.inl b) adj (by simp)
    · exact pc (.inr a) (.inr b) adj (by simp)
    · exact (not_adj_pieceInternal_outside object Z a b adj).elim
    · exact ctx (.inr a) (.inl b) adj
    · exact (not_adj_pieceInternal_outside object Z b a adj.symm).elim
    · exact ctx (.inr a) (.inr b) adj

end KeepsAll

end DeletedAndKept

section PairArm

variable {G : Graph.FiniteObject.{u}}

end PairArm

section PairArm

variable {G : Graph.FiniteObject.{u}}

open SupportAtom in
/-- Monotone transfer of a positive response along `ret_X ≤ ret_Y`. -/
theorem glue_mono_of_le {Z X Y : Finset G.Vertex}
    (le : (retainedPiece G Z X).graph ≤ (retainedPiece G Z Y).graph)
    (O : OutsideContext (boundary G Z)) {L : Nat → Prop}
    (cyc : HasCycleWithLength L (glue (retainedPiece G Z X) O)) :
    HasCycleWithLength L (glue (retainedPiece G Z Y) O) := by
  have le' : glueGraph (retainedPiece G Z X) O ≤ glueGraph (retainedPiece G Z Y) O :=
    glueGraph_mono (piece := retainedPiece G Z Y) O
      (retainedPiece G Z X).graph (retainedPiece G Z X).decideAdj le
  exact hasCycleWithLength_of_hom (left := glue (retainedPiece G Z X) O)
    (right := glue (retainedPiece G Z Y) O) ⟨id, fun h => le' h⟩
    Function.injective_id cyc

open Classical SupportAtom in
/-- **Pair arm, generic.**  If `Z = ∂Z = {a, b}` and two readings on `Z` have
equal boundary-degree profiles, then `ret_X ≤ ret_Y` (so, by symmetry, the
readings have the same graph). -/
theorem pair_le {Z X Y : Finset G.Vertex} {a b : G.Vertex}
    (hZ : Z = {a, b}) (hB : cutBoundary G Z = {a, b})
    (prof : (retainedPiece G Z X).boundaryDegreeProfile =
      (retainedPiece G Z Y).boundaryDegreeProfile) :
    (retainedPiece G Z X).graph ≤ (retainedPiece G Z Y).graph := by
  classical
  have noInt : ∀ i : PieceInternal G Z, False := by
    intro i
    have h1 : i.1 ∈ ({a, b} : Finset G.Vertex) := (Finset.ext_iff.1 hZ i.1).1 i.2.1
    exact i.2.2 ((Finset.ext_iff.1 hB i.1).2 h1)
  have inB : ∀ x : (boundary G Z).Vertex, x.1 = a ∨ x.1 = b := by
    intro x
    have : x.1 ∈ ({a, b} : Finset G.Vertex) := (Finset.ext_iff.1 hB x.1).1 x.2
    simpa using this
  intro p q hpq
  rcases p with x | i
  swap; · exact (noInt i).elim
  rcases q with y | i
  swap; · exact (noInt i).elim
  have posX : 0 < (retainedPiece G Z X).pack.degree (.inl x) :=
    degree_pos_of_adj (retainedPiece G Z X).pack hpq
  have eq : (retainedPiece G Z X).pack.degree (.inl x) =
      (retainedPiece G Z Y).pack.degree (.inl x) := congrFun prof x
  have posY : 0 < (retainedPiece G Z Y).pack.degree (.inl x) := eq ▸ posX
  letI : FinEnum (retainedPiece G Z Y).pack.Vertex := (retainedPiece G Z Y).pack.vertices
  rw [FiniteObject.degree_eq_ncard_neighborSet] at posY
  obtain ⟨z, hz⟩ := (Set.ncard_pos (Set.toFinite _)).1 posY
  rcases z with z | i
  swap; · exact (noInt i).elim
  have nxy : x ≠ y := fun h => (retainedPiece G Z X).graph.ne_of_adj hpq (by rw [h])
  have nxz : x ≠ z := fun h => (retainedPiece G Z Y).graph.ne_of_adj hz (by rw [h])
  have yz : y = z := by
    apply Subtype.ext
    have hx := inB x
    have hy := inB y
    have hz' := inB z
    have n1 : x.1 ≠ y.1 := fun h => nxy (Subtype.ext h)
    have n2 : x.1 ≠ z.1 := fun h => nxz (Subtype.ext h)
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz' with hz' | hz' <;>
      simp_all
  subst yz
  exact hz

/-- **Two labels cannot carry a three-label cycle.** -/
theorem armII_two_false {Z : Finset G.Vertex}
    {P : BoundaryPiece (SupportAtom.boundary G Z)}
    {O : OutsideContext (SupportAtom.boundary G Z)} {L : Nat → Prop}
    (two : (SupportAtom.cutBoundary G Z).card = 2)
    (pos : HasCycleWithLength L (glue P O))
    (many : ∀ c : Graph.CycleCertificate (glue P O) L,
      ∃ a b d : (SupportAtom.boundary G Z).Vertex,
        a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        (Sum.inl a : GluedVertex P O) ∈ c.walk.support ∧
        (Sum.inl b : GluedVertex P O) ∈ c.walk.support ∧
        (Sum.inl d : GluedVertex P O) ∈ c.walk.support) : False := by
  classical
  obtain ⟨c⟩ := pos
  obtain ⟨a, b, d, hab, had, hbd, -⟩ := many c
  have sub : ({a.1, b.1, d.1} : Finset G.Vertex) ⊆ SupportAtom.cutBoundary G Z := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact a.2
    · exact b.2
    · exact d.2
  have c3 : ({a.1, b.1, d.1} : Finset G.Vertex).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a.1, b.1, d.1, fun h => hab (Subtype.ext h), fun h => had (Subtype.ext h),
      fun h => hbd (Subtype.ext h), rfl⟩
  have := Finset.card_le_card sub
  omega


end PairArm

section TwoBoundary

open Classical

variable (object : Graph.FiniteObject.{u})

/-- **Generic separation**: a walk from an interior vertex of `S` (in `S`, not
on `∂S`) to a vertex outside `S` visits `∂S`. -/
theorem walk_from_interior_meets_boundary (S : Finset object.Vertex)
    {i x : object.Vertex} (walk : object.graph.Walk i x)
    (hi : i ∈ S) (hib : i ∉ SupportAtom.cutBoundary object S) (hx : x ∉ S) :
    ∃ v ∈ walk.support, v ∈ SupportAtom.cutBoundary object S := by
  obtain ⟨d, hd, dIn, dOut⟩ := walk.exists_boundary_dart
    ({y | y ∈ S ∧ y ∉ SupportAtom.cutBoundary object S} : Set object.Vertex)
    ⟨hi, hib⟩ (fun h => hx h.1)
  simp only [Set.mem_setOf_eq, not_and, not_not] at dIn dOut
  have sndS : d.snd ∈ S := by
    by_contra h
    exact dIn.2 ((SupportAtom.mem_cutBoundary_iff object S d.fst).2
      ⟨dIn.1, d.snd, d.adj, h⟩)
  exact ⟨d.snd, walk.dart_snd_mem_support_of_mem_darts hd, dOut sndS⟩

/-- **Generic exact split at `|∂S| = 2`**: `∂S = {a, b}` and either `S = {a, b}`
or `S` has an interior vertex and every walk from the interior to the outside
passes through `a` or `b` (`{a, b}` separates). -/
theorem two_boundary_split (S : Finset object.Vertex)
    (two : (SupportAtom.cutBoundary object S).card = 2) :
    ∃ a b, a ≠ b ∧ SupportAtom.cutBoundary object S = {a, b} ∧
      (S = {a, b} ∨
        ((∃ i ∈ S, i ∉ SupportAtom.cutBoundary object S) ∧
          ∀ i ∈ S, i ∉ SupportAtom.cutBoundary object S → ∀ x, x ∉ S →
            ∀ walk : object.graph.Walk i x, a ∈ walk.support ∨ b ∈ walk.support)) := by
  obtain ⟨a, b, ab, hab⟩ := Finset.card_eq_two.mp two
  refine ⟨a, b, ab, hab, ?_⟩
  by_cases interior : ∃ i ∈ S, i ∉ SupportAtom.cutBoundary object S
  · refine Or.inr ⟨interior, ?_⟩
    intro i hi hib x hx walk
    obtain ⟨v, hv, vB⟩ := walk_from_interior_meets_boundary object S walk hi hib hx
    rw [hab] at vB
    simp only [Finset.mem_insert, Finset.mem_singleton] at vB
    rcases vB with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · left
    push Not at interior
    apply Finset.Subset.antisymm
    · intro v hv
      rw [← hab]
      exact interior v hv
    · rw [← hab]
      intro v hv
      exact ((SupportAtom.mem_cutBoundary_iff object S v).1 hv).1

end TwoBoundary

end Hypostructure.Graph.GluedReadings
