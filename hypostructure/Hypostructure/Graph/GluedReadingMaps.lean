import Hypostructure.Graph.InterfaceReplacement
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
# Readings of a support of G: maps into G and G's own structure around `Z`

Let `Z` be a vertex support of a finite object `G`, `∂Z` its cut boundary and
`ret_X` the piece of `Z` that keeps only the edges with both ends in `X`.

* `glue (ret_X) (G − Z)` and `ret_X` embed injectively into `G`
  (`retainedGlueHom`, `readingHom`), so both inherit every cycle obstruction of
  `G`.
* Degree bookkeeping of `G` around `Z`, the shape of a support with one
  boundary vertex, the two-boundary separation and closures on G's outside
  side, one added edge to a cycle-free object, the vertex-deleted graph `G − S`,
  and the keeps-all split.

The only outside is G's own `G − Z`; no other boundaried context is read.
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

section PositiveLabels

variable {G : Graph.FiniteObject.{u}} {Z X : Finset G.Vertex}

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
