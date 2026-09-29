import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.Target
import Hypostructure.Graph.DeletionCriticality
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Transplanting a reading into its support, and linkage inclusion

Let `G` be a finite object, `Z` a vertex support with cut boundary `∂Z`, and
`G − Z` G's own surroundings (`SupportAtom.outside G Z`).  Every construction
below is on `∂Z`'s own labels, so the boundary-label bijection between a
`∂Z`-piece and G's piece `G[Z]` is the identity of `∂Z`.

* **Linkage inclusion** (`LinkageIncluded X`), for an arbitrary `∂Z`-piece `X`:
  every linkage of `X` -- a set of its edges in which every vertex has at most
  two neighbours and every interior vertex none or two, i.e. a family of
  internally disjoint `∂Z`-to-`∂Z` paths together with closed components -- is
  realized in `G[Z]`: an injective relabelling `φ` of its interior vertices into
  the interior of `Z`, fixing `∂Z`, sends each linkage edge to an edge of `G`.
  The image is a family in `G[Z]` with the same endpoint pairs and the same
  lengths, again internally disjoint.
* **The key lemma** (`cycle_transfer`): under linkage inclusion every cycle of
  `glue X (G − Z)` maps to a cycle of `G` of the same length.  Hence a
  target-avoiding `G` gives `¬ Target (glue X (G − Z))`
  (`not_target_of_linkageIncluded`), and a minimal `G` forbids a strictly
  smaller such gluing with the baseline (`not_vertexCount_lt_of_minimal`,
  `internalVertexCount_le_of_minimal`).
* **The transplant of a reading** (`transplant G Z Y`): the `∂Z`-piece whose
  interior is `int(Z) ∩ Y` and whose edges are those of `G` among
  `∂Z ∪ (int(Z) ∩ Y)`.  It is not a reading of `G` (its interior is smaller than
  `G[Z]`'s), and its gluing into `G − Z` is `G` with the removed set
  `D = int(Z) ∖ Y` deleted.  Its four replacement conditions are exact:
  (i) the profile of `G[Z]` iff no boundary vertex of `Z` has a neighbour in `D`
  (`transplant_profile_eq_iff`); (ii) the baseline iff every kept vertex keeps
  at least `threshold` neighbours outside `D` (`transplant_baseline_iff`);
  (iii) its interior is at most `int(Z)` (`transplant_internalVertexCount_le`);
  (iv) linkage inclusion holds (`transplant_linkageIncluded`).
* **Size equality from minimality** (`transplant_fills_of_baseline`,
  `transplant_size_eq`): on a minimal target-avoiding `G`, a transplant with
  the baseline fills `int(Z)`; otherwise the transplant is a strictly smaller
  baseline object without a target cycle.  The exact failure
  (`transplant_exact`): either `D = ∅`, or the canonical deficient vertex
  (`transplantDeficit`, the first kept vertex in `G`'s order with fewer than
  `threshold` kept neighbours) exists, lies in `Z`, and has a neighbour in `D`.
* **The equal-count bijection** (`contactEquiv`): equal reading counts at a
  boundary label are an explicit bijection between the two readings' contacts
  at that label.

Every statement is about an arbitrary finite object; nothing here knows a
presentation, a ledger, or a manuscript.
-/

namespace Hypostructure.Graph.Transplant

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## Generic counting helpers -/

/-- Degree in a pulled-back graph along an injective map. -/
theorem ncard_neighborSet_comap {α β : Type*} (G : SimpleGraph β) (d : α → β)
    (hd : Function.Injective d) (x : α) :
    ((G.comap d).neighborSet x).ncard = {w | G.Adj (d x) w ∧ w ∈ Set.range d}.ncard := by
  rw [← Set.ncard_image_of_injective _ hd]
  congr 1
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y, rfl⟩
  · rintro ⟨h, y, rfl⟩
    exact ⟨y, h, rfl⟩

/-- An injective, non-surjective vertex map strictly decreases the vertex count. -/
theorem vertexCount_lt_of_injective {A B : FiniteObject.{u}} (f : A.Vertex → B.Vertex)
    (hf : Function.Injective f) (hs : ¬ Function.Surjective f) :
    A.vertexCount < B.vertexCount := by
  letI : FinEnum A.Vertex := A.vertices
  letI : FinEnum B.Vertex := B.vertices
  change FinEnum.card A.Vertex < FinEnum.card B.Vertex
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_lt_of_injective_not_surjective f hf hs

/-- In a cycle, the edges at a vertex go to exactly two distinct neighbours. -/
theorem cycle_two_neighbours {V : Type*} {G : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) {w a : V} (ha : s(w, a) ∈ p.edges) :
    ∃ x y, x ≠ y ∧ ∀ c, s(w, c) ∈ p.edges ↔ c = x ∨ c = y := by
  have hw : w ∈ p.support := p.fst_mem_support_of_mem_edges ha
  obtain ⟨x, y, hxy, hset⟩ :=
    Set.ncard_eq_two.1 (hp.ncard_neighborSet_toSubgraph_eq_two hw)
  refine ⟨x, y, hxy, fun c => ?_⟩
  have key : s(w, c) ∈ p.edges ↔ c ∈ p.toSubgraph.neighborSet w := by
    rw [SimpleGraph.Subgraph.mem_neighborSet, ← SimpleGraph.Subgraph.mem_edgeSet,
      SimpleGraph.Walk.mem_edges_toSubgraph]
  rw [key, hset]
  simp

/-- A vertex of a cycle has a cycle edge. -/
theorem cycle_edge_of_mem_support {V : Type*} {G : SimpleGraph V} {u : V}
    {p : G.Walk u u} (hp : p.IsCycle) {w : V} (hw : w ∈ p.support) :
    ∃ a, s(w, a) ∈ p.edges := by
  have two := hp.ncard_neighborSet_toSubgraph_eq_two hw
  obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (s := p.toSubgraph.neighborSet w)
    (by rw [two]; decide)
  refine ⟨a, ?_⟩
  rw [← SimpleGraph.Walk.mem_edges_toSubgraph, SimpleGraph.Subgraph.mem_edgeSet]
  exact ha

section Linkage

variable {object : FiniteObject.{u}} {Z : Finset object.Vertex}

/-- A vertex of a `∂Z`-piece sent to `G` by a relabelling `φ` of its interior;
the boundary labels go to their own vertex of `∂Z` (the identity bijection of
labels). -/
def realize {X : BoundaryPiece (SupportAtom.boundary object Z)}
    (φ : X.Internal → object.Vertex) :
    (SupportAtom.boundary object Z).Vertex ⊕ X.Internal → object.Vertex
  | .inl b => b.1
  | .inr x => φ x

/-- **A linkage of a `∂Z`-piece `X`**: a set `L` of edges of `X` in which every
vertex has at most two neighbours and every interior vertex has none or two.
Its components are internally disjoint paths whose ends lie on `∂Z`, and
closed components. -/
structure IsLinkage (X : BoundaryPiece (SupportAtom.boundary object Z))
    (L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ X.Internal)) : Prop where
  le : L ≤ X.graph
  atMostTwo : ∀ v a b c, L.Adj v a → L.Adj v b → L.Adj v c → a = b ∨ a = c ∨ b = c
  internalTwo : ∀ x a, L.Adj (.inr x) a → ∃ b, b ≠ a ∧ L.Adj (.inr x) b

/-- **A linkage realized in `G[Z]`**: an injective relabelling `φ` of the
linkage's interior vertices into the interior of `Z`, fixing `∂Z`, that sends
every linkage edge to an edge of `G`.  The image is a family of paths of
`G[Z]` with the same endpoint pairs and the same lengths, internally disjoint. -/
def LinkageRealized (X : BoundaryPiece (SupportAtom.boundary object Z))
    (L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ X.Internal)) : Prop :=
  ∃ φ : X.Internal → object.Vertex,
    (∀ x a, L.Adj (.inr x) a → φ x ∈ Z ∧ φ x ∉ SupportAtom.cutBoundary object Z) ∧
    (∀ x y a c, L.Adj (.inr x) a → L.Adj (.inr y) c → φ x = φ y → x = y) ∧
    (∀ a c, L.Adj a c → object.graph.Adj (realize φ a) (realize φ c))

/-- **Linkage inclusion**: every linkage of `X` is realized in `G[Z]`. -/
def LinkageIncluded (X : BoundaryPiece (SupportAtom.boundary object Z)) : Prop :=
  ∀ L, IsLinkage X L → LinkageRealized X L

/-- **Key lemma: under linkage inclusion every cycle of `glue X (G − Z)` maps to
a cycle of `G` of the same length.**  The edges of the cycle owned by `X` form a
linkage of `X`; its realization, with the identity on `∂Z` and on `G − Z`, is
injective on the cycle and sends each cycle edge to an edge of `G`. -/
theorem cycle_transfer {X : BoundaryPiece (SupportAtom.boundary object Z)}
    (included : LinkageIncluded X) {LengthOK : Nat → Prop}
    (cycle : CycleCertificate (glue X (SupportAtom.outside object Z)) LengthOK) :
    Nonempty (CycleCertificate object LengthOK) := by
  classical
  set O := SupportAtom.outside object Z
  set H := glue X O
  obtain ⟨v, C, hC, hlen⟩ := cycle
  let pe := pieceEmbedding X O
  -- the linkage of `X` cut out by the cycle
  let L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ X.Internal) :=
    { Adj := fun a c => X.graph.Adj a c ∧ s(pe a, pe c) ∈ C.edges
      symm := ⟨fun a c ⟨h, e⟩ => ⟨h.symm, by rwa [Sym2.eq_swap]⟩⟩
      loopless := ⟨fun a ⟨h, _⟩ => X.graph.loopless.irrefl a h⟩ }
  -- a glue neighbour of an interior vertex of `X` is a vertex of `X`, by an `X`-edge
  have interiorNeighbour : ∀ (x : X.Internal) (c : H.Vertex),
      H.graph.Adj (pe (.inr x)) c → ∃ c', X.graph.Adj (.inr x) c' ∧ pe c' = c := by
    intro x c adj
    rcases (glueGraph_adj_iff X O _ _).1 adj with ⟨pl, pr, h, hl, hr⟩ | ⟨cl, cr, _, hl, _⟩
    · have : pl = .inr x := (pieceEmbedding X O).injective hl
      subst this
      exact ⟨pr, h, hr⟩
    · rcases cl with cl | cl <;> cases hl
  have linkage : IsLinkage X L := by
    refine ⟨fun a c h => h.1, ?_, ?_⟩
    · intro w a b c ha hb hc
      obtain ⟨x, y, _, hxy⟩ := cycle_two_neighbours hC ha.2
      have ea := (hxy _).1 ha.2
      have eb := (hxy _).1 hb.2
      have ec := (hxy _).1 hc.2
      have inj := (pieceEmbedding X O).injective
      rcases ea with ea | ea <;> rcases eb with eb | eb <;> rcases ec with ec | ec
      all_goals first
        | exact Or.inl (inj (ea.trans eb.symm))
        | exact Or.inr (Or.inl (inj (ea.trans ec.symm)))
        | exact Or.inr (Or.inr (inj (eb.trans ec.symm)))
    · intro x a ha
      obtain ⟨p, q, hpq, hset⟩ := cycle_two_neighbours hC ha.2
      have ea := (hset _).1 ha.2
      -- the other cycle neighbour of `x`
      have other : ∃ c, c ≠ pe a ∧ s(pe (.inr x), c) ∈ C.edges := by
        rcases ea with ea | ea
        · exact ⟨q, fun h => hpq (ea.symm.trans h.symm), (hset q).2 (Or.inr rfl)⟩
        · exact ⟨p, fun h => hpq (h.trans ea), (hset p).2 (Or.inl rfl)⟩
      obtain ⟨c, hc, hce⟩ := other
      obtain ⟨c', hadj, rfl⟩ := interiorNeighbour x c (C.adj_of_mem_edges hce)
      exact ⟨c', fun h => hc (by rw [h]), hadj, hce⟩
  obtain ⟨φ, inZ, injOn, adjOK⟩ := included L linkage
  -- the vertex map of the glued graph into `G`
  let ψ : H.Vertex → object.Vertex := fun a =>
    match a with
    | .inl b => b.1
    | .inr (.inl x) => φ x
    | .inr (.inr o) => o.1
  have ψ_pe : ∀ a, ψ (pe a) = realize φ a := by
    intro a
    rcases a with b | x <;> rfl
  have ψ_ce : ∀ a, ψ (contextEmbedding X O a) = SupportAtom.outsideDecode object Z a := by
    intro a
    rcases a with b | o <;> rfl
  -- every vertex of `X`'s interior on the cycle is active in the linkage
  have active : ∀ x : X.Internal, pe (.inr x) ∈ C.support → ∃ a, L.Adj (.inr x) a := by
    intro x hx
    obtain ⟨c, hc⟩ := cycle_edge_of_mem_support hC hx
    obtain ⟨c', hadj, rfl⟩ := interiorNeighbour x c (C.adj_of_mem_edges hc)
    exact ⟨c', hadj, hc⟩
  -- cycle edges go to edges of `G`
  have edgeOK : ∀ a c, s(a, c) ∈ C.edges → object.graph.Adj (ψ a) (ψ c) := by
    intro a c hac
    rcases (glueGraph_adj_iff X O a c).1 (C.adj_of_mem_edges hac) with
      ⟨pl, pr, h, rfl, rfl⟩ | ⟨cl, cr, h, rfl, rfl⟩
    · rw [ψ_pe, ψ_pe]
      exact adjOK pl pr ⟨h, hac⟩
    · rw [ψ_ce, ψ_ce]
      exact h
  -- `ψ` is injective on the cycle
  have boundaryZ : ∀ b : (SupportAtom.boundary object Z).Vertex, b.1 ∈ Z := fun b =>
    ((SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2).1
  have injS : ∀ a c, a ∈ C.support → c ∈ C.support → ψ a = ψ c → a = c := by
    intro a c ha hc eq
    rcases a with b | (x | o) <;> rcases c with b' | (y | o')
    · exact congrArg Sum.inl (Subtype.ext eq)
    · change b.1 = φ y at eq
      obtain ⟨a', ha'⟩ := active y hc
      exact absurd (show φ y ∈ SupportAtom.cutBoundary object Z from eq ▸ b.2)
        (inZ y a' ha').2
    · change b.1 = o'.1 at eq
      exact absurd (show o'.1 ∈ Z from eq ▸ boundaryZ b) o'.2
    · change φ x = b'.1 at eq
      obtain ⟨a', ha'⟩ := active x ha
      exact absurd (show φ x ∈ SupportAtom.cutBoundary object Z from eq.symm ▸ b'.2)
        (inZ x a' ha').2
    · change φ x = φ y at eq
      obtain ⟨a', ha'⟩ := active x ha
      obtain ⟨c', hc'⟩ := active y hc
      rw [injOn x y a' c' ha' hc' eq]
    · change φ x = o'.1 at eq
      obtain ⟨a', ha'⟩ := active x ha
      exact absurd (show o'.1 ∈ Z from eq ▸ (inZ x a' ha').1) o'.2
    · change o.1 = b'.1 at eq
      exact absurd (show o.1 ∈ Z from eq.symm ▸ boundaryZ b') o.2
    · change o.1 = φ y at eq
      obtain ⟨c', hc'⟩ := active y hc
      exact absurd (show o.1 ∈ Z from eq.symm ▸ (inZ y c' hc').1) o.2
    · exact congrArg (fun o => Sum.inr (Sum.inr o)) (Subtype.ext eq)
  -- the cycle, restricted to its own edges and vertices, mapped into `G`
  let K : SimpleGraph H.Vertex :=
    { Adj := fun a c => H.graph.Adj a c ∧ s(a, c) ∈ C.edges
      symm := ⟨fun a c ⟨h, e⟩ => ⟨h.symm, by rwa [Sym2.eq_swap]⟩⟩
      loopless := ⟨fun a ⟨h, _⟩ => H.graph.loopless.irrefl a h⟩ }
  have hK : ∀ e, e ∈ C.edges → e ∈ K.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a c => exact ⟨C.adj_of_mem_edges he, he⟩
  let S : Set H.Vertex := {a | a ∈ C.support}
  have hS : ∀ a ∈ (C.transfer K hK).support, a ∈ S := by
    intro a ha
    rw [SimpleGraph.Walk.support_transfer] at ha
    exact ha
  have hmap := SimpleGraph.Walk.map_induce (C.transfer K hK) hS
  have hC2 : ((C.transfer K hK).induce S hS).IsCycle := by
    rw [← SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce (G := K) S).toHom)
      (SimpleGraph.Embedding.induce (G := K) S).injective,
      hmap]
    exact hC.transfer hK
  have hlen2 : ((C.transfer K hK).induce S hS).length = C.length := by
    have := congrArg SimpleGraph.Walk.length hmap
    rw [SimpleGraph.Walk.length_map] at this
    rw [this]
    simp
  let f : (K.induce S) →g object.graph :=
    { toFun := fun a => ψ a.1
      map_rel' := fun {a c} h => edgeOK a.1 c.1 h.2 }
  have hf : Function.Injective f := fun a c eq => Subtype.ext (injS a.1 c.1 a.2 c.2 eq)
  exact ⟨{ vertex := f ⟨v, hS v (C.transfer K hK).start_mem_support⟩
           walk := ((C.transfer K hK).induce S hS).map f
           isCycle := hC2.map hf
           length_ok := by rw [SimpleGraph.Walk.length_map, hlen2]; exact hlen }⟩

/-- **A target-avoiding `G` gives a target-free linkage-included gluing.** -/
theorem not_target_of_linkageIncluded {LengthOK : Nat → Prop}
    {X : BoundaryPiece (SupportAtom.boundary object Z)}
    (avoids : ¬ HasCycleWithLength LengthOK object) (included : LinkageIncluded X) :
    ¬ HasCycleWithLength LengthOK (glue X (SupportAtom.outside object Z)) := by
  rintro ⟨cycle⟩
  exact avoids (cycle_transfer included cycle)

/-- **Minimality forbids a strictly smaller linkage-included gluing with the
baseline.**  Such a gluing would be a strictly smaller baseline object, so
minimality gives it a target cycle, which the key lemma carries into `G`. -/
theorem not_vertexCount_lt_of_minimal {LengthOK : Nat → Prop}
    {Baseline : FiniteObject.{u} → Prop}
    {X : BoundaryPiece (SupportAtom.boundary object Z)}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → HasCycleWithLength LengthOK H)
    (baseline : Baseline (glue X (SupportAtom.outside object Z)))
    (included : LinkageIncluded X) :
    ¬ (glue X (SupportAtom.outside object Z)).vertexCount < object.vertexCount := fun lt =>
  not_target_of_linkageIncluded avoids included
    (minimal _ (FiniteObject.lexicographicallySmaller_of_vertexCount_lt lt) baseline)

/-- **Size from minimality, interior form**: a linkage-included `∂Z`-piece whose
gluing into `G − Z` keeps the baseline has at least `int(Z)`'s interior. -/
theorem internalVertexCount_le_of_minimal {LengthOK : Nat → Prop}
    {Baseline : FiniteObject.{u} → Prop}
    {X : BoundaryPiece (SupportAtom.boundary object Z)}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → HasCycleWithLength LengthOK H)
    (baseline : Baseline (glue X (SupportAtom.outside object Z)))
    (included : LinkageIncluded X) :
    (SupportAtom.piece object Z).internalVertexCount ≤ X.internalVertexCount := by
  have same : object.vertexCount =
      (glue (SupportAtom.piece object Z) (SupportAtom.outside object Z)).vertexCount :=
    (FiniteObject.vertexCount_eq_of_isomorphic
      ⟨(SupportAtom.decomposition object Z).reconstructionIso⟩).symm
  have notLt := not_vertexCount_lt_of_minimal avoids minimal baseline included
  rw [same, glue_vertexCount, glue_vertexCount] at notLt
  omega

end Linkage

/-! ## The transplant of a reading -/

section Transplant

variable (object : FiniteObject.{u})

/-- The removed set `D = int(Z) ∖ Y`: interior vertices of `Z` outside `Y`. -/
def Removed (Z Y : Finset object.Vertex) (v : object.Vertex) : Prop :=
  v ∈ Z ∧ v ∉ SupportAtom.cutBoundary object Z ∧ v ∉ Y

/-- The interior of the transplant: the interior vertices of `Z` in `Y`. -/
abbrev TransplantInternal (Z Y : Finset object.Vertex) :=
  {v : object.Vertex // v ∈ Z ∧ v ∉ SupportAtom.cutBoundary object Z ∧ v ∈ Y}

/-- Decode a vertex of the transplant to `G`. -/
def transplantDecode (Z Y : Finset object.Vertex) :
    (SupportAtom.boundary object Z).Vertex ⊕ TransplantInternal object Z Y → object.Vertex
  | .inl b => b.1
  | .inr x => x.1

/-- **The transplant of `Y` into `Z`**: the `∂Z`-piece with interior
`int(Z) ∩ Y`, attached at `∂Z` by `G`'s own edges (the identity bijection of
labels), carrying every edge of `G` among `∂Z ∪ (int(Z) ∩ Y)`.  It is not a
reading of `G`: its interior omits `D = int(Z) ∖ Y`. -/
noncomputable def transplant (Z Y : Finset object.Vertex) :
    BoundaryPiece (SupportAtom.boundary object Z) where
  Internal := TransplantInternal object Z Y
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun v =>
      v ∈ Z ∧ v ∉ SupportAtom.cutBoundary object Z ∧ v ∈ Y
  graph := SimpleGraph.comap (transplantDecode object Z Y) object.graph
  decideAdj := Classical.decRel _

/-- The kept degree of `v`: its `G`-neighbours outside the removed set. -/
noncomputable def keptDegree (Z Y : Finset object.Vertex) (v : object.Vertex) : Nat :=
  {w | object.graph.Adj v w ∧ ¬ Removed object Z Y w}.ncard

/-- **The degree condition (ii) of the transplant, as a predicate on `G`**:
every vertex outside the removed set keeps at least `threshold` neighbours
outside it. -/
def TransplantDegreeCondition (threshold : Nat) (Z Y : Finset object.Vertex) : Prop :=
  ∀ v, ¬ Removed object Z Y v → threshold ≤ keptDegree object Z Y v

/-- A kept vertex whose kept degree is below `threshold`. -/
def TransplantDeficient (threshold : Nat) (Z Y : Finset object.Vertex)
    (v : object.Vertex) : Prop :=
  ¬ Removed object Z Y v ∧ keptDegree object Z Y v < threshold

/-- **The canonical exceptional vertex of the transplant**: the first vertex,
in `G`'s fixed vertex order, that is kept with fewer than `threshold` kept
neighbours; `none` when there is none. -/
noncomputable def transplantDeficit (threshold : Nat) (Z Y : Finset object.Vertex) :
    Option object.Vertex := by
  classical
  exact object.orderedVertices.find? fun v =>
    decide (TransplantDeficient object threshold Z Y v)

variable {object}

theorem cutBoundary_subset {Z : Finset object.Vertex} {v : object.Vertex}
    (h : v ∈ SupportAtom.cutBoundary object Z) : v ∈ Z :=
  ((SupportAtom.mem_cutBoundary_iff object Z v).1 h).1

theorem transplantDecode_injective (Z Y : Finset object.Vertex) :
    Function.Injective (transplantDecode object Z Y) := by
  intro a c h
  rcases a with b | x <;> rcases c with b' | y <;> simp only [transplantDecode] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd (show y.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) y.2.2.1
  · exact absurd (show x.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) x.2.2.1
  · exact congrArg Sum.inr (Subtype.ext h)

theorem range_transplantDecode (Z Y : Finset object.Vertex) (w : object.Vertex) :
    w ∈ Set.range (transplantDecode object Z Y) ↔ w ∈ Z ∧ ¬ Removed object Z Y w := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with b | x
    · exact ⟨cutBoundary_subset b.2, fun h => h.2.1 b.2⟩
    · exact ⟨x.2.1, fun h => h.2.2 x.2.2.2⟩
  · rintro ⟨wZ, notRemoved⟩
    by_cases hb : w ∈ SupportAtom.cutBoundary object Z
    · exact ⟨.inl ⟨w, hb⟩, rfl⟩
    · have wY : w ∈ Y := by
        by_contra wY
        exact notRemoved ⟨wZ, hb, wY⟩
      exact ⟨.inr ⟨w, wZ, hb, wY⟩, rfl⟩

theorem pieceDecode_injective (Z : Finset object.Vertex) :
    Function.Injective (SupportAtom.pieceDecode object Z) := by
  intro a c h
  rcases a with b | x <;> rcases c with b' | y <;> simp only [SupportAtom.pieceDecode] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd (show y.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) y.2.2
  · exact absurd (show x.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) x.2.2
  · exact congrArg Sum.inr (Subtype.ext h)

theorem range_pieceDecode (Z : Finset object.Vertex) (w : object.Vertex) :
    w ∈ Set.range (SupportAtom.pieceDecode object Z) ↔ w ∈ Z := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with b | x
    · exact cutBoundary_subset b.2
    · exact x.2.1
  · intro wZ
    by_cases hb : w ∈ SupportAtom.cutBoundary object Z
    · exact ⟨.inl ⟨w, hb⟩, rfl⟩
    · exact ⟨.inr ⟨w, wZ, hb⟩, rfl⟩

/-- **(iii) The transplant's interior is at most `int(Z)`.** -/
theorem transplant_internalVertexCount_le (Z Y : Finset object.Vertex) :
    (transplant object Z Y).internalVertexCount ≤
      (SupportAtom.piece object Z).internalVertexCount := by
  letI : FinEnum (TransplantInternal object Z Y) := (transplant object Z Y).internalVertices
  letI : FinEnum (SupportAtom.PieceInternal object Z) :=
    (SupportAtom.piece object Z).internalVertices
  change FinEnum.card (TransplantInternal object Z Y) ≤
    FinEnum.card (SupportAtom.PieceInternal object Z)
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  refine Fintype.card_le_of_injective
    (fun x : TransplantInternal object Z Y =>
      (⟨x.1, x.2.1, x.2.2.1⟩ : SupportAtom.PieceInternal object Z)) ?_
  intro x y h
  exact Subtype.ext (congrArg (fun z : SupportAtom.PieceInternal object Z => z.1) h)

/-- **The transplant's interior is `int(Z)` exactly when nothing is removed.** -/
theorem transplant_internalVertexCount_eq_iff (Z Y : Finset object.Vertex) :
    (transplant object Z Y).internalVertexCount =
        (SupportAtom.piece object Z).internalVertexCount ↔
      ∀ v, ¬ Removed object Z Y v := by
  letI : FinEnum (TransplantInternal object Z Y) := (transplant object Z Y).internalVertices
  letI : FinEnum (SupportAtom.PieceInternal object Z) :=
    (SupportAtom.piece object Z).internalVertices
  change FinEnum.card (TransplantInternal object Z Y) =
    FinEnum.card (SupportAtom.PieceInternal object Z) ↔ _
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  let incl : TransplantInternal object Z Y → SupportAtom.PieceInternal object Z :=
    fun x => ⟨x.1, x.2.1, x.2.2.1⟩
  have inj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun z : SupportAtom.PieceInternal object Z => z.1) h)
  constructor
  · intro eq v removed
    have surj : Function.Surjective incl := by
      by_contra notSurj
      have := Fintype.card_lt_of_injective_not_surjective incl inj notSurj
      omega
    obtain ⟨x, hx⟩ := surj ⟨v, removed.1, removed.2.1⟩
    have : x.1 = v := congrArg Subtype.val hx
    exact removed.2.2 (this ▸ x.2.2.2)
  · intro none
    have surj : Function.Surjective incl := by
      intro y
      have yY : y.1 ∈ Y := by
        by_contra yY
        exact none y.1 ⟨y.2.1, y.2.2, yY⟩
      exact ⟨⟨y.1, y.2.1, y.2.2, yY⟩, rfl⟩
    exact Fintype.card_of_bijective ⟨inj, surj⟩

/-- **(iv) The transplant is linkage-included**: its interior vertices are
vertices of `int(Z)`, and its edges are edges of `G`. -/
theorem transplant_linkageIncluded (Z Y : Finset object.Vertex) :
    LinkageIncluded (transplant object Z Y) := by
  intro L linkage
  refine ⟨fun x => (x : TransplantInternal object Z Y).1, ?_, ?_, ?_⟩
  · intro x _ _
    exact ⟨x.2.1, x.2.2.1⟩
  · intro x y _ _ _ _ h
    exact Subtype.ext h
  · intro a c h
    have adj := linkage.le h
    rcases a with b | x <;> rcases c with b' | y <;> exact adj

/-- **(i) The transplant has the boundary profile of `G[Z]` exactly when no
boundary vertex of `Z` has a neighbour in the removed set.** -/
theorem transplant_profile_eq_iff (Z Y : Finset object.Vertex) :
    (transplant object Z Y).boundaryDegreeProfile =
        (SupportAtom.piece object Z).boundaryDegreeProfile ↔
      ∀ (b : (SupportAtom.boundary object Z).Vertex) w,
        object.graph.Adj b.1 w → ¬ Removed object Z Y w := by
  letI : Finite object.Vertex := by letI := object.vertices; infer_instance
  have tDeg : ∀ b : (SupportAtom.boundary object Z).Vertex,
      (transplant object Z Y).boundaryDegree b =
        {w | object.graph.Adj b.1 w ∧ w ∈ Set.range (transplantDecode object Z Y)}.ncard := by
    intro b
    unfold BoundaryPiece.boundaryDegree
    rw [FiniteObject.degree_eq_ncard_neighborSet]
    exact ncard_neighborSet_comap object.graph _ (transplantDecode_injective Z Y) (.inl b)
  have pDeg : ∀ b : (SupportAtom.boundary object Z).Vertex,
      (SupportAtom.piece object Z).boundaryDegree b =
        {w | object.graph.Adj b.1 w ∧ w ∈ Set.range (SupportAtom.pieceDecode object Z)}.ncard := by
    intro b
    unfold BoundaryPiece.boundaryDegree
    rw [FiniteObject.degree_eq_ncard_neighborSet]
    exact ncard_neighborSet_comap object.graph _ (pieceDecode_injective Z) (.inl b)
  constructor
  · intro eq b w adj removed
    have e := congrFun eq b
    change (transplant object Z Y).boundaryDegree b =
      (SupportAtom.piece object Z).boundaryDegree b at e
    rw [tDeg, pDeg] at e
    have sub : {w | object.graph.Adj b.1 w ∧ w ∈ Set.range (transplantDecode object Z Y)} ⊂
        {w | object.graph.Adj b.1 w ∧ w ∈ Set.range (SupportAtom.pieceDecode object Z)} := by
      refine Set.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
      · rintro u ⟨h, hu⟩
        exact ⟨h, (range_pieceDecode Z u).2 ((range_transplantDecode Z Y u).1 hu).1⟩
      · intro same
        have mem : w ∈ {w | object.graph.Adj b.1 w ∧
            w ∈ Set.range (SupportAtom.pieceDecode object Z)} :=
          ⟨adj, (range_pieceDecode Z w).2 removed.1⟩
        rw [← same] at mem
        exact ((range_transplantDecode Z Y w).1 mem.2).2 removed
    exact absurd e (Set.ncard_lt_ncard sub (Set.toFinite _)).ne
  · intro none
    funext b
    change (transplant object Z Y).boundaryDegree b =
      (SupportAtom.piece object Z).boundaryDegree b
    rw [tDeg, pDeg]
    congr 1
    ext w
    simp only [Set.mem_setOf_eq, range_transplantDecode, range_pieceDecode]
    constructor
    · rintro ⟨h, wZ, -⟩
      exact ⟨h, wZ⟩
    · rintro ⟨h, wZ⟩
      exact ⟨h, wZ, none b w h⟩

/-- Decode a vertex of the transplant glued into `G − Z` to `G`. -/
def glueDecode (Z Y : Finset object.Vertex) :
    (glue (transplant object Z Y) (SupportAtom.outside object Z)).Vertex → object.Vertex
  | .inl b => b.1
  | .inr (.inl x) => (x : TransplantInternal object Z Y).1
  | .inr (.inr o) => (o : SupportAtom.OutsideInternal object Z).1

theorem glueDecode_injective (Z Y : Finset object.Vertex) :
    Function.Injective (glueDecode (object := object) Z Y) := by
  intro a c h
  rcases a with b | (x | o) <;> rcases c with b' | (y | o') <;> simp only [glueDecode] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd (show y.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) y.2.2.1
  · exact absurd (show o'.1 ∈ Z from h ▸ cutBoundary_subset b.2) o'.2
  · exact absurd (show x.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) x.2.2.1
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext h)
  · exact absurd (show o'.1 ∈ Z from h ▸ x.2.1) o'.2
  · exact absurd (show o.1 ∈ Z from h.symm ▸ cutBoundary_subset b'.2) o.2
  · exact absurd (show o.1 ∈ Z from h.symm ▸ y.2.1) o.2
  · exact congrArg (fun o => Sum.inr (Sum.inr o)) (Subtype.ext h)

theorem range_glueDecode (Z Y : Finset object.Vertex) (w : object.Vertex) :
    w ∈ Set.range (glueDecode (object := object) Z Y) ↔ ¬ Removed object Z Y w := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with b | (x | o)
    · exact fun h => h.2.1 b.2
    · exact fun h => h.2.2 x.2.2.2
    · exact fun h => o.2 h.1
  · intro notRemoved
    by_cases wZ : w ∈ Z
    · by_cases hb : w ∈ SupportAtom.cutBoundary object Z
      · exact ⟨.inl ⟨w, hb⟩, rfl⟩
      · have wY : w ∈ Y := by
          by_contra wY
          exact notRemoved ⟨wZ, hb, wY⟩
        exact ⟨.inr (.inl ⟨w, wZ, hb, wY⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨w, wZ⟩), rfl⟩

/-- **The glued transplant is `G` with the removed set deleted**: adjacency in
`glue (transplant G Z Y) (G − Z)` is adjacency in `G`. -/
theorem glue_transplant_adj_iff (Z Y : Finset object.Vertex)
    (a c : (glue (transplant object Z Y) (SupportAtom.outside object Z)).Vertex) :
    (glue (transplant object Z Y) (SupportAtom.outside object Z)).graph.Adj a c ↔
      object.graph.Adj (glueDecode Z Y a) (glueDecode Z Y c) := by
  change (glueGraph (transplant object Z Y) (SupportAtom.outside object Z)).Adj a c ↔ _
  rw [glueGraph_adj_iff]
  constructor
  · rintro (⟨pl, pr, h, rfl, rfl⟩ | ⟨cl, cr, h, rfl, rfl⟩)
    · rcases pl with b | x <;> rcases pr with b' | y <;> exact h
    · rcases cl with b | o <;> rcases cr with b' | o' <;> exact h
  · intro h
    rcases a with b | (x | o) <;> rcases c with b' | (y | o')
    · exact Or.inl ⟨.inl b, .inl b', h, rfl, rfl⟩
    · exact Or.inl ⟨.inl b, .inr y, h, rfl, rfl⟩
    · exact Or.inr ⟨.inl b, .inr o', h, rfl, rfl⟩
    · exact Or.inl ⟨.inr x, .inl b', h, rfl, rfl⟩
    · exact Or.inl ⟨.inr x, .inr y, h, rfl, rfl⟩
    · exact absurd ((SupportAtom.mem_cutBoundary_iff object Z x.1).2
        ⟨x.2.1, o'.1, h, o'.2⟩) x.2.2.1
    · exact Or.inr ⟨.inr o, .inl b', h, rfl, rfl⟩
    · exact absurd ((SupportAtom.mem_cutBoundary_iff object Z y.1).2
        ⟨y.2.1, o.1, h.symm, o.2⟩) y.2.2.1
    · exact Or.inr ⟨.inr o, .inr o', h, rfl, rfl⟩

/-- The degree of a vertex of the glued transplant is the kept degree of its
vertex of `G`. -/
theorem glue_transplant_degree (Z Y : Finset object.Vertex)
    (a : (glue (transplant object Z Y) (SupportAtom.outside object Z)).Vertex) :
    (glue (transplant object Z Y) (SupportAtom.outside object Z)).degree a =
      keptDegree object Z Y (glueDecode Z Y a) := by
  rw [FiniteObject.degree_eq_ncard_neighborSet,
    ← Set.ncard_image_of_injective _ (glueDecode_injective Z Y)]
  unfold keptDegree
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(glue_transplant_adj_iff Z Y a c).1 hc, (range_glueDecode Z Y _).1 ⟨c, rfl⟩⟩
  · rintro ⟨h, hw⟩
    obtain ⟨c, rfl⟩ := (range_glueDecode Z Y w).2 hw
    exact ⟨c, (glue_transplant_adj_iff Z Y a c).2 h, rfl⟩

/-- **(ii) The glued transplant keeps the baseline exactly when the degree
condition holds on `G`** (when some vertex is kept). -/
theorem transplant_baseline_iff {threshold : Nat} (Z Y : Finset object.Vertex)
    (kept : ∃ v, ¬ Removed object Z Y v) :
    MinimumDegreeAtLeast threshold
        (glue (transplant object Z Y) (SupportAtom.outside object Z)) ↔
      TransplantDegreeCondition object threshold Z Y := by
  constructor
  · intro base v notRemoved
    obtain ⟨a, rfl⟩ := (range_glueDecode Z Y v).2 notRemoved
    rw [← glue_transplant_degree]
    exact le_trans base (FiniteObject.minDegree_le_degree _ a)
  · intro cond
    obtain ⟨v, hv⟩ := kept
    obtain ⟨a, -⟩ := (range_glueDecode Z Y v).2 hv
    haveI : Nonempty (glue (transplant object Z Y) (SupportAtom.outside object Z)).Vertex :=
      ⟨a⟩
    unfold MinimumDegreeAtLeast
    apply FiniteObject.le_minDegree_of_forall_le_degree
    intro c
    rw [glue_transplant_degree]
    exact cond _ ((range_glueDecode Z Y _).1 ⟨c, rfl⟩)

/-- Removing a vertex makes the glued transplant strictly smaller than `G`. -/
theorem glue_transplant_vertexCount_lt {Z Y : Finset object.Vertex}
    {w : object.Vertex} (removed : Removed object Z Y w) :
    (glue (transplant object Z Y) (SupportAtom.outside object Z)).vertexCount <
      object.vertexCount :=
  vertexCount_lt_of_injective (glueDecode Z Y) (glueDecode_injective Z Y) fun surj =>
    (range_glueDecode Z Y w).1 (surj w) removed

/-- **Size equality from minimality**: on a minimal target-avoiding `G`, a
transplant whose gluing into `G − Z` keeps the baseline removes nothing -- `Y`
contains every interior vertex of `Z`.  Otherwise the transplant would be a
strictly smaller baseline object without a target cycle. -/
theorem transplant_fills_of_baseline {LengthOK : Nat → Prop} {threshold : Nat}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (Z Y : Finset object.Vertex)
    (baseline : MinimumDegreeAtLeast threshold
      (glue (transplant object Z Y) (SupportAtom.outside object Z))) :
    ∀ v, ¬ Removed object Z Y v := fun _ removed =>
  not_vertexCount_lt_of_minimal avoids minimal baseline
    (transplant_linkageIncluded Z Y) (glue_transplant_vertexCount_lt removed)

/-- **Size equality from minimality, interior form**: (ii) and (iv) give
`int(transplant) = int(Z)`. -/
theorem transplant_size_eq {LengthOK : Nat → Prop} {threshold : Nat}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (Z Y : Finset object.Vertex)
    (baseline : MinimumDegreeAtLeast threshold
      (glue (transplant object Z Y) (SupportAtom.outside object Z)))
    (included : LinkageIncluded (transplant object Z Y)) :
    (transplant object Z Y).internalVertexCount =
      (SupportAtom.piece object Z).internalVertexCount :=
  le_antisymm (transplant_internalVertexCount_le Z Y)
    (internalVertexCount_le_of_minimal avoids minimal baseline included)

/-- **`transplantDeficit` is exactly the first deficient kept vertex in `G`'s
order.** -/
theorem transplantDeficit_spec {threshold : Nat} {Z Y : Finset object.Vertex}
    {v : object.Vertex} :
    transplantDeficit object threshold Z Y = some v ↔
      TransplantDeficient object threshold Z Y v ∧
        ∃ before after, object.orderedVertices = before ++ v :: after ∧
          ∀ a ∈ before, ¬ TransplantDeficient object threshold Z Y a := by
  classical
  unfold transplantDeficit
  rw [List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]

theorem transplantDeficit_isSome_iff {threshold : Nat} {Z Y : Finset object.Vertex} :
    (transplantDeficit object threshold Z Y).isSome ↔
      ∃ v, TransplantDeficient object threshold Z Y v := by
  classical
  unfold transplantDeficit
  rw [List.find?_isSome]
  simp only [decide_eq_true_eq, FiniteObject.mem_orderedVertices, true_and]

/-- With nothing removed, the kept degree is the degree. -/
theorem keptDegree_eq_degree {Z Y : Finset object.Vertex}
    (none : ∀ w, ¬ Removed object Z Y w) (v : object.Vertex) :
    keptDegree object Z Y v = object.degree v := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  unfold keptDegree
  congr 1
  ext w
  exact ⟨fun h => h.1, fun h => ⟨h, none w⟩⟩

/-- A kept vertex with no removed neighbour keeps its degree. -/
theorem keptDegree_eq_degree_of_noRemovedNeighbour {Z Y : Finset object.Vertex}
    {v : object.Vertex} (free : ∀ w, object.graph.Adj v w → ¬ Removed object Z Y w) :
    keptDegree object Z Y v = object.degree v := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  unfold keptDegree
  congr 1
  ext w
  exact ⟨fun h => h.1, fun h => ⟨h, free w h⟩⟩

/-- **The transplant, exactly** (on a minimal target-avoiding `G` with the
baseline, some vertex kept): either nothing is removed (`int(Z) ⊆ Y`) and there
is no deficient vertex, or the canonical exceptional vertex `v` exists: it is
a kept vertex of `Z` with a neighbour in the removed set `D = int(Z) ∖ Y`
(an interior vertex of `Z` in `Y`, or a boundary vertex of `Z`) and fewer than
`threshold` neighbours outside `D`. -/
theorem transplant_exact {LengthOK : Nat → Prop} {threshold : Nat}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (base : MinimumDegreeAtLeast threshold object)
    (Z Y : Finset object.Vertex) (kept : ∃ v, ¬ Removed object Z Y v) :
    ((∀ v, ¬ Removed object Z Y v) ∧ transplantDeficit object threshold Z Y = none) ∨
      ∃ v, transplantDeficit object threshold Z Y = some v ∧ v ∈ Z ∧
        ¬ Removed object Z Y v ∧
        (∃ w, Removed object Z Y w ∧ object.graph.Adj v w) ∧
        keptDegree object Z Y v < threshold := by
  have degLower : ∀ v, threshold ≤ object.degree v := fun v =>
    le_trans base (object.minDegree_le_degree v)
  by_cases none : ∀ v, ¬ Removed object Z Y v
  · left
    refine ⟨none, ?_⟩
    cases h : transplantDeficit object threshold Z Y with
    | none => rfl
    | some v =>
        have low := ((transplantDeficit_spec (object := object)).1 h).1.2
        rw [keptDegree_eq_degree none] at low
        exact absurd low (Nat.not_lt.2 (degLower v))
  · right
    have notBase : ¬ MinimumDegreeAtLeast threshold
        (glue (transplant object Z Y) (SupportAtom.outside object Z)) := fun b =>
      none (transplant_fills_of_baseline avoids minimal Z Y b)
    have notCond : ¬ TransplantDegreeCondition object threshold Z Y := fun c =>
      notBase ((transplant_baseline_iff Z Y kept).2 c)
    have exists_def : ∃ v, TransplantDeficient object threshold Z Y v := by
      by_contra noDef
      apply notCond
      intro v hv
      by_contra low
      exact noDef ⟨v, hv, Nat.lt_of_not_le low⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
      ((transplantDeficit_isSome_iff (object := object)).2 exists_def)
    have deficient := ((transplantDeficit_spec (object := object)).1 hv).1
    have hasRemoved : ∃ w, Removed object Z Y w ∧ object.graph.Adj v w := by
      by_contra noNbr
      have free : ∀ w, object.graph.Adj v w → ¬ Removed object Z Y w :=
        fun w adj removed => noNbr ⟨w, removed, adj⟩
      have := deficient.2
      rw [keptDegree_eq_degree_of_noRemovedNeighbour free] at this
      exact absurd this (Nat.not_lt.2 (degLower v))
    obtain ⟨w, wRemoved, adj⟩ := hasRemoved
    have vZ : v ∈ Z := by
      by_contra vZ
      exact wRemoved.2.1 ((SupportAtom.mem_cutBoundary_iff object Z w).2
        ⟨wRemoved.1, v, adj.symm, vZ⟩)
    exact ⟨v, hv, vZ, deficient.1, ⟨w, wRemoved, adj⟩, deficient.2⟩

end Transplant

/-! ## The equal-count bijection at a boundary label -/

section Contacts

variable (object : FiniteObject.{u})

/-- The contacts of the reading `R` of `Z` at a boundary label `b`: the
neighbours `w ∈ Z` of `b` with `b, w ∈ R`.  Their number is the reading count
`c_R(b)`. -/
def contacts (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) : Set object.Vertex :=
  {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R}

/-- **The bijection that equal counts supply**: equal reading counts at `b` are
an explicit bijection between the two readings' contacts at `b`. -/
noncomputable def contactEquiv (Z R R' : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex)
    (counts : (contacts object Z R b).ncard = (contacts object Z R' b).ncard) :
    contacts object Z R b ≃ contacts object Z R' b := by
  classical
  letI : Finite object.Vertex := by letI := object.vertices; infer_instance
  letI : Fintype (contacts object Z R b) := Fintype.ofFinite _
  letI : Fintype (contacts object Z R' b) := Fintype.ofFinite _
  refine Fintype.equivOfCardEq ?_
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]
  exact counts

end Contacts

end Hypostructure.Graph.Transplant
