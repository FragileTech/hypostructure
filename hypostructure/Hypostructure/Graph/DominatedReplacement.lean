import Hypostructure.Graph.Transplant
import Hypostructure.Graph.PathChords

/-!
# Dominated replacement: external-type compression of a piece (CT3)

Let `G` be a finite object, `Z` a vertex support with cut boundary `∂Z`, and
`Y` a `∂Z`-boundaried gadget (an arbitrary `BoundaryPiece` on `∂Z`'s own
labels).  Every cycle of `glue Y (G − Z)` either lies entirely in `Y`, or it
cuts `Y` into a **linkage system**: the `Y`-edges of the cycle form a set of
vertex-disjoint paths whose ends are boundary terminals and whose interior
vertices are interior vertices of `Y` or pass through terminals
(`Transplant.IsLinkage`), and this edge set has no cycle (`IsLinkageSystem`).

* **Dominance** (`Dominated LengthOK Y`): (i) every linkage system of `Y` is
  realized in `G[Z]` (`Transplant.LinkageRealized`: an injective relabelling of
  its interior into the interior of `Z`, fixing `∂Z`, that sends each edge to an
  edge of `G`; its image is a linkage system of `G[Z]` with the same terminal
  pairing, the same length vector, and interiors in `int(Z)`), and (ii) `Y`
  has no accepted cycle of its own.  Interiors in `int(Z)` are what keeps the
  substituted closed walk simple: the realizing paths meet `∂Z` only at their
  own terminals, and the outside segments lie in `G − Z`.
* **The cycle decomposition** (`cycleLinkage_isAcyclic`): the `Y`-edges of a
  cycle of the gluing that is not entirely a `Y`-cycle form an acyclic edge set
  (a cycle inside it would cover the whole glued cycle, by
  `edges_subset_of_cycle_sub`).
* **The substitution lemma** (`cycle_transfer_of_dominated`): under dominance
  every accepted cycle of `glue Y (G − Z)` is an accepted cycle of `Y` or maps
  to an accepted cycle of `G` of the same length.  The proof restricts `Y` to
  the cycle's own linkage system and applies `Transplant.cycle_transfer` there.
* `not_target_glue_of_dominated`: a target-avoiding `G` gives a target-free
  `glue Y (G − Z)`.
* **Minimality** (`not_dominated_of_exclusion`): at a `G` with no replacement
  support (`lem:replacement`), no gadget `Y` with fewer interior vertices than
  `G[Z]`, the boundary-degree profile of `G[Z]` and the baseline in
  `glue Y (G − Z)` is dominated by `G[Z]`.
* **Terminal-pair form** (`dominated_of_twoTerminal`): when `∂Z` has exactly
  two labels `u ≠ v`, dominance reduces to the inclusion of the `u`–`v` path
  lengths of `Y` in the `u`–`v` path lengths of `G[Z]` (`pathLengths`) and
  (ii).  An acyclic linkage of a two-terminal piece is a single `u`–`v` path
  (`exists_path_cover`), realized position by position along a `G[Z]` path of
  the same length.  Hence (`exists_new_length_of_exclusion`) every smaller
  degree-valid target-free gadget of a two-exit support of `G` has a `u`–`v`
  path whose length is not a `u`–`v` path length of `G[Z]`.
* **The copy gadget** (`copyPiece`): `G[Z']` of a two-exit support `Z'` read
  on the two labels of `∂Z`.  It is a subgraph of `G`, keeps the baseline when
  glued into `G − Z`, and keeps the boundary-degree profile of `G[Z]` when the
  terminal inner degrees match; so (`internalVertexCount_le_of_twoExit`)
  `L_{Z'}(u', v') ⊆ L_Z(u, v)` forces `|int Z| ≤ |int Z'|`.

Vocabulary-free: nothing here knows a presentation, a ledger, or a manuscript
node.
-/

namespace Hypostructure.Graph.DominatedReplacement

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.Transplant

universe u

/-! ## Two cycles, one inside the other -/

section Cover

variable {V : Type*} {H : SimpleGraph V}

/-- At a vertex of a cycle `D` whose edges are edges of a cycle `C`, every
`C`-edge is a `D`-edge (both cycles have exactly two edges there). -/
theorem cycle_edge_mem_of_sub {w c : V} {D : H.Walk w w} (hD : D.IsCycle)
    {C : H.Walk c c} (hC : C.IsCycle) (sub : ∀ e ∈ D.edges, e ∈ C.edges)
    {x y : V} (hx : x ∈ D.support) (hxy : s(x, y) ∈ C.edges) :
    s(x, y) ∈ D.edges := by
  obtain ⟨a, ha⟩ := cycle_edge_of_mem_support hD hx
  obtain ⟨p, q, hpq, hD2⟩ := cycle_two_neighbours hD ha
  obtain ⟨p', q', _, hC2⟩ := cycle_two_neighbours hC hxy
  have hp := (hC2 p).1 (sub _ ((hD2 p).2 (Or.inl rfl)))
  have hq := (hC2 q).1 (sub _ ((hD2 q).2 (Or.inr rfl)))
  have hy := (hC2 y).1 hxy
  refine (hD2 y).2 ?_
  rcases hy with hy | hy <;> rcases hp with hp | hp <;> rcases hq with hq | hq
  all_goals first
    | exact absurd (hp.trans hq.symm) hpq
    | exact Or.inl (hy.trans hp.symm)
    | exact Or.inr (hy.trans hq.symm)

/-- Closure along a walk: if a predicate `S` holds at the start, and every
`E`-edge at an `S`-vertex is a `D`-edge leading to an `S`-vertex, then every
edge of a walk with edges in `E` is in `D`. -/
theorem edges_mem_of_closed {S : V → Prop} {E D : List (Sym2 V)}
    (step : ∀ x y, S x → s(x, y) ∈ E → s(x, y) ∈ D ∧ S y) :
    ∀ {a b : V} (W : H.Walk a b), S a → (∀ e ∈ W.edges, e ∈ E) →
      ∀ e ∈ W.edges, e ∈ D
  | _, _, .nil, _, _ => by simp
  | _, _, @SimpleGraph.Walk.cons _ _ a b _ _ W, ha, hE => by
      intro e he
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      have first := step a b ha (hE s(a, b) (by simp))
      rcases he with rfl | he
      · exact first.1
      · exact edges_mem_of_closed step W first.2
          (fun e' he' => hE e' (by simp [he'])) e he

/-- **A cycle inside a cycle is the whole cycle**: if every edge of the cycle
`D` is an edge of the cycle `C`, then every edge of `C` is an edge of `D`. -/
theorem edges_subset_of_cycle_sub {w c : V} {D : H.Walk w w} (hD : D.IsCycle)
    {C : H.Walk c c} (hC : C.IsCycle) (sub : ∀ e ∈ D.edges, e ∈ C.edges) :
    ∀ e ∈ C.edges, e ∈ D.edges := by
  classical
  obtain ⟨a, ha⟩ := cycle_edge_of_mem_support hD D.start_mem_support
  have hw : w ∈ C.support := C.fst_mem_support_of_mem_edges (sub _ ha)
  have key := edges_mem_of_closed (S := fun x => x ∈ D.support) (E := C.edges)
    (D := D.edges)
    (fun x y hx hxy =>
      ⟨cycle_edge_mem_of_sub hD hC sub hx hxy,
        D.snd_mem_support_of_mem_edges (cycle_edge_mem_of_sub hD hC sub hx hxy)⟩)
    (C.rotate w hw) D.start_mem_support
    (fun e he => (C.rotate_edges w hw).mem_iff.mp he)
  intro e he
  exact key e ((C.rotate_edges w hw).mem_iff.mpr he)

end Cover

/-! ## Paths in an acyclic graph -/

section Acyclic

variable {V : Type*} {L : SimpleGraph V}

/-- **Chord lemma**: in an acyclic graph, two adjacent vertices on a path are
consecutive on it. -/
theorem mem_edges_of_acyclic (acyc : L.IsAcyclic) [DecidableEq V] {s t : V}
    (P : L.Walk s t) {x y : V} (hx : x ∈ P.support) (hy : y ∈ P.support)
    (hxy : L.Adj x y) : s(x, y) ∈ P.edges := by
  by_contra notIn
  have bridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp acyc) hxy
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges] at bridge
  have mem := bridge ((P.takeUntil x hx).reverse.append (P.takeUntil y hy))
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse, List.mem_append,
    List.mem_reverse] at mem
  rcases mem with h | h
  · exact notIn (P.edges_takeUntil_subset_edges hx h)
  · exact notIn (P.edges_takeUntil_subset_edges hy h)

/-- **A longest path through `x`**: some path through `x` has every neighbour of
either end on it (it cannot be extended at either end). -/
theorem exists_closed_path [Fintype V] (x : V) :
    ∃ (a b : V) (p : L.Walk a b), p.IsPath ∧ x ∈ p.support ∧
      (∀ z, L.Adj a z → z ∈ p.support) ∧ (∀ z, L.Adj b z → z ∈ p.support) := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ (a b : V) (p : L.Walk a b), p.IsPath ∧ x ∈ p.support ∧ p.length = n
  have P0 : P 0 := ⟨x, x, .nil, SimpleGraph.Walk.IsPath.nil, by simp, rfl⟩
  have bound : ∀ n, P n → n ≤ Fintype.card V := by
    rintro n ⟨a, b, p, hp, -, rfl⟩
    exact le_of_lt hp.length_lt
  let N := Nat.findGreatest P (Fintype.card V)
  have PN : P N := Nat.findGreatest_spec (P := P) (Nat.zero_le _) P0
  have greatest : ∀ m, N < m → ¬ P m := by
    intro m hm Pm
    exact Nat.findGreatest_is_greatest hm (bound m Pm) Pm
  obtain ⟨a, b, p, hp, hx, hlen⟩ := PN
  refine ⟨a, b, p, hp, hx, ?_, ?_⟩
  · intro z hz
    by_contra notIn
    apply greatest (N + 1) (Nat.lt_succ_self N)
    refine ⟨z, b, .cons hz.symm p, ?_, ?_, ?_⟩
    · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hp, notIn⟩
    · simp [hx]
    · simp [hlen]
  · intro z hz
    by_contra notIn
    apply greatest (N + 1) (Nat.lt_succ_self N)
    refine ⟨a, z, p.concat hz, hp.concat notIn hz, ?_, ?_⟩
    · exact p.support_subset_support_concat hz hx
    · simp [hlen]

/-- A path through a vertex with a neighbour is not a single vertex once it
cannot be extended at its end. -/
theorem one_le_length_of_closed {a b x y : V} (p : L.Walk a b) (hx : x ∈ p.support)
    (hxy : L.Adj x y) (closed : ∀ z, L.Adj b z → z ∈ p.support) : 1 ≤ p.length := by
  cases p with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst hx
      have := closed y hxy
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at this
      exact absurd this.symm hxy.ne
  | cons _ _ => simp

/-- **The ends of an unextendable path are terminals**: in an acyclic graph in
which every non-terminal vertex with a neighbour has a second one, both ends of
a nontrivial unextendable path are terminals. -/
theorem terminal_ends_of_closed (acyc : L.IsAcyclic) {B : V → Prop}
    (internalTwo : ∀ x, ¬ B x → ∀ a, L.Adj x a → ∃ b, b ≠ a ∧ L.Adj x b)
    {a b : V} {p : L.Walk a b} (hp : p.IsPath) (pos : 1 ≤ p.length)
    (closedA : ∀ z, L.Adj a z → z ∈ p.support)
    (closedB : ∀ z, L.Adj b z → z ∈ p.support) : B a ∧ B b := by
  have notNil : ¬ p.Nil := by
    intro isNil
    rw [← SimpleGraph.Walk.length_eq_zero_iff] at isNil
    omega
  constructor
  · by_contra hB
    obtain ⟨z, hz, adj⟩ := internalTwo a hB p.snd (SimpleGraph.Walk.adj_snd notNil)
    exact hz (acyc.eq_snd_of_adj_start hp adj (closedA z adj))
  · by_contra hB
    obtain ⟨z, hz, adj⟩ := internalTwo b hB p.penultimate
      (SimpleGraph.Walk.adj_penultimate notNil).symm
    exact hz (acyc.eq_penultimate_of_adj_end hp adj (closedB z adj))

/-- **With two terminals, every vertex with a neighbour lies on an `s`–`t`
path.** -/
theorem exists_path_through [Fintype V] (acyc : L.IsAcyclic) {B : V → Prop}
    (internalTwo : ∀ x, ¬ B x → ∀ a, L.Adj x a → ∃ b, b ≠ a ∧ L.Adj x b)
    {s t : V} (hst : s ≠ t) (two : ∀ x, B x → x = s ∨ x = t)
    {x y : V} (hxy : L.Adj x y) :
    ∃ P : L.Walk s t, P.IsPath ∧ x ∈ P.support := by
  obtain ⟨a, b, p, hp, hx, closedA, closedB⟩ := exists_closed_path (L := L) x
  have pos := one_le_length_of_closed p hx hxy closedB
  obtain ⟨Ba, Bb⟩ := terminal_ends_of_closed acyc internalTwo hp pos closedA closedB
  have hab := PathChords.ne_of_path_length hp pos
  rcases two a Ba with rfl | rfl <;> rcases two b Bb with rfl | rfl
  · exact absurd rfl hab
  · exact ⟨p, hp, hx⟩
  · exact ⟨p.reverse, hp.reverse, by simpa using hx⟩
  · exact absurd rfl hab

/-- **An acyclic two-terminal linkage is one path**: in an acyclic graph with
exactly two terminals `s ≠ t`, in which every non-terminal vertex with a
neighbour has a second one, a graph with an edge has an `s`–`t` path carrying
every edge. -/
theorem exists_path_cover [Fintype V] [DecidableEq V] (acyc : L.IsAcyclic)
    {B : V → Prop}
    (internalTwo : ∀ x, ¬ B x → ∀ a, L.Adj x a → ∃ b, b ≠ a ∧ L.Adj x b)
    {s t : V} (hst : s ≠ t) (two : ∀ x, B x → x = s ∨ x = t)
    {a c : V} (hac : L.Adj a c) :
    ∃ P : L.Walk s t, P.IsPath ∧ ∀ x y, L.Adj x y → s(x, y) ∈ P.edges := by
  obtain ⟨P, hP, -⟩ := exists_path_through acyc internalTwo hst two hac
  refine ⟨P, hP, fun x y hxy => ?_⟩
  have onP : ∀ z w, L.Adj z w → z ∈ P.support := by
    intro z w hzw
    obtain ⟨Q, hQ, hz⟩ := exists_path_through acyc internalTwo hst two hzw
    have := acyc.path_unique ⟨Q, hQ⟩ ⟨P, hP⟩
    rw [Subtype.mk.injEq] at this
    rw [← this]
    exact hz
  exact mem_edges_of_acyclic acyc P (onP x y hxy) (onP y x hxy.symm) hxy

/-- An edge of a walk joins two consecutive positions. -/
theorem exists_getVert_of_mem_edges {s t : V} {P : L.Walk s t} {x y : V}
    (h : s(x, y) ∈ P.edges) :
    ∃ k < P.length, (x = P.getVert k ∧ y = P.getVert (k + 1)) ∨
      (x = P.getVert (k + 1) ∧ y = P.getVert k) := by
  unfold SimpleGraph.Walk.edges at h
  obtain ⟨d, hd, hde⟩ := List.mem_map.mp h
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hd
  refine ⟨k, P.length_darts ▸ hk, ?_⟩
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert k hk] at hde
  change s(P.getVert k, P.getVert (k + 1)) = s(x, y) at hde
  rcases Sym2.eq_iff.mp hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

end Acyclic

/-! ## Linkage systems and dominance -/

section Dominance

variable {object : FiniteObject.{u}} {Z : Finset object.Vertex}

/-- **A linkage system of a `∂Z`-gadget `Y`**: a linkage (`Transplant.IsLinkage`)
with no cycle, i.e. a family of vertex-disjoint paths between boundary
terminals (the `Y`-segments a cycle of `glue Y (G − Z)` cuts out of `Y`). -/
def IsLinkageSystem (Y : BoundaryPiece (SupportAtom.boundary object Z))
    (L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)) : Prop :=
  IsLinkage Y L ∧ L.IsAcyclic

/-- **`Y` is dominated by `G[Z]`**: (i) every linkage system of `Y` is realized
in `G[Z]` with the same terminal pairing and the same length vector, interiors
in `int(Z)` (`Transplant.LinkageRealized`), and (ii) `Y` has no accepted cycle
on its own. -/
def Dominated (LengthOK : Nat → Prop) (Y : BoundaryPiece (SupportAtom.boundary object Z)) :
    Prop :=
  (∀ L, IsLinkageSystem Y L → LinkageRealized Y L) ∧ ¬ HasCycleWithLength LengthOK Y.pack

/-- `Y` restricted to the edge set `L` (same boundary, same interior). -/
noncomputable abbrev withGraph (Y : BoundaryPiece (SupportAtom.boundary object Z))
    (L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)) :
    BoundaryPiece (SupportAtom.boundary object Z) where
  Internal := Y.Internal
  internalVertices := Y.internalVertices
  graph := L
  decideAdj := Classical.decRel _

theorem realize_withGraph {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)}
    (φ : Y.Internal → object.Vertex) :
    realize (X := withGraph Y L) φ = realize (X := Y) φ := by
  funext a
  cases a <;> rfl

theorem pieceEmbedding_withGraph {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)}
    (a : (SupportAtom.boundary object Z).Vertex ⊕ Y.Internal) :
    pieceEmbedding (withGraph Y L) (SupportAtom.outside object Z) a =
      pieceEmbedding Y (SupportAtom.outside object Z) a := by
  cases a <;> rfl

theorem contextEmbedding_withGraph {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)}
    (a : (SupportAtom.boundary object Z).Vertex ⊕ (SupportAtom.outside object Z).Internal) :
    contextEmbedding (withGraph Y L) (SupportAtom.outside object Z) a =
      contextEmbedding Y (SupportAtom.outside object Z) a := by
  cases a <;> rfl

/-- A restriction of `Y` to an acyclic edge set is linkage-included as soon as
`Y`'s linkage systems are realized: each of its linkages is a linkage system of
`Y`. -/
theorem linkageIncluded_withGraph {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    (realized : ∀ L, IsLinkageSystem Y L → LinkageRealized Y L)
    {L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)}
    (le : L ≤ Y.graph) (acyc : L.IsAcyclic) :
    LinkageIncluded (withGraph Y L) := by
  intro L' hL'
  obtain ⟨φ, inZ, injOn, adjOK⟩ := realized L'
    ⟨⟨le_trans hL'.le le, hL'.atMostTwo, hL'.internalTwo⟩, acyc.anti hL'.le⟩
  refine ⟨φ, inZ, injOn, fun a c hac => ?_⟩
  rw [realize_withGraph]
  exact adjOK a c hac

/-- **The linkage a cycle of the gluing cuts out of `Y`**: the edges of `Y`
that the cycle uses. -/
def cycleLinkage {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {c : (glue Y (SupportAtom.outside object Z)).Vertex}
    (C : (glue Y (SupportAtom.outside object Z)).graph.Walk c c) :
    SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal) where
  Adj a b := Y.graph.Adj a b ∧
    s(pieceEmbedding Y (SupportAtom.outside object Z) a,
      pieceEmbedding Y (SupportAtom.outside object Z) b) ∈ C.edges
  symm := ⟨fun _ _ ⟨h, e⟩ => ⟨h.symm, by rwa [Sym2.eq_swap]⟩⟩
  loopless := ⟨fun a ⟨h, _⟩ => Y.graph.loopless.irrefl a h⟩

/-- **The cycle decomposition**: if some edge of a cycle `C` of the gluing is
not owned by `Y`, the `Y`-edges of `C` form an acyclic edge set — a cycle among
them would be a cycle inside `C`, hence all of `C`. -/
theorem cycleLinkage_isAcyclic {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {c : (glue Y (SupportAtom.outside object Z)).Vertex}
    {C : (glue Y (SupportAtom.outside object Z)).graph.Walk c c} (hC : C.IsCycle)
    {a b : (glue Y (SupportAtom.outside object Z)).Vertex} (hab : s(a, b) ∈ C.edges)
    (notOwned : ¬ PieceOwns Y (SupportAtom.outside object Z) a b) :
    (cycleLinkage C).IsAcyclic := by
  intro w D hD
  let pe := pieceEmbedding Y (SupportAtom.outside object Z)
  let f : cycleLinkage C →g (glue Y (SupportAtom.outside object Z)).graph :=
    { toFun := pe
      map_rel' := fun {x y} h => C.adj_of_mem_edges h.2 }
  have hD' : (D.map f).IsCycle := hD.map pe.injective
  have sub : ∀ e ∈ (D.map f).edges, e ∈ C.edges := by
    intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.ind with
    | h x y => exact (D.adj_of_mem_edges he0).2
  have cover := edges_subset_of_cycle_sub hD' hC sub _ hab
  rw [SimpleGraph.Walk.edges_map, List.mem_map] at cover
  obtain ⟨e0, he0, himage⟩ := cover
  induction e0 using Sym2.ind with
  | h x y =>
      have adj := (D.adj_of_mem_edges he0).1
      change s(pe x, pe y) = s(a, b) at himage
      rcases Sym2.eq_iff.mp himage with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact notOwned ⟨x, y, adj, hx, hy⟩
      · exact notOwned ⟨y, x, adj.symm, hy, hx⟩

/-- **A cycle made of `Y`-edges is a cycle of `Y`.** -/
theorem pieceCycle_of_allOwned {LengthOK : Nat → Prop}
    {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {c : (glue Y (SupportAtom.outside object Z)).Vertex}
    {C : (glue Y (SupportAtom.outside object Z)).graph.Walk c c} (hC : C.IsCycle)
    (hlen : LengthOK C.length)
    (allOwned : ∀ a b, s(a, b) ∈ C.edges → PieceOwns Y (SupportAtom.outside object Z) a b) :
    HasCycleWithLength LengthOK Y.pack := by
  classical
  set O := SupportAtom.outside object Z
  set H := glue Y O
  let pe := pieceEmbedding Y O
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
  have inRange : ∀ a ∈ S, ∃ y, pe y = a := by
    intro a ha
    obtain ⟨b, hb⟩ := cycle_edge_of_mem_support hC ha
    obtain ⟨pl, _, _, hl, _⟩ := allOwned a b hb
    exact ⟨pl, hl⟩
  let g : S → (SupportAtom.boundary object Z).Vertex ⊕ Y.Internal :=
    fun a => Classical.choose (inRange a.1 a.2)
  have hg : ∀ a, pe (g a) = a.1 := fun a => Classical.choose_spec (inRange a.1 a.2)
  let f : (K.induce S) →g Y.graph :=
    { toFun := g
      map_rel' := fun {a b} h => by
        obtain ⟨pl, pr, adj, hl, hr⟩ := allOwned a.1 b.1 h.2
        have ea : g a = pl := pe.injective ((hg a).trans hl.symm)
        have eb : g b = pr := pe.injective ((hg b).trans hr.symm)
        rw [ea, eb]
        exact adj }
  have hf : Function.Injective f := by
    intro a b eq
    apply Subtype.ext
    rw [← hg a, ← hg b]
    exact congrArg pe eq
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
  exact ⟨{ vertex := f ⟨_, hS _ (C.transfer K hK).start_mem_support⟩
           walk := ((C.transfer K hK).induce S hS).map f
           isCycle := hC2.map hf
           length_ok := Eq.mpr
             (congrArg LengthOK ((SimpleGraph.Walk.length_map _ _).trans hlen2)) hlen }⟩

/-- **The substitution lemma.**  Under (i) of dominance, every accepted cycle of
`glue Y (G − Z)` is an accepted cycle of `Y`, or it maps to an accepted cycle of
`G` of the same length: its `Y`-segments are replaced by the realizing linkage
system of `G[Z]` (inside `int(Z)` apart from the terminals), and its outside
segments are kept. -/
theorem cycle_transfer_of_realized {LengthOK : Nat → Prop}
    {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    (realized : ∀ L, IsLinkageSystem Y L → LinkageRealized Y L)
    (cycle : CycleCertificate (glue Y (SupportAtom.outside object Z)) LengthOK) :
    HasCycleWithLength LengthOK Y.pack ∨ Nonempty (CycleCertificate object LengthOK) := by
  classical
  obtain ⟨c, C, hC, hlen⟩ := cycle
  by_cases allOwned : ∀ a b, s(a, b) ∈ C.edges →
      PieceOwns Y (SupportAtom.outside object Z) a b
  · exact Or.inl (pieceCycle_of_allOwned hC hlen allOwned)
  · right
    push Not at allOwned
    obtain ⟨a, b, hab, notOwned⟩ := allOwned
    have acyc := cycleLinkage_isAcyclic hC hab notOwned
    have included := linkageIncluded_withGraph realized
      (L := cycleLinkage C) (fun _ _ h => h.1) acyc
    have hE : ∀ e, e ∈ C.edges →
        e ∈ (glue (withGraph Y (cycleLinkage C)) (SupportAtom.outside object Z)).graph.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
          change (glueGraph (withGraph Y (cycleLinkage C))
            (SupportAtom.outside object Z)).Adj x y
          rw [glueGraph_adj_iff]
          rcases (glueGraph_adj_iff Y (SupportAtom.outside object Z) x y).1
              (C.adj_of_mem_edges he) with ⟨pl, pr, adj, hl, hr⟩ | ⟨cl, cr, adj, hl, hr⟩
          · refine Or.inl ⟨pl, pr, ⟨adj, ?_⟩, (pieceEmbedding_withGraph pl).trans hl,
              (pieceEmbedding_withGraph pr).trans hr⟩
            rw [hl, hr]
            exact he
          · exact Or.inr ⟨cl, cr, adj, (contextEmbedding_withGraph cl).trans hl,
              (contextEmbedding_withGraph cr).trans hr⟩
    exact cycle_transfer included
      ⟨c, C.transfer _ hE, hC.transfer hE,
        Eq.mpr (congrArg LengthOK (SimpleGraph.Walk.length_transfer (p := C) hE)) hlen⟩

/-- **`not_target_glue_of_dominated`**: a target-avoiding `G` and a gadget `Y`
dominated by `G[Z]` give a target-free `glue Y (G − Z)`. -/
theorem not_target_glue_of_dominated {LengthOK : Nat → Prop}
    {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    (avoids : ¬ HasCycleWithLength LengthOK object) (dominated : Dominated LengthOK Y) :
    ¬ HasCycleWithLength LengthOK (glue Y (SupportAtom.outside object Z)) := by
  rintro ⟨cycle⟩
  rcases cycle_transfer_of_realized dominated.1 cycle with own | inG
  · exact dominated.2 own
  · exact avoids inG

/-- A gadget with fewer interior vertices than `G[Z]` glues into a strictly
smaller object. -/
theorem glue_lexicographicallySmaller {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    (smaller : Y.internalVertexCount < (SupportAtom.piece object Z).internalVertexCount) :
    (glue Y (SupportAtom.outside object Z)).LexicographicallySmaller object := by
  apply FiniteObject.lexicographicallySmaller_of_vertexCount_lt
  have same : object.vertexCount =
      (glue (SupportAtom.piece object Z) (SupportAtom.outside object Z)).vertexCount :=
    (FiniteObject.vertexCount_eq_of_isomorphic
      ⟨(SupportAtom.decomposition object Z).reconstructionIso⟩).symm
  rw [same, glue_vertexCount, glue_vertexCount]
  omega

/-- **Dominance irreducibility from `lem:replacement`.**  At a target-avoiding
`G` with no replacement support, no gadget `Y` on the cut boundary of a proper
connected support `Z` with fewer interior vertices than `G[Z]`, the
boundary-degree profile of `G[Z]` and the baseline in `glue Y (G − Z)` is
dominated by `G[Z]`: otherwise `glue Y (G − Z)` is target-free
(`not_target_glue_of_dominated`) and `Y` is a replacement. -/
theorem not_dominated_of_exclusion {Baseline : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (exclusion : ∀ S : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (HasCycleWithLength LengthOK) object S)
    (connected : SupportComponents.Connected.ConnectedOn object Z)
    (proper : ∃ v, v ∉ Z)
    (Y : BoundaryPiece (SupportAtom.boundary object Z))
    (smaller : Y.internalVertexCount < (SupportAtom.piece object Z).internalVertexCount)
    (profile : Y.boundaryDegreeProfile = (SupportAtom.piece object Z).boundaryDegreeProfile)
    (baseline : Baseline (glue Y (SupportAtom.outside object Z))) :
    ¬ Dominated LengthOK Y := fun dominated =>
  exclusion Z ⟨connected, proper, Y, profile, baseline, glue_lexicographicallySmaller smaller,
    not_target_glue_of_dominated avoids dominated⟩

end Dominance

/-! ## The terminal-pair form -/

section TwoTerminal

variable {object : FiniteObject.{u}} {Z : Finset object.Vertex}

/-- `L_Z(a, b)`: the lengths of the `a`–`b` paths of `G` inside `Z`. -/
def pathLengths (object : FiniteObject.{u}) (Z : Finset object.Vertex)
    (a b : object.Vertex) : Set Nat :=
  {length | ∃ q : object.graph.Walk a b, q.IsPath ∧ (∀ w ∈ q.support, w ∈ Z) ∧
    q.length = length}

/-- The lengths of the `u`–`v` paths of a gadget `Y` between two terminals. -/
def gadgetLengths {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    (u v : (SupportAtom.boundary object Z).Vertex) : Set Nat :=
  {length | ∃ p : Y.graph.Walk (.inl u) (.inl v), p.IsPath ∧ p.length = length}

/-- **A two-terminal linkage realized along one path.**  If the linkage `L` of a
two-terminal gadget is carried by one `u`–`v` path `P` and `G` has a `u`–`v`
path `q` inside `Z` of the same length, then sending the `i`-th vertex of `P`
to the `i`-th vertex of `q` realizes `L` in `G[Z]`. -/
theorem linkageRealized_of_path {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {u v : (SupportAtom.boundary object Z).Vertex} (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    {L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal)}
    (P : L.Walk (.inl u) (.inl v)) (hP : P.IsPath)
    (cover : ∀ x y, L.Adj x y → s(x, y) ∈ P.edges)
    (q : object.graph.Walk u.1 v.1) (hq : q.IsPath) (hqZ : ∀ w ∈ q.support, w ∈ Z)
    (hlen : q.length = P.length) :
    LinkageRealized Y L := by
  classical
  have Pinj := hP.getVert_injOn
  have qinj := hq.getVert_injOn
  let φ : Y.Internal → object.Vertex := fun x =>
    if h : (Sum.inr x : (SupportAtom.boundary object Z).Vertex ⊕ Y.Internal) ∈ P.support then
      q.getVert (Classical.choose (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp h))
    else u.1
  -- an interior position carries an interior vertex, and the ends carry `u`, `v`
  have key : ∀ i ≤ P.length, realize φ (P.getVert i) = q.getVert i := by
    intro i hi
    rcases hvi : P.getVert i with b | x
    · rcases two b with rfl | rfl
      · have : i = 0 := Pinj (by simpa using hi) (by simp)
          (by rw [hvi, SimpleGraph.Walk.getVert_zero])
        subst this
        simp [realize]
      · have : i = P.length := Pinj (by simpa using hi) (by simp)
          (by rw [hvi, SimpleGraph.Walk.getVert_length])
        subst this
        rw [← hlen, SimpleGraph.Walk.getVert_length]
        rfl
    · have hx : (Sum.inr x : (SupportAtom.boundary object Z).Vertex ⊕ Y.Internal) ∈
          P.support := hvi ▸ P.getVert_mem_support i
      have spec := Classical.choose_spec (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx)
      have : Classical.choose (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx) = i :=
        Pinj spec.2 hi (spec.1.trans hvi.symm)
      change φ x = _
      simp only [φ, dif_pos hx]
      rw [this]
  -- positions of the interior vertices on the linkage
  have pos : ∀ x a, L.Adj (.inr x) a → ∃ i, 0 < i ∧ i < P.length ∧
      P.getVert i = .inr x ∧ φ x = q.getVert i := by
    intro x a hxa
    have hx := P.fst_mem_support_of_mem_edges (cover _ _ hxa)
    obtain ⟨i, hi, hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    have k := key i hle
    rw [hi] at k
    refine ⟨i, ?_, ?_, hi, k⟩
    · rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        rw [SimpleGraph.Walk.getVert_zero] at hi
        cases hi
      · exact h0
    · rcases Nat.lt_or_ge i P.length with hlt | hge
      · exact hlt
      · have : i = P.length := le_antisymm hle hge
        subst this
        rw [SimpleGraph.Walk.getVert_length] at hi
        cases hi
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x a hxa
    obtain ⟨i, i0, iL, _, hφ⟩ := pos x a hxa
    refine ⟨hφ ▸ hqZ _ (q.getVert_mem_support i), ?_⟩
    intro hb
    rcases two ⟨φ x, hb⟩ with h | h
    · have e : q.getVert i = q.getVert 0 := by
        rw [← hφ, SimpleGraph.Walk.getVert_zero]; exact congrArg Subtype.val h
      have := qinj (by simp only [Set.mem_setOf_eq]; omega) (by simp) e
      omega
    · have e : q.getVert i = q.getVert q.length := by
        rw [← hφ, SimpleGraph.Walk.getVert_length]; exact congrArg Subtype.val h
      have := qinj (by simp only [Set.mem_setOf_eq]; omega) (by simp) e
      omega
  · intro x y a c hxa hyc eq
    obtain ⟨i, _, iL, hi, hφi⟩ := pos x a hxa
    obtain ⟨j, _, jL, hj, hφj⟩ := pos y c hyc
    have ij : i = j := qinj (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) (hφi.symm.trans (eq.trans hφj))
    subst ij
    have := hi.symm.trans hj
    exact Sum.inr_injective this
  · intro a c hac
    obtain ⟨k, hk, h | h⟩ := exists_getVert_of_mem_edges (cover a c hac)
    · rw [h.1, h.2, key k (le_of_lt hk), key (k + 1) hk]
      exact q.adj_getVert_succ (hlen ▸ hk)
    · rw [h.1, h.2, key k (le_of_lt hk), key (k + 1) hk]
      exact (q.adj_getVert_succ (hlen ▸ hk)).symm

/-- **The terminal-pair form of dominance.**  On a support whose cut boundary is
exactly two labels `u ≠ v`, (i) of dominance reduces to the inclusion of the
`u`–`v` path lengths of `Y` in `L_Z(u, v)`: an acyclic linkage of `Y` is empty
or one `u`–`v` path (`exists_path_cover`). -/
theorem linkageSystems_realized_of_twoTerminal
    {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {u v : (SupportAtom.boundary object Z).Vertex} (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (lengths : gadgetLengths (Y := Y) u v ⊆ pathLengths object Z u.1 v.1) :
    ∀ L, IsLinkageSystem Y L → LinkageRealized Y L := by
  classical
  intro L ⟨link, acyc⟩
  letI : Fintype ((SupportAtom.boundary object Z).Vertex ⊕ Y.Internal) := by
    letI : FinEnum (SupportAtom.boundary object Z).Vertex :=
      (SupportAtom.boundary object Z).vertices
    letI : FinEnum Y.Internal := Y.internalVertices
    infer_instance
  by_cases hE : ∃ a c, L.Adj a c
  · obtain ⟨a, c, hac⟩ := hE
    obtain ⟨P, hP, cover⟩ := exists_path_cover (L := L) acyc
      (B := fun x => ∃ b, x = .inl b)
      (fun x hx a hxa => by
        rcases x with b | x
        · exact absurd ⟨b, rfl⟩ hx
        · exact link.internalTwo x a hxa)
      (s := .inl u) (t := .inl v) (fun h => hne (Sum.inl_injective h))
      (fun x ⟨b, hb⟩ => by
        subst hb
        rcases two b with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl)
      hac
    obtain ⟨q, hq, hqZ, hqlen⟩ := lengths
      (show (P.mapLe link.le).length ∈ gadgetLengths (Y := Y) u v from
        ⟨P.mapLe link.le, hP.mapLe link.le, rfl⟩)
    have mapLen : (P.mapLe link.le).length = P.length := SimpleGraph.Walk.length_map _ _
    exact linkageRealized_of_path hne two P hP cover q hq hqZ (hqlen.trans mapLen)
  · push Not at hE
    exact ⟨fun _ => u.1, fun x a h => absurd h (hE _ _), fun x _ a _ h => absurd h (hE _ _),
      fun a c h => absurd h (hE _ _)⟩

/-- **Terminal-pair dominance**: a two-terminal gadget whose `u`–`v` path lengths
lie in `L_Z(u, v)` and which has no accepted cycle is dominated by `G[Z]`. -/
theorem dominated_of_twoTerminal {LengthOK : Nat → Prop}
    {Y : BoundaryPiece (SupportAtom.boundary object Z)}
    {u v : (SupportAtom.boundary object Z).Vertex} (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (lengths : gadgetLengths (Y := Y) u v ⊆ pathLengths object Z u.1 v.1)
    (noCycle : ¬ HasCycleWithLength LengthOK Y.pack) :
    Dominated LengthOK Y :=
  ⟨linkageSystems_realized_of_twoTerminal hne two lengths, noCycle⟩

/-- **Two-exit irreducibility.**  At a target-avoiding `G` with no replacement
support, let `Z` be a proper connected support whose cut boundary is exactly
two labels `u ≠ v`.  Every gadget `Y` on `{u, v}` with fewer interior vertices
than `G[Z]`, the boundary-degree profile of `G[Z]`, the baseline in
`glue Y (G − Z)` and no accepted cycle of its own has a `u`–`v` path whose
length is not the length of any `u`–`v` path of `G` inside `Z`. -/
theorem exists_new_length_of_exclusion {Baseline : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (exclusion : ∀ S : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (HasCycleWithLength LengthOK) object S)
    (connected : SupportComponents.Connected.ConnectedOn object Z)
    (proper : ∃ v, v ∉ Z)
    {u v : (SupportAtom.boundary object Z).Vertex} (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (Y : BoundaryPiece (SupportAtom.boundary object Z))
    (smaller : Y.internalVertexCount < (SupportAtom.piece object Z).internalVertexCount)
    (profile : Y.boundaryDegreeProfile = (SupportAtom.piece object Z).boundaryDegreeProfile)
    (baseline : Baseline (glue Y (SupportAtom.outside object Z)))
    (noCycle : ¬ HasCycleWithLength LengthOK Y.pack) :
    ∃ p : Y.graph.Walk (.inl u) (.inl v), p.IsPath ∧
      p.length ∉ pathLengths object Z u.1 v.1 := by
  by_contra none
  push Not at none
  apply not_dominated_of_exclusion avoids exclusion connected proper Y smaller profile baseline
  apply dominated_of_twoTerminal hne two _ noCycle
  rintro _ ⟨p, hp, rfl⟩
  exact none p hp

end TwoTerminal

/-! ## A two-exit support of G copied onto another one -/

section Copy

variable {object : FiniteObject.{u}} {Z Z' : Finset object.Vertex}

/-- `N_S(a)`: the neighbours of `a` in `G` that lie in `S`. -/
def innerNeighbours (object : FiniteObject.{u}) (S : Finset object.Vertex)
    (a : object.Vertex) : Set object.Vertex :=
  object.graph.neighborSet a ∩ (S : Set object.Vertex)

theorem mem_innerNeighbours {S : Finset object.Vertex} {a w : object.Vertex} :
    w ∈ innerNeighbours object S a ↔ object.graph.Adj a w ∧ w ∈ S := by
  simp [innerNeighbours, SimpleGraph.mem_neighborSet]

theorem pieceDecode_injective (object : FiniteObject.{u}) (Z : Finset object.Vertex) :
    Function.Injective (SupportAtom.pieceDecode object Z) := by
  intro a c h
  rcases a with b | x <;> rcases c with b' | y <;> simp only [SupportAtom.pieceDecode] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd (show y.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) y.2.2
  · exact absurd (show x.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) x.2.2
  · exact congrArg Sum.inr (Subtype.ext h)

theorem mem_range_pieceDecode {w : object.Vertex} :
    w ∈ Set.range (SupportAtom.pieceDecode object Z) ↔ w ∈ Z := by
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with b | x
    · exact cutBoundary_subset b.2
    · exact x.2.1
  · intro hw
    by_cases hb : w ∈ SupportAtom.cutBoundary object Z
    · exact ⟨.inl ⟨w, hb⟩, rfl⟩
    · exact ⟨.inr ⟨w, hw, hb⟩, rfl⟩

/-- The boundary degree of `G[Z]` at a label is its number of neighbours in
`Z`. -/
theorem piece_boundaryDegree (b : (SupportAtom.boundary object Z).Vertex) :
    (SupportAtom.piece object Z).boundaryDegree b = (innerNeighbours object Z b.1).ncard := by
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  change ((SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph).neighborSet
    (.inl b)).ncard = _
  rw [ncard_neighborSet_comap _ _ (pieceDecode_injective object Z)]
  congr 1
  ext w
  rw [mem_innerNeighbours, Set.mem_setOf_eq, mem_range_pieceDecode]
  rfl

open Classical in
/-- The vertex map of the copy of `G[Z']` onto the labels of `∂Z`: the labels
`u` and `v` of `∂Z` go to the terminals `u'` and `v'` of `Z'`, and the interior
of `Z'` goes to itself. -/
noncomputable def copyDecode (u : (SupportAtom.boundary object Z).Vertex)
    (u' v' : (SupportAtom.boundary object Z').Vertex) :
    (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z' →
      object.Vertex
  | .inl b => if b = u then u'.1 else v'.1
  | .inr x => x.1

/-- **The copy of G's two-exit piece `G[Z']` onto `∂Z = {u, v}`**: a gadget on
`∂Z` whose interior is the interior of `Z'` and whose edges are the edges of
`G` among `Z'`, with `u, v` read as the terminals `u', v'` of `Z'`.  It is
constructed from G's own data (no choice). -/
noncomputable def copyPiece (u : (SupportAtom.boundary object Z).Vertex)
    (u' v' : (SupportAtom.boundary object Z').Vertex) :
    BoundaryPiece (SupportAtom.boundary object Z) where
  Internal := SupportAtom.PieceInternal object Z'
  internalVertices := (SupportAtom.piece object Z').internalVertices
  graph := SimpleGraph.comap (copyDecode u u' v') object.graph
  decideAdj := Classical.decRel _

variable {u v : (SupportAtom.boundary object Z).Vertex}
  {u' v' : (SupportAtom.boundary object Z').Vertex}

theorem copyDecode_left : copyDecode u u' v' (.inl u) = u'.1 := by
  simp [copyDecode]

theorem copyDecode_right (hne : u ≠ v) : copyDecode u u' v' (.inl v) = v'.1 := by
  simp [copyDecode, hne.symm]

theorem copyDecode_injective (two : ∀ b, b = u ∨ b = v) (hne' : u' ≠ v') :
    Function.Injective (copyDecode u u' v') := by
  classical
  have inner : ∀ (b : (SupportAtom.boundary object Z).Vertex)
      (x : SupportAtom.PieceInternal object Z'), copyDecode u u' v' (.inl b) ≠ x.1 := by
    intro b x h
    apply x.2.2
    by_cases hb : b = u
    · simp only [copyDecode, hb, if_true] at h
      exact h ▸ u'.2
    · simp only [copyDecode, hb, if_false] at h
      exact h ▸ v'.2
  intro a c h
  rcases a with b | x <;> rcases c with b' | y
  · by_cases hb : b = u <;> by_cases hb' : b' = u
    · rw [hb, hb']
    · exfalso
      simp only [copyDecode, hb, hb', if_true, if_false] at h
      exact hne' (Subtype.ext h)
    · exfalso
      simp only [copyDecode, hb, hb', if_true, if_false] at h
      exact hne' (Subtype.ext h.symm)
    · have h1 := (two b).resolve_left hb
      have h2 := (two b').resolve_left hb'
      rw [h1, h2]
  · exact absurd h (inner b y)
  · exact absurd h.symm (inner b' x)
  · exact congrArg Sum.inr (Subtype.ext h)

theorem mem_range_copyDecode (hne : u ≠ v) (two' : ∀ b, b = u' ∨ b = v')
    {w : object.Vertex} :
    w ∈ Set.range (copyDecode u u' v') ↔ w ∈ Z' := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with b | x
    · by_cases hb : b = u
      · subst hb
        rw [copyDecode_left]
        exact cutBoundary_subset u'.2
      · rcases two' u' with _ | _ <;> simp only [copyDecode, hb, if_false] <;>
          exact cutBoundary_subset v'.2
    · exact x.2.1
  · intro hw
    by_cases hb : w ∈ SupportAtom.cutBoundary object Z'
    · rcases two' ⟨w, hb⟩ with h | h
      · exact ⟨.inl u, by rw [copyDecode_left, ← h]⟩
      · exact ⟨.inl v, by rw [copyDecode_right hne, ← h]⟩
    · exact ⟨.inr ⟨w, hw, hb⟩, rfl⟩

/-- The copy has no accepted cycle: it is a subgraph of `G`. -/
theorem copyPiece_not_target {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (two : ∀ b, b = u ∨ b = v) (hne' : u' ≠ v') :
    ¬ HasCycleWithLength LengthOK (copyPiece u u' v').pack := fun cycle =>
  avoids (hasCycleWithLength_of_hom
    ({ toFun := copyDecode u u' v', map_rel' := fun h => h } :
      (copyPiece u u' v').pack.graph →g object.graph)
    (copyDecode_injective two hne') cycle)

/-- The `u`–`v` path lengths of the copy are `u'`–`v'` path lengths of `G`
inside `Z'`. -/
theorem copyPiece_gadgetLengths (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (hne' : u' ≠ v') (two' : ∀ b, b = u' ∨ b = v') :
    gadgetLengths (Y := copyPiece u u' v') u v ⊆ pathLengths object Z' u'.1 v'.1 := by
  rintro _ ⟨p, hp, rfl⟩
  let f : (copyPiece u u' v').graph →g object.graph :=
    { toFun := copyDecode u u' v', map_rel' := fun h => h }
  have inj : Function.Injective f := copyDecode_injective two hne'
  refine ⟨(p.map f).copy copyDecode_left (copyDecode_right hne), ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective inj hp
  · intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hw
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
    exact (mem_range_copyDecode hne two').1 ⟨a, rfl⟩
  · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]

theorem copyPiece_boundaryDegree (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (hne' : u' ≠ v') (two' : ∀ b, b = u' ∨ b = v')
    (b : (SupportAtom.boundary object Z).Vertex) :
    (copyPiece u u' v').boundaryDegree b =
      (innerNeighbours object Z' (copyDecode u u' v' (.inl b))).ncard := by
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  change ((SimpleGraph.comap (copyDecode u u' v') object.graph).neighborSet
    (.inl b)).ncard = _
  rw [ncard_neighborSet_comap _ _ (copyDecode_injective two hne')]
  congr 1
  ext w
  rw [mem_innerNeighbours, Set.mem_setOf_eq, mem_range_copyDecode hne two']

/-- **The copy keeps the boundary-degree profile of `G[Z]`** when each terminal
of `Z'` has as many neighbours in `Z'` as the matching terminal of `Z` has in
`Z`. -/
theorem copyPiece_profile (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (hne' : u' ≠ v') (two' : ∀ b, b = u' ∨ b = v')
    (degU : (innerNeighbours object Z' u'.1).ncard = (innerNeighbours object Z u.1).ncard)
    (degV : (innerNeighbours object Z' v'.1).ncard = (innerNeighbours object Z v.1).ncard) :
    (copyPiece u u' v').boundaryDegreeProfile =
      (SupportAtom.piece object Z).boundaryDegreeProfile := by
  funext b
  change (copyPiece u u' v').boundaryDegree b = (SupportAtom.piece object Z).boundaryDegree b
  rw [copyPiece_boundaryDegree hne two hne' two' b, piece_boundaryDegree b]
  rcases two b with rfl | rfl
  · rw [copyDecode_left]
    exact degU
  · rw [copyDecode_right hne]
    exact degV

/-- **The copy keeps the baseline**: glued into `G − Z`, every vertex has at
least its degree in `G` (interior vertices of `Z'` keep all their neighbours,
vertices of `G − Z` keep theirs, and a terminal trades its neighbours in `Z`
for as many in the copy). -/
theorem copyPiece_baseline {k : Nat} (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (two' : ∀ b, b = u' ∨ b = v')
    (base : ∀ w, k ≤ object.degree w)
    (degU : (innerNeighbours object Z' u'.1).ncard = (innerNeighbours object Z u.1).ncard)
    (degV : (innerNeighbours object Z' v'.1).ncard = (innerNeighbours object Z v.1).ncard) :
    MinimumDegreeAtLeast k (glue (copyPiece u u' v') (SupportAtom.outside object Z)) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : FinEnum (glue (copyPiece u u' v') (SupportAtom.outside object Z)).Vertex :=
    (glue (copyPiece u u' v') (SupportAtom.outside object Z)).vertices
  have rangeY : ∀ y ∈ Z', ∃ a, copyDecode u u' v' a = y :=
    fun y hy => (mem_range_copyDecode hne two').2 hy
  let pe := pieceEmbedding (copyPiece u u' v') (SupportAtom.outside object Z)
  let ce := contextEmbedding (copyPiece u u' v') (SupportAtom.outside object Z)
  let encY : object.Vertex → (glue (copyPiece u u' v') (SupportAtom.outside object Z)).Vertex :=
    fun y => if h : y ∈ Z' then pe (Classical.choose (rangeY y h)) else .inl u
  have encY_eq : ∀ y (h : y ∈ Z'), encY y = pe (Classical.choose (rangeY y h)) :=
    fun y h => dif_pos h
  have encY_inj : Set.InjOn encY (Z' : Set object.Vertex) := by
    intro y hy y' hy' e
    rw [encY_eq y hy, encY_eq y' hy'] at e
    have := congrArg (copyDecode u u' v') (pe.injective e)
    exact (Classical.choose_spec (rangeY y hy)).symm.trans
      (this.trans (Classical.choose_spec (rangeY y' hy')))
  have encY_adj : ∀ a y (h : y ∈ Z'), object.graph.Adj (copyDecode u u' v' a) y →
      (glue (copyPiece u u' v') (SupportAtom.outside object Z)).graph.Adj (pe a) (encY y) := by
    intro a y h adj
    rw [encY_eq y h]
    refine (glueGraph_adj_iff _ _ _ _).2 (Or.inl ⟨a, _, ?_, rfl, rfl⟩)
    change object.graph.Adj (copyDecode u u' v' a)
      (copyDecode u u' v' (Classical.choose (rangeY y h)))
    rw [Classical.choose_spec (rangeY y h)]
    exact adj
  let encO : object.Vertex → (glue (copyPiece u u' v') (SupportAtom.outside object Z)).Vertex :=
    fun y => if hb : y ∈ SupportAtom.cutBoundary object Z then .inl ⟨y, hb⟩
      else if hz : y ∉ Z then .inr (.inr ⟨y, hz⟩) else .inl u
  have encO_spec : ∀ y, (y ∉ Z ∨ y ∈ SupportAtom.cutBoundary object Z) →
      ∃ ca, ce ca = encO y ∧ SupportAtom.outsideDecode object Z ca = y := by
    intro y hy
    by_cases hb : y ∈ SupportAtom.cutBoundary object Z
    · refine ⟨.inl ⟨y, hb⟩, ?_, rfl⟩
      show Sum.inl ⟨y, hb⟩ = encO y
      simp only [encO]
      rw [dif_pos hb]
    · have hz : y ∉ Z := hy.resolve_right hb
      refine ⟨.inr ⟨y, hz⟩, ?_, rfl⟩
      show Sum.inr (Sum.inr ⟨y, hz⟩) = encO y
      simp only [encO]
      rw [dif_neg hb, dif_pos hz]
  have encO_inj : Set.InjOn encO {y | y ∉ Z ∨ y ∈ SupportAtom.cutBoundary object Z} := by
    intro y hy y' hy' e
    obtain ⟨ca, hca, hda⟩ := encO_spec y hy
    obtain ⟨cb, hcb, hdb⟩ := encO_spec y' hy'
    rw [← hca, ← hcb] at e
    rw [← hda, ← hdb, ce.injective e]
  have encO_adj : ∀ ca y, (y ∉ Z ∨ y ∈ SupportAtom.cutBoundary object Z) →
      object.graph.Adj (SupportAtom.outsideDecode object Z ca) y →
      (glue (copyPiece u u' v') (SupportAtom.outside object Z)).graph.Adj (ce ca) (encO y) := by
    intro ca y hy adj
    obtain ⟨cb, hcb, hdb⟩ := encO_spec y hy
    rw [← hcb]
    refine (glueGraph_adj_iff _ _ _ _).2 (Or.inr ⟨ca, cb, ?_, rfl, rfl⟩)
    change object.graph.Adj (SupportAtom.outsideDecode object Z ca)
      (SupportAtom.outsideDecode object Z cb)
    rw [hdb]
    exact adj
  haveI : Nonempty (glue (copyPiece u u' v') (SupportAtom.outside object Z)).Vertex :=
    ⟨.inl u⟩
  change k ≤ (glue (copyPiece u u' v') (SupportAtom.outside object Z)).minDegree
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro w
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  rcases w with b | (x | o)
  · have deg := base b.1
    rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
    have split := Set.ncard_inter_add_ncard_sdiff_eq_ncard
      (object.graph.neighborSet b.1) (Z : Set object.Vertex) (Set.toFinite _)
    have profileEq : (innerNeighbours object Z' (copyDecode u u' v' (.inl b))).ncard =
        (innerNeighbours object Z b.1).ncard := by
      rcases two b with rfl | rfl
      · rw [copyDecode_left]
        exact degU
      · rw [copyDecode_right hne]
        exact degV
    have hA : (encO '' (object.graph.neighborSet b.1 \ (Z : Set object.Vertex))).ncard =
        (object.graph.neighborSet b.1 \ (Z : Set object.Vertex)).ncard :=
      (encO_inj.mono (fun y hy => Or.inl hy.2)).ncard_image
    have hB : (encY '' innerNeighbours object Z' (copyDecode u u' v' (.inl b))).ncard =
        (innerNeighbours object Z' (copyDecode u u' v' (.inl b))).ncard :=
      (encY_inj.mono (fun y hy => hy.2)).ncard_image
    have disj : Disjoint (encO '' (object.graph.neighborSet b.1 \ (Z : Set object.Vertex)))
        (encY '' innerNeighbours object Z' (copyDecode u u' v' (.inl b))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', e⟩
      have hz : y ∉ Z := hy.2
      have hb' : y ∉ SupportAtom.cutBoundary object Z := fun h => hz (cutBoundary_subset h)
      rw [encY_eq y' hy'.2] at e
      have eO : encO y = .inr (.inr ⟨y, hz⟩) := (dif_neg hb').trans (dif_pos hz)
      rw [eO] at e
      have key : ∀ a, pieceEmbedding (copyPiece u u' v') (SupportAtom.outside object Z) a ≠
          Sum.inr (Sum.inr ⟨y, hz⟩) := by
        intro a h
        rcases a with a | a <;> cases h
      exact key _ e
    have sub : encO '' (object.graph.neighborSet b.1 \ (Z : Set object.Vertex)) ∪
        encY '' innerNeighbours object Z' (copyDecode u u' v' (.inl b)) ⊆
        (glue (copyPiece u u' v') (SupportAtom.outside object Z)).graph.neighborSet (.inl b) := by
      rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact encO_adj (.inl b) y (Or.inl hy.2) hy.1
      · exact encY_adj (.inl b) y hy.2 hy.1
    have le := Set.ncard_le_ncard sub (Set.toFinite _)
    rw [Set.ncard_union_eq disj (Set.toFinite _) (Set.toFinite _), hA, hB, profileEq] at le
    unfold innerNeighbours at le
    omega
  · have nbZ' : ∀ y, object.graph.Adj x.1 y → y ∈ Z' := by
      intro y adj
      by_contra hy
      exact x.2.2 ((SupportAtom.mem_cutBoundary_iff object Z' x.1).2 ⟨x.2.1, y, adj, hy⟩)
    have deg := base x.1
    rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
    have le : (object.graph.neighborSet x.1).ncard ≤
        ((glue (copyPiece u u' v') (SupportAtom.outside object Z)).graph.neighborSet
          (.inr (.inl x))).ncard :=
      Set.ncard_le_ncard_of_injOn encY (fun y hy => encY_adj (.inr x) y (nbZ' y hy) hy)
        (encY_inj.mono (fun y hy => nbZ' y hy)) (Set.toFinite _)
    omega
  · have nbOK : ∀ y, object.graph.Adj o.1 y →
        y ∉ Z ∨ y ∈ SupportAtom.cutBoundary object Z := by
      intro y adj
      by_cases hz : y ∈ Z
      · exact Or.inr ((SupportAtom.mem_cutBoundary_iff object Z y).2 ⟨hz, o.1, adj.symm, o.2⟩)
      · exact Or.inl hz
    have deg := base o.1
    rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
    have le : (object.graph.neighborSet o.1).ncard ≤
        ((glue (copyPiece u u' v') (SupportAtom.outside object Z)).graph.neighborSet
          (.inr (.inr o))).ncard :=
      Set.ncard_le_ncard_of_injOn encO (fun y hy => encO_adj (.inr o) y (nbOK y hy) hy)
        (encO_inj.mono (fun y hy => nbOK y hy)) (Set.toFinite _)
    omega

/-- **Two-exit size monotonicity at G.**  At a target-avoiding `G` of minimum
degree at least `k` with no replacement support, let `Z` be a proper connected
support with cut boundary `{u, v}` and `Z'` a support with cut boundary
`{u', v'}` whose terminals have as many neighbours in `Z'` as `u, v` have in
`Z`.  If every `u'`–`v'` path length inside `Z'` is a `u`–`v` path length
inside `Z` (`L_{Z'}(u', v') ⊆ L_Z(u, v)`), then `Z` has at most as many interior
vertices as `Z'`: otherwise the copy of `G[Z']` onto `{u, v}` is a strictly
smaller, profile-preserving, baseline-keeping gadget dominated by `G[Z]`. -/
theorem internalVertexCount_le_of_twoExit {k : Nat} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (exclusion : ∀ S : Finset object.Vertex,
      ¬ ReplacementSupport (MinimumDegreeAtLeast k) (HasCycleWithLength LengthOK) object S)
    (base : MinimumDegreeAtLeast k object)
    (connected : SupportComponents.Connected.ConnectedOn object Z)
    (proper : ∃ w, w ∉ Z)
    (hne : u ≠ v) (two : ∀ b, b = u ∨ b = v)
    (hne' : u' ≠ v') (two' : ∀ b, b = u' ∨ b = v')
    (degU : (innerNeighbours object Z' u'.1).ncard = (innerNeighbours object Z u.1).ncard)
    (degV : (innerNeighbours object Z' v'.1).ncard = (innerNeighbours object Z v.1).ncard)
    (lengths : pathLengths object Z' u'.1 v'.1 ⊆ pathLengths object Z u.1 v.1) :
    (SupportAtom.piece object Z).internalVertexCount ≤
      (SupportAtom.piece object Z').internalVertexCount := by
  by_contra lt
  push Not at lt
  exact not_dominated_of_exclusion avoids exclusion connected proper (copyPiece u u' v') lt
    (copyPiece_profile hne two hne' two' degU degV)
    (copyPiece_baseline hne two two'
      (fun w => le_trans base (object.minDegree_le_degree w)) degU degV)
    (dominated_of_twoTerminal hne two
      (fun _ h => lengths (copyPiece_gadgetLengths hne two hne' two' h))
      (copyPiece_not_target avoids two hne'))

end Copy

end Hypostructure.Graph.DominatedReplacement
