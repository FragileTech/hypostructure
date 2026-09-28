import Hypostructure.Graph.GluedReadingMaps

/-!
# The single-edge context between two boundary vertices

For a support `Z` and two boundary vertices `a ≠ b` of `∂Z`, the single-edge
context `a — b` is the `∂Z`-boundaried context with no internal vertex and the
one edge `ab`.  On a target-avoiding object, a reading `ret_R` glued to it has an
accepted cycle iff `ret_R` has an `a → b` path avoiding `ab` of accepted-minus-one
length; if `a ~ b` in the ambient object, return avoidance excludes every such
path.  Every path between two labels of the single-edge context has length one.

All results are vocabulary-free: they hold for every finite object, support and
reading.
-/

namespace Hypostructure.Graph.SingleEdgeContext

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Classical

universe u

variable {object : FiniteObject.{u}}

/-- Lemma P (vocabulary-free): a path starting at `u` that uses the edge `uz`
uses it first. -/
theorem path_first_edge {V : Type*} {G : SimpleGraph V} :
    ∀ {u v z : V} (p : G.Walk u v), p.IsPath → s(u, z) ∈ p.edges →
      ∃ (h : G.Adj u z) (r : G.Walk z v), p = .cons h r
  | _, _, _, .nil, _, mem => by simp at mem
  | u, v, z, .cons (v := w) h r, path, mem => by
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at mem
      rcases mem with eq | mem
      · rcases Sym2.eq_iff.1 eq with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨h, r, rfl⟩
        · exact absurd h (G.loopless.irrefl _)
      · exact absurd (r.fst_mem_support_of_mem_edges mem)
          ((SimpleGraph.Walk.cons_isPath_iff h r).1 path).2

/-- **Cycle-through-edge decomposition** (vocabulary-free): a cycle using the
edge `ab` yields an `a`–`b` path avoiding `ab` of length one less. -/
theorem cycle_through_edge {V : Type*} {G : SimpleGraph V} {v a b : V}
    (c : G.Walk v v) (cyc : c.IsCycle) (mem : s(a, b) ∈ c.edges) :
    ∃ w : G.Walk a b, w.IsPath ∧ s(a, b) ∉ w.edges ∧ w.length + 1 = c.length := by
  have aSupp : a ∈ c.support := c.fst_mem_support_of_mem_edges mem
  let c1 := c.rotate a aSupp
  have cyc1 : c1.IsCycle := cyc.rotate aSupp
  have mem1 : s(a, b) ∈ c1.edges :=
    (SimpleGraph.Walk.rotate_edges c a aSupp).mem_iff.2 mem
  have len1 : c1.length = c.length := SimpleGraph.Walk.length_rotate c a aSupp
  rw [← len1]
  clear_value c1
  cases c1 with
  | nil => exact absurd cyc1 SimpleGraph.Walk.IsCycle.not_of_nil
  | cons h1 q1 =>
    rename_i x
    obtain ⟨qPath, qFresh⟩ := (SimpleGraph.Walk.cons_isCycle_iff q1 h1).1 cyc1
    by_cases hx : x = b
    · subst hx
      refine ⟨q1.reverse, qPath.reverse, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
        exact qFresh
      · simp
    · have memq : s(a, b) ∈ q1.edges := by
        rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at mem1
        rcases mem1 with eq | m
        · rcases Sym2.eq_iff.1 eq with ⟨-, h⟩ | ⟨h, -⟩
          · exact absurd h.symm hx
          · subst h; exact absurd h1 (G.loopless.irrefl _)
        · exact m
      have memr : s(a, b) ∈ q1.reverse.edges := by
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact memq
      obtain ⟨hab, r, hr⟩ := path_first_edge q1.reverse qPath.reverse memr
      have rPath : r.IsPath := by
        have := qPath.reverse; rw [hr] at this
        exact ((SimpleGraph.Walk.cons_isPath_iff hab r).1 this).1
      have aNot : a ∉ r.support := by
        have := qPath.reverse; rw [hr] at this
        exact ((SimpleGraph.Walk.cons_isPath_iff hab r).1 this).2
      have abNot : s(a, b) ∉ r.edges := by
        have := qPath.reverse.edges_nodup; rw [hr, SimpleGraph.Walk.edges_cons] at this
        exact (List.nodup_cons.1 this).1
      have lenq : q1.length = r.length + 1 := by
        have := congrArg SimpleGraph.Walk.length hr
        simp at this; omega
      refine ⟨.cons h1 r.reverse, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        exact ⟨rPath.reverse, by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact aNot⟩
      · rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or]
        refine ⟨?_, ?_⟩
        · intro eq
          rcases Sym2.eq_iff.1 eq with ⟨-, h⟩ | ⟨h, -⟩
          · exact hx h.symm
          · subst h; exact absurd h1 (G.loopless.irrefl _)
        · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact abNot
      · simp [lenq]


/-! ### The single-edge context `a — b` on `∂Z` -/

/-- The boundaried context consisting of one edge between two boundary
vertices and nothing else. -/
noncomputable def edgeContext (Z : Finset object.Vertex)
    (a b : (SupportAtom.boundary object Z).Vertex) :
    OutsideContext (SupportAtom.boundary object Z) where
  Internal := PEmpty.{u + 1}
  internalVertices := inferInstance
  graph := SimpleGraph.fromEdgeSet {s(.inl a, .inl b)}
  decideAdj := Classical.decRel _

variable {Z R : Finset object.Vertex} {a b : (SupportAtom.boundary object Z).Vertex}

/-- Glued vertex of a boundary vertex. -/
abbrev gl (Z R : Finset object.Vertex) (a b : (SupportAtom.boundary object Z).Vertex)
    (x : (SupportAtom.boundary object Z).Vertex) :
    (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b)).Vertex :=
  .inl x

/-- The glued graph without the context edge. -/
noncomputable abbrev pieceSide (Z R : Finset object.Vertex)
    (a b : (SupportAtom.boundary object Z).Vertex) :=
  (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b)).graph.deleteEdges
    {s(gl Z R a b a, gl Z R a b b)}

/-- Pull a glued vertex back to the piece side (the context has no internal
vertices). -/
def pull : (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b)).Vertex →
    (SupportAtom.boundary object Z).Vertex ⊕ (SupportAtom.retainedPiece object Z R).Internal
  | .inl x => .inl x
  | .inr (.inl w) => .inr w
  | .inr (.inr o) => o.elim

theorem pull_injective :
    Function.Injective (pull (object := object) (Z := Z) (R := R) (a := a) (b := b)) := by
  intro x y h
  rcases x with x | x | x <;> rcases y with y | y | y <;>
    first | exact x.elim | exact y.elim | simp_all [pull]

/-- The pull-back is a graph homomorphism from the piece side of the gluing to
the reading. -/
noncomputable def pullHom : (pieceSide Z R a b) →g (SupportAtom.retainedPiece object Z R).graph where
  toFun := pull
  map_rel' := by
    intro x y adj
    rw [SimpleGraph.deleteEdges_adj] at adj
    obtain ⟨gadj, notE⟩ := adj
    rcases (glueGraph_adj_iff _ _ x y).1 gadj with owns | owns
    · obtain ⟨pl, pr, padj, rfl, rfl⟩ := owns
      rcases pl with pl | pl <;> rcases pr with pr | pr <;> exact padj
    · exfalso
      obtain ⟨cl, cr, cadj, rfl, rfl⟩ := owns
      change (SimpleGraph.fromEdgeSet _).Adj _ _ at cadj
      rw [SimpleGraph.fromEdgeSet_adj] at cadj
      have ceq : s(cl, cr) = s(.inl a, .inl b) := cadj.1
      apply notE
      show _ = _
      rcases cl with cl | cl
      · rcases cr with cr | cr
        · rcases Sym2.eq_iff.1 ceq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · cases h1; cases h2; rfl
          · cases h1; cases h2; exact Sym2.eq_swap
        · exact cr.elim
      · exact cl.elim

/-- Push the reading into the gluing. -/
noncomputable def pushHom :
    (SupportAtom.retainedPiece object Z R).graph →g
      (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b)).graph where
  toFun := pieceEmbedding _ _
  map_rel' := by
    intro x y adj
    exact (glueGraph_adj_iff _ _ _ _).2 (Or.inl ⟨x, y, adj, rfl, rfl⟩)

theorem pushHom_injective :
    Function.Injective (pushHom (object := object) (Z := Z) (R := R) (a := a) (b := b)) :=
  (pieceEmbedding _ _).injective

/-- **Single-edge context transfer, forward** (vocabulary-free). -/
theorem edgeContext_cycle_of_path {L : Nat → Prop} (ne : a ≠ b)
    (p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b))
    (path : p.IsPath) (fresh : s(.inl a, .inl b) ∉ p.edges) (ok : L (p.length + 1)) :
    HasCycleWithLength L (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b)) := by
  have hab : (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b)).graph.Adj
      (gl Z R a b a) (gl Z R a b b) := by
    refine (glueGraph_adj_iff _ _ _ _).2 (Or.inr ⟨.inl a, .inl b, ?_, rfl, rfl⟩)
    change (SimpleGraph.fromEdgeSet _).Adj _ _
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_singleton _, fun h => ne (Sum.inl_injective h)⟩
  let q := (p.map (pushHom (a := a) (b := b))).reverse
  have qPath : q.IsPath := (SimpleGraph.Walk.map_isPath_of_injective pushHom_injective path).reverse
  have qFresh : s(gl Z R a b a, gl Z R a b b) ∉ q.edges := by
    intro mem
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse, SimpleGraph.Walk.edges_map,
      List.mem_map] at mem
    obtain ⟨e, he, eq⟩ := mem
    apply fresh
    have : e = s(.inl a, .inl b) := by
      apply Sym2.map.injective pushHom_injective
      rw [eq]; rfl
    exact this ▸ he
  refine ⟨⟨_, .cons hab q, (SimpleGraph.Walk.cons_isCycle_iff q hab).2 ⟨qPath, ?_⟩, ?_⟩⟩
  · intro mem; exact qFresh (by rwa [Sym2.eq_swap] at mem ⊢)
  · convert ok using 2
    simp [q]
    exact (SimpleGraph.Walk.length_map _ _).trans (SimpleGraph.Walk.length_reverse _)


/-- The reading embeds in G. -/
noncomputable def readingHom (Z R : Finset object.Vertex) :
    (SupportAtom.retainedPiece object Z R).graph →g object.graph where
  toFun := SupportAtom.pieceDecode object Z
  map_rel' := fun h => h.1

theorem readingHom_injective (Z R : Finset object.Vertex) :
    Function.Injective (readingHom (object := object) Z R) := by
  intro x y h
  rcases x with a | a <;> rcases y with b | b <;>
    simp [readingHom, SupportAtom.pieceDecode] at h
  · exact congrArg Sum.inl h
  · exact absurd (h ▸ a.2) b.2.2
  · exact absurd (h ▸ b.2) a.2.2
  · exact congrArg Sum.inr (Subtype.ext h)

/-- **Single-edge context transfer, backward** (vocabulary-free): on a
target-avoiding object, every accepted cycle of a reading glued to the context
edge `ab` is the edge plus an `a`–`b` path of the reading avoiding `ab`. -/
theorem path_of_edgeContext_cycle {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (cyc : HasCycleWithLength L (glue (SupportAtom.retainedPiece object Z R) (edgeContext Z a b))) :
    ∃ p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b),
      p.IsPath ∧ s(.inl a, .inl b) ∉ p.edges ∧ L (p.length + 1) := by
  obtain ⟨c⟩ := cyc
  by_cases mem : s(gl Z R a b a, gl Z R a b b) ∈ c.walk.edges
  · obtain ⟨w, wPath, wFresh, wLen⟩ := cycle_through_edge c.walk c.isCycle mem
    have hw : ∀ e ∈ w.edges, e ∈ (pieceSide Z R a b).edgeSet := by
      intro e he
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨w.edges_subset_edgeSet he, fun h => wFresh ((Set.mem_singleton_iff.1 h) ▸ he)⟩
    refine ⟨(w.transfer _ hw).map pullHom,
      SimpleGraph.Walk.map_isPath_of_injective pull_injective (wPath.transfer hw), ?_, ?_⟩
    · intro m0
      have m : s(pull (gl Z R a b a), pull (gl Z R a b b)) ∈
          ((w.transfer _ hw).map pullHom).edges := m0
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at m
      obtain ⟨e, he, eq⟩ := m
      rw [SimpleGraph.Walk.edges_transfer] at he
      apply wFresh
      have : e = s(gl Z R a b a, gl Z R a b b) := by
        apply Sym2.map.injective pull_injective
        exact eq
      exact this ▸ he
    · show L (((w.transfer _ hw).map pullHom).length + 1)
      rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_transfer, wLen]
      exact c.length_ok
  · exfalso
    have hc : ∀ e ∈ c.walk.edges, e ∈ (pieceSide Z R a b).edgeSet := by
      intro e he
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨c.walk.edges_subset_edgeSet he, fun h => mem ((Set.mem_singleton_iff.1 h) ▸ he)⟩
    let f := (readingHom Z R).comp (pullHom (Z := Z) (R := R) (a := a) (b := b))
    have finj : Function.Injective f :=
      (readingHom_injective Z R).comp pull_injective
    exact avoids ⟨⟨_, (c.walk.transfer _ hc).map f,
      (c.isCycle.transfer hc).map finj, by
        rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_transfer]
        exact c.length_ok⟩⟩


/-- A reading path between adjacent boundary vertices that avoids their edge is
a return of that edge in G.  So by `K .returnAvoidance` the single-edge spectrum
is empty on both sides whenever `a ~ b` in G: the transfer bites exactly on
non-adjacent boundary pairs. -/
theorem no_spectrum_of_adj {L : Nat → Prop}
    (returnAvoidance : ∀ dart : object.graph.Dart,
      Disjoint (returnLengthSet object dart) (shiftedAcceptedSet L))
    (adj : object.graph.Adj b.1 a.1)
    (p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b))
    (path : p.IsPath) (fresh : s(.inl a, .inl b) ∉ p.edges) : ¬ L (p.length + 1) := by
  intro ok
  let d : object.graph.Dart := ⟨(b.1, a.1), adj⟩
  have hp : ∀ e ∈ (p.map (readingHom Z R)).edges,
      e ∈ (object.graph.deleteEdges {d.edge}).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨(p.map (readingHom Z R)).edges_subset_edgeSet he, ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', eq⟩ := he
    apply fresh
    have : e' = s(.inl a, .inl b) := by
      apply Sym2.map.injective (readingHom_injective Z R)
      rw [eq, h]
      change s(b.1, a.1) = s(a.1, b.1)
      exact Sym2.eq_swap
    exact this ▸ he'
  have mem : p.length ∈ returnLengthSet object d :=
    ⟨(p.map (readingHom Z R)).transfer _ hp,
      (SimpleGraph.Walk.map_isPath_of_injective (readingHom_injective Z R) path).transfer hp,
      (SimpleGraph.Walk.length_transfer _ _).trans (SimpleGraph.Walk.length_map _ _)⟩
  exact Set.disjoint_left.1 (returnAvoidance d) mem ok


/-- The single-edge context `a — b` is positive for a reading iff the reading
has an `a → b` path avoiding `ab` of accepted-minus-one length. -/
theorem edgeContext_positive_iff {G : FiniteObject.{u}} {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L G) {Z R : Finset G.Vertex}
    {a b : (SupportAtom.boundary G Z).Vertex} (ne : a ≠ b) :
    HasCycleWithLength L
        (glue (SupportAtom.retainedPiece G Z R) (edgeContext Z a b)) ↔
      ∃ p : (SupportAtom.retainedPiece G Z R).graph.Walk (.inl a) (.inl b),
        p.IsPath ∧ s(.inl a, .inl b) ∉ p.edges ∧ L (p.length + 1) :=
  ⟨path_of_edgeContext_cycle avoids,
    fun ⟨p, hp, hf, hl⟩ => edgeContext_cycle_of_path ne p hp hf hl⟩

/-- A path between two labels in a single-edge context has length exactly `1`. -/
theorem edgeContext_path_length {G : FiniteObject.{u}} {Z : Finset G.Vertex}
    {a b : (SupportAtom.boundary G Z).Vertex} {x y : (SupportAtom.boundary G Z).Vertex}
    (xy : x ≠ y)
    (σ : (edgeContext Z a b).graph.Walk (.inl x) (.inl y)) (hσ : σ.IsPath) :
    σ.length = 1 := by
  classical
  have pos : 1 ≤ σ.length := by
    rcases σ with _ | ⟨_, _⟩
    · exact absurd rfl xy
    · simp
  have sub : σ.edges.toFinset ⊆ {s(Sum.inl a, Sum.inl b)} := by
    intro e he
    have := σ.edges_subset_edgeSet (List.mem_toFinset.1 he)
    change e ∈ (SimpleGraph.fromEdgeSet _).edgeSet at this
    rw [SimpleGraph.edgeSet_fromEdgeSet] at this
    exact Finset.mem_singleton.2 (Set.mem_singleton_iff.1 this.1)
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hσ.edges_nodup, SimpleGraph.Walk.length_edges,
    Finset.card_singleton] at card
  omega

end Hypostructure.Graph.SingleEdgeContext
