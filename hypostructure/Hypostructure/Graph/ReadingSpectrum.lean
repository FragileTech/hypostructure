import Hypostructure.Graph.ReadingProfiles

/-!
# Reading spectra: edge contexts and degree-two chain contexts

For two boundary vertices `a ≠ b` of a support `Z`, the outside context made of
the single edge `ab` (`edgeContext`), or of a chain of `m` new degree-two
vertices from `a` to `b` (`chainContext`), turns an `a`–`b` path of a reading
into a cycle of the gluing and back (`edgeContext_cycle_of_path`,
`path_of_edgeContext_cycle`, `chain_cycle_of_path`, `path_of_chain_cycle`).
On a target-avoiding object, context-equivalent readings therefore share their
accepted path-length spectrum (`spectrum_transfer`, `chain_spectrum_transfer`)
and, at the dyadic target, their exact `a`–`b` path-length sets
(`exact_spectrum_one_way`).  A chain whose internal vertices have degree two is
traversed monotonically by every cycle (`forced_ascent`,
`cycle_chain_decomposition`).

Every statement is about an arbitrary finite object; nothing here knows a
presentation, a ledger, or a manuscript.
-/

universe u v

namespace Hypostructure.Graph.ReadingSpectrum.EdgeContext

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Classical


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
  · intro mem; exact qFresh (by rwa [Sym2.eq_swap] at mem ⊢ <;> exact mem)
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

/-- **D3: single-edge spectrum transfer** (vocabulary-free).  If two readings of
`Z` are context-equivalent on a target-avoiding object, then for any two
distinct boundary vertices `a, b`: the first has an `a`–`b` path avoiding `ab`
of accepted-minus-one length iff the second does. -/
theorem spectrum_transfer {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L object)
    {R R' : Finset object.Vertex}
    (equivalent : Response.ContextEquivalent (HasCycleWithLength L)
      (SupportAtom.retainedPiece object Z R) (SupportAtom.retainedPiece object Z R'))
    (ne : a ≠ b) :
    (∃ p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b),
        p.IsPath ∧ s(.inl a, .inl b) ∉ p.edges ∧ L (p.length + 1)) ↔
      (∃ p : (SupportAtom.retainedPiece object Z R').graph.Walk (.inl a) (.inl b),
        p.IsPath ∧ s(.inl a, .inl b) ∉ p.edges ∧ L (p.length + 1)) := by
  constructor
  · rintro ⟨p, hp, hf, hl⟩
    exact path_of_edgeContext_cycle avoids
      ((equivalent (edgeContext Z a b)).1 (edgeContext_cycle_of_path ne p hp hf hl))
  · rintro ⟨p, hp, hf, hl⟩
    exact path_of_edgeContext_cycle avoids
      ((equivalent (edgeContext Z a b)).2 (edgeContext_cycle_of_path ne p hp hf hl))

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

end Hypostructure.Graph.ReadingSpectrum.EdgeContext

namespace Hypostructure.Graph.ReadingSpectrum.DegreeTwoChain

variable {V : Type*} {G : SimpleGraph V}

/-- A chain `x 0 — x 1 — … — x (m+1)` whose internal vertices have degree two. -/
structure Chain (G : SimpleGraph V) (m : Nat) (x : Nat → V) : Prop where
  adj : ∀ i, i ≤ m → G.Adj (x i) (x (i + 1))
  inj : ∀ i j, i ≤ m + 1 → j ≤ m + 1 → x i = x j → i = j
  deg2 : ∀ i, 1 ≤ i → i ≤ m → ∀ w, G.Adj (x i) w → w = x (i - 1) ∨ w = x (i + 1)

variable {m : Nat} {x : Nat → V}

/-- **Forced ascent** (vocabulary-free): a simple walk leaving the chain at
`x i` upward, which has not used the lower chain, runs up the chain to
`x (m+1)` and then continues avoiding every internal chain vertex. -/
theorem forced_ascent (ch : Chain G m x) : ∀ (k i : Nat), i + k = m + 1 → 1 ≤ i →
    ∀ {t : V} (q : G.Walk (x i) t), q.IsPath →
      (∀ j, 1 ≤ j → j < i → x j ∉ q.support) → s(x (i - 1), x i) ∉ q.edges →
      (∀ j, 1 ≤ j → j ≤ m → t ≠ x j) →
      ∃ r : G.Walk (x (m + 1)) t, r.IsPath ∧ r.length + k = q.length ∧
        ∀ j, 1 ≤ j → j ≤ m → x j ∉ r.support := by
  intro k
  induction k with
  | zero =>
    intro i hi _ t q qp below _ _
    have : i = m + 1 := by omega
    subst this
    exact ⟨q, qp, by simp, fun j h1 h2 => below j h1 (by omega)⟩
  | succ k ih =>
    intro i hi i1 t q qp below fresh tne
    have im : i ≤ m := by omega
    cases q with
    | nil => exact absurd rfl (tne i i1 im)
    | cons h q' =>
      rename_i w
      have pc := (SimpleGraph.Walk.cons_isPath_iff h q').1 qp
      rcases ch.deg2 i i1 im w h with hw | hw
      · exfalso
        by_cases i2 : 2 ≤ i
        · exact below (i - 1) (by omega) (by omega) (by rw [← hw]; simp)
        · have : i = 1 := by omega
          subst this
          apply fresh
          rw [SimpleGraph.Walk.edges_cons]
          apply List.mem_cons.2 (Or.inl _)
          rw [hw]
          exact Sym2.eq_swap
      · subst hw
        obtain ⟨r, rp, rl, ravoid⟩ := ih (i + 1) (by omega) (by omega) q' pc.1
          (by
            intro j h1 h2 hj
            rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
            · exact below j h1 h2 (by simp [hj])
            · subst h2; exact pc.2 hj)
          (by
            have nd := qp.edges_nodup
            rw [SimpleGraph.Walk.edges_cons] at nd
            simpa using (List.nodup_cons.1 nd).1)
          tne
        exact ⟨r, rp, by simp; omega, ravoid⟩


/-- At an internal chain vertex a cycle uses the lower chain edge. -/
theorem cycle_lower_edge (ch : Chain G m x) {v : V} {C : G.Walk v v} (hc : C.IsCycle)
    {j : Nat} (j1 : 1 ≤ j) (jm : j ≤ m) (hj : x j ∈ C.support) :
    s(x (j - 1), x j) ∈ C.edges := by
  have two := hc.ncard_neighborSet_toSubgraph_eq_two hj
  have sub : C.toSubgraph.neighborSet (x j) ⊆ {x (j - 1), x (j + 1)} := by
    intro w hw
    rcases ch.deg2 j j1 jm w (C.toSubgraph.adj_sub hw) with e | e
    · exact Or.inl e
    · exact Or.inr (Set.mem_singleton_iff.2 e)
  by_cases lower : x (j - 1) ∈ C.toSubgraph.neighborSet (x j)
  · have adj : C.toSubgraph.Adj (x j) (x (j - 1)) := lower
    have : s(x j, x (j - 1)) ∈ C.edges := by
      rw [← SimpleGraph.Walk.mem_edges_toSubgraph]
      exact adj
    rwa [Sym2.eq_swap] at this
  · exfalso
    have sub1 : C.toSubgraph.neighborSet (x j) ⊆ {x (j + 1)} := by
      intro w hw
      rcases sub hw with e | e
      · exact absurd (e ▸ hw) lower
      · exact e
    have := Set.ncard_le_ncard sub1 (Set.toFinite _)
    rw [two, Set.ncard_singleton] at this
    omega

/-- A cycle meeting an internal chain vertex uses the first chain edge. -/
theorem cycle_first_edge (ch : Chain G m x) {v : V} {C : G.Walk v v} (hc : C.IsCycle) :
    ∀ j, 1 ≤ j → j ≤ m → x j ∈ C.support → s(x 0, x 1) ∈ C.edges := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro j1 jm hj
    have e := cycle_lower_edge ch hc j1 jm hj
    by_cases j0 : j = 0
    · subst j0; simpa using e
    · have hs : x j ∈ C.support := by
        simpa using C.fst_mem_support_of_mem_edges e
      exact ih (by omega) (by omega) hs

/-- **Chain decomposition of a cycle** (vocabulary-free): a cycle meeting an
internal chain vertex contains the whole chain, and the rest is a simple
`x (m+1)`–`x 0` path avoiding the internal chain, of length `|C| − (m+1)`. -/
theorem cycle_chain_decomposition (ch : Chain G m x) (m1 : 1 ≤ m) {v : V} {C : G.Walk v v}
    (hc : C.IsCycle) {j : Nat} (j1 : 1 ≤ j) (jm : j ≤ m) (hj : x j ∈ C.support) :
    ∃ r : G.Walk (x (m + 1)) (x 0), r.IsPath ∧ r.length + (m + 1) = C.length ∧
      ∀ i, 1 ≤ i → i ≤ m → x i ∉ r.support := by
  have e := cycle_first_edge ch hc j j1 jm hj
  obtain ⟨w, wp, wf, wl⟩ := Hypostructure.Graph.ReadingSpectrum.EdgeContext.cycle_through_edge C hc e
  obtain ⟨r, rp, rl, ra⟩ := forced_ascent ch m 1 (by omega) le_rfl w.reverse wp.reverse
    (fun j h1 h2 => by omega)
    (by rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; simpa using wf)
    (fun i h1 h2 eq => by have := ch.inj 0 i (by omega) (by omega) eq; omega)
  refine ⟨r, rp, ?_, ra⟩
  rw [SimpleGraph.Walk.length_reverse] at rl
  omega

end Hypostructure.Graph.ReadingSpectrum.DegreeTwoChain


namespace Hypostructure.Graph.ReadingSpectrum.ChainContext

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Classical

variable {object : FiniteObject.{u}} {Z R : Finset object.Vertex}

/-- The chain labels `x_0 = a, x_1, …, x_m, x_{m+1} = b` of the context. -/
noncomputable def xc (Z : Finset object.Vertex) (a b : (SupportAtom.boundary object Z).Vertex)
    (m : Nat) (i : Nat) : (SupportAtom.boundary object Z).Vertex ⊕ ULift.{u} (Fin m) :=
  if h0 : i = 0 then .inl a else if hm : i ≤ m then .inr ⟨⟨i - 1, by omega⟩⟩ else .inl b

variable {a b : (SupportAtom.boundary object Z).Vertex} {m : Nat}

theorem xc_inj (ab : a ≠ b) : ∀ i j, i ≤ m + 1 → j ≤ m + 1 →
    xc Z a b m i = xc Z a b m j → i = j := by
  intro i j hi hj e
  unfold xc at e
  by_cases i0 : i = 0 <;> by_cases j0 : j = 0 <;>
    by_cases im : i ≤ m <;> by_cases jm : j ≤ m <;> simp_all [ULift.ext_iff, Fin.ext_iff] <;>
    first | omega | exact ab e | exact ab e.symm

/-- The degree-two chain context of length `m + 1` between `a` and `b`. -/
noncomputable def chainContext (Z : Finset object.Vertex) (a b : (SupportAtom.boundary object Z).Vertex)
    (m : Nat) : OutsideContext (SupportAtom.boundary object Z) where
  Internal := ULift.{u} (Fin m)
  internalVertices := inferInstance
  graph := SimpleGraph.fromRel fun u v => ∃ i, i ≤ m ∧ u = xc Z a b m i ∧ v = xc Z a b m (i + 1)
  decideAdj := Classical.decRel _

/-- The glued chain vertices. -/
noncomputable def X (Z R : Finset object.Vertex) (a b : (SupportAtom.boundary object Z).Vertex)
    (m : Nat) (i : Nat) :
    (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).Vertex :=
  contextEmbedding _ (chainContext Z a b m) (xc Z a b m i)


theorem X_internal {i : Nat} (i1 : 1 ≤ i) (im : i ≤ m) :
    X Z R a b m i = .inr (.inr ⟨⟨i - 1, by omega⟩⟩) := by
  simp only [X, xc, show i ≠ 0 by omega, im, dite_false, dite_true]
  rfl

/-- **The glued chain is a degree-two chain** of the glued graph. -/
theorem chain_glue (ab : a ≠ b) :
    Hypostructure.Graph.ReadingSpectrum.DegreeTwoChain.Chain (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph m
      (X Z R a b m) where
  adj := by
    intro i hi
    refine (glueGraph_adj_iff _ _ _ _).2 (Or.inr ⟨xc Z a b m i, xc Z a b m (i + 1), ?_, rfl, rfl⟩)
    change (SimpleGraph.fromRel _).Adj _ _
    rw [SimpleGraph.fromRel_adj]
    refine ⟨fun e => ?_, Or.inl ⟨i, hi, rfl, rfl⟩⟩
    have := xc_inj ab i (i + 1) (by omega) (by omega) e
    omega
  inj := by
    intro i j hi hj e
    exact xc_inj ab i j hi hj ((contextEmbedding _ _).injective e)
  deg2 := by
    intro i i1 im w adj
    rcases (glueGraph_adj_iff _ _ _ _).1 adj with owns | owns
    · exfalso
      obtain ⟨pl, pr, -, hl, -⟩ := owns
      rw [X_internal i1 im] at hl
      rcases pl with pl | pl <;> cases hl
    · obtain ⟨cl, cr, cadj, hl, hr⟩ := owns
      have clEq : cl = xc Z a b m i := (contextEmbedding _ _).injective hl
      change (SimpleGraph.fromRel _).Adj _ _ at cadj
      rw [SimpleGraph.fromRel_adj] at cadj
      rcases cadj.2 with ⟨k, hk, e1, e2⟩ | ⟨k, hk, e1, e2⟩
      · have : i = k := xc_inj ab i k (by omega) (by omega) (clEq ▸ e1)
        subst this
        right
        rw [← hr, e2]; rfl
      · have : i = k + 1 := xc_inj ab i (k + 1) (by omega) (by omega) (clEq ▸ e2)
        subst this
        left
        rw [← hr, e1]; rfl


/-- The non-context-internal glued vertices. -/
def NotInternal (v : (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).Vertex) :
    Prop :=
  ∀ c, v ≠ (show (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).Vertex from
    .inr (.inr c))

theorem internal_is_X (c : ULift.{u} (Fin m)) :
    (.inr (.inr c) : GluedVertex (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)) =
      X Z R a b m (c.down.1 + 1) := by
  rw [X_internal (by omega) (by have := c.down.2; omega)]
  rfl

/-- Pull a non-internal glued vertex back to the reading. -/
def pullC (v : GluedVertex (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)) :
    (SupportAtom.boundary object Z).Vertex ⊕ (SupportAtom.retainedPiece object Z R).Internal :=
  match v with
  | .inl x => .inl x
  | .inr (.inl w) => .inr w
  | .inr (.inr _) => .inl a

theorem xc_internal {k : Nat} (k1 : 1 ≤ k) (km : k ≤ m) :
    ∃ c, xc Z a b m k = .inr c := by
  refine ⟨⟨⟨k - 1, by omega⟩⟩, ?_⟩
  simp only [xc, show k ≠ 0 by omega, km, dite_false, dite_true]

/-- The pull-back homomorphism on the non-internal part. -/
noncomputable def pullHomC (m1 : 1 ≤ m) :
    (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph.induce
        {v | NotInternal (a := a) (b := b) v} →g (SupportAtom.retainedPiece object Z R).graph where
  toFun v := pullC v.1
  map_rel' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ adj
    have adj' : (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph.Adj u v := adj
    rcases (glueGraph_adj_iff _ _ u v).1 adj' with owns | owns
    · obtain ⟨pl, pr, padj, rfl, rfl⟩ := owns
      rcases pl with pl | pl <;> rcases pr with pr | pr <;> exact padj
    · exfalso
      obtain ⟨cl, cr, cadj, rfl, rfl⟩ := owns
      change (SimpleGraph.fromRel _).Adj _ _ at cadj
      rw [SimpleGraph.fromRel_adj] at cadj
      have notInt : ∀ (y : (SupportAtom.boundary object Z).Vertex ⊕ ULift.{u} (Fin m)),
          NotInternal (a := a) (b := b) (R := R) (contextEmbedding _ _ y) → ∀ k, 1 ≤ k → k ≤ m →
            y ≠ xc Z a b m k := by
        intro y hy k k1 km e
        obtain ⟨c, hc⟩ := xc_internal (a := a) (b := b) k1 km
        exact hy c (by rw [e, hc]; rfl)
      rcases cadj.2 with ⟨k, hk, e1, e2⟩ | ⟨k, hk, e1, e2⟩
      · by_cases k0 : k = 0
        · subst k0
          exact notInt cr hv 1 le_rfl m1 e2
        · exact notInt cl hu k (by omega) hk e1
      · by_cases k0 : k = 0
        · subst k0
          exact notInt cl hu 1 le_rfl m1 e2
        · exact notInt cr hv k (by omega) hk e1

theorem pullHomC_injective (m1 : 1 ≤ m) :
    Function.Injective (pullHomC (object := object) (Z := Z) (R := R) (a := a) (b := b) m1) := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩ h
  have h' : pullC u = pullC v := h
  apply Subtype.ext
  rcases u with u | u | u <;> rcases v with v | v | v <;>
    first
    | exact absurd rfl (hu u)
    | exact absurd rfl (hv v)
    | simp_all [pullC]


theorem pullC_X_last : pullC (a := a) (b := b) (R := R) (X Z R a b m (m + 1)) = .inl b := by
  simp [X, xc, pullC, contextEmbedding]

theorem pullC_X_zero : pullC (a := a) (b := b) (R := R) (X Z R a b m 0) = .inl a := by
  simp [X, xc, pullC, contextEmbedding]

/-- Transport a walk supported in the non-internal part to the reading. -/
theorem induce_path_map {m1 : 1 ≤ m} {u v : (glue (SupportAtom.retainedPiece object Z R)
      (chainContext Z a b m)).Vertex}
    (w : (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph.Walk u v)
    (hs : ∀ y ∈ w.support, y ∈ {v | NotInternal (a := a) (b := b) (R := R) v}) (wp : w.IsPath) :
    ((w.induce _ hs).map (pullHomC m1)).IsPath ∧
      ((w.induce _ hs).map (pullHomC m1)).length = w.length := by
  have mapEq := SimpleGraph.Walk.map_induce w hs
  have ip : (w.induce _ hs).IsPath := by
    let e := SimpleGraph.Embedding.induce
        (G := (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph)
        {v | NotInternal (a := a) (b := b) (R := R) v}
    rw [← SimpleGraph.Walk.map_isPath_iff_of_injective (f := e.toHom) e.injective, mapEq]
    exact wp
  refine ⟨SimpleGraph.Walk.map_isPath_of_injective (pullHomC_injective m1) ip, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  have := congrArg SimpleGraph.Walk.length mapEq
  rwa [SimpleGraph.Walk.length_map] at this

/-- **Chain-context transfer, backward** (vocabulary-free): on a target-avoiding
object, an accepted cycle of a reading glued to the length-`(m+1)` chain between
`a ≠ b` is the chain plus a simple `b`–`a` path of the reading, of length
`|C| − (m+1)`. -/
theorem path_of_chain_cycle {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L object)
    (ab : a ≠ b) (m1 : 1 ≤ m)
    (cyc : HasCycleWithLength L (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m))) :
    ∃ p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl b) (.inl a),
      p.IsPath ∧ L (p.length + (m + 1)) := by
  obtain ⟨c⟩ := cyc
  by_cases hin : ∃ j, 1 ≤ j ∧ j ≤ m ∧ X Z R a b m j ∈ c.walk.support
  · obtain ⟨j, j1, jm, hj⟩ := hin
    obtain ⟨r, rp, rl, ra⟩ := Hypostructure.Graph.ReadingSpectrum.DegreeTwoChain.cycle_chain_decomposition (chain_glue ab) m1 c.isCycle j1 jm hj
    have hs : ∀ y ∈ r.support, y ∈ {v | NotInternal (a := a) (b := b) (R := R) v} := by
      intro y hy c' e
      rw [e, internal_is_X] at hy
      exact ra _ (by omega) (by have := c'.down.2; omega) hy
    obtain ⟨pp, pl⟩ := induce_path_map (m1 := m1) r hs rp
    let p := (r.induce _ hs).map (pullHomC m1)
    have e1 := pullC_X_last (a := a) (b := b) (R := R) (m := m)
    have e0 := pullC_X_zero (a := a) (b := b) (R := R) (m := m)
    refine ⟨p.copy e1 e0, by rw [SimpleGraph.Walk.isPath_copy]; exact pp, ?_⟩
    rw [SimpleGraph.Walk.length_copy]
    change L (p.length + (m + 1))
    rw [pl, rl]
    exact c.length_ok
  · exfalso
    push Not at hin
    have hs : ∀ y ∈ c.walk.support, y ∈ {v | NotInternal (a := a) (b := b) (R := R) v} := by
      intro y hy c' e
      rw [e, internal_is_X] at hy
      exact hin _ (by omega) (by have := c'.down.2; omega) hy
    have mapEq := SimpleGraph.Walk.map_induce c.walk hs
    have ic : (c.walk.induce _ hs).IsCycle := by
      let e := SimpleGraph.Embedding.induce
          (G := (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph)
          {v | NotInternal (a := a) (b := b) (R := R) v}
      rw [← SimpleGraph.Walk.map_isCycle_iff_of_injective (f := e.toHom) e.injective, mapEq]
      exact c.isCycle
    have il : (c.walk.induce _ hs).length = c.walk.length := by
      have := congrArg SimpleGraph.Walk.length mapEq
      rwa [SimpleGraph.Walk.length_map] at this
    let f := (Hypostructure.Graph.ReadingSpectrum.EdgeContext.readingHom Z R).comp (pullHomC (a := a) (b := b) m1)
    have finj : Function.Injective f :=
      (Hypostructure.Graph.ReadingSpectrum.EdgeContext.readingHom_injective Z R).comp (pullHomC_injective m1)
    exact avoids ⟨⟨_, (c.walk.induce _ hs).map f, ic.map finj, by
      convert c.length_ok using 1
      rw [SimpleGraph.Walk.length_map, il]⟩⟩


/-- Push the reading into the chain gluing. -/
noncomputable def pushHomC :
    (SupportAtom.retainedPiece object Z R).graph →g
      (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph where
  toFun := pieceEmbedding _ _
  map_rel' := by
    intro x y adj
    exact (glueGraph_adj_iff _ _ _ _).2 (Or.inl ⟨x, y, adj, rfl, rfl⟩)

/-- The chain walked downward from `X k` to `X 0`. -/
noncomputable def chainDown (ab : a ≠ b) : (k : Nat) → k ≤ m + 1 →
    (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)).graph.Walk
      (X Z R a b m k) (X Z R a b m 0)
  | 0, _ => .nil
  | k + 1, h => .cons ((chain_glue (R := R) ab).adj k (by omega)).symm (chainDown ab k (by omega))

theorem chainDown_spec (ab : a ≠ b) : ∀ k (h : k ≤ m + 1),
    (chainDown (R := R) ab k h).IsPath ∧ (chainDown (R := R) ab k h).length = k ∧
      ∀ y ∈ (chainDown (R := R) ab k h).support, ∃ j ≤ k, y = X Z R a b m j := by
  intro k
  induction k with
  | zero => intro h; simp [chainDown]
  | succ k ih =>
    intro h
    obtain ⟨pp, pl, ps⟩ := ih (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (SimpleGraph.Walk.cons _ (chainDown ab k _)).IsPath
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨pp, fun hmem => ?_⟩
      obtain ⟨j, hj, e⟩ := ps _ hmem
      have := (chain_glue (R := R) ab).inj (k + 1) j (by omega) (by omega) e
      omega
    · show (SimpleGraph.Walk.cons _ (chainDown ab k _)).length = k + 1
      simp [pl]
    · intro y hy
      change y ∈ (SimpleGraph.Walk.cons _ (chainDown ab k _)).support at hy
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨k + 1, le_rfl, rfl⟩
      · obtain ⟨j, hj, e⟩ := ps y hy
        exact ⟨j, by omega, e⟩

theorem X_last_eq : X Z R a b m (m + 1) = pushHomC (a := a) (b := b) (m := m) (R := R) (.inl b) := by
  simp [X, xc, pushHomC, contextEmbedding, pieceEmbedding]

theorem X_zero_eq : X Z R a b m 0 = pushHomC (a := a) (b := b) (m := m) (R := R) (.inl a) := by
  simp [X, xc, pushHomC, contextEmbedding, pieceEmbedding]

/-- **Chain-context transfer, forward** (vocabulary-free). -/
theorem chain_cycle_of_path {L : Nat → Prop} (ab : a ≠ b) (m1 : 1 ≤ m)
    (p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b))
    (pp : p.IsPath) (ok : L (p.length + (m + 1))) :
    HasCycleWithLength L (glue (SupportAtom.retainedPiece object Z R) (chainContext Z a b m)) := by
  let q := p.map (pushHomC (a := a) (b := b) (m := m))
  have qp : q.IsPath := SimpleGraph.Walk.map_isPath_of_injective (pieceEmbedding _ _).injective pp
  obtain ⟨cp, cl, cs⟩ := chainDown_spec (R := R) ab (m + 1) le_rfl
  let ch := (chainDown (R := R) ab (m + 1) le_rfl).copy X_last_eq X_zero_eq
  have chp : ch.IsPath := by simpa [ch] using cp
  have disj : q.support.tail.Disjoint ch.support.tail := by
    intro y hq hc
    have hc' : y ∈ (chainDown (R := R) ab (m + 1) le_rfl).support := by
      have := List.mem_of_mem_tail hc
      simpa [ch] using this
    obtain ⟨j, hj, rfl⟩ := cs y hc'
    have hq' := List.mem_of_mem_tail hq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hq'
    obtain ⟨z, -, hz⟩ := hq'
    by_cases j0 : j = 0
    · subst j0
      -- `X 0 = inl a` is the start of `q`, not in its tail
      have nd := qp.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support, List.nodup_cons] at nd
      rw [X_zero_eq] at hq
      exact nd.1 hq
    by_cases jl : j = m + 1
    · subst jl
      -- `X (m+1) = inl b` is the start of `ch`, not in its tail
      have nd := chp.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support, List.nodup_cons] at nd
      rw [X_last_eq] at hc
      exact nd.1 hc
    · rw [X_internal (by omega) (by omega)] at hz
      rcases z with z | z <;> cases hz
  refine ⟨⟨_, q.append ch, qp.isCycle_append chp disj (Or.inr (by
    simp only [ch, SimpleGraph.Walk.length_copy, cl]; omega)), ?_⟩⟩
  simp only [SimpleGraph.Walk.length_append, q, ch, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_map, cl]
  exact ok


/-- **Chain spectrum transfer** (vocabulary-free): context-equivalent readings
have `a`–`b` paths with `L(ℓ + m + 1)` simultaneously. -/
theorem chain_spectrum_transfer {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L object)
    (ab : a ≠ b) (m1 : 1 ≤ m) {R' : Finset object.Vertex}
    (equivalent : Response.ContextEquivalent (HasCycleWithLength L)
      (SupportAtom.retainedPiece object Z R) (SupportAtom.retainedPiece object Z R'))
    {p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b)}
    (pp : p.IsPath) (ok : L (p.length + (m + 1))) :
    ∃ p' : (SupportAtom.retainedPiece object Z R').graph.Walk (.inl a) (.inl b),
      p'.IsPath ∧ L (p'.length + (m + 1)) := by
  obtain ⟨q, qp, qok⟩ := path_of_chain_cycle (R := R') avoids ab m1
    ((equivalent (chainContext Z a b m)).1 (chain_cycle_of_path ab m1 p pp ok))
  exact ⟨q.reverse, qp.reverse, by simpa using qok⟩

/-- The dyadic window: between `2^(K-1)` and `2^(K+1)` the only accepted length
is `2^K`. -/
theorem dyadic_window {K n : Nat} (lo : 2 ^ (K - 1) < n) (hi : n < 2 ^ (K + 1))
    (ok : Hypostructure.Core.DyadicLength.PowerOfTwoLength n) : n = 2 ^ K := by
  obtain ⟨e, -, he⟩ := ok
  rw [he] at lo hi ⊢
  have h1 : K - 1 < e.1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 lo
  have h2 : e.1 < K + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hi
  have : e.1 = K ∨ (K = 0 ∧ e.1 = 0) := by omega
  rcases this with h | ⟨rfl, h⟩
  · rw [h]
  · rw [h]

/-- **Length-exact spectrum transfer at the dyadic target** (vocabulary-free):
on a target-avoiding object, context-equivalent readings have exactly the same
set of lengths of simple `a`–`b` paths, for any two distinct boundary vertices. -/
theorem exact_spectrum_one_way
    (avoids : ¬ HasCycleWithLength Hypostructure.Core.DyadicLength.PowerOfTwoLength object)
    (ab : a ≠ b) {R' : Finset object.Vertex}
    (equivalent : Response.ContextEquivalent
      (HasCycleWithLength Hypostructure.Core.DyadicLength.PowerOfTwoLength)
      (SupportAtom.retainedPiece object Z R) (SupportAtom.retainedPiece object Z R'))
    {p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b)} (pp : p.IsPath) :
    ∃ p' : (SupportAtom.retainedPiece object Z R').graph.Walk (.inl a) (.inl b),
      p'.IsPath ∧ p'.length = p.length := by
  classical
  letI i1 : FinEnum ((SupportAtom.boundary object Z).Vertex ⊕
      (SupportAtom.retainedPiece object Z R).Internal) := (SupportAtom.retainedPiece object Z R).pack.vertices
  letI i2 : FinEnum ((SupportAtom.boundary object Z).Vertex ⊕
      (SupportAtom.retainedPiece object Z R').Internal) :=
    (SupportAtom.retainedPiece object Z R').pack.vertices
  let N := Fintype.card ((SupportAtom.boundary object Z).Vertex ⊕
    (SupportAtom.retainedPiece object Z R).Internal)
  have NN : Fintype.card ((SupportAtom.boundary object Z).Vertex ⊕
      (SupportAtom.retainedPiece object Z R').Internal) = N :=
    Fintype.card_eq.2 ⟨Equiv.refl _⟩
  have pl : p.length < N := pp.length_lt
  let K := N + 2
  have big : N + 1 < 2 ^ (K - 1) := by
    have := Nat.lt_two_pow_self (n := N + 1)
    simpa [K] using this
  let mm := 2 ^ K - p.length - 1
  have hK : 2 ^ (K - 1) * 2 = 2 ^ K := by
    rw [← Nat.pow_succ]; congr 1
  have m1 : 1 ≤ mm := by simp only [mm]; omega
  have okp : Hypostructure.Core.DyadicLength.PowerOfTwoLength (p.length + (mm + 1)) := by
    refine ⟨⟨K, by simp only [mm]; omega⟩, by simp [K], ?_⟩
    simp only [mm]; omega
  obtain ⟨q, qp, qok⟩ := chain_spectrum_transfer (m := mm) avoids ab m1 equivalent pp okp
  have ql : q.length < N := NN ▸ qp.length_lt
  have eq := dyadic_window (K := K) (by simp only [mm]; omega) (by
    rw [Nat.pow_succ]; simp only [mm]; omega) qok
  exact ⟨q, qp, by simp only [mm] at eq; omega⟩

/-- **Exact spectrum equality at the dyadic target** (vocabulary-free): on a
target-avoiding object, two context-equivalent readings have the same simple
`a`–`b` path lengths, in both directions. -/
theorem exact_spectrum_iff
    (avoids : ¬ HasCycleWithLength Hypostructure.Core.DyadicLength.PowerOfTwoLength object)
    (ab : a ≠ b) {R' : Finset object.Vertex}
    (equivalent : Response.ContextEquivalent
      (HasCycleWithLength Hypostructure.Core.DyadicLength.PowerOfTwoLength)
      (SupportAtom.retainedPiece object Z R) (SupportAtom.retainedPiece object Z R'))
    (n : Nat) :
    (∃ p : (SupportAtom.retainedPiece object Z R).graph.Walk (.inl a) (.inl b),
        p.IsPath ∧ p.length = n) ↔
      (∃ p : (SupportAtom.retainedPiece object Z R').graph.Walk (.inl a) (.inl b),
        p.IsPath ∧ p.length = n) := by
  constructor
  · rintro ⟨p, pp, rfl⟩
    exact exact_spectrum_one_way avoids ab equivalent pp
  · rintro ⟨p, pp, rfl⟩
    obtain ⟨q, qp, ql⟩ := exact_spectrum_one_way (R := R') (R' := R) avoids ab
      (fun O => (equivalent O).symm) pp
    exact ⟨q, qp, ql⟩

end Hypostructure.Graph.ReadingSpectrum.ChainContext
