import Hypostructure.Graph.GluedReadingMaps

/-!
# Reading counts of a support, active labels and private edges

Let `Z` be a vertex support of a finite object, `∂Z` its cut boundary and
`ret_R` the piece of `Z` that keeps the edges with both ends in `R`.  The
reading count `c_R(b)` of a boundary vertex `b` is the number of `R`-neighbours
of `b` inside `Z` (when `b ∈ R`); it is exactly the boundary degree of `ret_R`
at `b`, so two readings have equal boundary-degree profiles iff their reading
counts agree everywhere.

Results (all vocabulary-free):
* the exact boundary-degree formula of a reading and the profile transfer;
* boundary-free readings are context-equivalent on a target-avoiding object;
* the reading-count bounds `c_R(b) + 1 ≤ deg b`;
* every accepted cycle of a reading glued to a cycle-free context crosses `∂Z`
  at two distinct active labels;
* if `glue ret_P O` has an accepted cycle and `glue ret_N O` has none, the cycle
  uses a private edge of `P` (both ends in `P`, not both in `N`).
-/

namespace Hypostructure.Graph.ReadingCounts

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {object : FiniteObject.{u}}


/-- `pieceDecode` is injective (vocabulary-free). -/
theorem pieceDecode_injective (Z : Finset object.Vertex) :
    Function.Injective (SupportAtom.pieceDecode object Z) := by
  intro x y h
  rcases x with a | a <;> rcases y with b | b <;>
    simp [SupportAtom.pieceDecode] at h
  · exact congrArg Sum.inl h
  · exact absurd (h ▸ a.2) b.2.2
  · exact absurd (h ▸ b.2) a.2.2
  · exact congrArg Sum.inr (Subtype.ext h)

theorem pieceDecode_mem (Z : Finset object.Vertex)
    (x : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    SupportAtom.pieceDecode object Z x ∈ Z := by
  rcases x with a | a
  · exact ((SupportAtom.mem_cutBoundary_iff object Z a.1).1 a.2).1
  · exact a.2.1

theorem exists_pieceDecode_eq {Z : Finset object.Vertex} {w : object.Vertex}
    (hw : w ∈ Z) : ∃ x, SupportAtom.pieceDecode object Z x = w := by
  classical
  by_cases hb : w ∈ SupportAtom.cutBoundary object Z
  · exact ⟨.inl ⟨w, hb⟩, rfl⟩
  · exact ⟨.inr ⟨w, hw, hb⟩, rfl⟩

/-- **Exact boundary-degree formula of a reading** (vocabulary-free).
At a boundary vertex `b` of `∂Z`, the reading of `Z` retained on `R` has degree
`#{w ∈ Z : b ~ w, b ∈ R, w ∈ R}`. -/
theorem retained_boundaryDegree (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    (SupportAtom.retainedPiece object Z R).boundaryDegree b =
      {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R}.ncard := by
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  let N : Set ((SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :=
    {x | (SupportAtom.retainedPiece object Z R).graph.Adj (.inl b) x}
  change N.ncard = _
  rw [← Set.ncard_image_of_injective N (pieceDecode_injective (object := object) Z)]
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have adj : (SupportAtom.retainedPiece object Z R).graph.Adj (.inl b) x := hx
    change (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
      SimpleGraph.comap (SupportAtom.pieceDecode object Z)
        (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _ at adj
    rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
      SimpleGraph.fromRel_adj] at adj
    obtain ⟨gAdj, -, rel⟩ := adj
    refine ⟨pieceDecode_mem Z x, gAdj, ?_⟩
    rcases rel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  · rintro ⟨wZ, adj, bR, wR⟩
    obtain ⟨x, rfl⟩ := exists_pieceDecode_eq wZ
    refine ⟨x, ?_, rfl⟩
    show (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
      SimpleGraph.comap (SupportAtom.pieceDecode object Z)
        (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _
    rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
      SimpleGraph.fromRel_adj]
    exact ⟨adj, adj.ne, Or.inl ⟨bR, wR⟩⟩

/-- A reading vanishes at a boundary vertex it does not retain. -/
theorem retained_boundaryDegree_eq_zero (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) (hb : b.1 ∉ R) :
    (SupportAtom.retainedPiece object Z R).boundaryDegree b = 0 := by
  rw [retained_boundaryDegree]
  convert Set.ncard_empty object.Vertex
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, bR, -⟩
  exact hb bR

/-- A reading is positive at a retained boundary vertex with a retained
neighbour in `Z`. -/
theorem retained_boundaryDegree_pos (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) (hb : b.1 ∈ R)
    {w : object.Vertex} (wZ : w ∈ Z) (wR : w ∈ R) (adj : object.graph.Adj b.1 w) :
    0 < (SupportAtom.retainedPiece object Z R).boundaryDegree b := by
  rw [retained_boundaryDegree]
  apply Set.ncard_pos (Set.toFinite _) |>.2
  exact ⟨w, wZ, adj, hb, wR⟩

/-- **Profile transfer** (vocabulary-free).  If two readings of `Z` have the
same boundary-degree profile, then every boundary vertex retained by the first
reading with a retained `Z`-neighbour is retained by the second. -/
theorem mem_of_profile_eq {Z R R' : Finset object.Vertex}
    (profile : (SupportAtom.retainedPiece object Z R).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object Z R').boundaryDegreeProfile)
    (b : (SupportAtom.boundary object Z).Vertex) (hb : b.1 ∈ R)
    {w : object.Vertex} (wZ : w ∈ Z) (wR : w ∈ R) (adj : object.graph.Adj b.1 w) :
    b.1 ∈ R' := by
  by_contra notIn
  have pos := retained_boundaryDegree_pos Z R b hb wZ wR adj
  have zero := retained_boundaryDegree_eq_zero Z R' b notIn
  have eq := congrFun profile b
  change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
    (SupportAtom.retainedPiece object Z R').boundaryDegree b at eq
  omega


/-! ### Boundary-free readings: the response carries no information -/

/-- The glued vertices that are retained internal vertices of the piece. -/
def InRetained (Z R : Finset object.Vertex)
    {O : OutsideContext (SupportAtom.boundary object Z)} :
    GluedVertex (SupportAtom.retainedPiece object Z R) O → Prop
  | .inr (.inl w) => w.1 ∈ R
  | _ => False

theorem pieceOwns_inRetained {Z R : Finset object.Vertex}
    (free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    {O : OutsideContext (SupportAtom.boundary object Z)}
    {x y : GluedVertex (SupportAtom.retainedPiece object Z R) O}
    (owns : PieceOwns (SupportAtom.retainedPiece object Z R) O x y) :
    InRetained Z R x ∧ InRetained Z R y := by
  obtain ⟨pl, pr, adj, rfl, rfl⟩ := owns
  change (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
      SimpleGraph.comap (SupportAtom.pieceDecode object Z)
        (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _ at adj
  rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
    SimpleGraph.fromRel_adj] at adj
  obtain ⟨-, -, rel⟩ := adj
  have both : SupportAtom.pieceDecode object Z pl ∈ R ∧
      SupportAtom.pieceDecode object Z pr ∈ R := by
    rcases rel with h | h
    · exact h
    · exact ⟨h.2, h.1⟩
  constructor
  · rcases pl with b | w
    · exact absurd b.2 (free _ both.1)
    · exact both.1
  · rcases pr with b | w
    · exact absurd b.2 (free _ both.2)
    · exact both.2

theorem contextOwns_not_inRetained {Z R : Finset object.Vertex}
    {O : OutsideContext (SupportAtom.boundary object Z)}
    {x y : GluedVertex (SupportAtom.retainedPiece object Z R) O}
    (owns : ContextOwns (SupportAtom.retainedPiece object Z R) O x y) :
    ¬ InRetained Z R x ∧ ¬ InRetained Z R y := by
  obtain ⟨cl, cr, -, rfl, rfl⟩ := owns
  constructor
  · rcases cl with b | o <;> exact id
  · rcases cr with b | o <;> exact id

theorem inRetained_iff_of_adj {Z R : Finset object.Vertex}
    (free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    {O : OutsideContext (SupportAtom.boundary object Z)}
    {x y : GluedVertex (SupportAtom.retainedPiece object Z R) O}
    (adj : (glue (SupportAtom.retainedPiece object Z R) O).graph.Adj x y) :
    (InRetained Z R x ↔ InRetained Z R y) := by
  rcases (glueGraph_adj_iff _ O x y).1 adj with owns | owns
  · obtain ⟨hx, hy⟩ := pieceOwns_inRetained free owns
    exact iff_of_true hx hy
  · obtain ⟨hx, hy⟩ := contextOwns_not_inRetained owns
    exact iff_of_false hx hy

theorem walk_inRetained {Z R : Finset object.Vertex}
    (free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    {O : OutsideContext (SupportAtom.boundary object Z)} :
    ∀ {x y : GluedVertex (SupportAtom.retainedPiece object Z R) O}
      (walk : (glue (SupportAtom.retainedPiece object Z R) O).graph.Walk x y),
      ∀ v ∈ walk.support, (InRetained Z R v ↔ InRetained Z R x)
  | _, _, .nil, v, hv => by
      simp at hv
      subst hv
      exact Iff.rfl
  | _, _, .cons adj rest, v, hv => by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact Iff.rfl
      · exact (walk_inRetained free rest v hv).trans (inRetained_iff_of_adj free adj).symm

/-- The ambient vertex of a retained glued vertex. -/
def inRetainedVertex (Z R : Finset object.Vertex)
    {O : OutsideContext (SupportAtom.boundary object Z)} :
    ∀ x : GluedVertex (SupportAtom.retainedPiece object Z R) O,
      InRetained Z R x → object.Vertex
  | .inl _, h => h.elim
  | .inr (.inl w), _ => w.1
  | .inr (.inr _), h => h.elim

/-- Decode a retained glued vertex back to the ambient graph (default elsewhere). -/
def retainedDecode (Z R : Finset object.Vertex)
    {O : OutsideContext (SupportAtom.boundary object Z)} (default : object.Vertex) :
    GluedVertex (SupportAtom.retainedPiece object Z R) O → object.Vertex
  | .inl b => b.1
  | .inr (.inl w) => w.1
  | .inr (.inr _) => default

/-- The retained part of any gluing embeds in the ambient graph. -/
def retainedHom {Z R : Finset object.Vertex}
    (_free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    {O : OutsideContext (SupportAtom.boundary object Z)} (default : object.Vertex) :
    (glue (SupportAtom.retainedPiece object Z R) O).graph.induce
        {x | InRetained Z R x} →g object.graph where
  toFun x := retainedDecode Z R default x.1
  map_rel' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ adj
    have adj' : (glue (SupportAtom.retainedPiece object Z R) O).graph.Adj x y := adj
    rcases (glueGraph_adj_iff _ O x y).1 adj' with owns | owns
    · obtain ⟨pl, pr, padj, rfl, rfl⟩ := owns
      have padj' := padj
      change (SimpleGraph.comap (SupportAtom.pieceDecode object Z) object.graph ⊓
        SimpleGraph.comap (SupportAtom.pieceDecode object Z)
          (SimpleGraph.fromRel fun left right => left ∈ R ∧ right ∈ R)).Adj _ _ at padj'
      rw [SimpleGraph.inf_adj, SimpleGraph.comap_adj] at padj'
      rcases pl with b | w <;> rcases pr with b' | w' <;> exact padj'.1
    · exact absurd hx (contextOwns_not_inRetained owns).1

theorem retainedHom_injective {Z R : Finset object.Vertex}
    (free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    {O : OutsideContext (SupportAtom.boundary object Z)} (default : object.Vertex) :
    Function.Injective (retainedHom free (O := O) default) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  rcases x with b | w | o <;> try exact absurd hx id
  rcases y with b' | w' | o' <;> try exact absurd hy id
  have h' : w.1 = w'.1 := h
  have : w = w' := Subtype.ext h'
  subst this
  rfl

/-- **Boundary-free readings see only the context** (vocabulary-free).  If a
reading `R` of `Z` retains no vertex of `∂Z` and the ambient graph has no
accepted cycle, then every accepted cycle of `R` glued to any context `O` is an
accepted cycle of any other reading `R'` glued to `O`. -/
theorem target_transfer_of_boundaryFree {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {Z R : Finset object.Vertex}
    (free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    (R' : Finset object.Vertex)
    (O : OutsideContext (SupportAtom.boundary object Z))
    (cycle : HasCycleWithLength LengthOK (glue (SupportAtom.retainedPiece object Z R) O)) :
    HasCycleWithLength LengthOK (glue (SupportAtom.retainedPiece object Z R') O) := by
  obtain ⟨c⟩ := cycle
  by_cases start : InRetained Z R c.vertex
  · -- the cycle lives in the retained internal vertices: it is a cycle of G
    exfalso
    let s : Set (glue (SupportAtom.retainedPiece object Z R) O).Vertex :=
      {x | InRetained Z R x}
    have allIn : ∀ v ∈ c.walk.support, v ∈ s := fun v hv =>
      (walk_inRetained free c.walk v hv).2 start
    let default : object.Vertex := inRetainedVertex Z R c.vertex start
    have mapEq := SimpleGraph.Walk.map_induce c.walk allIn
    have hind : (c.walk.induce s allIn).IsCycle := by
      rw [← SimpleGraph.Walk.map_isCycle_iff_of_injective
        (f := (SimpleGraph.Embedding.induce
          (G := (glue (SupportAtom.retainedPiece object Z R) O).graph) s).toHom)
        (SimpleGraph.Embedding.induce
          (G := (glue (SupportAtom.retainedPiece object Z R) O).graph) s).injective, mapEq]
      exact c.isCycle
    have hlen : (c.walk.induce s allIn).length = c.walk.length := by
      have := congrArg SimpleGraph.Walk.length mapEq
      rwa [SimpleGraph.Walk.length_map] at this
    exact avoids ⟨⟨_, (c.walk.induce s allIn).map (retainedHom free default),
      hind.map (retainedHom_injective free default),
      by convert c.length_ok using 1; exact (SimpleGraph.Walk.length_map _ _).trans hlen⟩⟩
  · have edgesIn : ∀ e ∈ c.walk.edges,
        e ∈ (glue (SupportAtom.retainedPiece object Z R') O).graph.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have adj := c.walk.adj_of_mem_edges he
        have ha := c.walk.fst_mem_support_of_mem_edges he
        rcases (glueGraph_adj_iff _ O a b).1 adj with owns | owns
        · exact absurd ((walk_inRetained free c.walk a ha).1
            (pieceOwns_inRetained free owns).1) start
        · obtain ⟨cl, cr, cadj, h1, h2⟩ := owns
          exact (glueGraph_adj_iff (SupportAtom.retainedPiece object Z R') O a b).2
            (Or.inr ⟨cl, cr, cadj, h1, h2⟩)
    exact ⟨⟨c.vertex, c.walk.transfer _ edgesIn, c.isCycle.transfer edgesIn,
      by convert c.length_ok using 1; apply SimpleGraph.Walk.length_transfer⟩⟩

/-- **Two boundary-free readings are context-equivalent and in one fibre**
(vocabulary-free): two readings that retain no vertex of `∂Z` have the same
(zero) boundary-degree profile and the same response in every context. -/
theorem boundaryFree_contextEquivalent {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {Z R R' : Finset object.Vertex}
    (free : ∀ w ∈ R, w ∉ SupportAtom.cutBoundary object Z)
    (free' : ∀ w ∈ R', w ∉ SupportAtom.cutBoundary object Z) :
    (SupportAtom.retainedPiece object Z R).boundaryDegreeProfile =
        (SupportAtom.retainedPiece object Z R').boundaryDegreeProfile ∧
      Response.ContextEquivalent (HasCycleWithLength LengthOK)
        (SupportAtom.retainedPiece object Z R)
        (SupportAtom.retainedPiece object Z R') := by
  refine ⟨?_, fun O => ⟨target_transfer_of_boundaryFree avoids free R' O,
    target_transfer_of_boundaryFree avoids free' R O⟩⟩
  funext b
  change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
    (SupportAtom.retainedPiece object Z R').boundaryDegree b
  rw [retained_boundaryDegree_eq_zero Z R b (fun h => free _ h b.2),
    retained_boundaryDegree_eq_zero Z R' b (fun h => free' _ h b.2)]



/-- The exact reading count `c_R(b) = #{w ∈ Z : b ~ w, b ∈ R, w ∈ R}`. -/
noncomputable def readingCount (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) : Nat :=
  {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R}.ncard

/-- Profile equality of two readings is exactly equality of reading counts. -/
theorem profile_eq_iff_counts (Z R R' : Finset object.Vertex) :
    (SupportAtom.retainedPiece object Z R).boundaryDegreeProfile =
        (SupportAtom.retainedPiece object Z R').boundaryDegreeProfile ↔
      ∀ b, readingCount Z R b = readingCount Z R' b := by
  constructor
  · intro h b
    have := congrFun h b
    change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
      (SupportAtom.retainedPiece object Z R').boundaryDegree b at this
    rwa [retained_boundaryDegree, retained_boundaryDegree] at this
  · intro h
    funext b
    change (SupportAtom.retainedPiece object Z R).boundaryDegree b =
      (SupportAtom.retainedPiece object Z R').boundaryDegree b
    rw [retained_boundaryDegree, retained_boundaryDegree]
    exact h b

/-- **D1 degree bound** (vocabulary-free): at a boundary vertex of `Z`, every
reading count is at most `deg_G(b) − 1` (the outside neighbour is never
counted). -/
theorem readingCount_add_one_le (Z R : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    readingCount Z R b + 1 ≤ object.degree b.1 := by
  letI : Finite object.Vertex := by letI := object.vertices; infer_instance
  obtain ⟨-, n, adj, nZ⟩ := (SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have sub : {w | w ∈ Z ∧ object.graph.Adj b.1 w ∧ b.1 ∈ R ∧ w ∈ R} ⊆
      object.graph.neighborSet b.1 \ {n} := by
    rintro w ⟨wZ, wAdj, -, -⟩
    refine ⟨wAdj, ?_⟩
    rintro rfl
    exact nZ wZ
  calc readingCount Z R b + 1 ≤ (object.graph.neighborSet b.1 \ {n}).ncard + 1 :=
        Nat.add_le_add_right (Set.ncard_le_ncard sub (Set.toFinite _)) 1
    _ = _ := Set.ncard_sdiff_singleton_add_one adj (Set.toFinite _)


/-- A positive reading count means `b` is retained and has a retained
`Z`-neighbour. -/
theorem readingCount_pos {Z R : Finset object.Vertex}
    {b : (SupportAtom.boundary object Z).Vertex} (pos : 0 < readingCount Z R b) :
    b.1 ∈ R ∧ ∃ w ∈ R, object.graph.Adj b.1 w := by
  obtain ⟨w, wZ, adj, bR, wR⟩ := (Set.ncard_pos (Set.toFinite _)).1 pos
  exact ⟨bR, w, wR, adj⟩


section Active

variable {G : FiniteObject.{u}}

/-- The active part of a support: vertices with a neighbour in `Z ∩ X`. -/
noncomputable def activePart (Z X : Finset G.Vertex) : Finset G.Vertex := by
  classical
  exact X.filter fun v => ∃ x, x ∈ Z ∧ x ∈ X ∧ G.graph.Adj v x

theorem retained_le_active (Z X : Finset G.Vertex) :
    (SupportAtom.retainedPiece G Z X).graph ≤
      (SupportAtom.retainedPiece G Z (activePart Z X)).graph := by
  classical
  intro p q h
  have mem := GluedReadings.retained_adj_mem h
  have gadj : G.graph.Adj (SupportAtom.pieceDecode G Z p) (SupportAtom.pieceDecode G Z q) := h.1
  refine ⟨h.1, ?_⟩
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
  refine ⟨h.2.1, Or.inl ⟨?_, ?_⟩⟩
  · simp only [activePart, Finset.mem_filter]
    exact ⟨mem.1, _, pieceDecode_mem Z q, mem.2, gadj⟩
  · simp only [activePart, Finset.mem_filter]
    exact ⟨mem.2, _, pieceDecode_mem Z p, mem.1, gadj.symm⟩

theorem readingCount_pos_of_active {Z X : Finset G.Vertex}
    {l : (SupportAtom.boundary G Z).Vertex} (h : l.1 ∈ activePart Z X) :
    0 < readingCount Z X l := by
  classical
  simp only [activePart, Finset.mem_filter] at h
  obtain ⟨lX, x, xZ, xX, adj⟩ := h
  unfold readingCount
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨x, xZ, adj, lX, xX⟩

/-- **Two active labels** (vocabulary-free).  On an avoiding object, every
accepted cycle of a reading glued to a cycle-free context crosses `∂Z` at two
distinct labels, each with a positive reading count. -/
theorem two_active_labels {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L G)
    {Z X : Finset G.Vertex} {O : OutsideContext (SupportAtom.boundary G Z)}
    (ctxFree : ¬ HasCycleWithLength L O.pack)
    (pos : HasCycleWithLength L (glue (SupportAtom.retainedPiece G Z X) O)) :
    ∃ l₁ l₂ : (SupportAtom.boundary G Z).Vertex, l₁ ≠ l₂ ∧
      0 < readingCount Z X l₁ ∧ 0 < readingCount Z X l₂ := by
  have pos' := GluedReadings.glue_mono_of_le (retained_le_active Z X) O pos
  obtain ⟨c⟩ := pos'
  have hp := DefectGeometry.pieceExclusive c ctxFree
  have ho : DefectGeometry.ContextExclusive c := by
    rcases DefectGeometry.local_or_mixed c with loc | mix
    · exact absurd (DefectGeometry.local_target c loc)
        (GluedReadings.retainedPiece_avoids avoids Z _)
    · exact mix
  obtain ⟨l₁, l₂, ne, h1, h2⟩ := GluedReadings.two_retained_labels c hp ho
  exact ⟨l₁, l₂, ne, readingCount_pos_of_active h1, readingCount_pos_of_active h2⟩

/-- **Every accepted cycle of the positive reading uses a private edge**
(vocabulary-free): if `glue ret_P O` has an accepted cycle `c` and
`glue ret_N O` has none, then `c` traverses the glued copy of a `G`-edge
`xy` with `x, y ∈ Z ∩ P` and not both in `N`. -/
theorem cycle_uses_private {L : Nat → Prop} {Z P N : Finset G.Vertex}
    {O : OutsideContext (SupportAtom.boundary G Z)}
    (c : CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) L)
    (neg : ¬ HasCycleWithLength L (glue (SupportAtom.retainedPiece G Z N) O)) :
    ∃ pl pr : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z,
      s(pieceEmbedding (SupportAtom.retainedPiece G Z P) O pl,
        pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr) ∈ c.walk.edges ∧
      G.graph.Adj (SupportAtom.pieceDecode G Z pl) (SupportAtom.pieceDecode G Z pr) ∧
      SupportAtom.pieceDecode G Z pl ∈ P ∧ SupportAtom.pieceDecode G Z pr ∈ P ∧
      ¬ (SupportAtom.pieceDecode G Z pl ∈ N ∧ SupportAtom.pieceDecode G Z pr ∈ N) := by
  classical
  by_contra none
  push Not at none
  apply neg
  have edgesIn : ∀ e ∈ c.walk.edges,
      e ∈ (glue (SupportAtom.retainedPiece G Z N) O).graph.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have adj := c.walk.adj_of_mem_edges he
      rcases (glueGraph_adj_iff _ O a b).1 adj with owns | owns
      · obtain ⟨pl, pr, padj, rfl, rfl⟩ := owns
        have mem := GluedReadings.retained_adj_mem padj
        have both := none pl pr he padj.1 mem.1 mem.2
        refine (glueGraph_adj_iff (SupportAtom.retainedPiece G Z N) O _ _).2
          (Or.inl ⟨pl, pr, ⟨padj.1, ?_⟩, ?_, ?_⟩)
        · simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
          exact ⟨padj.2.1, Or.inl both⟩
        · cases pl <;> rfl
        · cases pr <;> rfl
      · obtain ⟨cl, cr, cadj, h1, h2⟩ := owns
        exact (glueGraph_adj_iff (SupportAtom.retainedPiece G Z N) O a b).2
          (Or.inr ⟨cl, cr, cadj, h1, h2⟩)
  exact ⟨⟨c.vertex, c.walk.transfer _ edgesIn, c.isCycle.transfer edgesIn,
    by convert c.length_ok using 1; apply SimpleGraph.Walk.length_transfer⟩⟩

end Active

end Hypostructure.Graph.ReadingCounts
