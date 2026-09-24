import Hypostructure.Graph.GluedCycleSides

/-! Structural facts about the literal context supplied by a target defect. -/

namespace Hypostructure.Graph

universe u

/-- The orientation and target-free sides of one bound target-defect witness.
The context here is the witness in `Response.TargetDefect`, not the ambient
graph's outside. -/
def TargetDefectStructure {boundary : Boundary.{u}}
    (LengthOK : Nat → Prop) (left right : BoundaryPiece boundary) : Prop :=
  ∃ outside : OutsideContext boundary,
    (HasCycleWithLength LengthOK (glue left outside) ∧
       ¬ HasCycleWithLength LengthOK (glue right outside) ∧
       ¬ HasCycleWithLength LengthOK (OutsideContext.pack outside) ∧
       ¬ HasCycleWithLength LengthOK (BoundaryPiece.pack right)) ∨
    (HasCycleWithLength LengthOK (glue right outside) ∧
       ¬ HasCycleWithLength LengthOK (glue left outside) ∧
       ¬ HasCycleWithLength LengthOK (OutsideContext.pack outside) ∧
       ¬ HasCycleWithLength LengthOK (BoundaryPiece.pack left))

/-- The negative gluing excludes accepted cycles on both of its literal
constituents. This keeps the original defect context and pair bound together. -/
theorem targetDefect_structure {boundary : Boundary.{u}}
    {LengthOK : Nat → Prop} {left right : BoundaryPiece boundary}
    (defect : Response.TargetDefect (HasCycleWithLength LengthOK) left right) :
    TargetDefectStructure LengthOK left right := by
  obtain ⟨outside, different⟩ := defect
  by_cases positiveLeft : HasCycleWithLength LengthOK (glue left outside)
  · have negativeRight : ¬ HasCycleWithLength LengthOK (glue right outside) := by
      intro positiveRight
      exact different ⟨fun _ => positiveRight, fun _ => positiveLeft⟩
    refine ⟨outside, Or.inl ⟨positiveLeft, negativeRight, ?_, ?_⟩⟩
    · intro contextCycle
      exact negativeRight (hasCycleWithLength_of_hom
        (contextHom right outside) (contextEmbedding right outside).injective
        contextCycle)
    · intro pieceCycle
      exact negativeRight (hasCycleWithLength_of_hom
        (pieceHom right outside) (pieceEmbedding right outside).injective
        pieceCycle)
  · have positiveRight : HasCycleWithLength LengthOK (glue right outside) := by
      by_contra negativeRight
      exact different ⟨fun yes => (positiveLeft yes).elim,
        fun yes => (negativeRight yes).elim⟩
    refine ⟨outside, Or.inr ⟨positiveRight, positiveLeft, ?_, ?_⟩⟩
    · intro contextCycle
      exact positiveLeft (hasCycleWithLength_of_hom
        (contextHom left outside) (contextEmbedding left outside).injective
        contextCycle)
    · intro pieceCycle
      exact positiveLeft (hasCycleWithLength_of_hom
        (pieceHom left outside) (pieceEmbedding left outside).injective
        pieceCycle)

/-- Forgetting the localization recovers the exact original target defect. -/
theorem TargetDefectStructure.toTargetDefect {boundary : Boundary.{u}}
    {LengthOK : Nat → Prop} {left right : BoundaryPiece boundary}
    (localization : TargetDefectStructure LengthOK left right) :
    Response.TargetDefect (HasCycleWithLength LengthOK) left right := by
  obtain ⟨outside, positiveLeft | positiveRight⟩ := localization
  · exact ⟨outside, fun equivalent => positiveLeft.2.1 (equivalent.mp positiveLeft.1)⟩
  · exact ⟨outside, fun equivalent => positiveRight.2.1 (equivalent.mpr positiveRight.1)⟩


namespace DefectGeometry

/-- Lift the very same walk along an injective side inclusion. -/
theorem liftWalk {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) :
    ∀ {a b : W} (w : H.Walk a b) {x y : V}, f x = a → f y = b →
      (∀ p q, s(p,q) ∈ w.edges → ∃ r t, G.Adj r t ∧ f r = p ∧ f t = q) →
      ∃ l : G.Walk x y, l.length = w.length ∧
        w.support = l.support.map f ∧ w.edges = l.edges.map (Sym2.map f) := by
  intro a b w
  induction w with
  | nil =>
      intro x y hx hy h
      have eq : x = y := f.injective (hx.trans hy.symm)
      subst y
      exact ⟨.nil, rfl, by simp [hx], rfl⟩
  | @cons a b c adj rest ih =>
      intro x y hx hy h
      obtain ⟨r,t,hrt,hr,ht⟩ := h a b (by simp)
      have rx : r = x := f.injective (hr.trans hx.symm)
      subst r
      obtain ⟨l,hl,hs,he⟩ := ih ht hy (by
        intro p q hpq
        exact h p q (by simp only [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hpq))
      refine ⟨.cons hrt l, ?_, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_cons, hl]
      · simp only [SimpleGraph.Walk.support_cons, List.map_cons, hs, hx, ht]
      · simp only [SimpleGraph.Walk.edges_cons, List.map_cons, he]
        change s(a,b) :: _ = s(f x,f t) :: _
        rw [hx,ht]

/-- A side containing all edges contains this cycle, with unchanged length. -/
theorem liftCycle {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) {a : W} (w : H.Walk a a) (hc : w.IsCycle)
    (h : ∀ p q, s(p,q) ∈ w.edges → ∃ r t, G.Adj r t ∧ f r = p ∧ f t = q) :
    ∃ (x : V) (l : G.Walk x x), l.IsCycle ∧ l.length = w.length ∧
      w.support = l.support.map f ∧ w.edges = l.edges.map (Sym2.map f) := by
  have base : ∃ x, f x = a := by
    cases w with
    | nil => have hn := hc.three_le_length; simp at hn
    | @cons _ b _ adj rest =>
        obtain ⟨x,y,hxy,hx,hy⟩ := h a b (by simp)
        exact ⟨x,hx⟩
  obtain ⟨x,hx⟩ := base
  obtain ⟨l,hl,hs,he⟩ := liftWalk f w hx hx h
  refine ⟨x,l,?_,hl,hs,he⟩
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · have hn := hc.edges_nodup
    rw [he] at hn
    exact hn.of_map
  · intro hn
    have hz : l.length = 0 := by rw [hn]; rfl
    have := hc.three_le_length
    omega
  · have hn := hc.support_nodup
    rw [hs, ← List.map_tail] at hn
    exact hn.of_map

variable {boundary : Boundary.{u}} {P : BoundaryPiece boundary}
    {O : OutsideContext boundary} {LengthOK : Nat → Prop}

/-- Edge ownership is recorded on the original cycle, including label edges. -/
def PieceExclusive (c : CycleCertificate (glue P O) LengthOK) : Prop :=
  ∃ x y, s(x,y) ∈ c.walk.edges ∧ PieceOwns P O x y ∧ ¬ ContextOwns P O x y

def ContextExclusive (c : CycleCertificate (glue P O) LengthOK) : Prop :=
  ∃ x y, s(x,y) ∈ c.walk.edges ∧ ContextOwns P O x y ∧ ¬ PieceOwns P O x y

def PieceLocal (c : CycleCertificate (glue P O) LengthOK) : Prop :=
  ∃ (x : boundary.Vertex ⊕ P.Internal) (l : P.graph.Walk x x),
    l.IsCycle ∧ l.length = c.walk.length ∧
    c.walk.support = l.support.map (pieceEmbedding P O) ∧
    c.walk.edges = l.edges.map (Sym2.map (pieceEmbedding P O))

def TwoLabels (c : CycleCertificate (glue P O) LengthOK) : Prop :=
  ∃ a b : boundary.Vertex, a ≠ b ∧
    Sum.inl a ∈ c.walk.support ∧ Sum.inl b ∈ c.walk.support

theorem pieceExclusive (c : CycleCertificate (glue P O) LengthOK)
    (avoids : ¬ HasCycleWithLength LengthOK (OutsideContext.pack O)) :
    PieceExclusive c := by
  classical
  by_contra hn
  have all : ∀ x y, s(x,y) ∈ c.walk.edges → ContextOwns P O x y := by
    intro x y he
    rcases (glueGraph_adj_iff P O x y).mp (c.walk.adj_of_mem_edges he) with hp | ho
    · by_contra ho
      exact hn ⟨x,y,he,hp,ho⟩
    · exact ho
  obtain ⟨x,l,hc,hl,_,_⟩ := liftCycle (contextEmbedding P O) c.walk c.isCycle all
  exact avoids ⟨⟨x,l,hc,hl ▸ c.length_ok⟩⟩

theorem local_or_mixed (c : CycleCertificate (glue P O) LengthOK) :
    PieceLocal c ∨ ContextExclusive c := by
  classical
  by_cases h : ∀ x y, s(x,y) ∈ c.walk.edges → PieceOwns P O x y
  · exact Or.inl (liftCycle (pieceEmbedding P O) c.walk c.isCycle h)
  · push_neg at h
    obtain ⟨x,y,he,hn⟩ := h
    have ho := (glueGraph_adj_iff P O x y).mp (c.walk.adj_of_mem_edges he)
    exact Or.inr ⟨x,y,he,ho.resolve_left hn,hn⟩

theorem local_target (c : CycleCertificate (glue P O) LengthOK)
    (h : PieceLocal c) : HasCycleWithLength LengthOK (BoundaryPiece.pack P) := by
  obtain ⟨x,l,hc,hl,_,_⟩ := h
  exact ⟨⟨x,l,hc,hl ▸ c.length_ok⟩⟩

/-- Two exclusive sources either expose label endpoints directly, or both interiors. -/
theorem twoLabels_of_exclusive (c : CycleCertificate (glue P O) LengthOK)
    (hp : PieceExclusive c) (ho : ContextExclusive c) : TwoLabels c := by
  have pieceSide : TwoLabels c ∨ ∃ i : P.Internal,
      Sum.inr (Sum.inl i) ∈ c.walk.support := by
    obtain ⟨x,y,he,⟨p,q,adj,hx,hy⟩,_⟩ := hp
    have mx := c.walk.fst_mem_support_of_mem_edges he
    have my := c.walk.snd_mem_support_of_mem_edges he
    rw [← hx] at mx
    rw [← hy] at my
    rcases p with a | i
    · rcases q with b | j
      · exact Or.inl ⟨a,b,fun eq => adj.ne (congrArg Sum.inl eq),mx,my⟩
      · exact Or.inr ⟨j,my⟩
    · exact Or.inr ⟨i,mx⟩
  have contextSide : TwoLabels c ∨ ∃ i : O.Internal,
      Sum.inr (Sum.inr i) ∈ c.walk.support := by
    obtain ⟨x,y,he,⟨p,q,adj,hx,hy⟩,_⟩ := ho
    have mx := c.walk.fst_mem_support_of_mem_edges he
    have my := c.walk.snd_mem_support_of_mem_edges he
    rw [← hx] at mx
    rw [← hy] at my
    rcases p with a | i
    · rcases q with b | j
      · exact Or.inl ⟨a,b,fun eq => adj.ne (congrArg Sum.inl eq),mx,my⟩
      · exact Or.inr ⟨j,my⟩
    · exact Or.inr ⟨i,mx⟩
  rcases pieceSide with labels | ⟨i,hi⟩
  · exact labels
  rcases contextSide with labels | ⟨j,hj⟩
  · exact labels
  exact GluedCycleSides.exists_two_labels_of_cycle_sides c.isCycle hi hj

theorem empty_local (c : CycleCertificate (glue P O) LengthOK)
    (hp : PieceExclusive c) (empty : IsEmpty boundary.Vertex) : PieceLocal c := by
  rcases local_or_mixed c with localized | mixed
  · exact localized
  · obtain ⟨a,b,_,_,_⟩ := twoLabels_of_exclusive c hp mixed
    exact (empty.false a).elim

theorem realized_mixed (c : CycleCertificate (glue P O) LengthOK)
    (hp : PieceExclusive c)
    (avoids : ¬ HasCycleWithLength LengthOK (BoundaryPiece.pack P)) :
    ContextExclusive c ∧ TwoLabels c := by
  rcases local_or_mixed c with localized | mixed
  · exact (avoids (local_target c localized)).elim
  · exact ⟨mixed,twoLabels_of_exclusive c hp mixed⟩

/-- An induced realization of this piece on the specified support. Boundary-fixing
realizations are included; the proof only needs the displayed underlying map. -/
structure SupportRealization (G : FiniteObject.{u}) (S : Finset G.Vertex)
    {boundary : Boundary.{u}} (P : BoundaryPiece boundary) where
  vertices : (boundary.Vertex ⊕ P.Internal) ≃ {v : G.Vertex // v ∈ S}
  adjacency : ∀ x y, P.graph.Adj x y ↔ G.graph.Adj (vertices x).val (vertices y).val

def SupportRealization.hom {G : FiniteObject.{u}} {S : Finset G.Vertex}
    {boundary : Boundary.{u}} {P : BoundaryPiece boundary}
    (r : SupportRealization G S P) : P.graph →g G.graph where
  toFun x := (r.vertices x).val
  map_rel' := (r.adjacency _ _).mp

theorem SupportRealization.injective {G : FiniteObject.{u}} {S : Finset G.Vertex}
    {boundary : Boundary.{u}} {P : BoundaryPiece boundary}
    (r : SupportRealization G S P) : Function.Injective r.hom := by
  intro x y h
  exact r.vertices.injective (Subtype.ext h)

/-- The selected implications all refer to each original positive certificate. -/
structure PositiveStructure (G : FiniteObject.{u}) (S : Finset G.Vertex)
    {boundary : Boundary.{u}} (LengthOK : Nat → Prop)
    (P N : BoundaryPiece boundary) (O : OutsideContext boundary) : Prop where
  positive : HasCycleWithLength LengthOK (glue P O)
  negative : ¬ HasCycleWithLength LengthOK (glue N O)
  contextFree : ¬ HasCycleWithLength LengthOK (OutsideContext.pack O)
  negativePieceFree : ¬ HasCycleWithLength LengthOK (BoundaryPiece.pack N)
  indispensable : ∀ c : CycleCertificate (glue P O) LengthOK, PieceExclusive c
  emptyBoundary : ∀ c : CycleCertificate (glue P O) LengthOK,
    IsEmpty boundary.Vertex → PieceLocal c
  realized : ∀ c : CycleCertificate (glue P O) LengthOK,
    SupportRealization G S P → ¬ PieceLocal c ∧ ContextExclusive c ∧ TwoLabels c
  external : ∀ c : CycleCertificate (glue P O) LengthOK,
    PieceLocal c ∨ (ContextExclusive c ∧ TwoLabels c)

end DefectGeometry

/-- One publication, retaining the same defect context in either orientation. -/
def BoundTargetDefectGeometry (G : FiniteObject.{u}) (S : Finset G.Vertex)
    {boundary : Boundary.{u}} (LengthOK : Nat → Prop)
    (left right : BoundaryPiece boundary) : Prop :=
  ∃ O : OutsideContext boundary,
    (¬ (HasCycleWithLength LengthOK (glue left O) ↔
        HasCycleWithLength LengthOK (glue right O))) ∧
    (DefectGeometry.PositiveStructure G S LengthOK left right O ∨
     DefectGeometry.PositiveStructure G S LengthOK right left O)

end Hypostructure.Graph
