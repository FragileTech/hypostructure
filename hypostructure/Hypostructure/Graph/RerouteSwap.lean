import Hypostructure.Graph.Transplant

/-!
# The rerouted swap of a reading into `Z` (`[144a]`, G audit S144a)

Vocabulary-free.  Fix a finite object `G`, a support `Z` with cut boundary
`∂Z`, and two vertex sets `P` (the replaced reading) and `Q` (the inserted
reading).  `swapPiece G Z P Q` is the `∂Z`-piece obtained from `G[Z]` by
**replacing the interior structure of `P` by a fresh copy of the interior
structure of `Q`**:

* interior: `int(Z) ∖ P` (the rest of `Z`, on `G`'s own vertices) together
  with a copy of `int(Z) ∩ Q` (fresh vertices);
* edges: the edges of `G` among `∂Z ∪ (int(Z) ∖ P)`; the edges of `G` among
  `∂Z ∪ (int(Z) ∩ Q)` *on the copy*; and no edge between the rest and the copy.

Unlike `Transplant.transplant`, this piece is not a subgraph of `G` when
`int(Z) ∩ Q` meets `int(Z) ∖ P`: the copy carries `Q`'s vertices a second time.
Its conditions are exact predicates on `G`:

* (i) the boundary profile of `G[Z]`: iff every `b ∈ ∂Z` has as many interior
  neighbours in `Q` as in `P` (the equal-contact-count identity);
* (ii) the baseline of `glue (swapPiece) (G − Z)`: iff four degree predicates
  on `G` (`SwapDegreeCondition`) hold, each read at a vertex of `G` in a role
  (rest, copy, boundary, outside);
* (iii) the interior size is `|int Z| − |int Z ∩ P| + |int Z ∩ Q|`;
* (iv) linkage inclusion: it holds when `int Z ∩ Q ⊆ P`; and if it fails, some
  linkage of the piece uses a vertex of `int Z ∩ Q ∖ P` both as itself and as
  its copy.
-/

namespace Hypostructure.Graph.RerouteSwap

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.Transplant

universe u

variable (object : FiniteObject.{u})

/-- Interior vertices of `Z` outside the replaced reading `P`. -/
abbrev RestInternal (Z P : Finset object.Vertex) :=
  {v : object.Vertex // v ∈ Z ∧ v ∉ SupportAtom.cutBoundary object Z ∧ v ∉ P}

/-- The interior of the swap piece: the rest of `Z`, and a copy of `int(Z) ∩ Q`. -/
abbrev SwapInternal (Z P Q : Finset object.Vertex) :=
  RestInternal object Z P ⊕ TransplantInternal object Z Q

/-- Decode a vertex of the swap piece to `G` (the copy decodes to its original). -/
def swapDecode (Z P Q : Finset object.Vertex) :
    (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q → object.Vertex
  | .inl b => b.1
  | .inr (.inl x) => x.1
  | .inr (.inr y) => y.1

variable {object}

/-- Rest-to-copy pairs, which the swap piece does not join. -/
def Cross {Z P Q : Finset object.Vertex} :
    (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q →
    (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q → Prop
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inr (.inl _) => True
  | _, _ => False

theorem Cross.symm {Z P Q : Finset object.Vertex}
    {a c : (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q}
    (h : Cross a c) : Cross c a := by
  rcases a with b | (x | y) <;> rcases c with b' | (x' | y') <;> simp only [Cross] at h ⊢

variable (object)

/-- The edges of the swap piece: edges of `G` between decoded ends, except
between the rest and the copy. -/
def swapGraph (Z P Q : Finset object.Vertex) :
    SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q) where
  Adj a c := object.graph.Adj (swapDecode object Z P Q a) (swapDecode object Z P Q c) ∧
    ¬ Cross a c
  symm := ⟨fun _ _ ⟨h, k⟩ => ⟨h.symm, fun k' => k k'.symm⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => object.graph.loopless.irrefl _ h⟩

/-- **The swap piece**: `G[Z]` with the interior structure of `P` replaced by a
copy of the interior structure of `Q`, on `∂Z`'s own labels. -/
noncomputable def swapPiece (Z P Q : Finset object.Vertex) :
    BoundaryPiece (SupportAtom.boundary object Z) where
  Internal := SwapInternal object Z P Q
  internalVertices := by
    classical
    letI : FinEnum object.Vertex := object.vertices
    infer_instance
  graph := swapGraph object Z P Q
  decideAdj := Classical.decRel _


/-! ## Sizes -/

section Sizes

variable {object}

/-- The number of interior vertices of `Z` in `Y`. -/
noncomputable def intCount (Z Y : Finset object.Vertex) : Nat :=
  Nat.card (TransplantInternal object Z Y)

theorem finEnum_card_eq_natCard (α : Type u) (e : FinEnum α) : e.card = Nat.card α := by
  letI := e
  rw [Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard]

/-- The interior of `G[Z]` splits by membership in `P`. -/
noncomputable def pieceSplit (Z P : Finset object.Vertex) :
    SupportAtom.PieceInternal object Z ≃ RestInternal object Z P ⊕ TransplantInternal object Z P := by
  classical
  exact
    { toFun := fun x =>
        if h : x.1 ∈ P then .inr ⟨x.1, x.2.1, x.2.2, h⟩ else .inl ⟨x.1, x.2.1, x.2.2, h⟩
      invFun := fun s => match s with
        | .inl x => ⟨x.1, x.2.1, x.2.2.1⟩
        | .inr y => ⟨y.1, y.2.1, y.2.2.1⟩
      left_inv := by
        intro x
        by_cases h : x.1 ∈ P <;> simp [h]
      right_inv := by
        intro s
        rcases s with x | y
        · have h : x.1 ∉ P := x.2.2.2
          simp [h]
        · have h : y.1 ∈ P := y.2.2.2
          simp [h] }

theorem finite_vertex : Finite object.Vertex := by
  letI := object.vertices
  infer_instance

/-- **(iii) The size of the swap piece**: `|int S| + |int Z ∩ P| = |int Z| + |int Z ∩ Q|`. -/
theorem swapPiece_internalVertexCount (Z P Q : Finset object.Vertex) :
    (swapPiece object Z P Q).internalVertexCount + intCount Z P =
      (SupportAtom.piece object Z).internalVertexCount + intCount Z Q := by
  haveI : Finite object.Vertex := finite_vertex
  unfold BoundaryPiece.internalVertexCount
  rw [finEnum_card_eq_natCard, finEnum_card_eq_natCard]
  change Nat.card (SwapInternal object Z P Q) + _ = Nat.card (SupportAtom.PieceInternal object Z) + _
  rw [Nat.card_sum, Nat.card_congr (pieceSplit Z P), Nat.card_sum]
  unfold intCount
  omega

end Sizes


/-! ## The glued swap -/

section Glue

variable {object}

/-- Decode a vertex of the glued swap to `G`. -/
def gdec (Z P Q : Finset object.Vertex) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex → object.Vertex
  | .inl b => b.1
  | .inr (.inl (.inl x)) => x.1
  | .inr (.inl (.inr y)) => y.1
  | .inr (.inr o) => o.1

/-- A vertex of the glued swap is a rest vertex. -/
def IsRest (Z P Q : Finset object.Vertex) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex → Prop
  | .inr (.inl (.inl _)) => True
  | _ => False

/-- A vertex of the glued swap is a copy vertex. -/
def IsCopy (Z P Q : Finset object.Vertex) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex → Prop
  | .inr (.inl (.inr _)) => True
  | _ => False

/-- The rest-to-copy pairs of the glued swap. -/
def GCross (Z P Q : Finset object.Vertex) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex →
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex → Prop
  | .inr (.inl (.inl _)), .inr (.inl (.inr _)) => True
  | .inr (.inl (.inr _)), .inr (.inl (.inl _)) => True
  | _, _ => False

theorem cut_of_adj_outside {Z : Finset object.Vertex} {x o : object.Vertex}
    (xZ : x ∈ Z) (adj : object.graph.Adj x o) (oZ : o ∉ Z) :
    x ∈ SupportAtom.cutBoundary object Z :=
  (SupportAtom.mem_cutBoundary_iff object Z x).2 ⟨xZ, o, adj, oZ⟩

/-- **Adjacency in the glued swap is adjacency in `G`, except between the rest and
the copy.** -/
theorem glue_swap_adj_iff (Z P Q : Finset object.Vertex)
    (a c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).graph.Adj a c ↔
      object.graph.Adj (gdec Z P Q a) (gdec Z P Q c) ∧ ¬ GCross Z P Q a c := by
  change (glueGraph (swapPiece object Z P Q) (SupportAtom.outside object Z)).Adj a c ↔ _
  rw [glueGraph_adj_iff]
  constructor
  · rintro (⟨pl, pr, h, rfl, rfl⟩ | ⟨cl, cr, h, rfl, rfl⟩)
    · rcases pl with b | (x | y) <;> rcases pr with b' | (x' | y') <;> exact h
    · rcases cl with b | o <;> rcases cr with b' | o' <;> exact ⟨h, fun hc => hc⟩
  · rintro ⟨h, nc⟩
    rcases a with b | ((x | y) | o) <;> rcases c with b' | ((x' | y') | o')
    · exact Or.inl ⟨.inl b, .inl b', ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact Or.inl ⟨.inl b, .inr (.inl x'), ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact Or.inl ⟨.inl b, .inr (.inr y'), ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact Or.inr ⟨.inl b, .inr o', h, rfl, rfl⟩
    · exact Or.inl ⟨.inr (.inl x), .inl b', ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact Or.inl ⟨.inr (.inl x), .inr (.inl x'), ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact absurd trivial nc
    · exact absurd (cut_of_adj_outside x.2.1 h o'.2) x.2.2.1
    · exact Or.inl ⟨.inr (.inr y), .inl b', ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact absurd trivial nc
    · exact Or.inl ⟨.inr (.inr y), .inr (.inr y'), ⟨h, fun hc => hc⟩, rfl, rfl⟩
    · exact absurd (cut_of_adj_outside y.2.1 h o'.2) y.2.2.1
    · exact Or.inr ⟨.inr o, .inl b', h, rfl, rfl⟩
    · exact absurd (cut_of_adj_outside x'.2.1 h.symm o.2) x'.2.2.1
    · exact absurd (cut_of_adj_outside y'.2.1 h.symm o.2) y'.2.2.1
    · exact Or.inr ⟨.inr o, .inr o', h, rfl, rfl⟩

/-- Equal decodes: the same vertex, or a rest vertex and its copy. -/
theorem gdec_eq_cases (Z P Q : Finset object.Vertex)
    {a c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex}
    (h : gdec Z P Q a = gdec Z P Q c) :
    a = c ∨ (IsRest Z P Q a ∧ IsCopy Z P Q c) ∨ (IsCopy Z P Q a ∧ IsRest Z P Q c) := by
  rcases a with b | ((x | y) | o) <;> rcases c with b' | ((x' | y') | o') <;>
    simp only [gdec] at h
  · exact Or.inl (congrArg Sum.inl (Subtype.ext h))
  · exact absurd (show x'.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) x'.2.2.1
  · exact absurd (show y'.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) y'.2.2.1
  · exact absurd (show o'.1 ∈ Z from h ▸ cutBoundary_subset b.2) o'.2
  · exact absurd (show x.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) x.2.2.1
  · exact Or.inl (congrArg (fun x => Sum.inr (Sum.inl (Sum.inl x))) (Subtype.ext h))
  · exact Or.inr (Or.inl ⟨trivial, trivial⟩)
  · exact absurd (show o'.1 ∈ Z from h ▸ x.2.1) o'.2
  · exact absurd (show y.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) y.2.2.1
  · exact Or.inr (Or.inr ⟨trivial, trivial⟩)
  · exact Or.inl (congrArg (fun x => Sum.inr (Sum.inl (Sum.inr x))) (Subtype.ext h))
  · exact absurd (show o'.1 ∈ Z from h ▸ y.2.1) o'.2
  · exact absurd (show o.1 ∈ Z from h.symm ▸ cutBoundary_subset b'.2) o.2
  · exact absurd (show o.1 ∈ Z from h.symm ▸ x'.2.1) o.2
  · exact absurd (show o.1 ∈ Z from h.symm ▸ y'.2.1) o.2
  · exact Or.inl (congrArg (fun o => Sum.inr (Sum.inr o)) (Subtype.ext h))


/-! ### Degrees in the glued swap, read on `G` -/

variable (object) in
/-- `w` is an interior vertex of `Z` lying in `Y`. -/
def InteriorIn (Z Y : Finset object.Vertex) (w : object.Vertex) : Prop :=
  w ∈ Z ∧ w ∉ SupportAtom.cutBoundary object Z ∧ w ∈ Y

variable (object) in
/-- `w` is an interior vertex of `Z` lying outside `Y`. -/
def InteriorOut (Z Y : Finset object.Vertex) (w : object.Vertex) : Prop :=
  w ∈ Z ∧ w ∉ SupportAtom.cutBoundary object Z ∧ w ∉ Y

/-- The degree, in the glued swap, of a rest vertex `v`: its `G`-neighbours
outside `int(Z) ∩ P`. -/
noncomputable def restDeg (Z P : Finset object.Vertex) (v : object.Vertex) : Nat :=
  {w | object.graph.Adj v w ∧ ¬ InteriorIn object Z P w}.ncard

/-- The degree, in the glued swap, of a copy vertex `v`: its `G`-neighbours in
`∂Z` or in `int(Z) ∩ Q`. -/
noncomputable def copyDeg (Z Q : Finset object.Vertex) (v : object.Vertex) : Nat :=
  {w | object.graph.Adj v w ∧ ¬ InteriorOut object Z Q w}.ncard

/-- The degree, in the glued swap, of a boundary vertex `b`: its `G`-neighbours
outside `int(Z) ∩ P`, plus its copies in `int(Z) ∩ Q`. -/
noncomputable def bdryDeg (Z P Q : Finset object.Vertex) (v : object.Vertex) : Nat :=
  {w | object.graph.Adj v w ∧ ¬ InteriorIn object Z P w}.ncard +
    {w | object.graph.Adj v w ∧ InteriorIn object Z Q w}.ncard

theorem exists_nonCopy {Z P Q : Finset object.Vertex} {w : object.Vertex}
    (h : ¬ InteriorIn object Z P w) :
    ∃ c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex,
      gdec Z P Q c = w ∧ ¬ IsCopy Z P Q c := by
  by_cases wZ : w ∈ Z
  · by_cases hb : w ∈ SupportAtom.cutBoundary object Z
    · exact ⟨.inl ⟨w, hb⟩, rfl, fun hc => hc⟩
    · have wP : w ∉ P := fun wP => h ⟨wZ, hb, wP⟩
      exact ⟨.inr (.inl (.inl ⟨w, wZ, hb, wP⟩)), rfl, fun hc => hc⟩
  · exact ⟨.inr (.inr ⟨w, wZ⟩), rfl, fun hc => hc⟩

theorem exists_nonRest {Z P Q : Finset object.Vertex} {w : object.Vertex}
    (h : ¬ InteriorOut object Z Q w) :
    ∃ c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex,
      gdec Z P Q c = w ∧ ¬ IsRest Z P Q c := by
  by_cases wZ : w ∈ Z
  · by_cases hb : w ∈ SupportAtom.cutBoundary object Z
    · exact ⟨.inl ⟨w, hb⟩, rfl, fun hc => hc⟩
    · have wQ : w ∈ Q := by
        by_contra wQ
        exact h ⟨wZ, hb, wQ⟩
      exact ⟨.inr (.inl (.inr ⟨w, wZ, hb, wQ⟩)), rfl, fun hc => hc⟩
  · exact ⟨.inr (.inr ⟨w, wZ⟩), rfl, fun hc => hc⟩

theorem exists_copy {Z P Q : Finset object.Vertex} {w : object.Vertex}
    (h : InteriorIn object Z Q w) :
    ∃ c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex,
      gdec Z P Q c = w ∧ IsCopy Z P Q c :=
  ⟨.inr (.inl (.inr ⟨w, h⟩)), rfl, trivial⟩

theorem injOn_nonCopy (Z P Q : Finset object.Vertex) :
    Set.InjOn (gdec Z P Q)
      {c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex |
        ¬ IsCopy Z P Q c} := by
  intro c hc c' hc' h
  rcases gdec_eq_cases Z P Q h with e | ⟨_, k⟩ | ⟨k, _⟩
  · exact e
  · exact absurd k hc'
  · exact absurd k hc

theorem injOn_nonRest (Z P Q : Finset object.Vertex) :
    Set.InjOn (gdec Z P Q)
      {c : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex |
        ¬ IsRest Z P Q c} := by
  intro c hc c' hc' h
  rcases gdec_eq_cases Z P Q h with e | ⟨k, _⟩ | ⟨_, k⟩
  · exact e
  · exact absurd k hc
  · exact absurd k hc'

/-- **A rest vertex has degree `restDeg`** in the glued swap. -/
theorem glue_degree_rest (Z P Q : Finset object.Vertex) (x : RestInternal object Z P) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).degree
        (.inr (.inl (.inl x))) = restDeg Z P x.1 := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have sub : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).graph.neighborSet
      (.inr (.inl (.inl x))) ⊆ {c | ¬ IsCopy Z P Q c} := by
    intro c hc
    have := ((glue_swap_adj_iff Z P Q _ c).1 hc).2
    rcases c with b | ((x' | y') | o) <;> first | exact fun k => k | exact absurd trivial this
  rw [← Set.InjOn.ncard_image ((injOn_nonCopy Z P Q).mono sub)]
  unfold restDeg
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (glue_swap_adj_iff Z P Q _ c).1 hc
    refine ⟨hc'.1, ?_⟩
    rintro ⟨wZ, wb, wP⟩
    rcases c with b | ((x' | y') | o)
    · exact wb b.2
    · exact x'.2.2.2 wP
    · exact hc'.2 trivial
    · exact o.2 wZ
  · rintro ⟨adj, nin⟩
    obtain ⟨c, rfl, nc⟩ := exists_nonCopy (Q := Q) nin
    refine ⟨c, ?_, rfl⟩
    refine (glue_swap_adj_iff Z P Q _ c).2 ⟨adj, ?_⟩
    rcases c with b | ((x' | y') | o) <;> first | exact fun k => k | exact absurd trivial nc

/-- **A copy vertex has degree `copyDeg`** in the glued swap. -/
theorem glue_degree_copy (Z P Q : Finset object.Vertex) (y : TransplantInternal object Z Q) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).degree
        (.inr (.inl (.inr y))) = copyDeg Z Q y.1 := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have sub : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).graph.neighborSet
      (.inr (.inl (.inr y))) ⊆ {c | ¬ IsRest Z P Q c} := by
    intro c hc
    have := ((glue_swap_adj_iff Z P Q _ c).1 hc).2
    rcases c with b | ((x' | y') | o) <;> first | exact fun k => k | exact absurd trivial this
  rw [← Set.InjOn.ncard_image ((injOn_nonRest Z P Q).mono sub)]
  unfold copyDeg
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (glue_swap_adj_iff Z P Q _ c).1 hc
    refine ⟨hc'.1, ?_⟩
    rintro ⟨wZ, wb, wQ⟩
    rcases c with b | ((x' | y') | o)
    · exact wb b.2
    · exact hc'.2 trivial
    · exact wQ y'.2.2.2
    · exact o.2 wZ
  · rintro ⟨adj, nin⟩
    obtain ⟨c, rfl, nc⟩ := exists_nonRest (P := P) nin
    refine ⟨c, ?_, rfl⟩
    refine (glue_swap_adj_iff Z P Q _ c).2 ⟨adj, ?_⟩
    rcases c with b | ((x' | y') | o) <;> first | exact fun k => k | exact absurd trivial nc

/-- **An outside vertex has its degree in `G`** in the glued swap. -/
theorem glue_degree_outside (Z P Q : Finset object.Vertex) (o : SupportAtom.OutsideInternal object Z) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).degree (.inr (.inr o)) =
      object.degree o.1 := by
  rw [FiniteObject.degree_eq_ncard_neighborSet, FiniteObject.degree_eq_ncard_neighborSet]
  have sub : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).graph.neighborSet
      (.inr (.inr o)) ⊆ {c | ¬ IsCopy Z P Q c} := by
    intro c hc
    have := ((glue_swap_adj_iff Z P Q _ c).1 hc).1
    rcases c with b | ((x' | y') | o')
    · exact fun k => k
    · exact fun k => k
    · exact absurd (cut_of_adj_outside y'.2.1 this.symm o.2) y'.2.2.1
    · exact fun k => k
  rw [← Set.InjOn.ncard_image ((injOn_nonCopy Z P Q).mono sub)]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ((glue_swap_adj_iff Z P Q _ c).1 hc).1
  · intro adj
    have nin : ¬ InteriorIn object Z P w := fun h => by
      have := cut_of_adj_outside h.1 adj.symm o.2
      exact h.2.1 this
    obtain ⟨c, rfl, nc⟩ := exists_nonCopy (Q := Q) nin
    refine ⟨c, ?_, rfl⟩
    refine (glue_swap_adj_iff Z P Q _ c).2 ⟨adj, ?_⟩
    exact fun k => k

/-- **A boundary vertex has degree `bdryDeg`** in the glued swap. -/
theorem glue_degree_boundary (Z P Q : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).degree (.inl b) =
      bdryDeg Z P Q b.1 := by
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  set N := (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).graph.neighborSet
    (.inl b) with hN
  haveI : Finite (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex := by
    letI := (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).vertices
    infer_instance
  have finN : N.Finite := Set.toFinite _
  have split : N = {c ∈ N | ¬ IsCopy Z P Q c} ∪ {c ∈ N | IsCopy Z P Q c} := by
    ext c; by_cases h : IsCopy Z P Q c <;> simp [h]
  have disj : Disjoint {c ∈ N | ¬ IsCopy Z P Q c} {c ∈ N | IsCopy Z P Q c} :=
    Set.disjoint_left.2 fun c h1 h2 => h1.2 h2.2
  have cardSplit : N.ncard = {c ∈ N | ¬ IsCopy Z P Q c}.ncard +
      {c ∈ N | IsCopy Z P Q c}.ncard := by
    conv_lhs => rw [split]
    exact Set.ncard_union_eq disj (finN.subset fun c h => h.1) (finN.subset fun c h => h.1)
  rw [cardSplit]
  unfold bdryDeg
  congr 1
  · rw [← Set.InjOn.ncard_image ((injOn_nonCopy Z P Q).mono fun c hc => hc.2)]
    congr 1
    ext w
    constructor
    · rintro ⟨c, ⟨hc, nc⟩, rfl⟩
      have hc' := (glue_swap_adj_iff Z P Q _ c).1 hc
      refine ⟨hc'.1, ?_⟩
      rintro ⟨wZ, wb, wP⟩
      rcases c with b' | ((x' | y') | o)
      · exact wb b'.2
      · exact x'.2.2.2 wP
      · exact nc trivial
      · exact o.2 wZ
    · rintro ⟨adj, nin⟩
      obtain ⟨c, rfl, nc⟩ := exists_nonCopy (Q := Q) nin
      exact ⟨c, ⟨(glue_swap_adj_iff Z P Q _ c).2 ⟨adj, fun k => k⟩, nc⟩, rfl⟩
  · have hsub : {c ∈ N | IsCopy Z P Q c} ⊆ {c | ¬ IsRest Z P Q c} := by
      intro c hc
      rcases c with b' | ((x' | y') | o)
      · exact fun k => k
      · exact absurd hc.2 (fun k => k)
      · exact fun k => k
      · exact fun k => k
    rw [← Set.InjOn.ncard_image ((injOn_nonRest Z P Q).mono hsub)]
    congr 1
    ext w
    constructor
    · rintro ⟨c, ⟨hc, cc⟩, rfl⟩
      have hc' := (glue_swap_adj_iff Z P Q _ c).1 hc
      refine ⟨hc'.1, ?_⟩
      rcases c with b' | ((x' | y') | o)
      · exact absurd cc (fun k => k)
      · exact absurd cc (fun k => k)
      · exact y'.2
      · exact absurd cc (fun k => k)
    · rintro ⟨adj, inQ⟩
      obtain ⟨c, rfl, cc⟩ := exists_copy (P := P) inQ
      exact ⟨c, ⟨(glue_swap_adj_iff Z P Q _ c).2 ⟨adj, fun k => k⟩, cc⟩, rfl⟩


/-! ### (ii) The baseline, exactly -/

variable (object) in
/-- **A vertex of `G`, read in one of its four roles, whose degree in the glued
swap is below `threshold`**: as a rest vertex, as a copy vertex, as a boundary
vertex of `Z`, or as an outside vertex. -/
def SwapDeficient (threshold : Nat) (Z P Q : Finset object.Vertex) (v : object.Vertex) : Prop :=
  (InteriorOut object Z P v ∧ restDeg Z P v < threshold) ∨
    (InteriorIn object Z Q v ∧ copyDeg Z Q v < threshold) ∨
    (v ∈ SupportAtom.cutBoundary object Z ∧ bdryDeg Z P Q v < threshold) ∨
    (v ∉ Z ∧ object.degree v < threshold)

variable (object) in
/-- **The degree condition (ii) of the swap, as a predicate on `G`.** -/
def SwapDegreeCondition (threshold : Nat) (Z P Q : Finset object.Vertex) : Prop :=
  ∀ v, ¬ SwapDeficient object threshold Z P Q v

/-- **(ii) The glued swap keeps the baseline exactly when the degree condition
holds on `G`** (when the glued swap has a vertex). -/
theorem swap_baseline_iff {threshold : Nat} (Z P Q : Finset object.Vertex)
    (hne : Nonempty (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex) :
    MinimumDegreeAtLeast threshold
        (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)) ↔
      SwapDegreeCondition object threshold Z P Q := by
  constructor
  · intro base v hdef
    have low : ∀ a : (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex,
        threshold ≤ (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).degree a :=
      fun a => le_trans base (FiniteObject.minDegree_le_degree _ a)
    rcases hdef with ⟨hv, lt⟩ | ⟨hv, lt⟩ | ⟨hv, lt⟩ | ⟨hv, lt⟩
    · have := low (.inr (.inl (.inl ⟨v, hv⟩)))
      rw [glue_degree_rest] at this
      exact absurd lt (Nat.not_lt.2 this)
    · have := low (.inr (.inl (.inr ⟨v, hv⟩)))
      rw [glue_degree_copy] at this
      exact absurd lt (Nat.not_lt.2 this)
    · have := low (.inl ⟨v, hv⟩)
      rw [glue_degree_boundary] at this
      exact absurd lt (Nat.not_lt.2 this)
    · have := low (.inr (.inr ⟨v, hv⟩))
      rw [glue_degree_outside] at this
      exact absurd lt (Nat.not_lt.2 this)
  · intro cond
    haveI := hne
    unfold MinimumDegreeAtLeast
    apply FiniteObject.le_minDegree_of_forall_le_degree
    intro a
    by_contra low
    have lt := Nat.lt_of_not_le low
    rcases a with b | ((x | y) | o)
    · rw [glue_degree_boundary] at lt
      exact cond b.1 (Or.inr (Or.inr (Or.inl ⟨b.2, lt⟩)))
    · rw [glue_degree_rest] at lt
      exact cond x.1 (Or.inl ⟨x.2, lt⟩)
    · rw [glue_degree_copy] at lt
      exact cond y.1 (Or.inr (Or.inl ⟨y.2, lt⟩))
    · rw [glue_degree_outside] at lt
      exact cond o.1 (Or.inr (Or.inr (Or.inr ⟨o.2, lt⟩)))

variable (object) in
/-- **The canonical exceptional vertex of the swap**: the first vertex in `G`'s
fixed vertex order that is deficient in some role; `none` when there is none. -/
noncomputable def swapDeficit (threshold : Nat) (Z P Q : Finset object.Vertex) :
    Option object.Vertex := by
  classical
  exact object.orderedVertices.find? fun v => decide (SwapDeficient object threshold Z P Q v)

theorem swapDeficit_spec {threshold : Nat} {Z P Q : Finset object.Vertex} {v : object.Vertex} :
    swapDeficit object threshold Z P Q = some v ↔
      SwapDeficient object threshold Z P Q v ∧
        ∃ before after, object.orderedVertices = before ++ v :: after ∧
          ∀ a ∈ before, ¬ SwapDeficient object threshold Z P Q a := by
  classical
  unfold swapDeficit
  rw [List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]

theorem swapDeficit_isSome_iff {threshold : Nat} {Z P Q : Finset object.Vertex} :
    (swapDeficit object threshold Z P Q).isSome ↔
      ∃ v, SwapDeficient object threshold Z P Q v := by
  classical
  unfold swapDeficit
  rw [List.find?_isSome]
  simp only [decide_eq_true_eq, FiniteObject.mem_orderedVertices, true_and]

theorem swapDeficit_eq_none_iff {threshold : Nat} {Z P Q : Finset object.Vertex} :
    swapDeficit object threshold Z P Q = none ↔ SwapDegreeCondition object threshold Z P Q := by
  constructor
  · intro h v hv
    have := (swapDeficit_isSome_iff (object := object)).2 ⟨v, hv⟩
    rw [h] at this
    exact absurd this (by simp)
  · intro cond
    cases h : swapDeficit object threshold Z P Q with
    | none => rfl
    | some v => exact absurd (((swapDeficit_spec (object := object)).1 h).1) (cond v)

end Glue


/-! ## (i) The boundary profile, exactly -/

section Profile

variable {object}

/-- A vertex of the swap piece is a copy vertex. -/
def IsCopyP {Z P Q : Finset object.Vertex} :
    (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q → Prop
  | .inr (.inr _) => True
  | _ => False

theorem injOn_swapDecode_nonCopy (Z P Q : Finset object.Vertex) :
    Set.InjOn (swapDecode object Z P Q)
      {c : (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q |
        ¬ IsCopyP c} := by
  intro a ha c hc h
  rcases a with b | (x | y) <;> rcases c with b' | (x' | y') <;> simp only [swapDecode] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd (show x'.1 ∈ SupportAtom.cutBoundary object Z from h ▸ b.2) x'.2.2.1
  · exact absurd trivial hc
  · exact absurd (show x.1 ∈ SupportAtom.cutBoundary object Z from h.symm ▸ b'.2) x.2.2.1
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext h)
  · exact absurd trivial hc
  · exact absurd trivial ha
  · exact absurd trivial ha
  · exact absurd trivial ha

theorem injOn_swapDecode_copy (Z P Q : Finset object.Vertex) :
    Set.InjOn (swapDecode object Z P Q)
      {c : (SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q |
        IsCopyP c} := by
  intro a ha c hc h
  rcases a with b | (x | y) <;> rcases c with b' | (x' | y') <;> simp only [swapDecode] at h
  all_goals first
    | exact absurd ha (fun k => k)
    | exact absurd hc (fun k => k)
    | exact congrArg (fun y => Sum.inr (Sum.inr y)) (Subtype.ext h)

/-- **The boundary degree of the swap piece at `b`.** -/
theorem swapPiece_boundaryDegree (Z P Q : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    (swapPiece object Z P Q).boundaryDegree b =
      {w | object.graph.Adj b.1 w ∧ w ∈ Z ∧ ¬ InteriorIn object Z P w}.ncard +
        {w | object.graph.Adj b.1 w ∧ InteriorIn object Z Q w}.ncard := by
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  haveI : Finite ((SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q) := by
    letI := (swapPiece object Z P Q).pack.vertices
    exact (inferInstance : Finite (swapPiece object Z P Q).pack.Vertex)
  change ((swapGraph object Z P Q).neighborSet (.inl b)).ncard = _
  set N := (swapGraph object Z P Q).neighborSet (.inl b) with hN
  have finN : N.Finite := Set.toFinite _
  have split : N = {c ∈ N | ¬ IsCopyP c} ∪ {c ∈ N | IsCopyP c} := by
    ext c; by_cases h : IsCopyP c <;> simp [h]
  have disj : Disjoint {c ∈ N | ¬ IsCopyP c} {c ∈ N | IsCopyP c} :=
    Set.disjoint_left.2 fun c h1 h2 => h1.2 h2.2
  have cardSplit : N.ncard = {c ∈ N | ¬ IsCopyP c}.ncard + {c ∈ N | IsCopyP c}.ncard := by
    conv_lhs => rw [split]
    exact Set.ncard_union_eq disj (finN.subset fun c h => h.1) (finN.subset fun c h => h.1)
  rw [cardSplit]
  congr 1
  · rw [← Set.InjOn.ncard_image ((injOn_swapDecode_nonCopy Z P Q).mono fun c hc => hc.2)]
    congr 1
    ext w
    constructor
    · rintro ⟨c, ⟨hc, nc⟩, rfl⟩
      have hc' : object.graph.Adj b.1 (swapDecode object Z P Q c) := hc.1
      refine ⟨hc', ?_, ?_⟩
      · rcases c with b' | (x' | y')
        · exact cutBoundary_subset b'.2
        · exact x'.2.1
        · exact absurd trivial nc
      · rintro ⟨wZ, wb, wP⟩
        rcases c with b' | (x' | y')
        · exact wb b'.2
        · exact x'.2.2.2 wP
        · exact absurd trivial nc
    · rintro ⟨adj, wZ, nin⟩
      by_cases wb : w ∈ SupportAtom.cutBoundary object Z
      · exact ⟨.inl ⟨w, wb⟩, ⟨⟨adj, fun k => k⟩, fun k => k⟩, rfl⟩
      · have wP : w ∉ P := fun wP => nin ⟨wZ, wb, wP⟩
        exact ⟨.inr (.inl ⟨w, wZ, wb, wP⟩), ⟨⟨adj, fun k => k⟩, fun k => k⟩, rfl⟩
  · rw [← Set.InjOn.ncard_image ((injOn_swapDecode_copy Z P Q).mono fun c hc => hc.2)]
    congr 1
    ext w
    constructor
    · rintro ⟨c, ⟨hc, cc⟩, rfl⟩
      rcases c with b' | (x' | y')
      · exact absurd cc (fun k => k)
      · exact absurd cc (fun k => k)
      · exact ⟨hc.1, y'.2⟩
    · rintro ⟨adj, inQ⟩
      exact ⟨.inr (.inr ⟨w, inQ⟩), ⟨⟨adj, fun k => k⟩, trivial⟩, rfl⟩

/-- The boundary degree of `G`'s own piece at `b` is its `G`-degree into `Z`. -/
theorem piece_boundaryDegree (Z : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex) :
    (SupportAtom.piece object Z).boundaryDegree b =
      {w | object.graph.Adj b.1 w ∧ w ∈ Z}.ncard := by
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have := ncard_neighborSet_comap object.graph (SupportAtom.pieceDecode object Z)
    (pieceDecode_injective Z) (.inl b)
  refine this.trans ?_
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, range_pieceDecode]
  rfl

/-- **(i) The swap has the boundary profile of `G[Z]` exactly when every boundary
vertex of `Z` has as many interior neighbours in `Q` as in `P`.** -/
theorem swapPiece_profile_eq_iff (Z P Q : Finset object.Vertex) :
    (swapPiece object Z P Q).boundaryDegreeProfile =
        (SupportAtom.piece object Z).boundaryDegreeProfile ↔
      ∀ b : (SupportAtom.boundary object Z).Vertex,
        {w | object.graph.Adj b.1 w ∧ InteriorIn object Z Q w}.ncard =
          {w | object.graph.Adj b.1 w ∧ InteriorIn object Z P w}.ncard := by
  haveI : Finite object.Vertex := finite_vertex
  have key : ∀ b : (SupportAtom.boundary object Z).Vertex,
      {w | object.graph.Adj b.1 w ∧ w ∈ Z}.ncard =
        {w | object.graph.Adj b.1 w ∧ w ∈ Z ∧ ¬ InteriorIn object Z P w}.ncard +
          {w | object.graph.Adj b.1 w ∧ InteriorIn object Z P w}.ncard := by
    intro b
    rw [← Set.ncard_union_eq]
    · congr 1
      ext w
      constructor
      · rintro ⟨adj, wZ⟩
        by_cases h : InteriorIn object Z P w
        · exact Or.inr ⟨adj, h⟩
        · exact Or.inl ⟨adj, wZ, h⟩
      · rintro (⟨adj, wZ, -⟩ | ⟨adj, h⟩)
        · exact ⟨adj, wZ⟩
        · exact ⟨adj, h.1⟩
    · exact Set.disjoint_left.2 fun w h1 h2 => h1.2.2 h2.2
  constructor
  · intro eq b
    have e := congrFun eq b
    change (swapPiece object Z P Q).boundaryDegree b = (SupportAtom.piece object Z).boundaryDegree b
      at e
    rw [swapPiece_boundaryDegree, piece_boundaryDegree, key] at e
    omega
  · intro h
    funext b
    change (swapPiece object Z P Q).boundaryDegree b = (SupportAtom.piece object Z).boundaryDegree b
    rw [swapPiece_boundaryDegree, piece_boundaryDegree, key, h b]

end Profile


/-! ## (iv) Linkage inclusion, and (iii) the size relation from minimality -/

section Linkage

variable {object}

/-- A linkage of the swap piece that uses a vertex of `G` both as a rest vertex
and as its copy. -/
def LinkageDoubleUse {Z P Q : Finset object.Vertex}
    (L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q)) :
    Prop :=
  ∃ (x : RestInternal object Z P) (y : TransplantInternal object Z Q), x.1 = y.1 ∧
    (∃ a, L.Adj (.inr (.inl x)) a) ∧ (∃ a, L.Adj (.inr (.inr y)) a)

/-- **Linkage inclusion of the swap, exactly**: it holds, or some linkage of the
swap piece uses a vertex of `int(Z) ∩ Q ∖ P` both as itself and as its copy. -/
theorem swap_linkage_dichotomy (Z P Q : Finset object.Vertex) :
    LinkageIncluded (swapPiece object Z P Q) ∨
      ∃ L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q),
        IsLinkage (swapPiece object Z P Q) L ∧ LinkageDoubleUse L := by
  by_cases inc : LinkageIncluded (swapPiece object Z P Q)
  · exact Or.inl inc
  · right
    unfold LinkageIncluded at inc
    push Not at inc
    obtain ⟨L, hL, hnot⟩ := inc
    refine ⟨L, hL, ?_⟩
    by_contra hnone
    apply hnot
    refine ⟨fun x => swapDecode object Z P Q (.inr x), ?_, ?_, ?_⟩
    · intro x a _
      rcases x with x | y
      · exact ⟨x.2.1, x.2.2.1⟩
      · exact ⟨y.2.1, y.2.2.1⟩
    · intro x y a c hxa hyc h
      rcases x with x | x' <;> rcases y with y | y'
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact absurd ⟨x, y', h, ⟨a, hxa⟩, ⟨c, hyc⟩⟩ hnone
      · exact absurd ⟨y, x', h.symm, ⟨c, hyc⟩, ⟨a, hxa⟩⟩ hnone
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro a c hac
      have := (hL.le hac).1
      rcases a with b | x <;> rcases c with b' | y <;> exact this

/-- If every interior vertex of `Q` lies in `P`, the swap piece is linkage-included. -/
theorem swap_linkageIncluded_of_subset {Z P Q : Finset object.Vertex}
    (sub : ∀ v, InteriorIn object Z Q v → v ∈ P) :
    LinkageIncluded (swapPiece object Z P Q) := by
  rcases swap_linkage_dichotomy (object := object) Z P Q with inc | ⟨L, -, x, y, e, -, -⟩
  · exact inc
  · exact absurd (e ▸ sub y.1 y.2) x.2.2.2

/-- **Size from minimality (iii)**: a linkage-included swap whose gluing into
`G − Z` keeps the baseline satisfies `|int Z ∩ P| ≤ |int Z ∩ Q|`. -/
theorem swap_size_le {LengthOK : Nat → Prop} {threshold : Nat}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (Z P Q : Finset object.Vertex)
    (baseline : MinimumDegreeAtLeast threshold
      (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)))
    (included : LinkageIncluded (swapPiece object Z P Q)) :
    intCount Z P ≤ intCount Z Q := by
  have le := internalVertexCount_le_of_minimal avoids minimal baseline included
  have eq := swapPiece_internalVertexCount (object := object) Z P Q
  omega

/-- A linkage-included swap piece glues into `G − Z` without a target cycle. -/
theorem swap_not_target {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object) (Z P Q : Finset object.Vertex)
    (included : LinkageIncluded (swapPiece object Z P Q)) :
    ¬ HasCycleWithLength LengthOK
      (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)) :=
  not_target_of_linkageIncluded avoids included

/-- **Descent on the swapped object (E07)**: a linkage-included swap that keeps the
baseline is not lexicographically smaller than `G` (fewer vertices, or the same
vertices and fewer edges): minimality of `G`, with the target-freeness of the
swap. -/
theorem swap_not_lexSmaller {LengthOK : Nat → Prop} {threshold : Nat}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (Z P Q : Finset object.Vertex)
    (baseline : MinimumDegreeAtLeast threshold
      (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)))
    (included : LinkageIncluded (swapPiece object Z P Q)) :
    ¬ (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).LexicographicallySmaller
      object :=
  fun lex => swap_not_target avoids Z P Q included (minimal _ lex baseline)

/-- **The swap, exactly** (a minimal target-avoiding `G` with the baseline, the
glued swap having a vertex).  One of:

* the swap is valid: no vertex of `G` is deficient in any role, the piece is
  linkage-included, and `|int Z ∩ P| ≤ |int Z ∩ Q|`;
* G's canonical exceptional vertex `swapDeficit` exists, lies in `Z`, and is
  deficient in one of the roles rest / copy / boundary;
* some linkage of the swap piece uses a vertex of `G` both as itself and as its
  copy. -/
theorem swap_exact {LengthOK : Nat → Prop} {threshold : Nat}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (base : MinimumDegreeAtLeast threshold object)
    (Z P Q : Finset object.Vertex)
    (hv : ∃ v, ¬ InteriorIn object Z P v ∨ InteriorIn object Z Q v) :
    (swapDeficit object threshold Z P Q = none ∧
        LinkageIncluded (swapPiece object Z P Q) ∧ intCount Z P ≤ intCount Z Q) ∨
      (∃ v, swapDeficit object threshold Z P Q = some v ∧ v ∈ Z ∧
        SwapDeficient object threshold Z P Q v) ∨
      ∃ L : SimpleGraph ((SupportAtom.boundary object Z).Vertex ⊕ SwapInternal object Z P Q),
        IsLinkage (swapPiece object Z P Q) L ∧ LinkageDoubleUse L := by
  have hne : Nonempty (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex := by
    obtain ⟨v, hv⟩ := hv
    rcases hv with h | h
    · obtain ⟨c, -, -⟩ := exists_nonCopy (Q := Q) h
      exact ⟨c⟩
    · obtain ⟨c, -, -⟩ := exists_copy (P := P) h
      exact ⟨c⟩
  rcases swap_linkage_dichotomy (object := object) Z P Q with inc | witness
  · cases h : swapDeficit object threshold Z P Q with
    | none =>
        left
        have cond := (swapDeficit_eq_none_iff (object := object)).1 h
        have baseline := (swap_baseline_iff Z P Q hne).2 cond
        exact ⟨rfl, inc, swap_size_le avoids minimal Z P Q baseline inc⟩
    | some v =>
        right; left
        have hdef := ((swapDeficit_spec (object := object)).1 h).1
        refine ⟨v, rfl, ?_, hdef⟩
        rcases hdef with ⟨hv', -⟩ | ⟨hv', -⟩ | ⟨hv', -⟩ | ⟨hv', lt⟩
        · exact hv'.1
        · exact hv'.1
        · exact cutBoundary_subset hv'
        · exact absurd lt (Nat.not_lt.2 (le_trans base (object.minDegree_le_degree v)))
  · right; right; exact witness

end Linkage


/-! ## The contact bijection, fixed by `G`'s vertex order -/

section Rank

variable {object}

/-- The rank of a vertex in `G`'s fixed vertex order. -/
noncomputable def rank (v : object.Vertex) : Nat := by
  classical
  exact object.orderedVertices.idxOf v

theorem rank_injective : Function.Injective (rank (object := object)) := by
  classical
  intro a c h
  have ha : a ∈ object.orderedVertices := FiniteObject.mem_orderedVertices _ _
  have hc : c ∈ object.orderedVertices := FiniteObject.mem_orderedVertices _ _
  have hne : ∀ x : object.Vertex, x ∈ object.orderedVertices → object.orderedVertices.idxOf x
      < object.orderedVertices.length := fun x hx => List.idxOf_lt_length_iff.2 hx
  have e1 : object.orderedVertices[object.orderedVertices.idxOf a]'(hne a ha) = a :=
    List.getElem_idxOf (hne a ha)
  have e2 : object.orderedVertices[object.orderedVertices.idxOf c]'(hne c hc) = c :=
    List.getElem_idxOf (hne c hc)
  have hh : object.orderedVertices.idxOf a = object.orderedVertices.idxOf c := h
  rw [← e1, ← e2]
  simp only [hh]

/-- `G`'s vertex order as a linear order on its vertices. -/
@[reducible] noncomputable def rankOrder (object : FiniteObject.{u}) : LinearOrder object.Vertex :=
  LinearOrder.lift' rank rank_injective

/-- **The canonical bijection between two contact sets of equal size**: the
`k`-th vertex of the first, in `G`'s vertex order, goes to the `k`-th vertex of
the second.  This is the equal-count contact bijection (`Transplant.contactEquiv`)
with its choice fixed by `G.orderedVertices`. -/
noncomputable def orderEquiv (S T : Set object.Vertex) (h : S.ncard = T.ncard) : S ≃ T := by
  classical
  haveI : Finite object.Vertex := finite_vertex
  letI : LinearOrder object.Vertex := rankOrder object
  have hS : S.Finite := Set.toFinite S
  have hT : T.Finite := Set.toFinite T
  have cS : hS.toFinset.card = S.ncard := (Set.ncard_eq_toFinset_card S hS).symm
  have cT : hT.toFinset.card = S.ncard := by rw [h]; exact (Set.ncard_eq_toFinset_card T hT).symm
  exact
    (Equiv.subtypeEquivRight fun x => (Set.Finite.mem_toFinset hS).symm).trans
      (((hS.toFinset.orderIsoOfFin cS).symm.toEquiv).trans
        ((hT.toFinset.orderIsoOfFin cT).toEquiv.trans
          (Equiv.subtypeEquivRight fun x => Set.Finite.mem_toFinset hT)))


/-- **Attachment through the bijection.**  When a boundary vertex `b` has as many
interior neighbours in `P` as in `Q` (the profile identity), the copy vertices
the swap piece attaches to `b` are exactly the images, under the canonical
order bijection, of `b`'s interior neighbours in `P`: each replaced stub goes to
the copy of the `k`-th `Q`-neighbour, `k` its rank among the `P`-neighbours. -/
theorem swap_attachment (Z P Q : Finset object.Vertex)
    (b : (SupportAtom.boundary object Z).Vertex)
    (hc : {w | object.graph.Adj b.1 w ∧ InteriorIn object Z P w}.ncard =
      {w | object.graph.Adj b.1 w ∧ InteriorIn object Z Q w}.ncard)
    (y : TransplantInternal object Z Q) :
    (swapPiece object Z P Q).graph.Adj (.inl b) (.inr (.inr y)) ↔
      ∃ w : {w | object.graph.Adj b.1 w ∧ InteriorIn object Z P w},
        ((orderEquiv _ _ hc) w).1 = y.1 := by
  constructor
  · intro h
    have adj : object.graph.Adj b.1 y.1 := h.1
    refine ⟨(orderEquiv _ _ hc).symm ⟨y.1, adj, y.2⟩, ?_⟩
    exact congrArg Subtype.val ((orderEquiv _ _ hc).apply_symm_apply ⟨y.1, adj, y.2⟩)
  · rintro ⟨w, hw⟩
    have mem := ((orderEquiv _ _ hc) w).2
    rw [hw] at mem
    exact ⟨mem.1, fun k => k⟩

end Rank


/-! ## (B07) The response of the swapped object: an accepted cycle uses a vertex twice -/

section Response

variable {object}

/-- **A cycle mapped by an edge-preserving map that is injective on the cycle is a
cycle of `G` of the same length.** -/
theorem cycle_map_of_injOn {H : FiniteObject.{u}} (ψ : H.Vertex → object.Vertex)
    {LengthOK : Nat → Prop} (cert : CycleCertificate H LengthOK)
    (edgeOK : ∀ a c, s(a, c) ∈ cert.walk.edges → object.graph.Adj (ψ a) (ψ c))
    (injS : ∀ a c, a ∈ cert.walk.support → c ∈ cert.walk.support → ψ a = ψ c → a = c) :
    Nonempty (CycleCertificate object LengthOK) := by
  classical
  obtain ⟨v, C, hC, hlen⟩ := cert
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

/-- **The response of the swapped object.**  On a target-avoiding `G`, every
accepted cycle of `glue (swapPiece) (G − Z)` passes through some vertex `v` of
`int(Z) ∩ Q ∖ P` both as itself (a rest vertex) and as its copy: otherwise
`gdec` is injective on the cycle and carries it to an accepted cycle of `G`. -/
theorem swap_cycle_double_use {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object) (Z P Q : Finset object.Vertex)
    (cert : CycleCertificate (glue (swapPiece object Z P Q) (SupportAtom.outside object Z))
      LengthOK) :
    ∃ (x : RestInternal object Z P) (y : TransplantInternal object Z Q), x.1 = y.1 ∧
      (Sum.inr (Sum.inl (Sum.inl x)) :
          (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex) ∈
        cert.walk.support ∧
      (Sum.inr (Sum.inl (Sum.inr y)) :
          (glue (swapPiece object Z P Q) (SupportAtom.outside object Z)).Vertex) ∈
        cert.walk.support := by
  by_contra none
  push Not at none
  apply avoids
  refine cycle_map_of_injOn (gdec Z P Q) cert ?_ ?_
  · intro a c hac
    exact ((glue_swap_adj_iff Z P Q a c).1 (cert.walk.adj_of_mem_edges hac)).1
  · intro a c ha hc h
    rcases gdec_eq_cases Z P Q h with e | ⟨ra, cc⟩ | ⟨ca, rc⟩
    · exact e
    · exfalso
      rcases a with b | ((x | y) | o)
      · exact absurd ra (fun k => k)
      · rcases c with b' | ((x' | y') | o')
        · exact absurd cc (fun k => k)
        · exact absurd cc (fun k => k)
        · exact none x y' (by simpa [gdec] using h) ha hc
        · exact absurd cc (fun k => k)
      · exact absurd ra (fun k => k)
      · exact absurd ra (fun k => k)
    · exfalso
      rcases a with b | ((x | y) | o)
      · exact absurd ca (fun k => k)
      · exact absurd ca (fun k => k)
      · rcases c with b' | ((x' | y') | o')
        · exact absurd rc (fun k => k)
        · exact none x' y (by simpa [gdec] using h.symm) hc ha
        · exact absurd rc (fun k => k)
        · exact absurd rc (fun k => k)
      · exact absurd ca (fun k => k)

end Response

end Hypostructure.Graph.RerouteSwap
