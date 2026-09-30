## hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:115-153
```lean

/-- `(P, N)` is `(A, B)` or `(B, A)`. -/
abbrev SparseTargetDefectWitness.Orientation (w : SparseTargetDefectWitness data object)
    (P N : Finset object.Vertex) : Prop :=
  (P = sparseDeclaredSupport data object w.first ∧
      N = sparseDeclaredSupport data object w.second) ∨
    (P = sparseDeclaredSupport data object w.second ∧
      N = sparseDeclaredSupport data object w.first)

/-- The positive reading `P` at `O` against the negative `N`. -/
abbrev SparseTargetDefectWitness.Separates (w : SparseTargetDefectWitness data object)
    (P N : Finset object.Vertex) : Prop :=
  Graph.HasCycleWithLength data.LengthOK
      (Graph.glue (SupportAtom.retainedPiece object w.support P) w.outside) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK
      (Graph.glue (SupportAtom.retainedPiece object w.support N) w.outside)

/-- Every positive cycle of `glue ret_P O` traverses a private edge `xy` of
`P` (`x, y ∈ P`, `y ∉ N`) whose non-`N` end `y` is internal to `Z`. -/
abbrev SparseTargetDefectWitness.CyclesUsePrivateEdge
    (w : SparseTargetDefectWitness data object) (P N : Finset object.Vertex) : Prop :=
  ∀ c : Graph.CycleCertificate
      (Graph.glue (SupportAtom.retainedPiece object w.support P) w.outside) data.LengthOK,
    ∃ pl pr : (SupportAtom.boundary object w.support).Vertex ⊕
        SupportAtom.PieceInternal object w.support,
      s(Graph.pieceEmbedding (SupportAtom.retainedPiece object w.support P) w.outside pl,
        Graph.pieceEmbedding (SupportAtom.retainedPiece object w.support P)
          w.outside pr) ∈ c.walk.edges ∧
      object.graph.Adj (SupportAtom.pieceDecode object w.support pl)
        (SupportAtom.pieceDecode object w.support pr) ∧
      SupportAtom.pieceDecode object w.support pl ∈ P ∧
      SupportAtom.pieceDecode object w.support pr ∈ P ∧
      SupportAtom.pieceDecode object w.support pr ∉ N ∧
      SupportAtom.pieceDecode object w.support pr ∉ SupportAtom.cutBoundary object w.support

/-- Arm (ii) of the spectrum split: every accepted cycle of `glue ret_P O`
meets three distinct labels. -/
abbrev SparseTargetDefectWitness.CyclesMeetThreeLabels
    (w : SparseTargetDefectWitness data object) (P : Finset object.Vertex) : Prop :=
```

## hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:190-208
```lean
/-- `WitnessReadingCountsStatement` at one target-defect witness `w`. -/
noncomputable abbrev WitnessReadingCountsAtWitness {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  (∀ b, w.count w.first b = w.count w.second b) ∧
  (∀ b : (SupportAtom.boundary object w.support).Vertex,
    b.1 ∈ sparseDeclaredSupport data object w.first →
    ∀ x ∈ sparseDeclaredSupport data object w.first, object.graph.Adj b.1 x →
    b.1 ∈ sparseDeclaredSupport data object w.second) ∧
  (∀ b : (SupportAtom.boundary object w.support).Vertex,
    b.1 ∈ sparseDeclaredSupport data object w.second →
    ∀ x ∈ sparseDeclaredSupport data object w.second, object.graph.Adj b.1 x →
    b.1 ∈ sparseDeclaredSupport data object w.first)

/-- **Reading counts and transfer at the canonical witness**: `c_A(b) = c_B(b)`
at every `b ∈ ∂Z`; a boundary vertex of `A` with an `A`-neighbour lies in `B`,
and conversely. -/
noncomputable def WitnessReadingCountsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingCountsAtWitness
```

## hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:272-287
```lean
/-- `PositiveCyclePrivateEdgeStatement` at one target-defect witness `w`. -/
noncomputable abbrev PositiveCyclePrivateEdgeAtWitness {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  ∃ P N : Finset object.Vertex, w.Orientation P N ∧ w.Separates P N ∧
    w.CyclesUsePrivateEdge P N ∧
    ¬ ((SupportAtom.retainedPiece object w.support P).graph ≤
      (SupportAtom.retainedPiece object w.support N).graph)

/-- **Every positive cycle uses a private edge, so `ret_P ⊄ ret_N`**: at the
canonical witness, with `P` the positive and `N` the negative reading at `O`,
every accepted cycle of `glue ret_P O` traverses a private edge `xy` of `P`
(`x, y ∈ P`, `y ∉ N`, `y` internal to `Z`), and `ret_P` has an edge that is not
an edge of `ret_N`. -/
noncomputable def PositiveCyclePrivateEdgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PositiveCyclePrivateEdgeAtWitness
```

## hypostructure/Hypostructure/Graph/ReadingProfiles.lean:45-148
```lean

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

```

## hypostructure/Hypostructure/Graph/TargetDefectStructure.lean:243-270
```lean
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

/-- The bound target-defect geometry at one fixed separating context `O`:
`O` separates the two readings, and the positive one carries the positive
structure against the negative one, in either orientation. -/
def BoundTargetDefectGeometryAt (G : FiniteObject.{u}) (S : Finset G.Vertex)
    {boundary : Boundary.{u}} (LengthOK : Nat → Prop)
    (left right : BoundaryPiece boundary) (O : OutsideContext boundary) : Prop :=
  (¬ (HasCycleWithLength LengthOK (glue left O) ↔
      HasCycleWithLength LengthOK (glue right O))) ∧
    (DefectGeometry.PositiveStructure G S LengthOK left right O ∨
     DefectGeometry.PositiveStructure G S LengthOK right left O)

```

## hypostructure/Hypostructure/Graph/Gluing.lean:20-42
```lean
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    SimpleGraph (GluedVertex piece outside) :=
  piece.graph.map (pieceEmbedding piece outside) ⊔
    outside.graph.map (contextEmbedding piece outside)

/-- Adjacency in a gluing is exactly adjacency owned by one finite side. -/
theorem glueGraph_adj_iff {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (left right : GluedVertex piece outside) :
    (glueGraph piece outside).Adj left right <->
      OwnedAdjacency piece outside left right := by
  rw [glueGraph]
  constructor
  · rintro (pieceAdjacent | contextAdjacent)
    · exact Or.inl ((SimpleGraph.map_adj (pieceEmbedding piece outside)
        piece.graph left right).mp pieceAdjacent)
    · exact Or.inr ((SimpleGraph.map_adj (contextEmbedding piece outside)
        outside.graph left right).mp contextAdjacent)
  · rintro (pieceAdjacent | contextAdjacent)
    · exact Or.inl ((SimpleGraph.map_adj (pieceEmbedding piece outside)
        piece.graph left right).mpr pieceAdjacent)
    · exact Or.inr ((SimpleGraph.map_adj (contextEmbedding piece outside)
        outside.graph left right).mpr contextAdjacent)
```
