## GluedReadingMaps.lean 118-139
```lean
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

```

## GluedReadingMaps.lean 2009-2026
```lean
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
```

## GluedReadingMaps.lean 2069-2072
```lean
G-edge iff every edge of `G[Z]` not inside `X` joins two `∂Z` vertices. -/
theorem keepsAll_iff (Z X : Finset object.Vertex) :
    KeepsAll Z X ↔ DroppedAreBoundary Z X := by
  constructor
```

## CanonicalSupportSelection.lean 26-64
```lean
universe u

variable (object : FiniteObject.{u})

/-- The candidate family: the connected vertex sets containing the seed. -/
noncomputable def candidates (seed : Finset object.Vertex) :
    Finset (Finset object.Vertex) := by
  classical
  exact object.vertexFinset.powerset.filter fun support =>
    seed ⊆ support ∧ SupportComponents.Connected.ConnectedOn object support

variable {object}

theorem mem_candidates_iff {seed support : Finset object.Vertex} :
    support ∈ candidates object seed ↔
      seed ⊆ support ∧ SupportComponents.Connected.ConnectedOn object support := by
  classical
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨_, rest⟩; exact rest
  · intro rest
    exact ⟨fun vertex _ => object.mem_vertexFinset vertex, rest⟩

/-- Every candidate of least cardinality: the manuscript's "minimum possible
number of vertices". -/
noncomputable def minimalCandidates (object : FiniteObject.{u})
    (seed : Finset object.Vertex) : Finset (Finset object.Vertex) := by
  classical
  exact (candidates object seed).filter fun support =>
    ∀ other ∈ candidates object seed, support.card ≤ other.card

/-- **The canonical minimum connected support containing the seed.**

`none` exactly when no connected set contains the seed; otherwise the head of
the object's own enumeration of the minimum-cardinality candidates.  The choice
uses only the object and the seed. -/
noncomputable def select? (object : FiniteObject.{u})
    (seed : Finset object.Vertex) : Option (Finset object.Vertex) :=
  (minimalCandidates object seed).toList.head?
```