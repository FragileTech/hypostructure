# Node 20 residual: direct witness definitions

Selected verbatim line ranges used only to classify the actual binders in
`sparseTargetDefectResidual`. These do not audit the proof tree or establish a
new link between the existential outside context and the complement of the
fixed object. Omitted lines are comments or unrelated declarations; each
displayed source line is transcribed exactly from its cited range.

## Fixed support boundary and its two sides

`hypostructure/Hypostructure/Graph/Strategy/InterfaceReplacement.lean`, lines
121–125 and 151–165:

```lean
def cutBoundary : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact support.filter fun vertex =>
    (object.orderedNeighbors vertex).any fun neighbor => neighbor ∉ support

abbrev BoundaryVertex :=
  {vertex : object.Vertex // vertex ∈ cutBoundary object support}

abbrev PieceInternal :=
  {vertex : object.Vertex //
    vertex ∈ support ∧ vertex ∉ cutBoundary object support}

abbrev OutsideInternal := {vertex : object.Vertex // vertex ∉ support}

noncomputable def boundary : Boundary.{u} where
  Vertex := BoundaryVertex object support
```

## Realization and context types

`hypostructure/Hypostructure/Graph/Boundary.lean`, lines 30–42:

```lean
structure BoundaryPiece (boundary : Boundary.{u}) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (boundary.Vertex ⊕ Internal)
  decideAdj : DecidableRel graph.Adj

structure OutsideContext (boundary : Boundary.{u}) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (boundary.Vertex ⊕ Internal)
  decideAdj : DecidableRel graph.Adj
```

`hypostructure/Hypostructure/Graph/Gluing.lean`, lines 18–23 and 67–77:

```lean
def glueGraph {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    SimpleGraph (GluedVertex piece outside) :=
  piece.graph.map (pieceEmbedding piece outside) ⊔
    outside.graph.map (contextEmbedding piece outside)

noncomputable def glue {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    FiniteObject.{u} where
  Vertex := GluedVertex piece outside
  graph := glueGraph piece outside
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum piece.Internal := piece.internalVertices
    letI : FinEnum outside.Internal := outside.internalVertices
    infer_instance
  decideAdj := Classical.decRel _
```

## Attempt fields and the bound response pair

`hypostructure/Hypostructure/Graph/DeclaredRankQuotient.lean`, lines 61–80,
85–105, and 131–138:

```lean
structure AttemptedQuotient (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) {Coordinate : Type u}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Type (u + 2) where
  support : Finset object.Vertex
  connected : SupportComponents.Connected.ConnectedOn object support
  carries : ∀ coordinate ∈ family, coordinateSupport coordinate ⊆ support
  Label : Type (u + 1)
  Value : Type (u + 1)
  label : Coordinate → Label
  value : BoundaryPiece (SupportAtom.boundary object support) → Label → Value
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑family →
    (∀ left right : BoundaryPiece (SupportAtom.boundary object support),
      (∀ coordinate ∈ family, value left (label coordinate) =
        value right (label coordinate)) →
      left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
        Response.ContextEquivalent Target left right) →
    ReplacementSupport Baseline Target object support
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑family →
    (∀ left right : BoundaryPiece (SupportAtom.boundary object support),
      (∀ coordinate ∈ family, value left (label coordinate) =
        value right (label coordinate)) →
      left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
        Response.ContextEquivalent Target left right) →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ (Target representative → Target object)

def Identifies (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (left right : BoundaryPiece (SupportAtom.boundary object attempt.support)) :
    Prop :=
  ∀ coordinate ∈ family,
    attempt.value left (attempt.label coordinate) =
      attempt.value right (attempt.label coordinate)
```

## Exact target-defect witness

`hypostructure/Hypostructure/Graph/Response.lean`, lines 101–106:

```lean
def TargetDefect {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (left right : BoundaryPiece boundary) : Prop :=
  exists outside : OutsideContext boundary,
    Not (Target (glue left outside) <-> Target (glue right outside))
```
