# Node 20 Stage 3: exact connected-cut declarations

Verbatim, line-numbered declarations concerning the fixed graph G and the residual-bound support S. Stage 3 must check whether their conjunction excludes its accepted open case `rc05_proper_empty_boundary` by a path crossing argument. That consequence is a proposed inference, not an added premise. Keep every complementary case and both orientations of the same target-defect witness.

## `hypostructure/Hypostructure/Graph/SupportComponents.lean:59-66`

```lean
59: def ConnectedOn (object : FiniteObject.{u})
60:     (core : Finset object.Vertex) : Prop :=
61:   core.Nonempty ∧
62:     ∀ ⦃left right : object.Vertex⦄, left ∈ core → right ∈ core →
63:       ∃ path : object.graph.Walk left right,
64:         path.IsPath ∧ ∀ vertex ∈ path.support, vertex ∈ core
65: 
66: /-- Ambient graph connectedness, expressed on the explicit full support used
```

## `hypostructure/Hypostructure/Graph/Strategy/InterfaceReplacement.lean:118-126`

```lean
118: 
119: variable (object : FiniteObject.{u}) (support : Finset object.Vertex)
120: 
121: /-- The literal cut boundary of a retained connected support. -/
122: def cutBoundary : Finset object.Vertex := by
123:   letI : DecidableEq object.Vertex := object.vertices.decEq
124:   exact support.filter fun vertex =>
125:     (object.orderedNeighbors vertex).any fun neighbor => neighbor ∉ support
126: 
```

## `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean:8324-8327`

```lean
8324:   | .noProperBaseline, object =>
8325:       (∀ subgraph : Graph.ProperSubgraph object,
8326:         ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value) ∧
8327:       object.graph.Connected
```
