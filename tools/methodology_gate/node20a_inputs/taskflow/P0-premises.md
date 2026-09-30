# P0-premises: inherited-premise check

Result: SUBMITTED_RESULT for the assigned premise check on `node20a-stage3b-S1@7d3186b`.

Both declared source files match their pinned SHA-256 values in `/input/assignment.json`. The residual record identifies its source revision as `g-repair-base @ 7d3186b`. This is a documentary and mathematical projection check; no Lean implementation or kernel check is claimed.

## Fixed objects and conjunction projection

Let `h : Node20aOutcome selected`, `G = selected.object : Graph.FiniteObject`, and `data = spineData.toParameters`. The residual record's vocabulary parameter named `data` is instantiated by `spineData`; thus its table expression `data.toParameters object` instantiates to our `data G`, not to a further conversion of our parameter object.

The verbatim residual definition contains all six following conjuncts (in the task's requested order):

```lean
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingsCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .positiveCyclePrivateEdge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
```

These are separate quoted conjuncts of the full 128-fact residual, not a replacement definition. Repeated conjunction elimination on `h` gives each one; conjunction introduction gives their simultaneous conjunction. The recorded `Holds` clauses below identify their exact statement types. No other residual fact is discarded or altered.

## Exact statement quotations

The following sections, including their Lean declarations, are copied verbatim from the residual record. Each source locator refers to that record.

Residual-record locator: lines 831–850.

### 21. `K .sparseTargetDefectResidual` (fact `f021_sparseTargetDefectResidual`)

`Holds … .sparseTargetDefectResidual object = SparseTargetDefectResidualStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1200-1212:

```lean
/-- Node `[125]`, the sole nonterminal named-exit payload: clause (b) of
`def:named-surplus-exits` at G's declared sparse family
(`lem:context-universality`, tex 6106-6112), at G's canonical witness
`sparseTargetDefectWitness` -- two distinct declared coordinates of G, read on
G's own piece at their canonical connected support `Z`, agree in G's actual
outside context and are separated by the witness's `∂Z`-boundaried context
`O`. -/
noncomputable abbrev SparseTargetDefectResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ witness, sparseTargetDefectWitness data object = some witness ∧
    witness.Spec
```

Residual-record locator: lines 851–872.

### 22. `K .sparseTargetDefectStructure` (fact `f022_sparseTargetDefectStructure`)

`Holds … .sparseTargetDefectStructure object = SparseTargetDefectStructureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1214-1228:

```lean
/-- Node `[20]`: the bound target-defect geometry of the two readings of
`[125]`'s identified pair on G's piece at `[125]`'s support `Z`, at `[125]`'s
separating context `O` -- all three read from the one canonical witness
`sparseTargetDefectWitness`, the witness `[125]` publishes. -/
noncomputable abbrev SparseTargetDefectStructureStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ witness, sparseTargetDefectWitness data object = some witness ∧
    Graph.BoundTargetDefectGeometryAt object witness.support data.LengthOK
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        witness.support (sparseDeclaredSupport data object witness.first))
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        witness.support (sparseDeclaredSupport data object witness.second))
      witness.outside
```

Residual-record locator: lines 971–981.

### 29. `K .witnessReadingsCycleFree` (fact `f029_witnessReadingsCycleFree`)

`Holds … .witnessReadingsCycleFree object = WitnessReadingsCycleFreeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 171-174:

```lean
/-- **Both reading pieces are cycle-free** (each embeds in G). -/
noncomputable def WitnessReadingsCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingsCycleFreeAtWitness
```

Residual-record locator: lines 2143–2155.

### 115. `K .witnessReadingCounts` (fact `f115_witnessReadingCounts`)

`Holds … .witnessReadingCounts object = WitnessReadingCountsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 203-208:

```lean
/-- **Reading counts and transfer at the canonical witness**: `c_A(b) = c_B(b)`
at every `b ∈ ∂Z`; a boundary vertex of `A` with an `A`-neighbour lies in `B`,
and conversely. -/
noncomputable def WitnessReadingCountsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingCountsAtWitness
```

Residual-record locator: lines 2184–2198.

### 118. `K .positiveCyclePrivateEdge` (fact `f118_positiveCyclePrivateEdge`)

`Holds … .positiveCyclePrivateEdge object = PositiveCyclePrivateEdgeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 280-287:

```lean
/-- **Every positive cycle uses a private edge, so `ret_P ⊄ ret_N`**: at the
canonical witness, with `P` the positive and `N` the negative reading at `O`,
every accepted cycle of `glue ret_P O` traverses a private edge `xy` of `P`
(`x, y ∈ P`, `y ∉ N`, `y` internal to `Z`), and `ret_P` has an edge that is not
an edge of `ret_N`. -/
noncomputable def PositiveCyclePrivateEdgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PositiveCyclePrivateEdgeAtWitness
```

Residual-record locator: lines 528–543.

### 7. `K .tightEndpoint` (fact `f007_tightEndpoint`)

`Holds … .tightEndpoint object = TightEndpointStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2665-2673:

```lean
/-- Node `[9]`: every oriented edge has an endpoint exactly at the
threshold. -/
noncomputable abbrev TightEndpointStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ dart : object.graph.Dart,
    object.degree dart.fst = data.threshold ∨
      object.degree dart.snd = data.threshold)
```

## Identification at the retained witness

At the fixed `data, G`, f021 supplies `w : SparseTargetDefectWitness data G`, the equality `hw : sparseTargetDefectWitness data G = some w`, and `w.Spec`. Keep `Z = w.support`, `O = w.outside`, `A = sparseDeclaredSupport data G w.first`, and `B = sparseDeclaredSupport data G w.second`.

For f022, if its existential supplies `v` with equality `hv`, then `hw.symm.trans hv : some w = some v`. Injectivity of `Option.some` gives `w = v`; substitution yields precisely the quoted geometry at `w.support`, the retained pieces of `w.first` and `w.second`, and `w.outside`.

For f029, f115 and f118 the exact quoted types are the displayed `AtSparseTargetDefectWitness` statements; their named witness predicates are retained at those types. The supplied stage3b context, lines 61–63, explicitly records their canonical some-equalities and their identification with the f021 witness by the same injectivity argument. Reusing that accepted identification keeps all three predicates at this same `w`. In particular, the context records f118's orientation, separation and private-edge condition at `w`, applying to the original positive certificate. No new witness or certificate is selected by this check.

For f007 the exact domain is `G.graph.Dart`: for each such dart, one of its two ambient degrees equals `data.threshold`. This premise does not assert tightness of an arbitrary vertex or of both endpoints.

Thus all six requested premises are inherited simultaneously at their recorded types and the retained objects. The accepted geometry, cycle-free, reading-count and private-edge predicates are used as retained statements; this check neither strengthens them nor derives the later cyclic-segment obligations. Minimality, exclusions, all other conjuncts, independent witnesses and accounts remain unchanged. No representation or domain change is required.

There is no missing source, identification or inference for P0-premises. No immediate subobligations arise within this task. Side observation: the context's unresolved contiguous-segment extraction belongs to the separate S1 work and is not executed here. No move or branch is marked closed.
