# Node [20a]: defining declarations of the residual witness (verbatim excerpt for Stage 2 repair)

Supplied because both Stage 2 reviewers requested "the narrow defining excerpt for the declared-coordinate domain/support map, SparseTargetDefectWitness.Spec and BoundTargetDefectGeometryAt". Verbatim line ranges from `hypostructure/Hypostructure/Graph/` at g-repair-base 7d3186b; nothing added.

## `Statements/CanonicalSurplus.lean` lines 166-232

```lean
/-- The spine coordinates the survival clause reads: the canonical `[129]`
family, or no coordinate when `[129]`'s family does not exist. -/
def canonicalSpineCoordinates (data : Parameters)
    (object : Graph.FiniteObject.{u}) : DeclaredCoordinateFamily object :=
  (canonicalBaselineSpineFamily data object).getD
    (DeclaredCoordinateFamily.empty object)

/-- The declared sparse coordinates. -/
abbrev SparseDeclaredCoordinate (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type u :=
  (object.Vertex × object.Vertex) ⊕
    (object.PairCoordinate ⊕ (canonicalSpineCoordinates data object).Coordinate)

def sparseDeclaredFamily (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (SparseDeclaredCoordinate data object) := by
  classical
  exact match canonicalPairActivation data object with
    | some activation =>
        (object.excessPorts data.threshold).image Sum.inl ∪
          ((activation.pairFamily (object.portPairSchedule data.threshold)).image
              (Sum.inr ∘ Sum.inl) ∪
            (canonicalSpineCoordinates data object).family.image
              (Sum.inr ∘ Sum.inr))
    | none =>
        (canonicalSpineCoordinates data object).family.image (Sum.inr ∘ Sum.inr)

def sparseDeclaredSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    SparseDeclaredCoordinate data object → Finset object.Vertex := by
  classical
  exact fun coordinate => match coordinate with
    | .inl demand =>
        ((canonicalPairActivation data object).map
          fun activation => activation.declaredSupport demand).getD ∅
    | .inr (.inl pair) => Graph.DeclaredSignature.Coordinate.support pair
    | .inr (.inr spine) =>
        (canonicalSpineCoordinates data object).coordinateSupport spine

theorem pairFamily_subset_sparseDeclaredFamily (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (coordinate : object.PairCoordinate)
    (member : coordinate ∈ (Graph.pairResponseActivation active).pairFamily
      (object.portPairSchedule data.threshold)) :
    (Sum.inr (Sum.inl coordinate) : SparseDeclaredCoordinate data object) ∈
      sparseDeclaredFamily data object := by
  classical
  unfold sparseDeclaredFamily
  rw [canonicalPairActivation_eq data object active]
  simp only [Finset.mem_union, Finset.mem_image, Function.comp_apply]
  exact Or.inr (Or.inl ⟨coordinate, member, rfl⟩)


/-- **The named sparse surplus exits of G** (`def:named-surplus-exits`), at G's
declared sparse family. -/
abbrev DeclaredSparseSurplusExit (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
    (sparseDeclaredFamily data object) (sparseDeclaredSupport data object)

/-- **G survives the sparse surplus exits** of its declared sparse family. -/
abbrev DeclaredSparseSurvivor (data : Parameters)
```

## `Statements/SurplusPair.lean` lines 1098-1176

```lean
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  DeclaredSparseSurplusExit data object

/-- **One target-defective identification of G's declared sparse family**
(node `[125]`, clause (b) of `def:named-surplus-exits`): the identified pair of
declared coordinates, the canonical connected support `Z` of their union, and
the separating `∂Z`-boundaried context `O`. -/
structure SparseTargetDefectWitness (data : Parameters)
    (object : Graph.FiniteObject.{u}) where
  /-- The first identified declared coordinate. -/
  first : SparseDeclaredCoordinate data object
  /-- The second identified declared coordinate. -/
  second : SparseDeclaredCoordinate data object
  /-- The canonical connected support `Z` of the two declared supports. -/
  support : Finset object.Vertex
  /-- The `∂Z`-boundaried context separating the two readings. -/
  outside : Graph.OutsideContext
    (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object support)

/-- The clauses of clause (b) at one witness (`lem:context-universality`,
tex 6106-6112): the two coordinates are distinct members of G's declared
family, `Z` is the canonical support of their union, their readings on G's
piece at `Z` lie in one boundary-degree fibre and agree in G's actual outside
context `G - Z`, and the witness's context `O` separates them.  This is
`Graph.ResidualTargetDefect` at G's declared family with its existentials
named by the witness. -/
def SparseTargetDefectWitness.Spec {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (witness : SparseTargetDefectWitness data object) : Prop := by
  classical
  exact witness.first ∈ sparseDeclaredFamily data object ∧
    witness.second ∈ sparseDeclaredFamily data object ∧
    witness.first ≠ witness.second ∧
    Graph.CanonicalSupport.select? object
        (sparseDeclaredSupport data object witness.first ∪
          sparseDeclaredSupport data object witness.second) =
      some witness.support ∧
    (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        witness.support
        (sparseDeclaredSupport data object witness.first)).boundaryDegreeProfile =
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        witness.support
        (sparseDeclaredSupport data object witness.second)).boundaryDegreeProfile ∧
    (Graph.canonicalCoordinateResponse (Graph.HasCycleWithLength data.LengthOK)
        object witness.support (sparseDeclaredSupport data object witness.first)
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
          witness.support) ↔
      Graph.canonicalCoordinateResponse (Graph.HasCycleWithLength data.LengthOK)
        object witness.support (sparseDeclaredSupport data object witness.second)
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
          witness.support)) ∧
    ¬ (Graph.canonicalCoordinateResponse (Graph.HasCycleWithLength data.LengthOK)
          object witness.support
          (sparseDeclaredSupport data object witness.first) witness.outside ↔
        Graph.canonicalCoordinateResponse (Graph.HasCycleWithLength data.LengthOK)
          object witness.support
          (sparseDeclaredSupport data object witness.second) witness.outside)

open Classical in
/-- **G's canonical target-defective identification**: the `Classical.choose`
of clause (b)'s witness at G's declared sparse family, `none` when clause (b)
fails at G.  Nodes `[125]` and `[20]` both speak about this one witness, so
the structure of `[20]` is stated at `[125]`'s own pair, support and
separating context. -/
noncomputable def sparseTargetDefectWitness (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (SparseTargetDefectWitness data object) :=
  if h : ∃ witness : SparseTargetDefectWitness data object, witness.Spec then
    some (Classical.choose h)
  else none

theorem sparseTargetDefectWitness_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {witness : SparseTargetDefectWitness data object}
    (selected : sparseTargetDefectWitness data object = some witness) :
    witness.Spec := by
  unfold sparseTargetDefectWitness at selected
  split at selected
```

## `Statements/SparseExitResidual.lean` lines 20-60

```lean
window packing `P₀`, every certified capacity presentation of G), so it can be
carried on the one ledger and used later as a budget term or a structural
constraint.

Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## The canonical witness's readings -/

/-- The reading of a declared coordinate on G's piece at the witness support
`Z`: `ret_X` for `X` the coordinate's declared support. -/
noncomputable abbrev SparseTargetDefectWitness.reading {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object)
    (c : SparseDeclaredCoordinate data object) :
    Graph.BoundaryPiece (SupportAtom.boundary object w.support) :=
  SupportAtom.retainedPiece object w.support (sparseDeclaredSupport data object c)

/-- The two declared supports `{A, B}` of the witness's pair. -/
noncomputable abbrev SparseTargetDefectWitness.pairSupports {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object) :
    Set (Finset object.Vertex) :=
  {sparseDeclaredSupport data object w.first, sparseDeclaredSupport data object w.second}

/-- The witness with its two coordinates exchanged (same `Z`, same `O`). -/
def SparseTargetDefectWitness.swap {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : SparseTargetDefectWitness data object :=
  ⟨w.second, w.first, w.support, w.outside⟩

/-- `P` holds at G's canonical target-defect witness. -/
abbrev AtSparseTargetDefectWitness (data : Parameters) (object : Graph.FiniteObject.{u})
    (P : SparseTargetDefectWitness data object → Prop) : Prop :=
  ∃ w, sparseTargetDefectWitness data object = some w ∧ P w

```

## `NamedSurplusExits.lean` lines 126-170

```lean
    (SimpleGraph.Hom.ofLE le) (fun _ _ equal => equal) cycle

/-- **The canonical response of a declared coordinate of G at a support `Z`**
(`def:declared-coordinate-signature`, `val_X(r)`): the coordinate read on G's
own piece at `Z` restricted to its declared support (`retainedPiece`), on the
unchanged boundary `∂Z`, tested against every `∂Z`-boundaried context.  It is
the only response a blocker or an exit may read: no caller-chosen label or
value enters. -/
def canonicalCoordinateResponse (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support carried : Finset object.Vertex) :
    OutsideContext (SupportAtom.boundary object support) → Prop :=
  fun outside => Target (glue (SupportAtom.retainedPiece object support carried) outside)

/-- **Clause (b) at G's declared family** (`lem:context-universality`,
tex 6106-6112; `def:target-complete-compression`, tex 6138): two distinct
declared coordinates of the family, read on G's own piece at the canonical
connected support `Z` of their union, lie in one boundary-degree fibre, agree
in G's actual outside context `G - Z`, and are separated by some
`∂Z`-boundaried context. -/
def ResidualTargetDefect (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop := by
  classical
  exact ∃ first ∈ family, ∃ second ∈ family, first ≠ second ∧
    ∃ support : Finset object.Vertex,
      CanonicalSupport.select? object
          (coordinateSupport first ∪ coordinateSupport second) = some support ∧
      (SupportAtom.retainedPiece object support
          (coordinateSupport first)).boundaryDegreeProfile =
        (SupportAtom.retainedPiece object support
          (coordinateSupport second)).boundaryDegreeProfile ∧
      (canonicalCoordinateResponse Target object support (coordinateSupport first)
          (SupportAtom.outside object support) ↔
        canonicalCoordinateResponse Target object support (coordinateSupport second)
          (SupportAtom.outside object support)) ∧
      ∃ outside : OutsideContext (SupportAtom.boundary object support),
        ¬ (canonicalCoordinateResponse Target object support
              (coordinateSupport first) outside ↔
            canonicalCoordinateResponse Target object support
              (coordinateSupport second) outside)

/-- The boundary-profile companion of clause (b) (`lem:degree-profile-fibres`,
tex 6088): two distinct declared coordinates of the family whose readings on
G's piece at their canonical support lie in different boundary-degree fibres.
```

## `InterfaceReplacement.lean` lines 150-225

```lean

abbrev BoundaryVertex :=
  {vertex : object.Vertex // vertex ∈ cutBoundary object support}

abbrev PieceInternal :=
  {vertex : object.Vertex //
    vertex ∈ support ∧ vertex ∉ cutBoundary object support}

abbrev OutsideInternal := {vertex : object.Vertex // vertex ∉ support}

noncomputable def boundary : Boundary.{u} where
  Vertex := BoundaryVertex object support
  vertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex => vertex ∈ cutBoundary object support

/-- Decode a vertex of the atom side back to the ambient graph.  Both
constructors are already ambient vertices carrying a membership proof, so this
is the first projection and nothing is rebuilt. -/
def pieceDecode :
    (boundary object support).Vertex ⊕ PieceInternal object support →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr vertex => vertex.1

def outsideDecode :
    (boundary object support).Vertex ⊕ OutsideInternal object support →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr vertex => vertex.1

noncomputable def piece : BoundaryPiece (boundary object support) where
  Internal := PieceInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ support ∧ vertex ∉ cutBoundary object support
  graph := SimpleGraph.comap (pieceDecode object support) object.graph
  decideAdj := Classical.decRel _

/-- The same support's piece with only the edges `retained` owns.

`piece` and `retainedPiece` share a boundary, an internal type and an internal
enumeration; **only the owned graph varies**.  That is what makes two readings
of one support comparable: `Response.ContextEquivalent` is stated at a single
`Boundary`, so a construction that also moved the boundary could never be
tested against the unrestricted reading.

This is the constructor a carrier restriction needs.  `def:typeA-route8-carriers`
restricts a response state by *retaining* the declared coordinates carried
inside a chosen set and forgetting the rest, while keeping the full boundary
degree profile -- and the boundary profile is preserved here because the
boundary itself is untouched. -/
noncomputable def retainedPiece (retained : Finset object.Vertex) :
    BoundaryPiece (boundary object support) where
  Internal := PieceInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ support ∧ vertex ∉ cutBoundary object support
  graph :=
    SimpleGraph.comap (pieceDecode object support) object.graph ⊓
      SimpleGraph.comap (pieceDecode object support)
        (SimpleGraph.fromRel fun left right =>
          left ∈ retained ∧ right ∈ retained)
  decideAdj := Classical.decRel _

noncomputable def outside : OutsideContext (boundary object support) where
  Internal := OutsideInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex => vertex ∉ support
  graph := SimpleGraph.comap (outsideDecode object support) object.graph
  decideAdj := Classical.decRel _

theorem not_adj_pieceInternal_outside
```

## `CanonicalSupportSelection.lean` lines 1-64

```lean
import Hypostructure.Graph.SupportComponents

/-!
# Canonical selection of a minimum connected support containing a seed

The manuscript repeatedly names *"the lexicographically first connected subgraph
of `G` with the minimum possible number of vertices that contains …"*.  This
module is the framework's single implementation of that phrase.

The candidate family is every vertex subset of the object that contains the seed
and is connected.  Among those, the ones of least cardinality are the minimum
ones, and the selection is the head of the object's own enumeration of that
family.  So the result is a function of the object and the seed alone — no path,
no ordering and no witness is supplied by a caller — which is the canonicity the
manuscript's constructions claim.

Nothing here knows what a seed is for.  A pair of demand supports, a family of
pair supports, or a single window all select through the same three
declarations.
-/

namespace Hypostructure.Graph.CanonicalSupport

open Hypostructure.Graph

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

## `Boundary.lean` lines 1-70

```lean
import Hypostructure.Graph.Finite

/-!
# Finite graph boundaries

A boundary piece and an outside context are finite boundaried graphs on the
same labelled interface.  Either side may own boundary--boundary edges; gluing
identifies equal boundary labels and takes the union of both edge sets.  Edge
ownership may therefore overlap.  The structures contain no target,
obstruction, or problem-specific state.
-/

namespace Hypostructure.Graph

universe u

/-- A finite labelled interface. -/
structure Boundary where
  Vertex : Type u
  vertices : FinEnum Vertex

namespace Boundary

/-- Number of interface labels, derived from the supplied finite schedule. -/
def vertexCount (boundary : Boundary.{u}) : Nat :=
  boundary.vertices.card

end Boundary

/-- The atom side of a graph decomposition. -/
structure BoundaryPiece (boundary : Boundary.{u}) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (boundary.Vertex ⊕ Internal)
  decideAdj : DecidableRel graph.Adj

/-- The outside side of a graph decomposition on the same labelled boundary. -/
structure OutsideContext (boundary : Boundary.{u}) where
  Internal : Type u
  internalVertices : FinEnum Internal
  graph : SimpleGraph (boundary.Vertex ⊕ Internal)
  decideAdj : DecidableRel graph.Adj

namespace BoundaryPiece

/-- Internal size is the replacement-relevant vertex count. -/
def internalVertexCount {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) : Nat :=
  piece.internalVertices.card

/-- Forget the distinguished interface and obtain an ordinary finite graph. -/
def pack {boundary : Boundary.{u}} (piece : BoundaryPiece boundary) :
    FiniteObject.{u} where
  Vertex := boundary.Vertex ⊕ piece.Internal
  graph := piece.graph
  vertices := by
    letI : FinEnum boundary.Vertex := boundary.vertices
    letI : FinEnum piece.Internal := piece.internalVertices
    infer_instance
  decideAdj := piece.decideAdj

end BoundaryPiece

namespace OutsideContext

/-- Internal size of the outside context. -/
def internalVertexCount {boundary : Boundary.{u}}
    (outside : OutsideContext boundary) : Nat :=
  outside.internalVertices.card

```

## `Gluing.lean` lines 55-95

```lean
  rcases (glueGraph_adj_iff _ outside left right).mp adjacency with
    owned | contextOwned
  · refine (glueGraph_adj_iff piece outside left right).mpr (Or.inl ?_)
    obtain ⟨source, target, ownedAdj, sourceEq, targetEq⟩ := owned
    refine ⟨source, target, le ownedAdj, ?_, ?_⟩
    · cases source <;> exact sourceEq
    · cases target <;> exact targetEq
  · exact (glueGraph_adj_iff piece outside left right).mpr (Or.inr contextOwned)

/-- The glued graph with its finite schedule derived from the three disjoint
vertex families.
-/
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

/-- Exact vertex accounting for a literal gluing. -/
@[simp]
theorem glue_vertexCount {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    (glue piece outside).vertexCount =
      boundary.vertexCount + piece.internalVertexCount +
        outside.internalVertexCount := by
  letI : FinEnum boundary.Vertex := boundary.vertices
  letI : FinEnum piece.Internal := piece.internalVertices
  letI : FinEnum outside.Internal := outside.internalVertices
  simp [glue, FiniteObject.vertexCount, Boundary.vertexCount,
    BoundaryPiece.internalVertexCount, OutsideContext.internalVertexCount,
    FinEnum.card_eq_fintypeCard, Nat.add_assoc]

namespace OwnedDecomposition

/-- The exact ownership law reconstructs the ambient graph up to isomorphism. -/
```

## `TargetDefectStructure.lean` lines 1-277

```lean
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

/-- One publication, retaining the same defect context in either orientation. -/
def BoundTargetDefectGeometry (G : FiniteObject.{u}) (S : Finset G.Vertex)
    {boundary : Boundary.{u}} (LengthOK : Nat → Prop)
    (left right : BoundaryPiece boundary) : Prop :=
  ∃ O : OutsideContext boundary, BoundTargetDefectGeometryAt G S LengthOK left right O

end Hypostructure.Graph
```
