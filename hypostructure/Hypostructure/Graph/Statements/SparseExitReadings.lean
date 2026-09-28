import Hypostructure.Graph.Statements.SparseExitResidual
import Hypostructure.Graph.ReadingSpectrumArms
import Hypostructure.Graph.EdgeSwitchPaths

/-!
# Statements: the readings of the canonical target-defect witness, and the edge
# switches of G

Facts about G and its fixed objects that the `[20a]` residual carries, each
stated over the registered `Parameters`:

* **Edge switches of G** (from the selection, the baseline and the tight/slack
  structure): two high vertices, or one vertex of degree `≥ δ + 2`, force paths
  in G minus two edges whose length plus one is accepted; where the surplus of G
  sits; the switch at every high/baseline edge.
* **The readings at G's canonical witness `w = (A, B, Z, O)`**: the reading
  counts `c_A = c_B` on `∂Z`; at least two active labels (so neither support is
  boundary-free, and no single label carries the activity); the exact partition
  of `∂Z`; the private edge of the positive reading on every positive cycle
  (`ret_P ⊄ ret_N`); the whole case; arm (i) of the spectrum split refined
  (`|π| ≥ 2`, and `|σ| ≥ 2` at an adjacent pair); a separating single-edge
  context never sits at an adjacent pair and is itself a clause-(b) witness;
  the swap object and the switch at the private edge; the outside returns of
  the baseline labels.

Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## Edge switches of G -/

/-- **Two high vertices force a path**: for `h₁ ≠ h₂` above the baseline and
neighbours `u₁ ~ h₁`, `u₂ ~ h₂` with `u₁ ≠ u₂`, `u₁ ≁ u₂`: both `u₁, u₂` sit at
the baseline and `G − {u₁h₁, u₂h₂}` has a simple `u₁`–`u₂` path of length `ℓ`
with `ℓ + 1` accepted. -/
def TwoHighForcedPathStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ h₁ h₂ u₁ u₂ : object.Vertex,
    data.threshold < object.degree h₁ → data.threshold < object.degree h₂ → h₁ ≠ h₂ →
    object.graph.Adj u₁ h₁ → object.graph.Adj u₂ h₂ → u₁ ≠ u₂ →
    ¬ object.graph.Adj u₁ u₂ →
    object.degree u₁ = data.threshold ∧ object.degree u₂ = data.threshold ∧
      ∃ p : (object.graph.deleteEdges {s(u₁, h₁), s(u₂, h₂)}).Walk u₁ u₂,
        p.IsPath ∧ data.LengthOK (p.length + 1)

/-- **A vertex of degree `≥ δ + 2` forces paths between its non-adjacent
neighbours**: `G − {hu₁, hu₂}` has a simple `u₁`–`u₂` path `p` with
`|p| + 1` accepted; either `p` avoids `h` (and `|p| + 2` is not accepted), or it
splits at `h` into two returns `ℓ₁ + ℓ₂ = |p|` with neither `ℓᵢ + 1`
accepted. -/
def SameHighForcedPathStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ h u₁ u₂ : object.Vertex, data.threshold + 2 ≤ object.degree h →
    object.graph.Adj h u₁ → object.graph.Adj h u₂ → u₁ ≠ u₂ → ¬ object.graph.Adj u₁ u₂ →
    ∃ p : (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).Walk u₁ u₂,
      p.IsPath ∧ data.LengthOK (p.length + 1) ∧
      ((h ∉ p.support ∧ ¬ data.LengthOK (p.length + 2)) ∨
        ∃ ℓ₁ ℓ₂, ℓ₁ + ℓ₂ = p.length ∧ ¬ data.LengthOK (ℓ₁ + 1) ∧
          ¬ data.LengthOK (ℓ₂ + 1))

/-- **Where the surplus of G sits**: G has a vertex of degree `≥ δ + 2`, or two
distinct vertices of degree exactly `δ + 1`. -/
def HighSurplusConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∃ h, data.threshold + 2 ≤ object.degree h) ∨
    ∃ h₁ h₂, h₁ ≠ h₂ ∧ object.degree h₁ = data.threshold + 1 ∧
      object.degree h₂ = data.threshold + 1

/-- **The switch at every high/baseline edge `hc`**: a forced path from `c`,
by the same-vertex switch at `h` when `deg h ≥ δ + 2` (to a neighbour `u` of
`h` with `u ≠ c`, `u ≁ c`, in `G − {hc, hu}`), else by the two-edge switch with
a second high vertex `h₂ ≠ h` and its neighbour `u₂ ≠ c`, `u₂ ≁ c` (in
`G − {ch, u₂h₂}`). -/
def HighEndpointSwitchStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ h c : object.Vertex, data.threshold + 1 ≤ object.degree h →
    object.degree c = data.threshold → object.graph.Adj h c →
    (data.threshold + 2 ≤ object.degree h ∧ ∃ u, object.graph.Adj h u ∧ u ≠ c ∧
        ¬ object.graph.Adj c u ∧
        ∃ p : (object.graph.deleteEdges {s(h, c), s(h, u)}).Walk c u,
          p.IsPath ∧ data.LengthOK (p.length + 1)) ∨
      ∃ h₂ u₂, h₂ ≠ h ∧ data.threshold + 1 ≤ object.degree h₂ ∧
        object.graph.Adj u₂ h₂ ∧ u₂ ≠ c ∧ ¬ object.graph.Adj c u₂ ∧
        ∃ p : (object.graph.deleteEdges {s(c, h), s(u₂, h₂)}).Walk c u₂,
          p.IsPath ∧ data.LengthOK (p.length + 1)

/-! ## The spectrum split at every clause-(b) witness -/

/-- **The path-spectrum split at every clause-(b) witness of G** (not only the
canonical one): for every `w'` with `w'.Spec`, a positive reading `P` and a
negative reading `N` at `w'.outside`, and either (i) labels `a ≠ b`, a path
`π : a → b` of `ret_P` and an outside path `σ : b → a` meeting no other label
with `|π| + |σ|` accepted and `≥ 3`, every `ret_N` path `π'` between the same
labels having `|π'| ≠ |π|` and (unless both `π'` and `σ` are single edges)
`|π'| + |σ|` not accepted; or (ii) every accepted cycle of the positive gluing
meets three labels. -/
noncomputable def EveryWitnessSpectrumSplitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ w' : SparseTargetDefectWitness data object, w'.Spec →
    ∃ P ∈ w'.pairSupports, ∃ N ∈ w'.pairSupports,
      Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w'.support P) w'.outside) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w'.support N) w'.outside) ∧
      ((∃ a b : (SupportAtom.boundary object w'.support).Vertex, a ≠ b ∧
          ∃ π : (SupportAtom.retainedPiece object w'.support P).graph.Walk
              (.inl a) (.inl b), π.IsPath ∧
          ∃ σ : w'.outside.graph.Walk (.inl b) (.inl a), σ.IsPath ∧
            (∀ d, (Sum.inl d : _ ⊕ w'.outside.Internal) ∈ σ.support → d = a ∨ d = b) ∧
            data.LengthOK (π.length + σ.length) ∧ 3 ≤ π.length + σ.length ∧
            ∀ π' : (SupportAtom.retainedPiece object w'.support N).graph.Walk
                (.inl a) (.inl b), π'.IsPath →
              π'.length ≠ π.length ∧
              ((1 < π'.length ∨ 1 < σ.length) → ¬ data.LengthOK (π'.length + σ.length))) ∨
        (∀ c : Graph.CycleCertificate
            (Graph.glue (SupportAtom.retainedPiece object w'.support P) w'.outside)
            data.LengthOK,
          ∃ a b d : (SupportAtom.boundary object w'.support).Vertex,
            a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
            (Sum.inl a : Graph.GluedVertex _ w'.outside) ∈ c.walk.support ∧
            (Sum.inl b : Graph.GluedVertex _ w'.outside) ∈ c.walk.support ∧
            (Sum.inl d : Graph.GluedVertex _ w'.outside) ∈ c.walk.support))

/-! ## The readings at the canonical witness -/

section Readings

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The reading count `c_X(b)` of the declared coordinate `x` at a boundary
vertex `b` of the witness support. -/
noncomputable abbrev SparseTargetDefectWitness.count
    (w : SparseTargetDefectWitness data object) (x : SparseDeclaredCoordinate data object)
    (b : (SupportAtom.boundary object w.support).Vertex) : Nat :=
  Graph.ReadingCounts.readingCount w.support (sparseDeclaredSupport data object x) b

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
  ∀ c : Graph.CycleCertificate
      (Graph.glue (SupportAtom.retainedPiece object w.support P) w.outside) data.LengthOK,
    ∃ a b d : (SupportAtom.boundary object w.support).Vertex,
      a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      (Sum.inl a : Graph.GluedVertex _ w.outside) ∈ c.walk.support ∧
      (Sum.inl b : Graph.GluedVertex _ w.outside) ∈ c.walk.support ∧
      (Sum.inl d : Graph.GluedVertex _ w.outside) ∈ c.walk.support

/-- The whole case `Z ⊆ X` at one orientation: `ret_X` positive and `ret_Y`
negative at `O`, and every positive cycle passes through an internal vertex of
`Z ∖ Y`. -/
abbrev WholeCycleMeetsDeficitAt (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading x) w.outside) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading y) w.outside) ∧
    ∀ c : Graph.CycleCertificate (Graph.glue (w.reading x) w.outside) data.LengthOK,
      ∃ i : SupportAtom.PieceInternal object w.support,
        i.1 ∉ sparseDeclaredSupport data object y ∧
        (Sum.inr (Sum.inl i) : Graph.GluedVertex (w.reading x) w.outside) ∈ c.walk.support

/-- The whole case `Z ⊆ X` at one orientation: an edge `st` of G is a private
edge of `X` (both ends in `X`, not both in `Y`) iff one end lies in `Z ∖ Y`. -/
abbrev WholePrivateEdgesAt (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    ∀ s t : object.Vertex, object.graph.Adj s t →
      ((s ∈ sparseDeclaredSupport data object x ∧
          t ∈ sparseDeclaredSupport data object x ∧
          ¬ (s ∈ sparseDeclaredSupport data object y ∧
            t ∈ sparseDeclaredSupport data object y)) ↔
        ((s ∈ w.support ∧ s ∉ sparseDeclaredSupport data object y) ∨
          (t ∈ w.support ∧ t ∉ sparseDeclaredSupport data object y)))

end Readings

/-- **Reading counts and transfer at the canonical witness**: `c_A(b) = c_B(b)`
at every `b ∈ ∂Z`; a boundary vertex of `A` with an `A`-neighbour lies in `B`,
and conversely. -/
noncomputable def WitnessReadingCountsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    (∀ b, w.count w.first b = w.count w.second b) ∧
    (∀ b : (SupportAtom.boundary object w.support).Vertex,
      b.1 ∈ sparseDeclaredSupport data object w.first →
      ∀ x ∈ sparseDeclaredSupport data object w.first, object.graph.Adj b.1 x →
      b.1 ∈ sparseDeclaredSupport data object w.second) ∧
    (∀ b : (SupportAtom.boundary object w.support).Vertex,
      b.1 ∈ sparseDeclaredSupport data object w.second →
      ∀ x ∈ sparseDeclaredSupport data object w.second, object.graph.Adj b.1 x →
      b.1 ∈ sparseDeclaredSupport data object w.first)

/-- **At least two active labels at the canonical witness**: the set of labels
`l ∈ ∂Z` with `c_A(l) > 0` has at least two elements; two distinct ones have
`1 ≤ c_A(l) = c_B(l) ≤ deg(l) − 1` and lie in `A ∩ B`; in particular both `A`
and `B` meet `∂Z` (no reading is boundary-free). -/
noncomputable def WitnessActiveLabelsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    2 ≤ {l : (SupportAtom.boundary object w.support).Vertex | 0 < w.count w.first l}.ncard ∧
    (∃ x ∈ sparseDeclaredSupport data object w.first,
      x ∈ SupportAtom.cutBoundary object w.support) ∧
    (∃ x ∈ sparseDeclaredSupport data object w.second,
      x ∈ SupportAtom.cutBoundary object w.support) ∧
    ∃ l₁ l₂ : (SupportAtom.boundary object w.support).Vertex, l₁ ≠ l₂ ∧
      ∀ l, (l = l₁ ∨ l = l₂) →
        0 < w.count w.first l ∧ w.count w.first l = w.count w.second l ∧
        l.1 ∈ sparseDeclaredSupport data object w.first ∧
        l.1 ∈ sparseDeclaredSupport data object w.second ∧
        w.count w.first l + 1 ≤ object.degree l.1

/-- **`|∂Z| = 2`: the whole boundary is active and lies in `A ∩ B`.** -/
noncomputable def TwoBoundaryAllActiveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    (SupportAtom.cutBoundary object w.support).card = 2 →
    ∀ b : (SupportAtom.boundary object w.support).Vertex,
      0 < w.count w.first b ∧ b.1 ∈ sparseDeclaredSupport data object w.first ∧
        b.1 ∈ sparseDeclaredSupport data object w.second

open Classical in
/-- **The exact partition of `∂Z`** at the canonical witness: every boundary
vertex is (i) active (`c_A = c_B ≥ 1`, in `A ∩ B`), or (ii) a zero-count vertex
of `A ∪ B`, isolated in `G[A]` resp. `G[B]`, or (iii) a Steiner vertex
(`∉ A ∪ B`), a cut vertex of `G[Z]`. -/
noncomputable def BoundaryPartitionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ b : (SupportAtom.boundary object w.support).Vertex,
      (0 < w.count w.first b ∧ b.1 ∈ sparseDeclaredSupport data object w.first ∧
        b.1 ∈ sparseDeclaredSupport data object w.second) ∨
      (w.count w.first b = 0 ∧ w.count w.second b = 0 ∧
        (b.1 ∈ sparseDeclaredSupport data object w.first ∨
          b.1 ∈ sparseDeclaredSupport data object w.second) ∧
        (b.1 ∈ sparseDeclaredSupport data object w.first →
          ∀ x ∈ sparseDeclaredSupport data object w.first, ¬ object.graph.Adj b.1 x) ∧
        (b.1 ∈ sparseDeclaredSupport data object w.second →
          ∀ x ∈ sparseDeclaredSupport data object w.second, ¬ object.graph.Adj b.1 x)) ∨
      (b.1 ∉ sparseDeclaredSupport data object w.first ∧
        b.1 ∉ sparseDeclaredSupport data object w.second ∧
        ¬ Graph.SupportComponents.Connected.ConnectedOn object (w.support.erase b.1))

/-- **Every positive cycle uses a private edge, so `ret_P ⊄ ret_N`**: at the
canonical witness, with `P` the positive and `N` the negative reading at `O`,
every accepted cycle of `glue ret_P O` traverses a private edge `xy` of `P`
(`x, y ∈ P`, `y ∉ N`, `y` internal to `Z`), and `ret_P` has an edge that is not
an edge of `ret_N`. -/
noncomputable def PositiveCyclePrivateEdgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ P N : Finset object.Vertex, w.Orientation P N ∧ w.Separates P N ∧
      w.CyclesUsePrivateEdge P N ∧
      ¬ ((SupportAtom.retainedPiece object w.support P).graph ≤
        (SupportAtom.retainedPiece object w.support N).graph)

/-- **Whole case: every positive cycle passes through `Z ∖ Y`**, at both
orientations (`Z ⊆ A` and `Z ⊆ B`). -/
noncomputable def WholeCycleMeetsDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    WholeCycleMeetsDeficitAt w w.first w.second ∧ WholeCycleMeetsDeficitAt w w.second w.first

/-- **Whole case: the private edges of `X` are exactly the edges at `Z ∖ Y`**,
at both orientations. -/
noncomputable def WholePrivateEdgesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    WholePrivateEdgesAt w w.first w.second ∧ WholePrivateEdgesAt w w.second w.first

/-- **Arm (i) of the spectrum split, refined, at the canonical witness**: with
`P` positive and `N` negative at `O`, either the refined arm (i)
(`ArmOneRefined`: active labels in `A ∩ B`, a private edge on `π`, `|π| ≥ 2`;
at `a ~ b`: `|σ| ≥ 2`, `|π| + 1`, `|σ| + 1` not accepted, the four residue
classes and the outside closures; no outside `b → a` path completes `π`; and
`|σ| = 1` makes the single-edge context `a — b` separating), or arm (ii); and
`|∂Z| = 2` forces the refined arm (i). -/
noncomputable def SpectrumArmOneRefinedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ P N : Finset object.Vertex, w.Orientation P N ∧ w.Separates P N ∧
      (Graph.ReadingSpectrumArms.ArmOneRefined w.support P N w.outside ∨
        w.CyclesMeetThreeLabels P) ∧
      ((SupportAtom.cutBoundary object w.support).card = 2 →
        Graph.ReadingSpectrumArms.ArmOneRefined w.support P N w.outside)

/-- The witness with the single-edge context `a — b` in place of `O`. -/
noncomputable abbrev SparseTargetDefectWitness.atEdge {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object)
    (a b : (SupportAtom.boundary object w.support).Vertex) :
    SparseTargetDefectWitness data object :=
  ⟨w.first, w.second, w.support, Graph.SingleEdgeContext.edgeContext w.support a b⟩

/-- The single-edge context `a — b` separates the two readings of `w`. -/
abbrev SparseTargetDefectWitness.EdgeSeparates {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object)
    (a b : (SupportAtom.boundary object w.support).Vertex) : Prop :=
  ¬ (Graph.HasCycleWithLength data.LengthOK
      (Graph.glue (w.reading w.first) (Graph.SingleEdgeContext.edgeContext w.support a b)) ↔
    Graph.HasCycleWithLength data.LengthOK
      (Graph.glue (w.reading w.second) (Graph.SingleEdgeContext.edgeContext w.support a b)))

/-- **A separating single-edge context is never at an adjacent pair, and is a
clause-(b) witness**: at the canonical witness, if the single-edge context
`a — b` (`a ≠ b` in `∂Z`) separates the readings, then `a ≁ b` in G and
`w_ab = (A, B, Z, a — b)` satisfies the clause-(b) specification. -/
noncomputable def SeparatingEdgeContextWitnessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a b : (SupportAtom.boundary object w.support).Vertex, a ≠ b → w.EdgeSeparates a b →
      ¬ object.graph.Adj a.1 b.1 ∧ (w.atEdge a b).Spec

/-- **The spectrum split at a separating single-edge context**: at the
canonical witness, if `a — b` separates the readings, then `a ≁ b`, one reading
`P` is positive and the other `N` negative at `a — b`, and either a reading path
`π : a' → b'` has `|π| + 1` accepted while every `ret_N` path `π'` between the
same labels has `|π'| ≠ |π|` and (if `|π'| ≥ 2`) `|π'| + 1` not accepted, or
every accepted cycle of the positive gluing meets three labels. -/
noncomputable def SeparatingEdgeContextSpectrumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a b : (SupportAtom.boundary object w.support).Vertex, a ≠ b → w.EdgeSeparates a b →
      ¬ object.graph.Adj a.1 b.1 ∧
      ∃ P N : Finset object.Vertex,
        Graph.HasCycleWithLength data.LengthOK
          (Graph.glue (SupportAtom.retainedPiece object w.support P)
            (Graph.SingleEdgeContext.edgeContext w.support a b)) ∧
        ¬ Graph.HasCycleWithLength data.LengthOK
          (Graph.glue (SupportAtom.retainedPiece object w.support N)
            (Graph.SingleEdgeContext.edgeContext w.support a b)) ∧
        ((∃ a' b' : (SupportAtom.boundary object w.support).Vertex, a' ≠ b' ∧
            ∃ π : (SupportAtom.retainedPiece object w.support P).graph.Walk
                (.inl a') (.inl b'), π.IsPath ∧ data.LengthOK (π.length + 1) ∧
            ∀ π' : (SupportAtom.retainedPiece object w.support N).graph.Walk
                (.inl a') (.inl b'), π'.IsPath →
              π'.length ≠ π.length ∧ (1 < π'.length → ¬ data.LengthOK (π'.length + 1))) ∨
          (∀ c : Graph.CycleCertificate
              (Graph.glue (SupportAtom.retainedPiece object w.support P)
                (Graph.SingleEdgeContext.edgeContext w.support a b)) data.LengthOK,
            ∃ x y d : (SupportAtom.boundary object w.support).Vertex,
              x ≠ y ∧ x ≠ d ∧ y ≠ d ∧
              (Sum.inl x : Graph.GluedVertex _
                (Graph.SingleEdgeContext.edgeContext w.support a b)) ∈ c.walk.support ∧
              (Sum.inl y : Graph.GluedVertex _
                (Graph.SingleEdgeContext.edgeContext w.support a b)) ∈ c.walk.support ∧
              (Sum.inl d : Graph.GluedVertex _
                (Graph.SingleEdgeContext.edgeContext w.support a b)) ∈ c.walk.support))

/-- **The swap object of the canonical witness**: the positive reading `P` has
a private edge `xy` (`x, y ∈ P ⊆ Z`, `y ∉ N`, `y` internal to `Z`), and
`G − Priv(P)` (the edges of `G[P]` not in `G[N]` removed) fails the baseline at
a tight endpoint of a private edge. -/
noncomputable def PrivateEdgeSwapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ P N : Finset object.Vertex, w.Orientation P N ∧
      (∃ x y, object.graph.Adj x y ∧ x ∈ P ∧ y ∈ P ∧ y ∉ N ∧
        x ∈ w.support ∧ y ∈ w.support ∧ y ∉ SupportAtom.cutBoundary object w.support) ∧
      ∃ x y, object.graph.Adj x y ∧ x ∈ P ∧ y ∈ P ∧ ¬ (x ∈ N ∧ y ∈ N) ∧
        ∃ v, (v = x ∨ v = y) ∧
          (Graph.EdgeSwitchPaths.spanning object
            (Graph.EdgeSwitchPaths.swapGraph N P)).degree v + 1 ≤ data.threshold ∧
          ¬ Graph.MinimumDegreeAtLeast data.threshold
            (Graph.EdgeSwitchPaths.spanning object (Graph.EdgeSwitchPaths.swapGraph N P))

/-- **The private edge of the positive reading and its switch**: at the
canonical witness there is a private edge `xy` of `P` (`x, y ∈ P ⊆ Z`, `y ∉ N`,
`y` internal) with either both ends at the baseline, both losing the edge in
the swap object (`deg ≤ δ − 1` at `x` and at `y`), or a high end `h`
(`deg ≥ δ + 1`) and a baseline end `c`, with the forced path from `c` of the
switch at `hc`. -/
noncomputable def PrivateEdgeSwitchStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ P N : Finset object.Vertex, w.Orientation P N ∧
      ∃ x y, object.graph.Adj x y ∧ x ∈ P ∧ y ∈ P ∧ y ∉ N ∧
        x ∈ w.support ∧ y ∈ w.support ∧
        y ∉ SupportAtom.cutBoundary object w.support ∧
        ((object.degree x = data.threshold ∧ object.degree y = data.threshold ∧
            (Graph.EdgeSwitchPaths.spanning object
              (Graph.EdgeSwitchPaths.swapGraph N P)).degree x + 1 ≤ data.threshold ∧
            (Graph.EdgeSwitchPaths.spanning object
              (Graph.EdgeSwitchPaths.swapGraph N P)).degree y + 1 ≤ data.threshold) ∨
          ∃ h c, ((h = x ∧ c = y) ∨ (h = y ∧ c = x)) ∧
            data.threshold + 1 ≤ object.degree h ∧ object.degree c = data.threshold ∧
            ((data.threshold + 2 ≤ object.degree h ∧ ∃ u, object.graph.Adj h u ∧ u ≠ c ∧
                ¬ object.graph.Adj c u ∧
                ∃ p : (object.graph.deleteEdges {s(h, c), s(h, u)}).Walk c u,
                  p.IsPath ∧ data.LengthOK (p.length + 1)) ∨
              ∃ h₂ u₂, h₂ ≠ h ∧ data.threshold + 1 ≤ object.degree h₂ ∧
                object.graph.Adj u₂ h₂ ∧ u₂ ≠ c ∧ ¬ object.graph.Adj c u₂ ∧
                ∃ p : (object.graph.deleteEdges {s(c, h), s(u₂, h₂)}).Walk c u₂,
                  p.IsPath ∧ data.LengthOK (p.length + 1)))

/-- **Every baseline label has an outside return**: at the canonical witness,
every `a ∈ ∂Z` of degree `δ` is joined to another `b' ∈ ∂Z` by a path `τ` of
length `≥ 2` with interior in `V ∖ Z`. -/
noncomputable def CubicLabelOutsidePathStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a ∈ SupportAtom.cutBoundary object w.support, object.degree a = data.threshold →
      ∃ b' ∈ SupportAtom.cutBoundary object w.support, b' ≠ a ∧
        ∃ τ : object.graph.Walk a b', τ.IsPath ∧
          (∀ x ∈ τ.support, x ∉ w.support ∨ x = a ∨ x = b') ∧ 2 ≤ τ.length

open Classical in
/-- **`|∂Z| = 2` with a baseline label: outside paths in both orientations**:
if `∂Z = {x, y}` and one of `x, y` has degree `δ`, then G has paths `x → y`
and `y → x` of length `≥ 2` with interior in `V ∖ Z`. -/
noncomputable def TwoBoundaryOutsideBothStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ x y, x ≠ y → SupportAtom.cutBoundary object w.support = {x, y} →
      (object.degree x = data.threshold ∨ object.degree y = data.threshold) →
      (∃ τ : object.graph.Walk x y, τ.IsPath ∧
        (∀ v ∈ τ.support, v ∉ w.support ∨ v = x ∨ v = y) ∧ 2 ≤ τ.length) ∧
      (∃ τ : object.graph.Walk y x, τ.IsPath ∧
        (∀ v ∈ τ.support, v ∉ w.support ∨ v = y ∨ v = x) ∧ 2 ≤ τ.length)

end Hypostructure.Graph.Strategy.Spine
