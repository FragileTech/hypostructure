import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Statements.CanonicalCapacityExplicit
import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.Statements.TypeBLanes
import Hypostructure.Graph.Statements.CanonicalPairHandoff
import Hypostructure.Graph.GluedReadingMaps
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.ObjectCapacityLedger

/-!
# Statements: the strict-surplus named sparse exit `[20a]`, made explicit

Node `[20a]` (thm:main (i), tex 339-346) returns G with the strict surplus
`σ > C_sp⌈√n⌉` and the target-defective identification of `[125]` pinned to
G's one canonical witness `w = (first, second, Z, O)`
(`sparseTargetDefectWitness`).  The statements below are the bounds, ratios,
identities and obstructions that the residual's own facts force at G; each is
a fact about G and its fixed objects (the canonical witness, the canonical
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

/-- The high-degree vertices `H = {deg ≠ δ}` of G. -/
noncomputable abbrev sparseHighDegreeCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  letI : FinEnum object.Vertex := object.vertices
  (Finset.univ.filter fun v => object.degree v ≠ data.threshold).card

/-- The darts of G with both ends at the baseline degree. -/
noncomputable abbrev sparseLowDartCount (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  (Finset.univ.filter fun d : object.graph.Dart =>
    object.degree d.fst = data.threshold ∧ object.degree d.snd = data.threshold).card

/-! ## The single budget -/

/-- **Edge–surplus identity**: `2m = δ·n + σ`. -/
def EdgeSurplusIdentityStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  2 * object.edgeCount = data.threshold * object.vertexCount +
    object.degreeSurplus data.threshold

/-- **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`:
`σ + 6|H| + lowDarts = 3n`). -/
def SurplusDartIdentityStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  object.degreeSurplus data.threshold + 2 * data.threshold * sparseHighDegreeCount data object +
      sparseLowDartCount data object =
    data.threshold * object.vertexCount

/-- **High-degree count**: `|H| ≤ σ`. -/
def HighDegreeCountBoundStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  sparseHighDegreeCount data object ≤ object.degreeSurplus data.threshold

/-- **At least one high-degree vertex**: `1 ≤ |H|`. -/
def HighDegreePositiveStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  1 ≤ sparseHighDegreeCount data object

/-- **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every
high vertex has all its neighbours among the `n − |H|` baseline vertices). -/
def HighDegreeSurplusCapacityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  object.degreeSurplus data.threshold ≤ sparseHighDegreeCount data object *
    (object.vertexCount - sparseHighDegreeCount data object - data.threshold)

/-- **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`). -/
noncomputable def PackingOrderBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  data.windowOrder * (canonicalWindowPacking data object).card ≤ object.vertexCount

/-- **`C + 1 ≤ ⌈√n⌉`.** -/
def CeilSqrtAboveScaleStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  data.spineScale + 1 ≤ Core.ceilSqrt object.vertexCount

/-- **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`). -/
def OrderAboveScaleSquareStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  data.spineScale * (data.spineScale + 1) + 9 ≤ object.vertexCount

/-! ## The order of G (K4) -/

/-! ## The envelope (K5) -/

/-- **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`. -/
def SixVertexExtremalEnvelopeStatement (object : Graph.FiniteObject.{u}) : Prop :=
  object.edgeCount + 4 ≤ 2 * object.vertexCount

/-! ## The capacity presentations of G (K6) -/

/-! ## The canonical witness (A26–A39) -/

/-- **The readings are not target-complete.** -/
noncomputable def WitnessReadingsNotTargetCompleteStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ¬ Graph.Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile
      (Graph.HasCycleWithLength data.LengthOK) (w.reading w.first) (w.reading w.second)

/-- **Neither reading has an accepted cycle at `G − Z`.** -/
noncomputable def WitnessActualOutsideNegativeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (w.reading w.first) (SupportAtom.outside object w.support)) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (w.reading w.second) (SupportAtom.outside object w.support))

/-- **Both reading pieces are cycle-free** (each embeds in G). -/
noncomputable def WitnessReadingsCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ¬ Graph.HasCycleWithLength data.LengthOK (w.reading w.first).pack ∧
      ¬ Graph.HasCycleWithLength data.LengthOK (w.reading w.second).pack

/-- **`|Z| + 1 ≤ n`.** -/
noncomputable def WitnessSupportOrderBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => w.support.card + 1 ≤ object.vertexCount

/-- **No reading's gluing with `G − Z` is a lexicographically smaller
baseline object** (¬K3). -/
noncomputable def WitnessReadingGluesNotSmallerBaselineStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ X ∈ w.pairSupports,
      ¬ (Graph.MinimumDegreeAtLeast data.threshold
            (Graph.glue (SupportAtom.retainedPiece object w.support X)
              (SupportAtom.outside object w.support)) ∧
          (Graph.glue (SupportAtom.retainedPiece object w.support X)
            (SupportAtom.outside object w.support)).LexicographicallySmaller object)

/-- **Exit (e) is excluded at G**: no open-port suppression cycle has an
accepted lifted length `|walk| + |chords|`. -/
def NoSuppressionChordViolationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (tvs : Graph.TightVertexSuppression.CompatibleFamily object)
    (certificate : Graph.CycleCertificate tvs.suppressed data.LengthOK),
    ¬ data.LengthOK (certificate.walk.length + (tvs.usedChords certificate.walk).card)

/-! ## Contexts realized in G (K1) -/

/-- **`O` is not realized in `G − Z`.** -/
noncomputable def WitnessOutsideNotRealizedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    IsEmpty (Graph.GluedReadings.RealizedIn w.outside)

/-- **Both readings are negative in every context realized in `G − Z`.** -/
noncomputable def RealizedContextsNegativeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ O' : Graph.OutsideContext (SupportAtom.boundary object w.support),
      Nonempty (Graph.GluedReadings.RealizedIn O') →
        ¬ Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading w.first) O') ∧
          ¬ Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading w.second) O')

/-- **No negative sub-gluing is a lexicographically smaller baseline object**:
the negative reading `N` at `O`, against every sub-context `O' ≤ O`. -/
noncomputable def NegativeSubGluingNotSmallerBaselineStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ N ∈ w.pairSupports,
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w.support N) w.outside) ∧
      ∀ g ≤ w.outside.graph,
        ¬ (Graph.MinimumDegreeAtLeast data.threshold
              (Graph.glue (SupportAtom.retainedPiece object w.support N)
                (Graph.GluedReadings.subContext w.outside g)) ∧
            (Graph.glue (SupportAtom.retainedPiece object w.support N)
              (Graph.GluedReadings.subContext w.outside g)).LexicographicallySmaller object)

/-- **The O-part of one positive cycle still separates**: a sub-context
`O' ≤ O` with `P` positive and `N` negative, every `O'`-internal vertex of
`O'`-degree at most `2`, and `glue N O'` not a baseline object. -/
noncomputable def CycleSubContextSeparatesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ P ∈ w.pairSupports, ∃ N ∈ w.pairSupports, ∃ g ≤ w.outside.graph,
      Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w.support P)
          (Graph.GluedReadings.subContext w.outside g)) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w.support N)
          (Graph.GluedReadings.subContext w.outside g)) ∧
      (∀ o : w.outside.Internal,
        (Graph.GluedReadings.subContext w.outside g).pack.degree (.inr o) ≤ 2) ∧
      ¬ Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (SupportAtom.retainedPiece object w.support N)
          (Graph.GluedReadings.subContext w.outside g))

/-- Arm (i) of the path-spectrum split at the witness: the positive reading
`P` and the negative reading `N` at `O`, labels `a ≠ b` of `∂Z`, a path
`π : a → b` of `ret_P` and an `O`-path `σ : b → a` meeting no other label with
`|π| + |σ| = 2^k` (`k ≥ 2`), and every `a → b` path `π'` of `ret_N` has
`|π'| ≠ |π|` and `|π'| + |σ| ≠ 2^j` (`j ≥ 2`). -/
noncomputable abbrev SparseTargetDefectWitness.SpectrumArmOne {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object) : Prop :=
  ∃ P ∈ w.pairSupports, ∃ N ∈ w.pairSupports,
    Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w.support P) w.outside) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w.support N) w.outside) ∧
    ∃ a b : (SupportAtom.boundary object w.support).Vertex, a ≠ b ∧
      ∃ π : (SupportAtom.retainedPiece object w.support P).graph.Walk (.inl a) (.inl b),
        π.IsPath ∧
      ∃ σ : w.outside.graph.Walk (.inl b) (.inl a), σ.IsPath ∧
        (∀ d, (Sum.inl d : _ ⊕ w.outside.Internal) ∈ σ.support → d = a ∨ d = b) ∧
        (∃ k, 2 ≤ k ∧ π.length + σ.length = 2 ^ k) ∧
        ∀ π' : (SupportAtom.retainedPiece object w.support N).graph.Walk (.inl a) (.inl b),
          π'.IsPath → π'.length ≠ π.length ∧ ∀ j, 2 ≤ j → π'.length + σ.length ≠ 2 ^ j

/-- **The path-length spectrum split** at the witness: for the positive
reading `P` and the negative reading `N` at `O`, either (i) labels `a ≠ b` of
`∂Z`, a path `π : a → b` of `ret_P` and an `O`-path `σ : b → a` meeting no
other label with `|π| + |σ| = 2^k` (`k ≥ 2`), such that every `a → b` path
`π'` of `ret_N` has `|π'| ≠ |π|` and `|π'| + |σ| ≠ 2^j` for every `j ≥ 2`; or
(ii) every accepted cycle of `glue ret_P O` meets three distinct labels. -/
noncomputable def PathSpectrumSplitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ P ∈ w.pairSupports, ∃ N ∈ w.pairSupports,
      Graph.HasCycleWithLength data.LengthOK
          (Graph.glue (SupportAtom.retainedPiece object w.support P) w.outside) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
          (Graph.glue (SupportAtom.retainedPiece object w.support N) w.outside) ∧
      ((∃ a b : (SupportAtom.boundary object w.support).Vertex, a ≠ b ∧
          ∃ π : (SupportAtom.retainedPiece object w.support P).graph.Walk
              (.inl a) (.inl b), π.IsPath ∧
          ∃ σ : w.outside.graph.Walk (.inl b) (.inl a), σ.IsPath ∧
            (∀ d, (Sum.inl d : _ ⊕ w.outside.Internal) ∈ σ.support → d = a ∨ d = b) ∧
            (∃ k, 2 ≤ k ∧ π.length + σ.length = 2 ^ k) ∧
            ∀ π' : (SupportAtom.retainedPiece object w.support N).graph.Walk
                (.inl a) (.inl b), π'.IsPath →
              π'.length ≠ π.length ∧ ∀ j, 2 ≤ j → π'.length + σ.length ≠ 2 ^ j) ∨
        (∀ c : Graph.CycleCertificate
            (Graph.glue (SupportAtom.retainedPiece object w.support P) w.outside)
            data.LengthOK,
          ∃ a b d : (SupportAtom.boundary object w.support).Vertex,
            a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
            (Sum.inl a : Graph.GluedVertex _ w.outside) ∈ c.walk.support ∧
            (Sum.inl b : Graph.GluedVertex _ w.outside) ∈ c.walk.support ∧
            (Sum.inl d : Graph.GluedVertex _ w.outside) ∈ c.walk.support))


/-! ## Admissible quotients of G (K7) -/

/-! ## Admissible quotients of G (K7) -/

/-- **Every admissible quotient of G is label-injective** on its family. -/
def AdmissibleQuotientsLabelInjectiveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ {Coordinate : Type u} (family : Finset Coordinate)
    (cs : Coordinate → Finset object.Vertex)
    (q : Graph.DeclaredQuotient (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object family cs),
    Set.InjOn q.label ↑family

/-! ## The boundary of the canonical support (K2) -/

section BoundaryStatements

open Classical


/-- **The one-boundary shape**: every support `S` with a single boundary vertex
`b`, a second vertex and a vertex outside has `b` with exactly two neighbours
in `S` and two outside (`deg b = 4`, a 2+2 cut vertex). -/
def SingleBoundaryShapeStatement (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (S : Finset object.Vertex) (b : object.Vertex),
    SupportAtom.cutBoundary object S = {b} →
    ∀ z ∈ S, z ≠ b → (∃ x, x ∉ S) →
      (by classical exact (object.vertexFinset.filter fun y =>
          object.graph.Adj b y ∧ y ∈ S).card) = 2 ∧
      (by classical exact (object.vertexFinset.filter fun y =>
          object.graph.Adj b y ∧ y ∉ S).card) = 2

/-- **`2 ≤ |∂Z ∩ X⁺|`** for one declared support `X⁺ ∈ {A, B}`. -/
noncomputable def PositiveSupportBoundaryTwoStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    (by classical exact 2 ≤ (SupportAtom.cutBoundary object w.support ∩
        sparseDeclaredSupport data object w.first).card) ∨
      (by classical exact 2 ≤ (SupportAtom.cutBoundary object w.support ∩
        sparseDeclaredSupport data object w.second).card)

/-- The number of edges from `∂Z` to `V ∖ Z`. -/
noncomputable abbrev supportCutEdgeCount (object : Graph.FiniteObject.{u})
    (Z : Finset object.Vertex) : Nat := by
  classical
  exact ∑ v ∈ SupportAtom.cutBoundary object Z,
    (object.vertexFinset.filter fun y => object.graph.Adj v y ∧ y ∉ Z).card

/-- **`2 ≤ e(∂Z, V ∖ Z)`.** -/
noncomputable def SupportCutEdgesTwoStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    2 ≤ supportCutEdgeCount object w.support

/-- **A boundary vertex with at most two neighbours in `Z`.** -/
noncomputable def BoundaryLowInsideVertexStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ b ∈ SupportAtom.cutBoundary object w.support, object.internalDegree w.support b ≤ 2

/-- **An outside vertex with at most two outside neighbours and a neighbour in
`Z`.** -/
noncomputable def OutsideLowVertexStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∃ x, x ∉ w.support ∧
      (by classical exact (object.vertexFinset.filter fun y =>
        object.graph.Adj x y ∧ y ∉ w.support).card) ≤ 2 ∧
      ∃ y ∈ w.support, object.graph.Adj x y

/-- **`∂Z = {a, b}` with an interior vertex: one terminal has at most two
neighbours in `T' = (V ∖ Z) ∪ {a, b}`.** -/
noncomputable def TwoBoundaryLowOutsideSideStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a b : object.Vertex, SupportAtom.cutBoundary object w.support = {a, b} →
      (∃ i ∈ w.support, i ∉ SupportAtom.cutBoundary object w.support) →
      object.internalDegree (Graph.GluedReadings.outsideSide object w.support a b) a ≤ 2 ∨
        object.internalDegree (Graph.GluedReadings.outsideSide object w.support a b) b ≤ 2

/-- **2-sum closure on the `Z` side**: if `a ≁ b` and both have two
neighbours in `Z`, then `G[Z]` has an `a`–`b` path `P` with `|P| + 1`
accepted. -/
noncomputable def TwoBoundarySupportClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a b : object.Vertex, a ≠ b → SupportAtom.cutBoundary object w.support = {a, b} →
      ¬ object.graph.Adj a b →
      2 ≤ object.internalDegree w.support a → 2 ≤ object.internalDegree w.support b →
      ∃ p : object.graph.Walk a b, p.IsPath ∧ (∀ v ∈ p.support, v ∈ w.support) ∧
        data.LengthOK (p.length + 1)

/-- **2-sum closure on the outside side** (interior arm). -/
noncomputable def TwoBoundaryOutsideClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a b : object.Vertex, a ≠ b → SupportAtom.cutBoundary object w.support = {a, b} →
      (∃ i ∈ w.support, i ∉ SupportAtom.cutBoundary object w.support) →
      ¬ object.graph.Adj a b →
      2 ≤ object.internalDegree (Graph.GluedReadings.outsideSide object w.support a b) a →
      2 ≤ object.internalDegree (Graph.GluedReadings.outsideSide object w.support a b) b →
      ∃ q : object.graph.Walk a b, q.IsPath ∧
        (∀ v ∈ q.support, v ∈ Graph.GluedReadings.outsideSide object w.support a b) ∧
        data.LengthOK (q.length + 1)

/-- **The length-set constraint at `∂Z = {a, b}`**: an `a`–`b` path in `Z`
and a `b`–`a` path in `T'` (not both single edges) never sum to an accepted
length. -/
noncomputable def TwoBoundaryNoTargetSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ a b : object.Vertex, SupportAtom.cutBoundary object w.support = {a, b} →
      ∀ (p : object.graph.Walk a b), p.IsPath → (∀ v ∈ p.support, v ∈ w.support) →
      ∀ (q : object.graph.Walk b a), q.IsPath →
        (∀ v ∈ q.support, v ∈ Graph.GluedReadings.outsideSide object w.support a b) →
        (1 < p.length ∨ 1 < q.length) → ¬ data.LengthOK (p.length + q.length)

/-- The outside `W = V ∖ Z` of a support. -/
noncomputable abbrev supportOutside (object : Graph.FiniteObject.{u})
    (Z : Finset object.Vertex) : Finset object.Vertex := by
  classical
  exact object.vertexFinset.filter fun y => y ∉ Z

/-- **`2 ≤ |W|` or `3 ≤ |∂Z|`.** -/
noncomputable def OutsideOrBoundaryLargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    2 ≤ (supportOutside object w.support).card ∨
      3 ≤ (SupportAtom.cutBoundary object w.support).card

/-! ## The compression route at G's own pieces (K3) -/

/-- **Every G-edge a reading drops at `G − Z` has an endpoint below the
baseline there.** -/
noncomputable def DroppedEdgeTightDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ X ∈ w.pairSupports,
      ∀ a b : (Graph.glue (SupportAtom.retainedPiece object w.support X)
          (SupportAtom.outside object w.support)).Vertex,
        object.graph.Adj (Graph.GluedReadings.retainedGlueHom w.support X a)
          (Graph.GluedReadings.retainedGlueHom w.support X b) →
        ¬ (Graph.glue (SupportAtom.retainedPiece object w.support X)
            (SupportAtom.outside object w.support)).graph.Adj a b →
        (Graph.glue (SupportAtom.retainedPiece object w.support X)
            (SupportAtom.outside object w.support)).degree a < data.threshold ∨
          (Graph.glue (SupportAtom.retainedPiece object w.support X)
            (SupportAtom.outside object w.support)).degree b < data.threshold

/-- **At most one reading is whole**: `¬ (Z ⊆ A ∧ Z ⊆ B)`. -/
noncomputable def NotBothReadingsWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ¬ (w.support ⊆ sparseDeclaredSupport data object w.first ∧
        w.support ⊆ sparseDeclaredSupport data object w.second)

/-! The whole-case facts with `X` the whole reading and `Y` the other one. -/
section WholeCase

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- `Z ⊆ X ⇒` `ret_X` positive and `ret_Y` negative at `O`. -/
noncomputable abbrev WholeOrientation (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading x) w.outside) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading y) w.outside)

/-- `Z ⊆ X ⇒ 1 ≤ |Z ∖ Y|`. -/
noncomputable abbrev WholeDeficitNonempty (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    1 ≤ (by classical exact (w.support \ sparseDeclaredSupport data object y).card)

/-- `Z ⊆ X ⇒` every `s ∈ Z ∖ Y` is internal, has no `∂Z`-neighbour, and is
isolated in every gluing of `ret_Y`. -/
noncomputable abbrev WholeDeficitStructure (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    ∀ s ∈ w.support, s ∉ sparseDeclaredSupport data object y →
      s ∉ SupportAtom.cutBoundary object w.support ∧
      (∀ b ∈ SupportAtom.cutBoundary object w.support, ¬ object.graph.Adj s b) ∧
      ∃ i : SupportAtom.PieceInternal object w.support, i.1 = s ∧
        ∀ O' : Graph.OutsideContext (SupportAtom.boundary object w.support),
          (Graph.glue (w.reading y) O').degree (.inr (.inl i)) = 0

/-- `Z ⊆ X ⇒` no gluing of `ret_Y` has the baseline. -/
noncomputable abbrev WholeNoBaseline (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    ∀ O' : Graph.OutsideContext (SupportAtom.boundary object w.support),
      ¬ Graph.MinimumDegreeAtLeast data.threshold (Graph.glue (w.reading y) O')

/-- `Z ⊆ X ⇒` every gluing of `ret_Y` has at least `|Z ∖ Y|` isolated
vertices. -/
noncomputable abbrev WholeIsolatedCount (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    ∀ O' : Graph.OutsideContext (SupportAtom.boundary object w.support),
      letI : FinEnum (Graph.glue (w.reading y) O').Vertex :=
        (Graph.glue (w.reading y) O').vertices
      (by classical exact (w.support \ sparseDeclaredSupport data object y).card) ≤
        (Finset.univ.filter fun v => (Graph.glue (w.reading y) O').degree v = 0).card

/-- `Z ⊆ X ⇒` every gluing of `ret_Y` has total degree deficit
`Σ_v (δ − deg v) ≥ δ·|Z ∖ Y|`. -/
noncomputable abbrev WholeDeficitSum (w : SparseTargetDefectWitness data object)
    (x y : SparseDeclaredCoordinate data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object x →
    ∀ O' : Graph.OutsideContext (SupportAtom.boundary object w.support),
      letI : FinEnum (Graph.glue (w.reading y) O').Vertex :=
        (Graph.glue (w.reading y) O').vertices
      data.threshold * (by classical exact (w.support \ sparseDeclaredSupport data object y).card) ≤
        Finset.univ.sum fun v => data.threshold - (Graph.glue (w.reading y) O').degree v

end WholeCase

/-- **Whole case `Z ⊆ A`: `A` positive and `B` negative at `O`.** -/
noncomputable def FirstWholeOrientationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeOrientation w w.first w.second

/-- **Whole case `Z ⊆ A`: `1 ≤ |Z ∖ B|`.** -/
noncomputable def FirstWholeDeficitNonemptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeDeficitNonempty w w.first w.second

/-- **Whole case `Z ⊆ A`: the deficit set `Z ∖ B` is internal, has no
`∂Z`-neighbour, and is isolated in every gluing of `ret_B`.** -/
noncomputable def FirstWholeDeficitStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeDeficitStructure w w.first w.second

/-- **Whole case `Z ⊆ A`: `δ·|Z ∖ B| ≤ Σ (δ − deg)` in every gluing of
`ret_B`.** -/
noncomputable def FirstWholeDeficitSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeDeficitSum w w.first w.second

/-- **Whole case `Z ⊆ B`: `B` positive and `A` negative at `O`.** -/
noncomputable def SecondWholeOrientationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeOrientation w w.second w.first

/-- **Whole case `Z ⊆ B`: `1 ≤ |Z ∖ A|`.** -/
noncomputable def SecondWholeDeficitNonemptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeDeficitNonempty w w.second w.first

/-- **Whole case `Z ⊆ B`: the deficit set `Z ∖ A` is internal, has no
`∂Z`-neighbour, and is isolated in every gluing of `ret_A`.** -/
noncomputable def SecondWholeDeficitStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeDeficitStructure w w.second w.first

/-- **Whole case `Z ⊆ B`: `δ·|Z ∖ A| ≤ Σ (δ − deg)` in every gluing of
`ret_A`.** -/
noncomputable def SecondWholeDeficitSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => WholeDeficitSum w w.second w.first


/-! ## Deleting the deficit set, and the keeps-all split (K3, continued) -/

/-- The whole-case deficit set `S = Z ∖ B`. -/
noncomputable abbrev wholeDeletedSet {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Finset object.Vertex :=
  w.support \ sparseDeclaredSupport data object w.second

/-- Its complement `T = V ∖ S`. -/
noncomputable abbrev wholeKeptSet {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Finset object.Vertex :=
  object.vertexFinset \ wholeDeletedSet w

/-- **Whole case (`Z ⊆ A` with `S = Z ∖ B`, and `Z ⊆ B` with `S = Z ∖ A`):
`G − S` is lexicographically smaller than G, has no accepted cycle, and fails
`δ ≥ 3`.** -/
noncomputable abbrev DeletedSupportReductionAt {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
      (object.induce (wholeKeptSet w)).LexicographicallySmaller object ∧
      ¬ Graph.HasCycleWithLength data.LengthOK (object.induce (wholeKeptSet w)) ∧
      ¬ Graph.MinimumDegreeAtLeast 3 (object.induce (wholeKeptSet w))

noncomputable def DeletedSupportReductionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => DeletedSupportReductionAt w ∧ DeletedSupportReductionAt w.swap

/-- **Whole case: a deficient vertex of `G − S` exists, and every one lies in
`Z ∩ B`, is internal to `Z`, and has a neighbour in `S`.** -/
noncomputable abbrev DeletedSupportDeficientVertexAt {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
      (∃ v ∈ wholeKeptSet w, object.localDegree (wholeKeptSet w) v < 3) ∧
      (∀ v ∈ wholeKeptSet w, object.localDegree (wholeKeptSet w) v < 3 →
        v ∈ w.support ∧ v ∈ sparseDeclaredSupport data object w.second ∧
        v ∉ SupportAtom.cutBoundary object w.support ∧
        1 ≤ object.localDegree (wholeDeletedSet w) v)

noncomputable def DeletedSupportDeficientVertexStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => DeletedSupportDeficientVertexAt w ∧ DeletedSupportDeficientVertexAt w.swap

/-- **Whole case: the deficit sums**
`1 ≤ Σ_T (3 − deg_{G−S}) = Σ_T (d_S − (deg − 3)) ≤ e(S, T)`, with equality
`= e(S, T)` when every `T`-neighbour of `S` has degree `3`. -/
noncomputable abbrev DeletedSupportDeficitSumsAt {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
      1 ≤ (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) ∧
      (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) =
        (wholeKeptSet w).sum
          (fun v => object.localDegree (wholeDeletedSet w) v - (object.degree v - 3)) ∧
      (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) ≤
        (wholeKeptSet w).sum (fun v => object.localDegree (wholeDeletedSet w) v) ∧
      ((∀ v ∈ wholeKeptSet w, 0 < object.localDegree (wholeDeletedSet w) v →
          object.degree v = 3) →
        (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) =
          (wholeKeptSet w).sum (fun v => object.localDegree (wholeDeletedSet w) v))

noncomputable def DeletedSupportDeficitSumsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => DeletedSupportDeficitSumsAt w ∧ DeletedSupportDeficitSumsAt w.swap

/-- **Whole case: one restoring edge forces an accepted closing path**: if
adding `xy` to `G − S` restores `δ ≥ 3`, then `G − S` has a `y → x` path of
length `ℓ` with `ℓ + 1` accepted. -/
noncomputable abbrev DeletedSupportEdgeRestorationAt {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
      ∀ x y : (object.induce (wholeKeptSet w)).Vertex, x ≠ y →
        Graph.MinimumDegreeAtLeast 3
          (Graph.GluedReadings.addEdgeObj (object.induce (wholeKeptSet w)) x y) →
        ∃ p : (object.induce (wholeKeptSet w)).graph.Walk y x, p.IsPath ∧
          data.LengthOK (p.length + 1)

noncomputable def DeletedSupportEdgeRestorationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => DeletedSupportEdgeRestorationAt w ∧ DeletedSupportEdgeRestorationAt w.swap

/-- **Whole case: any restoring edge set forces an accepted cycle through a
new edge.** -/
noncomputable abbrev DeletedSupportEdgeSetRestorationAt {data : Parameters} {object : Graph.FiniteObject.{u}}
    (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
      ∀ F : SimpleGraph (object.induce (wholeKeptSet w)).Vertex,
        Graph.MinimumDegreeAtLeast 3
          (Graph.GluedReadings.addEdgesObj (object.induce (wholeKeptSet w)) F) →
        ∃ c : Graph.CycleCertificate
            (Graph.GluedReadings.addEdgesObj (object.induce (wholeKeptSet w)) F) data.LengthOK,
          ∃ e ∈ c.walk.edges, e ∈ F.edgeSet ∧ e ∉ (object.induce (wholeKeptSet w)).graph.edgeSet

noncomputable def DeletedSupportEdgeSetRestorationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w => DeletedSupportEdgeSetRestorationAt w ∧ DeletedSupportEdgeSetRestorationAt w.swap

/-- **Keeps-all for `A` with `Z ⊄ A`**: `Z ⊄ B`, and both readings' profiles
differ from the whole piece's. -/
noncomputable def FirstKeepsAllNotWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    Graph.GluedReadings.KeepsAll w.support (sparseDeclaredSupport data object w.first) →
    ¬ w.support ⊆ sparseDeclaredSupport data object w.first →
      ¬ w.support ⊆ sparseDeclaredSupport data object w.second ∧
      (w.reading w.first).boundaryDegreeProfile ≠
        (SupportAtom.piece object w.support).boundaryDegreeProfile ∧
      (w.reading w.second).boundaryDegreeProfile ≠
        (SupportAtom.piece object w.support).boundaryDegreeProfile

/-- **Keeps-all for `B` with `Z ⊄ B`**: `Z ⊄ A`, and both readings' profiles
differ from the whole piece's. -/
noncomputable def SecondKeepsAllNotWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    Graph.GluedReadings.KeepsAll w.support (sparseDeclaredSupport data object w.second) →
    ¬ w.support ⊆ sparseDeclaredSupport data object w.second →
      ¬ w.support ⊆ sparseDeclaredSupport data object w.first ∧
      (w.reading w.second).boundaryDegreeProfile ≠
        (SupportAtom.piece object w.support).boundaryDegreeProfile ∧
      (w.reading w.first).boundaryDegreeProfile ≠
        (SupportAtom.piece object w.support).boundaryDegreeProfile

/-- **The pair arm does not occur**: `¬ (∂Z = Z = {a, b})` (equal profiles
on a two-vertex all-boundary support force equal readings, against the
separation at `O`). -/
noncomputable def PairArmExcludedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ¬ ∃ a b, SupportAtom.cutBoundary object w.support = {a, b} ∧ w.support = {a, b}

/-- **`|∂Z| = 2` forces arm (i) of the spectrum split**, `∂Z = {a, b}` inside
one declared support, an interior vertex of `Z`, and `{a, b}` separating the
interior from `V ∖ Z`. -/
noncomputable def TwoBoundaryForcesArmOneStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    (SupportAtom.cutBoundary object w.support).card = 2 →
    w.SpectrumArmOne ∧
    ∃ a b, a ≠ b ∧ SupportAtom.cutBoundary object w.support = {a, b} ∧
      ({a, b} ⊆ sparseDeclaredSupport data object w.first ∨
        {a, b} ⊆ sparseDeclaredSupport data object w.second) ∧
      (∃ i ∈ w.support, i ∉ SupportAtom.cutBoundary object w.support) ∧
      ∀ i ∈ w.support, i ∉ SupportAtom.cutBoundary object w.support →
        ∀ x, x ∉ w.support → ∀ walk : object.graph.Walk i x,
          a ∈ walk.support ∨ b ∈ walk.support

/-- **Arm (i) gives a forced path in `G[Z]`**: a simple `a–b` path `p` of
`G[Z]` between two boundary vertices with `|p| + 1 ≤ |Z|` and `|p| + s = 2^k`
(`k ≥ 2`, `s ≥ 1`, `(|p| + s) % 4 = 0`). -/
noncomputable def ArmOneForcedPathStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    w.SpectrumArmOne →
    ∃ a b : object.Vertex, a ≠ b ∧
      a ∈ SupportAtom.cutBoundary object w.support ∧
      b ∈ SupportAtom.cutBoundary object w.support ∧
      ∃ p : object.graph.Walk a b, p.IsPath ∧
        (∀ v ∈ p.support, v ∈ w.support) ∧ p.length + 1 ≤ w.support.card ∧
        ∃ s k, 2 ≤ k ∧ p.length + s = 2 ^ k ∧ 1 ≤ s ∧ (p.length + s) % 4 = 0

/-- **`|∂Z| = 2`, the K1 × K2 cross constraint**: `∂Z = {a, b}` carries the
forced path `p ⊆ G[Z]` (`|p| + s = 2^k`); no simple `b → a` path `q` in
`T' = (V ∖ Z) ∪ {a, b}` (not both single edges) has `|p| + |q|` accepted; and
if `a ≁ b` with both terminals of `T'`-degree `≥ 2`, the outside closure `q`
exists with `|q| + 1` accepted and `|p| + |q|` not accepted. -/
noncomputable def TwoBoundaryForcedPathCrossStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    (SupportAtom.cutBoundary object w.support).card = 2 →
    ∃ a b : object.Vertex, a ≠ b ∧ SupportAtom.cutBoundary object w.support = {a, b} ∧
      ∃ p : object.graph.Walk a b, p.IsPath ∧ (∀ v ∈ p.support, v ∈ w.support) ∧
        (∃ s k, 2 ≤ k ∧ p.length + s = 2 ^ k ∧ 1 ≤ s) ∧
        (∀ q : object.graph.Walk b a, q.IsPath →
          (∀ v ∈ q.support, v ∈ Graph.GluedReadings.outsideSide object w.support a b) →
          (1 < p.length ∨ 1 < q.length) → ¬ data.LengthOK (p.length + q.length)) ∧
        (¬ object.graph.Adj a b →
          2 ≤ object.internalDegree (Graph.GluedReadings.outsideSide object w.support a b) a →
          2 ≤ object.internalDegree (Graph.GluedReadings.outsideSide object w.support a b) b →
          ∃ q : object.graph.Walk b a, q.IsPath ∧ data.LengthOK (q.length + 1) ∧
            ¬ data.LengthOK (p.length + q.length))

/-- **`Z` is a minimum connected set containing `A ∪ B`.** -/
noncomputable def SupportSteinerMinimalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ Y : Finset object.Vertex,
      (∀ v, v ∈ sparseDeclaredSupport data object w.first ∨
        v ∈ sparseDeclaredSupport data object w.second → v ∈ Y) →
      Graph.SupportComponents.Connected.ConnectedOn object Y → w.support.card ≤ Y.card

/-- **Every vertex of `Z ∖ (A ∪ B)` is a cut vertex of `G[Z]`.** -/
noncomputable def SteinerVerticesCutStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    ∀ v ∈ w.support, v ∉ sparseDeclaredSupport data object w.first →
      v ∉ sparseDeclaredSupport data object w.second →
      ¬ Graph.SupportComponents.Connected.ConnectedOn object (w.support.erase v)

/-- **The whole case pins `Z`**: `Z ⊆ A ⇒ Z = A ∧ B ⊆ A`, and `Z ⊆ B ⇒ Z = B ∧ A ⊆ B`. -/
noncomputable def WholeSupportEqualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    (w.support ⊆ sparseDeclaredSupport data object w.first →
      w.support = sparseDeclaredSupport data object w.first ∧
        sparseDeclaredSupport data object w.second ⊆ sparseDeclaredSupport data object w.first) ∧
    (w.support ⊆ sparseDeclaredSupport data object w.second →
      w.support = sparseDeclaredSupport data object w.second ∧
        sparseDeclaredSupport data object w.first ⊆ sparseDeclaredSupport data object w.second)

/-- The whole-case count `|S| + |∂Z| ≤ |Z|` at one orientation. -/
noncomputable abbrev WholeDeficitBoundaryCountAt {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
    (wholeDeletedSet w).card + (SupportAtom.cutBoundary object w.support).card ≤ w.support.card

/-- **Whole case: `|S| + |∂Z| ≤ |Z|`** (`S = Z ∖ B` resp. `Z ∖ A`). -/
noncomputable def WholeDeficitBoundaryCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    WholeDeficitBoundaryCountAt w ∧ WholeDeficitBoundaryCountAt w.swap

/-- The whole-case cut bound `e(S, T) ≤ D_T + σ` at one orientation. -/
noncomputable abbrev WholeCutEdgeSurplusBoundAt {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object) : Prop :=
  w.support ⊆ sparseDeclaredSupport data object w.first →
    (wholeKeptSet w).sum (fun v => object.localDegree (wholeDeletedSet w) v) ≤
      (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) +
        object.degreeSurplus data.threshold

/-- **Whole case: `e(S, T) ≤ D_T + σ`**, with `D_T = Σ_T (3 − deg_{G−S})`. -/
noncomputable def WholeCutEdgeSurplusBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object fun w =>
    WholeCutEdgeSurplusBoundAt w ∧ WholeCutEdgeSurplusBoundAt w.swap

end BoundaryStatements

/-! ## The window packing at G -/

/-- **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its
remainder). -/
noncomputable def RemainderDeficiencyBelowCutStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  object.positiveDeficiency (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold ≤
    object.boundaryIncidence (object.remainderSupport (canonicalWindowPacking data object))

/-- **The window cut capacity** at `P₀`:
`e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`. -/
noncomputable def WindowCutCapacityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  object.boundaryIncidence (object.remainderSupport (canonicalWindowPacking data object)) +
      2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card ≤
    data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) +
      object.ambientSurplus (object.windowSupport (canonicalWindowPacking data object))
        data.threshold

/-! ## The canonical capacity presentation of G (K6 at the canonical objects) -/

section CanonicalCapacity

open Hypostructure.Graph.SameTokenBlockerRoles

/-- The certification budget `B = S·n + (⌊log₂ n⌋ + 1)·σ`. -/
abbrev certificationBudget (data : Parameters) (object : Graph.FiniteObject.{u}) : Nat :=
  data.surplusScale * object.vertexCount +
    (Nat.log2 object.vertexCount + 1) * object.degreeSurplus data.threshold

/-- The pair-deficit coefficient `K = C² − 3C − 2M₀C − 2S − 16M₀`. -/
abbrev pairDeficitCoefficient (data : Parameters) : ℤ :=
  (data.spineScale : ℤ) ^ 2 - 3 * data.spineScale -
    2 * (homogeneousTokenCap data.routingLabelBound : ℤ) * data.spineScale -
    2 * data.surplusScale - 16 * (homogeneousTokenCap data.routingLabelBound : ℤ)

/-- `P` holds at G's canonical capacity presentation `c` and the canonical
object ledger `L` at it. -/
abbrev AtCanonicalCapacityCounts (data : Parameters) (object : Graph.FiniteObject.{u})
    (P : (c : SurplusCapacity data object) →
      Graph.ObjectCapacityLedger object data.threshold data.windowOrder c → Prop) : Prop :=
  ∃ c L, canonicalCapacity data object = some c ∧
    canonicalObjectLedgerAt data object c = some L ∧ P c L

/-- **G's canonical capacity presentation is the explicit one**: the recorded
blocker activation of G's active family on the node-`[19]` packing. -/
noncomputable def CanonicalCapacityExplicitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (connected : object.graph.Connected),
    canonicalCapacity data object = some (explicitCapacity active avoids connected)

/-- **`|𝔘_sp(G)| = 4n + 2σ`.** -/
def PrimitiveCarrierCountStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  (object.primitiveCarrier data.threshold).card =
    4 * object.vertexCount + 2 * object.degreeSurplus data.threshold

/-- **The exact token count at the canonical presentation**:
`|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`:
`|𝔗_cap| = 4n + 3σ + 15ν`). -/
noncomputable def CanonicalTokenCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c _ =>
    c.tokens.card + 2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card =
      4 * object.vertexCount + 3 * object.degreeSurplus data.threshold +
        3 * (data.windowOrder * (canonicalWindowPacking data object).card)

/-- **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger. -/
noncomputable def CanonicalBlockedFreePartitionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    L.presented.blocked.card + freeCount data object c =
      (object.degreeSurplus data.threshold).choose 2

/-- **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`,
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`. -/
noncomputable def CanonicalLedgerDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
        2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
          ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
            (c.tokens.card : ℤ)) ≤
      2 * ((freeCount data object c : ℤ) - (certificationBudget data object : ℤ)) +
        2 * ((L.presented.blocked.card : ℤ) -
          (homogeneousTokenCap data.routingLabelBound : ℤ) * c.tokens.card)

/-- **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`. -/
def PairCountDeficitStatement (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
      2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
        ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) : ℤ) ≤
    2 * (((object.degreeSurplus data.threshold).choose 2 : ℕ) -
      (certificationBudget data object : ℤ))

/-- **The certification criterion at the canonical presentation**: its
canonical certified ledger exists iff `|Π_free| ≤ B`. -/
noncomputable def CanonicalCertificationCriterionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c _ =>
    ((canonicalCertifiedCapacityDataAt data object c).isSome ↔
      freeCount data object c ≤ certificationBudget data object)

/-- The paper's budget `E = E_spine + (m − m₀)(⌊log₂ n⌋ + 1)` at a spine family. -/
noncomputable abbrev paperBudget (data : Parameters) (object : Graph.FiniteObject.{u})
    (spineCount : Nat) : Nat :=
  Graph.spineDeficit object.vertexCount data.threshold spineCount +
    (object.edgeCount - Graph.cubicBaselineEdgeCount object.vertexCount data.threshold) *
      (Nat.log2 object.vertexCount + 1)

/-- **The paper's budget at the canonical spine family fits the certification
budget**: `E_paper ≤ B`. -/
noncomputable def PaperBudgetBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
    paperBudget data object spine.family.card ≤ certificationBudget data object

/-- **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and
presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist. -/
noncomputable def PaperBudgetCertifiesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ spine c, canonicalBaselineSpineFamily data object = some spine ∧
    canonicalCapacity data object = some c ∧
    (freeCount data object c ≤ paperBudget data object spine.family.card →
      (canonicalCertifiedCapacityDataAt data object c).isSome)

/-- **If the free side fits `B`, the blocked side is overloaded**:
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load
`> M₀` and carries an `L_geom` role-homogeneous matching or star. -/
noncomputable def CanonicalOverloadOfFitsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    freeCount data object c ≤ certificationBudget data object →
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (c.tokens.card : ℤ)) ≤
        2 * ((L.presented.blocked.card : ℤ) -
          (homogeneousTokenCap data.routingLabelBound : ℤ) * c.tokens.card) ∧
      ∃ token ∈ L.presented.tokens,
        homogeneousTokenCap data.routingLabelBound < L.presented.load token ∧
        ∃ role : Role,
          (∃ pattern ⊆ L.presented.roleFibre token role,
              PatternFamily.IsMatching pattern ∧
                geometricPatternBound data.routingLabelBound ≤ pattern.card) ∨
          (∃ centre, ∃ pattern ⊆ L.presented.roleFibre token role,
              PatternFamily.IsStar pattern centre ∧
                geometricPatternBound data.routingLabelBound ≤ pattern.card)

/-- **If every token carries load `≤ M₀`, the free side exceeds `B`**:
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`. -/
noncomputable def CanonicalFreeExcessOfCappedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    (∀ t ∈ L.presented.tokens, L.presented.load t ≤ homogeneousTokenCap data.routingLabelBound) →
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (c.tokens.card : ℤ)) ≤
        2 * ((freeCount data object c : ℤ) - (certificationBudget data object : ℤ))

/-- **Where G sits in the pair-code chain**: either the `[137]`→`[143]`
configuration holds at the canonical objects (blocked pair, `[137]` count,
canonical pattern, overload, caps fail), or G's canonical first failure exists
and yields the `[182]` residual, or the target defect of the canonical return
system's obstruction coordinates, or that obstruction's handoff together with
the Type B fan entry `[65]`. -/
noncomputable def PairCodeConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (DependentPairFamilyStatement data object ∧
      BlockedPairEntropySandwichStatement data object ∧
      HomogeneousBottleneckPatternSchema data object ∧
      SparsePressureOverloadSchema data object ∧
      ¬ HomogeneousCapsHoldStatement data object) ∨
    (PairOverlapFirstFailureStatement data object ∧
      (PairConditionalFactorizationResidualStatement data object ∨
        (∃ returns, canonicalPairDemandReturns data object = some returns ∧
          Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
            returns.obstructionCoordinates pairCoordinateSupport) ∨
        ((∃ returns, canonicalPairDemandReturns data object = some returns ∧
            PairObstructionHandoff data object returns) ∧
          TypeBFanEntryStatement data object)))

end CanonicalCapacity

open Classical in
/-- **Every target-defect witness of G has the `[20a]` structure** (not only the
canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`;
the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`;
`2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the
whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a
minimum connected set containing `A ∪ B`. -/
noncomputable def SpecWitnessStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ w : SparseTargetDefectWitness data object, w.Spec →
    IsEmpty (Graph.GluedReadings.RealizedIn w.outside) ∧
    Graph.BoundTargetDefectGeometryAt object w.support data.LengthOK
      (w.reading w.first) (w.reading w.second) w.outside ∧
    2 ≤ (SupportAtom.cutBoundary object w.support).card ∧
    (∃ vertex, vertex ∉ w.support) ∧
    (2 ≤ (by classical exact (SupportAtom.cutBoundary object w.support ∩
        sparseDeclaredSupport data object w.first).card) ∨
      2 ≤ (by classical exact (SupportAtom.cutBoundary object w.support ∩
        sparseDeclaredSupport data object w.second).card)) ∧
    (¬ ∃ a b, SupportAtom.cutBoundary object w.support = {a, b} ∧ w.support = {a, b}) ∧
    (w.support ⊆ sparseDeclaredSupport data object w.first →
      (Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading w.first) w.outside) ∧
        ¬ Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading w.second) w.outside)) ∧
      (∃ s ∈ w.support, s ∉ sparseDeclaredSupport data object w.second)) ∧
    (∀ Y : Finset object.Vertex,
      (by classical exact sparseDeclaredSupport data object w.first ∪
        sparseDeclaredSupport data object w.second) ⊆ Y →
      Graph.SupportComponents.Connected.ConnectedOn object Y → w.support.card ≤ Y.card)

end Hypostructure.Graph.Strategy.Spine
