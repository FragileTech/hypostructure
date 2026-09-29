import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Statements.CanonicalCapacityExplicit
import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.Statements.TypeBLanes
import Hypostructure.Graph.Statements.CanonicalPairHandoff
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.ObjectCapacityLedger

/-!
# Statements: the strict-surplus facts of `[20]`, made explicit

The bounds, ratios, identities and obstructions that the strict arm of `[19]`
forces at G (hoisted from the former `[20a]` exit to the top of the strict arm),
the pair-code chain, and the entry-prefix fact about the witness triples of
clause (b).  Each is a fact about G and its fixed objects (the canonical window
packing `P₀`, every certified capacity presentation of G), so it can be carried
on the one ledger and used later as a budget term or a structural constraint.

G-only restatement (`g-repair`): exit (b) of `[125]`, stated about G, is empty
at G (two readings of G always agree in G's own surroundings `G − Z`), so the
`[20a]` exit is closed and its witness-level statements (at `[125]`'s pinned
witness `(first, second, Z, O)` and its separating context `O`) are removed.

Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## The witness triples of clause (b) -/

/-- The two declared supports `{A, B}` of a witness triple's pair. -/
noncomputable abbrev SparseTargetDefectWitness.pairSupports {data : Parameters}
    {object : Graph.FiniteObject.{u}} (w : SparseTargetDefectWitness data object) :
    Set (Finset object.Vertex) :=
  {sparseDeclaredSupport data object w.first, sparseDeclaredSupport data object w.second}

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

/-- **Exit (e) is excluded at G**: no open-port suppression cycle has an
accepted lifted length `|walk| + |chords|`. -/
def NoSuppressionChordViolationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (tvs : Graph.TightVertexSuppression.CompatibleFamily object)
    (certificate : Graph.CycleCertificate tvs.suppressed data.LengthOK),
    ¬ data.LengthOK (certificate.walk.length + (tvs.usedChords certificate.walk).card)

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
and yields the `[182]` residual, or the canonical return system's obstruction
handoff together with the Type B fan entry `[65]`.  (G-only restatement: the
target defect of the obstruction coordinates, exit (b) stated about G, is empty
at G -- two readings of G agree in `G − Z` -- and is not an outcome.) -/
noncomputable def PairCodeConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (DependentPairFamilyStatement data object ∧
      BlockedPairEntropySandwichStatement data object ∧
      HomogeneousBottleneckPatternSchema data object ∧
      SparsePressureOverloadSchema data object ∧
      ¬ HomogeneousCapsHoldStatement data object) ∨
    (PairOverlapFirstFailureStatement data object ∧
      (PairConditionalFactorizationResidualStatement data object ∨
        ((∃ returns, canonicalPairDemandReturns data object = some returns ∧
            PairObstructionHandoff data object returns) ∧
          TypeBFanEntryStatement data object)))

end CanonicalCapacity

open Classical in
/-- **The witness triples of clause (b) at G, stated about G** (G-only
restatement of the former `[20a]` structure at every clause-(b) witness; key
name kept for ledger stability): at every witness triple `w = (A, B, Z)` of G
whose `Z` is the canonical support of `A ∪ B`, `Z` is connected, contains `A`
and `B`, and is a minimum connected set containing `A ∪ B`; and no witness of G
satisfies clause (b): G's own surroundings `G − Z` never separate two readings
of G.  (The former clauses read the separating context `O`, which is not part of
G, and are removed.) -/
noncomputable def SpecWitnessStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ w : SparseTargetDefectWitness data object,
    Graph.CanonicalSupport.select? object
        (sparseDeclaredSupport data object w.first ∪
          sparseDeclaredSupport data object w.second) = some w.support →
    Graph.SupportComponents.Connected.ConnectedOn object w.support ∧
    sparseDeclaredSupport data object w.first ⊆ w.support ∧
    sparseDeclaredSupport data object w.second ⊆ w.support ∧
    (∀ Y : Finset object.Vertex,
      sparseDeclaredSupport data object w.first ∪
          sparseDeclaredSupport data object w.second ⊆ Y →
      Graph.SupportComponents.Connected.ConnectedOn object Y → w.support.card ≤ Y.card) ∧
    ¬ w.Spec

end Hypostructure.Graph.Strategy.Spine
