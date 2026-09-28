import Hypostructure.Graph.Statements.JointHubs
import Hypostructure.Graph.HubLinkObject
import Hypostructure.Graph.CapacityFreeSide.Degree
import Hypostructure.Graph.CapacityFreeSide.Count
import Hypostructure.Graph.CapacityFreeSide.CsBound
import Hypostructure.Graph.CapacityFreeSide.ExtendedLoad
import Hypostructure.Graph.CapacityFreeSide.Separated

/-!
# Statements: links between the hubs of `R`, the slot relation, and the free side of G

Each statement is one of G's own facts at its canonical objects (library:
`Graph/HubLinkObject.lean`, `Graph/HubLink/*`, `Graph/CapacityFreeSide/*`):

* at `P₀`: the link structure of the hubs of `R` (chains, rainbow paths, link degeneracy),
  the hub classes of the cubic vertices, the slot relation, the closed bag-link classes,
  the two-hop links and the slot relation linear in `h_R`;
* on the strict arm of the surplus scale: the scale pressure;
* at G's canonical capacity presentation: the structure and the count of the free side.

Every registered constant is an explicit `Parameters` argument; this module imports no
strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.CapacityFreeSide
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- **The link structure of the hubs of `R`** at `P₀`. -/
noncomputable abbrev HubLinkStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.HubLinkStructure object (canonicalWindowPacking data object)

/-- **The hub classes of the cubic vertices of G.** -/
noncomputable abbrev HubClassCountsStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.HubClassCounts object

/-- **The slot relation of G** (`4σ + 21|H| ≤ 3n + 6|H|²`, …). -/
noncomputable abbrev SlotRelationStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.SlotRelation object

/-- **Closed bag-link classes of the hubs of `R`** at `P₀`. -/
noncomputable abbrev ClosedClassesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.ClosedClasses object (canonicalWindowPacking data object)

/-- **Two-hop links between the hubs of `R`** at `P₀`. -/
noncomputable abbrev HubTwoHopLinksStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.HubTwoHopLinks object (canonicalWindowPacking data object)

/-- **The slot relation linear in `h_R`** at `P₀`:
`4σ + 15|H| ≤ 3n + K·h_R + 584ν + 32σ_W`, `K = 1811497284`. -/
noncomputable abbrev SlotLinearStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.SlotLinear object (canonicalWindowPacking data object)

/-- **The scale pressure** at `C = C_sp`, `q = ⌈√n⌉`:
`C·q + 15|H| < 3s + K·h_R + 584ν + 32σ_W`. -/
noncomputable abbrev ScalePressureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HubLinkObject.ScalePressure object (canonicalWindowPacking data object)
    data.spineScale (Core.ceilSqrt (@Fintype.card object.Vertex (@FinEnum.instFintype _ object.vertices)))

/-- **The free side of G's canonical capacity charge, structurally**: at G's canonical
capacity presentation (the recorded activation of its active family), every free pair is two
selected ports `p ≠ q` with disjoint declared supports, disjoint `T`, disjoint returns,
distinct centres, each end off the other's return, no target-response and no chord-set
obstruction, and one port triangular or one centre in the other port's `T`. -/
noncomputable def FreeSideStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (c : SurplusCapacity data object),
    canonicalCapacity data object = some c ∧
    c.activation = Graph.recordSparsePairDEBlockers
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold) (LengthOK := data.LengthOK)
      (Graph.pairResponseActivation active) (object.portPairSchedule data.threshold) ∧
    ∀ pair ∈ Graph.freeSide object.vertexPairDecidableEq (object.portPairSchedule data.threshold)
        c.tokenOrder c.Eligible c.eligibleDecidable,
      ∃ p q, ∃ (hp : p ∈ object.excessPorts data.threshold)
          (hq : q ∈ object.excessPorts data.threshold),
        p ≠ q ∧ (∀ x, x ∈ pair ↔ x = p ∨ x = q) ∧
        Disjoint ((Graph.pairResponseActivation active).declaredSupport p)
          ((Graph.pairResponseActivation active).declaredSupport q) ∧
        Disjoint (portT hp) (portT hq) ∧
        Disjoint ((Graph.pairResponseActivation active).returnSupport p)
          ((Graph.pairResponseActivation active).returnSupport q) ∧
        p.1 ≠ q.1 ∧ p.2 ∉ (Graph.pairResponseActivation active).returnSupport q ∧
        q.2 ∉ (Graph.pairResponseActivation active).returnSupport p ∧
        ¬ Graph.SparsePairDEResponseObstructionAt
            (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
            (LengthOK := data.LengthOK)
            (Graph.pairResponseActivation active) (object.portPairSchedule data.threshold) pair ∧
        (Graph.pairResponseActivation active).chordObstructions pair = [] ∧
        (object.graph.Adj (Graph.pairResponseChordEnds active p).1
            (Graph.pairResponseChordEnds active p).2 ∨
          object.graph.Adj (Graph.pairResponseChordEnds active q).1
            (Graph.pairResponseChordEnds active q).2 ∨
          p.1 ∈ portT hq ∨ q.1 ∈ portT hp)

/-- **The free-side count of G**: at G's canonical capacity presentation and canonical object
ledger, `|𝒜₀| = σ`, `s(v) = d(v) − δ`, `|Π_free| ≤ τσ + Λ`
(`τ` the triangular ports, `Λ = Σ_q Σ_{v∈T(q)} s(v)`); G2 with the count substituted; in the
capped arm `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(τσ + Λ − B)`; and for every `Δ ≥ max d`:
`|Π_free| ≤ σ(τ + 3(Δ − 3))`, the capped arm in this form, and (when `K ≥ 0`)
`n·K ≤ 2σ(τ + 3(Δ − 3))` in the capped arm. -/
noncomputable def FreeSideCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (c : SurplusCapacity data object)
    (L : Graph.ObjectCapacityLedger object data.threshold data.windowOrder c),
    canonicalCapacity data object = some c ∧
    canonicalObjectLedgerAt data object c = some L ∧
    c.activation = Graph.recordSparsePairDEBlockers
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold) (LengthOK := data.LengthOK)
      (Graph.pairResponseActivation active) (object.portPairSchedule data.threshold) ∧
    (object.excessPorts data.threshold).card = object.degreeSurplus data.threshold ∧
    (∀ v, sAt object data.threshold v = object.degree v - data.threshold) ∧
    freeCount data object c ≤
      tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) *
          object.degreeSurplus data.threshold +
        ∑ q ∈ object.excessPorts data.threshold,
          ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q, sAt object data.threshold v ∧
    (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
        2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
          ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
            (c.tokens.card : ℤ)) ≤
      2 * (((tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) *
          object.degreeSurplus data.threshold +
        ∑ q ∈ object.excessPorts data.threshold,
          ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q,
            sAt object data.threshold v : ℕ) : ℤ) - (certificationBudget data object : ℤ)) +
        2 * ((L.presented.blocked.card : ℤ) -
          (homogeneousTokenCap data.routingLabelBound : ℤ) * c.tokens.card) ∧
    ((∀ t ∈ L.presented.tokens, L.presented.load t ≤ homogeneousTokenCap data.routingLabelBound) →
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (c.tokens.card : ℤ)) ≤
        2 * (((tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) *
            object.degreeSurplus data.threshold +
          ∑ q ∈ object.excessPorts data.threshold,
            ∑ v ∈ (Graph.pairResponseActivation active).localBuffer q,
              sAt object data.threshold v : ℕ) : ℤ) - (certificationBudget data object : ℤ))) ∧
    ∀ Δ : ℕ, (∀ v : object.Vertex, object.degree v ≤ Δ) →
      freeCount data object c ≤ object.degreeSurplus data.threshold *
          (tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) +
            3 * (Δ - 3)) ∧
      ((∀ t ∈ L.presented.tokens,
          L.presented.load t ≤ homogeneousTokenCap data.routingLabelBound) →
        0 ≤ pairDeficitCoefficient data →
        (object.vertexCount : ℤ) * pairDeficitCoefficient data ≤
          2 * ((object.degreeSurplus data.threshold *
            (tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) +
              3 * (Δ - 3)) : ℕ) : ℤ))

/-- **The free-side count against the hubs**: `|Π_free| ≤ σ(τ + |H| − 1)` (a hub lies in the
support `T(q)` of at most `|H| − 1` ports), and in the capped arm (when `K ≥ 0`)
`n·K ≤ 2σ(τ + |H| − 1)`. -/
noncomputable def FreeSideHubsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (c : SurplusCapacity data object)
    (L : Graph.ObjectCapacityLedger object data.threshold data.windowOrder c),
    canonicalCapacity data object = some c ∧
    canonicalObjectLedgerAt data object c = some L ∧
    freeCount data object c ≤ object.degreeSurplus data.threshold *
      (tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) +
        (sparseHighDegreeCount data object - 1)) ∧
    ((∀ t ∈ L.presented.tokens, L.presented.load t ≤ homogeneousTokenCap data.routingLabelBound) →
      0 ≤ pairDeficitCoefficient data →
      (object.vertexCount : ℤ) * pairDeficitCoefficient data ≤
        2 * ((object.degreeSurplus data.threshold *
          (tauAt (threshold := data.threshold) (Graph.pairResponseChordEnds active) +
            (sparseHighDegreeCount data object - 1)) : ℕ) : ℤ))

/-- **The extended charge leaves no pair free**: `Π_free^ext = ∅` at G's canonical capacity
presentation (every scheduled pair is blocked, centre–shoulder blocked, or triangular). -/
noncomputable def ExtFreeEmptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
    extFree data.LengthOK c = ∅

/-- **The extended loads**: `C(σ, 2) = Σ_{t ∈ 𝔗} load_ext(t)` and `|𝔗| ≤ 8n + σ`. -/
noncomputable def ExtLoadSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
    (object.degreeSurplus data.threshold).choose 2 = ∑ t ∈ c.tokens, extLoad data.LengthOK c t ∧
    c.tokens.card ≤ 8 * object.vertexCount + object.degreeSurplus data.threshold

/-- **The extended overload**:
`c²K + 2M₀(8n + σ − |𝔗|) + 2B ≤ 2 Σ_{t∈𝔗} (load_ext(t) − M₀)`. -/
noncomputable def ExtOverloadStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
    (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
        2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
          ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
            (c.tokens.card : ℤ)) +
        2 * (certificationBudget data object : ℤ) ≤
      2 * ∑ t ∈ c.tokens,
        ((extLoad data.LengthOK c t : ℤ) - homogeneousTokenCap data.routingLabelBound)

/-- **An overloaded extended token**: when `K > 0`, some token has `load_ext > M₀`. -/
noncomputable def ExtOverloadedTokenStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
    (0 < pairDeficitCoefficient data →
      ∃ t ∈ c.tokens, homogeneousTokenCap data.routingLabelBound < extLoad data.LengthOK c t)

/-- **The new port loads**: `newLoad(p) ≤ (|H| − 1) + [p triangular]·σ` for every selected
port. -/
noncomputable def NewLoadBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
    ∀ p ∈ object.excessPorts data.threshold,
      newLoad data.LengthOK c p ≤ (sparseHighDegreeCount data object - 1) +
        (by classical exact if TriPortAt object p then object.degreeSurplus data.threshold else 0)

/-- **Separated pairs and the congestion trade-off**: at G's canonical capacity presentation,
a pair of ports with disjoint declared supports and disjoint returns has only target-response
or chord-set blockers; and
`C(σ, 2) ≤ Σ_v C(d_D(v), 2) + Σ_v C(d_R(v), 2) + |Sep|`
(`D = T ∪ Γ`, `R` the canonical returns, `d_X(v) = #{p : v ∈ X(p)}`). -/
noncomputable def SeparatedPairsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (c : SurplusCapacity data object),
    canonicalCapacity data object = some c ∧
    c.activation = Graph.recordSparsePairDEBlockers
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold) (LengthOK := data.LengthOK)
      (Graph.pairResponseActivation active) (object.portPairSchedule data.threshold) ∧
    (∀ (p q : object.Vertex × object.Vertex) (pair : Finset (object.Vertex × object.Vertex)),
      p ∈ object.excessPorts data.threshold → (∀ x, x ∈ pair ↔ x = p ∨ x = q) →
      Disjoint ((Graph.pairResponseActivation active).declaredSupport p)
        ((Graph.pairResponseActivation active).declaredSupport q) →
      Disjoint ((Graph.pairResponseActivation active).returnSupport p)
        ((Graph.pairResponseActivation active).returnSupport q) →
      ∀ b ∈ c.activation.blockers pair,
        b.kind = BlockerKind.targetResponse ∨ b.kind = BlockerKind.arithmeticChordSet) ∧
    (letI : FinEnum object.Vertex := object.vertices
    letI := object.vertexPairDecidableEq
    (object.degreeSurplus data.threshold).choose 2 ≤
      ∑ v : object.Vertex, ((object.excessPorts data.threshold).filter fun p =>
          v ∈ (Graph.pairResponseActivation active).declaredSupport p).card.choose 2 +
      ∑ v : object.Vertex, ((object.excessPorts data.threshold).filter fun p =>
          v ∈ (Graph.pairResponseActivation active).returnSupport p).card.choose 2 +
      ((object.portPairSchedule data.threshold).filter fun pr =>
          ∀ p ∈ pr, ∀ q ∈ pr, p ≠ q →
            Disjoint ((Graph.pairResponseActivation active).declaredSupport p)
              ((Graph.pairResponseActivation active).declaredSupport q) ∧
            Disjoint ((Graph.pairResponseActivation active).returnSupport p)
              ((Graph.pairResponseActivation active).returnSupport q)).card)

end Hypostructure.Graph.Strategy.Spine
