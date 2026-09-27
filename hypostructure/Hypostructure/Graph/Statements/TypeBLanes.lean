import Hypostructure.Graph.Statements.CanonicalTypeB
import Hypostructure.Graph.Statements.SurplusPairRouting
import Hypostructure.Graph.Statements.CanonicalSurplusCode

/-!
# Statements: the Type B support of the selected counterexample

Node `[65]` receives **one** assigned Type B support `X = (Y_X, H_X)` of the
selected counterexample `G`, in one of the manuscript's entry forms
(`def:typeB-assigned-ledger`, tex 12909).  Each form is a *lane*: the canonical
object of `G` that the producing key fixed, together with the literal statement
of the upstream arm that produced it, so that the lanes are mutually exclusive
on `G`:

* ordinary (`[62]` yes → `[64]`): `X = (X₀, H(X₀))`,
  `canonicalTypeBOrdinarySupport`, on the `K .netChargeCap` arm of `[57]`;
* decorated (`[107]` yes → `[108]` → `[66]`): `X = (X₀, {z})`,
  `canonicalTypeBDecoratedSupport`, on the `K .netChargeCap` arm of `[57]`;
* absorbed (`[173]` no → `[175]` yes → `[177]`): `X = canonicalTypeBAbsorbedSupport`,
  the support of `G`'s canonical selected half-edge outside the subcubic
  candidates, on the `K .exactCollisionFails` arm;
* same-token (`[144]` → `[144a]`): `X = canonicalSameTokenSupport`, at which
  the `[144]` handoff holds, on the `K .surplusAbove` arm of `[19]`;
* pair obstruction (`[179]`/`[180]` → `[187]`): `X` is the canonical support
  of the first-separator handoff of G's retained pair obstruction
  (`canonicalPairObstructionSupport` at `canonicalPairDemandReturns`), on the
  `K .surplusAbove` arm of `[19]`.  No part
  of the continuation `[67]`--`[85]` runs there.

Every key of the continuation `[67]`--`[85]` is `TypeBLaneAt P`: the predicate
`P` is evaluated at exactly the lane's one canonical `(Y_X, H_X)`.  A decision
reads its predecessor key, destructures its lane and splits `P`/`¬P` at that one
support (d2ded0e's argument path).

The quantitative bridge statements (`prop:typeB-bridge-reduction`,
`def:typeB-residual-mass`, `prop:typeB-bridge-sublinear`) are stated at the
canonical packing `P₀` and at `G`'s canonical piece collections.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

section Lanes

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- **The ordinary lane** `[64]` → `[65]`: `X = (X₀, H(X₀))` on the net-cap arm
of `[57]` and the Type B arm `σ(X₀) > 0` of `[62]`. -/
def TypeBOrdinaryLane (core centres : Finset object.Vertex) : Prop :=
  NetChargeCapStatement data object ∧
    canonicalTypeBOrdinarySupport data object = some (core, centres) ∧
    0 < object.ambientSurplus core data.threshold

/-- **The decorated lane** `[108]` → `[66]` → `[65]`: `X = (X₀, {z})` with the
canonical exit-`(7)` envelope, on the net-cap arm of `[57]` and the Type A arm
`σ(X₀) = 0` of `[62]`; `z` exists exactly on the exit-`(7)` arm of `[107]`. -/
def TypeBDecoratedLane (core centres : Finset object.Vertex) : Prop :=
  NetChargeCapStatement data object ∧
    canonicalTypeBDecoratedSupport data object = some (core, centres) ∧
    object.ambientSurplus core data.threshold = 0 ∧
    (canonicalTypeBDecoratedEnvelope data object).isSome

/-- **The absorbed lane** `[177]` → `[65]`: on the failed-collision arm of `[173]`,
with the `[175]` fan data, `X = (Y_X, H_X)` is the absorbed support of `G`'s
canonical absorbed half-edge `ε` (`canonicalTypeBAbsorbedSupport`): `ε`'s
retained first-failure prefix and its first high centre.  It exists exactly when
some selected corridor meets a high-degree vertex (`K .typeBAbsorbedHalfEdge`). -/
def TypeBAbsorbedLane (core centres : Finset object.Vertex) : Prop :=
  ExactCollisionFailsStatement data object ∧
    AbsorbedGermFanDataStatement data object ∧
    canonicalTypeBAbsorbedSupport data object = some (core, centres)

/-- `(Y, H)` is the Type B support of `G`, in one of the continuation lanes. -/
def TypeBLaneMember (core centres : Finset object.Vertex) : Prop :=
  TypeBOrdinaryLane data object core centres ∨
    TypeBDecoratedLane data object core centres ∨
    TypeBAbsorbedLane data object core centres

/-- **A fact at the Type B support of `G`**: `P` holds at the one canonical
support `(Y_X, H_X)` of the lane `G` is on.  Every lane has at most one support
and the lanes are mutually exclusive, so a decision splits `P`/`¬P` at exactly
that support. -/
def TypeBLaneAt (P : Finset object.Vertex → Finset object.Vertex → Prop) :
    Prop :=
  ∃ core centres, TypeBLaneMember data object core centres ∧ P core centres

/-- The B2 disjoint choice of a support at `P₀` (`def:typeB-bridge-statements`
B2(a)--(c), tex 14119): the `Classical.choice` of the B2 yes arm at `(Y, H)`.
It is the choice underlying `canonicalTypeBDisjointChoice`. -/
noncomputable def canonicalTypeBChoice (core centres : Finset object.Vertex) :
    Option (Graph.TypeBRefinedSupport.DisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres
      centres) := by
  classical
  exact if h : Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres
      centres then some (Classical.choice h) else none

end Lanes

/-! ## Node `[65]` -/

/-- **Node `[65]`, the common Type B entry** (tex 961).  On the continuation
lanes the assigned centres are nonempty and high.  On the strict-surplus arm
there are two lanes, each at its own canonical support: the `[144]` lane, at
G's canonical same-token support `(Y, H) = canonicalSameTokenSupport`
(`Statements/CanonicalSameToken.lean`), where the canonical envelope of G's
canonical first separator escapes physically with core `Y` and decorations
`H`; and the `[179]`/`[180]` lane, at the canonical support of the first-
separator handoff of G's retained pair obstruction
(`canonicalPairObstructionSupport`, `Statements/CanonicalPairHandoff.lean`). -/
def TypeBFanEntryStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  TypeBLaneAt data object (fun core centres =>
      centres.Nonempty ∧
        ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre) ∨
    (SurplusAboveStatement data object ∧
      ((∃ core centres,
          canonicalSameTokenSupport data object = some (core, centres) ∧
            SameTokenHandoffAt data object core centres) ∨
        ∃ returns, canonicalPairDemandReturns data object = some returns ∧
          ∃ core centres,
            canonicalPairObstructionSupport data object returns =
                some (core, centres) ∧
              PairObstructionHandoffAt data object returns core centres))

/-- Node `[175]`, yes (tex 927, `lem:absorbed-germ-fan-data` (ii)): some selected
corridor meets a high-degree vertex, i.e. `G`'s canonical absorbed half-edge (a
selected half-edge outside node `[153]`'s subcubic candidates) exists.  This is
the arm that enters Type B at `[177]`. -/
noncomputable def TypeBAbsorbedHalfEdgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ epsilon, canonicalTypeBAbsorbedHalfEdge data object = some epsilon

/-- Node `[175]`, no: every selected corridor is subcubic --- every selected
half-edge is a node-`[153]` candidate, so there is no absorbed half-edge. -/
noncomputable def TypeBAbsorbedHalfEdgeAbsentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  canonicalTypeBAbsorbedHalfEdge data object = none

/-- **Node `[177]`, every discarded half-edge is charged to Type B**
(`lem:absorbed-germ-fan-data`, tex 7933: "every half-edge it discards is charged
to the Type B ledger"): every selected half-edge `ε` outside node `[153]`'s
subcubic candidates has its own pinned absorbed Type B support
`canonicalTypeBAbsorbedSupportAt ε = (J_ε, {z_ε})` --- `z_ε` high, the only high
vertex of the prefix `J_ε ∋ z_ε` through it, `J_ε` inside the canonical
remainder --- and that support's negative part is charged to the surplus of
`z_ε` (`lem:typeB-bridge-deficit-bound`). -/
noncomputable def TypeBAbsorbedChargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ epsilon : ColdEligibleHalfEdge data object,
    AbsorbedHalfEdgeOutside data object epsilon →
      ∃ core centre,
        canonicalTypeBAbsorbedSupportAt data object epsilon = some (core, {centre}) ∧
        Graph.IsHighCentre object data.threshold centre ∧ centre ∈ core ∧
        Graph.TypeBRefinedSupport.centres object data.threshold core ⊆ {centre} ∧
        core ⊆ object.remainderSupport (canonicalWindowPacking data object) ∧
        TypeBBridgeDeficitBoundAt data object core {centre}

/-- Node `[65]` at the `[64]` entry: the ordinary Type B support `(X₀, H(X₀))`
is negative and carries a high centre (`def:canonical-decomp`). -/
noncomputable abbrev TypeBAssignedSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ core centres, TypeBOrdinaryLane data object core centres ∧
    object.NegativeNetCharge core data.threshold data.dischargeScale ∧
    ∃ centre ∈ core, Graph.IsHighCentre object data.threshold centre

/-- Node `[65]` on the decorated lane (`def:decorated-fan-envelope`,
`lem:decorated-fan-admissibility`): the canonical exit-`(7)` envelope of `X₀`
has core `X₀` and decorations `{z}`, its centres are high with nonempty
assigned first-neighbour supports of actual neighbours, and it is admissible. -/
noncomputable abbrev TypeBDecoratedAssignedSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ core centres, TypeBDecoratedLane data object core centres ∧
    ∃ envelope, canonicalTypeBDecoratedEnvelope data object = some envelope ∧
      envelope.core = core ∧ envelope.decorations = centres ∧
      (∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre) ∧
      (∀ centre ∈ centres,
        (envelope.assigned centre).Nonempty ∧
          ∀ first ∈ envelope.assigned centre, object.graph.Adj centre first) ∧
      Graph.DecoratedHandoff.Admissible object data.LengthOK
        (handoffUncompressible data object) (handoffWindowFree data object)
        envelope

/-! ## Nodes `[68]`, `[69]`, `[79]` -/

/-- Node `[68]`, yes: some assigned centre of the Type B support is heavy,
`d_G(h) > δ + 1`. -/
def TypeBFanHeavyCentreStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∃ centre ∈ centres, data.threshold + 1 < object.degree centre)

/-- Node `[68]`, no → `[78]`: every assigned centre of the Type B support has
degree `δ + 1`. -/
def TypeBFanDegreeFourCentresStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∀ centre ∈ centres, object.degree centre = data.threshold + 1)

/-- Node `[69]` (`cor:heavy-center-local-dichotomy`, tex 2322): at the heavy
arm's Type B support, every heavy assigned centre carries the routed local
dichotomy. -/
def TypeBFanLocalDichotomyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    (∃ centre ∈ centres, data.threshold + 1 < object.degree centre) ∧
      ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
        HeavyCentreRoutedAlternative data object core centres centre)

/-- Node `[79]` (`cor:degree-four-local-activation`, tex 2336): every assigned
centre of the Type B support carries the degree-four fan profile. -/
def TypeBFanDegreeFourProfileStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    ∀ centre ∈ centres, DegreeFourFanProfile data object core centres centre)

/-- `lem:compatible-pair-fan-closure` at the assigned profiles of the Type B
support. -/
def CompatiblePairFanClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (CompatiblePairFanClosureAt data object)

/-- `prop:fan-closed-port-typeB-routing` at the assigned profiles of the Type B
support. -/
def FanClosedPortTypeBRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (FanClosedPortTypeBRoutingAt data object)

/-- `cor:compatible-pair-typeB-routing` at the assigned profiles of the Type B
support. -/
def CompatiblePairTypeBRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (CompatiblePairTypeBRoutingAt data object)

/-- `prop:triangular-port-typeB-routing` at the assigned profiles of the Type B
support. -/
def TriangularPortTypeBRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (TriangularPortTypeBRoutingAt data object)

/-! ## The triangular fan core at the heavy centres of the Type B support -/

/-- `def:triangular-fan-core` (tex 2378) at every heavy assigned centre `h` of the
Type B support and every nonempty family of triangular ports of `h`: G's
canonical shoulders of each port are exactly its two shoulders, joined by the
port's chord. -/
noncomputable def TriangularFanCoreStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex, ports.Nonempty →
        ports ⊆ Graph.triangularEndpoints object centre →
        ∀ endpoint ∈ ports,
          (∀ vertex : object.Vertex,
            vertex ∈ triangularShoulders object centre endpoint ↔
              Graph.IsShoulder object centre endpoint vertex) ∧
          (triangularShoulders object centre endpoint).card = 2 ∧
          ∃ left right : object.Vertex,
            left ∈ triangularShoulders object centre endpoint ∧
              right ∈ triangularShoulders object centre endpoint ∧ left ≠ right ∧
                object.graph.Adj left right)

/-- `lem:triangular-first-landing` (tex 2463) at every heavy assigned centre of the
Type B support: every completion edge of G's canonical triangular fan core lands
centrally, cross-triangularly, or outside, and exactly one of these. -/
noncomputable def TriangularFirstLandingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex, ports.Nonempty →
        ports ⊆ Graph.triangularEndpoints object centre →
        ∀ endpoint shoulder target : object.Vertex,
          triangularCompletion object centre ports endpoint shoulder target →
            ((triangularCentral object centre ports endpoint shoulder target ∧
                ¬ triangularCrossTriangular object centre ports endpoint shoulder
                  target ∧
                ¬ triangularOutside object centre ports endpoint shoulder target) ∨
              (triangularCrossTriangular object centre ports endpoint shoulder
                  target ∧
                ¬ triangularCentral object centre ports endpoint shoulder target ∧
                ¬ triangularOutside object centre ports endpoint shoulder target) ∨
              (triangularOutside object centre ports endpoint shoulder target ∧
                ¬ triangularCentral object centre ports endpoint shoulder target ∧
                ¬ triangularCrossTriangular object centre ports endpoint shoulder
                  target)) ∧
            (object.graph.Adj centre target → target = centre) ∧
            target ∉ ports)

/-- `lem:triangular-cross-shoulder` (tex 2490) at every heavy assigned centre of
the Type B support, on G's canonical cross-triangular incidences: two distinct
cross edges between two shoulder pairs force a shoulder above the baseline, and
with every shoulder at the baseline the cross edge is unique. -/
noncomputable def TriangularCrossShoulderStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex, ports.Nonempty →
        ports ⊆ Graph.triangularEndpoints object centre →
        ∀ first ∈ ports, ∀ second ∈ ports, first ≠ second →
          let between := fun source target =>
            triangularCrossTriangular object centre ports first source target ∧
              triangularCrossTriangular object centre ports second target source
          (∀ source target source' target',
            between source target → between source' target' →
              (source ≠ source' ∨ target ≠ target') →
                ∃ shoulder,
                  (shoulder ∈ triangularShoulders object centre first ∨
                    shoulder ∈ triangularShoulders object centre second) ∧
                  data.threshold < object.degree shoulder) ∧
          ((∀ shoulder,
              (shoulder ∈ triangularShoulders object centre first ∨
                shoulder ∈ triangularShoulders object centre second) →
              object.degree shoulder ≤ data.threshold) →
            ∀ source target source' target',
              between source target → between source' target' →
                source = source' ∧ target = target'))

/-! ## Nodes `[70]`--`[72]`, `[80]`--`[81]` -/

/-- Node `[70]` (`lem:fan-certificate`, `def:typeB-fan-safe` (i)): at the Type B
support, every assigned centre has its fan-safe graph, and whenever G's
canonical fan-certificate labelling is present at it, the label packing caps its
degree (`d_G(h) ≤ 8`, the registered cap). -/
noncomputable def TypeBFanCertificateCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∀ centre ∈ centres,
      FanSafeAt data object centre ∧
        ∀ marking, canonicalFanCertificateLabelling data object centre = some marking →
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder)

/-- Nodes `[71]`/`[80]`, yes (`def:marked-typeB-fan`): every assigned centre of
the Type B support carries G's canonical fan-certificate labelling, under the
cap. -/
noncomputable def TypeBFanCertificateMarkedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    TypeBCertificateMarkedAt data object centres)

/-- Nodes `[71]`/`[80]`, no: some assigned centre of the Type B support is a
fan-certificate residual centre: G's canonical fan-certificate labelling is
absent there. -/
noncomputable def TypeBFanCertificateResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    ∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      canonicalFanCertificateLabelling data object centre = none)

/-- Nodes `[72]`/`[81]`, the direct fan-window cycles are excluded inside the
local fan-window ledger (`lem:typeB-direct-fan-window-cycles`,
`lem:typeB-two-window-cycles`, `def:direct-cycle-free-closed-pair`, tex 13379):
at the marked Type B support every assigned centre is direct-cycle free at
`P₀`. -/
noncomputable def TypeBFanDirectCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun _core centres =>
    TypeBCertificateMarkedAt data object centres ∧
      ∀ centre ∈ centres,
        Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
          data.LengthOK (canonicalWindowPacking data object) centre)

/-- Nodes `[72]`/`[81]`, the local B1 fan ledger (`lem:typeB-hybrid-B1`,
tex 13647): at the direct-cycle-free Type B support every assigned centre
carries the hybrid B1 entry at its assigned fan envelope over
`W₀ = windowSupport P₀`. -/
noncomputable def TypeBFanHybridEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    ∀ centre ∈ centres,
      HybridB1Entry data object centre
        (typeBFanEnvelope core centres centre)
        (Graph.FiniteObject.windowSupport (canonicalWindowPacking data object)))

/-- The B1 ledger of the Type B support `(Y, H)`, as the hybrid entry fact
states it. -/
noncomputable abbrev TypeBB1At (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) : Prop :=
  ∀ centre ∈ centres,
    HybridB1Entry data object centre
      (typeBFanEnvelope core centres centre)
      (Graph.FiniteObject.windowSupport (canonicalWindowPacking data object))

/-- Node `[72]`, yes (`def:typeB-bridge-statements` B1 and B2, tex 14119: "local
fan-window ledger complete; B2 disjointness holds"): the local B1 ledger of the
Type B support is complete and B2 holds there. -/
noncomputable def TypeBB2ChoiceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    TypeBB1At data object core centres ∧ TypeBB2At data object core centres)

/-- Node `[73]`, B2 no (`lem:typeB-bridge-to-overlap`, tex 13927): the
certificate-marked Type B support carries G's canonical minimal overlap
obstruction at `P₀`. -/
noncomputable def TypeBB2ObstructionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    TypeBCertificateMarkedAt data object centres ∧
      ∃ obstruction, canonicalOverlapObstruction data object core centres =
        some obstruction)

/-- Node `[81]`, yes (degree-four arm, tex 1019: "`c ≤ 1`, or `c ≥ 2` with B2
disjoint ledger?"): at the Type B support with its local B1 ledger, every
assigned centre has at most one cubic-closed neighbour in its assigned fan
envelope, or B2 holds there. -/
noncomputable def TypeBDegreeFourLedgerStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    TypeBB1At data object core centres ∧
      ((∀ centre ∈ centres,
        Graph.TypeBFanIncidence.closedCount object data.threshold
          (typeBFanEnvelope core centres centre) centre ≤ 1) ∨
      TypeBB2At data object core centres))

/-- Node `[81]`, no → `[83]` (tex 1021: "`c ≥ 2` and B2 fails; minimal Type B
overlap obstruction"): some assigned centre of the certificate-marked Type B
support has at least two cubic-closed neighbours, and the support carries G's
canonical minimal overlap obstruction at `P₀` (`lem:typeB-bridge-to-overlap`). -/
noncomputable def TypeBDegreeFourOverlapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    (∃ centre ∈ centres,
      2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
        (typeBFanEnvelope core centres centre) centre) ∧
    TypeBCertificateMarkedAt data object centres ∧
      ∃ obstruction, canonicalOverlapObstruction data object core centres =
        some obstruction)

/-- The B2-paid ledger of the Type B support `(Y, H)` (`def:typeB-bridge-statements`
B2(a)--(d)): B2 holds, the canonical disjoint choice refines every candidate
charge, and the canonical B2 ledger has its exact augmented refinement, its
post-ledger core hygiene (`lem:typeB-postledger-core-hygiene`) and its grouped
envelope coverage. -/
noncomputable abbrev TypeBB2LedgerAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  TypeBB2At data object core centres ∧
    (∃ choice, canonicalTypeBChoice data object core centres = some choice ∧
      ∀ centre (member : centre ∈ centres),
        (choice.entry centre member).EntryRefines data.threshold
          data.dischargeScale core centre) ∧
    ∃ ledger, canonicalTypeBDisjointChoice data object core centres =
        some ledger ∧
      ledger.ExactAugmentedLedgerRefinement ∧
      PostLedgerComponents data object ledger ∧
      GroupedEnvelopeCoverage data object ledger

/-- Node `[82]` (degree-four arm, tex 1020: "yes: certificate-closed or
B2-paid; `N₀(X) ≥ 0` outside route 8"), with `lem:typeB-exclusion` Step 1
(tex 14405--14430) and `prop:typeB-bridge-reduction`: at the `[81]`-yes support,
either every assigned centre has `c ≤ 1` and its marked fan is
certificate-closed (`D_B ≤ 0`), or the support is B2-paid: its canonical B2
ledger exists and its remaining core carries the whole deficit,
`Σ_{remaining core} ch ≤ s·No(X)`. -/
noncomputable def TypeBDegreeFourClosedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    ((∀ centre ∈ centres,
        Graph.TypeBFanIncidence.closedCount object data.threshold
          (typeBFanEnvelope core centres centre) centre ≤ 1) ∧
      ∀ centre ∈ centres,
        Graph.TypeBFanIncidence.IsCertificateClosed object data.threshold
          data.dischargeScale (typeBFanEnvelope core centres centre) centre) ∨
    (TypeBB2LedgerAt data object core centres ∧
      ∃ ledger, canonicalTypeBDisjointChoice data object core centres =
          some ledger ∧
        RemainingCoreCharge data object ledger ≤
          typeBScaledNetCharge data object core centres))

/-- `prop:typeB-global-local-bridge` (tex 14028): at the B2-failure arm's Type B
support `(Y_X, H_X)` (a connected admissible support inside the remainder of
`P₀`, with no fan-certificate residual centre), G's canonical minimal overlap
obstruction inherits the five global-to-local constraints. -/
noncomputable def TypeBGlobalLocalBridgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    TypeBCertificateMarkedAt data object centres ∧
    ∃ obstruction, canonicalOverlapObstruction data object core centres =
        some obstruction ∧
      Graph.TypeBRefinedSupport.GlobalLocalReflectionACE data.typeABPresentation
        object data.windowOrder data.LengthOK data.threshold
        data.dischargeScale core centres obstruction)

/-! ## Nodes `[73]`--`[76]`, `[82]`--`[85]` -/

/-- Node `[74]`, B2(a)--(d) on the B2 yes arm of `[72]`: the Type B support is
B2-paid (`TypeBB2LedgerAt`). -/
noncomputable abbrev TypeBDisjointLedgerStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    TypeBB2LedgerAt data object core centres)

/-- Node `[74]`, `prop:typeB-bridge-reduction` (tex 14289) on the Type B
support's canonical B2 ledger: the remaining core carries the whole deficit,
`Σ_{remaining core} ch ≤ s·No(X)`, so a nonnegative remaining core (no route-8
residual) gives `N₀(X) ≥ 0`. -/
noncomputable abbrev TypeBExcludedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    ∃ ledger, canonicalTypeBDisjointChoice data object core centres = some ledger ∧
      RemainingCoreCharge data object ledger ≤
        typeBScaledNetCharge data object core centres)

/-- A Type B support is a **bridge residual** (`def:typeB-bridge-statements`
(i)/(ii)): it has a fan-certificate residual centre, or it is certificate-marked
and carries G's canonical minimal overlap obstruction. -/
noncomputable abbrev TypeBBridgeResidualAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  (∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      canonicalFanCertificateLabelling data object centre = none) ∨
    (TypeBCertificateMarkedAt data object centres ∧
      ∃ obstruction, canonicalOverlapObstruction data object core centres =
        some obstruction)

/-- **Node `[76]`/`[85]`**, `lem:typeB-exclusion` with `thm:branch-kill` at the
Type B support: Type B cannot carry the linear deficit outside route `8`.  On the
B2 arm (`[74]` → `[76]`, `[82]` → `[85]`) the support is B2-paid and its
remaining core --- the route-`8` input `[77]` --- carries the whole deficit,
`Σ_{remaining core} ch ≤ s·No(X)`; on the fan-mass arms (`[75]` → `[76]`,
`[84]` → `[85]`) B2 fails and the support's negative part is charged to its
assigned surplus by `lem:typeB-bridge-deficit-bound`. -/
noncomputable abbrev TypeBExclusionResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    (TypeBB2LedgerAt data object core centres ∧
      ∃ ledger, canonicalTypeBDisjointChoice data object core centres =
          some ledger ∧
        RemainingCoreCharge data object ledger ≤
          typeBScaledNetCharge data object core centres) ∨
    (¬ TypeBB2At data object core centres ∧
      TypeBBridgeDeficitBoundAt data object core centres))

/-- Node `[77]`, the Type B entry into route `8` (tex 979: "route-8 cores
continue in Part IX"): if the Type B support is negative, `s·No(X) < 0`, then
either its canonical B2 ledger hands a negative remaining core to route `8`, or
B2 fails and its negative part is charged to its assigned surplus. -/
noncomputable abbrev TypeBRoute8EntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    typeBScaledNetCharge data object core centres < 0 →
      (∃ ledger, canonicalTypeBDisjointChoice data object core centres =
          some ledger ∧ RemainingCoreCharge data object ledger < 0) ∨
      (¬ TypeBB2At data object core centres ∧
        TypeBBridgeDeficitBoundAt data object core centres))

/-- Nodes `[75]`/`[84]` (`def:typeB-residual-mass`,
`lem:typeB-bridge-deficit-bound`, tex 14682--14810): at the
certificate-residual arm's Type B support, which has a fan-certificate residual
centre, the support-level negative part is charged to its assigned surplus. -/
noncomputable def TypeBFanCertificateResidualMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    (∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      canonicalFanCertificateLabelling data object centre = none) ∧
    TypeBBridgeDeficitBoundAt data object core centres)

/-- Nodes `[73]`/`[75]`, `[83]`/`[84]` (`lem:typeB-bridge-deficit-bound`): at the
B2-failure arm's Type B support, which carries G's canonical reflected minimal
overlap obstruction, the support-level negative part is charged to its
assigned surplus. -/
noncomputable abbrev TypeBOverlapObstructionMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAt data object (fun core centres =>
    TypeBCertificateMarkedAt data object centres ∧
    (∃ obstruction, canonicalOverlapObstruction data object core centres =
        some obstruction ∧
      Graph.TypeBRefinedSupport.GlobalLocalReflectionACE data.typeABPresentation
        object data.windowOrder data.LengthOK data.threshold
        data.dischargeScale core centres obstruction) ∧
    TypeBBridgeDeficitBoundAt data object core centres)

/-! ## The bridge statements at `P₀` -/

/-- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap` at every
negative positive-surplus canonical piece of `P₀`: its canonical B2 ledger at
its own high centres leaves a negative remaining core (with its post-ledger
hygiene and grouped envelope coverage), or it carries a minimal overlap
obstruction. -/
noncomputable abbrev TypeBBridgeReductionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ piece : Graph.TypeBRefinedSupport.CanonicalPiece object
      (canonicalWindowPacking data object),
    object.NegativeNetCharge piece.vertices data.threshold data.dischargeScale →
    0 < object.ambientSurplus piece.vertices data.threshold →
    (∃ ledger, canonicalTypeBDisjointChoice data object piece.vertices
        (Graph.TypeBRefinedSupport.centres object data.threshold
          piece.vertices) = some ledger ∧
      ledger.ExactAugmentedLedgerRefinement ∧
      ¬ 0 ≤ RemainingCoreCharge data object ledger ∧
      PostLedgerComponents data object ledger ∧
      GroupedEnvelopeCoverage data object ledger) ∨
    ∃ obstruction, canonicalOverlapObstruction data object piece.vertices
      (Graph.TypeBRefinedSupport.centres object data.threshold piece.vertices) =
        some obstruction

section Collections

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- A canonical piece of `P₀` is a *Type B bridge-residual* piece: negative,
positive surplus, and bridge-residual (`def:typeB-bridge-statements` (i)/(ii)). -/
def TypeBOrdinaryBridgePiece
    (component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) : Prop :=
  let piece := object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component
  object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
    0 < object.ambientSurplus piece data.threshold ∧
    Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
      data.threshold data.dischargeScale

/-- A canonical piece of `P₀` is a *decorated handoff* piece: negative, zero
surplus, with a surviving exit-`(7)` separator (`def:decorated-fan-envelope`). -/
def TypeBGroupedHandoffPiece
    (component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) : Prop :=
  let piece := object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component
  object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
    object.ambientSurplus piece data.threshold = 0 ∧
    SeparatorHandoffAt data object piece

open scoped Classical in
/-- **The ordinary bridge-residual union of `G`** (`def:typeB-residual-mass`,
the canonical role): the union of the bridge-residual canonical pieces of `P₀`. -/
noncomputable def canonicalOrdinaryBridgeUnion : Finset object.Vertex :=
  ((object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object))).filter
      (TypeBOrdinaryBridgePiece data object)).biUnion
    (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)))

open scoped Classical in
/-- **The grouped decorated-envelope union of `G`** (`def:typeB-residual-mass`,
the decorated role): the union of the decorated handoff canonical pieces of
`P₀`. -/
noncomputable def canonicalGroupedBridgeUnion : Finset object.Vertex :=
  ((object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object))).filter
      (TypeBGroupedHandoffPiece data object)).biUnion
    (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)))

open scoped Classical in
/-- **The grouped centres `H_𝔠` of `G`**: the canonical surviving exit-`(7)`
separators of the decorated handoff pieces of `P₀`. -/
noncomputable def canonicalGroupedCentres : Finset object.Vertex :=
  ((object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object))).filter
      (TypeBGroupedHandoffPiece data object)).biUnion fun component =>
    (canonicalHandoffSeparatorAt data object
      (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component)).toFinset

open scoped Classical in
/-- **The absorbed core of a decorated handoff piece**
(`lem:decorated-envelope-deficit-bound`, tex 14724): the vertices of the piece
covered by the canonical exit-`(7)` envelope of the piece, namely its
decorations and their assigned first neighbours; empty when the piece has no
canonical envelope. -/
noncomputable def canonicalGroupedAbsorbedCore (piece : Finset object.Vertex) :
    Finset object.Vertex :=
  match canonicalHandoffEnvelopeAt data object piece (handoffHighDegree data object)
      (handoffAbsorbing data object (canonicalWindowPacking data object)) with
  | some envelope =>
      piece ∩ (envelope.decorations ∪ envelope.decorations.biUnion envelope.assigned)
  | none => ∅

open scoped Classical in
/-- **G's route-`8` pieces of a support** (`lem:typeB-bridge-with-route8-core`,
`lem:decorated-envelope-with-route8-core`: the canonical collection `𝒜_X` of
route-`8` residual supports): the canonical pieces of `support` that carry a
route-`8` residual profile, i.e. on which the Type A routing and unsaturation
pair of `lem:typeB-bridge-deficit-bound` fails. -/
noncomputable def canonicalBridgeRoute8Pieces (support : Finset object.Vertex) :
    Finset (Graph.SupportComponents.Connected.Component object support) :=
  (object.canonicalPieces support).filter fun piece =>
    ¬ Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
      (object.pieceSupport support piece) data.threshold data.dischargeScale

end Collections

/-- Nodes `[73]`/`[75]` and `[83]`/`[84]`, `def:typeB-residual-mass`: the Type B
residual fan-mass facts at `P₀`, on its canonical pieces and on the two
canonical role unions, each with G's canonical route-`8` pieces `𝒜` extracted
(`lem:typeB-bridge-with-route8-core`). -/
noncomputable abbrev TypeBBridgeMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let ordinary := canonicalOrdinaryBridgeUnion data object
  let grouped := canonicalGroupedBridgeUnion data object
  (∀ component ∈ object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object)),
    let piece := object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component
    object.NegativeNetCharge piece data.threshold data.dischargeScale →
    0 < object.ambientSurplus piece data.threshold →
    (∀ centre ∈ piece, Graph.IsHighCentre object data.threshold centre →
      CentreBridgeMassBound data object piece
        (Graph.TypeBRefinedSupport.centres object data.threshold piece) centre) ∧
      (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
          data.threshold data.dischargeScale →
        piece.card + data.dischargeScale *
              object.ambientSurplus piece data.threshold ≤
          data.dischargeScale * object.positiveDeficiency piece data.threshold +
            data.bridgeMassFactor * data.dischargeScale *
              object.ambientSurplus piece data.threshold)) ∧
    (let remainder := object.remainderSupport (canonicalWindowPacking data object)
     let route8 := canonicalBridgeRoute8Pieces data object remainder
     (∀ piece ∈ route8,
        object.ambientSurplus (object.pieceSupport remainder piece)
          data.threshold = 0) →
      ∑ piece ∈ object.canonicalPieces remainder,
          ((object.pieceSupport remainder piece).card +
              data.dischargeScale * object.ambientSurplus
                (object.pieceSupport remainder piece) data.threshold -
            data.dischargeScale * object.positiveDeficiency
              (object.pieceSupport remainder piece) data.threshold) ≤
        Graph.TypeBEnvelopeCharge.route8Deficit object remainder data.threshold
            data.dischargeScale route8 +
          data.bridgeMassFactor * data.dischargeScale *
            object.degreeSurplus data.threshold) ∧
    let ordinaryRoute8 := canonicalBridgeRoute8Pieces data object ordinary
    let groupedRoute8 := canonicalBridgeRoute8Pieces data object grouped
    (∀ piece ∈ ordinaryRoute8,
        object.ambientSurplus (object.pieceSupport ordinary piece)
          data.threshold = 0) →
      (∀ piece ∈ groupedRoute8,
        object.ambientSurplus (object.pieceSupport grouped piece)
          data.threshold = 0) →
      ∑ piece ∈ object.canonicalPieces ordinary,
          ((object.pieceSupport ordinary piece).card +
              data.dischargeScale * object.ambientSurplus
                (object.pieceSupport ordinary piece) data.threshold -
            data.dischargeScale * object.positiveDeficiency
              (object.pieceSupport ordinary piece) data.threshold) +
        ∑ piece ∈ object.canonicalPieces grouped,
          ((object.pieceSupport grouped piece).card +
              data.dischargeScale * object.ambientSurplus
                (object.pieceSupport grouped piece) data.threshold -
            data.dischargeScale * object.positiveDeficiency
              (object.pieceSupport grouped piece) data.threshold) ≤
        Graph.TypeBEnvelopeCharge.route8Deficit object ordinary
            data.threshold data.dischargeScale ordinaryRoute8 +
          Graph.TypeBEnvelopeCharge.route8Deficit object grouped
            data.threshold data.dischargeScale groupedRoute8 +
          2 * (data.bridgeMassFactor * data.dischargeScale *
            object.degreeSurplus data.threshold)

/-- `prop:typeB-bridge-sublinear` (tex 14955) at the two canonical role unions
of `P₀`: with no route-`8` core extracted, the bridge residual mass of both
roles is at most twice the assigned surplus, and the surplus is at most the
near-cubic threshold. -/
noncomputable abbrev TypeBBridgeSublinearStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let ordinary := canonicalOrdinaryBridgeUnion data object
  let grouped := canonicalGroupedBridgeUnion data object
  ((∀ piece ∈ object.canonicalPieces ordinary,
      Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
        (object.pieceSupport ordinary piece) data.threshold data.dischargeScale) →
    (∀ piece ∈ object.canonicalPieces grouped,
      Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
        (object.pieceSupport grouped piece) data.threshold data.dischargeScale) →
    ∑ piece ∈ object.canonicalPieces ordinary,
        ((object.pieceSupport ordinary piece).card +
            data.dischargeScale * object.ambientSurplus
              (object.pieceSupport ordinary piece) data.threshold -
          data.dischargeScale * object.positiveDeficiency
            (object.pieceSupport ordinary piece) data.threshold) +
      ∑ piece ∈ object.canonicalPieces grouped,
        ((object.pieceSupport grouped piece).card +
            data.dischargeScale * object.ambientSurplus
              (object.pieceSupport grouped piece) data.threshold -
          data.dischargeScale * object.positiveDeficiency
            (object.pieceSupport grouped piece) data.threshold) ≤
      2 * (data.bridgeMassFactor * data.dischargeScale *
        object.degreeSurplus data.threshold)) ∧
    object.degreeSurplus data.threshold ≤
      data.surplusThreshold object.vertexCount

open scoped Classical in
/-- **`prop:typeB-bridge-sublinear`'s hypotheses on `G`**, in the `[113]`-tested
form, at `P₀`: (i) every negative positive-surplus canonical piece is
bridge-residual, and (ii) the decorated handoff pieces carry the grouped
decorated-envelope fan assignment of `def:typeB-assigned-ledger` at `G`'s own
objects --- the grouped centres `H_𝔠` (the canonical surviving separators),
their canonical fan envelopes, and the canonical absorbed cores --- with the
off-absorbed routing/unsaturation pair and the absorbed cardinalities covered
by the centres' cubic-closed counts (`lem:decorated-envelope-deficit-bound`'s
hypotheses). -/
def TypeBSublinearHypotheses (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∀ component ∈ object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object)),
    let piece := object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component
    object.NegativeNetCharge piece data.threshold data.dischargeScale →
    0 < object.ambientSurplus piece data.threshold →
    Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
      data.threshold data.dischargeScale) ∧
  ∃ handoffPieces : Finset (Graph.SupportComponents.Connected.Component
      object (object.remainderSupport (canonicalWindowPacking data object))),
    (∀ component,
      component ∈ handoffPieces ↔
        component ∈ object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object)) ∧
          TypeBGroupedHandoffPiece data object component) ∧
    ∃ centres : Finset object.Vertex,
      centres = canonicalGroupedCentres data object ∧
      (∀ centre ∈ centres, data.threshold < object.degree centre) ∧
      ∃ fanEnvelope : object.Vertex → Finset object.Vertex,
        fanEnvelope = typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) ∧
      ∃ absorbedAt : Finset object.Vertex → Finset object.Vertex,
        absorbedAt = canonicalGroupedAbsorbedCore data object ∧
        (∀ component ∈ handoffPieces,
          let piece := object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component
          absorbedAt piece ⊆ piece ∧
            (∀ vertex ∈ piece \ absorbedAt piece,
              object.internalDegree piece vertex ≤ data.threshold) ∧
            (∀ vertex ∈ piece \ absorbedAt piece,
              object.internalDegree piece vertex = data.threshold →
              ∃ receiver : object.Vertex,
                object.traceReceiver? piece data.threshold vertex =
                    some receiver ∧
                  object.IsReceiver piece data.threshold receiver ∧
                    receiver ∉ absorbedAt piece) ∧
            ∀ receiver ∈ object.receivers piece data.threshold \
                absorbedAt piece,
              1 + object.restrictedLoad piece (absorbedAt piece)
                  data.threshold receiver ≤
                data.dischargeScale *
                  object.missingPorts piece data.threshold receiver) ∧
        ∑ component ∈ handoffPieces,
            (absorbedAt (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component)).card ≤
          ∑ centre ∈ centres,
            Graph.TypeBFanIncidence.closedCount object data.threshold
              (fanEnvelope centre) centre

/-- The exact negation of the sublinear hypotheses, retained as the tested
residual state (the manuscript's Part IX bridge-residual continuation). -/
noncomputable abbrev TypeBSublinearResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ TypeBSublinearHypotheses data object

end Hypostructure.Graph.Strategy.Spine
