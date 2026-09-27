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
* absorbed (`[173]` no → `[177]`): for each selected half-edge `ε`,
  `X_ε = canonicalTypeBAbsorbedSupport ε`, on the `K .exactCollisionFails` arm;
* same-token (`[144]` → `[144a]`): `X = canonicalSameTokenSupport`, at which
  the `[144]` handoff holds, on the `K .surplusAbove` arm of `[19]`;
* pair obstruction (`[179]`/`[180]` → `[187]`): `X` is the canonical support
  of the first-separator handoff of G's retained pair obstruction
  (`canonicalPairObstructionSupport` at `canonicalPairDemandReturns`), on the
  `K .surplusAbove` arm of `[19]`.  No part
  of the continuation `[67]`--`[85]` runs there.

Every key of the continuation `[67]`--`[85]` is `TypeBLaneAll P` (a fact at
the lane's support) or `TypeBLaneSome P` (a decision's positive arm): the
predicate `P` is evaluated at exactly the lane's canonical `(Y_X, H_X)`.  A
decision reads its predecessor key, destructures its lane and splits `P` at
that lane's support (d2ded0e's argument path).

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

/-- **The absorbed lane at one selected half-edge** `[177]` → `[65]`:
`X_ε = (V(germ ε), {first high centre})`. -/
def TypeBAbsorbedLane (epsilon : ColdEligibleHalfEdge data object)
    (core centres : Finset object.Vertex) : Prop :=
  ∃ routing : ColdFailureRoutingStatement data object,
    Sum.inl epsilon ∉ coldRoutedCandidates data object routing ∧
      canonicalTypeBAbsorbedSupport data object epsilon = some (core, centres)

/-- Node `[177]` entered: on the failed-collision arm of `[173]`, with the
`[175]` fan data, every selected half-edge outside the subcubic candidates has
its canonical absorbed support. -/
def TypeBAbsorbedEntered : Prop :=
  ExactCollisionFailsStatement data object ∧
    AbsorbedGermFanDataStatement data object ∧
    ∃ routing : ColdFailureRoutingStatement data object,
      ∀ epsilon : ColdEligibleHalfEdge data object,
        Sum.inl epsilon ∉ coldRoutedCandidates data object routing →
          (canonicalTypeBAbsorbedSupport data object epsilon).isSome

/-- **A fact at the Type B support of `G`**: `P` holds at the lane's
canonical support (at every absorbed support, on the absorbed lane). -/
def TypeBLaneAll (P : Finset object.Vertex → Finset object.Vertex → Prop) :
    Prop :=
  (∃ core centres, TypeBOrdinaryLane data object core centres ∧ P core centres) ∨
    (∃ core centres, TypeBDecoratedLane data object core centres ∧
      P core centres) ∨
    (TypeBAbsorbedEntered data object ∧
      ∀ epsilon core centres, TypeBAbsorbedLane data object epsilon core centres →
        P core centres)

/-- **A positive decision arm at the Type B support of `G`**: `P` holds at the
lane's canonical support (at some absorbed support, on the absorbed lane). -/
def TypeBLaneSome (P : Finset object.Vertex → Finset object.Vertex → Prop) :
    Prop :=
  (∃ core centres, TypeBOrdinaryLane data object core centres ∧ P core centres) ∨
    (∃ core centres, TypeBDecoratedLane data object core centres ∧
      P core centres) ∨
    (TypeBAbsorbedEntered data object ∧
      ∃ epsilon core centres, TypeBAbsorbedLane data object epsilon core centres ∧
        P core centres)

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
  TypeBLaneAll data object (fun _core centres =>
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
  TypeBLaneSome data object (fun _core centres =>
    ∃ centre ∈ centres, data.threshold + 1 < object.degree centre)

/-- Node `[68]`, no → `[78]`: every assigned centre of the Type B support has
degree `δ + 1`. -/
def TypeBFanDegreeFourCentresStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun _core centres =>
    ∀ centre ∈ centres, object.degree centre = data.threshold + 1)

/-- Node `[69]` (`cor:heavy-center-local-dichotomy`, tex 2322): at the heavy
arm's Type B support, every heavy assigned centre carries the routed local
dichotomy. -/
def TypeBFanLocalDichotomyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun _core centres =>
    (∃ centre ∈ centres, data.threshold + 1 < object.degree centre) ∧
      ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
        HeavyCentreRoutedAlternative data object centre)

/-- Node `[79]` (`cor:degree-four-local-activation`, tex 2336): every assigned
centre of the Type B support carries the degree-four fan profile. -/
def TypeBFanDegreeFourProfileStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun _core centres =>
    ∀ centre ∈ centres, DegreeFourFanProfile data object centre)

/-! ## Nodes `[70]`--`[72]`, `[80]`--`[81]` -/

/-- Node `[70]` (`lem:fan-certificate`, `def:typeB-fan-safe` (i)): the fan-safe
graph and the certificate-marked cap at every assigned centre of the Type B
support. -/
noncomputable def TypeBFanCertificateCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun _core centres =>
    ∀ centre ∈ centres,
      FanSafeAt data object centre ∧
        ∀ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder)

/-- Nodes `[71]`/`[80]`, yes (`def:marked-typeB-fan`): every assigned centre of
the Type B support carries a fan-certificate labelling, under the cap. -/
noncomputable def TypeBFanCertificateMarkedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun _core centres =>
    ∀ centre ∈ centres,
      ∃ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
        object.degree centre ≤
          Graph.WindowCurvature.fanPackingCap data.windowOrder)

/-- Nodes `[71]`/`[80]`, no: some assigned centre of the Type B support is a
fan-certificate residual centre. -/
noncomputable def TypeBFanCertificateResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun _core centres =>
    ∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre))

/-- Nodes `[72]`/`[81]`, the local B1 fan ledger (`lem:typeB-hybrid-B1`,
tex 13647): every assigned centre of the Type B support carries the hybrid B1
entry at its canonical fan envelope over `W₀ = windowSupport P₀`. -/
noncomputable def TypeBFanHybridEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun _core centres =>
    ∀ centre ∈ centres,
      HybridB1Entry data object centre
        (Graph.TypeBProfileSchedule.canonicalEnvelope object centre)
        (Graph.FiniteObject.windowSupport (canonicalWindowPacking data object)))

/-- Nodes `[72]`/`[81]`, direct-cycle arm (`lem:typeB-direct-fan-window-cycles`,
tex 13398): some assigned centre of the Type B support carries a direct
fan-window configuration at `P₀`. -/
noncomputable def TypeBFanDirectCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun _core centres =>
    ∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      Graph.TypeBDirectCycle.DirectCycleConfiguration object data.windowOrder
        data.LengthOK (canonicalWindowPacking data object) centre)

/-- Nodes `[72]`/`[81]`, direct-cycle-free arm
(`def:direct-cycle-free-closed-pair`, tex 13379). -/
noncomputable def TypeBFanDirectCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun _core centres =>
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre →
      Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
        data.LengthOK (canonicalWindowPacking data object) centre)

/-- Nodes `[72]`/`[81]`, B2 yes (`def:typeB-bridge-statements` B2, tex 14119):
the assigned centres of the Type B support admit a disjoint choice at `P₀`. -/
noncomputable def TypeBB2ChoiceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun core centres =>
    Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres
      centres)

/-- Nodes `[73]`/`[83]`, B2 no (`lem:typeB-bridge-to-overlap`, tex 13927): the
Type B support carries a minimal overlap obstruction at `P₀`. -/
noncomputable def TypeBB2ObstructionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun core centres =>
    Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres))

/-- `prop:typeB-global-local-bridge` (tex 14028): at the B2-failure arm's Type B
support, every minimal overlap obstruction, when its core is a canonical piece
of `P₀`, inherits the five global-to-local constraints. -/
noncomputable def TypeBGlobalLocalBridgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun core centres =>
    Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres) ∧
    ∀ piece : Graph.TypeBRefinedSupport.CanonicalPiece object
        (canonicalWindowPacking data object),
      piece.vertices = core →
      ∀ obstruction : Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale (canonicalWindowPacking data object)
          piece.vertices centres,
        Graph.TypeBRefinedSupport.GlobalLocalReflectionACE data.typeABPresentation
          object data.windowOrder data.LengthOK data.threshold
          data.dischargeScale piece centres obstruction)

/-! ## Nodes `[73]`--`[76]`, `[82]`--`[85]` -/

/-- Node `[74]`/`[82]`, B2(a)--(d) on the one disjoint choice of the Type B
support: its entries refine their candidate charge; when the core is a
canonical piece of `P₀` whose high centres are assigned, the canonical B2
ledger has its exact augmented refinement, its post-ledger core hygiene
(`lem:typeB-postledger-core-hygiene`) and its grouped envelope coverage. -/
noncomputable abbrev TypeBDisjointLedgerStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun core centres =>
    (∃ choice, canonicalTypeBChoice data object core centres = some choice ∧
      ∀ centre (member : centre ∈ centres),
        (choice.entry centre member).EntryRefines data.threshold
          data.dischargeScale core centre) ∧
    ∀ piece : Graph.TypeBRefinedSupport.CanonicalPiece object
        (canonicalWindowPacking data object),
      piece.vertices = core →
      Graph.TypeBRefinedSupport.centres object data.threshold core ⊆ centres →
      ∃ ledger, canonicalTypeBDisjointChoice data object piece.vertices centres =
          some ledger ∧
        ledger.ExactAugmentedLedgerRefinement ∧
        PostLedgerComponents data object ledger ∧
        GroupedEnvelopeCoverage data object ledger)

/-- Node `[74]`/`[82]`, `prop:typeB-bridge-reduction` (tex 14289) on the Type B
support's canonical B2 ledger: a nonnegative remaining core charge gives
`N₀(Y_X) ≥ 0`. -/
noncomputable abbrev TypeBExcludedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun core centres =>
    ∀ ledger, canonicalTypeBDisjointChoice data object core centres = some ledger →
      0 ≤ RemainingCoreCharge data object ledger →
        object.NonNegativeNetCharge core data.threshold data.dischargeScale)

/-- Node `[76]`/`[85]`: a negative Type B support whose core is a canonical piece
of `P₀` keeps a negative post-ledger core on its canonical B2 ledger; its
deficit is carried only through the route-`8` residual `[77]`. -/
noncomputable abbrev TypeBExclusionResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun core centres =>
    ∀ piece : Graph.TypeBRefinedSupport.CanonicalPiece object
        (canonicalWindowPacking data object),
      piece.vertices = core →
      Graph.TypeBRefinedSupport.centres object data.threshold core ⊆ centres →
      object.NegativeNetCharge core data.threshold data.dischargeScale →
      ∃ ledger, canonicalTypeBDisjointChoice data object piece.vertices centres =
          some ledger ∧
        ledger.ExactAugmentedLedgerRefinement ∧
        PostLedgerComponents data object ledger ∧
        ¬ 0 ≤ RemainingCoreCharge data object ledger)

/-- Nodes `[75]`/`[84]` (`def:typeB-residual-mass`, tex 14682): at the
certificate-residual arm's Type B support, the fan-certificate residual centre
is charged to its assigned surplus. -/
noncomputable def TypeBFanCertificateResidualMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun _core centres =>
    ∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre) ∧
      CentreBridgeMassBound data object centre)

/-- Nodes `[73]`/`[75]`, `[83]`/`[84]`: at the B2-failure arm's Type B support,
which carries a minimal overlap obstruction, the assigned centres are charged
to their surplus. -/
noncomputable abbrev TypeBOverlapObstructionMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneSome data object (fun core centres =>
    Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object data.threshold
        data.dischargeScale (canonicalWindowPacking data object) core centres) ∧
      ∀ centre ∈ centres, CentreBridgeMassBound data object centre)

/-- Nodes `[76]`/`[85]`: when the canonical B2 ledger of the Type B support
leaves a negative remaining core, its assigned centres are charged to their
surplus. -/
noncomputable abbrev TypeBExclusionResidualMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBLaneAll data object (fun core centres =>
    ∀ ledger, canonicalTypeBDisjointChoice data object core centres = some ledger →
      ¬ 0 ≤ RemainingCoreCharge data object ledger →
        ∀ centre ∈ centres, CentreBridgeMassBound data object centre)

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
    Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) piece.vertices
      (Graph.TypeBRefinedSupport.centres object data.threshold piece.vertices))

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

end Collections

/-- Nodes `[73]`/`[75]` and `[83]`/`[84]`, `def:typeB-residual-mass`: the Type B
residual fan-mass facts at `P₀`, on its canonical pieces and on the two
canonical role unions. -/
noncomputable abbrev TypeBBridgeMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let ordinary := canonicalOrdinaryBridgeUnion data object
  let grouped := canonicalGroupedBridgeUnion data object
  (∀ component ∈ object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object)),
    let piece := object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) component
    object.NegativeNetCharge piece data.threshold data.dischargeScale →
    0 < object.ambientSurplus piece data.threshold →
    (∀ centre ∈ piece, Graph.IsHighCentre object data.threshold centre →
      CentreBridgeMassBound data object centre) ∧
      (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
          data.threshold data.dischargeScale →
        piece.card + data.dischargeScale *
              object.ambientSurplus piece data.threshold ≤
          data.dischargeScale * object.positiveDeficiency piece data.threshold +
            data.bridgeMassFactor * data.dischargeScale *
              object.ambientSurplus piece data.threshold)) ∧
    (∀ route8 : Finset (Graph.SupportComponents.Connected.Component object
        (object.remainderSupport (canonicalWindowPacking data object))),
      (∀ piece ∈ route8,
        object.ambientSurplus (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) piece)
          data.threshold = 0) →
      (∀ piece ∈ object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object)), piece ∉ route8 →
        Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
          (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) piece) data.threshold
          data.dischargeScale) →
      ∑ piece ∈ object.canonicalPieces (object.remainderSupport (canonicalWindowPacking data object)),
          ((object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) piece).card +
              data.dischargeScale * object.ambientSurplus
                (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) piece) data.threshold -
            data.dischargeScale * object.positiveDeficiency
              (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) piece) data.threshold) ≤
        Graph.TypeBEnvelopeCharge.route8Deficit object (object.remainderSupport (canonicalWindowPacking data object)) data.threshold
            data.dischargeScale route8 +
          data.bridgeMassFactor * data.dischargeScale *
            object.degreeSurplus data.threshold) ∧
    ∀ ordinaryRoute8 : Finset
        (Graph.SupportComponents.Connected.Component object ordinary),
    ∀ groupedRoute8 : Finset
        (Graph.SupportComponents.Connected.Component object grouped),
      (∀ piece ∈ ordinaryRoute8,
        object.ambientSurplus (object.pieceSupport ordinary piece)
          data.threshold = 0) →
      (∀ piece ∈ groupedRoute8,
        object.ambientSurplus (object.pieceSupport grouped piece)
          data.threshold = 0) →
      (∀ piece ∈ object.canonicalPieces ordinary, piece ∉ ordinaryRoute8 →
        Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
          (object.pieceSupport ordinary piece) data.threshold
          data.dischargeScale) →
      (∀ piece ∈ object.canonicalPieces grouped, piece ∉ groupedRoute8 →
        Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
          (object.pieceSupport grouped piece) data.threshold
          data.dischargeScale) →
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
        fanEnvelope = Graph.TypeBProfileSchedule.canonicalEnvelope object ∧
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
