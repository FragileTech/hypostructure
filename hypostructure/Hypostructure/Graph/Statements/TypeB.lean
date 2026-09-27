import Hypostructure.Graph.Statements.TypeA
import Hypostructure.Graph.ColdCorridorTails
import Hypostructure.Graph.DecoratedHandoffTails

/-!
# Statements: TypeB

Proof-agnostic statement definitions of the minimum-degree cycle spine:
Type B per-centre and per-ledger predicates, the triangular and open-port
lemmas, and the fan-closed port routing.  The key statements pinned to the
selected counterexample's Type B support live in `Statements/TypeBLanes.lean`.
Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- `cor:uncompressible` at node `[14]`, as the envelope's admissibility reads
it. -/
abbrev handoffUncompressible (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex → Prop :=
  fun support =>
    ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support

/-- Node `[14]` (`cor:uncompressible`) is literally the envelope's
uncompressibility clause at every support. -/
theorem handoffUncompressible_of_uncompressible {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (uncompressible : UncompressibleStatement data object) :
    ∀ support : Finset object.Vertex, handoffUncompressible data object support :=
  fun support compressible => uncompressible support compressible

/-- The counted core satisfies the paper's single compound core-safety clause:
it is `P₁₃`-free and has no internal sub-support of minimum degree at least the
registered baseline.  Keeping the conjunction in the existing predicate avoids
introducing a second certificate carrier for `lem:decorated-fan-admissibility`. -/
abbrev handoffWindowFree (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Finset object.Vertex → Prop :=
  fun support =>
    (∀ window : Finset object.Vertex, window ⊆ support →
      ¬ object.InducesWindow data.windowOrder window) ∧
    ∀ internal : Finset object.Vertex, internal ⊆ support →
      ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce internal)

/-- **`lem:absorbed-germ-fan-data` (ii) at one selected half-edge `ε` of G**
(tex 7926-7952, with `lem:typeA-high-degree-handoff`, tex 11110-11131, and
`def:decorated-fan-envelope`, tex 10898-10925), read at node `[153]`'s retained
routing.  `handoff = (z, Y)`:

* `z` is the least high vertex of `ε`'s first-failure prefix (the heavy
  centre; its node-`[10]` neighbours sit at the baseline);
* "the two corridor incidences at `z` are distinct, so the segments of the
  corridor on either side of `z` are two connector tails separated at `z`,
  which is the decorated handoff configuration of
  `lem:typeA-high-degree-handoff`": the envelope has the one decoration
  `H = {z}`, its assigned first neighbours are the two corridor incidences
  `a` (entry side) and `b` (exit side), and its arms are the two corridor
  segments at `z` cut at their first entry into the counted core
  (`DecoratedHandoff.firstEntryArm`);
* `Y` is that counted core: a connected remainder core `Y ⊆ R(P₀)` (hence
  `P₁₃`-free with empty internal `3`-core), with `z ∉ Y` ("the only new
  vertices counted outside `Y` are the decorations", tex 11155), and every
  full handoff path `z a A_{z,a}` is simple.

The paper never names `Y` for a cold corridor; this is the envelope its
sentence asserts. -/
noncomputable def AbsorbedHandoffAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (handoff : object.Vertex × Finset object.Vertex) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact
    let centre := handoff.1
    let core := handoff.2
    let classified := coldRoutedClassified data object routing
    let corridor := coldOccurrenceCorridorAt data object classified epsilon
    let traceEnd := coldRoutedTraceEnd data object routing epsilon
    ∃ firstIndex : corridor.Segment,
      centre = corridor.head firstIndex ∧
      firstIndex.1 ≤ traceEnd ∧
      data.threshold < object.degree centre ∧
        (∀ earlier : corridor.Segment, earlier.1 < firstIndex.1 →
          object.degree (corridor.head earlier) ≤ data.threshold) ∧
        (∀ neighbour : object.Vertex, object.graph.Adj centre neighbour →
          object.degree neighbour = data.threshold) ∧
      let entry := corridor.entryNeighbour firstIndex.1
      let exit := corridor.exitNeighbour firstIndex.1
      Graph.SupportComponents.Connected.ConnectedOn object core ∧
        core ⊆ object.remainderSupport
          (canonicalWindowPacking data object) ∧
        centre ∉ core ∧
        entry ≠ exit ∧
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object
              (canonicalWindowPacking data object)),
          envelope.core = core ∧
            envelope.decorations = {centre} ∧
            envelope.assigned centre = {entry, exit} ∧
            envelope.arm centre entry =
              Graph.DecoratedHandoff.firstEntryArm core
                (corridor.entryTail firstIndex.1) ∧
            envelope.arm centre exit =
              Graph.DecoratedHandoff.firstEntryArm core
                (corridor.exitTail firstIndex.1) ∧
            (∀ first ∈ envelope.assigned centre,
              centre ∉ envelope.arm centre first) ∧
            Graph.DecoratedHandoff.Admissible object data.LengthOK
              (handoffUncompressible data object)
              (handoffWindowFree data object) envelope

/-- **The counted remainder core at `ε`'s heavy centre** (the configuration
`lem:absorbed-germ-fan-data` (ii) asserts, tex 7926-7952, read through
`lem:typeA-high-degree-handoff` and `def:decorated-fan-envelope`): a connected
`Y ⊆ R(P₀)` with `z ∉ Y` which both corridor segments at the corridor vertex
`z` of index `firstIndex` enter.  Node `[177]` decides this at G's canonical
absorbed half-edge (`AbsorbedHandoffCoreStatement` /
`AbsorbedHandoffCoreAbsentStatement`); given such `Y`, the admissible envelope
`AbsorbedHandoffAt` is built from G's facts
(`Contracts.TypeB.absorbedHandoffAt_of_remainderCore`). -/
noncomputable def AbsorbedRemainderCoreAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (firstIndex : (coldOccurrenceCorridorAt data object
      (coldRoutedClassified data object routing) epsilon).Segment) : Prop :=
  let corridor := coldOccurrenceCorridorAt data object
    (coldRoutedClassified data object routing) epsilon
  ∃ core : Finset object.Vertex,
    Graph.SupportComponents.Connected.ConnectedOn object core ∧
      core ⊆ object.remainderSupport (canonicalWindowPacking data object) ∧
      corridor.head firstIndex ∉ core ∧
      (∃ vertex ∈ corridor.entryTail firstIndex.1, vertex ∈ core) ∧
      ∃ vertex ∈ corridor.exitTail firstIndex.1, vertex ∈ core

/-- **The registered discharge profile of the Type B fan ledger**
(`def:typeB-multiclosed-residual`): baseline `δ`, discharge rate `α = 1/s` at
the registered discharge scale `s`, and the registered entropy denominator.  The
closed-neighbour deficit reads only `α`; no statement quantifies over another
profile. -/
def typeBDischargeProfile (data : Parameters) :
    Graph.ReceiverLoad.LoadCapacityProfile where
  baselineDegree := data.threshold
  loadMultiplier := data.dischargeScale
  remainderEntropyThresholdDenominator := data.entropyDenominator

/-- `cor:compatible-pair-typeB-routing` at one assigned profile and one
fan-compatible open pair, at the registered discharge rate `α = 1/s`:
`D_B(𝔉_h) ≥ (k+1)α - 1 > 0`. -/
def CompatiblePairRoutes (data : Parameters) (object : Graph.FiniteObject.{u})
    (profile : Graph.TypeBFanClosedPorts.Profile object)
    (left right : object.Vertex) : Prop :=
  Graph.NormalForm object data.threshold profile.marked.fan.hub →
    Graph.FanCompatible object profile.marked.fan.hub left right →
    left ∈ profile.remainder →
    right ∈ profile.remainder →
    (∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub left shoulder →
        shoulder ∈ profile.envelope) →
    (∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub right shoulder →
        shoulder ∈ profile.envelope) →
    2 ≤ profile.closedCount ∧
      ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (data.dischargeScale : ℚ)) - 1
        ≤ profile.closedNeighbourDeficit (typeBDischargeProfile data) ∧
      0 < profile.closedNeighbourDeficit (typeBDischargeProfile data)

/-- `prop:triangular-port-typeB-routing` at one assigned profile and one
family of `k - 2` triangular ports at a heavy centre `k > δ + 1`, at the
registered discharge rate: `D_B(𝔉_h) ≥ ((s+1)k - (s(δ+2) - 1))/s`, the
manuscript's `(5k - 19)/4` at `δ = 3`, `s = 4`. -/
def TriangularPortsRoute (data : Parameters) (object : Graph.FiniteObject.{u})
    (profile : Graph.TypeBFanClosedPorts.Profile object)
    (ports : Finset object.Vertex) : Prop :=
  Graph.NormalForm object data.threshold profile.marked.fan.hub →
    ports ⊆ Graph.triangularEndpoints object profile.marked.fan.hub →
    ports.card = object.degree profile.marked.fan.hub - 2 →
    data.threshold + 1 < object.degree profile.marked.fan.hub →
    (∀ endpoint ∈ ports, endpoint ∈ profile.remainder) →
    (∀ endpoint ∈ ports, ∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub endpoint shoulder →
        shoulder ∈ profile.envelope) →
    ports.card ≤ profile.closedCount ∧
      (((data.dischargeScale : ℚ) + 1) *
            (object.degree profile.marked.fan.hub : ℚ) -
          ((data.dischargeScale : ℚ) * ((data.threshold : ℚ) + 2) - 1)) /
          (data.dischargeScale : ℚ) ≤
        profile.closedNeighbourDeficit (typeBDischargeProfile data) ∧
      0 < profile.closedNeighbourDeficit (typeBDischargeProfile data)

/-- **The assigned fan envelope at a centre of a Type B support `(Y, H)`**
(`def:marked-typeB-fan`, `def:typeB-assigned-ledger`, the envelope `E_h` of
`def:typeB-residual-mass`): the centre together with the assigned support
`Y ∪ H`.  A fan neighbour `u` of `h` is cubic-closed exactly when its two
non-`h` incidences are assigned to that support, i.e. `u` has internal degree
`3` in the assigned fan envelope.  It is literally the envelope on which the B2
candidate entries of `(Y, H)` are evaluated
(`TypeBRefinedSupport.fanEnvelope`). -/
noncomputable abbrev typeBFanEnvelope {object : Graph.FiniteObject.{u}}
    (core centres : Finset object.Vertex) (centre : object.Vertex) :
    Finset object.Vertex :=
  Graph.TypeBRefinedSupport.fanEnvelope core centres centre

/-- **The assigned Type B fan-window profile of the support `(Y, H)`**
(`def:typeB-window-incidence-profile`, `def:fan-closed-port`): its centre is an
assigned centre of `H`, its recorded window is the packed-window union
`W₀ = windowSupport P₀` of the canonical maximal packing, and its envelope is the
assigned fan envelope of its centre in `(Y, H)`.  Only the certificate labelling
of the marked fan is left free. -/
def IsFixedTypeBProfile (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex)
    (profile : Graph.TypeBFanClosedPorts.Profile object) : Prop :=
  profile.marked.fan.hub ∈ centres ∧
    profile.window =
      Graph.FiniteObject.windowSupport (canonicalWindowPacking data object) ∧
    profile.envelope = typeBFanEnvelope core centres profile.marked.fan.hub

/-- **G's canonical fan-certificate labelling at a centre** (node `[71]`,
`def:marked-typeB-fan`): the `Classical.choice` of a fan-certificate labelling
`S_h : N(h) → 𝓛` of `h` in `G`, or `none` when `h` carries none (a
fan-certificate residual centre). -/
noncomputable def canonicalFanCertificateLabelling (data : Parameters)
    (object : Graph.FiniteObject.{u}) (centre : object.Vertex) :
    Option (Graph.FanCertificateLabelling object data.windowOrder centre) := by
  classical
  exact if h : Nonempty (Graph.FanCertificateLabelling object data.windowOrder centre)
    then some (Classical.choice h) else none

theorem canonicalFanCertificateLabelling_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {centre : object.Vertex} :
    canonicalFanCertificateLabelling data object centre = none ↔
      IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre) := by
  classical
  unfold canonicalFanCertificateLabelling
  split
  · next h => simp only [reduceCtorEq, false_iff, not_isEmpty_iff]; exact h
  · next h => simpa using h

/-- **The assigned centres of `(Y, H)` are certificate-marked at `[71]`**: every
`h ∈ H` carries G's canonical fan-certificate labelling, and the label packing
caps its degree (`lem:fan-certificate`: `d_G(h) ≤ 8`, the registered cap). -/
def TypeBCertificateMarkedAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (centres : Finset object.Vertex) : Prop :=
  ∀ centre ∈ centres,
    ∃ marking, canonicalFanCertificateLabelling data object centre = some marking ∧
      object.degree centre ≤ Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- **B2 at the support `(Y, H)`** (`def:typeB-bridge-statements` B2(a)--(c),
`def:typeB-candidate-ledger`, tex 14119): the support has no fan-certificate
residual centre (every demand is certificate-marked at `[71]`), and the demands
`H` admit a choice of candidate entries --- each evaluated on the assigned fan
envelope `E_h` of `(Y, H)` --- with pairwise disjoint ledger supports. -/
def TypeBB2At (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) : Prop :=
  TypeBCertificateMarkedAt data object centres ∧
    Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres centres

/-- **G's canonical minimal overlap obstruction of `(Y, H)`**
(`def:typeB-overlap-obstruction`, `lem:typeB-bridge-to-overlap`): the
`Classical.choice` of a minimal Type B overlap obstruction among the demands `H`
at `P₀`, or `none`. -/
noncomputable def canonicalOverlapObstruction (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) :
    Option (Graph.TypeBRefinedSupport.OverlapObstruction object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres) := by
  classical
  exact if h : Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
      data.threshold data.dischargeScale (canonicalWindowPacking data object) core
      centres) then some (Classical.choice h) else none

theorem canonicalOverlapObstruction_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {core centres : Finset object.Vertex}
    (present : Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
      data.threshold data.dischargeScale (canonicalWindowPacking data object) core
      centres)) :
    ∃ obstruction, canonicalOverlapObstruction data object core centres =
      some obstruction := by
  classical
  unfold canonicalOverlapObstruction
  exact ⟨_, dif_pos present⟩

/-- **`lem:typeB-bridge-deficit-bound` at the support `(Y, H)`** (tex 14803):
when the non-window core carries no route-`8` residual profile --- the Type A
routing and unsaturation pair on `Y` off its own centres
(`BridgeResidualComponentAt`) --- the negative part is charged to the assigned
surplus, `No₋(X) ≤ F·Σ_{h ∈ H}(d_G(h) − δ)`, written subtraction-free at the
discharge scale:
`|Y| + s·σ(H) ≤ s·def⁺(Y) + F·s·σ(H)` with `σ(H) = ambientSurplus H`. -/
def TypeBBridgeDeficitBoundAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) : Prop :=
  Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object core data.threshold
      data.dischargeScale →
    core.card + data.dischargeScale * object.ambientSurplus centres data.threshold ≤
      data.dischargeScale * object.positiveDeficiency core data.threshold +
        data.bridgeMassFactor * data.dischargeScale *
          object.ambientSurplus centres data.threshold

/-- **`s·No(X)` of the support `X = (Y, H)`** (`def:net-charge`,
`def:typeB-assigned-ledger`): `s·def⁺(Y) − s·σ(H) − |Y|`. -/
noncomputable def typeBScaledNetCharge (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Int :=
  ((data.dischargeScale * object.positiveDeficiency core data.threshold : Nat) : Int) -
    ((data.dischargeScale * object.ambientSurplus centres data.threshold : Nat) : Int) -
    (core.card : Int)

/-- The two routed alternatives of node `[69]` at one heavy centre:
`cor:heavy-center-local-dichotomy` with each alternative carried to fan-closed
ports in every fixed profile at the centre --- a fan-compatible open pair
by `cor:compatible-pair-typeB-routing`, or a family of `d_G(h) - 2` triangular
ports (in particular three) by `prop:triangular-port-typeB-routing`. -/
def HeavyCentreRoutedAlternative (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex)
    (centre : object.Vertex) : Prop :=
  (∃ left right : object.Vertex,
      Graph.FanCompatible object centre left right ∧
        ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
          IsFixedTypeBProfile data object core centres profile →
          profile.marked.fan.hub = centre →
            CompatiblePairRoutes data object profile left right) ∨
    (∃ ports ⊆ Graph.triangularEndpoints object centre,
      ports.card = object.degree centre - 2 ∧ 3 ≤ ports.card ∧
        ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
          IsFixedTypeBProfile data object core centres profile →
          profile.marked.fan.hub = centre →
            TriangularPortsRoute data object profile ports)

/-- `lem:same-center-open-port-compatibility` on the selected residual object.
The paper's port hypotheses are all explicit; the conclusion is the canonical
fan-compatible pair used by the heavy-centre alternative. -/
def SameCenterOpenPortCompatibilityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    Graph.IsHighCentre object data.threshold centre →
      ∀ left right : object.Vertex,
        object.graph.Adj centre left →
        object.graph.Adj centre right →
        left ≠ right →
        ¬ object.graph.Adj left right →
        Graph.IsOpenPort object centre left →
        Graph.IsOpenPort object centre right →
        Graph.FanCompatible object centre left right

/-- The degree-four fan profile of `cor:degree-four-local-activation` at one
centre of the support `(Y, H)`: degree `δ + 1`, a fan-compatible open pair or
`δ - 1` triangular ports, centre surplus `1`, and the registered-scale
closed-neighbour profile of the assigned fan envelope of the centre. -/
def DegreeFourFanProfile (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) (centre : object.Vertex) : Prop :=
  object.degree centre = data.threshold + 1 ∧
    ((∃ left right : object.Vertex,
        Graph.FanCompatible object centre left right) ∨
      data.threshold - 1 ≤ (Graph.triangularEndpoints object centre).card) ∧
    object.degree centre - data.threshold = 1 ∧
    Graph.TypeBFanIncidence.closedCount object data.threshold
        (typeBFanEnvelope core centres centre) centre ≤
      data.threshold + 1 ∧
    Graph.TypeBFanIncidence.scaledDeficit object data.threshold
        data.dischargeScale
        (typeBFanEnvelope core centres centre) centre =
      (data.dischargeScale : Int) *
          (Graph.TypeBFanIncidence.closedCount object data.threshold
            (typeBFanEnvelope core centres centre)
            centre : Int) -
        (data.dischargeScale : Int) * (data.threshold : Int) +
        ((data.threshold : Int) + 2)

/-! ### G's canonical triangular fan core

`def:triangular-fan-core` at a heavy centre `h` and a family of triangular ports
of `h` (given by their endpoints): the shoulder pair of a port is
`N_G(x) \ {h}`, the core is `{h} ∪ ports ∪ shoulders`, and the four incidence
relations are the completion, central, cross-triangular and outside edges.
These are G's own objects; the lane facts below are stated at them. -/

/-- The shoulders `N_G(x) \ {h}` of the triangular port with endpoint `x` at `h`. -/
noncomputable def triangularShoulders (object : Graph.FiniteObject.{u})
    (centre endpoint : object.Vertex) : Finset object.Vertex := by
  classical
  exact (object.orderedNeighbors endpoint).toFinset.erase centre

/-- The triangular fan core `{h} ∪ ports ∪ shoulders`. -/
noncomputable def triangularCore (object : Graph.FiniteObject.{u})
    (centre : object.Vertex) (ports : Finset object.Vertex) :
    Finset object.Vertex := by
  classical
  exact insert centre (ports ∪ ports.biUnion (triangularShoulders object centre))

/-- A shoulder completion edge: an edge at a shoulder other than the two edges
inside its triangular port. -/
def triangularCompletion (object : Graph.FiniteObject.{u}) (centre : object.Vertex)
    (ports : Finset object.Vertex) (endpoint shoulder target : object.Vertex) : Prop :=
  endpoint ∈ ports ∧ shoulder ∈ triangularShoulders object centre endpoint ∧
    object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
      target ∉ triangularShoulders object centre endpoint

/-- A central completion edge: it lands at the centre. -/
def triangularCentral (object : Graph.FiniteObject.{u}) (centre : object.Vertex)
    (ports : Finset object.Vertex) (endpoint shoulder target : object.Vertex) : Prop :=
  triangularCompletion object centre ports endpoint shoulder target ∧ target = centre

/-- A cross-triangular completion edge: it lands at a shoulder of another port. -/
def triangularCrossTriangular (object : Graph.FiniteObject.{u})
    (centre : object.Vertex) (ports : Finset object.Vertex)
    (endpoint shoulder target : object.Vertex) : Prop :=
  triangularCompletion object centre ports endpoint shoulder target ∧
    ∃ other ∈ ports, other ≠ endpoint ∧
      target ∈ triangularShoulders object centre other

/-- An outside completion edge: it leaves the core and avoids `N_G(h)`. -/
def triangularOutside (object : Graph.FiniteObject.{u}) (centre : object.Vertex)
    (ports : Finset object.Vertex) (endpoint shoulder target : object.Vertex) : Prop :=
  triangularCompletion object centre ports endpoint shoulder target ∧
    target ∉ triangularCore object centre ports ∧ ¬ object.graph.Adj centre target

/-- `def:triangular-fan-core` on the active object.  Ports are represented by
their endpoints because the centre is fixed.  The shoulder finset is exactly
`N_G(x) \setminus {h}`; the core is the paper's induced vertex set, so the
ambient graph supplies its induced adjacency.  The four incidence relations
record precisely completion, central, cross-triangular, and outside edges. -/
def TriangularFanCoreLaw (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex,
        ports.Nonempty →
          ports ⊆ Graph.triangularEndpoints object centre →
            ∃ shoulders : object.Vertex → Finset object.Vertex,
              ∃ core : Finset object.Vertex,
                ∃ completion central crossTriangular outside :
                    object.Vertex → object.Vertex → object.Vertex → Prop,
                  (∀ endpoint ∈ ports,
                    (∀ vertex : object.Vertex,
                      vertex ∈ shoulders endpoint ↔
                        Graph.IsShoulder object centre endpoint vertex) ∧
                    (shoulders endpoint).card = 2 ∧
                    ∃ left right : object.Vertex,
                      left ∈ shoulders endpoint ∧
                        right ∈ shoulders endpoint ∧ left ≠ right ∧
                          object.graph.Adj left right) ∧
                  (∀ vertex : object.Vertex,
                    vertex ∈ core ↔
                      vertex = centre ∨ vertex ∈ ports ∨
                        ∃ endpoint ∈ ports, vertex ∈ shoulders endpoint) ∧
                  (∀ endpoint shoulder target : object.Vertex,
                    completion endpoint shoulder target ↔
                      endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                        object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                          target ∉ shoulders endpoint) ∧
                  (∀ endpoint shoulder target : object.Vertex,
                    central endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target = centre) ∧
                  (∀ endpoint shoulder target : object.Vertex,
                    crossTriangular endpoint shoulder target ↔
                      completion endpoint shoulder target ∧
                        ∃ other ∈ ports,
                          other ≠ endpoint ∧ target ∈ shoulders other) ∧
                  ∀ endpoint shoulder target : object.Vertex,
                    outside endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target ∉ core ∧
                    ¬ object.graph.Adj centre target

/-- `lem:triangular-shoulder-completion`, stated directly on the active graph.
`completion` is the paper's incidence predicate: an edge at a shoulder other
than the two edges inside its triangular port. -/
def TriangularShoulderCompletionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ endpoint ∈ Graph.triangularEndpoints object centre,
        ∃ left right : object.Vertex,
          Graph.IsShoulder object centre endpoint left ∧
          Graph.IsShoulder object centre endpoint right ∧ left ≠ right ∧
          object.graph.Adj left right ∧
          (∀ shoulder, shoulder = left ∨ shoulder = right →
            ∃ target : object.Vertex,
              object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                target ≠ left ∧ target ≠ right) ∧
          ¬ (object.graph.Adj centre left ∧ object.graph.Adj centre right) ∧
          (∀ shoulder, shoulder = left ∨ shoulder = right →
            object.graph.Adj centre shoulder →
              object.degree shoulder = data.threshold ∧
              ∀ target : object.Vertex,
                (object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                  target ≠ left ∧ target ≠ right) ↔ target = centre) ∧
          ∀ shoulder target,
            shoulder = left ∨ shoulder = right →
            object.graph.Adj shoulder target → target ≠ endpoint →
              target ≠ left → target ≠ right →
                object.graph.Adj centre target → target = centre

/-- `lem:triangular-port-return`, with `R_p` the endpoint-to-centre return and
`Q_p = R_p.tail`.  Thus the restored cycle has length `|Q_p| + 2 = |R_p| + 1`.
The final conjunct is precisely the noncentral shoulder-completion incidence
used by the next first-landing lemma. -/
def TriangularPortReturnStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ endpoint ∈ Graph.triangularEndpoints object centre,
        ∃ left right : object.Vertex,
          Graph.IsShoulder object centre endpoint left ∧
          Graph.IsShoulder object centre endpoint right ∧ left ≠ right ∧
          ∃ return' : Graph.FiniteObject.SurplusPort.PortReturn
              object centre endpoint left right,
            endpoint ∉ return'.path.tail.support ∧
            ¬ data.LengthOK (return'.path.length + 1) ∧
            (return'.path.tail.length ≠ 1 →
              ∃ shoulder target : object.Vertex,
                (shoulder = left ∨ shoulder = right) ∧
                object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                target ≠ left ∧ target ≠ right ∧ target ≠ centre ∧
                s(shoulder, target) ∈ return'.path.tail.edges)

/-- `lem:triangular-first-landing`, stated for the literal predicates supplied
by `def:triangular-fan-core`.  The three displayed arms include their mutual
exclusions, so “exactly one” is part of the proposition rather than prose. -/
def TriangularFirstLandingLaw (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex,
        ports.Nonempty →
          ports ⊆ Graph.triangularEndpoints object centre →
            ∀ shoulders : object.Vertex → Finset object.Vertex,
              ∀ core : Finset object.Vertex,
                ∀ completion central crossTriangular outside :
                    object.Vertex → object.Vertex → object.Vertex → Prop,
                  (∀ endpoint ∈ ports,
                    (∀ vertex : object.Vertex,
                      vertex ∈ shoulders endpoint ↔
                        Graph.IsShoulder object centre endpoint vertex) ∧
                    (shoulders endpoint).card = 2 ∧
                    ∃ left right : object.Vertex,
                      left ∈ shoulders endpoint ∧
                        right ∈ shoulders endpoint ∧ left ≠ right ∧
                          object.graph.Adj left right) →
                  (∀ vertex : object.Vertex,
                    vertex ∈ core ↔
                      vertex = centre ∨ vertex ∈ ports ∨
                        ∃ endpoint ∈ ports, vertex ∈ shoulders endpoint) →
                  (∀ endpoint shoulder target : object.Vertex,
                    completion endpoint shoulder target ↔
                      endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                        object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                          target ∉ shoulders endpoint) →
                  (∀ endpoint shoulder target : object.Vertex,
                    central endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target = centre) →
                  (∀ endpoint shoulder target : object.Vertex,
                    crossTriangular endpoint shoulder target ↔
                      completion endpoint shoulder target ∧
                        ∃ other ∈ ports,
                          other ≠ endpoint ∧ target ∈ shoulders other) →
                  (∀ endpoint shoulder target : object.Vertex,
                    outside endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target ∉ core ∧
                        ¬ object.graph.Adj centre target) →
                  ∀ endpoint shoulder target : object.Vertex,
                    completion endpoint shoulder target →
                      ((central endpoint shoulder target ∧
                          ¬ crossTriangular endpoint shoulder target ∧
                          ¬ outside endpoint shoulder target) ∨
                        (crossTriangular endpoint shoulder target ∧
                          ¬ central endpoint shoulder target ∧
                          ¬ outside endpoint shoulder target) ∨
                        (outside endpoint shoulder target ∧
                          ¬ central endpoint shoulder target ∧
                          ¬ crossTriangular endpoint shoulder target)) ∧
                      (object.graph.Adj centre target → target = centre) ∧
                      target ∉ ports

/-- `lem:triangular-cross-shoulder` on the target-safe selected object.
An edge between two distinct shoulder pairs is represented by the literal
cross-incidence predicate in both orientations.  The first conclusion is the
paper's high-shoulder arm (a shoulder above the baseline) after its
quadrilateral arm is discharged by target safety; the second is the stated
matching-size consequence on the residual where every shoulder sits at the
baseline. -/
def TriangularCrossShoulderLaw (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex,
        ports.Nonempty →
          ports ⊆ Graph.triangularEndpoints object centre →
            ∀ shoulders : object.Vertex → Finset object.Vertex,
              ∀ crossTriangular :
                  object.Vertex → object.Vertex → object.Vertex → Prop,
                (∀ endpoint ∈ ports,
                  (∀ vertex : object.Vertex,
                    vertex ∈ shoulders endpoint ↔
                      Graph.IsShoulder object centre endpoint vertex) ∧
                  (shoulders endpoint).card = 2 ∧
                  ∃ left right : object.Vertex,
                    left ∈ shoulders endpoint ∧
                      right ∈ shoulders endpoint ∧ left ≠ right ∧
                        object.graph.Adj left right) →
                (∀ endpoint shoulder target : object.Vertex,
                  crossTriangular endpoint shoulder target ↔
                    endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                      object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                        target ∉ shoulders endpoint ∧
                        ∃ other ∈ ports,
                          other ≠ endpoint ∧ target ∈ shoulders other) →
                ∀ first ∈ ports, ∀ second ∈ ports, first ≠ second →
                  let between := fun source target =>
                    crossTriangular first source target ∧
                      crossTriangular second target source
                  (∀ source target source' target',
                    between source target → between source' target' →
                      (source ≠ source' ∨ target ≠ target') →
                        ∃ shoulder,
                          (shoulder ∈ shoulders first ∨
                            shoulder ∈ shoulders second) ∧
                          data.threshold < object.degree shoulder) ∧
                  ((∀ shoulder,
                      (shoulder ∈ shoulders first ∨
                        shoulder ∈ shoulders second) →
                      object.degree shoulder ≤ data.threshold) →
                    ∀ source target source' target',
                      between source target → between source' target' →
                        source = source' ∧ target = target')

/-- `def:open-port-suppression`, identified with the generic simultaneous
tight-vertex suppression construction.  `CompatibleFamily` contains clauses
(a)--(c), `CenterCapacity` is clause (d), and `suppressed_adj` is the displayed
definition of `G / Q`. -/
noncomputable def OpenPortSuppressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ family : Graph.TightVertexSuppression.CompatibleFamily object,
    (∀ index,
      data.threshold <
        object.degree (family.configuration index).center) →
      (∀ index other,
        object.graph.Adj (family.configuration index).vertex other ↔
          other = (family.configuration index).center ∨
            other = (family.configuration index).left ∨
              other = (family.configuration index).right) ∧
      (∀ ⦃first second⦄, first ≠ second →
        Disjoint
          ({(family.configuration first).vertex,
            (family.configuration first).left,
            (family.configuration first).right} : Set object.Vertex)
          {(family.configuration second).vertex,
            (family.configuration second).left,
            (family.configuration second).right}) ∧
      (∀ first second,
        (family.configuration first).center ≠
            (family.configuration second).vertex ∧
          (family.configuration first).center ≠
            (family.configuration second).left ∧
          (family.configuration first).center ≠
            (family.configuration second).right) ∧
      Function.Injective (fun index =>
        s((family.configuration index).left,
          (family.configuration index).right)) ∧
      (∀ index,
        ¬ object.graph.Adj (family.configuration index).left
          (family.configuration index).right) ∧
      (family.CenterCapacity data.threshold ↔
        ∀ centre, data.threshold < object.degree centre →
          family.centerLoad centre ≤ object.degree centre - data.threshold) ∧
      family.deletedVertices = Finset.univ.image
        (fun index => (family.configuration index).vertex) ∧
      ∀ left right : family.suppressed.Vertex,
        family.suppressed.graph.Adj left right ↔
          object.graph.Adj left.1 right.1 ∨
            ∃ index,
              (left.1 = (family.configuration index).left ∧
                right.1 = (family.configuration index).right) ∨
              (left.1 = (family.configuration index).right ∧
                right.1 = (family.configuration index).left)

/-- `lem:open-port-suppression-safe`.  The capacity hypothesis is written in
the paper's clause-(d) form; the preceding definition fact identifies it with
the canonical simultaneous-suppression `CenterCapacity`.  The suppressed
graph is already a `FiniteObject`, so its finiteness and simplicity are
present in the type and the mathematical conclusion left to prove is the
paper's pointwise minimum-degree assertion. -/
noncomputable def OpenPortSuppressionSafeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ family : Graph.TightVertexSuppression.CompatibleFamily object,
    (∀ index,
      data.threshold <
        object.degree (family.configuration index).center) →
    (∀ centre, data.threshold < object.degree centre →
      family.centerLoad centre ≤ object.degree centre - data.threshold) →
    ∀ vertex : family.suppressed.Vertex,
      3 ≤ family.suppressed.degree vertex

/-- `lem:single-open-port-suppression-witness`.  `OpenPortWitness` states that
the path is simple, avoids the deleted port vertex, and has accepted restored
length.  Via `lengthOK_iff_powerOfTwo`, this is exactly a path of length
`2^j - 1` for some `j ≥ 2`. -/
noncomputable def SingleOpenPortSuppressionWitnessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ configuration : Graph.TightVertexSuppression.Configuration object,
    data.threshold < object.degree configuration.center →
      Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness object
        data.LengthOK configuration.vertex configuration.left
          configuration.right)

/-- `lem:suppressed-family-critical-cycle`.  The first conjunct is the
minimality-produced accepted cycle using a nonempty set of added chords.  The
second is the paper's conclusion for every accepted suppressed cycle: its
simultaneous expansion is a simple source cycle, has one extra edge per used
chord, and its lifted length is not accepted. -/
noncomputable def SuppressedFamilyCriticalCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ family : Graph.TightVertexSuppression.CompatibleFamily object,
    Nonempty family.Index →
    (∀ index,
      data.threshold <
        object.degree (family.configuration index).center) →
    (∀ centre, data.threshold < object.degree centre →
      family.centerLoad centre ≤ object.degree centre - data.threshold) →
    (∃ certificate : Graph.CycleCertificate family.suppressed data.LengthOK,
      (family.usedChords certificate.walk).Nonempty) ∧
    ∀ certificate : Graph.CycleCertificate family.suppressed data.LengthOK,
      (family.usedChords certificate.walk).Nonempty ∧
        ∃ expanded : Graph.TightVertexSuppression.CompatibleFamily.ExpandedCycle
            family certificate,
          expanded.walk.length = certificate.walk.length +
              (family.usedChords certificate.walk).card ∧
            ¬ data.LengthOK expanded.walk.length

/-- `def:typeB-fan-safe`, clause (i), at one centre `h`: no two distinct fan
neighbours are joined by a simple return in `G - h` whose closing length is
accepted. -/
def FanSafeAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (centre : object.Vertex) : Prop :=
  ∀ first second : object.Vertex,
    object.graph.Adj centre first → object.graph.Adj centre second →
      first ≠ second →
      ∀ return' : Graph.DecoratedHandoff.FanReturn object centre first second,
        ¬ data.LengthOK (return'.walk.length + 2)

/-- `def:fan-closed-port` at the assigned Type-B profiles of the support
`(Y, H)`.  The equivalence exposes clauses (a)--(c) of the manuscript; clause
(c) is the derived incidence classification proved by
`TypeBFanClosedPorts.IsFanClosed.incidence_classified`. -/
def FanClosedPortAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object core centres profile →
    ∀ endpoint : object.Vertex,
    profile.IsFanClosed endpoint ↔
      endpoint ∈ profile.remainder ∧
      (∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub endpoint shoulder →
          shoulder ∈ profile.envelope) ∧
      (∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub endpoint shoulder →
          profile.IsWindowIncidence endpoint shoulder ∨
            profile.IsNonWindowIncidence endpoint shoulder)

/-- `lem:compatible-pair-fan-closure`, in the exact canonical upstream form. -/
def CompatiblePairFanClosureAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object core centres profile →
    ∀ left right : object.Vertex,
    Graph.FanCompatible object profile.marked.fan.hub left right →
    left ∈ profile.remainder →
    right ∈ profile.remainder →
    (∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub left shoulder →
        shoulder ∈ profile.envelope) →
    (∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub right shoulder →
        shoulder ∈ profile.envelope) →
    profile.IsFanClosed left ∧ profile.IsFanClosed right ∧ left ≠ right

/-- `prop:fan-closed-port-typeB-routing`, at the assigned profiles of the support `(Y, H)`, at
the registered discharge rate `α = 1/s`: `r ≥ 2` fan-closed ports give
`D_B(𝔉_h) ≥ r - (δ - (k+1)α) ≥ (k+1)α - 1 > 0`. -/
def FanClosedPortTypeBRoutingAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object core centres profile →
    Graph.NormalForm object data.threshold profile.marked.fan.hub →
    ∀ ports : Finset object.Vertex,
      (∀ vertex ∈ ports, profile.IsFanClosed vertex) →
      2 ≤ ports.card →
      ports.card ≤ profile.closedCount ∧
        (ports.card : ℚ) -
            ((data.threshold : ℚ) -
              ((object.degree profile.marked.fan.hub : ℚ) + 1) *
                (1 / (data.dischargeScale : ℚ)))
          ≤ profile.closedNeighbourDeficit (typeBDischargeProfile data) ∧
        ((object.degree profile.marked.fan.hub : ℚ) + 1) *
            (1 / (data.dischargeScale : ℚ)) - 1
          ≤ profile.closedNeighbourDeficit (typeBDischargeProfile data) ∧
        0 < profile.closedNeighbourDeficit (typeBDischargeProfile data)

/-- `cor:compatible-pair-typeB-routing`, at the assigned profiles of the support `(Y, H)`. -/
def CompatiblePairTypeBRoutingAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object core centres profile →
    ∀ left right : object.Vertex,
    CompatiblePairRoutes data object profile left right

/-- `prop:triangular-port-typeB-routing`, at the assigned profiles of the support `(Y, H)`.
The family has the manuscript's exact size `k - 2`; every endpoint is recorded
on the remainder side and both of its triangular shoulder incidences are
assigned to the fan envelope. -/
def TriangularPortTypeBRoutingAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object core centres profile →
    ∀ ports : Finset object.Vertex,
    TriangularPortsRoute data object profile ports

/-- The local B1 incidence calculation (`lem:typeB-hybrid-incidence-budget`,
`lem:typeB-hybrid-B1`) at one marked high centre and one fan envelope. -/
noncomputable def HybridB1Entry (data : Parameters)
    (object : Graph.FiniteObject.{u}) (centre : object.Vertex)
    (envelope windowSupport : Finset object.Vertex) : Prop :=
  (∀ left ∈ Graph.TypeBFanIncidence.closedNeighbours object
      data.threshold envelope centre,
    ∀ right ∈ Graph.TypeBFanIncidence.closedNeighbours object
        data.threshold envelope centre,
      left ≠ right →
      ∀ shared : object.Vertex,
        shared ∈ Graph.TypeBHybridIncidence.nonHubIncidences object
          centre left →
        shared ∉ Graph.TypeBHybridIncidence.nonHubIncidences object
          centre right) ∧
  Graph.TypeBHybridIncidence.windowIncidences object data.threshold
        envelope windowSupport centre +
      Graph.TypeBHybridIncidence.nonWindowIncidences object
        data.threshold envelope windowSupport centre =
    (data.threshold - 1) *
      Graph.TypeBFanIncidence.closedCount object data.threshold
        envelope centre ∧
  2 * Graph.TypeBFanIncidence.scaledDeficit object data.threshold
          data.dischargeScale envelope centre ≤
      (data.dischargeScale : Int) *
        ((Graph.TypeBHybridIncidence.windowIncidences object
            data.threshold envelope windowSupport centre : Int) +
          (Graph.TypeBHybridIncidence.nonWindowIncidences object
            data.threshold envelope windowSupport centre : Int)) ∧
  Graph.TypeBHybridIncidence.nonWindowDemand object data.threshold
        data.dischargeScale envelope windowSupport centre ≤
      (data.dischargeScale : Int) *
        (Graph.TypeBHybridIncidence.nonWindowIncidences object
          data.threshold envelope windowSupport centre : Int) ∧
  (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
      envelope centre →
    0 < Graph.TypeBFanIncidence.scaledDeficit object data.threshold
      data.dischargeScale envelope centre)

/-- The envelope residual charge bound of `def:typeB-residual-mass` at one
assigned centre of the support `(Y, H)`, on its assigned fan envelope `E_h`. -/
noncomputable def CentreBridgeMassBound (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex)
    (centre : object.Vertex) : Prop :=
  Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
      data.dischargeScale
      (typeBFanEnvelope core centres centre) centre ≤
    data.bridgeMassFactor * data.dischargeScale *
      (object.degree centre - data.threshold)

/-- Node `[67]`, the standing law: every high centre of the object has its
neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` --
cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside
`{h}` for a nonadjacent pair.  Both arms of the degree split run on it. -/
noncomputable abbrev HighCentreNormalFormStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[67]`: `lem:heavy-neighbourhood-normal-form`, at every high
  -- centre of the object at once.  It is not about one support, so it is
  -- stated of the object and both arms of the split read it.
  (∀ centre : object.Vertex,
    Graph.IsHighCentre object data.threshold centre →
    Graph.NormalForm object data.threshold centre)

/-- The remaining scaled core charge of one B2 disjoint ledger: the
post-ledger core charge summed by `prop:typeB-bridge-reduction`. -/
noncomputable def RemainingCoreCharge (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)}
    {core centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale packing core centres) : Int :=
  ∑ vertex ∈ ledger.remainingCore,
    Graph.TypeBRefinedSupport.scaledCoreCharge object data.threshold
      data.dischargeScale core vertex

/-- Every remaining component of one B2 disjoint ledger carries the post-ledger
Type A hygiene of `lem:typeB-postledger-core-hygiene`. -/
noncomputable def PostLedgerComponents (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)}
    {core : Finset object.Vertex}
    {centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale packing core centres) : Prop :=
  ∀ component : Graph.SupportComponents.Connected.Component
        object ledger.remainingCore,
    component ∈ Graph.SupportComponents.Connected.order object
        ledger.remainingCore →
      Graph.TypeBPostLedgerCore.PostLedgerComponent
        data.typeABPresentation ledger component

/-- B2(d): the exit-`(7)` productions of any family of remaining components of
one B2 disjoint ledger form a grouped decorated envelope on exactly those
components. -/
noncomputable def GroupedEnvelopeCoverage (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)}
    {core : Finset object.Vertex}
    {centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale packing core centres) : Prop :=
  ∀ components :
      Finset (Graph.TypeBMaximalCompletion.RemainingComponent ledger),
    (∀ component ∈ components,
      component ∈ Graph.SupportComponents.Connected.order object
        ledger.remainingCore) →
      ∀ production : ∀ component :
          Graph.TypeBMaximalCompletion.SelectedComponent ledger components,
        Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
          component.1 data.LengthOK (handoffHighDegree data object)
          (handoffAbsorbing data object packing),
        ∃ grouped :
          Graph.DecoratedHandoff.GroupedEnvelopes object
            data.LengthOK (handoffUncompressible data object)
            (handoffWindowFree data object)
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing)
            (Graph.TypeBMaximalCompletion.SelectedComponent ledger components),
          (∀ component :
              Graph.TypeBMaximalCompletion.SelectedComponent ledger components,
            (grouped.envelope component).core =
              Graph.SupportComponents.Connected.vertices object
                ledger.remainingCore component.1) ∧
            ∀ centre : object.Vertex,
              centre ∈ grouped.centres ↔
                ∃ component :
                  Graph.TypeBMaximalCompletion.SelectedComponent ledger
                    components,
                  centre = (production component).separation.separator

end Hypostructure.Graph.Strategy.Spine
