import Hypostructure.Graph.Statements.TypeA
import Hypostructure.Graph.TypeBProfileSchedule

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

/-- The exact case-(ii) handoff of `lem:absorbed-germ-fan-data` at one selected
branch-excess half-edge `ε`, at node `[153]`'s retained routing.  `centre` is the
least high vertex of `ε`'s own first-failure prefix (its node-`[10]` neighbours
sit at the baseline), and that prefix is the counted core of an actual
`DecoratedHandoff.Envelope` with decoration `{centre}`: connected, inside the
canonical remainder, admissible, with two distinct assigned first neighbours.
Everything is read at `ε` itself, so the core is `ε`'s prefix and contains the
centre. -/
noncomputable def AbsorbedHandoffAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (centre : object.Vertex) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact
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
      let core := corridor.prefixSupport traceEnd
      Graph.SupportComponents.Connected.ConnectedOn object core ∧
        core ⊆ object.remainderSupport
          (canonicalWindowPacking data object) ∧
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object
              (canonicalWindowPacking data object)),
          envelope.core = core ∧
            envelope.decorations = {centre} ∧
            Graph.DecoratedHandoff.Admissible object data.LengthOK
              (handoffUncompressible data object)
              (handoffWindowFree data object) envelope ∧
            ∃ first second : object.Vertex,
              first ≠ second ∧
                first ∈ envelope.assigned centre ∧
                second ∈ envelope.assigned centre

/-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii), the decorated handoff fan
support at the first high centre.  For every selected branch-excess half-edge
`ε` outside the subcubic candidate set, `ε`'s retained first-failure prefix is a
connected subset of the canonical remainder and supplies the counted core; the
least high vertex of that prefix is its decoration (`AbsorbedHandoffAt`). -/
noncomputable def AbsorbedGermDecoratedAssignedSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Eligible := ColdEligibleHalfEdge data object
  exact ∃ routing : ColdFailureRoutingStatement data object,
    let candidates := coldRoutedCandidates data object routing
    ∀ epsilon : Eligible,
      Sum.inl epsilon ∉ candidates →
      ∃ centre, AbsorbedHandoffAt data object routing epsilon centre

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

/-- **A Type B fan-window profile of `G` at the fixed packing**
(`def:typeB-window-incidence-profile`, `def:fan-closed-port`): its recorded
window is the packed-window union `W₀ = windowSupport P₀` of the canonical
maximal packing, and its envelope is the canonical fan envelope of its centre.
Only the certificate labelling of the marked fan is left free. -/
def IsFixedTypeBProfile (data : Parameters) (object : Graph.FiniteObject.{u})
    (profile : Graph.TypeBFanClosedPorts.Profile object) : Prop :=
  profile.window =
      Graph.FiniteObject.windowSupport (canonicalWindowPacking data object) ∧
    profile.envelope =
      Graph.TypeBProfileSchedule.canonicalEnvelope object profile.marked.fan.hub

/-- The two routed alternatives of node `[69]` at one heavy centre:
`cor:heavy-center-local-dichotomy` with each alternative carried to fan-closed
ports in every fixed profile at the centre --- a fan-compatible open pair
by `cor:compatible-pair-typeB-routing`, or a family of `d_G(h) - 2` triangular
ports (in particular three) by `prop:triangular-port-typeB-routing`. -/
def HeavyCentreRoutedAlternative (data : Parameters)
    (object : Graph.FiniteObject.{u}) (centre : object.Vertex) : Prop :=
  (∃ left right : object.Vertex,
      Graph.FanCompatible object centre left right ∧
        ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
          IsFixedTypeBProfile data object profile →
          profile.marked.fan.hub = centre →
            CompatiblePairRoutes data object profile left right) ∨
    (∃ ports ⊆ Graph.triangularEndpoints object centre,
      ports.card = object.degree centre - 2 ∧ 3 ≤ ports.card ∧
        ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
          IsFixedTypeBProfile data object profile →
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
centre: degree `δ + 1`, a fan-compatible open pair or `δ - 1` triangular ports,
centre surplus `1`, and the registered-scale closed-neighbour profile of the
canonical fan envelope of the centre. -/
def DegreeFourFanProfile (data : Parameters) (object : Graph.FiniteObject.{u})
    (centre : object.Vertex) : Prop :=
  object.degree centre = data.threshold + 1 ∧
    ((∃ left right : object.Vertex,
        Graph.FanCompatible object centre left right) ∨
      data.threshold - 1 ≤ (Graph.triangularEndpoints object centre).card) ∧
    object.degree centre - data.threshold = 1 ∧
    Graph.TypeBFanIncidence.closedCount object data.threshold
        (Graph.TypeBProfileSchedule.canonicalEnvelope object centre) centre ≤
      data.threshold + 1 ∧
    Graph.TypeBFanIncidence.scaledDeficit object data.threshold
        data.dischargeScale
        (Graph.TypeBProfileSchedule.canonicalEnvelope object centre) centre =
      (data.dischargeScale : Int) *
          (Graph.TypeBFanIncidence.closedCount object data.threshold
            (Graph.TypeBProfileSchedule.canonicalEnvelope object centre)
            centre : Int) -
        (data.dischargeScale : Int) * (data.threshold : Int) +
        ((data.threshold : Int) + 2)

/-- `def:triangular-fan-core` on the active object.  Ports are represented by
their endpoints because the centre is fixed.  The shoulder finset is exactly
`N_G(x) \setminus {h}`; the core is the paper's induced vertex set, so the
ambient graph supplies its induced adjacency.  The four incidence relations
record precisely completion, central, cross-triangular, and outside edges. -/
def TriangularFanCoreStatement (data : Parameters)
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
def TriangularFirstLandingStatement (data : Parameters)
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
def TriangularCrossShoulderStatement (data : Parameters)
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

/-- `def:fan-closed-port`, using the canonical upstream assigned Type-B
profile.  The equivalence exposes clauses (a)--(c) of the manuscript; clause
(c) is the derived incidence classification proved by
`TypeBFanClosedPorts.IsFanClosed.incidence_classified`. -/
def FanClosedPortStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object profile →
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
def CompatiblePairFanClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object profile →
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

/-- `prop:fan-closed-port-typeB-routing`, in the canonical upstream form, at
the registered discharge rate `α = 1/s`: `r ≥ 2` fan-closed ports give
`D_B(𝔉_h) ≥ r - (δ - (k+1)α) ≥ (k+1)α - 1 > 0`. -/
def FanClosedPortTypeBRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object profile →
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

/-- `cor:compatible-pair-typeB-routing`, in the canonical upstream form. -/
def CompatiblePairTypeBRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object profile →
    ∀ left right : object.Vertex,
    CompatiblePairRoutes data object profile left right

/-- `prop:triangular-port-typeB-routing`, in the canonical upstream form.
The family has the manuscript's exact size `k - 2`; every endpoint is recorded
on the remainder side and both of its triangular shoulder incidences are
assigned to the fan envelope. -/
def TriangularPortTypeBRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ profile : Graph.TypeBFanClosedPorts.Profile object,
    IsFixedTypeBProfile data object profile →
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
assigned centre, on the canonical fan envelope of the centre. -/
noncomputable def CentreBridgeMassBound (data : Parameters)
    (object : Graph.FiniteObject.{u}) (centre : object.Vertex) : Prop :=
  Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
      data.dischargeScale
      (Graph.TypeBProfileSchedule.canonicalEnvelope object centre) centre ≤
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
    {piece : Graph.TypeBRefinedSupport.CanonicalPiece object packing}
    {centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale packing piece.vertices centres) : Prop :=
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
    {piece : Graph.TypeBRefinedSupport.CanonicalPiece object packing}
    {centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale packing piece.vertices centres) : Prop :=
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
