import Hypostructure.Graph.Strategy.NormalizationRank
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics

/-!
# The global Type-A / Type-B alternative on the ledger's own carriers

These declarations state the global structural alternative of
`def:admissible`, `def:net-charge`, the Type-A node and the Type-B node of a
discharging argument that splits a normalized support on its published
assigned surplus.

**Every carrier is the one the executed spine produces.**  The support is a
parameter, never a quantity recomputed from `object`: the branch supplies
CT9's normalized support
(`Graph.Strategy.NormalizationRank.exactInducedPathComplementSupport`), and the
numeric coordinates are the aggregates the local-supply Strategy publishes
(`Core.Strategy.LocalSupplyLowerBound.Summary`).  The per-vertex observations
below are the *registered* CT14 observations of that same Strategy
(`NormalizationRank.supportIncidence`, `NormalizationRank.boundaryIncidence`,
`FiniteObject.degree`), and the baseline is always the registered
`Presentation.baselineDegree`.

No numeral survives.  The discharging rate `α = 1/loadMultiplier` of
`Graph.ReceiverLoad.LoadCapacityProfile.dischargeRate` enters
`NegativeNetCharge` through the presentation field `dischargeScale`, which the
application fills from the registered profile's own `loadMultiplier`, exactly
as `baselineDegree` and `inducedPathOrder` are filled.

An earlier application-side version of this module built its own remainder
from `Graph.InducedPathMaximalPacking.maximalWindowSet object 13`.  That is a
*second*, application-side maximal packing: `ObstructionPackingClosure.Packing`
selects only *some* maximal conflict-free family, two maximal packings have
different complements, and nothing in the framework identifies them.  Every
statement indexed by that recomputed remainder was therefore unprovable in
principle, not merely unproved.
-/

namespace Hypostructure.Graph.TypeAB

open Hypostructure
open scoped BigOperators

universe u

/-- The registered presentation these propositions read.  The baseline degree,
the induced-path order and the discharge scale are the ones the problem already
registered, and `Target`/`LengthOK` are the already registered target and its
accepted cycle lengths. -/
structure Presentation where
  /-- The registered baseline degree. -/
  baselineDegree : Nat
  /-- The registered induced-path order. -/
  inducedPathOrder : Nat
  /-- The registered discharge scale `1/α`, i.e. the problem's own
  `Graph.ReceiverLoad.LoadCapacityProfile.loadMultiplier`.  The discharging
  rate of `lem:typeA-unsaturated-discharge` is its reciprocal, which is exactly
  `LoadCapacityProfile.dischargeRate`; `NegativeNetCharge` reads it from here
  rather than writing it out. -/
  dischargeScale : Nat
  /-- The registered ambient target. -/
  Target : FiniteObject.{u} → Prop
  /-- The registered accepted cycle lengths. -/
  LengthOK : Nat → Prop

variable (presentation : Presentation.{u})

/-- The baseline predicate induced by the registered baseline degree. -/
abbrev Baseline (object : FiniteObject.{u}) : Prop :=
  MinimumDegreeAtLeast presentation.baselineDegree object

/-- `def:admissible`'s positive deficiency `def⁺(X)`, written with the
*registered* CT14 required-mass observation
(`NormalizationRank.localSupply.requiredMass = baseline - supportIncidence`).
Nothing is recomputed: this is the same per-vertex number the local-supply
Strategy aggregates into `Summary.requiredMass`. -/
noncomputable def positiveDeficiency
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Nat :=
  support.sum fun vertex =>
    presentation.baselineDegree -
      Graph.Strategy.NormalizationRank.supportIncidence object support vertex

/-- `def:canonical-decomp`'s assigned surplus `σ(X)`, written with the
*registered* CT14 surplus observation
(`NormalizationRank.localSupply.surplus = degree - baseline`).  It is summed
over the support itself, exactly as the ledger aggregates it: members at or
below the baseline contribute zero, so no separate centre family is carried. -/
noncomputable def assignedSurplus
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Nat :=
  support.sum fun vertex => object.degree vertex - presentation.baselineDegree

/-- The members of the support that actually carry assigned surplus: the
manuscript's high-degree fan centres.  This is a *derived* subset of the
support, not a carried datum, so no unconstrained centre family can enter a
certificate. -/
noncomputable def assignedCenters
    (object : FiniteObject.{u}) (support : Finset object.Vertex) :
    Finset object.Vertex :=
  support.filter fun vertex => presentation.baselineDegree < object.degree vertex

/-- A positive assigned surplus is carried by an actual member.  This is the
support-level twin of `LocalSupplyLowerBound.Summary.assignedSurplusNonAtom`,
so a Type-B certificate does not have to assert a nonempty centre family. -/
theorem assignedCenters_nonempty_of_assignedSurplus_pos
    {presentation : Presentation.{u}}
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    (positive : 0 < assignedSurplus presentation object support) :
    (assignedCenters presentation object support).Nonempty := by
  rcases Finset.eq_empty_or_nonempty
    (assignedCenters presentation object support) with empty | nonempty
  · exfalso
    have vanishes : assignedSurplus presentation object support = 0 := by
      refine Finset.sum_eq_zero fun vertex member => ?_
      have notCentre :
          vertex ∉ assignedCenters presentation object support := by
        simp [empty]
      have low : object.degree vertex ≤ presentation.baselineDegree := by
        by_contra high
        exact notCentre
          (Finset.mem_filter.mpr ⟨member, Nat.not_le.mp high⟩)
      omega
    omega
  · exact nonempty

/-- `def:internal-3-core`, read at the registered baseline through the
framework predicate the normalization node itself publishes.  Its negation is
exactly the fact CT6 produces on the active-ledger terminal
(`NormalizationRank.exactInducedPathComponent_emptyInternalCore`), and for an
arbitrary sub-support of CT9's complement it is
`NormalizationRank.exactInducedPathSubset_minDegree_lt`. -/
def EmptyInternalThreeCore
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ¬ Graph.Strategy.NormalizationRank.HasInternalCore object
      presentation.baselineDegree support

/-- `lem:stub-positive`'s pointwise half in the registered CT14 observations:
every baseline deficiency inside the support is paid by a literal incidence
leaving it. -/
def BoundarySupplied
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∀ vertex ∈ support,
    presentation.baselineDegree -
        Graph.Strategy.NormalizationRank.supportIncidence object support
          vertex ≤
      Graph.Strategy.NormalizationRank.boundaryIncidence object support vertex

/-- `cor:uncompressible` at the A/B checkpoint: every proper baseline-preserving
induced sub-support already realizes the registered target. -/
def HereditarilyTargetUncompressible
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∀ smaller : Finset object.Vertex,
    smaller.Nonempty → smaller ⊂ support →
      Baseline presentation (object.induce smaller) →
        presentation.Target (object.induce smaller)

/-- **Uncompressibility is already carried by the empty internal core.**

`Baseline (object.induce smaller)` is `baselineDegree ≤ (object.induce
smaller).minDegree`, which on a nonempty `smaller ⊆ support` is literally a
witness of `NormalizationRank.HasInternalCore object baselineDegree support`.
So the empty-internal-core fact the normalization ledger publishes refutes the
hypothesis and the implication holds with no further input.

This settles, by proof rather than by argument, that `uncompressible` adds no
obligation to a certificate whose support already carries `emptyThreeCore`. -/
theorem hereditarilyTargetUncompressible_of_emptyInternalThreeCore
    {presentation : Presentation.{u}}
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    (empty : EmptyInternalThreeCore presentation object support) :
    HereditarilyTargetUncompressible presentation object support := by
  intro smaller nonempty proper baseline
  exact absurd
    ⟨smaller, (Finset.ssubset_iff_subset_ne.mp proper).1, nonempty, baseline⟩
    empty

/-- `def:dyadic-safe` in the contextual sense: the arm that reaches the A/B
split is the target-avoiding arm, and this is the same datum
`globalLocalReflection` clause (a) reads. -/
def ContextuallyDyadicSafe (object : FiniteObject.{u}) : Prop :=
  ¬ presentation.Target object

/-- **`def:net-charge` at the registered discharging rate `α`, written on the
ledger's published coordinates.**

`summary.requiredMass` is `def⁺(R)`, `summary.assignedSurplus` is `σ_R`, and
`summary.netDeficiency.remainder` is `|R|`; integer subtraction is intentional,
since no truncated natural subtraction can turn an overpaid support into a
negative one.

**This is the one coordinate no registered node supplies, and the reason is
now a single named missing inequality rather than a mismatch of columns.**

The local-supply Strategy publishes `netDeficiency` at the rate
`coefficient / scale = observedSupply / |R|` with `surplus := assignedSurplus`,
so `NetDeficiencyAccounting.not_rate_reached` at any `rate` strictly above that
ratio yields exactly `rate·|R| + σ_R > def⁺(R)`, i.e. this proposition at that
`rate`.  Instantiating `rate` at the presentation's own discharging rate
`α = 1/loadMultiplier` (`Graph.ReceiverLoad.LoadCapacityProfile.dischargeRate`)
therefore produces `NegativeNetCharge` verbatim -- **provided** the consumer can
discharge the applicability condition

  `observedSupply / |R| < α`,

which is the manuscript's own `Δ_net(R) ≤ τ_win < α` at node `[56]`.  That is
the single fact still missing: it needs `lem:surplus-aware-window-stub`'s
`e(R, W) ≤ 15 p₁₃ + σ_W` together with `prop:p13-density`'s `θ < 1/73`, and
`.obstructionPacking` is not among the local-supply Strategy's requirements.
`Core.Strategy.LocalSupplyLowerBound.Profile.summaryOfResidual`'s docstring
records exactly which structure would have to carry it.

The field is kept at the manuscript's statement rather than lowered to the
published cap, because lowering it would make the Type-A/Type-B disjunction
vacuous: the two alternatives are exhaustive in `assignedSurplus`, so without a
quarter bound they assert only that a normalized support exists.

The multiplier below is `presentation.dischargeScale`, the registered
`loadMultiplier` of the problem's own
`Graph.ReceiverLoad.LoadCapacityProfile`; clearing the denominator of
`def:net-charge`'s `α = 1/loadMultiplier` is what turns `def⁺(R) - σ_R < α|R|`
into the integer comparison stated here.  At the registered profile
`loadMultiplier = 4` this is the manuscript's quarter bound verbatim. -/
def NegativeNetCharge
    (summary : Core.Strategy.LocalSupplyLowerBound.Summary) : Prop :=
  (presentation.dischargeScale : Int) *
      ((summary.requiredMass : Int) - (summary.assignedSurplus : Int)) <
    (summary.netDeficiency.remainder : Int)

/-- What the ledger *does* publish in the same coordinates: the net deficiency
is bounded by the observed supply.  Recorded here so the distance between the
published cap and `NegativeNetCharge` is visible in the source. -/
theorem netDeficiency_le_publishedCap
    (summary : Core.Strategy.LocalSupplyLowerBound.Summary) :
    (summary.requiredMass : Int) - (summary.assignedSurplus : Int) ≤
      (summary.observedSupply : Int) := by
  have cap := summary.netDeficiencyCap
  omega

/-- **The common global certificate assembled before the A/B split, on the
ledger's own carriers.**

`support` is CT9's normalized support and `summary` is the local-supply ledger
entry published for exactly that support.  The three equations tie the two
together; they are the whole reason the certificate is not vacuous, and they
are the producer's only numeric obligation.  Every other field is a fact the
normalization and avoidance ledgers already publish about that support.

There is no `component` field.  CT6's component schedule
(`NormalizationRank.exactInducedPathComponents`) is produced, but the
continuation reads `LocalSupplyLowerBound.Summary` aggregated over the *whole*
complement, so the split is taken on `σ(R)` and the support this certificate
can carry is `R`. -/
structure AdmissibleNegativeSupport (object : FiniteObject.{u}) where
  /-- CT9's normalized support, supplied by the residual. -/
  support : Finset object.Vertex
  /-- The local-supply ledger entry published for that support. -/
  summary : Core.Strategy.LocalSupplyLowerBound.Summary
  /-- `netDeficiency.remainder` is `|R|`. -/
  remainder_eq : summary.netDeficiency.remainder = support.card
  /-- `requiredMass` is `def⁺(R)`, aggregated from the registered CT14
  required-mass observation over the same members. -/
  requiredMass_eq : summary.requiredMass =
    positiveDeficiency presentation object support
  /-- `assignedSurplus` is `σ_R`, aggregated from the registered CT14 surplus
  observation over the same members. -/
  assignedSurplus_eq : summary.assignedSurplus =
    assignedSurplus presentation object support
  /-- `NormalizationRank.exactInducedPathSubset_free`. -/
  p13Free : InducedPathFree (object.induce support)
    presentation.inducedPathOrder
  /-- `NormalizationRank.exactInducedPathSubset_minDegree_lt`. -/
  emptyThreeCore : EmptyInternalThreeCore presentation object support
  /-- `NormalizationRank.supportIncidence_deficiency_le_boundaryIncidence` at
  the residual's own `Baseline`. -/
  boundarySupplied : BoundarySupplied presentation object support
  /-- Discharged by `hereditarilyTargetUncompressible_of_emptyInternalThreeCore`
  from the field above; retained because `def:admissible` names it. -/
  uncompressible : HereditarilyTargetUncompressible presentation object support
  /-- The target-avoiding arm's own datum. -/
  dyadicSafe : ContextuallyDyadicSafe presentation object
  /-- `def:net-charge` at the registered `α`; see `NegativeNetCharge`. -/
  negative : NegativeNetCharge presentation summary

/-- A simple return avoiding the center would close with two fan edges. -/
def FanReturnSafe (object : FiniteObject.{u})
    (center left right : object.Vertex) : Prop :=
  ∀ walk : object.graph.Walk left right,
    walk.IsPath → center ∉ walk.support →
      ¬ presentation.LengthOK (walk.length + 2)

/-- The paper's concrete fan-safe neighbour condition at one assigned
high-degree center, at the registered baseline. -/
def FanSafeCenter (object : FiniteObject.{u})
    (center : object.Vertex) : Prop :=
  presentation.baselineDegree < object.degree center ∧
    ∀ left ∈ object.orderedNeighbors center,
      ∀ right ∈ object.orderedNeighbors center,
        left ≠ right → FanReturnSafe presentation object center left right

/-- Certificate-marked Type-B data (`def:marked-typeB-fan`).  Labels are
explicit natural codes; the pair condition records the paper's legal pair
relation through fan-return safety rather than an unconstrained boolean
table. -/
structure MarkedFanData (object : FiniteObject.{u})
    (centers : Finset object.Vertex) where
  label : object.Vertex → Nat
  centers_safe : ∀ center ∈ centers, FanSafeCenter presentation object center
  pair_legal :
    ∀ center ∈ centers,
      ∀ left ∈ object.orderedNeighbors center,
        ∀ right ∈ object.orderedNeighbors center,
          left ≠ right →
            label left ≠ 0 ∧ label right ≠ 0 ∧
              FanReturnSafe presentation object center left right

/-- A decorated handoff arm (`def:decorated-fan-envelope`) is an actual simple
walk from a neighbour of its center into the selected support. -/
structure DecoratedHandoffData (object : FiniteObject.{u})
    (support centers : Finset object.Vertex) where
  terminal : object.Vertex → object.Vertex
  arm : (center : object.Vertex) → center ∈ centers →
    (first : object.Vertex) → first ∈ object.orderedNeighbors center →
      object.graph.Walk first (terminal first)
  terminal_mem :
    ∀ (center : object.Vertex) (center_mem : center ∈ centers)
      (first : object.Vertex)
      (first_mem : first ∈ object.orderedNeighbors center),
      terminal first ∈ support
  arm_path :
    ∀ (center : object.Vertex) (center_mem : center ∈ centers)
      (first : object.Vertex)
      (first_mem : first ∈ object.orderedNeighbors center),
      (arm center center_mem first first_mem).IsPath
  centers_safe : ∀ center ∈ centers, FanSafeCenter presentation object center

/-- The Type-B node's two halves: certificate-marked fan data or decorated
handoff data. -/
inductive TypeBDecoration (object : FiniteObject.{u})
    (support centers : Finset object.Vertex) : Type u where
  | marked (data : MarkedFanData presentation object centers)
  | handoff (data : DecoratedHandoffData presentation object support centers)

/-- Paper Type A: a negative admissible support with no assigned surplus,
hence ambient-cubic.  `ambientCubic` is the ledger's own reading of
`assignedSurplus = 0`
(`NormalizationRank.localSupply_degree_le_baselineDegree_of_surplus_eq_zero`
together with the residual's `Baseline`, i.e.
`NegativeSupport.Support.ambientDegree_eq_of_noHigh`). -/
structure TypeACertificate (object : FiniteObject.{u}) where
  common : AdmissibleNegativeSupport presentation object
  noSurplus : common.summary.assignedSurplus = 0
  ambientCubic :
    ∀ vertex ∈ common.support,
      object.degree vertex = presentation.baselineDegree

/-- The manuscript's Type A conclusion `def⁺(X) < α|X|`, in the ledger's
published coordinates and at the registered discharge scale.  It is a
*consequence* of the common certificate rather than a second obligation: with
no assigned surplus the net-charge inequality is already the bound.  At the
registered `dischargeScale = 4` this is the manuscript's `def⁺(X) < |X|/4`. -/
theorem TypeACertificate.strictQuarter
    {presentation : Presentation.{u}} {object : FiniteObject.{u}}
    (certificate : TypeACertificate presentation object) :
    presentation.dischargeScale * certificate.common.summary.requiredMass <
      certificate.common.summary.netDeficiency.remainder := by
  have negative :
      (presentation.dischargeScale : Int) *
          ((certificate.common.summary.requiredMass : Int) -
            (certificate.common.summary.assignedSurplus : Int)) <
        (certificate.common.summary.netDeficiency.remainder : Int) :=
    certificate.common.negative
  rw [certificate.noSurplus] at negative
  simp only [Nat.cast_zero, sub_zero] at negative
  exact_mod_cast negative

/-- Paper Type B: a negative admissible support with a genuine assigned
high-degree fan certificate or decorated handoff.  The centre family is
`assignedCenters`, derived from the support, so nothing unconstrained enters
here. -/
structure TypeBCertificate (object : FiniteObject.{u}) where
  common : AdmissibleNegativeSupport presentation object
  positiveSurplus : 0 < common.summary.assignedSurplus
  decoration :
    TypeBDecoration presentation object common.support
      (assignedCenters presentation object common.support)

/-- The Type-B centre family is nonempty: this is a consequence of the
published positive surplus, not a further obligation. -/
theorem TypeBCertificate.centers_nonempty
    {presentation : Presentation.{u}} {object : FiniteObject.{u}}
    (certificate : TypeBCertificate presentation object) :
    (assignedCenters presentation object
      certificate.common.support).Nonempty := by
  refine assignedCenters_nonempty_of_assignedSurplus_pos ?_
  have identity := certificate.common.assignedSurplus_eq
  have positive := certificate.positiveSurplus
  omega

/-- The two alternatives are disjoint on the one ledger entry the execution
selects: the split node reads exactly this published aggregate. -/
theorem selectedSupport_typeA_typeB_disjoint
    {presentation : Presentation.{u}} (object : FiniteObject.{u})
    (common : AdmissibleNegativeSupport presentation object) :
    ¬ (common.summary.assignedSurplus = 0 ∧
        0 < common.summary.assignedSurplus) := by
  omega

/-- A finite graph carried as a literal subgraph of an ambient graph.  The
certificate need not be proper: identity realizes a certificate produced on
the current residual, while composition transports it through the official
minimal-counterexample prefix. -/
structure EmbeddedSubgraph (object : FiniteObject.{u}) where
  value : FiniteObject.{u}
  vertexEmbedding : value.Vertex ↪ object.Vertex
  included : value.graph.map vertexEmbedding ≤ object.graph

namespace EmbeddedSubgraph

def identity (object : FiniteObject.{u}) : EmbeddedSubgraph object where
  value := object
  vertexEmbedding := Function.Embedding.refl _
  included := by
    rintro _ _ ⟨_different, left, right, adjacent, rfl, rfl⟩
    exact adjacent

def throughProper
    {source : FiniteObject.{u}}
    (outer : ProperSubgraph source)
    (inner : EmbeddedSubgraph outer.value) :
    EmbeddedSubgraph source where
  value := inner.value
  vertexEmbedding := inner.vertexEmbedding.trans outer.vertexEmbedding
  included := by
    rintro _ _ ⟨_different, left, right, adjacent, rfl, rfl⟩
    have innerAdjacent :
        outer.value.graph.Adj
          (inner.vertexEmbedding left) (inner.vertexEmbedding right) :=
      inner.included (SimpleGraph.map_adj_apply' adjacent
        (inner.vertexEmbedding.injective.ne adjacent.ne))
    exact outer.included (SimpleGraph.map_adj_apply' innerAdjacent
      (outer.vertexEmbedding.injective.ne innerAdjacent.ne))

def throughIso
    {left right : FiniteObject.{u}}
    (iso : left.Iso right)
    (inner : EmbeddedSubgraph left) :
    EmbeddedSubgraph right where
  value := inner.value
  vertexEmbedding := inner.vertexEmbedding.trans iso.toEquiv.toEmbedding
  included := by
    rintro _ _ ⟨_different, first, second, adjacent, rfl, rfl⟩
    have innerAdjacent :
        left.graph.Adj
          (inner.vertexEmbedding first) (inner.vertexEmbedding second) :=
      inner.included (SimpleGraph.map_adj_apply' adjacent
        (inner.vertexEmbedding.injective.ne adjacent.ne))
    exact iso.map_rel_iff.mpr innerAdjacent

end EmbeddedSubgraph

/-- Global Type A means that the ambient graph contains the complete paper
Type-A certificate.  This is an ordinary proposition, and a certificate
constructed on the current graph enters through `EmbeddedSubgraph.identity`.
-/
def GlobalTypeA (object : FiniteObject.{u}) : Prop :=
  ∃ subgraph : EmbeddedSubgraph object,
    Nonempty (TypeACertificate presentation subgraph.value)

/-- Global Type B means that the ambient graph contains the complete paper
Type-B certificate. -/
def GlobalTypeB (object : FiniteObject.{u}) : Prop :=
  ∃ subgraph : EmbeddedSubgraph object,
    Nonempty (TypeBCertificate presentation subgraph.value)

def GlobalTypeA.ofCurrent {presentation : Presentation.{u}}
    {object : FiniteObject.{u}}
    (certificate : TypeACertificate presentation object) :
    GlobalTypeA presentation object :=
  ⟨EmbeddedSubgraph.identity object, ⟨certificate⟩⟩

def GlobalTypeB.ofCurrent {presentation : Presentation.{u}}
    {object : FiniteObject.{u}}
    (certificate : TypeBCertificate presentation object) :
    GlobalTypeB presentation object :=
  ⟨EmbeddedSubgraph.identity object, ⟨certificate⟩⟩

def GlobalTypeA.mapProper {presentation : Presentation.{u}}
    {source : FiniteObject.{u}}
    (subgraph : ProperSubgraph source)
    (certificate : GlobalTypeA presentation subgraph.value) :
    GlobalTypeA presentation source := by
  rcases certificate with ⟨inner, proof⟩
  exact ⟨inner.throughProper subgraph, proof⟩

def GlobalTypeB.mapProper {presentation : Presentation.{u}}
    {source : FiniteObject.{u}}
    (subgraph : ProperSubgraph source)
    (certificate : GlobalTypeB presentation subgraph.value) :
    GlobalTypeB presentation source := by
  rcases certificate with ⟨inner, proof⟩
  exact ⟨inner.throughProper subgraph, proof⟩

theorem GlobalTypeA.iff_of_iso {presentation : Presentation.{u}}
    {left right : FiniteObject.{u}} (iso : left.Iso right) :
    GlobalTypeA presentation left ↔ GlobalTypeA presentation right := by
  constructor
  · rintro ⟨inner, proof⟩
    exact ⟨inner.throughIso iso, proof⟩
  · rintro ⟨inner, proof⟩
    exact ⟨inner.throughIso iso.symm, proof⟩

theorem GlobalTypeB.iff_of_iso {presentation : Presentation.{u}}
    {left right : FiniteObject.{u}} (iso : left.Iso right) :
    GlobalTypeB presentation left ↔ GlobalTypeB presentation right := by
  constructor
  · rintro ⟨inner, proof⟩
    exact ⟨inner.throughIso iso, proof⟩
  · rintro ⟨inner, proof⟩
    exact ⟨inner.throughIso iso.symm, proof⟩

end Hypostructure.Graph.TypeAB
