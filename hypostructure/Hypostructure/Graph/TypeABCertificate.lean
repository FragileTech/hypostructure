import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.MinimumDegreeCycleTarget

/-!
# The global Type-A / Type-B alternative

These declarations state the global structural alternative of
`def:admissible`, `def:net-charge`, the Type-A node and the Type-B node of a
discharging argument that splits a normalized support on its published
assigned surplus.

The support is a parameter, never a quantity recomputed from `object`, and the
baseline is always the registered `Presentation.baselineDegree`.

No numeral survives.  The discharging rate `α` enters `NegativeNetCharge`
through the presentation field `dischargeScale = 1/α`, filled by the
application exactly as `baselineDegree` and `inducedPathOrder` are filled.
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
  /-- The registered discharge scale `1/α`; `NegativeNetCharge` reads it from
  here rather than writing it out. -/
  dischargeScale : Nat
  /-- The registered ambient target. -/
  Target : FiniteObject.{u} → Prop
  /-- The registered accepted cycle lengths. -/
  LengthOK : Nat → Prop

variable (presentation : Presentation.{u})

/-- The baseline predicate induced by the registered baseline degree. -/
abbrev Baseline (object : FiniteObject.{u}) : Prop :=
  MinimumDegreeAtLeast presentation.baselineDegree object

/-- `def:admissible`'s positive deficiency `def⁺(X)` at the registered baseline. -/
noncomputable def positiveDeficiency
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Nat :=
  object.positiveDeficiency support presentation.baselineDegree

/-- The assigned surplus `σ(X)`: the excess `degree − baseline` summed over the
support itself.  Members at or below the baseline contribute zero, so no
separate centre family is carried. -/
noncomputable def assignedSurplus
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Nat :=
  object.ambientSurplus support presentation.baselineDegree

/-- The members of the support that actually carry assigned surplus: the
manuscript's high-degree fan centres.  This is a *derived* subset of the
support, not a carried datum, so no unconstrained centre family can enter a
certificate. -/
noncomputable def assignedCenters
    (object : FiniteObject.{u}) (support : Finset object.Vertex) :
    Finset object.Vertex :=
  support.filter fun vertex => presentation.baselineDegree < object.degree vertex

/-- A positive assigned surplus is carried by an actual member, so a Type-B
certificate does not have to assert a nonempty centre family. -/
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

/-- `def:internal-3-core`, read at the registered baseline: no nonempty
sub-support induces a subgraph of minimum degree at least the baseline. -/
def EmptyInternalThreeCore
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ¬ ∃ smaller : Finset object.Vertex,
      smaller ⊆ support ∧ smaller.Nonempty ∧
        Baseline presentation (object.induce smaller)

/-- `lem:stub-positive`'s pointwise half: every baseline deficiency inside the support is paid by a literal incidence
leaving it. -/
def BoundarySupplied
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∀ vertex ∈ support,
    presentation.baselineDegree -
        object.internalDegree support vertex ≤
      object.degree vertex - object.internalDegree support vertex

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
smaller).minDegree`, which on a nonempty `smaller ⊆ support` contradicts
`EmptyInternalThreeCore`.  So the empty-internal-core fact refutes the
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

/-- `def:target-safe` in the contextual sense: the arm that reaches the A/B
split is the target-avoiding arm. -/
def ContextuallyDyadicSafe (object : FiniteObject.{u}) : Prop :=
  ¬ presentation.Target object

/-- **`def:net-charge` at the registered discharging rate `α`.**

`No(X) = def⁺(X) − σ(X) − α|V(X)|` is negative exactly when
`def⁺(X) − σ(X) < α|V(X)|`.  The multiplier below is
`presentation.dischargeScale = 1/α`; clearing the denominator gives the integer
comparison stated here, and integer subtraction is used so that no truncated
natural subtraction can turn an overpaid support into a negative one.  At
`dischargeScale = 4` this is `def:net-charge`'s `α = 1/4`. -/
def NegativeNetCharge (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Prop :=
  (presentation.dischargeScale : Int) *
      ((positiveDeficiency presentation object support : Int) -
        (assignedSurplus presentation object support : Int)) <
    (support.card : Int)

/-- **The common global certificate assembled before the A/B split**: an
admissible support (`def:admissible`) of negative net charge. -/
structure AdmissibleNegativeSupport (object : FiniteObject.{u}) where
  /-- The support, supplied by the residual. -/
  support : Finset object.Vertex
  /-- `def:admissible`: the support is `P₁₃`-free. -/
  p13Free : InducedPathFree (object.induce support)
    presentation.inducedPathOrder
  /-- `def:admissible`: empty internal `3`-core. -/
  emptyThreeCore : EmptyInternalThreeCore presentation object support
  /-- Every baseline deficiency inside the support is paid by an incidence
  leaving it. -/
  boundarySupplied : BoundarySupplied presentation object support
  /-- Discharged by `hereditarilyTargetUncompressible_of_emptyInternalThreeCore`
  from the field above; retained because `def:admissible` names it. -/
  uncompressible : HereditarilyTargetUncompressible presentation object support
  /-- The target-avoiding arm's own datum. -/
  dyadicSafe : ContextuallyDyadicSafe presentation object
  /-- `def:net-charge` at the registered `α`; see `NegativeNetCharge`. -/
  negative : NegativeNetCharge presentation object support

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
hence ambient-cubic.  `ambientCubic` records that every vertex of the
support sits exactly at the baseline. -/
structure TypeACertificate (object : FiniteObject.{u}) where
  common : AdmissibleNegativeSupport presentation object
  noSurplus : assignedSurplus presentation object common.support = 0
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
    presentation.dischargeScale *
        positiveDeficiency presentation object certificate.common.support <
      certificate.common.support.card := by
  have negative :
      (presentation.dischargeScale : Int) *
          ((positiveDeficiency presentation object
              certificate.common.support : Int) -
            (assignedSurplus presentation object
              certificate.common.support : Int)) <
        (certificate.common.support.card : Int) :=
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
  positiveSurplus :
    0 < assignedSurplus presentation object common.support
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
  exact certificate.positiveSurplus

/-- The two alternatives are disjoint on the one ledger entry the execution
selects: the split node reads exactly this published aggregate. -/
theorem selectedSupport_typeA_typeB_disjoint
    {presentation : Presentation.{u}} (object : FiniteObject.{u})
    (common : AdmissibleNegativeSupport presentation object) :
    ¬ (assignedSurplus presentation object common.support = 0 ∧
        0 < assignedSurplus presentation object common.support) := by
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
