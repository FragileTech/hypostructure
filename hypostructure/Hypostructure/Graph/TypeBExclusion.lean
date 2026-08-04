import Mathlib.Data.Rat.Floor
import Hypostructure.Graph.TypeBBridgeResidual

/-!
# Type B exclusion under the refined ledger

This file is the graph-mathematics content of manuscript node `[65]`
(`typeB`), fed by nodes `[71]`--`[73]` and `[82]`--`[85]`, of
`original_erdos_64_proof.tex`:

* `def:typeB-multiclosed-residual`, certificate-closed half -- `fanDeficit`
  (`D_B(𝔉_h) = c(𝔉_h) - (3 - (k+1)α)` computed on the assigned support),
  `IsCertificateClosed` (`D_B ≤ 0`) and the manuscript's "Equivalently"
  reformulation `isCertificateClosed_iff` (`c ≤ ⌊3 - (k+1)α⌋`, the
  `closedCountCap`);
* `lem:fan-certificate`, charge half -- `neg_fanDeficit_le_fanEntryCharge`
  (`ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) ≥ (3 - (k+1)α) - c = -D_B`) and
  `fanEntryCharge_nonneg`;
* `def:typeB-bridge-statements` (B2), disjoint-carrier clause (a)/(c) --
  `DisjointCarriers`, and its negation `SharedCarrier`, the shared carrier of
  `def:typeB-overlap-obstruction`;
* `prop:typeB-bridge-reduction`, summation step --
  `netCharge_eq_residualCoreCharge_add_sum_fanEntryCharge` (B2(c): the fan
  entries are a disjoint refinement of the ledger) and
  `residualCoreCharge_sub_sum_fanDeficit_le_netCharge`;
* `lem:typeB-exclusion` -- `typeBExclusion` and, for its "Consequently"
  clause, `sharedCarrier_of_netCharge_neg`.

## The discharge rate is read, never written

Every rate in this file is `α = ledger.dischargeRate`, that is `1/loadMultiplier`
from the registered presentation record
`Hypostructure.Graph.ReceiverLoad.LoadCapacityProfile`.  At the registered
`loadMultiplier = 4` each statement below reduces on the nose to the
manuscript's own spelling: the fan deficit `c - (3 - (k+1)α)` becomes
`c - (11 - k)/4`, the closed-count cap `⌊3 - (k+1)α⌋` becomes `1` for `k ≤ 7`
and `0` for `k = 8`, and `|V(X)|·α` becomes `|V(X)|/4`.

The only numeral that stays a literal is the `3` of the cubic baseline: it is
the cubic-graph geometry carried by `NormalForm.neighbourCubic`, not a rate.

Two ledger constraints are consumed, both already declared on
`LoadCapacityProfile` and both used only through their cleared forms:

* `one_lt_five_mul_dischargeRate` (`1 < 5α`) -- the positive-deficit side, i.e.
  a fully closed degree-four fan really does overflow;
* `nine_mul_dischargeRate_le_three` (`9α ≤ 3`) -- the fan-credit side, i.e. the
  closed-count cap is nonnegative across the whole degree window `4 ≤ k ≤ 8`.

## Nothing is redefined

The assigned Type B support `X`, its counted core `Y_X`, its assigned centres
`H_X`, the vertex charges `ch_X`, the augmented ledger `Ĉh_B(X)`, the net
charge `No(X)`, the fan envelope blocks and the post-ledger core charge are all
`Hypostructure.Graph.TypeBBridgeResidual`.  The assigned fan-window profile
`𝔉_h`, its closed-neighbour count `c(𝔉)` and its deficit `D_B(𝔉)` are
`Hypostructure.Graph.TypeBFanClosedPorts`; the hybrid B1 ledger and its capacity
are `Hypostructure.Graph.TypeBHybridLedger`; the certificate-marked fan and its
degree cap `d_G(h) ≤ 8` are `Hypostructure.Graph.TypeBMarkedFan`; the
high-neighbourhood normal form is `Hypostructure.Graph.TypeBOpenPorts`.

## The manuscript's absence hypotheses are alternatives, not hypotheses

`lem:typeB-exclusion` is stated in the manuscript as a conditional:

> Let `X` be a connected admissible support carrying high-degree surplus.
> Assume that `X` contains no fan-certificate residual center and admits the
> refined support ledger B2.  If `X` contains neither an admissible route-8
> residual profile nor an admissible positive-deficit Type B fan-window
> residual, then `def⁺(X) - σ(X) ≥ |V(X)|/4`, so that `No(X) ≥ 0`.
> Consequently, a Type B support with `No(X) < 0` and with no route-8 or
> positive-deficit fan-window residual is a Type B bridge residual: it witnesses
> failure of B2.

Every one of those "contains no ..." clauses is carried here as an *alternative*
of a disjunction rather than as a hypothesis, so `typeBExclusion` has **no**
hypothesis asserting the absence of a configuration:

* "no fan-certificate residual center" is the *positive* datum
  `markedAt : centre ↦ Marked object` -- a certificate-marked fan at each
  assigned centre.  `TypeBMarkedFan.IsFanCertificateResidual` is precisely the
  negation of that datum, so supplying it is exactly the manuscript's
  hypothesis, in positive form.
* "admits B2" is replaced by the decidable dichotomy
  `disjointCarriers_or_sharedCarrier`: either the fan entries have disjoint
  carriers, or two assigned centres share one -- a minimal Type B overlap
  obstruction, i.e. a **Type B bridge residual**, which is retained as an
  alternative and is never closed here.
* "no positive-deficit Type B fan-window residual" is replaced by the sign
  dichotomy on `D_B(𝔉_h)`.  On the positive side the hybrid B1 ledger of
  `lem:typeB-hybrid-B1` pays the deficit; that fan is retained, not excluded.
* "no route-8 residual profile" is replaced by the sign of the post-ledger core
  charge `Residual.residualCoreCharge`, exactly as
  `lem:typeB-bridge-with-route8-core` carries `-D_A(𝒜_X)` in its conclusion
  rather than assuming the absence of a route-8 core.  The route-8 core is
  retained as an alternative and is never closed here.

The only ambient structural input is `TypeBOpenPorts.NormalForm`, an explicit
argument exactly as in `TypeBOpenPorts.heavyCenterTriangularAlternative`,
`TypeBFanClosedPorts.fanClosedPortTypeBRouting` and
`TypeBBridgeResidual.negativePart_le_eight_surplus`; the four-cycle absence
behind it is read off the incoming residual by
`TypeBOpenPorts.LocalHypotheses.normalForm` (`ctx.avoids`).

Manuscript invariants consumed: 4 (high-degree independence, through
`NormalForm.neighbourCubic`, i.e. edge-deletion criticality), 16
(certificate-marked fan degree `d_G(h) ≤ 8`, through `Marked.degree_le_eight`),
23 (window stub capacity, through the hybrid window/non-window credit of
`Profile.hybridCapacity`), 24 (remainder deficiency density: the charges
`δ⁺_X`, `ch_X` and the deficit `D_B = c - (3 - (k+1)α)`), and 25 (legal `P₁₃`
labels, through the fan certificate carried by `Marked`).

All rational quantities are over `ℚ`, consistent with
`TypeBFanClosedPorts.Profile.closedNeighbourDeficit` and
`TypeBBridgeResidual.Residual.netCharge`.
-/

namespace Hypostructure.Graph.TypeBExclusion

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts
open Hypostructure.Graph.TypeBBridgeResidual
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u

variable {object : FiniteObject.{u}}

/-! ## `def:typeB-multiclosed-residual`: the deficit of an assigned fan

The manuscript's `c(𝔉_h)` counts the cubic-closed fan neighbours of `h`
recorded by the assigned profile.  Inside a support those are exactly the fan
neighbours whose two non-`h` incidences are carried by the counted core, i.e.
`Residual.closedFanNeighbours` -- the neighbours that can carry negative charge.
The two counts agree on the nose whenever the profile records the fan on the
remainder side (`deficit_fanProfile` below, which is
`TypeBBridgeResidual.closedCount_eq_closedFanCount`). -/

/-- `D_B(𝔉_h) = c(𝔉_h) - (3 - (k+1)α)` of `def:typeB-multiclosed-residual`,
computed on the assigned Type B support, with the discharge rate `α` read from
the registered presentation.  At `α = 1/4` the subtrahend is the manuscript's
`(11 - k)/4`.

This is the same expression as
`TypeBFanClosedPorts.Profile.closedNeighbourDeficit`, on the support's own
closed-fan count; `deficit_fanProfile` identifies the two. -/
noncomputable def fanDeficit (residual : Residual object)
    (ledger : LoadCapacityProfile) (hub : object.Vertex) : ℚ :=
  (residual.closedFanCount hub : ℚ)
    - (3 - ((object.degree hub : ℚ) + 1) * ledger.dischargeRate)

/-- `def:typeB-multiclosed-residual`: the fan at `h` is *certificate-closed*
when `D_B(𝔉_h) ≤ 0`. -/
def IsCertificateClosed (residual : Residual object)
    (ledger : LoadCapacityProfile) (hub : object.Vertex) : Prop :=
  fanDeficit residual ledger hub ≤ 0

/-- The largest closed-neighbour count a certificate-closed fan of degree `k`
can carry: `⌊3 - (k+1)α⌋`.

This is not a new threshold -- it is the integer part of the subtrahend of
`fanDeficit`, i.e. of the manuscript's own `(11-k)/4` at `α = 1/4`, where it
*computes* to `1` for `k ≤ 7` and to `0` for `k = 8` (the manuscript's "when
`k = 8`, the exclusion of the positive-deficit residual forces `c = 0`"). -/
noncomputable def closedCountCap (ledger : LoadCapacityProfile) (degree : Nat) : ℤ :=
  ⌊3 - ((degree : ℚ) + 1) * ledger.dischargeRate⌋

/-- The manuscript's "Equivalently" clause of `def:typeB-multiclosed-residual`:
certificate-closedness is a bound on the closed-neighbour count alone.

At the registered `α = 1/4` the right-hand side computes to `c ≤ 1` for `k ≤ 7`
and `c = 0` for `k = 8`; no degree window is needed to state it, because the cap
is read off the rate rather than tabulated. -/
theorem isCertificateClosed_iff (residual : Residual object)
    (ledger : LoadCapacityProfile) (hub : object.Vertex) :
    IsCertificateClosed residual ledger hub ↔
      (residual.closedFanCount hub : ℤ) ≤ closedCountCap ledger (object.degree hub) := by
  unfold IsCertificateClosed fanDeficit closedCountCap
  rw [Int.le_floor]
  push_cast
  constructor
  · intro closed
    linarith
  · intro small
    linarith

/-! ## The assigned fan-window profile at one centre of the support -/

/-- The assigned Type B fan-window profile `𝔉_h` of
`def:typeB-window-incidence-profile` carried by the support `X` at one of its
assigned centres: the certificate-marked fan at `h`, the ambient packed-window
union `W`, and the counted core `Y_X` as the assigned fan envelope.

This is not a new carrier: it is `TypeBFanClosedPorts.Profile`, whose three
data fields are supplied by the support and the marked fan. -/
def fanProfile (residual : Residual object) (window : Finset object.Vertex)
    (marked : Marked object) : Profile object where
  marked := marked
  window := window
  envelope := residual.core

/-- The profile's `c(𝔉)` is the support's count of cubic-closed fan
neighbours, hence the two deficits agree.  This is
`TypeBBridgeResidual.closedCount_eq_closedFanCount`, whose input is the
recording convention of `def:typeB-window-incidence-profile` ("a profile records
the assigned fan neighbours that lie in the remainder side `R = G - W`") -- a
positive statement about the profile, never an absence. -/
theorem deficit_fanProfile (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (window : Finset object.Vertex) (marked : Marked object)
    (normal : NormalForm object marked.fan.hub)
    (remainderSide : ∀ u : object.Vertex,
      object.graph.Adj marked.fan.hub u → u ∉ window) :
    (fanProfile residual window marked).closedNeighbourDeficit ledger
      = fanDeficit residual ledger marked.fan.hub := by
  unfold Profile.closedNeighbourDeficit fanDeficit
  rw [closedCount_eq_closedFanCount residual (fanProfile residual window marked)
    normal rfl remainderSide]
  rfl

/-! ## Step 1 of `lem:typeB-exclusion`: the closed-neighbourhood charge

The manuscript computes, for the assigned centre `h` of degree `k` with `c`
cubic-closed neighbours,

`ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) ≥ (3 - k - α) + c(-α) + (k - c)(1 - α)
  = (3 - (k+1)α) - c = -D_B(𝔉_h)`,

which at `α = 1/4` is the manuscript's own `(11-k)/4 - c`.

`ch_X(h) = 3 - k - α` is `TypeBBridgeResidual.centerCharge`; the two neighbour
bounds are `Residual.neg_dischargeRate_le_vertexCharge` and
`Residual.one_sub_dischargeRate_le_vertexCharge_of_coreDegree_le_two`, the latter
fed by `Residual.coreDegree_le_two_of_unassigned` and
`NormalForm.neighbourCubic`. -/

/-- The fan entry of `def:typeB-candidate-ledger` (a) at an assigned centre, in
the `No`-form: the charge carried by the fan envelope block minus the surplus
unit `d_G(h) - 3` assigned to the centre.  `fanEntryCharge_eq` identifies it
with the manuscript's `ch_X(h) + Σ_{u ∈ N(h)} ch_X(u)`. -/
noncomputable def fanEntryCharge (residual : Residual object)
    (ledger : LoadCapacityProfile) (hub : object.Vertex) : ℚ :=
  (∑ y ∈ residual.envelopeBlock hub, residual.vertexCharge ledger y)
    - ((object.degree hub : ℚ) - 3)

/-- The counted core sees the whole fan, so `d_{Y_X}(h) = d_G(h)`. -/
theorem coreDegree_hub (residual : Residual object) {hub : object.Vertex}
    (fanInCore : neighbourRim object hub ⊆ residual.core) :
    residual.coreDegree hub = object.degree hub := by
  have setEq : (residual.core.filter fun w => object.graph.Adj hub w)
      = neighbourRim object hub := by
    ext w
    rw [Finset.mem_filter, mem_neighbourRim]
    exact ⟨fun member => member.2,
      fun adjacency => ⟨fanInCore ((mem_neighbourRim object hub w).2 adjacency), adjacency⟩⟩
  unfold Residual.coreDegree
  rw [setEq]
  exact card_eq_degree_of_isNeighbourhood object hub _ (mem_neighbourRim object hub)

/-- A high-degree centre seen by its own fan is not deficient: `δ⁺_X(h) = 0`. -/
theorem deficiency_hub (residual : Residual object) {hub : object.Vertex}
    (high : 4 ≤ object.degree hub)
    (fanInCore : neighbourRim object hub ⊆ residual.core) :
    residual.deficiency hub = 0 := by
  have degreeEq := coreDegree_hub residual fanInCore
  have cast : (4 : ℚ) ≤ (object.degree hub : ℚ) := by exact_mod_cast high
  unfold Residual.deficiency
  refine max_eq_left ?_
  rw [degreeEq]
  linarith

/-- The centre's own ordinary charge is exactly one discharge unit. -/
theorem vertexCharge_hub (residual : Residual object)
    (ledger : LoadCapacityProfile) {hub : object.Vertex}
    (high : 4 ≤ object.degree hub)
    (fanInCore : neighbourRim object hub ⊆ residual.core) :
    residual.vertexCharge ledger hub = -ledger.dischargeRate := by
  unfold Residual.vertexCharge
  rw [deficiency_hub residual high fanInCore]
  ring

theorem hub_not_mem_rim (object : FiniteObject.{u}) (hub : object.Vertex) :
    hub ∉ neighbourRim object hub := by
  intro member
  exact object.graph.irrefl ((mem_neighbourRim object hub hub).1 member)

/-- When the counted core carries the whole fan, the envelope block is the
closed neighbourhood `{h} ∪ N(h)`, so a weight sums over it as the centre plus
the whole fan. -/
theorem sum_envelopeBlock (residual : Residual object) {hub : object.Vertex}
    (fanInCore : neighbourRim object hub ⊆ residual.core)
    (weight : object.Vertex → ℚ) :
    ∑ y ∈ residual.envelopeBlock hub, weight y
      = weight hub + ∑ u ∈ neighbourRim object hub, weight u := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have blockEq :
      residual.envelopeBlock hub = insert hub (neighbourRim object hub) := by
    simp only [Residual.envelopeBlock]
    congr 1
    exact Finset.inter_eq_left.2 fanInCore
  rw [blockEq, Finset.sum_insert (hub_not_mem_rim object hub)]

/-- The fan entry is literally the manuscript's
`ch_X(h) + Σ_{u ∈ N(h)} ch_X(u)`, with `ch_X(h) = 3 - k - α` the assigned
centre charge of `def:typeB-assigned-ledger`. -/
theorem fanEntryCharge_eq (residual : Residual object)
    (ledger : LoadCapacityProfile) {hub : object.Vertex}
    (high : 4 ≤ object.degree hub)
    (fanInCore : neighbourRim object hub ⊆ residual.core) :
    fanEntryCharge residual ledger hub
      = centerCharge object ledger hub
        + ∑ u ∈ neighbourRim object hub, residual.vertexCharge ledger u := by
  unfold fanEntryCharge centerCharge
  rw [sum_envelopeBlock residual fanInCore,
    vertexCharge_hub residual ledger high fanInCore]
  ring

/-- Every fan neighbour that is *not* cubic-closed has an incidence outside the
counted core, hence internal degree at most two, hence charge at least `1 - α`
(the manuscript's `3/4` at `α = 1/4`).  Cubicity of the neighbour is
`NormalForm.neighbourCubic` (invariant 4 in its edge-deletion-critical form). -/
theorem one_sub_dischargeRate_le_vertexCharge_of_not_closed (residual : Residual object)
    (ledger : LoadCapacityProfile)
    {hub : object.Vertex} (normal : NormalForm object hub)
    {u : object.Vertex} (rimMember : u ∈ neighbourRim object hub)
    (notClosed : u ∉ residual.closedFanNeighbours hub) :
    1 - ledger.dischargeRate ≤ residual.vertexCharge ledger u := by
  have adjacency : object.graph.Adj hub u := (mem_neighbourRim object hub u).1 rimMember
  have failing : ¬ ∀ w : object.Vertex, object.graph.Adj u w → w ≠ hub →
      w ∈ residual.core := by
    intro assigned
    exact notClosed (Residual.mem_closedFanNeighbours_iff.2 ⟨adjacency, assigned⟩)
  simp only [not_forall] at failing
  obtain ⟨w, adjW, _, outside⟩ := failing
  exact residual.one_sub_dischargeRate_le_vertexCharge_of_coreDegree_le_two ledger
    (residual.coreDegree_le_two_of_unassigned (normal.neighbourCubic adjacency) adjW outside)

/-- **Step 1 of `lem:typeB-exclusion`** (the charge half of
`lem:fan-certificate`).  At an assigned centre whose fan the counted core
carries,

`ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) ≥ (3 - (k+1)α) - c = -D_B(𝔉_h)`.

No sign hypothesis on `D_B` is used, so the inequality holds at every assigned
centre; the certificate-closed conclusion is the corollary below. -/
theorem neg_fanDeficit_le_fanEntryCharge (residual : Residual object)
    (ledger : LoadCapacityProfile)
    {hub : object.Vertex} (normal : NormalForm object hub)
    (fanInCore : neighbourRim object hub ⊆ residual.core) :
    -(fanDeficit residual ledger hub) ≤ fanEntryCharge residual ledger hub := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have closedSubset : residual.closedFanNeighbours hub ⊆ neighbourRim object hub :=
    Finset.filter_subset _ _
  have rimCard : (neighbourRim object hub).card = object.degree hub :=
    card_eq_degree_of_isNeighbourhood object hub _ (mem_neighbourRim object hub)
  have split :
      (∑ u ∈ neighbourRim object hub \ residual.closedFanNeighbours hub,
          residual.vertexCharge ledger u)
        + ∑ u ∈ residual.closedFanNeighbours hub, residual.vertexCharge ledger u
        = ∑ u ∈ neighbourRim object hub, residual.vertexCharge ledger u :=
    Finset.sum_sdiff closedSubset
  have lowClosed :
      ((residual.closedFanNeighbours hub).card : ℚ) * (-ledger.dischargeRate)
        ≤ ∑ u ∈ residual.closedFanNeighbours hub, residual.vertexCharge ledger u := by
    have step := Finset.card_nsmul_le_sum (residual.closedFanNeighbours hub)
      (residual.vertexCharge ledger) (-ledger.dischargeRate)
      fun y _ => residual.neg_dischargeRate_le_vertexCharge ledger y
    rwa [nsmul_eq_mul] at step
  have lowRest :
      ((neighbourRim object hub \ residual.closedFanNeighbours hub).card : ℚ)
          * (1 - ledger.dischargeRate)
        ≤ ∑ u ∈ neighbourRim object hub \ residual.closedFanNeighbours hub,
            residual.vertexCharge ledger u := by
    have step := Finset.card_nsmul_le_sum
      (neighbourRim object hub \ residual.closedFanNeighbours hub)
      (residual.vertexCharge ledger) (1 - ledger.dischargeRate) ?_
    · rwa [nsmul_eq_mul] at step
    · intro y member
      obtain ⟨rimMember, notClosed⟩ := Finset.mem_sdiff.1 member
      exact one_sub_dischargeRate_le_vertexCharge_of_not_closed residual ledger normal
        rimMember notClosed
  have cardDiff :
      (neighbourRim object hub \ residual.closedFanNeighbours hub).card
        = (neighbourRim object hub).card - (residual.closedFanNeighbours hub).card :=
    Finset.card_sdiff_of_subset closedSubset
  have countLe : (residual.closedFanNeighbours hub).card ≤ (neighbourRim object hub).card :=
    Finset.card_le_card closedSubset
  have cardCast :
      ((neighbourRim object hub \ residual.closedFanNeighbours hub).card : ℚ)
        = (object.degree hub : ℚ) - (residual.closedFanCount hub : ℚ) := by
    rw [cardDiff, rimCard] at *
    have countDef : residual.closedFanCount hub = (residual.closedFanNeighbours hub).card := rfl
    rw [countDef]
    have step : ((object.degree hub - (residual.closedFanNeighbours hub).card : Nat) : ℚ)
        = (object.degree hub : ℚ) - ((residual.closedFanNeighbours hub).card : ℚ) := by
      rw [Nat.cast_sub (by omega)]
    exact step
  have countDef : ((residual.closedFanNeighbours hub).card : ℚ)
      = (residual.closedFanCount hub : ℚ) := rfl
  rw [fanEntryCharge_eq residual ledger normal.high fanInCore]
  unfold fanDeficit centerCharge
  rw [countDef] at lowClosed
  rw [cardCast] at lowRest
  linarith

/-- **The certificate-closed fan carries nonnegative charge**
(`lem:fan-certificate`, charge half; `def:typeB-multiclosed-residual`).  This is
the first alternative of the manuscript's Type B ledger. -/
theorem fanEntryCharge_nonneg (residual : Residual object)
    (ledger : LoadCapacityProfile) {hub : object.Vertex}
    (normal : NormalForm object hub)
    (fanInCore : neighbourRim object hub ⊆ residual.core)
    (closed : IsCertificateClosed residual ledger hub) :
    0 ≤ fanEntryCharge residual ledger hub := by
  have step := neg_fanDeficit_le_fanEntryCharge residual ledger normal fanInCore
  unfold IsCertificateClosed at closed
  linarith

/-! ## `def:typeB-bridge-statements` (B2): the disjoint-carrier clause -/

/-- The disjoint-carrier part of the refined support ledger B2, clauses (a) and
(c) of `def:typeB-bridge-statements`: no carrier is assigned to two different
fan centres, so the fan entries are a disjoint refinement of the augmented
ledger. -/
def DisjointCarriers (residual : Residual object) : Prop :=
  ∀ h ∈ residual.centers, ∀ h' ∈ residual.centers, h ≠ h' →
    Disjoint (residual.envelopeBlock h) (residual.envelopeBlock h')

/-- The failure of the disjoint-carrier clause, in the explicit form of
`def:typeB-overlap-obstruction`: two distinct assigned fan centres of the same
support share a carrier.  A support in this state is a **Type B bridge
residual** (`def:typeB-bridge-statements` (ii)); nothing here closes it. -/
def SharedCarrier (residual : Residual object) : Prop :=
  ∃ h ∈ residual.centers, ∃ h' ∈ residual.centers, h ≠ h' ∧
    ∃ carrier : object.Vertex,
      carrier ∈ residual.envelopeBlock h ∧ carrier ∈ residual.envelopeBlock h'

/-- B2's disjoint-carrier clause is a genuine dichotomy: either it holds, or the
support exhibits an explicit overlap obstruction.  This is what replaces the
manuscript's "assume `X` admits B2" hypothesis. -/
theorem disjointCarriers_or_sharedCarrier (residual : Residual object) :
    DisjointCarriers residual ∨ SharedCarrier residual := by
  classical
  by_cases holds : DisjointCarriers residual
  · exact Or.inl holds
  · refine Or.inr ?_
    by_contra shared
    refine holds ?_
    intro h hMember h' h'Member distinct
    rw [Finset.disjoint_left]
    intro carrier leftMember rightMember
    exact shared ⟨h, hMember, h', h'Member, distinct, carrier, leftMember, rightMember⟩

/-! ## Step 2 of `lem:typeB-exclusion`: summing the entries under B2 -/

/-- **Clause B2(c) in force.**  Under the disjoint-carrier clause the fan
entries and the post-ledger core are a disjoint refinement of the net charge:

`No(X) = (charge of the post-ledger core) + Σ_{h ∈ H_X} (fan entry at h)`.

This is an exact identity, not an estimate: the surplus units cancel against the
assigned centre charges of `def:typeB-assigned-ledger`. -/
theorem netCharge_eq_residualCoreCharge_add_sum_fanEntryCharge
    (residual : Residual object) (ledger : LoadCapacityProfile)
    (b2 : DisjointCarriers residual) :
    residual.netCharge ledger
      = residual.residualCoreCharge ledger
        + ∑ h ∈ residual.centers, fanEntryCharge residual ledger h := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have unionSubset :
      residual.centers.biUnion residual.envelopeBlock ⊆ residual.core :=
    residual.biUnion_envelopeBlock_subset_core
  have splitSum :
      residual.residualCoreCharge ledger
          + ∑ y ∈ residual.centers.biUnion residual.envelopeBlock,
              residual.vertexCharge ledger y
        = ∑ y ∈ residual.core, residual.vertexCharge ledger y := by
    rw [Residual.residualCoreCharge, Residual.residualCore]
    exact Finset.sum_sdiff unionSubset
  have pairwise :
      (residual.centers : Set object.Vertex).PairwiseDisjoint residual.envelopeBlock := by
    intro a aMember b bMember distinct
    exact b2 a (Finset.mem_coe.1 aMember) b (Finset.mem_coe.1 bMember) distinct
  have blocks :
      ∑ y ∈ residual.centers.biUnion residual.envelopeBlock, residual.vertexCharge ledger y
        = ∑ h ∈ residual.centers,
            ∑ y ∈ residual.envelopeBlock h, residual.vertexCharge ledger y :=
    Finset.sum_biUnion pairwise
  have entries :
      ∑ h ∈ residual.centers,
          ∑ y ∈ residual.envelopeBlock h, residual.vertexCharge ledger y
        = (∑ h ∈ residual.centers, fanEntryCharge residual ledger h) + residual.surplus := by
    unfold fanEntryCharge Residual.surplus
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have ledgerIdentity := residual.netCharge_eq_sum_vertexCharge_sub_surplus ledger
  rw [blocks, entries] at splitSum
  linarith

/-- **Step 2 of `lem:typeB-exclusion`, quantitative form.**  Under B2's
disjoint-carrier clause the net charge of the support is bounded below by the
post-ledger core charge minus the total positive deficit of its fans. -/
theorem residualCoreCharge_sub_sum_fanDeficit_le_netCharge (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (fanInCore : ∀ h ∈ residual.centers, neighbourRim object h ⊆ residual.core)
    (b2 : DisjointCarriers residual) :
    residual.residualCoreCharge ledger
        - ∑ h ∈ residual.centers, fanDeficit residual ledger h
      ≤ residual.netCharge ledger := by
  have identity :=
    netCharge_eq_residualCoreCharge_add_sum_fanEntryCharge residual ledger b2
  have bound :
      ∑ h ∈ residual.centers, -(fanDeficit residual ledger h)
        ≤ ∑ h ∈ residual.centers, fanEntryCharge residual ledger h :=
    Finset.sum_le_sum fun h member =>
      neg_fanDeficit_le_fanEntryCharge residual ledger (normal h member) (fanInCore h member)
  rw [Finset.sum_neg_distrib] at bound
  linarith

/-- **`lem:typeB-exclusion`, conclusion form.**  A support all of whose assigned
fans are certificate-closed, whose fan entries have disjoint carriers (B2), and
whose post-ledger core is discharged, has `No(X) ≥ 0`. -/
theorem netCharge_nonneg_of_certificateClosed (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (fanInCore : ∀ h ∈ residual.centers, neighbourRim object h ⊆ residual.core)
    (b2 : DisjointCarriers residual)
    (closed : ∀ h ∈ residual.centers, IsCertificateClosed residual ledger h)
    (discharged : 0 ≤ residual.residualCoreCharge ledger) :
    0 ≤ residual.netCharge ledger := by
  have main :=
    residualCoreCharge_sub_sum_fanDeficit_le_netCharge residual ledger normal fanInCore b2
  have nonpos : ∑ h ∈ residual.centers, fanDeficit residual ledger h ≤ 0 :=
    Finset.sum_nonpos fun h member => closed h member
  linarith

/-- The manuscript's displayed inequality `def⁺(X) - σ(X) ≥ |V(X)|/4` is the
same statement as `No(X) ≥ 0`; generically the right-hand side is `α|V(X)|`. -/
theorem card_mul_dischargeRate_le_of_netCharge_nonneg (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (nonneg : 0 ≤ residual.netCharge ledger) :
    (residual.core.card : ℚ) * ledger.dischargeRate
      ≤ residual.totalDeficiency - residual.surplus := by
  unfold Residual.netCharge at nonneg
  linarith

/-! ## `lem:typeB-exclusion` -/

/-- **`lem:typeB-exclusion`**, manuscript node `[65]` (`typeB`), fed by
`[71]`--`[73]` and `[82]`--`[85]`.

Let `X` be an assigned Type B support each of whose assigned centres carries a
certificate-marked fan (equivalently: `X` contains no fan-certificate residual
centre), whose counted core carries those fans, and which records them on the
remainder side `R = G - W`.  Then exactly the manuscript's refined Type B ledger
holds, as a four-way alternative:

* **(b1)** some assigned centre carries a *positive-deficit Type B fan-window
  residual*, `D_B(𝔉_h) > 0`, and the hybrid B1 ledger of
  `lem:typeB-hybrid-B1` pays it: `D_B(𝔉_h) ≤ ½ I_W + D_N`; or
* **(res-B2)** two assigned centres share a carrier -- the support is a
  **Type B bridge residual**, witnessing failure of the disjoint-carrier clause
  B2 of `def:typeB-bridge-statements`; or
* **(res-8)** the post-ledger core carries negative charge -- the retained
  **route-8 / Type A residual core** of `lem:typeB-bridge-with-route8-core`; or
* **(a)** every assigned fan satisfies the whole of Step 1: the label-packing
  degree bound `k = d_G(h) ≤ 8`, certificate-closedness `D_B(𝔉_h) ≤ 0` in both
  the deficit and the `c`-forms (`c ≤ ⌊3 - (k+1)α⌋`, which at the registered
  `α = 1/4` computes to `1` for `k ≤ 7` and to `0` for `k = 8` -- the
  manuscript's "when `k = 8`, the exclusion of the positive-deficit residual
  forces `c = 0`"), and nonnegative closed-neighbourhood charge; and
  `No(X) ≥ 0`, i.e. `def⁺(X) - σ(X) ≥ α|V(X)|`.

The last alternative is the manuscript's conclusion; the middle two are the two
residuals the manuscript retains, so this is exactly "Type B is killed outside
route 8 and outside the Type B bridge residual".

There is no hypothesis of the form "configuration `X` does not occur": the
manuscript's three absence clauses are the first three alternatives. -/
theorem typeBExclusion (residual : Residual object) (ledger : LoadCapacityProfile)
    (window : Finset object.Vertex)
    (markedAt : object.Vertex → Marked object)
    (hubAt : ∀ h ∈ residual.centers, (markedAt h).fan.hub = h)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (fanInCore : ∀ h ∈ residual.centers, neighbourRim object h ⊆ residual.core)
    (remainderSide : ∀ h ∈ residual.centers, ∀ u : object.Vertex,
      object.graph.Adj h u → u ∉ window) :
    (∃ h ∈ residual.centers,
        0 < (fanProfile residual window (markedAt h)).closedNeighbourDeficit ledger ∧
          (fanProfile residual window (markedAt h)).closedNeighbourDeficit ledger
            ≤ (fanProfile residual window (markedAt h)).hybridCapacity ledger) ∨
      SharedCarrier residual ∨
      residual.residualCoreCharge ledger < 0 ∨
      ((∀ h ∈ residual.centers,
          object.degree h ≤ 8 ∧
            IsCertificateClosed residual ledger h ∧
            (residual.closedFanCount h : ℤ) ≤ closedCountCap ledger (object.degree h) ∧
            0 ≤ fanEntryCharge residual ledger h) ∧
        0 ≤ residual.netCharge ledger ∧
        (residual.core.card : ℚ) * ledger.dischargeRate
          ≤ residual.totalDeficiency - residual.surplus) := by
  classical
  by_cases positive : ∃ h ∈ residual.centers, 0 < fanDeficit residual ledger h
  · obtain ⟨h, member, deficitPos⟩ := positive
    refine Or.inl ⟨h, member, ?_, ?_⟩
    · have normalAt : NormalForm object (markedAt h).fan.hub := by
        rw [hubAt h member]
        exact normal h member
      have remainderAt : ∀ u : object.Vertex,
          object.graph.Adj (markedAt h).fan.hub u → u ∉ window := by
        rw [hubAt h member]
        exact remainderSide h member
      have deficitEq :=
        deficit_fanProfile residual ledger window (markedAt h) normalAt remainderAt
      rw [hubAt h member] at deficitEq
      rw [deficitEq]
      exact deficitPos
    · have normalAt : NormalForm object (markedAt h).fan.hub := by
        rw [hubAt h member]
        exact normal h member
      exact (Profile.typeBHybridB1 (fanProfile residual window (markedAt h)) ledger normalAt).1
  · have closed : ∀ h ∈ residual.centers, IsCertificateClosed residual ledger h := by
      intro h member
      unfold IsCertificateClosed
      by_contra notClosed
      exact positive ⟨h, member, not_le.1 notClosed⟩
    rcases disjointCarriers_or_sharedCarrier residual with b2 | shared
    · rcases lt_or_ge (residual.residualCoreCharge ledger) 0 with negative | discharged
      · exact Or.inr (Or.inr (Or.inl negative))
      · have nonneg := netCharge_nonneg_of_certificateClosed residual ledger normal fanInCore b2
          closed discharged
        refine Or.inr (Or.inr (Or.inr
          ⟨fun h member => ?_, nonneg,
            card_mul_dischargeRate_le_of_netCharge_nonneg residual ledger nonneg⟩))
        have cap : object.degree h ≤ 8 := by
          have step := (markedAt h).degree_le_eight
          rwa [hubAt h member] at step
        exact ⟨cap, closed h member,
          (isCertificateClosed_iff residual ledger h).1 (closed h member),
          fanEntryCharge_nonneg residual ledger (normal h member) (fanInCore h member)
            (closed h member)⟩
    · exact Or.inr (Or.inl shared)

/-- **The "Consequently" clause of `lem:typeB-exclusion`.**  A Type B support
with `No(X) < 0` whose assigned fans are all certificate-closed and whose
post-ledger core is discharged *is* a Type B bridge residual: it exhibits two
assigned centres sharing a carrier, i.e. it witnesses failure of the
disjoint-carrier clause B2 of `def:typeB-bridge-statements`.

The residual is produced, never closed. -/
theorem sharedCarrier_of_netCharge_neg (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (fanInCore : ∀ h ∈ residual.centers, neighbourRim object h ⊆ residual.core)
    (closed : ∀ h ∈ residual.centers, IsCertificateClosed residual ledger h)
    (discharged : 0 ≤ residual.residualCoreCharge ledger)
    (negative : residual.netCharge ledger < 0) :
    SharedCarrier residual := by
  rcases disjointCarriers_or_sharedCarrier residual with b2 | shared
  · exact absurd
      (netCharge_nonneg_of_certificateClosed residual ledger normal fanInCore b2 closed
        discharged)
      (not_le.2 negative)
  · exact shared

/-! ## Non-vacuity

Both live branches of the exclusion are realised on the explicit finite graph
already used by `TypeBFanClosedPorts` and `TypeBBridgeResidual`: a degree-four
centre whose four neighbours are cubic with private shoulder pairs.  In each
case every hypothesis of `typeBExclusion` is discharged, the other three
alternatives are *refuted*, and the four-way alternative therefore resolves to a
named branch.  Both branches hold at **every** presentation profile, so neither
depends on the registered numeral.

* On the support the object's own enumeration produces -- the canonical assigned
  envelope, which carries every shoulder -- all four fan neighbours are
  cubic-closed, so `D_B = 4 - (3 - 5α) = 1 + 5α > 0` (the manuscript's `9/4` at
  `α = 1/4`) and the alternative resolves to the **positive-deficit fan paid by
  the hybrid B1 ledger** (`positiveDeficit_branch`).
* On the support that stops at the closed neighbourhood of the centre -- so that
  no shoulder is assigned -- no fan neighbour is cubic-closed, `c = 0`,
  `D_B = 5α - 3 ≤ 0` by the ledger's own `9α ≤ 3` (the manuscript's `-7/4` at
  `α = 1/4`), the post-ledger core is empty, and the alternative resolves to the
  **certificate-closed conclusion `No(X) ≥ 0`** (`certificateClosed_branch`).

The centre set is nonempty in both cases (`hub_mem_bridge_centers`,
`hub_mem_closed_centers`), so neither branch is reached vacuously. -/

namespace Witness

open Hypostructure.Graph.TypeBFanClosedPorts.Witness
open Hypostructure.Graph.TypeBBridgeResidual.Witness

local instance vertexDecEq : DecidableEq fanObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 13))

local instance vertexFintype : Fintype fanObject.Vertex :=
  inferInstanceAs (Fintype (Fin 13))

local instance adjDecidable : DecidableRel fanObject.graph.Adj := fanObject.decideAdj

/-- The certificate-marked fan supplied at every vertex: the witness fan.  This
is the positive datum "the support contains no fan-certificate residual
centre". -/
def markedAt : fanObject.Vertex → Marked fanObject := fun _ => markedFan

theorem markedAt_hub (h : fanObject.Vertex) : (markedAt h).fan.hub = hub := rfl

/-- The packed-window union misses the fan, so the profile records its
neighbours on the remainder side `R = G - W`. -/
theorem window_separated :
    ∀ u : fanObject.Vertex, fanObject.graph.Adj hub u → u ∉ hybridWindow := by
  decide

/-! ### The positive-deficit branch -/

theorem bridge_rim_subset_core :
    neighbourRim fanObject hub ⊆ bridgeResidual.core := by
  intro v _
  rw [core_eq]
  exact fanObject.mem_vertexFinset v

/-- `c = k = 4` gives `D_B = 4 - (3 - 5α) = 1 + 5α`, the manuscript's `9/4` at
`α = 1/4`. -/
theorem bridge_fanDeficit (ledger : LoadCapacityProfile) :
    fanDeficit bridgeResidual ledger hub = 1 + 5 * ledger.dischargeRate := by
  unfold fanDeficit
  rw [closedFanCount_eq, degree_hub]
  push_cast
  ring

/-- The exclusion theorem applies to the support the object's own enumeration
produces: every hypothesis is realised. -/
theorem exclusion_applies_positiveDeficit (ledger : LoadCapacityProfile) :
    (∃ h ∈ bridgeResidual.centers,
        0 < (fanProfile bridgeResidual hybridWindow (markedAt h)).closedNeighbourDeficit
              ledger ∧
          (fanProfile bridgeResidual hybridWindow (markedAt h)).closedNeighbourDeficit
              ledger
            ≤ (fanProfile bridgeResidual hybridWindow (markedAt h)).hybridCapacity ledger) ∨
      SharedCarrier bridgeResidual ∨
      bridgeResidual.residualCoreCharge ledger < 0 ∨
      ((∀ h ∈ bridgeResidual.centers,
          fanObject.degree h ≤ 8 ∧
            IsCertificateClosed bridgeResidual ledger h ∧
            (bridgeResidual.closedFanCount h : ℤ)
              ≤ closedCountCap ledger (fanObject.degree h) ∧
            0 ≤ fanEntryCharge bridgeResidual ledger h) ∧
        0 ≤ bridgeResidual.netCharge ledger ∧
        (bridgeResidual.core.card : ℚ) * ledger.dischargeRate
          ≤ bridgeResidual.totalDeficiency - bridgeResidual.surplus) := by
  refine typeBExclusion bridgeResidual ledger hybridWindow markedAt ?_ ?_ ?_ ?_
  · intro h member
    rw [centers_eq, Finset.mem_singleton] at member
    subst member
    rfl
  · intro h member
    rw [centers_eq, Finset.mem_singleton] at member
    subst member
    exact fanNormalForm
  · intro h member
    rw [centers_eq, Finset.mem_singleton] at member
    subst member
    exact bridge_rim_subset_core
  · intro h member
    rw [centers_eq, Finset.mem_singleton] at member
    subst member
    exact window_separated

theorem hub_mem_bridge_centers : hub ∈ bridgeResidual.centers := by
  rw [centers_eq]
  exact Finset.mem_singleton_self hub

theorem bridge_disjointCarriers : DisjointCarriers bridgeResidual := by
  intro h member h' member' distinct
  rw [centers_eq, Finset.mem_singleton] at member member'
  exact absurd (member.trans member'.symm) distinct

/-- **The four-way alternative of `typeBExclusion` resolves to the
positive-deficit branch here.**  The other three alternatives all fail on this
support -- no two centres share a carrier, the post-ledger core is discharged,
and the fan is *not* certificate-closed because `D_B = 1 + 5α > 0` -- so the
exclusion delivers a positive-deficit Type B fan-window residual whose deficit
the hybrid B1 ledger of `lem:typeB-hybrid-B1` pays.  That fan is retained, not
closed. -/
theorem positiveDeficit_branch (ledger : LoadCapacityProfile) :
    ∃ h ∈ bridgeResidual.centers,
      0 < (fanProfile bridgeResidual hybridWindow (markedAt h)).closedNeighbourDeficit
            ledger ∧
        (fanProfile bridgeResidual hybridWindow (markedAt h)).closedNeighbourDeficit
            ledger
          ≤ (fanProfile bridgeResidual hybridWindow (markedAt h)).hybridCapacity ledger := by
  rcases exclusion_applies_positiveDeficit ledger with branch | shared | negative | conclusion
  · exact branch
  · exfalso
    obtain ⟨h, member, h', member', distinct, carrier, leftMember, rightMember⟩ := shared
    exact absurd rightMember
      (Finset.disjoint_left.1 (bridge_disjointCarriers h member h' member' distinct) leftMember)
  · exact absurd negative (not_lt.2 (discharged ledger))
  · exfalso
    obtain ⟨-, closed, -, -⟩ := conclusion.1 hub hub_mem_bridge_centers
    unfold IsCertificateClosed at closed
    rw [bridge_fanDeficit ledger] at closed
    have rate := ledger.dischargeRate_nonneg
    linarith

/-! ### The certificate-closed branch -/

/-- The counted core that stops at the closed neighbourhood of the centre: no
shoulder is assigned, so no fan neighbour is cubic-closed. -/
def closedCore : Finset fanObject.Vertex :=
  letI : DecidableEq fanObject.Vertex := fanObject.vertices.decEq
  insert hub (neighbourRim fanObject hub)

/-- The assigned Type B support carried by that core. -/
def closedResidual : Residual fanObject where
  core := closedCore
  recordedCentres := {hub}

theorem mem_closedCore_iff (vertex : fanObject.Vertex) :
    vertex ∈ closedCore ↔ vertex = hub ∨ fanObject.graph.Adj hub vertex := by
  letI : DecidableEq fanObject.Vertex := fanObject.vertices.decEq
  simp only [closedCore, Finset.mem_insert, mem_neighbourRim]

theorem closed_rim_subset_core :
    neighbourRim fanObject hub ⊆ closedResidual.core := by
  letI : DecidableEq fanObject.Vertex := fanObject.vertices.decEq
  exact Finset.subset_insert _ _

theorem hub_mem_closedCore : hub ∈ closedResidual.core :=
  (mem_closedCore_iff hub).2 (Or.inl rfl)

theorem closed_centers : closedResidual.centers = ({hub} : Finset fanObject.Vertex) := by
  letI : DecidableEq fanObject.Vertex := fanObject.vertices.decEq
  show ({hub} : Finset fanObject.Vertex) ∩ closedResidual.core = {hub}
  exact Finset.inter_eq_left.2 (Finset.singleton_subset_iff.2 hub_mem_closedCore)

/-- Every fan neighbour of the witness centre has an incidence outside the
closed neighbourhood of the centre: its private shoulder. -/
theorem shoulder_outside :
    ∀ u : fanObject.Vertex, fanObject.graph.Adj hub u →
      ∃ w : fanObject.Vertex, fanObject.graph.Adj u w ∧ w ≠ hub ∧
        ¬ fanObject.graph.Adj hub w := by
  decide

/-- No fan neighbour has both non-`h` incidences inside the counted core, so
`c = 0`. -/
theorem closed_closedFanNeighbours :
    closedResidual.closedFanNeighbours hub = (∅ : Finset fanObject.Vertex) := by
  refine Finset.eq_empty_iff_forall_notMem.2 ?_
  intro u member
  obtain ⟨adjacency, assigned⟩ := Residual.mem_closedFanNeighbours_iff.1 member
  obtain ⟨w, incidence, notHub, notAdjacent⟩ := shoulder_outside u adjacency
  rcases (mem_closedCore_iff w).1 (assigned w incidence notHub) with equalHub | adjHub
  · exact notHub equalHub
  · exact notAdjacent adjHub

theorem closed_closedFanCount : closedResidual.closedFanCount hub = 0 := by
  unfold Residual.closedFanCount
  rw [closed_closedFanNeighbours, Finset.card_empty]

/-- `D_B = 0 - (3 - 5α) = 5α - 3 ≤ 0`: the fan is certificate-closed, at every
presentation profile, by the ledger's own fan-credit constraint `9α ≤ 3`.  At
`α = 1/4` this is the manuscript's `-7/4`. -/
theorem closed_isCertificateClosed (ledger : LoadCapacityProfile) :
    IsCertificateClosed closedResidual ledger hub := by
  unfold IsCertificateClosed fanDeficit
  rw [closed_closedFanCount, degree_hub]
  have credit := ledger.nine_mul_dischargeRate_le_three
  have rate := ledger.dischargeRate_nonneg
  push_cast
  linarith

/-- The single fan envelope block exhausts the counted core, so the post-ledger
core is empty. -/
theorem closed_residualCore :
    closedResidual.residualCore = (∅ : Finset fanObject.Vertex) := by
  letI : DecidableEq fanObject.Vertex := fanObject.vertices.decEq
  have blockEq : closedResidual.envelopeBlock hub = closedResidual.core := by
    simp only [Residual.envelopeBlock]
    rw [Finset.inter_eq_left.2 closed_rim_subset_core]
    rfl
  have unionEq :
      closedResidual.centers.biUnion closedResidual.envelopeBlock = closedResidual.core := by
    rw [closed_centers, Finset.singleton_biUnion, blockEq]
  simp only [Residual.residualCore, unionEq, Finset.sdiff_self]

theorem closed_residualCoreCharge (ledger : LoadCapacityProfile) :
    closedResidual.residualCoreCharge ledger = 0 := by
  unfold Residual.residualCoreCharge
  rw [closed_residualCore, Finset.sum_empty]

theorem closed_disjointCarriers : DisjointCarriers closedResidual := by
  intro h member h' member' distinct
  rw [closed_centers, Finset.mem_singleton] at member member'
  exact absurd (member.trans member'.symm) distinct

/-- The support really does carry an assigned high-degree centre. -/
theorem hub_mem_closed_centers : hub ∈ closedResidual.centers := by
  rw [closed_centers]
  exact Finset.mem_singleton_self hub

/-- **The four-way alternative of `typeBExclusion` resolves to the killing
branch here.**  The first three alternatives all fail on this support -- no fan
has positive deficit, no two centres share a carrier, and the post-ledger core
charge is `0` -- so the exclusion delivers its conclusion: every assigned fan
obeys `d_G(h) ≤ 8`, is certificate-closed with `c` under the closed-count cap,
carries nonnegative closed-neighbourhood charge, and `No(X) ≥ 0`, i.e.
`def⁺(X) - σ(X) ≥ α|V(X)|`.  The centre set is nonempty
(`hub_mem_closed_centers`), so the conclusion is not reached vacuously. -/
theorem certificateClosed_branch (ledger : LoadCapacityProfile) :
    (∀ h ∈ closedResidual.centers,
        fanObject.degree h ≤ 8 ∧
          IsCertificateClosed closedResidual ledger h ∧
          (closedResidual.closedFanCount h : ℤ)
            ≤ closedCountCap ledger (fanObject.degree h) ∧
          0 ≤ fanEntryCharge closedResidual ledger h) ∧
      0 ≤ closedResidual.netCharge ledger ∧
      (closedResidual.core.card : ℚ) * ledger.dischargeRate
        ≤ closedResidual.totalDeficiency - closedResidual.surplus := by
  have normal : ∀ h ∈ closedResidual.centers, NormalForm fanObject h := by
    intro h member
    rw [closed_centers, Finset.mem_singleton] at member
    subst member
    exact fanNormalForm
  have fanInCore : ∀ h ∈ closedResidual.centers,
      neighbourRim fanObject h ⊆ closedResidual.core := by
    intro h member
    rw [closed_centers, Finset.mem_singleton] at member
    subst member
    exact closed_rim_subset_core
  have hubAt : ∀ h ∈ closedResidual.centers, (markedAt h).fan.hub = h := by
    intro h member
    rw [closed_centers, Finset.mem_singleton] at member
    subst member
    rfl
  have remainderSide : ∀ h ∈ closedResidual.centers, ∀ u : fanObject.Vertex,
      fanObject.graph.Adj h u → u ∉ hybridWindow := by
    intro h member
    rw [closed_centers, Finset.mem_singleton] at member
    subst member
    exact window_separated
  rcases typeBExclusion closedResidual ledger hybridWindow markedAt hubAt normal fanInCore
    remainderSide with ⟨h, member, deficitPos, -⟩ | shared | negative | conclusion
  · exfalso
    rw [closed_centers, Finset.mem_singleton] at member
    subst member
    rw [deficit_fanProfile closedResidual ledger hybridWindow (markedAt hub) fanNormalForm
      window_separated] at deficitPos
    exact absurd deficitPos (not_lt.2 (closed_isCertificateClosed ledger))
  · exfalso
    obtain ⟨h, member, h', member', distinct, carrier, leftMember, rightMember⟩ := shared
    exact absurd rightMember
      (Finset.disjoint_left.1 (closed_disjointCarriers h member h' member' distinct) leftMember)
  · exfalso
    rw [closed_residualCoreCharge ledger] at negative
    exact absurd negative (by norm_num)
  · exact conclusion

end Witness

end Hypostructure.Graph.TypeBExclusion
