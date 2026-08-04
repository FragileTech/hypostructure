import Hypostructure.Graph.TypeBExclusion

/-!
# The Type B residual fan mass, charged to the bridge-residual centres

This file is the graph-mathematics content of manuscript node `[75]`/`[84]`
(`fanmass`) of `original_erdos_64_proof.tex`, *with the charge set the
manuscript actually uses*:

> Charges **residual centers and B2 failures** to high-degree fan-center surplus
> and obtains `M_B ≤ 16 σ(G) = o(|R|)`.

`Hypostructure.Graph.TypeBBridgeResidual` already carries the ledger
(`Residual`, `No(X)`, `No_-(X)`, `σ(X)`, the fan envelopes, `σ(G)`) and the
*canonical decomposition* `bridgeResiduals`, one assigned support per vertex
carrying ambient surplus.  That collection is `def:canonical-decomp`; it is
**not** the collection `𝒳_B` of `def:typeB-residual-mass`, which is a
*subcollection* -- exactly the members that are Type B bridge residuals in the
sense of `def:typeB-bridge-statements`:

> A *Type B bridge residual* is either (i) a connected assigned Type B support
> containing a fan-certificate residual center of `def:marked-typeB-fan`; or
> (ii) a connected assigned Type B support in which the local B1 entries have
> been supplied, the support assignment has been made maximal, and the
> disjoint-carrier part of B2 fails; or (iii) a grouped decorated Type B
> envelope support whose envelope ledger cannot be closed.

So the charge set of node `[75]` is the set of centres satisfying (i) or (ii) --
"fan-certificate residual centers and B2 failures" -- not the set of *all* heavy
centres.  Clause (iii), the grouped decorated envelope role, is a statement
about which supports enter the collection, not a different estimate: its bound
`lem:decorated-envelope-deficit-bound` is the same per-centre calculation, and
here it is literally the same theorem
(`negativePart_le_eight_surplus_of_discharged`, which quantifies over every
`Residual` and so over multi-centre grouped supports such as `overlapSupport`).

This file supplies the charge set:

* `IsFanCertificateResidual` (clause (i)) is `TypeBMarkedFan`'s, and is decided
  by `TypeBProfileSchedule.isFanCertificateResidual_iff` (`9 ≤ d_G(h)`);
* `IsB2Failure` (clause (ii)) is the local form of `TypeBExclusion.SharedCarrier`
  -- the fan envelope at `h` shares a carrier with the fan envelope at another
  high-degree centre.  `exists_isB2Failure_of_sharedCarrier` proves it is
  implied by `SharedCarrier` on every assigned support (so no B2 failure escapes
  the charge), and `sharedCarrier_overlapSupport` proves the converse on the
  object-derived support that assigns the overlapping pair (so the clause is
  never charged vacuously);
* `IsChargedCentre = IsFanCertificateResidual ∨ IsB2Failure` is the charge set,
  `chargedCentres` its enumeration, and `fanMassResiduals` the collection `𝒳_B`
  -- a genuine `List.Sublist` of `bridgeResiduals`
  (`fanMassResiduals_sublist_bridgeResiduals`), strictly smaller in general
  (`Witness.chargedCentres_witness`: on the degree-four fan witness the charge
  set is *empty* while the heavy-centre set is `[hub]`).

What is proved:

* `sharp_le_eight_surplus_rat` -- the arithmetic step
  `(k - 3) + (1 + k)α ≤ 8(k-3)` of display (1) over `ℚ`, together with its
  equivalence `sharp_le_eight_surplus_iff_rat` to the fan-credit clause
  `(1 + k)α ≤ 7(k - 3)` (the manuscript's `27k ≥ 85` at `α = 1/4`), and
  `envelopeAllowance_sharp_of_mem`, which shows the first inequality of display
  (1) is an equality on the charge set (`c_h = d_G(h)` there), so the estimate
  is not obtained through unrealisable slack;
* `negativePart_le_eight_surplus_of_discharged` and
  `neg_eight_surplus_add_dischargeRate_card_le_netCharge` --
  `lem:typeB-bridge-deficit-bound`, `No_-(X) ≤ 8 Σ_{h ∈ H_X}(d_G(h)-3)` and the
  displayed refinement `No(X) ≥ -8 Σ_{h ∈ H_X}(d_G(h)-3) + α|H_X|`;
* `fanSurplusMass_le_two_globalSurplusPos` -- `S_B(𝒳_B) ≤ 2σ(G)`, the
  at-most-twice counting of `def:typeB-residual-mass`;
* `typeBFanMassSublinear` and `fanResidualMass_le_sixteen_globalSurplus` --
  `prop:typeB-bridge-sublinear`, `M_B(𝒳_B) ≤ 8 S_B(𝒳_B) ≤ 16 σ(G)`.

## Nothing is redefined and nothing is hypothesised

The support `Residual`, the ledger, `No_-`, `σ(X)`, `σ(G)`, the fan envelopes,
the canonical support `canonicalResidual` and the canonical decomposition
`bridgeResiduals` are `Hypostructure.Graph.TypeBBridgeResidual`; the
disjoint-carrier clause `DisjointCarriers` and its failure `SharedCarrier` are
`Hypostructure.Graph.TypeBExclusion`; `IsFanCertificateResidual`,
`neighbourRim` and the fan certificate are
`Hypostructure.Graph.TypeBMarkedFan`; `canonicalEnvelope` and
`isFanCertificateResidual_iff` are
`Hypostructure.Graph.TypeBProfileSchedule`; the closed-neighbour count `c(𝔉_h)`
that `Residual.closedFanCount` reproduces
(`TypeBBridgeResidual.closedCount_eq_closedFanCount`) and its deficit
`closedNeighbourDeficit` are `Hypostructure.Graph.TypeBFanClosedPorts`.

The manuscript's "the non-window core left after deleting the Type B fan
envelopes contains no admissible route-8 Type A residual profile" is not a
hypothesis here either: as in `TypeBBridgeResidual`, the post-ledger core charge
`Residual.residualCoreCharge` appears as an explicit term of the conclusion,
exactly as `lem:typeB-bridge-with-route8-core` carries `-D_A(𝒜_X)`.  The only
ambient structural input is `TypeBOpenPorts.NormalForm`, supplied as an explicit
argument exactly as in `TypeBBridgeResidual.negativePart_le_eight_surplus`.

All rational quantities are over `ℚ`, consistent with
`TypeBFanClosedPorts.Profile.closedNeighbourDeficit`.

## The discharge rate is read, never written

The per-vertex discharge rate `α` is a *chosen* proof-design parameter, so it is
not a literal here: every mass, allowance and charge below reads
`ReceiverLoad.LoadCapacityProfile.dischargeRate`, that is `1/loadMultiplier`
from the registered presentation, exactly as `TypeBBridgeResidual` does.  At the
registered `loadMultiplier = 4` every statement is verbatim the manuscript's,
and the only property of the rate any proof in this file uses is
`dischargeRate_le_one` (`α ≤ 1`) together with `dischargeRate_nonneg`, both of
which hold for every profile.
-/

namespace Hypostructure.Graph.TypeBFanMass

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBBridgeResidual
open Hypostructure.Graph.TypeBExclusion
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)
open Hypostructure.Graph.TypeBProfileSchedule (canonicalEnvelope
  mem_canonicalEnvelope_iff isFanCertificateResidual_iff)

universe u

variable {object : FiniteObject.{u}}

/-! ## Display (1) of `lem:typeB-bridge-deficit-bound`, as rational arithmetic

The manuscript's local calculation at a centre of degree `k` with `c ≤ k`
cubic-closed fan neighbours is

`(k - 3 + α) + cα ≤ (k - 3 + α) + kα = (k - 3) + (1 + k)α ≤ 8(k - 3)`,

with the per-vertex discharge rate `α` read from the registered presentation
(`ReceiverLoad.LoadCapacityProfile.dischargeRate`) rather than written as a
literal.  At the registered `loadMultiplier = 4`, i.e. `α = 1/4`, the middle
term is the manuscript's `(5/4)k - 11/4` and the last inequality is the
manuscript's, "the last inequality being equivalent to `27k ≥ 85`, and holding
for every `k ≥ 4`": clearing the denominator in `(1 + k)/4 ≤ 7(k - 3)` gives
`1 + k ≤ 28k - 84`, that is `27k ≥ 85`.

Both the equivalence and the range are recorded here, over `ℚ` and free of any
graph data, so that the arithmetic can be inspected on its own.  The only
property of the rate used is `α ≤ 1`
(`ReceiverLoad.LoadCapacityProfile.dischargeRate_le_one`, which holds for every
profile) together with `0 ≤ α`, exactly as in
`TypeBBridgeResidual.sharp_le_eight_surplus`. -/

/-- The last step of display (1) *is* the fan-credit clause `(1 + k)α ≤ 7(k-3)`:
the manuscript's parenthetical is an equivalence, not an implication.  At
`α = 1/4` clearing the denominator turns the right-hand side into
`1 + k ≤ 28k - 84`, i.e. the manuscript's `27k ≥ 85`. -/
theorem sharp_le_eight_surplus_iff_rat (rate k : ℚ) :
    (k - 3) + (1 + k) * rate ≤ 8 * (k - 3) ↔ (1 + k) * rate ≤ 7 * (k - 3) := by
  constructor <;> intro step <;> linarith

/-- The fan-credit clause holds for every `k ≥ 4` as soon as a vertex is
discharged by at most one whole unit: `α ≤ 1` reduces it to `1 + k ≤ 7(k - 3)`,
i.e. `6k ≥ 22`, with room to spare.  At `α = 1/4` this is the manuscript's
`27k ≥ 85`, with room `27 * 4 - 85 = 23`. -/
theorem sharp_clause_of_dischargeRate_le_one {rate k : ℚ} (le_one : rate ≤ 1)
    (high : 4 ≤ k) : (1 + k) * rate ≤ 7 * (k - 3) := by
  have bound : (1 + k) * rate ≤ (1 + k) * 1 :=
    mul_le_mul_of_nonneg_left le_one (by linarith)
  rw [mul_one] at bound
  linarith

/-- **The per-centre arithmetic of `lem:typeB-bridge-deficit-bound`:**
`(k - 3) + (1 + k)α ≤ 8(k - 3)` for every `k ≥ 4` and every rate `α ≤ 1`,
through the fan-credit clause.  At `α = 1/4` this is the manuscript's
`(5/4)k - 11/4 ≤ 8(k - 3)`. -/
theorem sharp_le_eight_surplus_rat {rate k : ℚ} (le_one : rate ≤ 1) (high : 4 ≤ k) :
    (k - 3) + (1 + k) * rate ≤ 8 * (k - 3) :=
  (sharp_le_eight_surplus_iff_rat rate k).2
    (sharp_clause_of_dischargeRate_le_one le_one high)

/-- The first step of display (1): `c ≤ k` turns the envelope allowance into the
sharp value `(k - 3) + (1 + k)α`, the manuscript's `(5/4)k - 11/4` at
`α = 1/4`. -/
theorem allowance_le_sharp_rat {rate k c : ℚ} (nonneg : 0 ≤ rate) (cap : c ≤ k) :
    (k - 3 + rate) + c * rate ≤ (k - 3) + (1 + k) * rate := by
  have step : c * rate ≤ k * rate := mul_le_mul_of_nonneg_right cap nonneg
  linarith

/-- **Display (1) of `lem:typeB-bridge-deficit-bound`, over `ℚ`:**
`(k - 3 + α) + cα ≤ (k - 3) + (1 + k)α ≤ 8(k - 3)` whenever `4 ≤ k`,
`c ≤ k` and `0 ≤ α ≤ 1`. -/
theorem allowance_le_eight_surplus_rat {rate k c : ℚ} (nonneg : 0 ≤ rate)
    (le_one : rate ≤ 1) (high : 4 ≤ k) (cap : c ≤ k) :
    (k - 3 + rate) + c * rate ≤ 8 * (k - 3) :=
  le_trans (allowance_le_sharp_rat nonneg cap) (sharp_le_eight_surplus_rat le_one high)

/-- The slack in display (1) still covers the per-centre discharge unit that the
identity `(B-ledger)` returns, which is what turns the deficit bound into the
manuscript's displayed refinement `No(X) ≥ -8 Σ (d_G(h)-3) + α|H_X|`.  Over `ℚ`
the clause is `(2 + k)α ≤ 7(k - 3)`, which at `α ≤ 1` reduces to `6k ≥ 23`; at
`α = 1/4` it is the manuscript's `27k ≥ 88`. -/
theorem sharp_add_dischargeRate_le_eight_surplus_rat {rate k : ℚ} (le_one : rate ≤ 1)
    (high : 4 ≤ k) :
    (k - 3) + (1 + k) * rate + rate ≤ 8 * (k - 3) := by
  have expand : (k - 3) + (1 + k) * rate + rate = (k - 3) + (2 + k) * rate := by ring
  have bound : (2 + k) * rate ≤ (2 + k) * 1 :=
    mul_le_mul_of_nonneg_left le_one (by linarith)
  rw [mul_one] at bound
  rw [expand]
  linarith

/-! ## The fan envelope of a centre, ambiently

`Residual.envelopeBlock h` is the fan envelope `E_h` *inside* one assigned
support: the centre together with its fan neighbours that the support counts.
The ambient version below forgets the support, so it contains every
support-relative one; that is exactly the direction needed to see that no
carrier overlap can escape the charge set. -/

/-- The ambient fan envelope `E_h` of `lem:typeB-bridge-deficit-bound`: the
centre together with its fan neighbours. -/
def fanEnvelope (object : FiniteObject.{u}) (hub : object.Vertex) :
    Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  insert hub (neighbourRim object hub)

@[simp] theorem mem_fanEnvelope_iff (object : FiniteObject.{u})
    (hub vertex : object.Vertex) :
    vertex ∈ fanEnvelope object hub ↔ vertex = hub ∨ object.graph.Adj hub vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [fanEnvelope]

theorem hub_mem_fanEnvelope (object : FiniteObject.{u}) (hub : object.Vertex) :
    hub ∈ fanEnvelope object hub :=
  (mem_fanEnvelope_iff object hub hub).2 (Or.inl rfl)

/-- Every carrier of a support-relative fan envelope is an ambient one. -/
theorem envelopeBlock_subset_fanEnvelope (residual : Residual object)
    (hub : object.Vertex) :
    residual.envelopeBlock hub ⊆ fanEnvelope object hub := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro vertex member
  simp only [Residual.envelopeBlock, Finset.mem_insert, Finset.mem_inter] at member
  rcases member with rfl | ⟨rim, _⟩
  · exact hub_mem_fanEnvelope object vertex
  · exact (mem_fanEnvelope_iff object hub vertex).2
      (Or.inr ((mem_neighbourRim object hub vertex).1 rim))

/-- The ambient fan envelope is carried by the canonical assigned support at the
centre, so the canonical support is a legitimate home for every carrier the
overlap condition below mentions. -/
theorem fanEnvelope_subset_canonicalEnvelope (object : FiniteObject.{u})
    (hub : object.Vertex) :
    fanEnvelope object hub ⊆ canonicalEnvelope object hub := by
  intro vertex member
  rcases (mem_fanEnvelope_iff object hub vertex).1 member with rfl | adjacent
  · exact (mem_canonicalEnvelope_iff vertex vertex).2 (Or.inl rfl)
  · exact (mem_canonicalEnvelope_iff hub vertex).2 (Or.inr (Or.inl adjacent))

/-! ## The charge set: fan-certificate residual centres and B2 failures -/

/-- The high-degree centres, other than `h`, whose ambient fan envelope shares a
carrier with the ambient fan envelope at `h`.  A nonempty set of partners is
precisely the local shape of the disjoint-carrier failure
`TypeBExclusion.SharedCarrier`. -/
def overlapPartners (object : FiniteObject.{u}) (hub : object.Vertex) :
    Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  object.vertexFinset.filter fun other =>
    4 ≤ object.degree other ∧ other ≠ hub ∧
      (fanEnvelope object hub ∩ fanEnvelope object other).Nonempty

theorem mem_overlapPartners_iff {hub other : object.Vertex} :
    other ∈ overlapPartners object hub ↔
      4 ≤ object.degree other ∧ other ≠ hub ∧
        ∃ carrier : object.Vertex,
          carrier ∈ fanEnvelope object hub ∧ carrier ∈ fanEnvelope object other := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp only [overlapPartners, Finset.mem_filter, object.mem_vertexFinset, true_and,
    Finset.Nonempty, Finset.mem_inter]

/-- **Clause (ii) of `def:typeB-bridge-statements`, localised at a centre.**  A
high-degree centre is a *B2 failure* when the carriers of its fan envelope are
not private to it: another high-degree centre's fan envelope meets it.  This is
the manuscript's failure of the disjoint-carrier part of B2, read at the centre
that is charged for it.

`sharedCarrier_overlapSupport` produces the support in which the failure is
literally `TypeBExclusion.SharedCarrier`, and
`exists_isB2Failure_of_sharedCarrier` shows conversely that every support
witnessing `SharedCarrier` has one of its assigned centres in this set. -/
def IsB2Failure (object : FiniteObject.{u}) (hub : object.Vertex) : Prop :=
  4 ≤ object.degree hub ∧ (overlapPartners object hub).Nonempty

instance decidableIsB2Failure (object : FiniteObject.{u}) (hub : object.Vertex) :
    Decidable (IsB2Failure object hub) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isB2Failure_iff {hub : object.Vertex} :
    IsB2Failure object hub ↔
      4 ≤ object.degree hub ∧
        ∃ other : object.Vertex, 4 ≤ object.degree other ∧ other ≠ hub ∧
          ∃ carrier : object.Vertex,
            carrier ∈ fanEnvelope object hub ∧ carrier ∈ fanEnvelope object other := by
  unfold IsB2Failure
  constructor
  · rintro ⟨high, other, member⟩
    exact ⟨high, other, mem_overlapPartners_iff.1 member⟩
  · rintro ⟨high, other, data⟩
    exact ⟨high, other, mem_overlapPartners_iff.2 data⟩

theorem high_of_isB2Failure {hub : object.Vertex} (failure : IsB2Failure object hub) :
    4 ≤ object.degree hub := failure.1

/-- **The charge set of node `[75]`.**  A high-degree centre is charged for
Type B bridge residual mass exactly when it is a fan-certificate residual centre
(clause (i) of `def:typeB-bridge-statements`) or a B2 failure (clause (ii)).

This is *not* the set of all heavy centres: a heavy centre carrying a fan
certificate whose envelope carriers are private to it is charged nothing.
`Witness.chargedCentres_witness` exhibits exactly such a centre. -/
def IsChargedCentre (object : FiniteObject.{u}) (hub : object.Vertex) : Prop :=
  IsFanCertificateResidual object hub ∨ IsB2Failure object hub

theorem high_of_isChargedCentre {hub : object.Vertex}
    (charged : IsChargedCentre object hub) : 4 ≤ object.degree hub := by
  rcases charged with residual | failure
  · exact residual.1
  · exact failure.1

/-- The charge set is decided by two local observables: `9 ≤ d_G(h)` for the
fan-certificate residual clause (`isFanCertificateResidual_iff`), and a nonempty
overlap-partner set for the B2 clause. -/
theorem isChargedCentre_iff (object : FiniteObject.{u}) (hub : object.Vertex) :
    IsChargedCentre object hub ↔
      9 ≤ object.degree hub ∨ IsB2Failure object hub := by
  unfold IsChargedCentre
  rw [isFanCertificateResidual_iff object hub]

/-- The charge set, enumerated in the object's own vertex scan order: the
vertices carrying ambient surplus that are fan-certificate residual centres or
B2 failures. -/
def chargedCentres (object : FiniteObject.{u}) : List object.Vertex :=
  (bridgeCentres object).filter fun hub =>
    decide (9 ≤ object.degree hub) || decide (IsB2Failure object hub)

@[simp] theorem mem_chargedCentres_iff (object : FiniteObject.{u})
    (hub : object.Vertex) :
    hub ∈ chargedCentres object ↔ IsChargedCentre object hub := by
  rw [chargedCentres, List.mem_filter, mem_bridgeCentres_iff, isChargedCentre_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨_, clause⟩
    exact clause
  · rintro (nine | failure)
    · exact ⟨by omega, Or.inl nine⟩
    · exact ⟨failure.1, Or.inr failure⟩

/-- **The charge set is a subcollection of the canonical decomposition.**  This
is `def:typeB-residual-mass`'s "let `𝒳_B` be a subcollection of the canonical
admissible supports which are Type B bridge residuals". -/
theorem chargedCentres_sublist_bridgeCentres (object : FiniteObject.{u}) :
    (chargedCentres object).Sublist (bridgeCentres object) :=
  List.filter_sublist

theorem chargedCentres_subset_bridgeCentres (object : FiniteObject.{u}) :
    ∀ hub ∈ chargedCentres object, hub ∈ bridgeCentres object :=
  fun _ member => (chargedCentres_sublist_bridgeCentres object).mem member

theorem chargedCentres_nodup (object : FiniteObject.{u}) :
    (chargedCentres object).Nodup :=
  (chargedCentres_sublist_bridgeCentres object).nodup (bridgeCentres_nodup object)

/-! ## The charge set really is the manuscript's B2 failure

Clause (ii) of `def:typeB-bridge-statements` is a statement about a *support*:
two distinct assigned fan centres share a carrier.  The two theorems below tie
the local charge condition to that support-level statement in both directions,
so the charge set is neither too small (nothing escapes) nor vacuous (the
condition is realised by an object-derived support). -/

/-- The object-derived support that assigns an overlapping pair of high-degree
centres: the union of their canonical assigned fan envelopes, with both centres
recorded.  This is the minimal support in which clause (ii) can be read, and it
is built from the object's own schedules -- nothing is chosen. -/
def overlapSupport (object : FiniteObject.{u}) (hub other : object.Vertex) :
    Residual object :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  { core := canonicalEnvelope object hub ∪ canonicalEnvelope object other
    recordedCentres := {hub, other} }

theorem hub_mem_overlapSupport_core (object : FiniteObject.{u})
    (hub other : object.Vertex) : hub ∈ (overlapSupport object hub other).core := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.mem_union_left _ ((mem_canonicalEnvelope_iff hub hub).2 (Or.inl rfl))

theorem other_mem_overlapSupport_core (object : FiniteObject.{u})
    (hub other : object.Vertex) : other ∈ (overlapSupport object hub other).core := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.mem_union_right _ ((mem_canonicalEnvelope_iff other other).2 (Or.inl rfl))

/-- Both centres of the overlap support are assigned to it: `H_X = {h, h'}`.
The containment `H_X ⊆ Y_X` of `def:typeB-assigned-ledger` is a construction
here, because the core is the union of the two canonical assigned envelopes. -/
theorem hub_mem_centers_overlapSupport (object : FiniteObject.{u})
    (hub other : object.Vertex) :
    hub ∈ (overlapSupport object hub other).centers := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.mem_inter.2
    ⟨Finset.mem_insert_self _ _, hub_mem_overlapSupport_core object hub other⟩

theorem other_mem_centers_overlapSupport (object : FiniteObject.{u})
    (hub other : object.Vertex) :
    other ∈ (overlapSupport object hub other).centers := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.mem_inter.2
    ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      other_mem_overlapSupport_core object hub other⟩

/-- **A B2 failure is a `SharedCarrier`.**  If the ambient fan envelopes of two
distinct high-degree centres share a carrier, then the object-derived support
that assigns both of them exhibits the disjoint-carrier failure of
`def:typeB-bridge-statements` (ii), in the exact form
`TypeBExclusion.SharedCarrier`.  There is no hypothesis: the support is built so
that it carries both fans. -/
theorem sharedCarrier_overlapSupport {hub other carrier : object.Vertex}
    (distinct : hub ≠ other) (leftMem : carrier ∈ fanEnvelope object hub)
    (rightMem : carrier ∈ fanEnvelope object other) :
    SharedCarrier (overlapSupport object hub other) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have hubMem : hub ∈ (overlapSupport object hub other).centers :=
    hub_mem_centers_overlapSupport object hub other
  have otherMem : other ∈ (overlapSupport object hub other).centers :=
    other_mem_centers_overlapSupport object hub other
  have leftBlock : carrier ∈ (overlapSupport object hub other).envelopeBlock hub := by
    rcases (mem_fanEnvelope_iff object hub carrier).1 leftMem with rfl | adjacent
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_inter.2
        ⟨(mem_neighbourRim object hub carrier).2 adjacent, ?_⟩)
      exact Finset.mem_union_left _
        (fanEnvelope_subset_canonicalEnvelope object hub leftMem)
  have rightBlock : carrier ∈ (overlapSupport object hub other).envelopeBlock other := by
    rcases (mem_fanEnvelope_iff object other carrier).1 rightMem with rfl | adjacent
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_inter.2
        ⟨(mem_neighbourRim object other carrier).2 adjacent, ?_⟩)
      exact Finset.mem_union_right _
        (fanEnvelope_subset_canonicalEnvelope object other rightMem)
  exact ⟨hub, hubMem, other, otherMem, distinct, carrier, leftBlock, rightBlock⟩

theorem exists_sharedCarrier_of_isB2Failure {hub : object.Vertex}
    (failure : IsB2Failure object hub) :
    ∃ other : object.Vertex, hub ≠ other ∧
      SharedCarrier (overlapSupport object hub other) := by
  obtain ⟨_, other, high, distinct, carrier, leftMem, rightMem⟩ := isB2Failure_iff.1 failure
  exact ⟨other, fun equal => distinct equal.symm,
    sharedCarrier_overlapSupport (fun equal => distinct equal.symm) leftMem rightMem⟩

/-- **No B2 failure escapes the charge set.**  Every assigned Type B support
whose fan entries fail the disjoint-carrier clause has one of its assigned
centres in the charge set.  The high-degree condition is the defining property
of `H_X` in `def:typeB-residual-mass` ("`h` is a high-degree Type B fan center
assigned to `X`"), and for the object's own collection it is the theorem
`TypeBBridgeResidual.high_of_mem_centers`. -/
theorem exists_isB2Failure_of_sharedCarrier (residual : Residual object)
    (high : ∀ h ∈ residual.centers, 4 ≤ object.degree h)
    (shared : SharedCarrier residual) :
    ∃ h ∈ residual.centers, IsB2Failure object h := by
  obtain ⟨h, hMem, other, otherMem, distinct, carrier, leftMem, rightMem⟩ := shared
  refine ⟨h, hMem, isB2Failure_iff.2 ⟨high h hMem, other, high other otherMem,
    fun equal => distinct equal.symm, carrier, ?_, ?_⟩⟩
  · exact envelopeBlock_subset_fanEnvelope residual h leftMem
  · exact envelopeBlock_subset_fanEnvelope residual other rightMem

/-- **A Type B bridge residual** in the sense of `def:typeB-bridge-statements`,
clauses (i) and (ii): an assigned Type B support containing a fan-certificate
residual centre, or one whose fan entries fail the disjoint-carrier clause of
B2.  This is a predicate on the existing `Residual`; no new carrier. -/
def IsBridgeResidual (residual : Residual object) : Prop :=
  (∃ h ∈ residual.centers, IsFanCertificateResidual object h) ∨ SharedCarrier residual

/-- **The charge set is complete.**  Every Type B bridge residual has an
assigned centre in the charge set, so no bridge residual is left unpaid by the
fan-mass accounting. -/
theorem exists_isChargedCentre_of_isBridgeResidual (residual : Residual object)
    (high : ∀ h ∈ residual.centers, 4 ≤ object.degree h)
    (bridge : IsBridgeResidual residual) :
    ∃ h ∈ residual.centers, IsChargedCentre object h := by
  rcases bridge with ⟨h, hMem, certificate⟩ | shared
  · exact ⟨h, hMem, Or.inl certificate⟩
  · obtain ⟨h, hMem, failure⟩ := exists_isB2Failure_of_sharedCarrier residual high shared
    exact ⟨h, hMem, Or.inr failure⟩

/-- The same statement for the object's own canonical decomposition, with the
high-degree condition discharged by `TypeBBridgeResidual.high_of_mem_centers`:
no hypothesis at all. -/
theorem exists_isChargedCentre_of_mem_bridgeResiduals {residual : Residual object}
    (member : residual ∈ bridgeResiduals object) (bridge : IsBridgeResidual residual) :
    ∃ h ∈ residual.centers, IsChargedCentre object h :=
  exists_isChargedCentre_of_isBridgeResidual residual
    (fun _ centreMem => high_of_mem_centers member centreMem) bridge

/-! ## `def:typeB-residual-mass`: the collection `𝒳_B` and its three quantities -/

/-- **The collection `𝒳_B` of `def:typeB-residual-mass`:** the canonical
assigned supports at the charged centres.  Each member is the framework's
canonical support `TypeBBridgeResidual.canonicalResidual`, so this really is a
subcollection of the canonical decomposition
(`fanMassResiduals_sublist_bridgeResiduals`) rather than a second carrier. -/
def fanMassResiduals (object : FiniteObject.{u}) : List (Residual object) :=
  (chargedCentres object).map (canonicalResidual object)

theorem fanMassResiduals_sublist_bridgeResiduals (object : FiniteObject.{u}) :
    (fanMassResiduals object).Sublist (bridgeResiduals object) :=
  List.Sublist.map _ (chargedCentres_sublist_bridgeCentres object)

theorem mem_bridgeResiduals_of_mem_fanMassResiduals {residual : Residual object}
    (member : residual ∈ fanMassResiduals object) :
    residual ∈ bridgeResiduals object :=
  (fanMassResiduals_sublist_bridgeResiduals object).mem member

theorem mem_fanMassResiduals_iff (object : FiniteObject.{u})
    (residual : Residual object) :
    residual ∈ fanMassResiduals object ↔
      ∃ center : object.Vertex, IsChargedCentre object center ∧
        residual = canonicalResidual object center := by
  rw [fanMassResiduals, List.mem_map]
  constructor
  · rintro ⟨center, member, rfl⟩
    exact ⟨center, (mem_chargedCentres_iff object center).1 member, rfl⟩
  · rintro ⟨center, charged, rfl⟩
    exact ⟨center, (mem_chargedCentres_iff object center).2 charged, rfl⟩

theorem fanMassResiduals_nodup (object : FiniteObject.{u}) :
    (fanMassResiduals object).Nodup :=
  (chargedCentres_nodup object).map (canonicalResidual_injective object)

/-- Every assigned centre of an enumerated member is a charged centre: the
collection charges nothing else. -/
theorem isChargedCentre_of_mem_centers {residual : Residual object}
    (member : residual ∈ fanMassResiduals object) {h : object.Vertex}
    (centreMem : h ∈ residual.centers) : IsChargedCentre object h := by
  obtain ⟨center, charged, rfl⟩ := (mem_fanMassResiduals_iff object residual).1 member
  rw [centers_canonicalResidual, Finset.mem_singleton] at centreMem
  subst centreMem
  exact charged

theorem high_of_mem_centers_fanMass {residual : Residual object}
    (member : residual ∈ fanMassResiduals object) {h : object.Vertex}
    (centreMem : h ∈ residual.centers) : 4 ≤ object.degree h :=
  high_of_isChargedCentre (isChargedCentre_of_mem_centers member centreMem)

/-- `M_B(𝒳_B) = Σ_{X ∈ 𝒳_B} No_-(X)`, the Type B residual fan mass. -/
noncomputable def fanResidualMass (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) : ℚ :=
  ((fanMassResiduals object).map fun member => member.negativePart profile).sum

/-- `S_B(𝒳_B) = Σ_{X ∈ 𝒳_B} Σ_{h ∈ H_X} s_X(h)` with `s_X(h) = d_G(h) - 3`. -/
noncomputable def fanSurplusMass (object : FiniteObject.{u}) : ℚ :=
  ((fanMassResiduals object).map Residual.surplus).sum

/-- `H_B(𝒳_B) = ⨆_{X ∈ 𝒳_B} H_X`, the tagged union of centre occurrences. -/
noncomputable def fanCenterOccurrences (object : FiniteObject.{u}) :
    List object.Vertex :=
  (fanMassResiduals object).flatMap fun member => member.centers.toList

/-- The undischarged remainder of the collection: the part of each post-ledger
core charge the Type A discharge has not yet paid.  It is carried as an explicit
term exactly as `lem:typeB-bridge-with-route8-core` carries `-D_A(𝒜_X)`, so no
statement below assumes the route-8 core away. -/
noncomputable def fanUndischargedMass (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) : ℚ :=
  ((fanMassResiduals object).map fun member =>
    max 0 (-member.residualCoreCharge profile)).sum

theorem fanResidualMass_nonneg (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) :
    0 ≤ fanResidualMass object profile := by
  unfold fanResidualMass
  refine List.sum_nonneg ?_
  intro x member
  obtain ⟨residual, _, rfl⟩ := List.mem_map.1 member
  exact Residual.negativePart_nonneg residual profile

/-- The tagged union of assigned centres is exactly the charge set: nothing is
double-counted and nothing is dropped. -/
theorem fanCenterOccurrences_eq_chargedCentres (object : FiniteObject.{u}) :
    fanCenterOccurrences object = chargedCentres object := by
  unfold fanCenterOccurrences fanMassResiduals
  induction chargedCentres object with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, List.flatMap_cons, ih, centers_canonicalResidual,
        Finset.toList_singleton, List.singleton_append]

/-- A charged vertex occurs *at most once* in `H_B(𝒳_B)`: the enumeration walks
the object's vertex schedule once. -/
theorem count_fanCenterOccurrences_le_one (object : FiniteObject.{u})
    (v : object.Vertex) :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    (fanCenterOccurrences object).count v ≤ 1 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [fanCenterOccurrences_eq_chargedCentres]
  exact List.nodup_iff_count_le_one.1 (chargedCentres_nodup object) v

/-- **The at-most-twice convention of `def:typeB-residual-mass`, verbatim.**  The
manuscript allows a centre to occur once in the ordinary role and once in the
grouped-envelope role; the derived charge set needs neither, so the convention
holds with the factor two unused. -/
theorem count_fanCenterOccurrences_le_two (object : FiniteObject.{u})
    (v : object.Vertex) :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    (fanCenterOccurrences object).count v ≤ 2 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact le_trans (count_fanCenterOccurrences_le_one object v) (by norm_num)

/-! ### List arithmetic for a subcollection -/

/-- A sublist of a list of nonnegative weights has the smaller sum.  This is the
only extra list fact a *subcollection* needs over the full decomposition. -/
theorem sublist_sum_map_le {α : Type*} {f : α → ℚ} :
    ∀ {sub big : List α}, sub.Sublist big → (∀ x ∈ big, 0 ≤ f x) →
      (sub.map f).sum ≤ (big.map f).sum := by
  intro sub big sublist
  induction sublist with
  | slnil => intro _; simp
  | cons head _ ih =>
      intro nonneg
      have tail := ih fun x member => nonneg x (List.mem_cons_of_mem head member)
      have headNonneg := nonneg head (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons]
      linarith
  | cons_cons head _ ih =>
      intro nonneg
      have tail := ih fun x member => nonneg x (List.mem_cons_of_mem head member)
      simp only [List.map_cons, List.sum_cons]
      linarith

/-! ### `S_B(𝒳_B) ≤ 2 σ(G)` -/

theorem fanSurplusMass_eq_sum_chargedCentres (object : FiniteObject.{u}) :
    fanSurplusMass object
      = ((chargedCentres object).map fun h => (object.degree h : ℚ) - 3).sum := by
  unfold fanSurplusMass fanMassResiduals
  rw [List.map_map]
  exact congrArg List.sum
    (List.map_congr_left fun h _ => surplus_canonicalResidual object h)

theorem fanSurplusMass_nonneg (object : FiniteObject.{u}) :
    0 ≤ fanSurplusMass object := by
  rw [fanSurplusMass_eq_sum_chargedCentres]
  refine List.sum_nonneg ?_
  intro x member
  obtain ⟨h, centreMem, rfl⟩ := List.mem_map.1 member
  have high : (4 : ℚ) ≤ (object.degree h : ℚ) := by
    exact_mod_cast high_of_isChargedCentre ((mem_chargedCentres_iff object h).1 centreMem)
  linarith

/-- **The charge set spends only the surplus of the centres it charges.**  The
manuscript's `S_B(𝒳_B)` is bounded by the object's total positive surplus,
because the charged centres are a subcollection of the vertices carrying ambient
surplus and each is charged once. -/
theorem fanSurplusMass_le_globalSurplusPos (object : FiniteObject.{u}) :
    fanSurplusMass object ≤ globalSurplusPos object := by
  rw [fanSurplusMass_eq_sum_chargedCentres, ← surplusMass_eq_globalSurplusPos,
    surplusMass_eq_sum_bridgeCentres]
  refine sublist_sum_map_le (chargedCentres_sublist_bridgeCentres object) ?_
  intro h member
  have high : (4 : ℚ) ≤ (object.degree h : ℚ) := by
    exact_mod_cast (mem_bridgeCentres_iff object h).1 member
  linarith

/-- **`S_B(𝒳_B) ≤ 2 σ(G)`** of `def:typeB-residual-mass`: each surplus unit is
counted at most twice, once in the ordinary role and once in the
grouped-envelope role.  The derived charge set counts it at most once
(`count_fanCenterOccurrences_le_one`), so the manuscript's factor two is
available and unused. -/
theorem fanSurplusMass_le_two_globalSurplusPos (object : FiniteObject.{u}) :
    fanSurplusMass object ≤ 2 * globalSurplusPos object := by
  have bound := fanSurplusMass_le_globalSurplusPos object
  have nonneg : (0 : ℚ) ≤ globalSurplusPos object := globalSurplusPos_nonneg
  linarith

/-- The same statement against the manuscript's `σ(G) = Σ_v (d_G(v) - 3)`, on
the standing branch where the minimum degree is at least three. -/
theorem fanSurplusMass_le_two_globalSurplus (object : FiniteObject.{u})
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v) :
    fanSurplusMass object ≤ 2 * globalSurplus object := by
  have bound := fanSurplusMass_le_two_globalSurplusPos object
  rwa [globalSurplusPos_eq_globalSurplus minDegree] at bound

/-! ## `lem:typeB-bridge-deficit-bound` on the charge set -/

/-- **`lem:typeB-bridge-deficit-bound`.**  Once the core left after the fan
envelopes are removed carries nonnegative charge, the whole negative part of a
Type B bridge residual is charged to eight times the surplus of its assigned
centres:

`No_-(X) ≤ 8 Σ_{h ∈ H_X} (d_G(h) - 3)`.

The estimate is display (1) summed over `H_X`; the arithmetic step is
`sharp_le_eight_surplus_rat`, i.e. `27k ≥ 85`.

This is also **`lem:decorated-envelope-deficit-bound`**, clause (iii) of
`def:typeB-bridge-statements`.  That lemma asserts the same inequality for a
grouped decorated Type B envelope support `X = 𝔛_𝔠*` with centre set `H_𝔠`, and
its proof says so: "the local calculation at a fixed center is the same as the
one used for an ordinary Type B bridge center".  A grouped envelope support is
a `Residual` whose assigned centre set is the incidence component `H_𝔠` -- for
instance `overlapSupport`, which groups two centres -- so the statement below,
which quantifies over every `Residual`, is that lemma verbatim.  What clause
(iii) adds is which supports enter `𝒳_B`, and that is a question about the
collection, answered by `chargedCentres` above. -/
theorem negativePart_le_eight_surplus_of_discharged (residual : Residual object)
    (profile : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (discharged : 0 ≤ residual.residualCoreCharge profile) :
    residual.negativePart profile
      ≤ 8 * ∑ h ∈ residual.centers, ((object.degree h : ℚ) - 3) := by
  have bound := residual.negativePart_le_eight_surplus profile normal
  have vanishes : max 0 (-residual.residualCoreCharge profile) = 0 :=
    max_eq_left (by linarith)
  rw [vanishes, add_zero] at bound
  exact bound

/-- **The displayed refinement of `lem:typeB-bridge-deficit-bound`:**
`No(X) ≥ -8 Σ_{h ∈ H_X}(d_G(h)-3) + α|H_X|`.  The per-centre discharge unit the
identity `(B-ledger)` returns still fits inside the slack of display (1), whose
clause over `ℚ` is `(2 + k)α ≤ 7(k - 3)`
(`sharp_add_dischargeRate_le_eight_surplus_rat`); at `α = 1/4` that is the
manuscript's `27k ≥ 88`. -/
theorem neg_eight_surplus_add_dischargeRate_card_le_netCharge
    (residual : Residual object) (profile : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (discharged : 0 ≤ residual.residualCoreCharge profile) :
    -(8 * residual.surplus) + (residual.centers.card : ℚ) * profile.dischargeRate
      ≤ residual.netCharge profile := by
  have envelope :=
    residual.residualCoreCharge_sub_sum_envelopeAllowance_le_netCharge profile normal
  have perCentre : ∀ h ∈ residual.centers,
      residual.envelopeAllowance profile h + profile.dischargeRate
        ≤ 8 * ((object.degree h : ℚ) - 3) := by
    intro h member
    have sharp := residual.envelopeAllowance_le_sharp profile h
    have high : (4 : ℚ) ≤ (object.degree h : ℚ) := by
      exact_mod_cast (normal h member).high
    have step := sharp_add_dischargeRate_le_eight_surplus_rat
      profile.dischargeRate_le_one high
    linarith
  have summed : ∑ h ∈ residual.centers,
        (residual.envelopeAllowance profile h + profile.dischargeRate)
      ≤ ∑ h ∈ residual.centers, 8 * ((object.degree h : ℚ) - 3) :=
    Finset.sum_le_sum perCentre
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at summed
  have surplusDef : ∑ h ∈ residual.centers, ((object.degree h : ℚ) - 3)
      = residual.surplus := rfl
  rw [surplusDef] at summed
  linarith

/-- The deficit bound in the form the collection uses, on an enumerated member:
the high-degree condition on `H_X` is the theorem
`high_of_mem_centers_fanMass`, so only the ambient normal form is supplied. -/
theorem negativePart_le_eight_surplus_of_mem {residual : Residual object}
    (_member : residual ∈ fanMassResiduals object) (profile : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h) :
    residual.negativePart profile
      ≤ 8 * residual.surplus + max 0 (-residual.residualCoreCharge profile) :=
  residual.negativePart_le_eight_surplus profile normal

/-- **Display (1) is attained on the charge set.**  At an assigned centre of an
enumerated member, `c_h = d_G(h)`, so the first inequality of display (1) is an
*equality* and the whole per-centre estimate rests on the arithmetic step
`(k - 3) + (1 + k)α ≤ 8(k-3)`, i.e. the fan-credit clause
`(1 + k)α ≤ 7(k - 3)`, which at `α = 1/4` is the manuscript's `27k ≥ 85`.  The
deficit bound is therefore not obtained through a slack the carrier could never
realise. -/
theorem envelopeAllowance_sharp_of_mem {residual : Residual object}
    (member : residual ∈ fanMassResiduals object) (profile : LoadCapacityProfile)
    {h : object.Vertex} (centreMem : h ∈ residual.centers) :
    residual.envelopeAllowance profile h
        = ((object.degree h : ℚ) - 3)
          + (1 + (object.degree h : ℚ)) * profile.dischargeRate ∧
      residual.envelopeAllowance profile h ≤ 8 * ((object.degree h : ℚ) - 3) := by
  obtain ⟨center, charged, rfl⟩ := (mem_fanMassResiduals_iff object residual).1 member
  rw [centers_canonicalResidual, Finset.mem_singleton] at centreMem
  subst centreMem
  refine ⟨envelopeAllowance_canonicalResidual object profile h, ?_⟩
  rw [envelopeAllowance_canonicalResidual object profile h]
  have high : (4 : ℚ) ≤ (object.degree h : ℚ) := by
    exact_mod_cast high_of_isChargedCentre charged
  exact sharp_le_eight_surplus_rat profile.dischargeRate_le_one high

/-! ## `prop:typeB-bridge-sublinear` on the charge set -/

theorem fanResidualMass_le_eight_fanSurplusMass (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (bounded : ∀ member ∈ fanMassResiduals object,
      member.negativePart profile
        ≤ 8 * member.surplus + max 0 (-member.residualCoreCharge profile)) :
    fanResidualMass object profile
      ≤ 8 * fanSurplusMass object + fanUndischargedMass object profile := by
  have step : ((fanMassResiduals object).map
        fun member => member.negativePart profile).sum
      ≤ ((fanMassResiduals object).map fun member =>
          8 * member.surplus + max 0 (-member.residualCoreCharge profile)).sum :=
    list_sum_map_le bounded
  have split : ((fanMassResiduals object).map fun member =>
        8 * member.surplus + max 0 (-member.residualCoreCharge profile)).sum
      = ((fanMassResiduals object).map fun member => 8 * member.surplus).sum
        + fanUndischargedMass object profile := by
    unfold fanUndischargedMass
    induction fanMassResiduals object with
    | nil => simp
    | cons head tail ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [split, list_sum_map_mul (fanMassResiduals object) 8 Residual.surplus] at step
  exact step

/-- **`prop:typeB-bridge-sublinear`, charged to the bridge-residual centres.**
For the object's own collection `𝒳_B` of Type B bridge residual supports -- the
canonical assigned supports at the fan-certificate residual centres and the B2
failures --

`M_B(𝒳_B) ≤ 8 S_B(𝒳_B) ≤ 16 σ(G)`,

up to the explicit undischarged remainder carried by the fan-envelope-free
cores.

The asymptotic tail `16 σ(G) = O(√n) = o(|R|)` is *not* an extra hypothesis.
`def:near-cubic-spine` records branch state, and that state is supplied by arm
(a) of the proved trichotomy `prop:nonnear-cubic-sharp-overload-routing`.  In
the authored DAG that arm is the at-or-below terminal of the node-`[19]`
`scaleThresholdDichotomy`, whose residual literally records
`σ(G) ≤ (audited √-table)(n)`; the whole Type B continuation is nested inside
that terminal, so the fact is in scope here.  It is therefore *consumed*, not
assumed, in `Graph.NearCubicSpine.fanResidualMass_le_sixteen_threshold`, which
combines this theorem with the branch fact through
`Graph.NearCubicSpine.globalSurplus_eq_degreeSurplus`.  What stays local -- and
what this statement keeps -- is the charge inequality itself: the bridge mass of
the charge set is bounded by a fixed multiple of the object's own global
surplus, using no branch fact at all. -/
theorem typeBFanMassSublinear (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (normal : ∀ member ∈ fanMassResiduals object, ∀ h ∈ member.centers,
      NormalForm object h) :
    fanResidualMass object profile
        ≤ 8 * fanSurplusMass object + fanUndischargedMass object profile ∧
      fanSurplusMass object ≤ 2 * globalSurplusPos object ∧
      fanResidualMass object profile
        ≤ 16 * globalSurplusPos object + fanUndischargedMass object profile := by
  have massBound := fanResidualMass_le_eight_fanSurplusMass object profile
    fun member mem => member.negativePart_le_eight_surplus profile (normal member mem)
  have surplusBound := fanSurplusMass_le_two_globalSurplusPos object
  exact ⟨massBound, surplusBound, by linarith⟩

/-- The same bound written against the manuscript's `σ(G) = Σ_v (d_G(v) - 3)`,
on the standing branch where the minimum degree is at least three. -/
theorem typeBFanMassSublinear_globalSurplus (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v)
    (normal : ∀ member ∈ fanMassResiduals object, ∀ h ∈ member.centers,
      NormalForm object h) :
    fanResidualMass object profile
        ≤ 8 * fanSurplusMass object + fanUndischargedMass object profile ∧
      fanSurplusMass object ≤ 2 * globalSurplus object ∧
      fanResidualMass object profile
        ≤ 16 * globalSurplus object + fanUndischargedMass object profile := by
  obtain ⟨massBound, surplusBound, total⟩ :=
    typeBFanMassSublinear object profile normal
  rw [globalSurplusPos_eq_globalSurplus minDegree] at surplusBound total
  exact ⟨massBound, surplusBound, total⟩

/-- **`prop:typeB-bridge-sublinear`, verbatim:** `M_B(𝒳_B) ≤ 16 σ(G)`, on the
branch where every fan-envelope-free core has been discharged -- the manuscript's
"whose non-window cores contain no admissible route-8 Type A residual profile",
here supplied positively as the nonnegativity of the post-ledger core charge. -/
theorem fanResidualMass_le_sixteen_globalSurplus (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v)
    (normal : ∀ member ∈ fanMassResiduals object, ∀ h ∈ member.centers,
      NormalForm object h)
    (discharged : ∀ member ∈ fanMassResiduals object,
      0 ≤ member.residualCoreCharge profile) :
    fanResidualMass object profile ≤ 16 * globalSurplus object := by
  have remainder : fanUndischargedMass object profile = 0 := by
    unfold fanUndischargedMass
    refine List.sum_eq_zero ?_
    intro x member
    obtain ⟨residual, residualMem, rfl⟩ := List.mem_map.1 member
    exact max_eq_left (by linarith [discharged residual residualMem])
  obtain ⟨_, _, total⟩ :=
    typeBFanMassSublinear_globalSurplus object profile minDegree normal
  rw [remainder, add_zero] at total
  exact total

/-! ## The charge set is strictly smaller than the heavy-centre set

The registration this file replaces charged *every* heavy centre.  On the
explicit finite graph already used by `TypeBFanClosedPorts`,
`TypeBBridgeResidual` and `TypeBExclusion` -- a degree-four centre whose four
neighbours are cubic with private shoulder pairs -- the heavy-centre set is
`[hub]`, whereas the charge set is **empty**: the centre is not a
fan-certificate residual centre (its degree is four, not at least nine) and it
is not a B2 failure (it is the only heavy centre, so no other fan envelope can
meet its own).  Consequently the fan mass of the charge set is `0` there, while
the heavy-centre accounting charges the hub's surplus. -/

namespace Witness

open Hypostructure.Graph.TypeBFanClosedPorts.Witness

local instance vertexDecEq : DecidableEq fanObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 13))

local instance vertexFintype : Fintype fanObject.Vertex :=
  inferInstanceAs (Fintype (Fin 13))

local instance adjDecidable : DecidableRel fanObject.graph.Adj := fanObject.decideAdj

/-- The heavy-centre set of the witness is the singleton `[hub]`: this is
`TypeBBridgeResidual.Witness.bridgeCentres_witness`. -/
theorem bridgeCentres_eq : bridgeCentres fanObject = [hub] :=
  Hypostructure.Graph.TypeBBridgeResidual.Witness.bridgeCentres_witness

/-- **The charge set of node `[75]` is empty on the witness**, while the
heavy-centre set is not.  The hub carries a genuine fan certificate and its
envelope carriers are private, so it is neither clause (i) nor clause (ii) of
`def:typeB-bridge-statements`. -/
theorem chargedCentres_witness : chargedCentres fanObject = [] := by decide

theorem not_isChargedCentre_hub : ¬ IsChargedCentre fanObject hub := by
  intro charged
  have member : hub ∈ chargedCentres fanObject :=
    (mem_chargedCentres_iff fanObject hub).2 charged
  rw [chargedCentres_witness] at member
  exact absurd member (List.not_mem_nil)

/-- The collection `𝒳_B` is empty on the witness, so the whole Type B bridge
residual fan mass it carries is zero: the charge set pays for nothing that the
local ledgers already close. -/
theorem fanMassResiduals_witness : fanMassResiduals fanObject = [] := by
  rw [fanMassResiduals, chargedCentres_witness, List.map_nil]

theorem fanResidualMass_witness (profile : LoadCapacityProfile) :
    fanResidualMass fanObject profile = 0 := by
  rw [fanResidualMass, fanMassResiduals_witness, List.map_nil, List.sum_nil]

theorem fanSurplusMass_witness : fanSurplusMass fanObject = 0 := by
  rw [fanSurplusMass, fanMassResiduals_witness, List.map_nil, List.sum_nil]

/-- The heavy-centre accounting, by contrast, charges one full surplus unit on
the same object: `TypeBBridgeResidual.Witness.surplusMass_eq`.  So the two
charge sets are genuinely different, not merely differently presented. -/
theorem surplusMass_witness_ne_fanSurplusMass :
    surplusMass fanObject ≠ fanSurplusMass fanObject := by
  rw [Hypostructure.Graph.TypeBBridgeResidual.Witness.surplusMass_eq,
    fanSurplusMass_witness]
  norm_num

end Witness

/-! ## The B2 clause is not vacuous

Two adjacent degree-four centres share their own two vertices as carriers of
their fan envelopes, so both are B2 failures and both are charged.  The support
that assigns them, `overlapSupport`, exhibits the disjoint-carrier failure of
`def:typeB-bridge-statements` (ii) as `TypeBExclusion.SharedCarrier`. -/

namespace B2Witness

/-- Generating relation of the B2 witness: adjacent centres `0` and `1`, with
`0` joined to `2, 3, 4` and `1` joined to `5, 6, 7`. -/
def rel (left right : Fin 8) : Prop :=
  (left.val = 0 ∧ 1 ≤ right.val ∧ right.val ≤ 4) ∨
    (left.val = 1 ∧ 5 ≤ right.val ∧ right.val ≤ 7)

instance decidableRel (left right : Fin 8) : Decidable (rel left right) := by
  unfold rel; infer_instance

/-- The B2 witness graph: two adjacent degree-four centres with private
pendant neighbours. -/
def pairObject : FiniteObject where
  Vertex := Fin 8
  graph := SimpleGraph.fromRel rel
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

local instance vertexDecEq : DecidableEq pairObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 8))

local instance vertexFintype : Fintype pairObject.Vertex :=
  inferInstanceAs (Fintype (Fin 8))

local instance adjDecidable : DecidableRel pairObject.graph.Adj := pairObject.decideAdj

/-- The first centre. -/
def leftCentre : pairObject.Vertex := (0 : Fin 8)

/-- The second centre. -/
def rightCentre : pairObject.Vertex := (1 : Fin 8)

theorem degree_left : pairObject.degree leftCentre = 4 := by decide

theorem degree_right : pairObject.degree rightCentre = 4 := by decide

theorem distinct : leftCentre ≠ rightCentre := by decide

/-- Both centres are heavy. -/
theorem bridgeCentres_eq : bridgeCentres pairObject = [leftCentre, rightCentre] := by
  decide

/-- Neither centre is a fan-certificate residual centre: both have degree four,
well below the label-packing cap. -/
theorem not_fanCertificateResidual_left :
    ¬ IsFanCertificateResidual pairObject leftCentre := by
  rw [isFanCertificateResidual_iff pairObject leftCentre, degree_left]
  omega

/-- **The B2 clause fires:** the left centre is a B2 failure. -/
theorem isB2Failure_left : IsB2Failure pairObject leftCentre := by decide

/-- **The B2 clause fires:** the right centre is a B2 failure. -/
theorem isB2Failure_right : IsB2Failure pairObject rightCentre := by decide

/-- Both centres are charged, and charged *only* through the B2 clause. -/
theorem chargedCentres_eq : chargedCentres pairObject = [leftCentre, rightCentre] := by
  decide

/-- The support that assigns the overlapping pair exhibits the disjoint-carrier
failure of `def:typeB-bridge-statements` (ii), in the exact form
`TypeBExclusion.SharedCarrier`. -/
theorem sharedCarrier_fires :
    SharedCarrier (overlapSupport pairObject leftCentre rightCentre) := by
  refine sharedCarrier_overlapSupport (carrier := leftCentre) distinct
    (hub_mem_fanEnvelope pairObject leftCentre) ?_
  refine (mem_fanEnvelope_iff pairObject rightCentre leftCentre).2 (Or.inr ?_)
  decide

/-- Both charged centres reappear as the assigned centres of the support that
witnesses their B2 failure, so the charge really is levied on the pair the
manuscript charges. -/
theorem centres_assigned_to_overlapSupport :
    leftCentre ∈ (overlapSupport pairObject leftCentre rightCentre).centers ∧
      rightCentre ∈ (overlapSupport pairObject leftCentre rightCentre).centers :=
  ⟨hub_mem_centers_overlapSupport pairObject leftCentre rightCentre,
    other_mem_centers_overlapSupport pairObject leftCentre rightCentre⟩

end B2Witness

end Hypostructure.Graph.TypeBFanMass
