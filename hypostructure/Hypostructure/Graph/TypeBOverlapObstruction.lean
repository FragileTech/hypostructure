import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sum
import Hypostructure.Core.AdmissibleQuotient
import Hypostructure.Graph.TypeBClosure
import Hypostructure.Graph.TypeBExclusion

/-!
# The minimal Type B overlap obstruction and the global-to-local bridge

This file is the graph-mathematics content of manuscript node `[73]`
(Figure 6, Part VI) of `original_erdos_64_proof.tex`:

* `def:typeB-ledger-carriers` -- `Carrier`, the disjoint union of the two
  carrier supports the development already uses, and
  `CandidateEntry.carriers`;
* `def:typeB-candidate-ledger` -- `CandidateEntry`, its carrier support, and
  the two manuscript constructors `certificateClosedEntry` (clause (a)) and
  `hybridEntry` (clause (b));  `HasDisjointChoice` is the manuscript's
  *disjoint refined Type B ledger* and `IsMaximal` its maximality clause;
* `def:typeB-overlap-obstruction` -- `OverlapObstruction` and the overlap
  support `overlapSupport` (`Z(𝒪)`);
* `lem:typeB-maximal-completion` -- `typeBMaximalCompletion`, the finite
  `|M|`-step completion, with `M = H_X = Residual.centers`;
* `lem:typeB-bridge-to-overlap` -- `bridgeToOverlap`, a genuine finite
  minimal-cardinality extraction over `Finset.powerset`;
* `lem:typeB-global-local-reflection`, clauses (a), (b), (c), (d), (e) --
  `contextualDyadicSafety`, `highDegreeSeparation`, `windowCompatibility`,
  `replacementObstruction`, `minimalOverlap`, assembled in
  `globalLocalReflection`;
* `prop:typeB-global-local-bridge` -- `typeBGlobalLocalBridge`;
* `def:typeB-bridge-statements` (B2) -- `RefinedSupportLedger`.

## Nothing is redefined

The assigned Type B support `X`, its counted core `Y_X`, its assigned centres
`H_X`, the vertex charges `ch_X`, the assigned centre charge `ch_X(h)`, the fan
envelope blocks `E_h` and the post-ledger core are all
`Hypostructure.Graph.TypeBBridgeResidual.Residual`.  The disjoint-carrier clause
of B2 in its canonical envelope form and its failure are
`Hypostructure.Graph.TypeBExclusion.DisjointCarriers` and `SharedCarrier`; the
present file relates both to the manuscript's quantified form
(`hasDisjointChoice_of_disjointCarriers`,
`sharedCarrier_of_not_hasDisjointChoice`) and never introduces a second notion of
carrier conflict.  The incidence carriers of clauses (c)/(d) of
`def:typeB-ledger-carriers` are `TypeBFanClosedPorts.Profile.incidences`; the
hybrid B1 capacity is `TypeBHybridLedger`; the certificate-marked fan and its
degree cap `d_G(h) ≤ 8` are `TypeBMarkedFan`; the high-neighbourhood normal form
is `TypeBOpenPorts`.

## No hypothesis asserts the absence of a structure

Clause (a) of `lem:typeB-global-local-reflection` -- contextual dyadic safety --
is *not* a hypothesis: it is `ctx.avoids`, the target avoidance the minimal
counterexample context already carries, read exactly as
`TypeBOpenPorts.LocalHypotheses.not_four_cycle` reads it.  Clause (b) --
high-degree separation -- is *not* a hypothesis either: it is the framework's
`DeletionCriticalityCertificate` at threshold three, through the existing
`tightEndpoint` and `slackVerticesIndependent` -- the two entries Core appended
at manuscript nodes `[9]`--`[10]`, read back by
`Graph.deletionCriticalityOfLedger`.  Clause (c) -- window
compatibility -- is *not* a hypothesis either: its first half is the *definition*
of a packed-window incidence (`TypeBFanClosedPorts.Profile.IsWindowIncidence`, an
edge between the remainder `R = G - W` and the packed-window union `W`) read off
the fields of `def:typeB-candidate-ledger`, and its second half is clause (a)
against the direct-cycle constructions of node `[72]`
(`TypeBClosure.DirectCycleConfiguration`).  Clause (d) -- the replacement
obstruction -- is *not* a hypothesis either: the ledger-response coordinates of
`Z(𝒪)` are this file's own `Carrier` / `CandidateEntry.carriers`, an attempted
identification of two of them is an arbitrary map on that family, and the
manuscript's four alternatives are the two constructors of
`Core.AdmissibleQuotient` read against `NoProperBaselineCertificate.excludes`.
Clause (b)'s certificate is not derived here either: it is the graph reading of
Core's nodes `[9]`--`[10]` ledger entries (`Graph.deletionCriticalityOfLedger`).
Clause (e) is the minimality field of `def:typeB-overlap-obstruction`.

All rational quantities are over `ℚ`, consistent with
`TypeBBridgeResidual.Residual.netCharge`.
-/

namespace Hypostructure.Graph.TypeBOverlapObstruction

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts
open Hypostructure.Graph.TypeBBridgeResidual
open Hypostructure.Graph.TypeBExclusion
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u v w

variable {object : FiniteObject.{u}}

/-! ## `def:typeB-ledger-carriers`: the two carrier supports -/

/-- `def:typeB-ledger-carriers`.  A Type B carrier is one piece of support-charge
data.  Clauses (a), (b) and (e) -- a non-centre vertex of `Y_X`, an assigned
high-degree centre of `H_X`, and a local internal/mixed reserve block -- all have
*vertex* supports; clauses (c) and (d) -- a packed-window incidence `(u, P, i)`
and a non-window fan incidence `uz` -- have *half-edge* supports.

Both underlying supports already exist in the development: the vertex supports
are the ones `TypeBBridgeResidual.Residual.envelopeBlock` collects, the half-edge
supports the ones `TypeBFanClosedPorts.Profile.incidences` collects (a pair
`(u, z)` carrying its owner `u`, exactly as
`def:typeB-window-incidence-profile` demands).  `Carrier` only names their
disjoint union, so that the manuscript's "two carriers are disjoint when their
underlying supports are disjoint" is a single `Disjoint`. -/
abbrev Carrier (object : FiniteObject.{u}) : Type u :=
  object.Vertex ⊕ (object.Vertex × object.Vertex)

/-- Disjointness of two carrier supports splits into the vertex part and the
incidence part. -/
theorem disjoint_disjSum_iff {vertices vertices' : Finset object.Vertex}
    {incidences incidences' : Finset (object.Vertex × object.Vertex)} :
    Disjoint (vertices.disjSum incidences) (vertices'.disjSum incidences') ↔
      Disjoint vertices vertices' ∧ Disjoint incidences incidences' := by
  constructor
  · intro disjointSum
    constructor
    · rw [Finset.disjoint_left]
      intro a leftMember rightMember
      exact Finset.disjoint_left.1 disjointSum
        (Finset.inl_mem_disjSum.2 leftMember) (Finset.inl_mem_disjSum.2 rightMember)
    · rw [Finset.disjoint_left]
      intro e leftMember rightMember
      exact Finset.disjoint_left.1 disjointSum
        (Finset.inr_mem_disjSum.2 leftMember) (Finset.inr_mem_disjSum.2 rightMember)
  · rintro ⟨vertexDisjoint, incidenceDisjoint⟩
    rw [Finset.disjoint_left]
    rintro (a | e) leftMember rightMember
    · exact Finset.disjoint_left.1 vertexDisjoint
        (Finset.inl_mem_disjSum.1 leftMember) (Finset.inl_mem_disjSum.1 rightMember)
    · exact Finset.disjoint_left.1 incidenceDisjoint
        (Finset.inr_mem_disjSum.1 leftMember) (Finset.inr_mem_disjSum.1 rightMember)

/-! ## `def:typeB-candidate-ledger`: candidate Type B ledger entries -/

/-- **`def:typeB-candidate-ledger`.**  A candidate Type B ledger entry for the
Type B demand attached to the marked fan centre `hub` of the assigned support
`residual`.

Clause (a) -- the certificate-closed case -- is the entry with `chosen = ∅`: a
set `A_h ⊆ N(h) \ H_X` of assigned non-centre vertices with
`ch_X(h) + Σ_{v ∈ A_h} ch_X(v) ≥ 0`, whose carriers are the centre together with
`A_h`.  Clause (b) -- the positive-deficit case -- is the entry whose `assigned`
vertices are the cubic-closed fan neighbours whose closed-neighbour deficit is
being paid and whose `chosen` incidences are the packed-window and non-window fan
incidences they use, each of capacity `1/2`.

The single field `pays` covers both clauses: the entry's total capacity is the
assigned centre charge, plus the assigned vertex charges, plus one half-unit per
chosen incidence carrier, and the entry is a candidate exactly when that capacity
is nonnegative.  For `chosen = ∅` this is verbatim clause (a); for the hybrid
entry `hybridEntry` below it is `lem:typeB-hybrid-incidence-budget`. -/
structure CandidateEntry (residual : Residual object) (ledger : LoadCapacityProfile)
    (hub : object.Vertex) where
  /-- Clause (a)'s `A_h`; clause (b)'s cubic-closed fan neighbours. -/
  assigned : Finset object.Vertex
  /-- The assigned vertices are fan neighbours of the centre: `A_h ⊆ N(h)`. -/
  assigned_rim : assigned ⊆ neighbourRim object hub
  /-- ... lying in the counted core `Y_X` (`def:typeB-ledger-carriers` (a)). -/
  assigned_core : assigned ⊆ residual.core
  /-- ... and not themselves entered as assigned high-degree centres:
  `A_h ⊆ N(h) \ H_X`. -/
  assigned_notCentre : ∀ v ∈ assigned, v ∉ residual.centers
  /-- Clause (b)'s chosen incidence carriers, of capacity `1/2` each
  (`def:typeB-ledger-carriers` (c), (d)).  Empty in clause (a). -/
  chosen : Finset (object.Vertex × object.Vertex)
  /-- Every chosen incidence is a non-`h` incidence *used by* one of the assigned
  fan neighbours, as `def:typeB-candidate-ledger` (b) requires. -/
  chosen_owned : ∀ incidence ∈ chosen,
    incidence.1 ∈ assigned ∧ incidence.2 ≠ hub ∧
      object.graph.Adj incidence.1 incidence.2
  /-- The entry pays its demand: `ch_X(h) + Σ_{v ∈ A_h} ch_X(v) + ½·|chosen| ≥ 0`.
  The half-unit per incidence carrier is the capacity of a half-edge carrier of
  `def:typeB-ledger-carriers` (c), (d), not a discharge rate: the rate `α` enters
  only through the charges, which read it from `ledger`. -/
  pays : 0 ≤ centerCharge object ledger hub
    + (∑ v ∈ assigned, residual.vertexCharge ledger v) + (chosen.card : ℚ) / 2

namespace CandidateEntry

variable {residual : Residual object} {ledger : LoadCapacityProfile}
  {hub hub' : object.Vertex}

/-- The vertex part of the carrier support: the centre together with the assigned
non-centre vertices (`def:typeB-candidate-ledger`). -/
noncomputable def vertexCarriers (entry : CandidateEntry residual ledger hub) :
    Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  insert hub entry.assigned

/-- The carrier support of the entry (`def:typeB-ledger-carriers`): its vertex
carriers together with its incidence carriers. -/
noncomputable def carriers (entry : CandidateEntry residual ledger hub) :
    Finset (Carrier object) :=
  entry.vertexCarriers.disjSum entry.chosen

theorem hub_mem_vertexCarriers (entry : CandidateEntry residual ledger hub) :
    hub ∈ entry.vertexCarriers := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.mem_insert_self _ _

theorem assigned_subset_vertexCarriers (entry : CandidateEntry residual ledger hub) :
    entry.assigned ⊆ entry.vertexCarriers := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.subset_insert _ _

/-- Every candidate entry at `h` carries a sub-block of the canonical fan
envelope block `E_h` of `lem:typeB-bridge-deficit-bound`.  This is what makes the
manuscript's quantified disjoint-carrier clause a refinement of the repository's
`TypeBExclusion.DisjointCarriers`, never a second notion of carrier. -/
theorem vertexCarriers_subset_envelopeBlock (entry : CandidateEntry residual ledger hub) :
    entry.vertexCarriers ⊆ residual.envelopeBlock hub := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp only [vertexCarriers, Residual.envelopeBlock]
  refine Finset.insert_subset_insert _ ?_
  intro v member
  exact Finset.mem_inter.2 ⟨entry.assigned_rim member, entry.assigned_core member⟩

theorem disjoint_carriers_iff (entry : CandidateEntry residual ledger hub)
    (entry' : CandidateEntry residual ledger hub') :
    Disjoint entry.carriers entry'.carriers ↔
      Disjoint entry.vertexCarriers entry'.vertexCarriers ∧
        Disjoint entry.chosen entry'.chosen :=
  disjoint_disjSum_iff

/-- Disjoint vertex carriers already force disjoint carrier supports: every
chosen incidence is owned by an assigned vertex, so the incidence blocks cannot
meet once the vertex blocks are disjoint. -/
theorem disjoint_carriers_of_disjoint_vertexCarriers
    {entry : CandidateEntry residual ledger hub} {entry' : CandidateEntry residual ledger hub'}
    (disjointVertices : Disjoint entry.vertexCarriers entry'.vertexCarriers) :
    Disjoint entry.carriers entry'.carriers := by
  refine (disjoint_carriers_iff entry entry').2 ⟨disjointVertices, ?_⟩
  rw [Finset.disjoint_left]
  intro incidence leftMember rightMember
  have leftOwner : incidence.1 ∈ entry.vertexCarriers :=
    entry.assigned_subset_vertexCarriers (entry.chosen_owned incidence leftMember).1
  have rightOwner : incidence.1 ∈ entry'.vertexCarriers :=
    entry'.assigned_subset_vertexCarriers (entry'.chosen_owned incidence rightMember).1
  exact Finset.disjoint_left.1 disjointVertices leftOwner rightOwner

end CandidateEntry

/-! ### The two manuscript constructors

A Type B demand always has at least one candidate entry.  Both constructors are
built from facts that already exist: clause (a) from
`TypeBExclusion.fanEntryCharge_nonneg` (`lem:fan-certificate`, charge half),
clause (b) from `TypeBExclusion.neg_fanDeficit_le_fanEntryCharge` together with
the incidence count `|incidences| = 2c(𝔉)` of
`lem:typeB-hybrid-incidence-budget` and the label-packing cap `d_G(h) ≤ 8` of
`TypeBMarkedFan.Marked.degree_le_eight`. -/

/-- High-degree separation in the form needed by
`def:typeB-candidate-ledger` (a): under the standing normal form no fan
neighbour of an assigned centre is itself an assigned centre, so
`N(h) \ H_X = N(h)`.  This is clause (b) of
`lem:typeB-global-local-reflection` read locally. -/
theorem rim_disjoint_centers (residual : Residual object) {hub : object.Vertex}
    (normal : NormalForm object hub)
    (centresHigh : ∀ h ∈ residual.centers, 4 ≤ object.degree h) :
    ∀ v ∈ neighbourRim object hub, v ∉ residual.centers := by
  intro v member centre
  have cubic : object.degree v = 3 :=
    normal.neighbourCubic ((mem_neighbourRim object hub v).1 member)
  have high := centresHigh v centre
  omega

/-- **`def:typeB-candidate-ledger` (a).**  At a certificate-closed marked fan
centre the whole fan is a candidate entry: its carriers are the centre together
with `N(h) ∩ Y_X`, and the augmented charge it carries is nonnegative by
`lem:fan-certificate`. -/
noncomputable def certificateClosedEntry (residual : Residual object)
    (ledger : LoadCapacityProfile)
    {hub : object.Vertex} (normal : NormalForm object hub)
    (centresHigh : ∀ h ∈ residual.centers, 4 ≤ object.degree h)
    (fanInCore : neighbourRim object hub ⊆ residual.core)
    (closed : IsCertificateClosed residual ledger hub) :
    CandidateEntry residual ledger hub where
  assigned := neighbourRim object hub
  assigned_rim := Finset.Subset.refl _
  assigned_core := fanInCore
  assigned_notCentre := rim_disjoint_centers residual normal centresHigh
  chosen := ∅
  chosen_owned := by
    intro incidence member
    exact absurd member (Finset.notMem_empty incidence)
  pays := by
    have nonneg := fanEntryCharge_nonneg residual ledger normal fanInCore closed
    rw [fanEntryCharge_eq residual ledger normal.high fanInCore] at nonneg
    simpa using nonneg

/-- **`def:typeB-candidate-ledger` (b).**  The hybrid fan entry: the fan envelope
at `h` together with *all* `2c(𝔉_h)` non-`h` incidences of its cubic-closed fan
neighbours, each of capacity `1/2`.

Its capacity is `ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) + c(𝔉_h)`, which by
`neg_fanDeficit_le_fanEntryCharge` is at least
`-D_B(𝔉_h) + c(𝔉_h) = 3 - (k+1)α`, the fan credit, hence nonnegative by the
recorded fan-credit constraint
`ReceiverLoad.LoadCapacityProfile.dischargeRate_le` (`9α ≤ 3`) together with the
label-packing cap `k ≤ 8`.  At `α = 1/4` the credit is the manuscript's
`(11-k)/4 ≥ 3/4 > 0`.  No sign hypothesis on `D_B(𝔉_h)` is used, so this
constructor applies at *every* assigned centre carrying a certificate-marked
fan; in particular a Type B demand never lacks a candidate entry. -/
noncomputable def hybridEntry (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (window : Finset object.Vertex) (marked : Marked object)
    {hub : object.Vertex} (hubEq : marked.fan.hub = hub)
    (normal : NormalForm object hub)
    (centresHigh : ∀ h ∈ residual.centers, 4 ≤ object.degree h)
    (fanInCore : neighbourRim object hub ⊆ residual.core)
    (remainderSide : ∀ u : object.Vertex, object.graph.Adj hub u → u ∉ window) :
    CandidateEntry residual ledger hub where
  assigned := neighbourRim object hub
  assigned_rim := Finset.Subset.refl _
  assigned_core := fanInCore
  assigned_notCentre := rim_disjoint_centers residual normal centresHigh
  chosen := (fanProfile residual window marked).incidences
  chosen_owned := by
    intro incidence member
    obtain ⟨owner, outside⟩ :=
      (Profile.mem_incidences_iff (fanProfile residual window marked) incidence).1 member
    obtain ⟨notHub, adjacency⟩ :=
      (Profile.mem_outsideNeighbours_iff (fanProfile residual window marked)
        incidence.1 incidence.2).1 outside
    refine ⟨?_, ?_, adjacency⟩
    · have rimMember : incidence.1 ∈ marked.fan.rim :=
        ((Profile.mem_closedNeighbours_iff (profile := fanProfile residual window marked)
          incidence.1).1 owner).1
      have adjacent : object.graph.Adj hub incidence.1 := by
        rw [← hubEq]
        exact (marked.rim_eq_neighbourhood incidence.1).1 rimMember
      exact (mem_neighbourRim object hub incidence.1).2 adjacent
    · rw [← hubEq]
      exact notHub
  pays := by
    have normalAt : NormalForm object (fanProfile residual window marked).marked.fan.hub := by
      show NormalForm object marked.fan.hub
      rw [hubEq]
      exact normal
    have remainderAt : ∀ u : object.Vertex,
        object.graph.Adj (fanProfile residual window marked).marked.fan.hub u →
          u ∉ (fanProfile residual window marked).window := by
      show ∀ u : object.Vertex, object.graph.Adj marked.fan.hub u → u ∉ window
      rw [hubEq]
      exact remainderSide
    have countEq :=
      closedCount_eq_closedFanCount residual (fanProfile residual window marked)
        normalAt rfl remainderAt
    have hubHere : (fanProfile residual window marked).marked.fan.hub = hub := hubEq
    rw [hubHere] at countEq
    have cardEq : (fanProfile residual window marked).incidences.card
        = 2 * residual.closedFanCount hub := by
      rw [Profile.card_incidences, countEq]
    have cardCast : ((fanProfile residual window marked).incidences.card : ℚ)
        = 2 * (residual.closedFanCount hub : ℚ) := by
      rw [cardEq]
      push_cast
      ring
    have deficitBound :=
      neg_fanDeficit_le_fanEntryCharge residual ledger normal fanInCore
    rw [fanEntryCharge_eq residual ledger normal.high fanInCore] at deficitBound
    have cap : (object.degree hub : ℚ) ≤ 8 := by
      have step := marked.degree_le_eight
      rw [hubEq] at step
      exact_mod_cast step
    have rateNonneg := ledger.dischargeRate_nonneg
    have credit := ledger.nine_mul_dischargeRate_le_three
    have highRate : ((object.degree hub : ℚ) + 1) * ledger.dischargeRate
        ≤ 9 * ledger.dischargeRate :=
      mul_le_mul_of_nonneg_right (by linarith) rateNonneg
    unfold fanDeficit at deficitBound
    rw [cardCast]
    linarith

/-! ## Disjoint refined Type B ledgers -/

/-- **`def:typeB-candidate-ledger`.**  A *disjoint refined Type B ledger* for a
finite family `demands` of Type B demands: a choice of one candidate entry for
every demand such that all chosen carriers are pairwise disjoint.

This is exactly the disjoint-carrier clause (a)/(c) of
`def:typeB-bridge-statements` (B2), quantified over the candidate entries as the
manuscript states it. -/
def HasDisjointChoice (residual : Residual object) (ledger : LoadCapacityProfile)
    (demands : Finset object.Vertex) : Prop :=
  ∃ entry : ∀ h : object.Vertex, h ∈ demands → CandidateEntry residual ledger h,
    ∀ h (hMember : h ∈ demands) h' (h'Member : h' ∈ demands), h ≠ h' →
      Disjoint (entry h hMember).carriers (entry h' h'Member).carriers

theorem hasDisjointChoice_empty (residual : Residual object)
    (ledger : LoadCapacityProfile) :
    HasDisjointChoice residual ledger (∅ : Finset object.Vertex) :=
  ⟨fun h member => absurd member (Finset.notMem_empty h),
    fun h member => absurd member (Finset.notMem_empty h)⟩

/-- A disjoint refined ledger restricts to every subfamily of demands.  This is
the step "one connected component already contains a subfamily with no disjoint
choice" of `lem:typeB-bridge-to-overlap`, in its contrapositive form. -/
theorem hasDisjointChoice_mono (residual : Residual object)
    (ledger : LoadCapacityProfile)
    {demands demands' : Finset object.Vertex} (subset : demands' ⊆ demands)
    (choice : HasDisjointChoice residual ledger demands) :
    HasDisjointChoice residual ledger demands' := by
  obtain ⟨entry, disjointCarriers⟩ := choice
  exact ⟨fun h member => entry h (subset member),
    fun h member h' member' distinct =>
      disjointCarriers h (subset member) h' (subset member') distinct⟩

/-- The canonical envelope form of the disjoint-carrier clause implies the
manuscript's quantified form: every candidate entry at `h` carries a sub-block of
`E_h`, so once the envelope blocks are pairwise disjoint *any* choice of
candidate entries has pairwise disjoint carriers.

This is the exact relationship between `TypeBExclusion.DisjointCarriers` and B2's
disjoint-carrier clause; no second notion of carrier conflict is introduced. -/
theorem hasDisjointChoice_of_disjointCarriers (residual : Residual object)
    (ledger : LoadCapacityProfile) (b2 : DisjointCarriers residual)
    (entry : ∀ h : object.Vertex, h ∈ residual.centers → CandidateEntry residual ledger h) :
    HasDisjointChoice residual ledger residual.centers := by
  refine ⟨entry, ?_⟩
  intro h member h' member' distinct
  refine CandidateEntry.disjoint_carriers_of_disjoint_vertexCarriers ?_
  exact Finset.disjoint_of_subset_left (entry h member).vertexCarriers_subset_envelopeBlock
    (Finset.disjoint_of_subset_right (entry h' member').vertexCarriers_subset_envelopeBlock
      (b2 h member h' member' distinct))

/-- The failure of B2's disjoint-carrier clause, in the manuscript's quantified
form, entails the repository's explicit shared carrier
`TypeBExclusion.SharedCarrier`: two distinct assigned fan centres of the same
support share a carrier.  So `bridgeToOverlap`'s input refines the residual the
Type B exclusion already produces. -/
theorem sharedCarrier_of_not_hasDisjointChoice (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (entry : ∀ h : object.Vertex, h ∈ residual.centers → CandidateEntry residual ledger h)
    (failure : ¬ HasDisjointChoice residual ledger residual.centers) :
    SharedCarrier residual := by
  rcases disjointCarriers_or_sharedCarrier residual with b2 | shared
  · exact absurd (hasDisjointChoice_of_disjointCarriers residual ledger b2 entry) failure
  · exact shared

/-! ## The maximality clause of `def:typeB-candidate-ledger` -/

/-- The core left after the chosen ledger entries are removed.  At the full
demand family `H_X` this is literally `Residual.residualCore`, the post-ledger
core of `lem:typeB-bridge-deficit-bound`. -/
noncomputable def remainingCore (residual : Residual object)
    (demands : Finset object.Vertex) : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  residual.core \ demands.biUnion residual.envelopeBlock

theorem remainingCore_centers (residual : Residual object) :
    remainingCore residual residual.centers = residual.residualCore := rfl

/-- **`def:typeB-candidate-ledger`, maximality; `def:typeB-bridge-statements`
(B2)(d).**  The refined ledger is *maximal* when, after the chosen entries are
removed, the remaining core has no assigned high-degree fan centre of `X`. -/
def IsMaximal (residual : Residual object) (demands : Finset object.Vertex) : Prop :=
  ∀ h ∈ residual.centers, h ∉ remainingCore residual demands

/-- Maximality is exactly "every assigned centre has been entered as a Type B
demand".  The nontrivial direction uses high-degree separation: a centre cannot
hide inside the fan envelope of a *different* centre, because every fan neighbour
of an assigned centre is cubic. -/
theorem isMaximal_iff (residual : Residual object) {demands : Finset object.Vertex}
    (subset : demands ⊆ residual.centers)
    (normal : ∀ h ∈ residual.centers, NormalForm object h) :
    IsMaximal residual demands ↔ residual.centers ⊆ demands := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  constructor
  · intro maximal h member
    have inCore : h ∈ residual.core := Residual.centers_subset_core member
    have notRemaining := maximal h member
    rw [remainingCore, Finset.mem_sdiff] at notRemaining
    have covered : h ∈ demands.biUnion residual.envelopeBlock := by
      by_contra notCovered
      exact notRemaining ⟨inCore, notCovered⟩
    obtain ⟨h', h'Member, block⟩ := Finset.mem_biUnion.1 covered
    rw [Residual.envelopeBlock, Finset.mem_insert] at block
    rcases block with rfl | rimMember
    · exact h'Member
    · exfalso
      have adjacency : object.graph.Adj h' h :=
        (mem_neighbourRim object h' h).1 (Finset.mem_inter.1 rimMember).1
      have cubic : object.degree h = 3 :=
        (normal h' (subset h'Member)).neighbourCubic adjacency
      have high := (normal h member).high
      omega
  · intro full h member
    rw [remainingCore, Finset.mem_sdiff]
    rintro ⟨-, notCovered⟩
    refine notCovered (Finset.mem_biUnion.2 ⟨h, full member, ?_⟩)
    rw [Residual.envelopeBlock]
    exact Finset.mem_insert_self _ _

/-- **`def:typeB-bridge-statements` (B2).**  The refined support ledger: the
disjoint-carrier clauses (a)/(c) together with the maximality clause (d). -/
structure RefinedSupportLedger (residual : Residual object)
    (ledger : LoadCapacityProfile) : Prop where
  /-- Clauses (a)/(c): a disjoint refined Type B ledger for the whole demand
  family `H_X`. -/
  disjointChoice : HasDisjointChoice residual ledger residual.centers
  /-- Clause (d): the ledger is maximal for the Type B support assignment. -/
  maximal : IsMaximal residual residual.centers

/-! ## `def:typeB-overlap-obstruction` -/

/-- **`def:typeB-overlap-obstruction`.**  A *minimal Type B overlap obstruction*
of the assigned support `residual`: a nonempty finite family `𝒟` of Type B
demands of `X` such that no choice of one candidate ledger entry per demand has
pairwise disjoint carriers, while every proper nonempty subfamily does admit such
a disjoint choice.

The candidate-entry family `{ℰ(d)}` of the manuscript is not free data: `ℰ(d)` is
the set of candidate entries at the demand centre `d`, i.e. the type
`CandidateEntry residual ledger d`, so it is determined by `𝒟` and by `X`. -/
structure OverlapObstruction (residual : Residual object)
    (ledger : LoadCapacityProfile) where
  /-- The demand family `𝒟`. -/
  demands : Finset object.Vertex
  /-- Every demand is attached to an assigned fan centre of `X`. -/
  demands_subset : demands ⊆ residual.centers
  /-- `𝒟` is nonempty. -/
  demands_nonempty : demands.Nonempty
  /-- No choice `E_d ∈ ℰ(d)` has pairwise disjoint carriers. -/
  noDisjointChoice : ¬ HasDisjointChoice residual ledger demands
  /-- Minimality: every proper nonempty subfamily admits a disjoint choice. -/
  minimal : ∀ ⦃sub : Finset object.Vertex⦄, sub ⊂ demands → sub.Nonempty →
    HasDisjointChoice residual ledger sub

/-- The vertices carried by the Type B ledger at one demand centre: the fan
envelope block `E_h` -- the centre together with its assigned fan neighbours,
which already contains every vertex carrier of every candidate entry at `h` --
together with the core endpoints of their incidence carriers, i.e. the vertices
that the witnessing wedges and window segments of the fan-safe relation pass
through. -/
noncomputable def carrierSupport (residual : Residual object) (hub : object.Vertex) :
    Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  residual.envelopeBlock hub ∪
    ((neighbourRim object hub).biUnion (neighbourRim object) ∩ residual.core)

theorem envelopeBlock_subset_carrierSupport (residual : Residual object)
    (hub : object.Vertex) :
    residual.envelopeBlock hub ⊆ carrierSupport residual hub := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.subset_union_left

/-- **`def:typeB-overlap-obstruction`: the overlap support `Z(𝒪)`.**  The support
induced by the fan centres in `𝒟`, all vertices and incidences appearing in their
candidate entries, and the paths or window segments witnessing the corresponding
fan-safe relations. -/
noncomputable def overlapSupport {residual : Residual object}
    {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger) : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obstruction.demands.biUnion (carrierSupport residual)

namespace OverlapObstruction

variable {residual : Residual object} {ledger : LoadCapacityProfile}

theorem demands_subset_overlapSupport (obstruction : OverlapObstruction residual ledger) :
    obstruction.demands ⊆ overlapSupport obstruction := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro h member
  refine Finset.mem_biUnion.2 ⟨h, member, ?_⟩
  refine envelopeBlock_subset_carrierSupport residual h ?_
  rw [Residual.envelopeBlock]
  exact Finset.mem_insert_self _ _

theorem vertexCarriers_subset_overlapSupport
    (obstruction : OverlapObstruction residual ledger) {hub : object.Vertex}
    (member : hub ∈ obstruction.demands) (entry : CandidateEntry residual ledger hub) :
    entry.vertexCarriers ⊆ overlapSupport obstruction := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro v inCarriers
  exact Finset.mem_biUnion.2 ⟨hub, member,
    envelopeBlock_subset_carrierSupport residual hub
      (entry.vertexCarriers_subset_envelopeBlock inCarriers)⟩

/-- **The connectivity step of `lem:typeB-bridge-to-overlap`.**  Cover the demand
family of a minimal overlap obstruction by two parts.  For *any* choice of one
candidate entry per demand whose carriers are pairwise disjoint inside each part,
some carrier is shared *across* the two parts.  The obstruction therefore does
not fall apart into two independent pieces: this is exactly why `Z(𝒪)` may be
taken connected. -/
theorem carrier_crosses (obstruction : OverlapObstruction residual ledger)
    (entry : ∀ h : object.Vertex, h ∈ obstruction.demands → CandidateEntry residual ledger h)
    {left right : Finset object.Vertex}
    (cover : ∀ h ∈ obstruction.demands, h ∈ left ∨ h ∈ right)
    (insideLeft : ∀ h (hMember : h ∈ obstruction.demands) h'
      (h'Member : h' ∈ obstruction.demands), h ∈ left → h' ∈ left → h ≠ h' →
      Disjoint (entry h hMember).carriers (entry h' h'Member).carriers)
    (insideRight : ∀ h (hMember : h ∈ obstruction.demands) h'
      (h'Member : h' ∈ obstruction.demands), h ∈ right → h' ∈ right → h ≠ h' →
      Disjoint (entry h hMember).carriers (entry h' h'Member).carriers) :
    ∃ h, ∃ hMember : h ∈ obstruction.demands, ∃ h', ∃ h'Member : h' ∈ obstruction.demands,
      h ∈ left ∧ h' ∈ right ∧ h ≠ h' ∧
        ¬ Disjoint (entry h hMember).carriers (entry h' h'Member).carriers := by
  by_contra noCross
  refine obstruction.noDisjointChoice ⟨entry, ?_⟩
  intro h hMember h' h'Member distinct
  have crossFree : ∀ a (aMember : a ∈ obstruction.demands) b
      (bMember : b ∈ obstruction.demands), a ∈ left → b ∈ right → a ≠ b →
      Disjoint (entry a aMember).carriers (entry b bMember).carriers := by
    intro a aMember b bMember aLeft bRight ab
    by_contra meets
    exact noCross ⟨a, aMember, b, bMember, aLeft, bRight, ab, meets⟩
  rcases cover h hMember with hLeft | hRight
  · rcases cover h' h'Member with h'Left | h'Right
    · exact insideLeft h hMember h' h'Member hLeft h'Left distinct
    · exact crossFree h hMember h' h'Member hLeft h'Right distinct
  · rcases cover h' h'Member with h'Left | h'Right
    · exact (crossFree h' h'Member h hMember h'Left hRight distinct.symm).symm
    · exact insideRight h hMember h' h'Member hRight h'Right distinct

end OverlapObstruction

/-! ## `lem:typeB-bridge-to-overlap` -/

/-- **`lem:typeB-bridge-to-overlap`, general form.**  If the disjoint-carrier
part of the B2 refined support ledger fails on some finite family of Type B
demands of `X`, then `X` contains a *minimal* Type B overlap obstruction.

The extraction is genuine and finite: among all nonempty subfamilies of the
declared demand family -- an explicit `Finset.powerset` -- for which the disjoint
choice fails, `Finset.exists_min_image` selects one of minimal cardinality, and
minimality of the cardinality is precisely the minimality clause of
`def:typeB-overlap-obstruction`.  Nothing is assumed. -/
theorem exists_overlapObstruction_of_not_hasDisjointChoice (residual : Residual object)
    (ledger : LoadCapacityProfile)
    {demands : Finset object.Vertex} (subset : demands ⊆ residual.centers)
    (failure : ¬ HasDisjointChoice residual ledger demands) :
    Nonempty (OverlapObstruction residual ledger) := by
  classical
  have nonempty : demands.Nonempty := by
    rcases Finset.eq_empty_or_nonempty demands with rfl | ne
    · exact absurd (hasDisjointChoice_empty residual ledger) failure
    · exact ne
  set failing : Finset (Finset object.Vertex) :=
    demands.powerset.filter
      (fun family => family.Nonempty ∧ ¬ HasDisjointChoice residual ledger family) with failingDef
  have selfMember : demands ∈ failing := by
    rw [failingDef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, nonempty, failure⟩
  obtain ⟨minimalFamily, minimalMember, minimalCard⟩ :=
    failing.exists_min_image Finset.card ⟨demands, selfMember⟩
  rw [failingDef, Finset.mem_filter, Finset.mem_powerset] at minimalMember
  obtain ⟨minimalSubset, minimalNonempty, minimalFailure⟩ := minimalMember
  refine ⟨{ demands := minimalFamily
            demands_subset := minimalSubset.trans subset
            demands_nonempty := minimalNonempty
            noDisjointChoice := minimalFailure
            minimal := ?_ }⟩
  intro sub proper subNonempty
  by_contra subFailure
  have subMember : sub ∈ failing := by
    rw [failingDef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨proper.subset.trans minimalSubset, subNonempty, subFailure⟩
  have cardLe := minimalCard sub subMember
  have cardLt := Finset.card_lt_card proper
  omega

/-- **`lem:typeB-bridge-to-overlap`.**  Let `X` be a connected assigned Type B
support with no fan-certificate residual centre.  If the disjoint-carrier part of
the B2 refined support ledger of `def:typeB-bridge-statements` fails for `X`,
then `X` contains a minimal Type B overlap obstruction in the sense of
`def:typeB-overlap-obstruction`.

"No fan-certificate residual centre" is not a hypothesis here either: it is the
positive datum that every assigned centre carries a candidate entry, which
`hybridEntry` supplies from a certificate-marked fan.  That datum is what makes
the failure equivalent to the repository's `TypeBExclusion.SharedCarrier`
(`sharedCarrier_of_not_hasDisjointChoice`). -/
theorem bridgeToOverlap (residual : Residual object) (ledger : LoadCapacityProfile)
    (failure : ¬ HasDisjointChoice residual ledger residual.centers) :
    Nonempty (OverlapObstruction residual ledger) :=
  exists_overlapObstruction_of_not_hasDisjointChoice residual ledger
    (Finset.Subset.refl _) failure

/-- The dichotomy the Type B routing consumes, in the shape of
`TypeBExclusion.disjointCarriers_or_sharedCarrier`: either the whole demand
family of `X` admits a disjoint refined Type B ledger, or `X` carries a minimal
Type B overlap obstruction. -/
theorem hasDisjointChoice_or_overlapObstruction (residual : Residual object)
    (ledger : LoadCapacityProfile) :
    HasDisjointChoice residual ledger residual.centers ∨
      Nonempty (OverlapObstruction residual ledger) := by
  by_cases holds : HasDisjointChoice residual ledger residual.centers
  · exact Or.inl holds
  · exact Or.inr (bridgeToOverlap residual ledger holds)

/-- The absence of a Type B overlap obstruction gives a disjoint refined ledger
for *every* subfamily of the Type B demands of `X`.  This is the step
"absence of a Type B overlap obstruction means precisely that the enlarged finite
demand family has a choice of candidate entries with pairwise disjoint carriers"
in the proof of `lem:typeB-maximal-completion`. -/
theorem hasDisjointChoice_of_isEmpty (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (noObstruction : IsEmpty (OverlapObstruction residual ledger))
    {demands : Finset object.Vertex} (subset : demands ⊆ residual.centers) :
    HasDisjointChoice residual ledger demands := by
  by_contra failure
  exact noObstruction.elim
    (exists_overlapObstruction_of_not_hasDisjointChoice residual ledger subset
      failure).some

/-! ## `lem:typeB-maximal-completion` -/

/-- The Type B demand centres of `X` not yet entered in the family, in the
object's own vertex scan order.  The manuscript adds the *lexicographically
first* such vertex; here that is the head of this schedule.  The finite set `ℳ`
of the manuscript's proof is `Residual.centers`, the assigned high-degree fan
centres of `X`; no new set is introduced. -/
noncomputable def unprocessedSchedule (residual : Residual object)
    (demands : Finset object.Vertex) : List object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  object.orderedVertices.filter fun vertex =>
    decide (vertex ∈ residual.centers ∧ vertex ∉ demands)

theorem mem_unprocessedSchedule_iff (residual : Residual object)
    (demands : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ unprocessedSchedule residual demands ↔
      vertex ∈ residual.centers ∧ vertex ∉ demands := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [unprocessedSchedule, List.mem_filter]
  simp [object.mem_orderedVertices vertex]

/-- One completion step of `lem:typeB-maximal-completion`: while the ledger is
not yet maximal, the lexicographically first unprocessed assigned centre is
available and can be added to the demand family, strictly decreasing the number
of unprocessed centres.  No step creates a new assigned centre, so the loop
terminates after at most `|ℳ| = |H_X|` steps. -/
theorem exists_nextDemand (residual : Residual object)
    {demands : Finset object.Vertex} (notFull : ¬ residual.centers ⊆ demands) :
    ∃ hub : object.Vertex,
      (unprocessedSchedule residual demands).head? = some hub ∧
        hub ∈ residual.centers ∧ hub ∉ demands := by
  obtain ⟨witness, witnessCentre, witnessNew⟩ := Finset.not_subset.1 notFull
  have witnessMember : witness ∈ unprocessedSchedule residual demands :=
    (mem_unprocessedSchedule_iff residual demands witness).2 ⟨witnessCentre, witnessNew⟩
  cases schedule : unprocessedSchedule residual demands with
  | nil =>
      rw [schedule] at witnessMember
      exact absurd witnessMember (List.not_mem_nil)
  | cons head tail =>
      refine ⟨head, rfl, ?_⟩
      have headMember : head ∈ unprocessedSchedule residual demands := by
        rw [schedule]
        exact List.mem_cons_self
      exact (mem_unprocessedSchedule_iff residual demands head).1 headMember

/-- The number of assigned centres of `X` not yet entered as Type B demands: the
size of the manuscript's unprocessed part of `ℳ = H_X`.  Each completion step
decreases it by exactly one, which is why the loop stops after at most `|ℳ|`
steps. -/
noncomputable def unprocessedCount (residual : Residual object)
    (demands : Finset object.Vertex) : Nat :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  (residual.centers \ demands).card

theorem unprocessedCount_eq_zero_iff (residual : Residual object)
    (demands : Finset object.Vertex) :
    unprocessedCount residual demands = 0 ↔ residual.centers ⊆ demands := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  show (residual.centers \ demands).card = 0 ↔ residual.centers ⊆ demands
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

private theorem completionLoop (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (noObstruction : IsEmpty (OverlapObstruction residual ledger)) :
    ∀ (fuel : Nat) (demands : Finset object.Vertex),
      demands ⊆ residual.centers →
      unprocessedCount residual demands ≤ fuel →
      ∃ final : Finset object.Vertex,
        demands ⊆ final ∧ final ⊆ residual.centers ∧
          HasDisjointChoice residual ledger final ∧ residual.centers ⊆ final := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro fuel
  induction fuel with
  | zero =>
      intro demands subset measure
      have full : residual.centers ⊆ demands :=
        (unprocessedCount_eq_zero_iff residual demands).1 (by omega)
      exact ⟨demands, Finset.Subset.refl _, subset,
        hasDisjointChoice_of_isEmpty residual ledger noObstruction subset, full⟩
  | succ remaining ih =>
      intro demands subset measure
      by_cases full : residual.centers ⊆ demands
      · exact ⟨demands, Finset.Subset.refl _, subset,
          hasDisjointChoice_of_isEmpty residual ledger noObstruction subset, full⟩
      · obtain ⟨hub, -, hubCentre, hubNew⟩ := exists_nextDemand residual full
        have enlargedSubset : insert hub demands ⊆ residual.centers :=
          Finset.insert_subset hubCentre subset
        have hubInDiff : hub ∈ residual.centers \ demands :=
          Finset.mem_sdiff.2 ⟨hubCentre, hubNew⟩
        have measureStep : unprocessedCount residual (insert hub demands) + 1
            = unprocessedCount residual demands := by
          have erased : residual.centers \ insert hub demands
              = (residual.centers \ demands).erase hub := by
            ext vertex
            simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
            tauto
          have positive : 0 < (residual.centers \ demands).card :=
            Finset.card_pos.2 ⟨hub, hubInDiff⟩
          show (residual.centers \ insert hub demands).card + 1
              = (residual.centers \ demands).card
          rw [erased, Finset.card_erase_of_mem hubInDiff]
          omega
        obtain ⟨final, enlargedFinal, finalSubset, finalLedger, finalFull⟩ :=
          ih (insert hub demands) enlargedSubset (by omega)
        exact ⟨final, (Finset.subset_insert hub demands).trans enlargedFinal,
          finalSubset, finalLedger, finalFull⟩

/-- **`lem:typeB-maximal-completion`**, manuscript node `[73]`; this is clause
(d) of `def:typeB-bridge-statements` (B2).

Let `X` be a connected assigned Type B support with no fan-certificate residual
centre, and suppose that no finite family of Type B demands in `X` forms a Type B
overlap obstruction in the sense of `def:typeB-overlap-obstruction`.  Then the
Type B demands of `X` admit a *maximal* disjoint refined Type B ledger extending
any declared starting family.

The proof is the manuscript's finite completion, formalised as a fuelled loop:
`ℳ` is `Residual.centers`, each step adds the lexicographically first
unprocessed vertex of `ℳ` (`exists_nextDemand`, using the object's own vertex
scan order), no step creates a new element of `ℳ`, and the loop therefore
terminates after at most `|ℳ|` steps.  Absence of an overlap obstruction is what
supplies the rechosen ledger of the enlarged family
(`hasDisjointChoice_of_isEmpty`). -/
theorem typeBMaximalCompletion (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (noObstruction : IsEmpty (OverlapObstruction residual ledger))
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    {start : Finset object.Vertex} (subset : start ⊆ residual.centers) :
    ∃ demands : Finset object.Vertex,
      start ⊆ demands ∧ demands ⊆ residual.centers ∧
        HasDisjointChoice residual ledger demands ∧ IsMaximal residual demands := by
  obtain ⟨final, extends', finalSubset, finalLedger, finalFull⟩ :=
    completionLoop residual ledger noObstruction (unprocessedCount residual start)
      start subset (le_refl _)
  exact ⟨final, extends', finalSubset, finalLedger,
    (isMaximal_iff residual finalSubset normal).2 finalFull⟩

/-- The maximal completion in the packaged form of `def:typeB-bridge-statements`:
the whole demand family `H_X` carries a disjoint refined Type B ledger and that
ledger is maximal.  This is B2. -/
theorem refinedSupportLedger_of_isEmpty (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (noObstruction : IsEmpty (OverlapObstruction residual ledger))
    (normal : ∀ h ∈ residual.centers, NormalForm object h) :
    RefinedSupportLedger residual ledger where
  disjointChoice :=
    hasDisjointChoice_of_isEmpty residual ledger noObstruction (Finset.Subset.refl _)
  maximal :=
    (isMaximal_iff residual (Finset.Subset.refl _) normal).2 (Finset.Subset.refl _)

/-! ## `lem:typeB-global-local-reflection`, clauses (a), (b), (c), (d), (e) -/

/-- **`lem:typeB-global-local-reflection` (a): contextual dyadic safety.**  No
cycle of `G` meeting `V(Z)` has an accepted (power-of-two) length.

The absence of the cycle is **not** a hypothesis: it is `ctx.avoids`, the target
avoidance the minimal-counterexample node already established and carries on the
residual, read exactly as `TypeBOpenPorts.LocalHypotheses.not_four_cycle` reads
it.  Because `Z ⊆ X ⊆ G`, a power-of-two cycle meeting `V(Z)` would be a
power-of-two cycle of `G`. -/
theorem contextualDyadicSafety
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    {residual : Residual ctx.G} {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger)
    {base : ctx.G.Vertex} (cycle : ctx.G.graph.Walk base base)
    (isCycle : cycle.IsCycle) :
    ∀ vertex ∈ overlapSupport obstruction, vertex ∈ cycle.support →
      ¬ LengthOK cycle.length := by
  intro _ _ _ accepted
  exact ctx.avoids ⟨⟨base, cycle, isCycle, accepted⟩⟩

/-- **`lem:typeB-global-local-reflection` (b): high-degree separation.**  The
high-degree fan centres in `Z` are independent, and every neighbour of such a
centre has ambient degree three.

Both halves are the framework's edge-deletion criticality at threshold three,
reused verbatim: independence is
`DeletionCriticalityCertificate.slackVerticesIndependent` (no edge joins two
vertices of degree at least four) and the cubicity of the neighbours is
`DeletionCriticalityCertificate.tightEndpoint` (every edge has an endpoint of
degree exactly three).  Nothing is restated and nothing is assumed. -/
theorem highDegreeSeparation
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {criticality : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (certificate : DeletionCriticalityCertificate criticality ctx)
    (thresholdThree : criticality.threshold = 3)
    {residual : Residual ctx.G} {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger) :
    (∀ h ∈ overlapSupport obstruction, ∀ h' ∈ overlapSupport obstruction,
        4 ≤ ctx.G.degree h → 4 ≤ ctx.G.degree h' → ¬ ctx.G.graph.Adj h h') ∧
      (∀ h ∈ overlapSupport obstruction, 4 ≤ ctx.G.degree h →
        ∀ u : ctx.G.Vertex, ctx.G.graph.Adj h u → ctx.G.degree u = 3) := by
  refine ⟨?_, ?_⟩
  · intro h _ h' _ hHigh h'High
    exact certificate.slackVerticesIndependent
      (by rw [thresholdThree]; omega) (by rw [thresholdThree]; omega)
  · intro h _ hHigh u adjacent
    have endpoint := certificate.tightEndpoint ⟨(h, u), adjacent⟩
    change ctx.G.degree h = criticality.threshold ∨
      ctx.G.degree u = criticality.threshold at endpoint
    rw [thresholdThree] at endpoint
    omega

/-! ### Clause (c): window compatibility

`def:typeB-window-incidence-profile` *defines* a packed-window incidence to be an
edge `u z` with `u` on the remainder side `R = G - W` and `z` in the packed
window union `W`; that definition is
`TypeBFanClosedPorts.Profile.IsWindowIncidence` verbatim.  So the first half of
clause (c) -- "every packed-window incidence of `Z` is one of the outside
incidences of the `R`--`W` supply" -- is a *membership*, proved below from the
fields of `def:typeB-candidate-ledger` alone.  Nothing is counted: the
`15p₁₃ + o(n)` figure of `lem:stub-positive` is a *size* of that supply, and the
manuscript's proof of clause (c) does not use it ("each packed-window incidence
is **by definition** an edge between `R = G - W` and the packed window union
`W`; such edges are exactly the incidence supply counted in
`lem:stub-positive`").

The second half is the direct-cycle exclusion, obtained from clause (a) by
contradiction, exactly as the manuscript obtains it: "if same-window or
two-window labels violated the displayed arithmetic exclusions, the
corresponding direct-cycle lemma would produce a power-of-two cycle meeting `Z`,
contradicting (a)". -/

/-- **`lem:typeB-global-local-reflection` (c), first half.**  A packed-window
incidence of `Z(𝒪)` -- an incidence carrier chosen by a candidate ledger entry
at a demand of `𝒪` whose outside endpoint lies in the packed-window union `W` --
is an edge between the remainder `R = G - W` and `W`, its owner is a
remainder-side fan neighbour of the demand centre, and that owner is a carrier of
`Z(𝒪)`.

Every step is definitional.  `CandidateEntry.chosen_owned` says a chosen
incidence is an edge `u z` owned by an assigned vertex `u`;
`CandidateEntry.assigned_rim` puts `u` in `N(h)`; the recording convention
`remainderSide` of `def:typeB-window-incidence-profile` -- the same argument
`typeBGlobalLocalBridge` already carries -- puts `u` outside `W`.  Together with
`z ∈ W` that is literally `Profile.IsWindowIncidence u z`, and with
`marked.rim_eq_neighbourhood` it is `Profile.remainder` membership.  The owner is
a vertex carrier of the entry (`assigned_subset_vertexCarriers`), hence a vertex
of `Z(𝒪)` by `vertexCarriers_subset_overlapSupport`.

No supply ceiling is stated, used or assumed. -/
theorem packedWindowIncidence (residual : Residual object)
    {ledger : LoadCapacityProfile}
    (window : Finset object.Vertex) (markedAt : object.Vertex → Marked object)
    (hubAt : ∀ h ∈ residual.centers, (markedAt h).fan.hub = h)
    (remainderSide : ∀ h ∈ residual.centers, ∀ u : object.Vertex,
      object.graph.Adj h u → u ∉ window)
    (obstruction : OverlapObstruction residual ledger) {hub : object.Vertex}
    (hubMember : hub ∈ obstruction.demands) (entry : CandidateEntry residual ledger hub)
    {incidence : object.Vertex × object.Vertex} (member : incidence ∈ entry.chosen)
    (inWindow : incidence.2 ∈ window) :
    (fanProfile residual window (markedAt hub)).IsWindowIncidence
        incidence.1 incidence.2 ∧
      incidence.1 ∈ (fanProfile residual window (markedAt hub)).remainder ∧
      incidence.1 ∈ overlapSupport obstruction := by
  have centre : hub ∈ residual.centers := obstruction.demands_subset hubMember
  obtain ⟨owner, -, adjacency⟩ := entry.chosen_owned incidence member
  have rimAdjacency : object.graph.Adj hub incidence.1 :=
    (mem_neighbourRim object hub incidence.1).1 (entry.assigned_rim owner)
  have outside : incidence.1 ∉ window := remainderSide hub centre incidence.1 rimAdjacency
  refine ⟨⟨outside, adjacency, inWindow⟩, ?_, ?_⟩
  · refine (Profile.mem_remainder_iff
      (profile := fanProfile residual window (markedAt hub)) incidence.1).2 ⟨?_, outside⟩
    refine ((markedAt hub).rim_eq_neighbourhood incidence.1).2 ?_
    rw [hubAt hub centre]
    exact rimAdjacency
  · exact OverlapObstruction.vertexCarriers_subset_overlapSupport obstruction hubMember
      entry (entry.assigned_subset_vertexCarriers owner)

/-- **Clause (a) in the form the direct-cycle eliminations of node `[72]`
consume.**  `def:direct-cycle-free-closed-pair` holds on the ambient minimal
counterexample: none of the same-window configurations of
`lem:typeB-direct-fan-window-cycles` and none of the two-window configurations of
`lem:typeB-two-window-cycles` occurs.

This is not a hypothesis.  `TypeBClosure.hasCycleWithLength_of_directCycleConfiguration`
turns any such configuration into a power-of-two cycle of `G`, and the target
avoidance `ctx.avoids` -- the very datum clause (a) `contextualDyadicSafety`
reads -- forbids it. -/
theorem directCycleFree
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    (accepted : TypeBClosure.AcceptedLengths LengthOK)
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)} :
    TypeBClosure.DirectCycleFree ctx.G := fun configuration =>
  ctx.avoids
    (TypeBClosure.hasCycleWithLength_of_directCycleConfiguration accepted configuration)

/-- **Clause (c), the same-window exclusion.**  A remainder-side owner with two
packed-window incidences into the *same* packed window, at coordinates `a < b`,
satisfies the arithmetic exclusion `b - a ∉ {2, 6}` of the first display of
`lem:typeB-direct-fan-window-cycles`.

The manuscript's argument, verbatim: a violating label pair is a
`TypeBClosure.SameWindowAttachmentWitness`, whose direct-cycle lemma
`hasCycleWithLength_of_dyadicSameWindowAttachment` produces the power-of-two
cycle `u p_a P p_b u` through the owner `u` of the incidences -- a vertex of `Z`
-- which clause (a) forbids.  The side condition `u ∉ W` is the first component
of `Profile.IsWindowIncidence`, not an assumption. -/
theorem sameWindowExclusion
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    (accepted : TypeBClosure.AcceptedLengths LengthOK)
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (profile : Profile ctx.G) {w : TypeBClosure.Window ctx.G} (packed : w.IsPacked)
    (inWindow : ∀ t ≤ 12, w.coordinate t ∈ profile.window)
    {owner : ctx.G.Vertex} {a b : Nat} (order : a < b) (bound : b ≤ 12)
    (lower : profile.IsWindowIncidence owner (w.coordinate a))
    (upper : profile.IsWindowIncidence owner (w.coordinate b)) :
    b - a ≠ 2 ∧ b - a ≠ 6 := by
  have free : ∀ t ≤ 12, owner ≠ w.coordinate t :=
    TypeBClosure.window_free_of_not_mem_window inWindow lower.1
  have exclusion : ¬ (b - a = 2 ∨ b - a = 6) := fun dyadicGap =>
    directCycleFree (ctx := ctx) accepted
      (Or.inl ⟨w, owner, a, b, packed, order, bound, free, lower.2.1, upper.2.1,
        dyadicGap⟩)
  exact ⟨fun equal => exclusion (Or.inl equal), fun equal => exclusion (Or.inr equal)⟩

/-- **Clause (c), the two-window exclusion.**  Two distinct remainder-side owners
with packed-window incidences into two vertex-disjoint packed windows satisfy the
arithmetic exclusion `|i - j| + |a - b| ∉ {0, 4, 12}` of
`lem:typeB-two-window-cycles`.

Again the manuscript's argument: a violating label pair is a
`TypeBClosure.TwoWindowPairWitness`, whose direct-cycle lemma
`hasCycleWithLength_of_dyadicTwoWindowPair` produces the power-of-two cycle
`u p_i P p_j v q_b Q q_a u` through both owners, which clause (a) forbids. -/
theorem twoWindowExclusion
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    (accepted : TypeBClosure.AcceptedLengths LengthOK)
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (profile : Profile ctx.G) {first second : TypeBClosure.Window ctx.G}
    (firstPacked : first.IsPacked) (secondPacked : second.IsPacked)
    (windowsDisjoint : ∀ s ≤ 12, ∀ t ≤ 12,
      first.coordinate s ≠ second.coordinate t)
    (firstInWindow : ∀ t ≤ 12, first.coordinate t ∈ profile.window)
    (secondInWindow : ∀ t ≤ 12, second.coordinate t ∈ profile.window)
    {left right : ctx.G.Vertex} {i j a b : Nat}
    (boundI : i ≤ 12) (boundJ : j ≤ 12) (boundA : a ≤ 12) (boundB : b ≤ 12)
    (distinct : left ≠ right)
    (leftFirst : profile.IsWindowIncidence left (first.coordinate i))
    (rightFirst : profile.IsWindowIncidence right (first.coordinate j))
    (leftSecond : profile.IsWindowIncidence left (second.coordinate a))
    (rightSecond : profile.IsWindowIncidence right (second.coordinate b)) :
    (max i j - min i j) + (max a b - min a b) ≠ 0 ∧
      (max i j - min i j) + (max a b - min a b) ≠ 4 ∧
      (max i j - min i j) + (max a b - min a b) ≠ 12 := by
  have exclusion : ¬ ((max i j - min i j) + (max a b - min a b) = 0 ∨
      (max i j - min i j) + (max a b - min a b) = 4 ∨
      (max i j - min i j) + (max a b - min a b) = 12) := fun dyadicSum =>
    directCycleFree (ctx := ctx) accepted
      (Or.inr (Or.inr (Or.inr
        ⟨first, second, left, right, i, j, a, b, firstPacked, secondPacked,
          windowsDisjoint, boundI, boundJ, boundA, boundB,
          TypeBClosure.window_free_of_not_mem_window firstInWindow leftFirst.1,
          TypeBClosure.window_free_of_not_mem_window secondInWindow leftSecond.1,
          TypeBClosure.window_free_of_not_mem_window firstInWindow rightFirst.1,
          TypeBClosure.window_free_of_not_mem_window secondInWindow rightSecond.1,
          distinct, leftFirst.2.1, rightFirst.2.1, leftSecond.2.1, rightSecond.2.1,
          dyadicSum⟩)))
  exact ⟨fun equal => exclusion (Or.inl equal),
    fun equal => exclusion (Or.inr (Or.inl equal)),
    fun equal => exclusion (Or.inr (Or.inr equal))⟩

/-- **`lem:typeB-global-local-reflection` (c): window compatibility.**

* Every packed-window incidence of `Z(𝒪)` is an edge between the remainder
  `R = G - W` and the packed-window union `W`, carried by a remainder-side fan
  neighbour of a demand centre which is itself a vertex of `Z(𝒪)`
  (`packedWindowIncidence`).
* The same-window and two-window labels satisfy the direct-cycle exclusions of
  `lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`, i.e.
  `def:direct-cycle-free-closed-pair` holds (`TypeBClosure.DirectCycleFree`); the
  two displayed arithmetic exclusions are `sameWindowExclusion` and
  `twoWindowExclusion`.

Neither half is a hypothesis and neither half is an estimate.  The first is the
definition of a packed-window incidence, read off the fields of
`def:typeB-candidate-ledger`; the second is clause (a) -- `ctx.avoids`, the
target avoidance `contextualDyadicSafety` reads -- against the direct-cycle
constructions of node `[72]`.  In particular the `15p₁₃ + o(n)` supply *size* of
`lem:stub-positive` is never stated, used or assumed: the manuscript's proof of
this clause does not use it either. -/
theorem windowCompatibility
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    (accepted : TypeBClosure.AcceptedLengths LengthOK)
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    {residual : Residual ctx.G} {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger)
    (window : Finset ctx.G.Vertex) (markedAt : ctx.G.Vertex → Marked ctx.G)
    (hubAt : ∀ h ∈ residual.centers, (markedAt h).fan.hub = h)
    (remainderSide : ∀ h ∈ residual.centers, ∀ u : ctx.G.Vertex,
      ctx.G.graph.Adj h u → u ∉ window) :
    (∀ h ∈ obstruction.demands, ∀ entry : CandidateEntry residual ledger h,
        ∀ incidence ∈ entry.chosen, incidence.2 ∈ window →
          (fanProfile residual window (markedAt h)).IsWindowIncidence
              incidence.1 incidence.2 ∧
            incidence.1 ∈ (fanProfile residual window (markedAt h)).remainder ∧
            incidence.1 ∈ overlapSupport obstruction) ∧
      TypeBClosure.DirectCycleFree ctx.G :=
  ⟨fun _ hubMember entry _ member inWindow =>
      packedWindowIncidence residual window markedAt hubAt remainderSide obstruction
        hubMember entry member inWindow,
    directCycleFree (ctx := ctx) accepted⟩

/-! ### Clause (d): the replacement obstruction

The manuscript reads "the candidate ledger entries and their carriers as local
target-response coordinates of the boundaried support `Z`".  Those coordinates
are not new data: they are `Carrier` -- the disjoint union of the two carrier
supports of `def:typeB-ledger-carriers` -- and the coordinate family of `Z(𝒪)`
is the family of `CandidateEntry.carriers` of the entries chosen at the demands
of `𝒪`.  An *attempted identification* of two such coordinates is an arbitrary
map `value : Carrier ctx.G → Value` on that family, and the manuscript's four
alternatives are exactly the two constructors of `Core.AdmissibleQuotient` read
against the minimality certificate the minimal counterexample already carries:

* *target-defective*, by `lem:context-universality`.  An identification that is
  distinguished by some outside context is not target-complete, so it supplies
  no certified representative; if it also identifies two distinct coordinates it
  is not label-injective either, so it is not an `AdmissibleQuotient` at all.
  This is `isEmpty_admissibleQuotient_of_identifies`.
* *target-complete compression with a smaller proper boundaried representative
  of the same boundary degree profile*, forbidden by `cor:uncompressible`.  This
  is the `Core.AdmissibleQuotient.representative` constructor, whose payload
  `Baseline subgraph.value` on a `ProperSubgraph` of `G` is refuted by
  `NoProperBaselineCertificate.excludes`, the minimality certificate the minimal
  counterexample already carries.
* *valid only after adjoining a larger support*, proper case, forbidden by
  `lem:proper-smearing`.  An enlarged proper support is again a `ProperSubgraph`
  of `G` retaining the baseline, hence the same `representative` payload and the
  same refutation.
* *valid only after adjoining a larger support*, whole-graph case, forbidden by
  `lem:no-silent-global-smearing`.  This is
  `Core.AdmissibleQuotient.not_rankReducing_of_excluded`, whose docstring records
  it as that lemma's case-(c) conclusion in full, together with its rank form
  `rank_eq_card_of_excluded` (`lem:full-rank`): the ledger coordinate family is
  finite, so "not rank-reducing" is the exact count `rank = |Carrier|`.

When none of the alternatives applies the coordinate stays in the obstruction:
the carrier conflict `𝒪` was extracted for is still there, and the surviving
identification separates its shared carrier from every other coordinate.  No
hypothesis is added -- `NoProperBaselineCertificate` is a framework certificate,
exactly as clause (b)'s `DeletionCriticalityCertificate` is -- and no second
notion of carrier, identification or quotient is introduced. -/

/-- The carrier conflict of a minimal Type B overlap obstruction, made explicit
at one choice of candidate entries: two distinct demands of `𝒟` carry candidate
entries sharing a ledger carrier.  This is `noDisjointChoice` read pointwise, in
the shape of `TypeBExclusion.SharedCarrier`; no second notion of carrier conflict
is introduced. -/
theorem exists_conflictingCarrier {residual : Residual object}
    {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger)
    (entry : ∀ h : object.Vertex, h ∈ obstruction.demands → CandidateEntry residual ledger h) :
    ∃ h, ∃ hMember : h ∈ obstruction.demands,
      ∃ h', ∃ h'Member : h' ∈ obstruction.demands, ∃ carrier : Carrier object,
        h ≠ h' ∧ carrier ∈ (entry h hMember).carriers ∧
          carrier ∈ (entry h' h'Member).carriers := by
  by_contra noConflict
  refine obstruction.noDisjointChoice ⟨entry, ?_⟩
  intro h hMember h' h'Member distinct
  rw [Finset.disjoint_left]
  intro carrier leftMember rightMember
  exact noConflict ⟨h, hMember, h', h'Member, carrier, distinct, leftMember, rightMember⟩

/-- **The routing half of `lem:typeB-global-local-reflection` (d).**  An attempted
identification of two *distinct* ledger-response coordinates of `Z(𝒪)` -- an
identification that would remove a carrier conflict -- is never admissible.

This is the manuscript's case exhaustion, contrapositive: such an identification
is not label-injective, so the only remaining alternative is the certified
smaller proper representative of `cor:uncompressible` /`lem:proper-smearing` /
`lem:no-silent-global-smearing`, and `NoProperBaselineCertificate.excludes`
refutes that.  What is left is the target-defective alternative of
`lem:context-universality`: the identification is distinguished by some outside
context and is not target-complete at all. -/
theorem isEmpty_admissibleQuotient_of_identifies
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (minimality : NoProperBaselineCertificate ctx)
    {Value : Type w} {value : Carrier ctx.G → Value}
    {carrier carrier' : Carrier ctx.G} (distinct : carrier ≠ carrier')
    (identified : value carrier = value carrier') :
    IsEmpty (Core.AdmissibleQuotient
      (fun subgraph : ProperSubgraph ctx.G => subgraph.value)
      Baseline (Carrier ctx.G) Value value) :=
  ⟨fun quotient =>
    distinct (quotient.injective_of_excluded minimality.excludes identified)⟩

/-- **`lem:typeB-global-local-reflection` (d): replacement obstruction.**  Every
quotient or identification among the ledger-response coordinates of `Z(𝒪)` that
survives the manuscript's alternatives -- i.e. every `Core.AdmissibleQuotient` on
the carrier family of `def:typeB-ledger-carriers` -- is label-injective, has full
rank, and therefore removes no carrier conflict: the shared carrier of the
obstruction stays a coordinate of the obstruction, separated by the
identification from every other coordinate.

The three forbidden alternatives are the `representative` constructor of
`Core.AdmissibleQuotient` -- the target-complete compression by a smaller proper
boundaried representative of `cor:uncompressible`, and the proper and whole-graph
delocalizations of `lem:proper-smearing` and `lem:no-silent-global-smearing` --
all refuted by `NoProperBaselineCertificate.excludes`; the fourth, the
target-defective alternative of `lem:context-universality`, is
`isEmpty_admissibleQuotient_of_identifies`.  The full-rank conclusion is
`Core.AdmissibleQuotient.rank_eq_card_of_excluded`, i.e. `lem:full-rank` on this
coordinate family, and it is exactly the "no silent global rank reduction"
conclusion of `lem:no-silent-global-smearing`.

Nothing here is a hypothesis: `minimality` is the framework certificate the
minimal counterexample already carries, and the coordinate family is the file's
own `Carrier` / `CandidateEntry.carriers`. -/
theorem replacementObstruction
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (minimality : NoProperBaselineCertificate ctx)
    {residual : Residual ctx.G} {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger)
    (entry : ∀ h : ctx.G.Vertex, h ∈ obstruction.demands → CandidateEntry residual ledger h)
    {Value : Type w} {value : Carrier ctx.G → Value}
    (quotient : Core.AdmissibleQuotient
      (fun subgraph : ProperSubgraph ctx.G => subgraph.value)
      Baseline (Carrier ctx.G) Value value) :
    Function.Injective value ∧
      Core.AdmissibleQuotient.rank value = Nat.card (Carrier ctx.G) ∧
      ∃ h, ∃ hMember : h ∈ obstruction.demands,
        ∃ h', ∃ h'Member : h' ∈ obstruction.demands, ∃ carrier : Carrier ctx.G,
          h ≠ h' ∧ carrier ∈ (entry h hMember).carriers ∧
            carrier ∈ (entry h' h'Member).carriers ∧
            ∀ other : Carrier ctx.G, value carrier = value other → carrier = other := by
  letI : Fintype ctx.G.Vertex := @FinEnum.instFintype _ ctx.G.vertices
  have injective : Function.Injective value :=
    quotient.injective_of_excluded minimality.excludes
  refine ⟨injective,
    (Core.AdmissibleQuotient.rank_eq_card_iff_injective value).2 injective, ?_⟩
  obtain ⟨h, hMember, h', h'Member, carrier, distinct, leftMember, rightMember⟩ :=
    exists_conflictingCarrier obstruction entry
  exact ⟨h, hMember, h', h'Member, carrier, distinct, leftMember, rightMember,
    fun _other identified => injective identified⟩

/-- **`lem:typeB-global-local-reflection` (e): minimal overlap.**  Every proper
connected sub-obstruction of `𝒪` has a refined disjoint ledger.  This is the
minimality clause of `def:typeB-overlap-obstruction`. -/
theorem minimalOverlap {residual : Residual object} {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger)
    {sub : Finset object.Vertex} (proper : sub ⊂ obstruction.demands)
    (nonempty : sub.Nonempty) :
    HasDisjointChoice residual ledger sub :=
  obstruction.minimal proper nonempty

/-! ### The reflection bundle -/

/-- **`lem:typeB-global-local-reflection`**, manuscript node `[73]`, assembled:
the global constraints a minimal Type B overlap obstruction inherits on its
overlap support `Z(𝒪)`.

* (a) *contextual dyadic safety* -- no cycle of `G` meeting `V(Z)` has an
  accepted (power-of-two) length (`contextualDyadicSafety`);
* (b) *high-degree separation* -- the high-degree fan centres in `Z` are
  independent and every neighbour of such a centre is cubic
  (`highDegreeSeparation`);
* (c) *window compatibility* -- every packed-window incidence of `Z` is an
  `R`--`W` edge carried by a remainder-side fan neighbour of `Z`, and the
  same-window and two-window labels satisfy the direct-cycle exclusions
  (`windowCompatibility`);
* (d) *replacement obstruction* -- every admissible identification among the
  ledger-response coordinates of `Z` is label-injective and of full rank, so no
  quotient, compression or delocalization removes the carrier conflict and the
  shared coordinate stays in the obstruction (`replacementObstruction`);
* (e) *minimal overlap* -- every proper nonempty sub-obstruction has a refined
  disjoint ledger (`minimalOverlap`).

Nothing here is a hypothesis: the inputs are `ctx.avoids`, the
deletion-criticality certificate (the graph reading of Core's nodes
`[9]`--`[10]` ledger entries, `Graph.deletionCriticalityOfLedger`), the
recording convention of `def:typeB-window-incidence-profile`, the
no-proper-baseline certificate the minimal counterexample already carries, and
the minimality field of `def:typeB-overlap-obstruction`. -/
theorem globalLocalReflection
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {criticality : DeletionCriticalityProfile Baseline}
    (accepted : TypeBClosure.AcceptedLengths LengthOK)
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (certificate : DeletionCriticalityCertificate criticality ctx)
    (thresholdThree : criticality.threshold = 3)
    (minimality : NoProperBaselineCertificate ctx)
    {residual : Residual ctx.G} {ledger : LoadCapacityProfile}
    (obstruction : OverlapObstruction residual ledger)
    (window : Finset ctx.G.Vertex) (markedAt : ctx.G.Vertex → Marked ctx.G)
    (hubAt : ∀ h ∈ residual.centers, (markedAt h).fan.hub = h)
    (remainderSide : ∀ h ∈ residual.centers, ∀ u : ctx.G.Vertex,
      ctx.G.graph.Adj h u → u ∉ window) :
    (∀ base : ctx.G.Vertex, ∀ cycle : ctx.G.graph.Walk base base, cycle.IsCycle →
        ∀ vertex ∈ overlapSupport obstruction, vertex ∈ cycle.support →
          ¬ LengthOK cycle.length) ∧
      ((∀ h ∈ overlapSupport obstruction, ∀ h' ∈ overlapSupport obstruction,
            4 ≤ ctx.G.degree h → 4 ≤ ctx.G.degree h' → ¬ ctx.G.graph.Adj h h') ∧
          (∀ h ∈ overlapSupport obstruction, 4 ≤ ctx.G.degree h →
            ∀ u : ctx.G.Vertex, ctx.G.graph.Adj h u → ctx.G.degree u = 3)) ∧
      ((∀ h ∈ obstruction.demands, ∀ entry : CandidateEntry residual ledger h,
            ∀ incidence ∈ entry.chosen, incidence.2 ∈ window →
              (fanProfile residual window (markedAt h)).IsWindowIncidence
                  incidence.1 incidence.2 ∧
                incidence.1 ∈ (fanProfile residual window (markedAt h)).remainder ∧
                incidence.1 ∈ overlapSupport obstruction) ∧
          TypeBClosure.DirectCycleFree ctx.G) ∧
      (∀ (Value : Type w) (value : Carrier ctx.G → Value),
          Core.AdmissibleQuotient
              (fun subgraph : ProperSubgraph ctx.G => subgraph.value)
              Baseline (Carrier ctx.G) Value value →
            ∀ entry : ∀ h : ctx.G.Vertex,
                h ∈ obstruction.demands → CandidateEntry residual ledger h,
              Function.Injective value ∧
                Core.AdmissibleQuotient.rank value = Nat.card (Carrier ctx.G) ∧
                ∃ h, ∃ hMember : h ∈ obstruction.demands,
                  ∃ h', ∃ h'Member : h' ∈ obstruction.demands,
                    ∃ carrier : Carrier ctx.G, h ≠ h' ∧
                      carrier ∈ (entry h hMember).carriers ∧
                        carrier ∈ (entry h' h'Member).carriers ∧
                        ∀ other : Carrier ctx.G,
                          value carrier = value other → carrier = other) ∧
      (∀ sub : Finset ctx.G.Vertex, sub ⊂ obstruction.demands → sub.Nonempty →
        HasDisjointChoice residual ledger sub) :=
  ⟨fun _ cycle isCycle => contextualDyadicSafety obstruction cycle isCycle,
    highDegreeSeparation certificate thresholdThree obstruction,
    windowCompatibility accepted obstruction window markedAt hubAt remainderSide,
    fun _ _ quotient entry => replacementObstruction minimality obstruction entry quotient,
    fun _ proper nonempty => minimalOverlap obstruction proper nonempty⟩

/-! ## `prop:typeB-global-local-bridge` -/

/-- **`prop:typeB-global-local-bridge`**, manuscript node `[73]`.

* *Forward.*  Every disjoint-carrier Type B bridge residual -- a support on which
  the disjoint-carrier part of B2 fails -- is represented by a minimal Type B
  overlap obstruction, which then satisfies clauses (a), (b), (c), (d) and (e) of
  `lem:typeB-global-local-reflection` (`contextualDyadicSafety`,
  `highDegreeSeparation`, `windowCompatibility`, `replacementObstruction`,
  `minimalOverlap`), assembled in `globalLocalReflection`.  The failure also
  exhibits the repository's explicit shared carrier
  `TypeBExclusion.SharedCarrier`, so the residual produced here is the one the
  Type B exclusion already retains.
* *Window compatibility.*  The third component below is the graph-layer half of
  clause (c), stated for *every* overlap obstruction of the support: each
  packed-window incidence of `Z(𝒪)` is an edge between the remainder `R = G - W`
  and the packed-window union `W`, owned by a remainder-side fan neighbour that
  is itself a vertex of `Z(𝒪)`.  Its direct-cycle half needs the ambient minimal
  counterexample and is `windowCompatibility`.
* *Converse.*  If the support has no fan-certificate residual centre -- the
  positive datum `markedAt`, which supplies a candidate entry at every assigned
  centre -- and carries no overlap obstruction, then B2 holds there: the whole
  demand family has a disjoint refined Type B ledger and that ledger is maximal.
  The hybrid B1 ledger of `lem:typeB-hybrid-B1` is available at every centre
  simultaneously, which is what `prop:typeB-bridge-reduction` consumes.

There is no hypothesis of the form "configuration `C` does not occur": the
obstruction is an *alternative*, and the B1 clause is produced, not assumed. -/
theorem typeBGlobalLocalBridge (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (window : Finset object.Vertex) (markedAt : object.Vertex → Marked object)
    (hubAt : ∀ h ∈ residual.centers, (markedAt h).fan.hub = h)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (fanInCore : ∀ h ∈ residual.centers, neighbourRim object h ⊆ residual.core)
    (remainderSide : ∀ h ∈ residual.centers, ∀ u : object.Vertex,
      object.graph.Adj h u → u ∉ window) :
    (¬ HasDisjointChoice residual ledger residual.centers →
        Nonempty (OverlapObstruction residual ledger) ∧ SharedCarrier residual) ∧
      (IsEmpty (OverlapObstruction residual ledger) →
        RefinedSupportLedger residual ledger ∧
          ∀ h ∈ residual.centers,
            (fanProfile residual window (markedAt h)).closedNeighbourDeficit ledger
              ≤ (fanProfile residual window (markedAt h)).hybridCapacity ledger) ∧
      (∀ obstruction : OverlapObstruction residual ledger,
        ∀ h ∈ obstruction.demands, ∀ entry : CandidateEntry residual ledger h,
          ∀ incidence ∈ entry.chosen, incidence.2 ∈ window →
            (fanProfile residual window (markedAt h)).IsWindowIncidence
                incidence.1 incidence.2 ∧
              incidence.1 ∈ (fanProfile residual window (markedAt h)).remainder ∧
              incidence.1 ∈ overlapSupport obstruction) := by
  have centresHigh : ∀ h ∈ residual.centers, 4 ≤ object.degree h :=
    fun h member => (normal h member).high
  have entry : ∀ h : object.Vertex, h ∈ residual.centers → CandidateEntry residual ledger h :=
    fun h member =>
      hybridEntry residual ledger window (markedAt h) (hubAt h member) (normal h member)
        centresHigh (fanInCore h member) (remainderSide h member)
  refine ⟨?_, ?_, ?_⟩
  · intro failure
    exact ⟨bridgeToOverlap residual ledger failure,
      sharedCarrier_of_not_hasDisjointChoice residual ledger entry failure⟩
  · intro noObstruction
    refine ⟨refinedSupportLedger_of_isEmpty residual ledger noObstruction normal, ?_⟩
    intro h member
    have normalAt : NormalForm object (fanProfile residual window (markedAt h)).marked.fan.hub := by
      show NormalForm object (markedAt h).fan.hub
      rw [hubAt h member]
      exact normal h member
    exact (Profile.typeBHybridB1 (fanProfile residual window (markedAt h)) ledger
      normalAt).1
  · intro obstruction _ hubMember chosenEntry _ member inWindow
    exact packedWindowIncidence residual window markedAt hubAt remainderSide obstruction
      hubMember chosenEntry member inWindow

/-! ## How clauses (c) and (d) are proved

Clause (c), *window compatibility*, is proved above as `windowCompatibility`,
with the two displayed arithmetic exclusions as `sameWindowExclusion` and
`twoWindowExclusion`; it is carried by the reflection bundle
`globalLocalReflection` and its graph-layer half by `typeBGlobalLocalBridge`.
Both halves of the manuscript's proof map onto existing objects, and neither uses
an estimate.

* *"Each packed-window incidence is by definition an edge between `R = G - W` and
  the packed window union `W`."*  That is `TypeBFanClosedPorts.Profile`'s own
  `IsWindowIncidence` -- `u ∉ W`, `u z ∈ E(G)`, `z ∈ W` -- so the clause is the
  **membership** `packedWindowIncidence`, proved from
  `CandidateEntry.chosen_owned`, `CandidateEntry.assigned_rim` and the recording
  convention of `def:typeB-window-incidence-profile` that
  `typeBGlobalLocalBridge` already carries.  *"Such edges are exactly the
  incidence supply counted in `lem:stub-positive`"* names the supply that
  membership lands in; the `15p₁₃ + o(n)` figure is that supply's asymptotic
  *size*, and the manuscript's proof of clause (c) does not use it.  Nothing here
  states, uses or assumes it, and no second window, incidence or carrier type is
  introduced: `W` is `Profile.window`, `R` is `Profile.remainder`, the incidences
  are `Profile.incidences` as chosen by `CandidateEntry.chosen`, and `Z(𝒪)` is
  `overlapSupport`.

* *"If same-window or two-window labels violated the displayed arithmetic
  exclusions, the corresponding direct-cycle lemma would produce a power-of-two
  cycle meeting `Z`, contradicting (a)."*  That is `directCycleFree`:
  `TypeBClosure.DirectCycleConfiguration` collects the four configurations of
  `lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`,
  `TypeBClosure.hasCycleWithLength_of_directCycleConfiguration` turns any of them
  into a power-of-two cycle, and `ctx.avoids` -- the datum clause (a)
  `contextualDyadicSafety` reads -- forbids it, giving
  `TypeBClosure.DirectCycleFree`, i.e. `def:direct-cycle-free-closed-pair`.

Clause (d), the *replacement obstruction*, is `replacementObstruction`, with its
routing half `isEmpty_admissibleQuotient_of_identifies` and the explicit carrier
conflict `exists_conflictingCarrier`; it is carried by the reflection bundle
`globalLocalReflection`.  Every step of the manuscript's proof maps onto an
existing object, and no new coordinate, identification, quotient or carrier is
introduced.

* *"Regard the candidate ledger entries and their carriers as local
  target-response coordinates of the boundaried support `Z`."*  Those coordinates
  are `Carrier` -- `def:typeB-ledger-carriers`' disjoint union of the vertex
  supports `Residual.envelopeBlock` collects and the half-edge supports
  `TypeBFanClosedPorts.Profile.incidences` collects -- and the coordinate family
  of `Z(𝒪)` is the family of `CandidateEntry.carriers` of the entries chosen at
  the demands of `𝒪`.  An attempted identification is an arbitrary map
  `value : Carrier ctx.G → Value` on that family; `Value` and `value` are
  universally quantified, so nothing is fixed or invented.  This is exactly the
  instantiation `Core.AdmissibleQuotient`'s own module note flags as "genuinely
  problem-specific: which concrete type plays `Coordinate` and which concrete map
  plays `value`".

* *"If an attempted identification of two such coordinates is distinguished by
  some outside context, it is target-defective by `lem:context-universality`."*
  A target-defective identification is not target-complete, so it supplies no
  certified representative; if it also identifies two distinct coordinates it is
  not label-injective either, so it inhabits neither constructor of
  `Core.AdmissibleQuotient` -- that is
  `isEmpty_admissibleQuotient_of_identifies`, the exact contrapositive of the
  manuscript's routing.

* *"If the identification is target-complete and supplies a smaller proper
  boundaried representative with the same boundary degree profile, it is a
  target-complete compression and is forbidden by `cor:uncompressible`."*  That
  witness is the `Core.AdmissibleQuotient.representative` constructor, whose
  payload is `Baseline subgraph.value` for a `ProperSubgraph` of `G`;
  `NoProperBaselineCertificate.excludes` refutes it.  That certificate is not a
  hypothesis: it is the minimality certificate the minimal counterexample already
  carries.

* *"If the identification becomes valid only after adjoining a larger support,
  the proper case is forbidden by `lem:proper-smearing` and the whole-graph case
  by `lem:no-silent-global-smearing`."*  An enlarged proper support is again a
  `ProperSubgraph` of `G` retaining the baseline, hence the same `representative`
  payload and the same refutation; the whole-graph case is
  `Core.AdmissibleQuotient.not_rankReducing_of_excluded`, whose docstring records
  it as `lem:no-silent-global-smearing`'s case-(c) conclusion in full, together
  with its sharp finite rank form `rank_eq_card_of_excluded` (`lem:full-rank`).
  The ledger coordinate family is finite -- `Carrier` is built from
  `FiniteObject.Vertex` -- so "not rank-reducing" is the exact count
  `rank value = |Carrier ctx.G|`, which is the second conclusion of
  `replacementObstruction`.

* *"When none of these alternatives applies, no quotient, compression or
  delocalization removes the carrier conflict, so the coordinate stays in the
  overlap obstruction."*  The conflict itself is `exists_conflictingCarrier`, the
  pointwise reading of `OverlapObstruction.noDisjointChoice` in the shape of
  `TypeBExclusion.SharedCarrier`; the surviving identification separates that
  shared carrier from every other coordinate, which is the third conclusion of
  `replacementObstruction`.

All five clauses (a), (b), (c), (d), (e) are proved above; their inputs --
`ctx.avoids`, the deletion-criticality certificate, the recording convention of
`def:typeB-window-incidence-profile` together with the direct-cycle constructions
of node `[72]`, the no-proper-baseline certificate, and the minimality field of
`def:typeB-overlap-obstruction` -- are all present. -/

/-! ## Non-vacuity

Every notion above is realised on the explicit finite graph already used by
`TypeBFanClosedPorts`, `TypeBBridgeResidual` and `TypeBExclusion`: a degree-four
centre with four cubic neighbours carrying private shoulder pairs, on the
assigned support that stops at the closed neighbourhood of the centre.  There
the fan is certificate-closed, so `certificateClosedEntry` produces a genuine
candidate ledger entry, the one-demand family has a disjoint refined ledger, no
overlap obstruction exists, and `typeBMaximalCompletion` fires and returns a
maximal ledger. -/

namespace Witness

open Hypostructure.Graph.TypeBFanClosedPorts.Witness
open Hypostructure.Graph.TypeBExclusion.Witness

theorem closed_centresHigh :
    ∀ h ∈ closedResidual.centers, 4 ≤ fanObject.degree h := by
  intro h member
  rw [closed_centers, Finset.mem_singleton] at member
  subst member
  rw [degree_hub]

theorem closed_normal :
    ∀ h ∈ closedResidual.centers, NormalForm fanObject h := by
  intro h member
  rw [closed_centers, Finset.mem_singleton] at member
  subst member
  exact fanNormalForm

/-- A genuine candidate Type B ledger entry of `def:typeB-candidate-ledger` (a)
on the witness. -/
noncomputable def closedEntry (ledger : LoadCapacityProfile) :
    CandidateEntry closedResidual ledger hub :=
  certificateClosedEntry closedResidual ledger fanNormalForm closed_centresHigh
    closed_rim_subset_core (closed_isCertificateClosed ledger)

/-- The one-demand family of the witness carries a disjoint refined Type B
ledger. -/
theorem closed_hasDisjointChoice (ledger : LoadCapacityProfile) :
    HasDisjointChoice closedResidual ledger closedResidual.centers := by
  refine ⟨fun h member => ?_, ?_⟩
  · rw [closed_centers, Finset.mem_singleton] at member
    subst member
    exact closedEntry ledger
  · intro h member h' member' distinct
    rw [closed_centers, Finset.mem_singleton] at member member'
    exact absurd (member.trans member'.symm) distinct

/-- The witness carries no Type B overlap obstruction: the only nonempty
subfamily of its demands is the whole family, and that family has a disjoint
refined ledger. -/
theorem closed_noObstruction (ledger : LoadCapacityProfile) :
    IsEmpty (OverlapObstruction closedResidual ledger) := by
  refine ⟨fun obstruction => ?_⟩
  have subset := obstruction.demands_subset
  rw [closed_centers] at subset
  rcases Finset.subset_singleton_iff.1 subset with empty | full
  · obtain ⟨vertex, member⟩ := obstruction.demands_nonempty
    rw [empty] at member
    exact absurd member (Finset.notMem_empty vertex)
  · refine obstruction.noDisjointChoice ?_
    rw [full]
    refine hasDisjointChoice_mono closedResidual ledger ?_
      (closed_hasDisjointChoice ledger)
    rw [closed_centers]

/-- **`lem:typeB-maximal-completion` fires on a concrete graph.**  The witness
support has no overlap obstruction, so its Type B demands admit a maximal
disjoint refined Type B ledger; the demand family it returns really does contain
the assigned centre, so the conclusion is not reached vacuously. -/
theorem maximalCompletion_fires (ledger : LoadCapacityProfile) :
    ∃ demands : Finset fanObject.Vertex,
      hub ∈ demands ∧ demands ⊆ closedResidual.centers ∧
        HasDisjointChoice closedResidual ledger demands ∧
        IsMaximal closedResidual demands := by
  obtain ⟨demands, extends', subset, choice, maximal⟩ :=
    typeBMaximalCompletion closedResidual ledger (closed_noObstruction ledger)
      closed_normal (start := (∅ : Finset fanObject.Vertex)) (Finset.empty_subset _)
  refine ⟨demands, ?_, subset, choice, maximal⟩
  have full := (isMaximal_iff closedResidual subset closed_normal).1 maximal
  exact full hub_mem_closed_centers

/-- **B2 holds on the witness**, in the packaged form of
`def:typeB-bridge-statements`: a disjoint refined ledger for the whole demand
family, and maximality. -/
theorem refinedSupportLedger_fires (ledger : LoadCapacityProfile) :
    RefinedSupportLedger closedResidual ledger :=
  refinedSupportLedger_of_isEmpty closedResidual ledger (closed_noObstruction ledger)
    closed_normal

end Witness

end Hypostructure.Graph.TypeBOverlapObstruction
