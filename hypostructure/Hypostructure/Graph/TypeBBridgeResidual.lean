import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Graph.TypeBProfileSchedule

/-!
# The Type B bridge residual mass and its deficit bound

This file is the graph-mathematics content of manuscript nodes `[75]`/`[84]`
(`fanmass`) of `original_erdos_64_proof.tex`:

* `def:typeB-residual-mass` -- `Residual`, the enumeration `bridgeResiduals`
  carrying `𝒳_B`, `residualMass` (`M_B`), `centerOccurrences` (`H_B`),
  `surplusMass` (`S_B`);
* `def:canonical-decomp` -- `bridgeResiduals` itself: one canonical assigned
  support per centre carrying ambient surplus, in the object's own vertex scan
  order, so that every surplus unit is assigned to exactly one member;
* `lem:typeB-bridge-deficit-bound` -- `envelopeAllowance_le_eight_surplus`,
  `residualCoreCharge_sub_eight_surplus_le_netCharge` and
  `negativePart_le_eight_surplus`;
* `prop:typeB-bridge-sublinear` -- `typeBBridgeSublinear`.

Everything is an observable of the object at hand.  A `Residual` carries only
two vertex supports: the counted core `Y_X` of `def:typeB-assigned-ledger` and
the assigned high-degree fan centres `H_X`.  The internal degree `d_{Y_X}`, the
deficiency `δ⁺_X`, the vertex and centre charges `ch_X`, the augmented ledger
`Ĉh_B(X)`, the net charge `No(X)` and its negative part `No_-(X)` are all
computed from those two supports and the object's own neighbour schedules; the
global surplus `σ(G) = Σ_v (d_G(v) - 3)` is likewise computed from the object's
own vertex schedule.  No parameter stands for a global property.

The collection `𝒳_B` is not free data either.  `def:canonical-decomp` assigns
each ambient surplus unit `d_G(h) - 3` to exactly one piece of the
decomposition, and `def:decorated-typeB-envelope-support` partitions the handoff
centres among the incidence components; both are performed here by *deriving the
collection from the object*, in exactly the shape
`TypeBProfileSchedule.profileCandidates` takes at node `[74]` and
`TypeBDegreeFour.degreeFourCores` takes at node `[79]`: `bridgeResiduals` lists
one canonical assigned support per centre of positive surplus, in the object's
own vertex scan order.  Because a centre is enumerated once, disjointness of the
assigned centre sets (`bridgeResiduals_pairwise`) is
`FiniteObject.orderedVertices_nodup`, the manuscript's "the same vertex may
occur at most twice in `H_B(𝒳_B)`" is `count_centerOccurrences_le_two`, and
nothing is lost: `centerOccurrences_eq_bridgeCentres` says the assigned centres
of the collection are precisely the vertices carrying ambient surplus.

No hypothesis anywhere in this file asserts the absence of a structure.  The
only ambient structural input is `TypeBOpenPorts.NormalForm`, supplied as an
explicit argument exactly as in `TypeBOpenPorts.heavyCenterTriangularAlternative`
and `TypeBFanClosedPorts.fanClosedPortTypeBRouting`; the four-cycle absence
behind it is read off the incoming residual by
`TypeBOpenPorts.LocalHypotheses.normalForm` (`ctx.avoids`).  In particular the
manuscript's route-8 clause of `lem:typeB-bridge-deficit-bound` -- "the
non-window core left after deleting the Type B fan envelopes contains no
admissible route-8 Type A residual profile" -- is *not* a hypothesis here.  It
is replaced by the residual-core charge `residualCoreCharge`, which appears as
an explicit term of the conclusion of
`residualCoreCharge_sub_eight_surplus_le_netCharge`, exactly the way
`lem:typeB-bridge-with-route8-core` carries `-D_A(𝒜_X)` in its conclusion
instead of assuming the absence.

All rational quantities are over `ℚ`, consistent with
`TypeBFanClosedPorts.Profile.closedNeighbourDeficit`.

## The discharge rate is read, never written

The per-vertex discharge rate `α` of `lem:typeA-unsaturated-discharge` is a
*chosen* proof-design parameter, so it is not a literal here: every charge below
reads `ReceiverLoad.LoadCapacityProfile.dischargeRate`, that is `1/α` from the
registered presentation field `loadMultiplier`.  At the registered profile
`loadMultiplier = 4` each statement is verbatim the manuscript's, and the only
property of the rate any proof in this file uses is
`dischargeRate_le_one` (`α ≤ 1`), which holds for every profile.
-/

namespace Hypostructure.Graph.TypeBBridgeResidual

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts
open Hypostructure.Graph.TypeBProfileSchedule (canonicalEnvelope
  mem_canonicalEnvelope_iff shoulder_mem_canonicalEnvelope)
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u

variable {object : FiniteObject.{u}}

/-! ## Decidability of the two local predicates

Both predicates quantify over the finite vertex type with decidable adjacency,
so both are decidable; this is what lets `d_{Y_X}` and `c_h` be honest
`Finset.card`s. -/

instance decidableAdjFrom (object : FiniteObject.{u}) (source : object.Vertex) :
    DecidablePred fun target => object.graph.Adj source target :=
  object.decideAdj source

instance decidableIncidencesAssigned (object : FiniteObject.{u})
    (support : Finset object.Vertex) (hub vertex : object.Vertex) :
    Decidable (∀ w : object.Vertex, object.graph.Adj vertex w → w ≠ hub →
      w ∈ support) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  infer_instance

/-! ## The global surplus `σ(G)` -/

/-- **`σ(G)` at the registered baseline.**
`σ_k(G) = Σ_{v ∈ V(G)} (d_G(v) - k)`, with `k` read from the presentation
record the problem registers as its `Core.Problem.presentation`, never written
as a literal.  This is the generic form of `prop:typeB-bridge-sublinear`'s
global surplus: nothing about the definition mentions the cubic case, and the
statements that quantify over an arbitrary registered presentation are stated
with this one. -/
noncomputable def globalSurplusOf (profile : LoadCapacityProfile)
    (object : FiniteObject.{u}) : ℚ :=
  ∑ v ∈ object.vertexFinset,
    ((object.degree v : ℚ) - (profile.baselineDegree : ℚ))

/-- The positive part of the registered-baseline global surplus,
`Σ_v max{0, d_G(v) - k}`. -/
noncomputable def globalSurplusPosOf (profile : LoadCapacityProfile)
    (object : FiniteObject.{u}) : ℚ :=
  ∑ v ∈ object.vertexFinset,
    max 0 ((object.degree v : ℚ) - (profile.baselineDegree : ℚ))

theorem globalSurplusPosOf_nonneg (profile : LoadCapacityProfile) :
    0 ≤ globalSurplusPosOf profile object :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

/-- On the standing minimum-degree invariant of the *registered* baseline, the
positive part is the registered-baseline surplus itself. -/
theorem globalSurplusPosOf_eq_globalSurplusOf (profile : LoadCapacityProfile)
    (minDegree : ∀ v : object.Vertex, profile.baselineDegree ≤ object.degree v) :
    globalSurplusPosOf profile object = globalSurplusOf profile object := by
  refine Finset.sum_congr rfl ?_
  intro v _
  have : ((profile.baselineDegree : Nat) : ℚ) ≤ (object.degree v : ℚ) := by
    exact_mod_cast minDegree v
  exact max_eq_right (by linarith)

/-- `σ(G) = Σ_{v ∈ V(G)} (d_G(v) - 3)`, written exactly as in
`prop:typeB-bridge-sublinear`, and computed from the object's own vertex
schedule.  This is the cubic instance of `globalSurplusOf`
(`globalSurplusOf_eq_globalSurplus`); the Type B charge algebra below is
written at the cubic geometry of `TypeBOpenPorts.NormalForm`, so the ledger
statements are stated with this spelling. -/
noncomputable def globalSurplus (object : FiniteObject.{u}) : ℚ :=
  ∑ v ∈ object.vertexFinset, ((object.degree v : ℚ) - 3)

/-- The positive part of the global surplus, `Σ_v max{0, d_G(v) - 3}`.  On the
standing branch `δ(G) ≥ 3` this is `σ(G)` itself
(`globalSurplusPos_eq_globalSurplus`). -/
noncomputable def globalSurplusPos (object : FiniteObject.{u}) : ℚ :=
  ∑ v ∈ object.vertexFinset, max 0 ((object.degree v : ℚ) - 3)

theorem globalSurplusPos_nonneg : 0 ≤ globalSurplusPos object :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

/-- With the standing minimum-degree invariant `δ(G) ≥ 3`, the positive part is
the manuscript's `σ(G)`. -/
theorem globalSurplusPos_eq_globalSurplus
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v) :
    globalSurplusPos object = globalSurplus object := by
  refine Finset.sum_congr rfl ?_
  intro v _
  have : (3 : ℚ) ≤ (object.degree v : ℚ) := by exact_mod_cast minDegree v
  exact max_eq_right (by linarith)

/-- **The cubic instance.**  At a presentation whose registered baseline is the
problem's cubic minimum degree, the registered-baseline surplus is exactly the
manuscript's `σ(G)`, so the existing ledger spelling is a *reading* of the
presentation rather than a second notion. -/
theorem globalSurplusOf_eq_globalSurplus (profile : LoadCapacityProfile)
    (cubic : profile.baselineDegree = 3) :
    globalSurplusOf profile object = globalSurplus object := by
  unfold globalSurplusOf globalSurplus
  rw [cubic]
  norm_num

/-- The positive-part cubic instance. -/
theorem globalSurplusPosOf_eq_globalSurplusPos (profile : LoadCapacityProfile)
    (cubic : profile.baselineDegree = 3) :
    globalSurplusPosOf profile object = globalSurplusPos object := by
  unfold globalSurplusPosOf globalSurplusPos
  rw [cubic]
  norm_num

/-- `ch_X(h) = -(d_G(h) - 3) - α`, the assigned centre charge of
`def:typeB-assigned-ledger`.  It depends only on the ambient degree of the
centre and on the chosen discharge rate `α = profile.dischargeRate`, so it is
stated for the object and the presentation profile rather than for one
support. -/
noncomputable def centerCharge (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) (h : object.Vertex) : ℚ :=
  -((object.degree h : ℚ) - 3) - profile.dischargeRate

/-! ## `def:typeB-assigned-ledger`: one assigned Type B support -/

/-- The data of one connected assigned Type B support `X`, in the shape used by
`def:typeB-assigned-ledger` and `def:typeB-residual-mass`:

* `core` is the counted core `Y_X = V(X)`;
* `centers` is the set `H_X` of high-degree fan centres whose surplus units are
  assigned to `X`.

There are no propositional fields: the internal degree, the deficiency, the two
charges, the augmented ledger, the net charge and the fan envelopes are all
*derived* below from these two supports and the object's own schedules. -/
structure Residual (object : FiniteObject.{u}) where
  /-- The counted core `Y_X = V(X)` of `def:typeB-assigned-ledger`. -/
  core : Finset object.Vertex
  /-- The recorded high-degree fan centres.  The assigned centres `H_X` are
  `centers ∩ core`, read off below: the canonical decomposition assigns centres
  *inside* the core it counts, so that containment is a construction, never a
  hypothesis. -/
  recordedCentres : Finset object.Vertex

namespace Residual

variable (residual : Residual object)

/-- The assigned high-degree fan centres `H_X` of `def:typeB-assigned-ledger`,
recorded inside the counted core by construction. -/
noncomputable def centers : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact residual.recordedCentres ∩ residual.core

variable {residual}

/-- `H_X ⊆ Y_X` holds by construction, so no consumer assumes it. -/
theorem centers_subset_core : residual.centers ⊆ residual.core := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro v member
  exact (Finset.mem_inter.1 member).2

variable (residual)

/-- `d_{Y_X}(y)`: the degree of `y` inside the counted core. -/
noncomputable def coreDegree (y : object.Vertex) : Nat :=
  (residual.core.filter fun w => object.graph.Adj y w).card

/-- `δ⁺_X(y) = max{0, 3 - d_{Y_X}(y)}`. -/
noncomputable def deficiency (y : object.Vertex) : ℚ :=
  max 0 (3 - (residual.coreDegree y : ℚ))

/-- `ch_X(y) = δ⁺_X(y) - α`, the ordinary vertex charge, with the discharge rate
`α` read from the presentation profile. -/
noncomputable def vertexCharge (profile : LoadCapacityProfile)
    (y : object.Vertex) : ℚ := residual.deficiency y - profile.dischargeRate

/-- `def⁺(X) = Σ_{y ∈ Y_X} δ⁺_X(y)`. -/
noncomputable def totalDeficiency : ℚ := ∑ y ∈ residual.core, residual.deficiency y

/-- `σ(X) = Σ_{h ∈ H_X} (d_G(h) - 3)`, the surplus assigned to `X`. -/
noncomputable def surplus : ℚ := ∑ h ∈ residual.centers, ((object.degree h : ℚ) - 3)

/-- `No(X) = def⁺(X) - σ(X) - α|V(X)|`. -/
noncomputable def netCharge (profile : LoadCapacityProfile) : ℚ :=
  residual.totalDeficiency - residual.surplus -
    (residual.core.card : ℚ) * profile.dischargeRate

/-- `Ĉh_B(X) = Σ_{y ∈ Y_X} ch_X(y) + Σ_{h ∈ H_X} ch_X(h)`, the augmented Type B
ledger of `def:typeB-assigned-ledger`. -/
noncomputable def augmentedLedger (profile : LoadCapacityProfile) : ℚ :=
  (∑ y ∈ residual.core, residual.vertexCharge profile y) +
    ∑ h ∈ residual.centers, centerCharge object profile h

/-- `No_-(X) = max{0, -No(X)}` of `def:typeB-residual-mass`. -/
noncomputable def negativePart (profile : LoadCapacityProfile) : ℚ :=
  max 0 (-residual.netCharge profile)

theorem negativePart_nonneg (profile : LoadCapacityProfile) :
    0 ≤ residual.negativePart profile := le_max_left _ _

/-! ### The exact accounting identity `(B-ledger)` -/

theorem sum_vertexCharge (profile : LoadCapacityProfile) :
    ∑ y ∈ residual.core, residual.vertexCharge profile y
      = residual.totalDeficiency
        - (residual.core.card : ℚ) * profile.dischargeRate := by
  unfold vertexCharge totalDeficiency
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

theorem sum_centerCharge (profile : LoadCapacityProfile) :
    ∑ h ∈ residual.centers, centerCharge object profile h
      = -residual.surplus
        - (residual.centers.card : ℚ) * profile.dischargeRate := by
  unfold centerCharge surplus
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    nsmul_eq_mul]

/-- The identity `(B-ledger)` of `def:typeB-assigned-ledger`:
`No(X) = Ĉh_B(X) + α|H_X|`. -/
theorem bLedger (profile : LoadCapacityProfile) :
    residual.netCharge profile
      = residual.augmentedLedger profile
        + (residual.centers.card : ℚ) * profile.dischargeRate := by
  unfold augmentedLedger netCharge
  rw [residual.sum_vertexCharge profile, residual.sum_centerCharge profile]
  ring

/-- The consequence recorded in `def:typeB-assigned-ledger`: a nonnegative
augmented ledger forces a nonnegative net charge. -/
theorem netCharge_nonneg_of_augmentedLedger_nonneg (profile : LoadCapacityProfile)
    (nonneg : 0 ≤ residual.augmentedLedger profile) :
    0 ≤ residual.netCharge profile := by
  rw [residual.bLedger profile]
  have : (0 : ℚ) ≤ (residual.centers.card : ℚ) * profile.dischargeRate :=
    mul_nonneg (Nat.cast_nonneg _) profile.dischargeRate_nonneg
  linarith

/-- The form of `(B-ledger)` used by the envelope estimate: the assigned centre
term `ch_X(h) + α` is exactly `-(d_G(h) - 3)`. -/
theorem netCharge_eq_sum_vertexCharge_sub_surplus (profile : LoadCapacityProfile) :
    residual.netCharge profile
      = (∑ y ∈ residual.core, residual.vertexCharge profile y)
        - residual.surplus := by
  rw [residual.sum_vertexCharge profile]
  unfold netCharge
  ring

/-! ### Elementary bounds on the two local charges -/

theorem coreDegree_le_degree (y : object.Vertex) :
    residual.coreDegree y ≤ object.degree y := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have subset : (residual.core.filter fun w => object.graph.Adj y w) ⊆
      neighbourRim object y := by
    intro w member
    exact (mem_neighbourRim object y w).2 (Finset.mem_filter.1 member).2
  have card := Finset.card_le_card subset
  rwa [card_eq_degree_of_isNeighbourhood object y (neighbourRim object y)
    (mem_neighbourRim object y)] at card

/-- A cubic fan neighbour with one incidence outside the assigned support has
internal degree at most two in the core. -/
theorem coreDegree_le_two_of_unassigned {u w : object.Vertex}
    (cubic : object.degree u = 3) (adjacent : object.graph.Adj u w)
    (outside : w ∉ residual.core) : residual.coreDegree u ≤ 2 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have subset : (residual.core.filter fun z => object.graph.Adj u z) ⊆
      (neighbourRim object u).erase w := by
    intro z member
    obtain ⟨inCore, adj⟩ := Finset.mem_filter.1 member
    refine Finset.mem_erase.2 ⟨?_, (mem_neighbourRim object u z).2 adj⟩
    rintro rfl
    exact outside inCore
  have wMem : w ∈ neighbourRim object u := (mem_neighbourRim object u w).2 adjacent
  have card := Finset.card_le_card subset
  rwa [Finset.card_erase_of_mem wMem,
    card_eq_degree_of_isNeighbourhood object u (neighbourRim object u)
      (mem_neighbourRim object u), cubic] at card

theorem deficiency_nonneg (y : object.Vertex) : 0 ≤ residual.deficiency y :=
  le_max_left _ _

/-- Every vertex charge is at least `-α`: one discharge unit is the whole
negative part a single core vertex can carry. -/
theorem neg_dischargeRate_le_vertexCharge (profile : LoadCapacityProfile)
    (y : object.Vertex) :
    -profile.dischargeRate ≤ residual.vertexCharge profile y := by
  have := residual.deficiency_nonneg y
  unfold vertexCharge
  linarith

/-- The manuscript's "a fan neighbour that is not cubic-closed has internal
degree at most `2` in the assigned envelope and contributes at least `3/4`":
generically, such a neighbour contributes at least `1 - α`. -/
theorem one_sub_dischargeRate_le_vertexCharge_of_coreDegree_le_two
    (profile : LoadCapacityProfile) {y : object.Vertex}
    (small : residual.coreDegree y ≤ 2) :
    1 - profile.dischargeRate ≤ residual.vertexCharge profile y := by
  have cast : (residual.coreDegree y : ℚ) ≤ 2 := by exact_mod_cast small
  have step : (3 : ℚ) - (residual.coreDegree y : ℚ) ≤ residual.deficiency y :=
    le_max_right _ _
  unfold vertexCharge
  linarith

theorem vertexCharge_nonneg_of_coreDegree_le_two (profile : LoadCapacityProfile)
    {y : object.Vertex} (small : residual.coreDegree y ≤ 2) :
    0 ≤ residual.vertexCharge profile y := by
  have := residual.one_sub_dischargeRate_le_vertexCharge_of_coreDegree_le_two
    profile small
  have rate := profile.dischargeRate_le_one
  linarith

/-! ### The fan envelopes (`lem:typeB-bridge-deficit-bound`, display (1)) -/

/-- `c_h`: the cubic-closed fan neighbours of the assigned centre `h`, that is
the fan neighbours whose two non-`h` incidences are assigned to the support.
This is the set counted by `c` in the proof of
`lem:typeB-bridge-deficit-bound`, and by `c(𝔉_h)` of
`def:typeB-multiclosed-residual` whenever the centre carries a fan certificate
(`closedNeighbours_eq_closedFanNeighbours`). -/
noncomputable def closedFanNeighbours (hub : object.Vertex) : Finset object.Vertex :=
  (neighbourRim object hub).filter fun u =>
    ∀ w : object.Vertex, object.graph.Adj u w → w ≠ hub → w ∈ residual.core

/-- `c_h = |{u ∈ N(h) : both non-`h` incidences of `u` are assigned}|`. -/
noncomputable def closedFanCount (hub : object.Vertex) : Nat :=
  (residual.closedFanNeighbours hub).card

variable {residual}

theorem mem_closedFanNeighbours_iff {hub u : object.Vertex} :
    u ∈ residual.closedFanNeighbours hub ↔
      object.graph.Adj hub u ∧
        ∀ w : object.Vertex, object.graph.Adj u w → w ≠ hub → w ∈ residual.core := by
  rw [closedFanNeighbours, Finset.mem_filter, mem_neighbourRim]

variable (residual)

theorem closedFanCount_le_degree (hub : object.Vertex) :
    residual.closedFanCount hub ≤ object.degree hub := by
  have subset : residual.closedFanNeighbours hub ⊆ neighbourRim object hub :=
    Finset.filter_subset _ _
  have card := Finset.card_le_card subset
  rwa [card_eq_degree_of_isNeighbourhood object hub (neighbourRim object hub)
    (mem_neighbourRim object hub)] at card

/-- The fan envelope `E_h` of `lem:typeB-bridge-deficit-bound` as a vertex set:
the centre `h` together with its assigned fan neighbours in `Y_X`.  The non-`h`
incidences of the cubic-closed neighbours enter the manuscript's envelope as
incidence carriers of nonnegative capacity, not as vertices, so they are not
part of this block. -/
noncomputable def envelopeBlock (hub : object.Vertex) : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  insert hub (neighbourRim object hub ∩ residual.core)

/-- The core left after the Type B fan envelopes are removed. -/
noncomputable def residualCore : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  residual.core \ residual.centers.biUnion residual.envelopeBlock

/-- The ledger charge of the core left after the fan envelopes are removed.
Since that core carries no assigned surplus, this is exactly its net charge, the
quantity the manuscript discharges through the Type A components of
`lem:typeB-postledger-core-hygiene`.  That decomposition is proved in
`Graph.TypeBPostLedgerCore.residualCoreCharge_eq_sum_components`, and the
discharge itself is
`Graph.TypeBPostLedgerCore.residualCoreCharge_nonneg_of_componentDeficit_nonneg`,
whose only remaining input is the sign of the extracted Type A deficit; the
per-component `reserve(Z) ≤ No(Z)` of the Type A saturated handoff and
unsaturated discharge is read one component at a time by
`Graph.TypeBPostLedgerCore.componentCharge_nonneg_of_discharged`. -/
noncomputable def residualCoreCharge (profile : LoadCapacityProfile) : ℚ :=
  ∑ y ∈ residual.residualCore, residual.vertexCharge profile y

/-- The manuscript's per-centre negative-part allowance
`(k - 3 + α) + αc` of display (1) in `lem:typeB-bridge-deficit-bound`, written
with the presentation's discharge rate in place of the literal quarter. -/
noncomputable def envelopeAllowance (profile : LoadCapacityProfile)
    (hub : object.Vertex) : ℚ :=
  ((object.degree hub : ℚ) - 3) + profile.dischargeRate
    + (residual.closedFanCount hub : ℚ) * profile.dischargeRate

/-- The first inequality of display (1): `c ≤ k` turns the allowance into the
sharp value `(k - 3) + α(1 + k)`, which is the manuscript's `(5/4)k - 11/4` at
`α = 1/4`. -/
theorem envelopeAllowance_le_sharp (profile : LoadCapacityProfile)
    (hub : object.Vertex) :
    residual.envelopeAllowance profile hub
      ≤ ((object.degree hub : ℚ) - 3)
        + (1 + (object.degree hub : ℚ)) * profile.dischargeRate := by
  have cast : (residual.closedFanCount hub : ℚ) ≤ (object.degree hub : ℚ) := by
    exact_mod_cast residual.closedFanCount_le_degree hub
  have prod : (residual.closedFanCount hub : ℚ) * profile.dischargeRate
      ≤ (object.degree hub : ℚ) * profile.dischargeRate :=
    mul_le_mul_of_nonneg_right cast profile.dischargeRate_nonneg
  have expand : (1 + (object.degree hub : ℚ)) * profile.dischargeRate
      = profile.dischargeRate
        + (object.degree hub : ℚ) * profile.dischargeRate := by ring
  rw [expand]
  unfold envelopeAllowance
  linarith

/-- The second inequality of display (1): `(k - 3) + α(1 + k) ≤ 8(k - 3)`.  At
`α = 1/4` this is the manuscript's `(5/4)k - 11/4 ≤ 8(k-3)`, equivalently
`27k ≥ 85`.  The generic proof uses only `α ≤ 1`
(`ReceiverLoad.LoadCapacityProfile.dischargeRate_le_one`, which holds for every
profile) together with `k ≥ 4`, since then `(k - 3) + (1 + k) ≤ 8(k - 3)` is
`6k ≥ 22`.  So no property of the chosen rate beyond "a vertex is discharged by
at most one whole unit" enters the bound. -/
theorem sharp_le_eight_surplus (profile : LoadCapacityProfile)
    {hub : object.Vertex} (high : 4 ≤ object.degree hub) :
    ((object.degree hub : ℚ) - 3)
        + (1 + (object.degree hub : ℚ)) * profile.dischargeRate
      ≤ 8 * ((object.degree hub : ℚ) - 3) := by
  have cast : (4 : ℚ) ≤ (object.degree hub : ℚ) := by exact_mod_cast high
  have nonneg : (0 : ℚ) ≤ 1 + (object.degree hub : ℚ) := by linarith
  have bound : (1 + (object.degree hub : ℚ)) * profile.dischargeRate
      ≤ (1 + (object.degree hub : ℚ)) * 1 :=
    mul_le_mul_of_nonneg_left profile.dischargeRate_le_one nonneg
  rw [mul_one] at bound
  linarith

/-- Display (1) of `lem:typeB-bridge-deficit-bound`:
`(k - 3 + α) + αc ≤ (k - 3) + α(1 + k) ≤ 8(k - 3)`. -/
theorem envelopeAllowance_le_eight_surplus (profile : LoadCapacityProfile)
    {hub : object.Vertex} (high : 4 ≤ object.degree hub) :
    residual.envelopeAllowance profile hub
      ≤ 8 * ((object.degree hub : ℚ) - 3) :=
  le_trans (residual.envelopeAllowance_le_sharp profile hub)
    (sharp_le_eight_surplus profile high)

/-! ### The negative part of one fan envelope

The manuscript bounds the *negative part* left by a fan envelope.  Envelopes at
different centres may overlap; the manuscript ignores rather than resolves those
overlaps, which is exactly the statement that the clamped charge below is
subadditive over the envelopes. -/

/-- The negative part of a vertex charge. -/
noncomputable def clampedCharge (profile : LoadCapacityProfile)
    (y : object.Vertex) : ℚ := min (residual.vertexCharge profile y) 0

theorem clampedCharge_nonpos (profile : LoadCapacityProfile) (y : object.Vertex) :
    residual.clampedCharge profile y ≤ 0 := min_le_right _ _

theorem clampedCharge_le_vertexCharge (profile : LoadCapacityProfile)
    (y : object.Vertex) :
    residual.clampedCharge profile y ≤ residual.vertexCharge profile y :=
  min_le_left _ _

theorem neg_dischargeRate_le_clampedCharge (profile : LoadCapacityProfile)
    (y : object.Vertex) :
    -profile.dischargeRate ≤ residual.clampedCharge profile y :=
  le_min (residual.neg_dischargeRate_le_vertexCharge profile y)
    (neg_nonpos.2 profile.dischargeRate_nonneg)

theorem clampedCharge_eq_zero_of_coreDegree_le_two (profile : LoadCapacityProfile)
    {y : object.Vertex} (small : residual.coreDegree y ≤ 2) :
    residual.clampedCharge profile y = 0 :=
  min_eq_right (residual.vertexCharge_nonneg_of_coreDegree_le_two profile small)

/-- Display (1) of `lem:typeB-bridge-deficit-bound` in ledger form: inside the
fan envelope at `h`, only `h` itself and the `c_h` cubic-closed fan neighbours
can carry negative charge, and each of them carries at most one discharge unit. -/
theorem neg_envelope_negativePart_le_sum_clampedCharge
    (profile : LoadCapacityProfile) {hub : object.Vertex}
    (normal : NormalForm object hub) :
    -((1 + (residual.closedFanCount hub : ℚ)) * profile.dischargeRate)
      ≤ ∑ y ∈ residual.envelopeBlock hub, residual.clampedCharge profile y := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  set carriers : Finset object.Vertex :=
    insert hub (residual.closedFanNeighbours hub) with carriersDef
  have vanishes : ∀ y ∈ residual.envelopeBlock hub, y ∉ carriers →
      residual.clampedCharge profile y = 0 := by
    intro y member notCarrier
    have neHub : y ≠ hub := by
      rintro rfl
      exact notCarrier (Finset.mem_insert_self _ _)
    have blockMem : y ∈ neighbourRim object hub ∩ residual.core := by
      rcases Finset.mem_insert.1 member with rfl | inside
      · exact absurd rfl neHub
      · exact inside
    obtain ⟨rimMem, _⟩ := Finset.mem_inter.1 blockMem
    have adjacent : object.graph.Adj hub y := (mem_neighbourRim object hub y).1 rimMem
    have notClosed : y ∉ residual.closedFanNeighbours hub := fun mem =>
      notCarrier (Finset.mem_insert_of_mem mem)
    have failing : ¬ ∀ w : object.Vertex, object.graph.Adj y w → w ≠ hub →
        w ∈ residual.core := by
      intro assigned
      exact notClosed (mem_closedFanNeighbours_iff.2 ⟨adjacent, assigned⟩)
    simp only [not_forall] at failing
    obtain ⟨w, adjW, _, outside⟩ := failing
    exact residual.clampedCharge_eq_zero_of_coreDegree_le_two profile
      (residual.coreDegree_le_two_of_unassigned (normal.neighbourCubic adjacent) adjW
        outside)
  have split := Finset.sum_filter_add_sum_filter_not (residual.envelopeBlock hub)
    (fun y => y ∈ carriers) (residual.clampedCharge profile)
  have zeroPart :
      ∑ y ∈ (residual.envelopeBlock hub).filter (fun y => y ∉ carriers),
        residual.clampedCharge profile y = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y member
    obtain ⟨blockMem, notCarrier⟩ := Finset.mem_filter.1 member
    exact vanishes y blockMem notCarrier
  have rateBound :
      ((residual.envelopeBlock hub).filter (fun y => y ∈ carriers)).card •
          (-profile.dischargeRate)
        ≤ ∑ y ∈ (residual.envelopeBlock hub).filter (fun y => y ∈ carriers),
            residual.clampedCharge profile y :=
    Finset.card_nsmul_le_sum _ _ _ fun y _ =>
      residual.neg_dischargeRate_le_clampedCharge profile y
  have cardBound :
      ((residual.envelopeBlock hub).filter (fun y => y ∈ carriers)).card
        ≤ 1 + residual.closedFanCount hub := by
    have subset : (residual.envelopeBlock hub).filter (fun y => y ∈ carriers) ⊆
        carriers := fun y member => (Finset.mem_filter.1 member).2
    have step := Finset.card_le_card subset
    have insertBound : carriers.card ≤ (residual.closedFanNeighbours hub).card + 1 := by
      rw [carriersDef]
      exact Finset.card_insert_le _ _
    have countDef :
        residual.closedFanCount hub = (residual.closedFanNeighbours hub).card := rfl
    omega
  have cardCast :
      (((residual.envelopeBlock hub).filter (fun y => y ∈ carriers)).card : ℚ)
        ≤ 1 + (residual.closedFanCount hub : ℚ) := by
    exact_mod_cast cardBound
  have cardRate :
      (((residual.envelopeBlock hub).filter (fun y => y ∈ carriers)).card : ℚ)
          * profile.dischargeRate
        ≤ (1 + (residual.closedFanCount hub : ℚ)) * profile.dischargeRate :=
    mul_le_mul_of_nonneg_right cardCast profile.dischargeRate_nonneg
  rw [nsmul_eq_mul, mul_neg] at rateBound
  rw [zeroPart, add_zero] at split
  rw [← split]
  linarith

/-- Subadditivity of a nonpositive weight over a family of blocks: overlaps only
help.  This is the manuscript's "after all overlaps are ignored rather than
resolved". -/
theorem sum_sum_le_sum_biUnion [DecidableEq object.Vertex] {g : object.Vertex → ℚ}
    (nonpos : ∀ y, g y ≤ 0) (index : Finset object.Vertex)
    (block : object.Vertex → Finset object.Vertex) :
    ∑ h ∈ index, ∑ y ∈ block h, g y ≤ ∑ y ∈ index.biUnion block, g y := by
  classical
  refine Finset.induction_on index ?_ ?_
  · simp
  · intro a rest notMem ih
    rw [Finset.sum_insert notMem, Finset.biUnion_insert]
    have inter := Finset.sum_union_inter (s₁ := block a)
      (s₂ := rest.biUnion block) (f := g)
    have nonposInter : ∑ y ∈ block a ∩ rest.biUnion block, g y ≤ 0 :=
      Finset.sum_nonpos fun y _ => nonpos y
    linarith

/-! ### `lem:typeB-bridge-deficit-bound` -/

theorem envelopeBlock_subset_core {hub : object.Vertex}
    (hubMem : hub ∈ residual.core) : residual.envelopeBlock hub ⊆ residual.core := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro y member
  simp only [envelopeBlock, Finset.mem_insert, Finset.mem_inter] at member
  rcases member with rfl | ⟨_, inside⟩
  · exact hubMem
  · exact inside

theorem biUnion_envelopeBlock_subset_core
    :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    residual.centers.biUnion residual.envelopeBlock ⊆ residual.core := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro y member
  obtain ⟨h, hMem, blockMem⟩ := Finset.mem_biUnion.1 member
  exact residual.envelopeBlock_subset_core (centers_subset_core hMem) blockMem

theorem sum_envelopeAllowance_eq (profile : LoadCapacityProfile) :
    ∑ h ∈ residual.centers, residual.envelopeAllowance profile h
      = residual.surplus
        + ∑ h ∈ residual.centers,
            (1 + (residual.closedFanCount h : ℚ)) * profile.dischargeRate := by
  unfold envelopeAllowance surplus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  ring

/-- **`lem:typeB-bridge-deficit-bound`, envelope form.**  The net charge of a
connected assigned Type B bridge residual is bounded below by the charge of the
core left after the fan envelopes are removed, minus the per-centre envelope
allowances `(d_G(h) - 3 + α) + αc_h` of display (1).

The manuscript's route-8 clause is not a hypothesis: the undischarged remainder
appears explicitly as `residualCoreCharge`, exactly as
`lem:typeB-bridge-with-route8-core` carries `-D_A(𝒜_X)` in its conclusion. -/
theorem residualCoreCharge_sub_sum_envelopeAllowance_le_netCharge
    (profile : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    :
    residual.residualCoreCharge profile
        - ∑ h ∈ residual.centers, residual.envelopeAllowance profile h
      ≤ residual.netCharge profile := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have unionSubset :
      residual.centers.biUnion residual.envelopeBlock ⊆ residual.core :=
    residual.biUnion_envelopeBlock_subset_core
  have splitSum :
      residual.residualCoreCharge profile
          + ∑ y ∈ residual.centers.biUnion residual.envelopeBlock,
              residual.vertexCharge profile y
        = ∑ y ∈ residual.core, residual.vertexCharge profile y := by
    rw [residualCoreCharge, residualCore]
    exact Finset.sum_sdiff unionSubset
  have clampLe :
      ∑ y ∈ residual.centers.biUnion residual.envelopeBlock,
          residual.clampedCharge profile y
        ≤ ∑ y ∈ residual.centers.biUnion residual.envelopeBlock,
            residual.vertexCharge profile y :=
    Finset.sum_le_sum fun y _ => residual.clampedCharge_le_vertexCharge profile y
  have subadd :
      ∑ h ∈ residual.centers,
          ∑ y ∈ residual.envelopeBlock h, residual.clampedCharge profile y
        ≤ ∑ y ∈ residual.centers.biUnion residual.envelopeBlock,
            residual.clampedCharge profile y :=
    sum_sum_le_sum_biUnion (residual.clampedCharge_nonpos profile) residual.centers
      residual.envelopeBlock
  have blockBound :
      ∑ h ∈ residual.centers,
          -((1 + (residual.closedFanCount h : ℚ)) * profile.dischargeRate)
        ≤ ∑ h ∈ residual.centers,
            ∑ y ∈ residual.envelopeBlock h, residual.clampedCharge profile y :=
    Finset.sum_le_sum fun h member =>
      residual.neg_envelope_negativePart_le_sum_clampedCharge profile
        (normal h member)
  rw [Finset.sum_neg_distrib] at blockBound
  have ledger := residual.netCharge_eq_sum_vertexCharge_sub_surplus profile
  have allowance := residual.sum_envelopeAllowance_eq profile
  linarith

/-- **`lem:typeB-bridge-deficit-bound`, surplus form.**  Display (1) collapses
every envelope allowance to `8(d_G(h) - 3)`. -/
theorem residualCoreCharge_sub_eight_surplus_le_netCharge
    (profile : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    :
    residual.residualCoreCharge profile - 8 * residual.surplus
      ≤ residual.netCharge profile := by
  have envelope :=
    residual.residualCoreCharge_sub_sum_envelopeAllowance_le_netCharge profile normal
  have allowanceBound :
      ∑ h ∈ residual.centers, residual.envelopeAllowance profile h
        ≤ ∑ h ∈ residual.centers, 8 * ((object.degree h : ℚ) - 3) :=
    Finset.sum_le_sum fun h member =>
      residual.envelopeAllowance_le_eight_surplus profile (normal h member).high
  rw [← Finset.mul_sum] at allowanceBound
  have surplusDef : ∑ h ∈ residual.centers, ((object.degree h : ℚ) - 3)
      = residual.surplus := rfl
  rw [surplusDef] at allowanceBound
  linarith

theorem surplus_nonneg (high : ∀ h ∈ residual.centers, 4 ≤ object.degree h) :
    0 ≤ residual.surplus := by
  refine Finset.sum_nonneg ?_
  intro h member
  have : (4 : ℚ) ≤ (object.degree h : ℚ) := by exact_mod_cast high h member
  linarith

/-- **`lem:typeB-bridge-deficit-bound`.**  Once the core left after the fan
envelopes are removed carries nonnegative charge -- the manuscript obtains this
from `lem:typeB-postledger-core-hygiene` together with the Type A saturated
handoff and unsaturated discharge, formalised as
`Graph.TypeBPostLedgerCore.negativePart_le_eight_surplus_of_componentDeficit_nonneg`
-- the whole negative part of the bridge residual is charged to eight times its
assigned surplus:

`No_-(X) ≤ 8 Σ_{h ∈ H_X} (d_G(h) - 3)`. -/
theorem negativePart_le_eight_surplus (profile : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h) :
    residual.negativePart profile
      ≤ 8 * residual.surplus + max 0 (-residual.residualCoreCharge profile) := by
  have main :=
    residual.residualCoreCharge_sub_eight_surplus_le_netCharge profile normal
  have nonneg : 0 ≤ residual.surplus :=
    residual.surplus_nonneg fun h member => (normal h member).high
  have remainder : -residual.residualCoreCharge profile
      ≤ max 0 (-residual.residualCoreCharge profile) := le_max_right _ _
  have remainderNonneg : (0 : ℚ) ≤ max 0 (-residual.residualCoreCharge profile) :=
    le_max_left _ _
  refine max_le (by linarith) (by linarith)

end Residual

/-! ## `c_h` is the manuscript's `c(𝔉_h)`

Whenever the assigned centre carries a fan certificate, the locally defined
count `c_h` is literally the closed-neighbour count `c(𝔉_h)` of
`def:typeB-multiclosed-residual`, computed by the canonical assigned
fan-window profile of `TypeBFanClosedPorts`. -/

/-- Every closed neighbour recorded by an assigned fan-window profile whose
envelope is the support is one of the residual's cubic-closed fan neighbours.
The manuscript's `c` in `lem:typeB-bridge-deficit-bound` carries no window
restriction -- it must count *every* fan neighbour whose two non-`h` incidences
are assigned, since those are exactly the neighbours that can carry negative
charge -- whereas `c(𝔉_h)` of `def:typeB-multiclosed-residual` additionally
asks for the remainder side, so the general relation is this inclusion. -/
theorem closedNeighbours_subset_closedFanNeighbours (residual : Residual object)
    (profile : Profile object) (assigned : profile.envelope = residual.core) :
    profile.closedNeighbours
      ⊆ residual.closedFanNeighbours profile.marked.fan.hub := by
  intro u member
  have expanded := (Profile.mem_closedNeighbours_iff (profile := profile) u).1 member
  have closed : profile.marked.IsCubicClosed profile.envelope u := expanded.2.1
  refine Residual.mem_closedFanNeighbours_iff.2
    ⟨(profile.marked.rim_eq_neighbourhood u).1 expanded.1, ?_⟩
  intro w adjacent notHub
  rw [← assigned]
  exact closed.2.2 w adjacent notHub

theorem closedCount_le_closedFanCount (residual : Residual object)
    (profile : Profile object) (assigned : profile.envelope = residual.core) :
    profile.closedCount ≤ residual.closedFanCount profile.marked.fan.hub :=
  Finset.card_le_card
    (closedNeighbours_subset_closedFanNeighbours residual profile assigned)

/-- When the profile records every fan neighbour of the centre on the remainder
side `R = G - W`, as `def:fan-closed-port` (a) does, the residual's count is
exactly the manuscript's `c(𝔉_h)`. -/
theorem closedNeighbours_eq_closedFanNeighbours (residual : Residual object)
    (profile : Profile object)
    (normal : NormalForm object profile.marked.fan.hub)
    (assigned : profile.envelope = residual.core)
    (remainderSide : ∀ u : object.Vertex,
      object.graph.Adj profile.marked.fan.hub u → u ∉ profile.window) :
    profile.closedNeighbours
      = residual.closedFanNeighbours profile.marked.fan.hub := by
  refine Finset.Subset.antisymm
    (closedNeighbours_subset_closedFanNeighbours residual profile assigned) ?_
  intro u member
  obtain ⟨adjacent, incidences⟩ := Residual.mem_closedFanNeighbours_iff.1 member
  have rimMem : u ∈ profile.marked.fan.rim :=
    (profile.marked.rim_eq_neighbourhood u).2 adjacent
  refine (Profile.mem_closedNeighbours_iff (profile := profile) u).2
    ⟨rimMem, ⟨rimMem, normal.neighbourCubic adjacent, ?_⟩, ?_⟩
  · intro w adjW notHub
    rw [assigned]
    exact incidences w adjW notHub
  · exact (Profile.mem_remainder_iff u).2 ⟨rimMem, remainderSide u adjacent⟩

theorem closedCount_eq_closedFanCount (residual : Residual object)
    (profile : Profile object)
    (normal : NormalForm object profile.marked.fan.hub)
    (assigned : profile.envelope = residual.core)
    (remainderSide : ∀ u : object.Vertex,
      object.graph.Adj profile.marked.fan.hub u → u ∉ profile.window) :
    profile.closedCount = residual.closedFanCount profile.marked.fan.hub := by
  unfold Profile.closedCount Residual.closedFanCount
  rw [closedNeighbours_eq_closedFanNeighbours residual profile normal assigned
    remainderSide]


/-! ## `def:canonical-decomp`: the collection `𝒳_B`, derived from the object

`def:typeB-residual-mass` sums `No_-(X)` over the collection `𝒳_B` of assigned
Type B bridge residual supports, and `def:canonical-decomp` assigns every
ambient surplus unit `d_G(h) - 3` to exactly one piece of that collection.  So
the collection is *not* free data, and it is not a bespoke record either: it is
an enumeration produced by the object, in exactly the shape
`TypeBProfileSchedule.profileCandidates` takes at node `[74]` and
`TypeBDegreeFour.degreeFourCores` takes at node `[79]` -- one canonical member
per centre carrying surplus, listed in the object's own vertex scan order.

Building the collection this way *is* the canonical decomposition.  A centre is
enumerated once, so the surplus unit it carries is assigned once, and every
statement the manuscript obtains by constructing the decomposition becomes a
consequence of `FiniteObject.orderedVertices_nodup`:

* the assigned centre sets of distinct members are disjoint
  (`bridgeResiduals_pairwise`);
* a vertex occurs at most once -- hence at most twice -- among the assigned
  centre occurrences (`count_centerOccurrences_le_one`,
  `count_centerOccurrences_le_two`);
* nothing is lost, because the assigned centres of the collection are exactly
  the vertices carrying ambient surplus
  (`centerOccurrences_eq_bridgeCentres`).
-/

/-- The centres of the object carrying ambient surplus, in its own vertex scan
order: the vertices with `d_G(h) - 3 > 0`.  A local observable, exactly like
`TypeBDegreeFour.degreeFourCenters` and `TypeBProfileSchedule.fanCentres`. -/
def bridgeCentres (object : FiniteObject.{u}) : List object.Vertex :=
  object.orderedVertices.filter fun vertex => decide (4 ≤ object.degree vertex)

@[simp] theorem mem_bridgeCentres_iff (object : FiniteObject.{u})
    (vertex : object.Vertex) :
    vertex ∈ bridgeCentres object ↔ 4 ≤ object.degree vertex := by
  simp [bridgeCentres]

theorem bridgeCentres_nodup (object : FiniteObject.{u}) :
    (bridgeCentres object).Nodup :=
  object.orderedVertices_nodup.filter _

/-- **The canonical assigned Type B bridge residual at a centre.**  Nothing is
redefined: the counted core `Y_X` is the framework's canonical assigned fan
envelope `TypeBProfileSchedule.canonicalEnvelope` -- the centre, its neighbours,
and the non-central incidences of those neighbours, all read off the object's
own vertex, neighbour and outside-incidence schedules -- and the recorded centre
is the centre itself.

The containment `H_X ⊆ Y_X` of `def:typeB-assigned-ledger` is therefore a
construction twice over: `Residual.centers` intersects with the core, and the
core does contain the centre (`centers_canonicalResidual`). -/
def canonicalResidual (object : FiniteObject.{u}) (center : object.Vertex) :
    Residual object where
  core := canonicalEnvelope object center
  recordedCentres := {center}

theorem center_mem_canonicalResidual_core (object : FiniteObject.{u})
    (center : object.Vertex) : center ∈ (canonicalResidual object center).core :=
  (mem_canonicalEnvelope_iff center center).2 (Or.inl rfl)

/-- The assigned centres of the canonical residual at a centre are exactly that
centre: `H_X = {h}`.  This is where the counted core paying for its own centre
is used, so it is not an unfolding of the definition. -/
theorem centers_canonicalResidual (object : FiniteObject.{u})
    (center : object.Vertex) :
    (canonicalResidual object center).centers = {center} := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine Finset.Subset.antisymm (fun vertex member => (Finset.mem_inter.1 member).1) ?_
  intro vertex member
  rw [Finset.mem_singleton] at member
  subst member
  exact Finset.mem_inter.2
    ⟨Finset.mem_singleton_self _, center_mem_canonicalResidual_core object vertex⟩

/-- `σ(X) = d_G(h) - 3` at the canonical residual: the member carries exactly
the ambient surplus of its own centre. -/
theorem surplus_canonicalResidual (object : FiniteObject.{u})
    (center : object.Vertex) :
    (canonicalResidual object center).surplus = (object.degree center : ℚ) - 3 := by
  unfold Residual.surplus
  rw [centers_canonicalResidual, Finset.sum_singleton]

/-- The canonical core carries the two non-central incidences of every fan
neighbour, so *every* neighbour of the centre is cubic-closed for the canonical
residual. -/
theorem closedFanNeighbours_canonicalResidual (object : FiniteObject.{u})
    (center : object.Vertex) :
    (canonicalResidual object center).closedFanNeighbours center
      = neighbourRim object center := by
  refine Finset.Subset.antisymm (Finset.filter_subset _ _) ?_
  intro u member
  have adjacent : object.graph.Adj center u := (mem_neighbourRim object center u).1 member
  refine Residual.mem_closedFanNeighbours_iff.2 ⟨adjacent, ?_⟩
  intro w incidence notCentre
  exact shoulder_mem_canonicalEnvelope adjacent incidence notCentre

/-- `c_h = d_G(h)` at the canonical residual. -/
theorem closedFanCount_canonicalResidual (object : FiniteObject.{u})
    (center : object.Vertex) :
    (canonicalResidual object center).closedFanCount center = object.degree center := by
  unfold Residual.closedFanCount
  rw [closedFanNeighbours_canonicalResidual]
  exact card_eq_degree_of_isNeighbourhood object center (neighbourRim object center)
    (mem_neighbourRim object center)

/-- Display (1) of `lem:typeB-bridge-deficit-bound` is *attained* on the derived
collection: `c_h = k` turns the per-centre allowance
`(k - 3 + α) + αc_h` into the sharp value `(k - 3) + α(1 + k)`, so the first
inequality of the display is an equality here and the deficit bound is not
proved through a slack the carrier could never realise. -/
theorem envelopeAllowance_canonicalResidual (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) (center : object.Vertex) :
    (canonicalResidual object center).envelopeAllowance profile center
      = ((object.degree center : ℚ) - 3)
        + (1 + (object.degree center : ℚ)) * profile.dischargeRate := by
  unfold Residual.envelopeAllowance
  rw [closedFanCount_canonicalResidual]
  ring

/-- **The enumerable carrier of assigned Type B bridge residual supports.**  The
collection `𝒳_B` of `def:typeB-residual-mass`: one canonical assigned support
per centre carrying ambient surplus, produced from the object's own vertex,
neighbour and outside-incidence schedules.  Nothing is authored, and a
downstream node scans this list. -/
def bridgeResiduals (object : FiniteObject.{u}) : List (Residual object) :=
  (bridgeCentres object).map (canonicalResidual object)

theorem canonicalResidual_injective (object : FiniteObject.{u}) :
    Function.Injective (canonicalResidual object) := by
  intro left right equal
  have record : ({left} : Finset object.Vertex) = {right} :=
    congrArg Residual.recordedCentres equal
  exact Finset.singleton_inj.1 record

theorem mem_bridgeResiduals_iff (object : FiniteObject.{u})
    (residual : Residual object) :
    residual ∈ bridgeResiduals object ↔
      ∃ center : object.Vertex, 4 ≤ object.degree center ∧
        residual = canonicalResidual object center := by
  rw [bridgeResiduals, List.mem_map]
  constructor
  · rintro ⟨center, member, rfl⟩
    exact ⟨center, (mem_bridgeCentres_iff object center).1 member, rfl⟩
  · rintro ⟨center, high, rfl⟩
    exact ⟨center, (mem_bridgeCentres_iff object center).2 high, rfl⟩

theorem bridgeResiduals_nodup (object : FiniteObject.{u}) :
    (bridgeResiduals object).Nodup :=
  (bridgeCentres_nodup object).map (canonicalResidual_injective object)

/-- **The enumeration is complete.**  Every vertex carrying ambient surplus is
the assigned centre of an enumerated member, so `def:canonical-decomp` loses no
surplus unit. -/
theorem exists_mem_bridgeResiduals {center : object.Vertex}
    (high : 4 ≤ object.degree center) :
    ∃ member ∈ bridgeResiduals object, member.centers = {center} :=
  ⟨canonicalResidual object center,
    (mem_bridgeResiduals_iff object _).2 ⟨center, high, rfl⟩,
    centers_canonicalResidual object center⟩

/-- **The former high-degree hypothesis, now a theorem.**  An assigned centre of
an enumerated member carries positive ambient surplus, because carrying it is
the defining filter of the enumeration. -/
theorem high_of_mem_centers {residual : Residual object}
    (member : residual ∈ bridgeResiduals object) {h : object.Vertex}
    (centreMem : h ∈ residual.centers) : 4 ≤ object.degree h := by
  obtain ⟨center, high, rfl⟩ := (mem_bridgeResiduals_iff object residual).1 member
  rw [centers_canonicalResidual, Finset.mem_singleton] at centreMem
  subst centreMem
  exact high

/-- **The former disjointness hypothesis, now a theorem.**  The assigned centre
sets of distinct enumerated members are disjoint.  Once the carrier is derived
from the object this is `FiniteObject.orderedVertices_nodup` and nothing else:
each member's assigned centre set is the singleton of its own centre, and the
object lists each of its vertices once.  This is the ordinary-role clause of
`def:typeB-residual-mass` ("high-degree centers are disjoint by the canonical
assignment in `def:canonical-decomp`") together with its grouped clause ("the
core--center incidence components partition the handoff-center set"): a single
enumeration realises both at once. -/
theorem bridgeResiduals_pairwise (object : FiniteObject.{u}) :
    (bridgeResiduals object).Pairwise
      fun left right => Disjoint left.centers right.centers := by
  rw [bridgeResiduals, List.pairwise_map]
  refine (bridgeCentres_nodup object).imp ?_
  intro left right distinct
  rw [centers_canonicalResidual, centers_canonicalResidual]
  exact Finset.disjoint_singleton.2 distinct

/-! ## `def:typeB-residual-mass`: the Type B residual fan mass -/

/-- `M_B(𝒳_B) = Σ_{X ∈ 𝒳_B} No_-(X)`. -/
noncomputable def residualMass (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) : ℚ :=
  ((bridgeResiduals object).map fun member => member.negativePart profile).sum

/-- `S_B(𝒳_B) = Σ_{X ∈ 𝒳_B} Σ_{h ∈ H_X} s_X(h)` with `s_X(h) = d_G(h) - 3`. -/
noncomputable def surplusMass (object : FiniteObject.{u}) : ℚ :=
  ((bridgeResiduals object).map Residual.surplus).sum

/-- The undischarged remainder of the collection: the part of each core charge
the Type A discharge has not yet paid.  It appears as an explicit term, exactly
as `lem:typeB-bridge-with-route8-core` carries `-D_A`, so nothing here assumes
the discharge has happened. -/
noncomputable def undischargedMass (object : FiniteObject.{u})
    (profile : LoadCapacityProfile) : ℚ :=
  ((bridgeResiduals object).map fun member =>
    max 0 (-member.residualCoreCharge profile)).sum

/-- `H_B(𝒳_B) = ⨆_{X ∈ 𝒳_B} H_X`, the tagged union of centre occurrences. -/
noncomputable def centerOccurrences (object : FiniteObject.{u}) :
    List object.Vertex :=
  (bridgeResiduals object).flatMap fun member => member.centers.toList

/-- The tagged union of assigned centres is exactly the schedule of centres
carrying ambient surplus.  Nothing is double-counted and nothing is dropped. -/
theorem centerOccurrences_eq_bridgeCentres (object : FiniteObject.{u}) :
    centerOccurrences object = bridgeCentres object := by
  unfold centerOccurrences bridgeResiduals
  induction bridgeCentres object with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, List.flatMap_cons, ih, centers_canonicalResidual,
        Finset.toList_singleton, List.singleton_append]

/-- **Sharper than the manuscript's convention, by construction.**  A vertex
occurs *at most once* in the tagged union `H_B(𝒳_B)`, because the object lists
each of its vertices once and the enumeration takes one member per centre. -/
theorem count_centerOccurrences_le_one (object : FiniteObject.{u})
    (v : object.Vertex) :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    (centerOccurrences object).count v ≤ 1 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [centerOccurrences_eq_bridgeCentres]
  exact List.nodup_iff_count_le_one.1 (bridgeCentres_nodup object) v

/-- **The at-most-twice convention of `def:typeB-residual-mass`, verbatim.**  A
vertex occurs at most twice in the tagged union `H_B(𝒳_B)`.  The manuscript
allows the double occurrence because it keeps an ordinary and a grouped role;
the derived collection needs neither, so the convention holds with room to
spare, and the factor two in `surplusMass_le_two_globalSurplusPos` is likewise
no longer used up. -/
theorem count_centerOccurrences_le_two (object : FiniteObject.{u})
    (v : object.Vertex) :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    (centerOccurrences object).count v ≤ 2 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact le_trans (count_centerOccurrences_le_one object v) (by norm_num)

/-! ### List arithmetic used by the two collection bounds -/

theorem list_sum_map_le {α : Type*} {role : List α} {f g : α → ℚ}
    (bound : ∀ x ∈ role, f x ≤ g x) :
    (role.map f).sum ≤ (role.map g).sum := by
  induction role with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      have headBound := bound head (List.mem_cons_self ..)
      have tailBound := ih fun x member => bound x (List.mem_cons_of_mem _ member)
      linarith

theorem list_sum_map_mul {α : Type*} (role : List α) (constant : ℚ) (f : α → ℚ) :
    (role.map fun x => constant * f x).sum = constant * (role.map f).sum := by
  induction role with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-! ### `S_B ≤ 2 σ(G)`: each surplus unit is spent once

The manuscript's factor two is the two roles of `def:typeB-residual-mass`, and
its content is that no surplus unit is spent more often than that.  On the
derived collection the accounting is exact: `surplusMass_eq_globalSurplusPos`
says `S_B(𝒳_B)` *is* the positive part of the global surplus, because the
enumeration walks the object's vertex schedule once and each enumerated member
carries the surplus of its own centre.  The manuscript's inequality follows with
the factor two intact and unused. -/

theorem surplusMass_eq_sum_bridgeCentres (object : FiniteObject.{u}) :
    surplusMass object
      = ((bridgeCentres object).map fun h => (object.degree h : ℚ) - 3).sum := by
  unfold surplusMass bridgeResiduals
  rw [List.map_map]
  exact congrArg List.sum
    (List.map_congr_left fun h _ => surplus_canonicalResidual object h)

/-- **The surplus mass of the derived collection is the global positive
surplus.**  Every unit of `Σ_v max{0, d_G(v) - 3}` is assigned, and assigned
once. -/
theorem surplusMass_eq_globalSurplusPos (object : FiniteObject.{u}) :
    surplusMass object = globalSurplusPos object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have support : (bridgeCentres object).toFinset
      = object.vertexFinset.filter fun v => 4 ≤ object.degree v := by
    ext v
    simp [object.mem_vertexFinset v]
  have listToFinset :
      ((bridgeCentres object).map fun h => (object.degree h : ℚ) - 3).sum
        = ∑ v ∈ (bridgeCentres object).toFinset, ((object.degree v : ℚ) - 3) :=
    (List.sum_toFinset _ (bridgeCentres_nodup object)).symm
  have clamp : ∑ v ∈ object.vertexFinset.filter (fun v => 4 ≤ object.degree v),
        ((object.degree v : ℚ) - 3)
      = ∑ v ∈ object.vertexFinset.filter (fun v => 4 ≤ object.degree v),
          max 0 ((object.degree v : ℚ) - 3) := by
    refine Finset.sum_congr rfl ?_
    intro v member
    have high : (4 : ℚ) ≤ (object.degree v : ℚ) := by
      exact_mod_cast (Finset.mem_filter.1 member).2
    exact (max_eq_right (by linarith)).symm
  have extend : ∑ v ∈ object.vertexFinset.filter (fun v => 4 ≤ object.degree v),
        max 0 ((object.degree v : ℚ) - 3)
      = ∑ v ∈ object.vertexFinset, max 0 ((object.degree v : ℚ) - 3) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro v member notFiltered
    have small : object.degree v ≤ 3 := by
      by_contra large
      exact notFiltered (Finset.mem_filter.2 ⟨member, by omega⟩)
    have cast : (object.degree v : ℚ) ≤ 3 := by exact_mod_cast small
    exact max_eq_left (by linarith)
  rw [surplusMass_eq_sum_bridgeCentres, listToFinset, support, clamp, extend]
  rfl

/-- The at-most-twice convention of `def:typeB-residual-mass`:
`S_B(𝒳_B) ≤ 2 σ(G)`.  The manuscript needs the factor two because a centre may
be assigned once in the ordinary role and once in the grouped role; the derived
collection assigns it once (`count_centerOccurrences_le_one`), so the bound
holds through the exact identity `surplusMass_eq_globalSurplusPos` and the
nonnegativity of the positive part.

This carries no hypothesis at all: the manuscript's "every assigned centre is
high" is the defining filter of `bridgeCentres`. -/
theorem surplusMass_le_two_globalSurplusPos (object : FiniteObject.{u}) :
    surplusMass object ≤ 2 * globalSurplusPos object := by
  have identity := surplusMass_eq_globalSurplusPos object
  have nonneg : (0 : ℚ) ≤ globalSurplusPos object := globalSurplusPos_nonneg
  linarith

/-! ### `M_B ≤ 8 S_B` -/

theorem residualMass_le_eight_surplusMass (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (bounded : ∀ member ∈ bridgeResiduals object,
      member.negativePart profile
        ≤ 8 * member.surplus + max 0 (-member.residualCoreCharge profile)) :
    residualMass object profile
      ≤ 8 * surplusMass object + undischargedMass object profile := by
  have step : ((bridgeResiduals object).map
        fun member => member.negativePart profile).sum
      ≤ ((bridgeResiduals object).map fun member =>
          8 * member.surplus + max 0 (-member.residualCoreCharge profile)).sum :=
    list_sum_map_le bounded
  have split : ((bridgeResiduals object).map fun member =>
        8 * member.surplus + max 0 (-member.residualCoreCharge profile)).sum
      = ((bridgeResiduals object).map fun member => 8 * member.surplus).sum
        + undischargedMass object profile := by
    unfold undischargedMass
    induction bridgeResiduals object with
    | nil => simp
    | cons head tail ih => simp [List.sum_cons, ih]; ring
  rw [split, list_sum_map_mul (bridgeResiduals object) 8 Residual.surplus] at step
  exact step

/-! ## `prop:typeB-bridge-sublinear` -/

/-- **`prop:typeB-bridge-sublinear`.**  For the object's own collection of Type B
bridge residual supports,

`M_B(𝒳_B) ≤ 8 S_B(𝒳_B) ≤ 16 σ(G)`,

up to the explicit undischarged remainder carried by the fan-envelope-free
cores.

The asymptotic tail `16 σ(G) = O(√n) = o(|R|)` of the manuscript is *not* an
extra hypothesis.  `def:near-cubic-spine` records branch state, and that state
is supplied by arm (a) of the proved trichotomy
`prop:nonnear-cubic-sharp-overload-routing`.  In the authored DAG that arm is
the at-or-below terminal of the node-`[19]` `scaleThresholdDichotomy`, whose
residual literally records `σ(G) ≤ (audited √-table)(n)`; the whole Type B
continuation is nested inside that terminal, so the fact is in scope here.  It
is therefore *consumed*, not assumed, in
`Graph.NearCubicSpine.residualMass_le_sixteen_threshold`, which combines this
theorem with the branch fact through
`Graph.NearCubicSpine.globalSurplus_eq_degreeSurplus`.  What stays local -- and
what this statement keeps -- is the charge inequality itself: the bridge mass is
bounded by a fixed multiple of the object's own global surplus, so any surplus
bound transports verbatim to a bridge-mass bound. -/
theorem typeBBridgeSublinear (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (normal : ∀ member ∈ bridgeResiduals object, ∀ h ∈ member.centers,
      NormalForm object h) :
    residualMass object profile
        ≤ 8 * surplusMass object + undischargedMass object profile ∧
      surplusMass object ≤ 2 * globalSurplusPos object ∧
      residualMass object profile
        ≤ 16 * globalSurplusPos object + undischargedMass object profile := by
  have massBound := residualMass_le_eight_surplusMass object profile
    fun member mem => member.negativePart_le_eight_surplus profile (normal member mem)
  have surplusBound := surplusMass_le_two_globalSurplusPos object
  exact ⟨massBound, surplusBound, by linarith⟩

/-- The same bound written against the manuscript's `σ(G) = Σ_v (d_G(v) - 3)`,
on the standing branch where the minimum degree is at least three. -/
theorem typeBBridgeSublinear_globalSurplus (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v)
    (normal : ∀ member ∈ bridgeResiduals object, ∀ h ∈ member.centers,
      NormalForm object h) :
    residualMass object profile
        ≤ 8 * surplusMass object + undischargedMass object profile ∧
      surplusMass object ≤ 2 * globalSurplus object ∧
      residualMass object profile
        ≤ 16 * globalSurplus object + undischargedMass object profile := by
  obtain ⟨massBound, surplusBound, total⟩ :=
    typeBBridgeSublinear object profile normal
  rw [globalSurplusPos_eq_globalSurplus minDegree] at surplusBound total
  exact ⟨massBound, surplusBound, total⟩

/-! ## Non-vacuity

Every hypothesis of `negativePart_le_eight_surplus` and of
`typeBBridgeSublinear` is realised simultaneously by the explicit finite graph
already used by `TypeBFanClosedPorts`: a degree-four centre whose four
neighbours are cubic with private shoulder pairs.  Nothing has to be chosen: the
object's own enumeration `bridgeResiduals` has exactly one entry there, the
canonical assigned support at that centre, whose fan-envelope-free core carries
nonnegative charge and whose count `c_h = d_G(h) = 4` attains the envelope
allowance `(k - 3 + α) + αc = (k - 3) + α(1 + k)` of display (1) with equality.
So the fan-mass bound is not vacuous, and the collection it is stated over is
not empty.

Nothing here fixes a discharge rate: every statement below is universally
quantified over the presentation profile, so the witness realises the hypotheses
for the registered profile and for any other. -/

namespace Witness

open Hypostructure.Graph.TypeBFanClosedPorts.Witness

local instance witnessDecEq : DecidableEq fanObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 13))

local instance witnessFintype : Fintype fanObject.Vertex :=
  inferInstanceAs (Fintype (Fin 13))

local instance witnessAdj : DecidableRel fanObject.graph.Adj := fanObject.decideAdj

/-- The assigned Type B bridge residual the object's own enumeration produces at
the witness centre. -/
def bridgeResidual : Residual fanObject := canonicalResidual fanObject hub

/-- The witness centre is the only vertex of the witness graph carrying ambient
surplus, so the derived collection has exactly one member. -/
theorem bridgeCentres_witness : bridgeCentres fanObject = [hub] := by decide

theorem bridgeResiduals_witness :
    bridgeResiduals fanObject = [bridgeResidual] := by
  unfold bridgeResiduals bridgeResidual
  rw [bridgeCentres_witness, List.map_cons, List.map_nil]

theorem centers_eq : bridgeResidual.centers = ({hub} : Finset fanObject.Vertex) :=
  centers_canonicalResidual fanObject hub

theorem normal_at_centers :
    ∀ h ∈ bridgeResidual.centers, NormalForm fanObject h := by
  intro h member
  rw [centers_eq, Finset.mem_singleton] at member
  subst member
  exact fanNormalForm

/-- The centre's four fan neighbours all have both non-centre incidences inside
the counted core, so `c_h = 4 = d_G(h)`. -/
theorem closedFanCount_eq : bridgeResidual.closedFanCount hub = 4 := by
  unfold bridgeResidual
  rw [closedFanCount_canonicalResidual, degree_hub]

theorem surplus_eq : bridgeResidual.surplus = 1 := by
  unfold bridgeResidual
  rw [surplus_canonicalResidual, degree_hub]
  norm_num

/-- The envelope allowance of display (1) is attained: `c = k = 4` gives
`(k - 3 + α) + αc = 1 + 5α`, which is the manuscript's `9/4` at `α = 1/4`. -/
theorem envelopeAllowance_eq (profile : LoadCapacityProfile) :
    bridgeResidual.envelopeAllowance profile hub
      = 1 + 5 * profile.dischargeRate := by
  unfold Residual.envelopeAllowance
  rw [degree_hub, closedFanCount_eq]
  push_cast
  ring

theorem envelopeAllowance_sharp (profile : LoadCapacityProfile) :
    bridgeResidual.envelopeAllowance profile hub
      = ((fanObject.degree hub : ℚ) - 3)
        + (1 + (fanObject.degree hub : ℚ)) * profile.dischargeRate := by
  rw [envelopeAllowance_eq, degree_hub]
  push_cast
  ring

/-- The counted core produced by the enumeration is the whole witness graph:
the centre, its four neighbours and their eight shoulders. -/
theorem core_eq : bridgeResidual.core = fanObject.vertexFinset := by decide

/-- Every vertex of the core left after the fan envelope is removed is a
shoulder of degree one, hence deficient. -/
theorem residualCore_degree :
    ∀ y ∈ bridgeResidual.residualCore, fanObject.degree y = 1 := by decide

/-- The manuscript's core-discharge input holds on the witness, at every
presentation profile. -/
theorem discharged (profile : LoadCapacityProfile) :
    0 ≤ bridgeResidual.residualCoreCharge profile := by
  refine Finset.sum_nonneg ?_
  intro y member
  refine bridgeResidual.vertexCharge_nonneg_of_coreDegree_le_two profile ?_
  have bound := bridgeResidual.coreDegree_le_degree y
  rw [residualCore_degree y member] at bound
  omega

/-- `lem:typeB-bridge-deficit-bound` fires on a concrete graph. -/
theorem deficit_bound_fires (profile : LoadCapacityProfile) :
    bridgeResidual.negativePart profile ≤ 8 * bridgeResidual.surplus := by
  have bound :=
    bridgeResidual.negativePart_le_eight_surplus profile normal_at_centers
  have zero : max 0 (-bridgeResidual.residualCoreCharge profile) = 0 :=
    max_eq_left (by linarith [discharged profile])
  rwa [zero, add_zero] at bound

theorem surplusMass_eq : surplusMass fanObject = 1 := by
  unfold surplusMass
  rw [bridgeResiduals_witness, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, surplus_eq]
  norm_num

/-- The witness discharges its own fan-envelope-free core, so the undischarged
remainder of the collection vanishes and the sublinear bound fires in its sharp
form `M_B ≤ 8 S_B`. -/
theorem undischargedMass_eq (profile : LoadCapacityProfile) :
    undischargedMass fanObject profile = 0 := by
  unfold undischargedMass
  rw [bridgeResiduals_witness, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, max_eq_left (by linarith [discharged profile])]
  norm_num

/-- `prop:typeB-bridge-sublinear` fires on a concrete graph. -/
theorem sublinear_fires (profile : LoadCapacityProfile) :
    residualMass fanObject profile
        ≤ 8 * surplusMass fanObject + undischargedMass fanObject profile ∧
      surplusMass fanObject ≤ 2 * globalSurplusPos fanObject ∧
      residualMass fanObject profile
        ≤ 16 * globalSurplusPos fanObject
          + undischargedMass fanObject profile := by
  refine typeBBridgeSublinear fanObject profile ?_
  intro member mem
  rw [bridgeResiduals_witness, List.mem_singleton] at mem
  subst mem
  exact normal_at_centers

/-- The collection the bound is stated over is genuinely occupied: it has one
member, its surplus mass is `1`, and its undischarged remainder is `0`, so
`M_B ≤ 8 S_B = 8`. -/
theorem sublinear_fires_sharp (profile : LoadCapacityProfile) :
    residualMass fanObject profile ≤ 8 * surplusMass fanObject ∧
      surplusMass fanObject = 1 := by
  obtain ⟨massBound, -, -⟩ := sublinear_fires profile
  rw [undischargedMass_eq profile, add_zero] at massBound
  exact ⟨massBound, surplusMass_eq⟩

end Witness

end Hypostructure.Graph.TypeBBridgeResidual
