import Hypostructure.Graph.Contracts.TypeB.Ledger

/-!
# Contracts: the Type B certificate, B1 and B2 ledger

`def:marked-typeB-fan`, `lem:typeB-direct-fan-window-cycles`,
`lem:typeB-two-window-cycles`, `lem:typeB-hybrid-incidence-budget`,
`lem:typeB-hybrid-B1`, `def:typeB-bridge-statements`,
`lem:typeB-bridge-to-overlap`, `prop:typeB-global-local-bridge`,
`prop:typeB-bridge-reduction` and `def:typeB-residual-mass`, each evaluated at
the Type B support of the selected counterexample.  Every decision below
splits its predicate at the support its predecessor fact is about
(`TypeBLaneAt.split`).
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## Certificate labelling -/

/-- **Nodes `[71]`/`[80]`**: at the capped Type B support, every assigned
centre carries G's canonical fan-certificate labelling, or one of them is a
fan-certificate residual centre (the canonical labelling is absent there). -/
theorem fanCertificate_split
    (cap : TypeBFanCertificateCapStatement data object) :
    TypeBFanCertificateMarkedStatement data object ∨
      TypeBFanCertificateResidualStatement data object := by
  rcases TypeBLaneAt.split (fun _core centres => ∀ centre ∈ centres,
      (canonicalFanCertificateLabelling data object centre).isSome)
      cap with marked | residual
  · refine Or.inl (TypeBLaneAt.imp (fun _core _centres _member holds => ?_)
      marked)
    intro centre centreMember
    obtain ⟨marking, markingEq⟩ :=
      Option.isSome_iff_exists.mp (holds.2 centre centreMember)
    exact ⟨marking, markingEq, (holds.1 centre centreMember).2 marking markingEq⟩
  · refine Or.inr (TypeBLaneAt.imp (fun _core _centres member holds => ?_)
      residual)
    have notAll := holds.2
    push Not at notAll
    obtain ⟨centre, centreMember, absent⟩ := notAll
    exact ⟨centre, centreMember, TypeBLaneMember.high member centre centreMember,
      Option.not_isSome_iff_eq_none.mp absent⟩

/-! ## Direct fan-window cycles -/

/-- **Nodes `[72]`/`[81]`, the direct cycles inside the local fan-window
ledger** (`lem:typeB-direct-fan-window-cycles`, `lem:typeB-two-window-cycles`):
a direct fan-window configuration at `P₀` builds a cycle of accepted length,
which the selection denies, so every assigned centre of the marked Type B
support is direct-cycle free. -/
theorem typeBFanDirectCycleFree
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (marked : TypeBFanCertificateMarkedStatement data object) :
    TypeBFanDirectCycleFreeStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member holds =>
      ⟨holds, fun _centre _centreMember configuration =>
        avoids (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
          (canonicalWindowPacking_spec data object).1 configuration)⟩)
    marked

/-! ## The hybrid B1 fan ledger -/

/-- `lem:typeB-hybrid-incidence-budget` and `lem:typeB-hybrid-B1` at one marked
high centre: the non-hub incidences of distinct cubic-closed neighbours are
disjoint, they number `(δ - 1)c`, their half-credit pays the deficit, the
non-window credit pays the non-window demand, and two closed neighbours make the
deficit positive. -/
theorem hybridB1Entry
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (quadrilateral : data.LengthOK 4)
    (three : 3 ≤ data.threshold)
    (deficitSlack :
      data.dischargeScale * data.threshold <
        2 * data.dischargeScale + (data.threshold + 2))
    {centre : object.Vertex}
    (high : Graph.IsHighCentre object data.threshold centre)
    (capSlack : object.degree centre + 1 ≤ data.dischargeScale * data.threshold)
    (envelope windowSupport : Finset object.Vertex) :
    HybridB1Entry data object centre envelope windowSupport := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro left leftMember right rightMember different shared leftIncidence
      rightIncidence
    exact Graph.TypeBHybridIncidence.endpoints_not_shared avoids quadrilateral
      (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp leftMember)
      (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp rightMember)
      different leftIncidence rightIncidence
  · exact Graph.TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences
      _ _ _ _ _
  · exact Graph.TypeBHybridIncidence.hybridCapacity_pays _ _ _ _ _ _
      three capSlack
  · exact Graph.TypeBHybridIncidence.nonWindowCredit_ge_demand _ _ _ _ _ _
      three capSlack
  · intro twoLe
    exact Graph.TypeBHybridIncidence.positive_deficit_of_two_le_closedCount
      _ _ _ _ _ twoLe high deficitSlack

/-- **Nodes `[72]`/`[81]`, B1**: the local B1 ledger at every assigned centre of
the direct-cycle-free, certificate-marked Type B support, at its assigned fan
envelope over `W₀`: the marking caps the degree by the label packing number,
which the registered discharge scale covers. -/
theorem typeBFanHybridEntry
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (quadrilateral : data.LengthOK 4)
    (three : 3 ≤ data.threshold)
    (fanCapSlack :
      Graph.WindowCurvature.fanPackingCap data.windowOrder + 1 ≤
        data.dischargeScale * data.threshold)
    (deficitSlack :
      data.dischargeScale * data.threshold <
        2 * data.dischargeScale + (data.threshold + 2))
    (free : TypeBFanDirectCycleFreeStatement data object) :
    TypeBFanHybridEntryStatement data object := by
  refine TypeBLaneAt.imp (fun _core _centres member holds centre centreMember => ?_)
    free
  obtain ⟨_marking, _markingEq, capped⟩ := holds.1 centre centreMember
  exact hybridB1Entry avoids quadrilateral three deficitSlack
    (TypeBLaneMember.high member centre centreMember)
    (le_trans (Nat.succ_le_succ capped) fanCapSlack) _ _

/-! ## The B2 disjoint ledger -/

/-- The canonical minimal overlap obstruction of a certificate-marked support
whose B2 disjoint choice fails (`lem:typeB-bridge-to-overlap`). -/
theorem canonicalOverlapObstruction_of_not_hasDisjointChoice
    {core centres : Finset object.Vertex}
    (member : TypeBLaneMember data object core centres)
    (failure : ¬ Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres
      centres) :
    ∃ obstruction, canonicalOverlapObstruction data object core centres =
      some obstruction :=
  canonicalOverlapObstruction_spec
    ((not_hasDisjointChoice_iff_overlapObstruction
      (TypeBLaneMember.high member)).mp failure)

/-- **Node `[72]`: local fan-window ledger complete; B2 disjointness holds?**
At the Type B support of the B1 fact (with its `[71]` marking), B2 holds, or the
support carries G's canonical minimal overlap obstruction
(`lem:typeB-bridge-to-overlap`). -/
theorem b2_split
    (hybrid : TypeBFanHybridEntryStatement data object)
    (marked : TypeBFanCertificateMarkedStatement data object) :
    TypeBB2ChoiceStatement data object ∨ TypeBB2ObstructionStatement data object := by
  rcases TypeBLaneAt.split (fun core centres =>
      Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
        data.dischargeScale (canonicalWindowPacking data object) core centres
        centres) (TypeBLaneAt.and hybrid marked) with holds | fails
  · exact Or.inl (TypeBLaneAt.imp (fun _core _centres _member holds =>
      ⟨holds.1.1, holds.1.2, holds.2⟩) holds)
  · exact Or.inr (TypeBLaneAt.imp (fun _core _centres member failure =>
      ⟨failure.1.2, canonicalOverlapObstruction_of_not_hasDisjointChoice member
        failure.2⟩) fails)

/-- **Node `[81]`** (degree-four arm, tex 1019): at the Type B support of the B1
fact (with its `[71]` marking), every assigned centre has `c ≤ 1` or B2 holds;
otherwise some centre has `c ≥ 2` and B2 fails, so the support carries G's
canonical minimal overlap obstruction (`lem:typeB-bridge-to-overlap`). -/
theorem degreeFourLedger_split
    (hybrid : TypeBFanHybridEntryStatement data object)
    (marked : TypeBFanCertificateMarkedStatement data object) :
    TypeBDegreeFourLedgerStatement data object ∨
      TypeBDegreeFourOverlapStatement data object := by
  rcases TypeBLaneAt.split (fun core centres =>
      (∀ centre ∈ centres,
        Graph.TypeBFanIncidence.closedCount object data.threshold
          (typeBFanEnvelope core centres centre) centre ≤ 1) ∨
      Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
        data.dischargeScale (canonicalWindowPacking data object) core centres
        centres) (TypeBLaneAt.and hybrid marked) with holds | fails
  · refine Or.inl (TypeBLaneAt.imp (fun _core _centres _member holds => ?_) holds)
    rcases holds.2 with small | choice
    · exact ⟨holds.1.1, Or.inl small⟩
    · exact ⟨holds.1.1, Or.inr ⟨holds.1.2, choice⟩⟩
  · refine Or.inr (TypeBLaneAt.imp (fun _core _centres member failure => ?_) fails)
    have noneSmall := failure.2
    push Not at noneSmall
    obtain ⟨⟨centre, centreMember, two⟩, noChoice⟩ := noneSmall
    exact ⟨⟨centre, centreMember, two⟩, failure.1.2,
      canonicalOverlapObstruction_of_not_hasDisjointChoice member noChoice⟩

/-- **B2(a)--(d) at a B2 support** (`def:typeB-bridge-statements`): the canonical
disjoint choice refines every candidate charge, and --- the core's high centres
being assigned on every lane --- the canonical B2 ledger exists with its exact
augmented refinement, its post-ledger hygiene and its grouped envelope. -/
theorem typeBB2LedgerAt
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    {core centres : Finset object.Vertex}
    (member : TypeBLaneMember data object core centres)
    (b2 : TypeBB2At data object core centres) :
    TypeBB2LedgerAt data object core centres := by
  classical
  refine ⟨b2, ?_, ?_⟩
  · obtain ⟨selected, selectedEq⟩ := canonicalTypeBChoice_spec b2.2
    exact ⟨selected, selectedEq, fun centre centreMember =>
      (Graph.TypeBRefinedSupport.mem_candidateFamily_iff.mp
        (selected.eligible centre centreMember)).2.entryRefines⟩
  · obtain ⟨ledger, ledgerEq⟩ := canonicalTypeBDisjointChoice_spec
      ⟨b2.2, TypeBLaneMember.high member, TypeBLaneMember.centres_subset member⟩
    obtain ⟨components, grouped⟩ := disjointLedgerCoreClosure avoids baseline
      uncompressible normalized (TypeBLaneMember.core_subset_remainder member)
      ledger
    exact ⟨ledger, ledgerEq, ledger.exactAugmentedLedgerRefinement, components,
      grouped⟩

/-- `prop:typeB-bridge-reduction` as an inequality: on any B2 ledger of the
support, the remaining core carries the whole deficit,
`Σ_{remaining core} ch ≤ s·No(X)`. -/
theorem remainingCoreCharge_le
    {core centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres) :
    RemainingCoreCharge data object ledger ≤
      typeBScaledNetCharge data object core centres :=
  Graph.TypeBEnvelopeCharge.remainingCore_le_scaledNetCharge ledger
    ledger.exactAugmentedLedgerRefinement

/-- **Node `[74]`**, B2(a)--(d) on the B2 yes arm of `[72]`: the B2 fact at the
Type B support makes it B2-paid. -/
theorem typeBDisjointLedger
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (choice : TypeBB2ChoiceStatement data object) :
    TypeBDisjointLedgerStatement data object :=
  TypeBLaneAt.imp (fun _core _centres member holds =>
      typeBB2LedgerAt avoids baseline uncompressible normalized member holds.2)
    choice

/-- **Node `[74]`**, `prop:typeB-bridge-reduction` on the canonical B2 ledger of
the Type B support: its remaining core carries the whole deficit. -/
theorem typeBExcluded (ledgers : TypeBDisjointLedgerStatement data object) :
    TypeBExcludedStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member holds => by
      obtain ⟨_b2, _choice, ledger, ledgerEq, _exact, _components, _grouped⟩ :=
        holds
      exact ⟨ledger, ledgerEq, remainingCoreCharge_le ledger⟩)
    ledgers

/-- **Node `[82]`**, `lem:typeB-exclusion` Step 1 on the degree-four arm, and
`prop:typeB-bridge-reduction` on its B2-paid case: a centre of degree `δ + 1`
with at most one cubic-closed neighbour has `s·D_B = s·c − s·δ + (δ + 2) ≤ 0` at
the registered `δ = 3`, `s = 4`, so its marked fan is certificate-closed;
otherwise the `[81]` yes arm is B2-paid and its remaining core carries the whole
deficit. -/
theorem typeBDegreeFourClosed
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (thresholdEq : data.threshold = 3) (scaleEq : data.dischargeScale = 4)
    (degreeFour : TypeBFanDegreeFourCentresStatement data object)
    (ledger : TypeBDegreeFourLedgerStatement data object) :
    TypeBDegreeFourClosedStatement data object := by
  refine TypeBLaneAt.imp (fun _core _centres member both => ?_)
    (TypeBLaneAt.and degreeFour ledger)
  rcases both.2.2 with small | paid
  · refine Or.inl ⟨small, fun centre centreMember => ?_⟩
    have degree := both.1 centre centreMember
    have count := small centre centreMember
    unfold Graph.TypeBFanIncidence.IsCertificateClosed
      Graph.TypeBFanIncidence.scaledDeficit
    rw [thresholdEq] at count
    rw [degree, thresholdEq, scaleEq]
    push_cast
    omega
  · have ledgerAt := typeBB2LedgerAt avoids baseline uncompressible normalized
      member paid
    obtain ⟨_b2, _choice, selected, selectedEq, _exact, _components, _grouped⟩ :=
      id ledgerAt
    exact Or.inr ⟨ledgerAt, selected, selectedEq, remainingCoreCharge_le selected⟩

/-- `prop:typeB-global-local-bridge`: at the B2-failure support, target safety,
the normal form at every demand, and the direct-cycle exclusion forced by
target safety give all five clauses of `lem:typeB-global-local-reflection` at
G's canonical minimal overlap obstruction of the support, whose core lies in the
remainder of `P₀`. -/
theorem typeBGlobalLocalBridge
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (normal : HighCentreNormalFormStatement data object)
    (obstructed : TypeBB2ObstructionStatement data object) :
    TypeBGlobalLocalBridgeStatement data object := by
  refine TypeBLaneAt.imp (fun _core _centres member present => ?_) obstructed
  obtain ⟨marked, obstruction, obstructionEq⟩ := present
  refine ⟨marked, obstruction, obstructionEq, ?_⟩
  have directFree : ∀ hub ∈ obstruction.demands,
      Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
        data.LengthOK (canonicalWindowPacking data object) hub := by
    intro _hub _hubMem configuration
    exact avoids
      (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
        (canonicalWindowPacking_spec data object).1
        configuration)
  exact Graph.TypeBRefinedSupport.globalLocalReflectionACE
    (presentation := data.typeABPresentation)
    (order := data.windowOrder) (LengthOK := data.LengthOK)
    (threshold := data.threshold) (dischargeScale := data.dischargeScale)
    obstruction (TypeBLaneMember.core_subset_remainder member)
    (by simpa [Graph.TypeAB.ContextuallyDyadicSafe,
      Parameters.typeABPresentation] using avoids)
    (fun hub hubMem => normal hub (obstruction.demands_high hub hubMem))
    directFree

/-- **Node `[83]`**: the degree-four overlap obstruction is reflected exactly as
at `[73]` (`prop:typeB-global-local-bridge`). -/
theorem typeBGlobalLocalBridge_of_degreeFour
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (normal : HighCentreNormalFormStatement data object)
    (overlap : TypeBDegreeFourOverlapStatement data object) :
    TypeBGlobalLocalBridgeStatement data object :=
  typeBGlobalLocalBridge avoids normal
    (TypeBLaneAt.imp (fun _ _ _ holds => holds.2) overlap)

/-! ## The Type B residual mass -/

/-- `def:typeB-residual-mass` at one high centre: the negative part of its
assigned fan envelope is paid by its assigned surplus at the registered mass
factor. -/
theorem centreBridgeMassBound
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    {core centres : Finset object.Vertex} {centre : object.Vertex}
    (high : Graph.IsHighCentre object data.threshold centre) :
    CentreBridgeMassBound data object core centres centre :=
  Graph.TypeBEnvelopeCharge.envelopeNegativePart_le _ high massSlack

/-- `lem:typeB-bridge-deficit-bound` at the Type B support of `G`: the core's
high centres are assigned on every lane. -/
theorem typeBBridgeDeficitBoundAt
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    {core centres : Finset object.Vertex}
    (member : TypeBLaneMember data object core centres) :
    TypeBBridgeDeficitBoundAt data object core centres :=
  fun residual => Graph.TypeBEnvelopeCharge.bridgeDeficitBound_assigned object
    core centres massSlack baseline (TypeBLaneMember.centres_subset member) residual

/-- **Nodes `[75]`/`[84]`**: the certificate-residual support is a Type B bridge
residual (`def:typeB-bridge-statements` (i)); its negative part is charged to
its assigned surplus (`lem:typeB-bridge-deficit-bound`). -/
theorem typeBFanCertificateResidualMass
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (residual : TypeBFanCertificateResidualStatement data object) :
    TypeBFanCertificateResidualMassStatement data object :=
  TypeBLaneAt.imp (fun _core _centres member holds =>
      ⟨holds, typeBBridgeDeficitBoundAt baseline massSlack member⟩) residual

/-- **Nodes `[73]`/`[75]`, `[83]`/`[84]`**: the obstructed support is a Type B
bridge residual (`def:typeB-bridge-statements` (ii)); its negative part is
charged to its assigned surplus (`lem:typeB-bridge-deficit-bound`). -/
theorem typeBOverlapObstructionMass
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (reflected : TypeBGlobalLocalBridgeStatement data object) :
    TypeBOverlapObstructionMassStatement data object :=
  TypeBLaneAt.imp (fun _core _centres member holds =>
    ⟨holds.1, holds.2, typeBBridgeDeficitBoundAt baseline massSlack member⟩)
    reflected

/-- A canonical minimal overlap obstruction refutes B2 at the support. -/
theorem not_typeBB2At_of_obstruction {core centres : Finset object.Vertex}
    {obstruction}
    (_obstructionEq : canonicalOverlapObstruction data object core centres =
      some obstruction) :
    ¬ TypeBB2At data object core centres := fun b2 =>
  obstruction.noDisjointChoice
    (hasDisjointChoice_mono obstruction.demands_subset b2.2)

/-- A fan-certificate residual centre refutes B2 at the support (B2 is stated
for supports without fan-certificate residual centres). -/
theorem not_typeBB2At_of_residual {core centres : Finset object.Vertex}
    (residual : ∃ centre ∈ centres, Graph.IsHighCentre object data.threshold centre ∧
      canonicalFanCertificateLabelling data object centre = none) :
    ¬ TypeBB2At data object core centres := by
  rintro ⟨marked, _choice⟩
  obtain ⟨centre, centreMember, _high, absent⟩ := residual
  obtain ⟨_marking, markingEq, _capped⟩ := marked centre centreMember
  rw [absent] at markingEq
  cases markingEq

/-- **Node `[76]`** on the B2 arm (`[74]` → `[76]`): the B2-paid support's
remaining core carries the whole deficit (the ledger fact and the bridge
reduction of `[74]`). -/
theorem typeBExclusionResidual
    (ledgers : TypeBDisjointLedgerStatement data object)
    (excluded : TypeBExcludedStatement data object) :
    TypeBExclusionResidualStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member both => Or.inl both)
    (TypeBLaneAt.and ledgers excluded)

/-- **Node `[76]`/`[85]`** on the certificate-residual fan-mass arm (`[75]` →
`[76]`, `[84]` → `[85]`): B2 fails and the `[75]`/`[84]` charge applies. -/
theorem typeBExclusionResidual_of_certificateMass
    (mass : TypeBFanCertificateResidualMassStatement data object) :
    TypeBExclusionResidualStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member holds =>
      Or.inr ⟨not_typeBB2At_of_residual holds.1, holds.2⟩) mass

/-- **Node `[76]`/`[85]`** on the B2-failure fan-mass arm (`[73]` → `[75]` →
`[76]`, `[83]` → `[84]` → `[85]`): B2 fails at the canonical obstruction and the
`[75]`/`[84]` charge applies. -/
theorem typeBExclusionResidual_of_obstructionMass
    (mass : TypeBOverlapObstructionMassStatement data object) :
    TypeBExclusionResidualStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member holds => by
      obtain ⟨_marked, ⟨_obstruction, obstructionEq, _reflected⟩, bound⟩ := holds
      exact Or.inr ⟨not_typeBB2At_of_obstruction obstructionEq, bound⟩) mass

/-- **Node `[85]`** on the `[82]` arm: a B2-paid support keeps its deficit in the
remaining core; a certificate-closed support at which B2 fails is a Type B
bridge residual (`def:typeB-bridge-statements` (ii)) charged by
`lem:typeB-bridge-deficit-bound`, and one at which B2 holds is B2-paid. -/
theorem typeBExclusionResidual_of_degreeFourClosed
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (closed : TypeBDegreeFourClosedStatement data object) :
    TypeBExclusionResidualStatement data object := by
  classical
  refine TypeBLaneAt.imp (fun _core _centres member holds => ?_) closed
  rcases holds with _certificateClosed | paid
  · by_cases b2 : TypeBB2At data object _core _centres
    · have ledgerAt := typeBB2LedgerAt avoids baseline uncompressible normalized
        member b2
      obtain ⟨_b2, _choice, selected, selectedEq, _exact, _components, _grouped⟩ :=
        id ledgerAt
      exact Or.inl ⟨ledgerAt, selected, selectedEq, remainingCoreCharge_le selected⟩
    · exact Or.inr ⟨b2, typeBBridgeDeficitBoundAt baseline massSlack member⟩
  · exact Or.inl paid

/-- **Node `[77]`**, the Type B entry into route `8`: a negative Type B support
hands a negative remaining core to route `8` on the B2 arm (its remaining core
carries the whole deficit, `[76]`), or is a bridge residual charged to its
surplus. -/
theorem typeBRoute8Entry
    (exclusion : TypeBExclusionResidualStatement data object) :
    TypeBRoute8EntryStatement data object :=
  TypeBLaneAt.imp (fun _core _centres _member holds negative => by
      rcases holds with ⟨_ledgerAt, ledger, ledgerEq, carried⟩ | residual
      · exact Or.inl ⟨ledger, ledgerEq, lt_of_le_of_lt carried negative⟩
      · exact Or.inr residual) exclusion

end Hypostructure.Graph.Contracts.TypeB
