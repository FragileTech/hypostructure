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
(`TypeBLaneAll.split`).
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## Certificate labelling -/

/-- **Nodes `[71]`/`[80]`**: at the capped Type B support, every assigned
centre carries a fan-certificate labelling, or one of them is a fan-certificate
residual centre. -/
theorem fanCertificate_split
    (cap : TypeBFanCertificateCapStatement data object) :
    TypeBFanCertificateMarkedStatement data object ∨
      TypeBFanCertificateResidualStatement data object := by
  rcases TypeBLaneAll.split (fun _core centres => ∃ centre ∈ centres,
      IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre))
      cap with residual | marked
  · refine Or.inr (TypeBLaneSome.imp (fun _core _centres member holds => ?_)
      residual)
    obtain ⟨centre, centreMember, unmarked⟩ := holds.2
    exact ⟨centre, centreMember, TypeBLaneMember.high member centre centreMember,
      unmarked⟩
  · refine Or.inl (TypeBLaneAll.imp (fun _core _centres _member holds => ?_)
      marked)
    intro centre centreMember
    have labelled : Nonempty
        (Graph.FanCertificateLabelling object data.windowOrder centre) := by
      by_contra none
      exact holds.2 ⟨centre, centreMember, not_nonempty_iff.mp none⟩
    obtain ⟨marking⟩ := labelled
    exact ⟨marking, (holds.1 centre centreMember).2 marking⟩

/-! ## Direct fan-window cycles -/

/-- **Nodes `[72]`/`[81]`, first half**: at the marked Type B support, some
assigned centre carries a direct fan-window configuration at `P₀`, or none
does. -/
theorem directCycle_split
    (marked : TypeBFanCertificateMarkedStatement data object) :
    TypeBFanDirectCycleStatement data object ∨
      TypeBFanDirectCycleFreeStatement data object := by
  rcases TypeBLaneAll.split (fun _core centres => ∃ centre ∈ centres,
      Graph.IsHighCentre object data.threshold centre ∧
        Graph.TypeBDirectCycle.DirectCycleConfiguration object data.windowOrder
          data.LengthOK (canonicalWindowPacking data object) centre)
      marked with cycle | free
  · exact Or.inl (TypeBLaneSome.imp (fun _ _ _ holds => holds.2) cycle)
  · exact Or.inr (TypeBLaneAll.imp (fun _core _centres _member holds centre
        centreMember high configuration =>
      holds.2 ⟨centre, centreMember, high, configuration⟩) free)

/-- A direct fan-window configuration at `P₀` builds a cycle of accepted
length. -/
theorem hasCycleWithLength_of_typeBFanDirectCycle
    (cycle : TypeBFanDirectCycleStatement data object) :
    Graph.HasCycleWithLength data.LengthOK object := by
  obtain ⟨_core, _centres, _member, _centre, _centreMember, _high, configuration⟩ :=
    TypeBLaneSome.exists cycle
  exact Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
    (canonicalWindowPacking_spec data object).1
    configuration

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

/-- **Nodes `[72]`/`[81]`, B1**: the local B1 ledger at every marked assigned
centre of the Type B support, at its canonical fan envelope over `W₀`: the
marking caps the degree by the label packing number, which the registered
discharge scale covers. -/
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
    (marked : TypeBFanCertificateMarkedStatement data object) :
    TypeBFanHybridEntryStatement data object := by
  refine TypeBLaneAll.imp (fun _core _centres member holds centre centreMember => ?_)
    marked
  obtain ⟨_marking, capped⟩ := holds centre centreMember
  exact hybridB1Entry avoids quadrilateral three deficitSlack
    (TypeBLaneMember.high member centre centreMember)
    (le_trans (Nat.succ_le_succ capped) fanCapSlack) _ _

/-! ## The B2 disjoint ledger -/

/-- **Nodes `[72]`/`[81]`, B2** (`lem:typeB-bridge-to-overlap`): at the
direct-cycle-free Type B support, the assigned centres admit a disjoint choice
at `P₀`, or the support carries a minimal overlap obstruction. -/
theorem b2_split
    (free : TypeBFanDirectCycleFreeStatement data object) :
    TypeBB2ChoiceStatement data object ∨ TypeBB2ObstructionStatement data object := by
  rcases TypeBLaneAll.split (fun core centres =>
      ¬ Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
        data.dischargeScale (canonicalWindowPacking data object) core centres
        centres) free with fails | holds
  · exact Or.inr (TypeBLaneSome.imp (fun _core _centres member failure =>
      (not_hasDisjointChoice_iff_overlapObstruction
        (TypeBLaneMember.high member)).mp failure.2) fails)
  · exact Or.inl (TypeBLaneAll.imp (fun _ _ _ holds => not_not.mp holds.2) holds)

/-- `prop:typeB-global-local-bridge`: at the B2-failure support, target safety,
the normal form at every demand, and the direct-cycle exclusion forced by
target safety give all five clauses of `lem:typeB-global-local-reflection` at
every minimal overlap obstruction on a canonical core. -/
theorem typeBGlobalLocalBridge
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (normal : HighCentreNormalFormStatement data object)
    (obstructed : TypeBB2ObstructionStatement data object) :
    TypeBGlobalLocalBridgeStatement data object := by
  refine TypeBLaneSome.imp (fun _core _centres _member present =>
    ⟨present, fun piece _pieceEq obstruction => ?_⟩) obstructed
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
    obstruction
    (by simpa [Graph.TypeAB.ContextuallyDyadicSafe,
      Parameters.typeABPresentation] using avoids)
    (fun hub hubMem => normal hub (obstruction.demands_high hub hubMem))
    directFree

/-- **Node `[74]`/`[82]`**, `def:typeB-bridge-statements` B2(a)--(d) at the
B2-success support: its canonical disjoint choice refines every candidate
charge; on a canonical core whose high centres are assigned, the canonical B2
ledger has its exact augmented refinement, and remainder normalization gives
the post-ledger hygiene of `lem:typeB-postledger-core-hygiene` and the grouped
decorated envelope of B2(d). -/
theorem typeBDisjointLedger
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (choice : TypeBB2ChoiceStatement data object) :
    TypeBDisjointLedgerStatement data object := by
  classical
  refine TypeBLaneAll.imp (fun core centres member hasChoice => ⟨?_, ?_⟩) choice
  · obtain ⟨selected, selectedEq⟩ := canonicalTypeBChoice_spec hasChoice
    exact ⟨selected, selectedEq, fun centre centreMember =>
      (Graph.TypeBRefinedSupport.mem_candidateFamily_iff.mp
        (selected.eligible centre centreMember)).2.entryRefines⟩
  · intro piece pieceEq subset
    subst pieceEq
    obtain ⟨ledger, ledgerEq⟩ := canonicalTypeBDisjointChoice_spec
      ⟨hasChoice, TypeBLaneMember.high member, subset⟩
    obtain ⟨components, grouped⟩ := disjointLedgerCoreClosure avoids baseline
      uncompressible normalized ledger
    exact ⟨ledger, ledgerEq, ledger.exactAugmentedLedgerRefinement, components,
      grouped⟩

/-- `prop:typeB-bridge-reduction`: the exact augmented refinement of a B2
disjoint ledger pays every selected entry, so a nonnegative remaining core
charge gives `N₀ ≥ 0`. -/
theorem nonNegativeNetCharge_of_remainingCoreCharge
    {core centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres)
    (clean : 0 ≤ RemainingCoreCharge data object ledger) :
    object.NonNegativeNetCharge core data.threshold data.dischargeScale := by
  have selectedNonnegative : (0 : Int) ≤ ledger.selectedEntryPayment₂ := by
    rw [Graph.TypeBRefinedSupport.DisjointLedger.selectedEntryPayment₂]
    refine Finset.sum_nonneg ?_
    intro centre _member
    exact (ledger.entry_isCandidate centre.1 centre.2).entryRefines
  exact Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative
    ledger ledger.exactAugmentedLedgerRefinement selectedNonnegative clean

/-- **Node `[74]`/`[82]`**, `prop:typeB-bridge-reduction` on the canonical B2
ledger of the Type B support. -/
theorem typeBExcluded (ledgers : TypeBDisjointLedgerStatement data object) :
    TypeBExcludedStatement data object :=
  TypeBLaneAll.imp (fun _core _centres _member _holds ledger _ledgerEq clean =>
    nonNegativeNetCharge_of_remainingCoreCharge ledger clean) ledgers

/-- **Node `[76]`/`[85]`**: a negative Type B support on a canonical core keeps
a negative remaining core on its canonical B2 ledger, by the bridge reduction on
that same ledger. -/
theorem typeBExclusionResidual
    (ledgers : TypeBDisjointLedgerStatement data object)
    (excluded : TypeBExcludedStatement data object) :
    TypeBExclusionResidualStatement data object := by
  refine TypeBLaneAll.imp (fun core centres _member both piece pieceEq subset
      negative => ?_) (TypeBLaneAll.and ledgers excluded)
  obtain ⟨ledger, ledgerEq, exact, components, _grouped⟩ :=
    both.1.2 piece pieceEq subset
  refine ⟨ledger, ledgerEq, exact, components, fun clean => ?_⟩
  subst pieceEq
  exact ((object.not_negativeNetCharge_iff piece.vertices data.threshold
    data.dischargeScale).mpr (both.2 ledger ledgerEq clean)) negative

/-! ## The Type B residual mass -/

/-- `def:typeB-residual-mass` at one high centre: the negative part of its
canonical fan envelope is paid by its assigned surplus at the registered mass
factor. -/
theorem centreBridgeMassBound
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    {centre : object.Vertex}
    (high : Graph.IsHighCentre object data.threshold centre) :
    CentreBridgeMassBound data object centre :=
  Graph.TypeBEnvelopeCharge.envelopeNegativePart_le _ high massSlack

/-- **Nodes `[75]`/`[84]`**: the fan-certificate residual centre is charged to
the bridge fan mass. -/
theorem typeBFanCertificateResidualMass
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (residual : TypeBFanCertificateResidualStatement data object) :
    TypeBFanCertificateResidualMassStatement data object :=
  TypeBLaneSome.imp (fun _core _centres _member holds => by
      obtain ⟨centre, centreMember, high, unmarked⟩ := holds
      exact ⟨centre, centreMember, high, unmarked,
        centreBridgeMassBound massSlack high⟩) residual

/-- **Nodes `[73]`/`[75]`, `[83]`/`[84]`**: the centres of the obstructed
support are charged to the bridge fan mass. -/
theorem typeBOverlapObstructionMass
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (reflected : TypeBGlobalLocalBridgeStatement data object) :
    TypeBOverlapObstructionMassStatement data object :=
  TypeBLaneSome.imp (fun _core _centres member holds =>
    ⟨holds.1, fun centre centreMember =>
      centreBridgeMassBound massSlack
        (TypeBLaneMember.high member centre centreMember)⟩) reflected

/-- **Nodes `[76]`/`[85]`**: the centres of the negative post-ledger residual
are charged to the bridge fan mass. -/
theorem typeBExclusionResidualMass
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (residual : TypeBExclusionResidualStatement data object) :
    TypeBExclusionResidualMassStatement data object :=
  TypeBLaneAll.imp (fun _core _centres member _holds _ledger _ledgerEq _negative
      centre centreMember =>
    centreBridgeMassBound massSlack
      (TypeBLaneMember.high member centre centreMember)) residual

end Hypostructure.Graph.Contracts.TypeB
