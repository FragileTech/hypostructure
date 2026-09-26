import Hypostructure.Graph.Contracts.TypeB.Support

/-!
# Contracts: the Type B certificate, B1 and B2 ledger

`def:marked-typeB-fan`, `lem:typeB-direct-fan-window-cycles`,
`lem:typeB-two-window-cycles`, `lem:typeB-hybrid-incidence-budget`,
`lem:typeB-hybrid-B1`, `def:typeB-bridge-statements`,
`lem:typeB-bridge-to-overlap`, `prop:typeB-global-local-bridge`,
`prop:typeB-bridge-reduction` and `def:typeB-residual-mass`, each stated once
over the Type B support family.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## Certificate labelling -/

/-- The certificate split: the residual arm is the exact negation of the
marked arm. -/
theorem typeBFanCertificateResidual_iff_not_marked :
    TypeBFanCertificateResidualStatement data object ↔
      ¬ TypeBFanCertificateMarkedStatement data object := by
  constructor
  · rintro ⟨packing, core, centres, support, centre, member, unmarked⟩ marked
    obtain ⟨marking⟩ := marked packing core centres support centre member
    exact unmarked.false marking
  · intro notMarked
    classical
    by_contra noResidual
    apply notMarked
    intro packing core centres support centre member
    by_contra unmarked
    exact noResidual ⟨packing, core, centres, support, centre, member,
      not_nonempty_iff.mp unmarked⟩

/-! ## Direct fan-window cycles -/

/-- The direct-cycle split: the free arm is the exact negation. -/
theorem typeBFanDirectCycleFree_iff_not_directCycle :
    TypeBFanDirectCycleFreeStatement data object ↔
      ¬ TypeBFanDirectCycleStatement data object := by
  constructor
  · rintro free ⟨packing, core, centres, support, centre, member, configuration⟩
    exact free packing core centres support centre member configuration
  · intro noCycle packing core centres support centre member configuration
    exact noCycle ⟨packing, core, centres, support, centre, member, configuration⟩

/-- `lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`: a
direct fan-window configuration at a Type B support closes an accepted cycle. -/
theorem hasCycleWithLength_of_typeBFanDirectCycle
    (cycle : TypeBFanDirectCycleStatement data object) :
    Graph.HasCycleWithLength data.LengthOK object := by
  obtain ⟨_packing, _core, _centres, support, _centre, _member, configuration⟩ :=
    cycle
  exact Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
    (TypeBSupport.valid support) configuration

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

/-- The local B1 ledger at every marked assigned centre: the marking caps the
degree by the label packing number, which the registered discharge scale
covers. -/
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
    (marked : TypeBFanCertificateMarkedStatement data object)
    (cap : TypeBFanCertificateCapStatement data object) :
    TypeBFanHybridEntryStatement data object := by
  intro packing core centres support centre member envelope windowSupport
  obtain ⟨marking⟩ := marked packing core centres support centre member
  have capped := (cap packing core centres support centre member).2 marking
  exact hybridB1Entry avoids quadrilateral three deficitSlack
    (TypeBSupport.high support centre member)
    (le_trans (Nat.succ_le_succ capped) fanCapSlack) envelope windowSupport

/-! ## The B2 disjoint ledger -/

/-- `lem:typeB-bridge-to-overlap` on the family: the obstruction arm is the
exact negation of the B2 choice arm. -/
theorem typeBB2Obstruction_iff_not_choice :
    TypeBB2ObstructionStatement data object ↔
      ¬ TypeBB2ChoiceStatement data object := by
  constructor
  · rintro ⟨packing, core, centres, support, obstruction⟩ choice
    exact ((not_hasDisjointChoice_iff_overlapObstruction
      (TypeBSupport.high support)).mpr obstruction)
      (choice packing core centres support)
  · intro noChoice
    classical
    by_contra noObstruction
    apply noChoice
    intro packing core centres support
    by_contra failure
    exact noObstruction ⟨packing, core, centres, support,
      (not_hasDisjointChoice_iff_overlapObstruction
        (TypeBSupport.high support)).mp failure⟩

/-- `prop:typeB-global-local-bridge`: target safety, the normal form at every
demand, and the direct-cycle exclusion forced by target safety give all five
clauses of `lem:typeB-global-local-reflection` at every minimal overlap
obstruction of a Type B support with a canonical core. -/
theorem typeBGlobalLocalBridge
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (normal : HighCentreNormalFormStatement data object) :
    TypeBGlobalLocalBridgeStatement data object := by
  intro packing piece centres support obstruction
  have directFree : ∀ hub ∈ obstruction.demands,
      Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
        data.LengthOK packing hub := by
    intro _hub _hubMem configuration
    exact avoids
      (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
        (TypeBSupport.valid support) configuration)
  exact Graph.TypeBRefinedSupport.globalLocalReflectionACE
    (presentation := data.typeABPresentation)
    (order := data.windowOrder) (LengthOK := data.LengthOK)
    (threshold := data.threshold) (dischargeScale := data.dischargeScale)
    obstruction
    (by simpa [Graph.TypeAB.ContextuallyDyadicSafe,
      Parameters.typeABPresentation] using avoids)
    (fun hub hubMem => normal hub (obstruction.demands_high hub hubMem))
    directFree

/-- `def:typeB-bridge-statements` B2(a)--(d) on the B2-success arm.  Every Type B
support carries a disjoint choice whose entries refine their candidate charge.
On a canonical core the choice is the disjoint ledger, remainder normalization
gives the empty internal baseline core and window freeness, and every remaining
component carries the post-ledger hygiene of
`lem:typeB-postledger-core-hygiene`; the exit-`(7)` productions of remaining
components form the grouped decorated envelope. -/
theorem typeBDisjointLedger
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (choice : TypeBB2ChoiceStatement data object) :
    TypeBDisjointLedgerStatement data object := by
  classical
  refine ⟨?_, ?_⟩
  · intro packing core centres support
    obtain ⟨selected⟩ := choice packing core centres support
    exact ⟨selected, fun centre member =>
      (Graph.TypeBRefinedSupport.mem_candidateFamily_iff.mp
        (selected.eligible centre member)).2.entryRefines⟩
  · intro packing piece centres canonical
    have support := TypeBCanonicalSupport.support canonical
    have assigned := TypeBCanonicalSupport.assigned canonical
    have valid := TypeBSupport.valid support
    have maximal := TypeBSupport.maximal support
    let ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
        data.dischargeScale packing piece.vertices centres :=
      ⟨Classical.choice (choice packing piece.vertices centres support),
        TypeBAssignedCentres.high assigned,
        TypeBAssignedCentres.centres_subset assigned⟩
    have noBaselineSubsupport : ∀ subset : Finset object.Vertex,
        subset ⊆ object.remainderSupport packing →
          ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce subset) :=
      fun subset inside => (normalized packing valid maximal subset inside).2
    have pieceFree : Graph.InducedPathFree (object.induce piece.vertices)
        data.windowOrder :=
      Graph.FiniteObject.inducedPathFree_induce_of_forall object
        (fun subset inside =>
          (normalized packing valid maximal subset
            (inside.trans piece.vertices_subset_remainder)).1)
    have emptyInternal : Graph.TypeAB.EmptyInternalThreeCore
        data.typeABPresentation object piece.vertices :=
      Graph.TypeBPostLedgerCore.emptyInternalThreeCore_of_noBaselineSubsupport
        (threshold := data.threshold) rfl
        (fun subset inside =>
          noBaselineSubsupport subset
            (inside.trans piece.vertices_subset_remainder))
    have targetSafe : Graph.TypeAB.ContextuallyDyadicSafe
        data.typeABPresentation object := by
      simpa [Graph.TypeAB.ContextuallyDyadicSafe,
        Parameters.typeABPresentation] using avoids
    have hereditary : Graph.TypeAB.HereditarilyTargetUncompressible
        data.typeABPresentation object piece.vertices :=
      Graph.TypeAB.hereditarilyTargetUncompressible_of_emptyInternalThreeCore
        emptyInternal
    have components : PostLedgerComponents data object ledger :=
      fun component member =>
        Graph.TypeBPostLedgerCore.postLedgerCoreHygiene
          data.typeABPresentation ledger component member rfl
          noBaselineSubsupport pieceFree targetSafe hereditary baseline
    refine ⟨ledger, ledger.exactAugmentedLedgerRefinement, components, ?_⟩
    intro selectedComponents subset production
    have windowFree : ∀ component, component ∈ selectedComponents →
        handoffWindowFree data object
          (Graph.SupportComponents.Connected.vertices object
            ledger.remainingCore component) := by
      intro component member
      have componentData := components component (subset component member)
      constructor
      · intro window windowSubset induces
        exact (normalized packing valid maximal window
          (windowSubset.trans componentData.containedInRemainder)).1 induces
      · intro internal internalSubset
        exact (normalized packing valid maximal internal
          (internalSubset.trans componentData.containedInRemainder)).2
    refine ⟨Graph.TypeBMaximalCompletion.groupedOfComponentExitSeven
      ledger selectedComponents production avoids windowFree uncompressible,
      ?_, ?_⟩
    · intro component
      exact Graph.TypeBMaximalCompletion.Grouped.envelope_core
        ledger selectedComponents production avoids windowFree uncompressible
        component
    · intro centre
      exact Graph.TypeBMaximalCompletion.Grouped.mem_centres_iff
        ledger selectedComponents production avoids windowFree uncompressible
        centre

/-- `prop:typeB-bridge-reduction`: the exact augmented refinement of a B2
disjoint ledger pays every selected entry, so a nonnegative remaining core
charge gives `N₀(X) ≥ 0`. -/
theorem typeBExcluded : TypeBExcludedStatement data object := by
  intro _packing _piece _centres _canonical ledger clean
  have selectedNonnegative : (0 : Int) ≤ ledger.selectedEntryPayment₂ := by
    rw [Graph.TypeBRefinedSupport.DisjointLedger.selectedEntryPayment₂]
    refine Finset.sum_nonneg ?_
    intro centre _member
    exact (ledger.entry_isCandidate centre.1 centre.2).entryRefines
  exact Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative
    ledger ledger.exactAugmentedLedgerRefinement selectedNonnegative clean

/-- A Type B support with a canonical core has negative net charge, so the
bridge reduction forces the remaining core of its B2 ledger to be negative. -/
theorem typeBExclusionResidual
    (ledgers : TypeBDisjointLedgerStatement data object)
    (excluded : TypeBExcludedStatement data object) :
    TypeBExclusionResidualStatement data object := by
  intro packing piece centres canonical
  obtain ⟨ledger, exact, components, _grouped⟩ :=
    ledgers.2 packing piece centres canonical
  refine ⟨ledger, exact, components, fun clean => ?_⟩
  exact ((object.not_negativeNetCharge_iff piece.vertices data.threshold
    data.dischargeScale).mpr
      (excluded packing piece centres canonical ledger clean))
    (TypeBAssignedCentres.negative (TypeBCanonicalSupport.assigned canonical))

/-! ## The Type B residual mass -/

/-- `def:typeB-residual-mass` at one high centre: its envelope residual charge
is paid by its assigned surplus at the registered mass factor. -/
theorem centreBridgeMassBound
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    {centre : object.Vertex}
    (high : Graph.IsHighCentre object data.threshold centre) :
    CentreBridgeMassBound data object centre :=
  fun envelope =>
    Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope high massSlack

/-- The fan-certificate residual centre is charged to the bridge fan mass. -/
theorem typeBFanCertificateResidualMass
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (residual : TypeBFanCertificateResidualStatement data object) :
    TypeBFanCertificateResidualMassStatement data object := by
  obtain ⟨packing, core, centres, support, centre, member, unmarked⟩ := residual
  exact ⟨packing, core, centres, support, centre, member, unmarked,
    centreBridgeMassBound massSlack (TypeBSupport.high support centre member)⟩

/-- The overlap obstruction's centres are charged to the bridge fan mass. -/
theorem typeBOverlapObstructionMass
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (obstruction : TypeBB2ObstructionStatement data object) :
    TypeBOverlapObstructionMassStatement data object := by
  obtain ⟨packing, core, centres, support, present⟩ := obstruction
  exact ⟨packing, core, centres, support, present, fun centre member =>
    centreBridgeMassBound massSlack (TypeBSupport.high support centre member)⟩

/-- The negative post-ledger residual's centres are charged to the bridge fan
mass. -/
theorem typeBExclusionResidualMass
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale)
    (residual : TypeBExclusionResidualStatement data object) :
    TypeBExclusionResidualMassStatement data object := by
  intro packing piece centres canonical
  obtain ⟨ledger, exact, _components, negative⟩ :=
    residual packing piece centres canonical
  exact ⟨ledger, exact, negative, fun centre member =>
    centreBridgeMassBound massSlack
      (TypeBSupport.high (TypeBCanonicalSupport.support canonical) centre member)⟩

end Hypostructure.Graph.Contracts.TypeB
