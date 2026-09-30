import HypostructureErdos64EG.Assembly.NearCubic.Survivor
import HypostructureErdos64EG.Assembly.Surplus.Strict
import Hypostructure.Graph.Strategy.SpineRows.SparseExitResidual
import Hypostructure.Graph.Strategy.SpineRows.SparseExitReadings
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SurplusRows
import HypostructureErdos64EG.Assembly.Surplus.RegisteredConstants

/-!
# Assembly: Final

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

-- The port-joint entry facts lengthen this ledger; `FactKeys.Available` then
-- needs more than the default instance budget.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
/-- Establish `def:surviving-cold-branch` before entering any hot/cold or
net-charge descendant.  The exhaustive sparse-exit split belongs to the
enclosing routing; its survivor ledger enters `[21]` directly and is then
retained monotonically by every later ExactLedger. -/
noncomputable def selectedNearCubicBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
        K .admissibleQuotientsLabelInjective, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .portEndDegree, K .hubLinkStructure, K .hubClassCounts, K .slotRelation, K .closedClasses, K .hubTwoHopLinks, K .slotLinear, K .hubWindowBudget, K .windowHubBounds, K .cubicNeighbourSupply, K .hubCountBound, K .lowEdgeParity, K .bigHubBound, K .bigHubVShapes, K .highSurplusBound, K .hubLengthThreePairs, K .tightEndpoint, K .slackIndependent,
        K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .densityExcess, K .remainderSlack, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
        K .primitiveCarrierCount, K .remainderPathBounds, K .windowFreeGeometry, K .inducedPathAttachment, K .windowPositionStubs, K .windowAttachmentGap, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
        K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .threeRouteFan, K .threeRouteChain, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
        K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    SelectedNearCubicBoundary selected := by
  match sparseSurplusSurvivorDichotomy
      (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left exitHistory =>
      -- `[187]`'s near-cubic target defect (Lean improvement: exit (b) is empty
      -- at G, lem:sparse-exit-b-empty).  The exit arm routes the literal exits to clause (b), stated
      -- about G, and `K .sparseTargetDefectEmpty` (two readings of G agree in
      -- `G − Z`) closes it.  No residual is returned.
      exact (selectedSparseExitClosed exitHistory).elim
  | .right survivorHistory =>
      -- The at-or-below survivor goes to `[21]`; `[125]` is entered only
      -- from the strict arm `[20]`.
      exact selectedNearCubicSurvivorBranch survivorHistory

/-- Node `[187]` collects only the other literal selected-root outcomes, each
with every fact of its ledger at its return (`Assembly/Residuals/`): the two
pair Type B subtypes (system arm; the increment arm is empty at G), the Type B sublinear failure and the route-`8` quotient
failure `[348]` as products of their arm blocks, the eleven private-carrier
rate failure subtypes, and the local cold-terminal exclusion as its one
reachable linear-arm singleton `linearRealizedSilent` and the two subtypes
reached through `[153]`'s repeat on the dense arms (its absorbed-germ product
is not entered: `[173]`'s no-arm is closed against `K .route8Rate`).
The pair-system entry retains its own source key and is not `[144a]`.  (G-only
restatement: the near-cubic target defect of `[187]` is closed at G -- exit
(b), stated about G, is empty; lem:sparse-exit-b-empty.)  g-pieces-constructed: `[154]`'s G2 yes-arm is
live again (the second representative `E` is a piece constructed from G, not a
reading carrying G's response), so the cold-terminal subtypes
`linearDenseAtOrAbove`, `linearDenseRateFailed` and
`linearRealizedDistinguished` are restored, with the two repeat-arm subtypes
`linearDenseAtOrAbove_repeatedDistinguished` and
`linearDenseRateFailed_repeatedDistinguished`. -/
abbrev OtherReturnedOutcome (selected : EGInput.{u}) :=
  (PairTypeBOutcome_independentSystem selected ∨
    PairTypeBOutcome_dependentSystem selected) ∨
  TypeBSublinearOutcome_product selected ∨
  Route8QuotientOutcome_product selected ∨
  (Route8RateFailsOutcome_realized_highEntropy selected ∨
    Route8RateFailsOutcome_realized_lowNonrepetitive selected ∨
    Route8RateFailsOutcome_realized_lowWedgeFree selected ∨
    Route8RateFailsOutcome_realized_lowWedge selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_highEntropy selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_lowWedge selected ∨
    Route8RateFailsOutcome_denseBelow_lowNonrepetitive selected ∨
    Route8RateFailsOutcome_denseBelow_lowWedgeFree selected ∨
    Route8RateFailsOutcome_denseBelow_lowWedge selected) ∨
  (ColdBranchClosedOutcome_linearRealizedSilent selected ∨
    (ColdBranchClosedOutcome_linearDenseAtOrAbove_repeated selected ∨
      ColdBranchClosedOutcome_linearDenseRateFailed_repeated selected) ∨
    (ColdBranchClosedOutcome_linearDenseAtOrAbove selected ∨
      ColdBranchClosedOutcome_linearDenseRateFailed selected) ∨
    ColdBranchClosedOutcome_linearRealizedDistinguished selected ∨
    (ColdBranchClosedOutcome_linearDenseAtOrAbove_repeatedDistinguished selected ∨
      ColdBranchClosedOutcome_linearDenseRateFailed_repeatedDistinguished selected))

/-- Exact selected-root reduction.  Every returned residual carries every fact
of the single ledger at its return, one `get` per fact; paths with different
fact sets are different residuals, stated as subtypes of the generic residual
or, where the paths form a full product, as the product of their arm blocks:
the six `[144a]` subtypes; the two `[172a]` subtypes; the six `[182]`
subtypes; the `[186]` joint balance product; the remaining `[187]` outcomes;
and the structural exhaustion residual `[54]` (5 subtypes).  `[153]`'s equal-state pair is no longer a
residual: it is the repeat subcase of (F5) and continues into the germ routing
(`[187]`).  (`[162]` is no longer returned: the dense pass needs no terminality
of a heavy-entry corridor.)
(G-only restatement: `[20a]` and the near-cubic target defect of `[187]` are
closed at G -- exit (b) of `[125]`, stated about G, is empty
(lem:sparse-exit-b-empty) -- and return no residual.  The cold-terminal subtypes on `[154]`'s G2 yes-arm are restored:
with the second representative `E` a piece constructed from G, G2 is a live
test (five subtypes, one per root path).  The
`[186]` joint balance product is restored: with the realizations of a trace
basin read on the pieces constructed from G, the essential carrier cores are no
longer empty, node `[123]`'s failed-rate arm is reached, and `[181]`,
`[183]`--`[186]` run as in the manuscript.)

Bounded-size residuals: on `[146]` no, the density order (`[158]`'s realized
package, or `[24]` on the bounded arm of `[153]`, against `θ ≥ 1/78`) is
decided exactly on G's order (`realizedOrderDichotomy`,
`boundedOrderDichotomy`); the arm `N₀ ≤ n` is closed and every residual below
the other arm carries the combined bound and `n < N₀` (`K .realizedOrderSmall`
or `K .boundedOrderSmall`): all eleven private-carrier rate failure subtypes,
the three bounded `[54]` subtypes, the two realized cold-terminal subtypes
`linearRealizedSilent` and `linearRealizedDistinguished`, and the product
paths through the prefix blocks `Route8LanePrefixBlock_realizedColdAtOrAbove` /
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`. -/
abbrev SelectedLedgerBoundaryResult (selected : EGInput.{u}) :=
  (Node144aOutcome_windowHandoff selected ∨ Node144aOutcome_windowFails selected ∨
    Node144aOutcome_remainderHandoff selected ∨
    Node144aOutcome_remainderFails selected ∨
    Node144aOutcome_primitiveHandoff selected ∨
    Node144aOutcome_primitiveFails selected) ∨
  (BlockedBarrierOverlapOutcome_DeficiencyAtOrAbove selected ∨
    BlockedBarrierOverlapOutcome_DeficiencyBelowRateFails selected) ∨
  (PairConditionalFactorizationOutcome_freeFactorizationFails selected ∨
    PairConditionalFactorizationOutcome_freeRealizabilityFails selected ∨
    PairConditionalFactorizationOutcome_freeIncrementFails selected ∨
    PairConditionalFactorizationOutcome_blockedFactorizationFails selected ∨
    PairConditionalFactorizationOutcome_blockedRealizabilityFails selected ∨
    PairConditionalFactorizationOutcome_blockedIncrementFails selected) ∨
  Route8JointBalanceOutcome_product selected ∨
  OtherReturnedOutcome selected ∨
  (Node54ResidualOutcome_realizedColdBelow selected ∨
    Node54ResidualOutcome_realizedBounded selected ∨
    Node54ResidualOutcome_unrealizedTauHighBounded selected ∨
    Node54ResidualOutcome_unrealizedRateFailsBounded selected ∨
    Node54ResidualOutcome_unrealizedBothRates selected)

-- The facts hoisted to the entry prefix and to the top of the strict arm of
-- `[19]` lengthen every ledger here, so `FactKeys.Available` and the returns
-- need more than the default budgets.
set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
noncomputable def selectedLedgerBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected := by
  have other : OtherReturnedOutcome selected → SelectedLedgerBoundaryResult selected :=
    fun outcome => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl outcome))))
  match selectedSurplusDichotomy history with
  | .left strictHistory =>
      -- Top of the strict arm of `[19]`: every fact that reads only entry facts
      -- and `K .surplusAbove` is published here, once, so both `[20]` arms
      -- (`[20a]` and `[125]`) carry it.  No decision.
      -- `[135]`'s exact window-join load, hoisted to the top of the strict arm; no decision.
      let windowJoinHistory :=
        (exactWindowJoinPressureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run strictHistory (by key_fresh)
      -- `[129]`'s baseline spine demand, hoisted to the top of the strict arm; no decision.
      let baselineDemandHistory :=
        (sparseExitBaselineSpineDemandRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run windowJoinHistory (by key_fresh)
      -- hoisted from `[20a]`: the budget identities; no decision.
      let budgetHistory :=
        (sparseExitBudgetRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run baselineDemandHistory (by key_fresh)
      -- where the surplus of G sits, once `C + 1 ≤ ⌈√n⌉` is on the ledger; no decision.
      -- Joint hubs (Lean improvement): the orders the high-surplus closure
      -- `8n ≤ 32s + 125s²` excludes against `σ > C_sp⌈√n⌉`; no decision.
      let highSurplusOrderHistory :=
        (highSurplusOrderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run budgetHistory (by key_fresh)
      -- Hub links (Lean improvement): the scale pressure; no decision.
      let scalePressureHistory :=
        (scalePressureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run highSurplusOrderHistory (by key_fresh)
      let highConfigHistory :=
        (highSurplusConfigurationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run scalePressureHistory (by key_fresh)
      -- the switch at every high/baseline edge of G; no decision.
      let highSwitchHistory :=
        (highEndpointSwitchRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run highConfigHistory (by key_fresh)
      -- Pair arms (Lean improvement): arm B of the pair code as implications; no decision.
      let pairArmBHistory :=
        (pairArmBRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run highSwitchHistory (by key_fresh)
      -- hoisted from `[20a]`: the sharpened envelope; no decision.
      let envelopeHistory :=
        (sparseExitEnvelopeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run pairArmBHistory (by key_fresh)
      -- hoisted from `[20a]`: the high-degree range; no decision.
      let highDegreeHistory :=
        (highDegreeSurplusRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run envelopeHistory (by key_fresh)
      -- hoisted from `[20a]`: G's canonical capacity presentation; no decision.
      let canonicalCapacityHistory :=
        (sparseExitCanonicalCapacityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run highDegreeHistory (by key_fresh)
      -- hoisted from `[20a]`: the canonical capacity counts; no decision.
      -- Joint hubs (Lean improvement): the window structure of G's canonical charge and the
      -- target-response obstructions at its canonical active family; no decision.
      let windowChargeHistory :=
        (windowChargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run canonicalCapacityHistory (by key_fresh)
      -- Free side (Lean improvement): the structure of the free side of G's canonical charge;
      -- no decision.
      let freeSideStructureHistory :=
        (freeSideStructureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run windowChargeHistory (by key_fresh)
      -- Pair arms (Lean improvement): arm A of the pair code as implications; no decision.
      let pairArmAHistory :=
        (pairArmARow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run freeSideStructureHistory (by key_fresh)
      let canonicalCountsHistory :=
        (sparseExitCanonicalCapacityCountsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run pairArmAHistory (by key_fresh)
      -- Free side (Lean improvement): the free-side count, G2 with it, and the capped arm;
      -- no decision.
      let freeSideCountHistory :=
        (freeSideCountRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run canonicalCountsHistory (by key_fresh)
      -- Free side (Lean improvement): the free side against the hubs; no decision.
      let freeSideHubsHistory :=
        (freeSideHubsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run freeSideCountHistory (by key_fresh)
      -- Free side (Lean improvement): the extended charge `Θ_ext`; no decision.
      let extendedChargeHistory :=
        (extendedChargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run freeSideHubsHistory (by key_fresh)
      -- hoisted from `[20a]`: the paper budget and the pair-code chain; no decision.
      let pairChainHistory :=
        (sparseExitPairChainRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run extendedChargeHistory (by key_fresh)
      -- EG-NODE [20] surplus-pair accounting branch
      -- The enclosing `[20]` routing tests `def:named-surplus-exits` before
      -- node `[125]`: the exit arm is closed at G (exit (b), stated about G, is
      -- empty); the survivor arm is `[125]`.
      match sparseSurplusSurvivorDichotomy
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData) pairChainHistory
          (by key_fresh) (by key_fresh) with
      | .left exitHistory =>
          -- `[20a]` (Lean improvement: exit (b) is empty at G,
          -- lem:sparse-exit-b-empty).  The exit arm
          -- routes the literal exits (a), (c), (d), (e) as terminals and clause
          -- (b), stated about G, to its payload; `K .sparseTargetDefectEmpty`
          -- (two readings of G agree in `G − Z`) closes the arm.  G is routed
          -- onto the survivor arm `[125]`; no `[20a]` residual is returned.
          exact (selectedSparseExitClosed exitHistory).elim
      | .right survivorHistory =>
          match selectedStrictSurplusBranch survivorHistory with
          | .inl handoff => exact Or.inl handoff
          | .inr (.inl pairEntry) =>
              exact other (Or.inl pairEntry)
          | .inr (.inr pair) =>
              exact Or.inr (Or.inr (Or.inl pair))
  | .right nearCubicHistory =>
      have survivor := selectedNearCubicBranch nearCubicHistory
      have liftRoute : SelectedRouteEightBoundary selected →
          SelectedLedgerBoundaryResult selected := by
        intro route
        match route with
        | .inl sublinear =>
            exact other (Or.inr (Or.inl sublinear))
        | .inr (.inl quotient) =>
            exact other (Or.inr (Or.inr (Or.inl quotient)))
        | .inr (.inr joint) =>
            exact Or.inr (Or.inr (Or.inr (Or.inl joint)))
      match survivor with
      | .inl route => exact liftRoute route
      | .inr (.inl rate) =>
          exact other (Or.inr (Or.inr (Or.inr (Or.inl rate))))
      | .inr (.inr (.inl blocked)) =>
          exact Or.inr (Or.inl blocked)
      | .inr (.inr (.inr (.inl cold))) =>
          exact other (Or.inr (Or.inr (Or.inr (Or.inr cold))))
      | .inr (.inr (.inr (.inr entropy))) =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr entropy))))

/-- The selected minimal counterexample has one of the exact boundary
outcomes, each with every fact of the single ledger at its return. -/
theorem selectedCounterexample_reaches_exactBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected :=
  selectedLedgerBoundary history

/-- Every counterexample to the public finite-graph statement reaches one of
the displayed boundary alternatives through the selected ledger. -/
theorem officialCounterexample_reaches_selectedLedgerBoundary
    (counterexample : ¬ OfficialStatement.{u}) :
    ∃ selected : EGInput.{u}, SelectedLedgerBoundaryResult selected := by
  classical
  have existsBad : ∃ object : Graph.FiniteObject.{u},
      Baseline object ∧ ¬ Target object := by
    by_contra noBad
    have closure : ∀ object : Graph.FiniteObject.{u},
        Baseline object → Target object := by
      intro object baseline
      by_contra avoids
      exact noBad ⟨object, baseline, avoids⟩
    apply counterexample
    exact target.target_to_statement closure
  obtain ⟨object, baseline, avoids⟩ := existsBad
  let input : EGInput.{u} := ⟨object, baseline, ()⟩
  let opened := openSelectedCounterexample input avoids
  exact ⟨opened.selected, selectedCounterexample_reaches_exactBoundary opened.history⟩

end HypostructureErdos64EG
