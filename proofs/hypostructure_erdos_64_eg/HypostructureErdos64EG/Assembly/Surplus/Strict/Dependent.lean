import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.BlockedPairEntropy
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FibrePressure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairOverlapFirstFailure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PressureSpineSurplusEstimate
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.RoleFibrePartition
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.WindowOverloadClass
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.HomogeneousBottleneckAudit
import HypostructureErdos64EG.Assembly.Surplus.Local

/-! A strict-surplus branch, with the complete original ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

-- EG-NODE [132] blocked-pair routing: exit or canonical blocker?
-- EG-NODE [133] sparse surplus exit closes
-- EG-NODE [134] canonical blocker ledger: each blocked pair gets one \(B_\pi\) and one capacity token
-- EG-NODE [135] exact window-join load: \(e(R,W)+2e_\times(W)=15p_{13}+\sigma_W\)
-- EG-NODE [136] tokenized blocked-pair ledger: \(|\Pi_{\rm blk}|=\sum_{C,t,r}\ell(t,r)\), supplies \(15p_{13}+\sigma_W,\sigma_R,4n+2\sigma\)
-- EG-NODE [137] coupled excess \(D_{\rm all}>0\)?
-- EG-NODE [139] token in \(\mathfrak T_W\)?
-- EG-NODE [141] token in \(\mathfrak T_R\)?
-- The facts hoisted to the entry prefix and to the top of the strict arm of
-- `[19]` lengthen this ledger; `FactKeys.Available` then needs more than the
-- default instance budget.
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 1000000 in
noncomputable def Assembly.Internal.strictSurplusDependent
    {selected : EGInput.{u}}
    (dependentHistory : ExactLedger EGInput.{u} selected
      [K .dependentPairFamily, K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
        K .paperBudgetBound, K .paperBudgetCertifies, K .pairCodeConfiguration,
        K .canonicalTokenCount,
        K .canonicalBlockedFreePartition, K .canonicalLedgerDeficit,
        K .pairCountDeficit, K .canonicalCertificationCriterion,
        K .canonicalOverloadOfFits, K .canonicalFreeExcessOfCapped,
        K .canonicalCapacityExplicit, K .highDegreePositive,
        K .highDegreeSurplusCapacity, K .orderAboveScaleSquare,
        K .sixVertexExtremalEnvelope, K .highEndpointSwitch, K .highSurplusConfiguration, K .edgeSurplusIdentity,
        K .ceilSqrtAboveScale, K .baselineSpineDemand, K .sparseUpperEnvelope,
        K .surplusAbove, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
          K .admissibleQuotientsLabelInjective, K .replacementExclusion,
          K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
          K .twoHighForcedPath, K .sameHighForcedPath, K .surplusDartIdentity, K .highDegreeCountBound, K .tightEndpoint,
        K .slackIndependent, K .singleBoundaryShape, K .noProperBaseline, K .returnAvoidance,
          K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
          K .minDegreeBaseline, K .bridgeless, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
          K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    StrictSurplusBoundaryResult selected := by
  -- `[130]`, blocked arm: `lem:degree-profile-fibres` at G's pair family, then
  -- blocker clause (d) at G's canonical activation, closed against it.
  let fibresHistory :=
    (pairDegreeProfileFibresRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      dependentHistory (by key_fresh)
  match pairProfileObstructionDichotomy (data := spineData) fibresHistory
      (by key_fresh) (by key_fresh) with
  | .left profileHistory =>
      exact (closeIncompatible profileHistory (K .pairDegreeProfileFibres)
        (K .pairProfileObstruction) (by key_fresh)).elimClosed
        (by infer_instance) |>.elim
  | .right noProfileHistory =>
      -- `[130]`, blocked arm: blocker clause (e) at G's canonical activation.  A
      -- type-(e) obstruction is a named sparse exit of G, so that arm closes
      -- against node `[125]`'s survivor on the same ledger.
      match pairResponseObstructionDichotomy (data := spineData) noProfileHistory
          (by key_fresh) (by key_fresh) with
      | .left obstructionHistory =>
          exact (closeIncompatible obstructionHistory (K .sparseSurplusSurvivor)
            (K .pairResponseObstruction) (by key_fresh)).elimClosed
            (by infer_instance) |>.elim
      | .right dependentHistory =>
          match blockedPairRoutingDichotomy (data := spineData) dependentHistory
              (by key_fresh) (by key_fresh) with
          | .left exitHistory =>
              -- `[133]`: the exit contradicts the survivor fact of `[125]`.
              exact (closeIncompatible exitHistory (K .sparseSurplusSurvivor)
                (K .sparsePairExit) (by key_fresh) |>.elimClosed (by infer_instance)).elim
          | .right noExitHistory =>
              -- `[132]` blocker arm, then `[134]`--`[136]`: the canonical blocker
              -- ledger, the exact window-join load, and the capacity-token ledger.
              let blockerHistory :=
                (canonicalBlockerRouteRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  noExitHistory (by key_fresh)
              let pairs :=
                (canonicalPairLedgerRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  blockerHistory (by key_fresh)
              -- `[135]`'s exact window-join load (`K .sparseUpperEnvelope`) is on
              -- the ledger since the top of the strict arm of `[19]`.
              let tokens :=
                (capacityTokenLedgerRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  pairs (by key_fresh)
              -- `[137]`: the entropy setup at G's `𝔗_cap` and spine family, then
              -- the entropy count on the free side of the capacity charge.
              let setup :=
                (blockedPairEntropySetupRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  tokens (by key_fresh)
              match blockedPairEntropyDichotomy (data := spineData) setup
                  (by key_fresh) (by key_fresh) with
              | .right failsHistory =>
                  -- The count fails on the free side: continue at `[178]`.
                  let unrealizedHistory :=
                    (blockedPairCodeUnrealizedRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run failsHistory (by key_fresh)
                  let firstFailure :=
                    (blockedPairOverlapFirstFailureRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run unrealizedHistory (by key_fresh)
                  -- `[131]`'s dependence prefix, cubic budget, skeleton room and
                  -- `[21]`'s skeleton domination are facts of G on this side too.
                  let mixed :=
                    (mixedSparseSpineDependenceRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run firstFailure (by key_fresh)
                  let cubic :=
                    (exactCubicBaselineBudgetRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run mixed (by key_fresh)
                  let room :=
                    (incrementalSkeletonRoomRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run cubic (by key_fresh)
                  let dominated :=
                    (skeletonDominatesRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run room (by key_fresh)
                  exact selectedPairCodeChainDependent dominated
              | .left sandwichHistory =>
                  let fibres :=
                    (roleFibrePartitionRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      sandwichHistory (by key_fresh)
                  let pressure :=
                    (fibrePressureRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      fibres (by key_fresh)
                  match coupledExcessDichotomy (data := spineData) pressure
                      (by key_fresh) (by key_fresh) with
                  | .left nearCubicHistory =>
                      -- `[138]`: `σ(G) ≤ R_L(n) ≤ C_sp ⌈√n⌉` against `[19]`.
                      let closedHistory :=
                        (pressureSpineSurplusEstimateRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).runAndCloseIncompatible
                            nearCubicHistory (K .surplusAbove) (K .spineSurplusEstimate)
                            (by key_fresh) (by key_fresh)
                      exact (closedHistory.elimClosed (by infer_instance)).elim
                  | .right overloadHistory =>
                      -- `[139]`--`[144]` on the literal overload residual.  The
                      -- node-`[144]` routing reads `lem:bridgeless` (on the ledger
                      -- since the entry prefix) and the high-centre normal form,
                      -- published here, once, on this arm.
                      let normal :=
                        (highCentreNormalFormRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run overloadHistory (by key_fresh)
                      match windowOverloadClassDichotomy (data := spineData) normal
                          (by key_fresh) (by key_fresh) with
                      | .left windowHistory =>
                          -- EG-NODE [140] window-incidence geometric audit: homogeneous matching/star
                          let audited :=
                            (windowBottleneckAuditRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).run windowHistory (by key_fresh)
                          match selectedBottleneckDischarge audited with
                          | .inl entered =>
                              exact Or.inl (Or.inl (node144aWindowHandoffReturn entered))
                          | .inr unresolved =>
                              exact Or.inl (Or.inr (Or.inl (node144aWindowFailsReturn unresolved)))
                      | .right windowAbsent =>
                          match remainderOverloadClassDichotomy (data := spineData)
                              windowAbsent (by key_fresh) (by key_fresh) with
                          | .left remainderHistory =>
                              -- EG-NODE [142] remainder-surplus geometric audit: homogeneous matching/star
                              let audited :=
                                (remainderBottleneckAuditRow (BranchState := BranchState)
                                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                                  (presentation := erdosReceiverLoadProfile)
                                  (data := spineData)).run remainderHistory
                                    (by key_fresh)
                              match selectedBottleneckDischarge audited with
                              | .inl entered =>
                                  exact Or.inl (Or.inr (Or.inr (Or.inl (node144aRemainderHandoffReturn entered))))
                              | .inr unresolved =>
                                  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (node144aRemainderFailsReturn unresolved)))))
                          | .right remainderAbsent =>
                              -- EG-NODE [143] primitive blocker-support geometric audit: homogeneous matching/star
                              let primitive :=
                                (primitiveClassOverloadRow (BranchState := BranchState)
                                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                                  (presentation := erdosReceiverLoadProfile)
                                  (data := spineData)).run remainderAbsent
                                    (by key_fresh)
                              let audited :=
                                (primitiveBottleneckAuditRow (BranchState := BranchState)
                                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                                  (presentation := erdosReceiverLoadProfile)
                                  (data := spineData)).run primitive (by key_fresh)
                              match selectedBottleneckDischarge audited with
                              | .inl entered =>
                                  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node144aPrimitiveHandoffReturn entered))))))
                              | .inr unresolved =>
                                  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (node144aPrimitiveFailsReturn unresolved))))))

end HypostructureErdos64EG
