import HypostructureErdos64EG.Assembly.Surplus.Boundary

/-!
# Assembly: Surplus / TypeBContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedStrictSurplusTypeBContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by simp [K_eq_iff])
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (triangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (capFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (fanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by simp [K_eq_iff]) :
    StrictSurplusTypeBOutcome selected := by
  -- The incoming ledger carries `K .typeBFanEntry`; the outcome is read off it.
  exact (history.get (K .typeBFanEntry)).down

end HypostructureErdos64EG
