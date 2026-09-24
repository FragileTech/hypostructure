import HypostructureErdos64EG.Assembly.TypeB.Internal.Certificate

/-!
# Assembly: TypeB / Certificate

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Compatibility wrapper for callers entering the common Type-B certificate
walk before node `[72]`.  It runs the four registered port producers and then
hands their literal output ledger to the certificate core. -/
noncomputable def selectedTypeBCertificateBoundary
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff]) :
    Assembly.Internal.TypeBCertificateBoundary selected
      ([K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort] ++ known) := by
  let routed := Assembly.Internal.selectedTypeBPortRoutingPrefix history fanClosedFresh
    compatibleClosureFresh fanClosedRoutingFresh compatibleRoutingFresh
  exact Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting routed
    (by simp [K_eq_iff, markedFresh])
    (by simp [K_eq_iff, residualFresh])
    (by simp [K_eq_iff, certificateMassFresh])
    (by simp [K_eq_iff, cycleFresh])
    (by simp [K_eq_iff, freeFresh])
    (by simp [K_eq_iff, choiceFresh])
    (by simp [K_eq_iff, obstructionFresh])
    (by simp [K_eq_iff, hybridFresh])
    (by simp [K_eq_iff, ledgerFresh])
    (by simp [K_eq_iff, excludedFresh])
    (by simp [K_eq_iff, exclusionResidualFresh])
    (by simp [K_eq_iff, exclusionMassFresh])
    (by simp [K_eq_iff, obstructionMassFresh])
    (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])

end HypostructureErdos64EG
