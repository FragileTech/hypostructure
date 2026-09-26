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
    (markedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (residualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      key_fresh)
    (cycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      key_fresh)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      key_fresh)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      key_fresh)
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      key_fresh) :
    Assembly.Internal.TypeBCertificateBoundary selected
      ([K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort] ++ known) := by
  let routed := Assembly.Internal.selectedTypeBPortRoutingPrefix history fanClosedFresh
    compatibleClosureFresh fanClosedRoutingFresh compatibleRoutingFresh
  exact Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting routed
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (globalLocalBridgeFresh := by key_fresh)

end HypostructureErdos64EG
