import HypostructureErdos64EG.Assembly.Surplus.Boundary
import HypostructureErdos64EG.Assembly.TypeB.Continuation

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

/-- **Node `[144a]` enters the Type B fan ledger.**  The proof of
`lem:same-token-bottleneck-routing` ends: "every surviving separated case enters
the Type B fan ledger".  On the literal strict-surplus handoff ledger, `[65]`
(`typeBFanEntry`) and `[67]` (`highCentreNormalForm`) are already present, so the
common continuation resumes at `[68]` without a duplicate key and returns one of
the four certificate outcomes.  It reads no near-cubic estimate. -/
-- EG-NODE [68] some center has \(d_G(h)>4\)?
-- EG-NODE [69] degree \(>4\) local dichotomy: fan-compatible open pair or \(k-2\) triangular ports gives fan-closed ports
-- EG-NODE [70] fan-safe graph, \(P_{13}\) certificate graph, and certificate-marked cap \(d_G(h)\le8\)
-- EG-NODE [78] degree-\(4\) branch: \(d_G(h)=4\)
-- EG-NODE [79] degree-\(4\) fan profile: center surplus \(1\), \(0\le c\le4\), \(D_B=c-\frac74\)
noncomputable def selectedSameTokenTypeBFanLedger
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
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
    TypeBCertificateOutcome selected := by
  have outcome : ∀ {later : FactKeys EGInput.{u}},
      Assembly.Internal.TypeBCertificateBoundary selected later →
        TypeBCertificateOutcome selected := by
    intro later boundary
    rcases boundary with residual | paid | exclusion | overlap
    · exact Or.inl ⟨(residual.get (K .fanCertificateResidualMass)).down,
        (residual.get (K .fanCertificateResidual)).down⟩
    · exact Or.inr (Or.inl ⟨(paid.get (K .typeBExcluded)).down,
        (paid.get (K .typeBDisjointLedger)).down,
        (paid.get (K .typeBB2Choice)).down⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨
        (exclusion.get (K .typeBExclusionResidualMass)).down,
        (exclusion.get (K .typeBExclusionResidual)).down,
        (exclusion.get (K .typeBDisjointLedger)).down⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨
        (overlap.get (K .typeBOverlapObstructionMass)).down,
        (overlap.get (K .typeBGlobalLocalBridge)).down,
        (overlap.get (K .typeBOverlapObstruction)).down⟩))
  rcases selectedTypeBAfterNormalFormContinuation history
      heavyFresh
      degreeFourFresh
      compatibilityFresh
      localFresh
      profileFresh
      triangularCoreFresh
      capFresh
      markedFresh
      residualFresh
      certificateMassFresh
      cycleFresh
      freeFresh
      choiceFresh
      obstructionFresh
      hybridFresh
      ledgerFresh
      excludedFresh
      exclusionResidualFresh
      exclusionMassFresh
      obstructionMassFresh
      (fanClosedFresh := fanClosedFresh)
      (compatibleClosureFresh := compatibleClosureFresh)
      (fanClosedRoutingFresh := fanClosedRoutingFresh)
      (compatibleRoutingFresh := compatibleRoutingFresh)
      (triangularRoutingFresh := triangularRoutingFresh)
      (shoulderCompletionFresh := shoulderCompletionFresh)
      (portReturnFresh := portReturnFresh)
      (firstLandingFresh := firstLandingFresh)
      (crossShoulderFresh := crossShoulderFresh)
      (fanSafeFresh := fanSafeFresh)
      (globalLocalBridgeFresh := globalLocalBridgeFresh) with heavy | degreeFour
  · exact outcome heavy
  · exact outcome degreeFour

end HypostructureErdos64EG
