import Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.SameCenterOpenPortCompatibility
import Hypostructure.Graph.Strategy.SpineRows.TriangularCrossShoulder
import Hypostructure.Graph.Strategy.SpineRows.TriangularFanCore
import Hypostructure.Graph.Strategy.SpineRows.TriangularFirstLanding
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortReturn
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.TriangularShoulderCompletion
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeFourProfile
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanLocalDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanSafe
import HypostructureErdos64EG.Assembly.TypeB.Internal.Certificate

/-!
# Assembly: TypeB / Continuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/- The complete carrier-neutral output of nodes `[67]`--`[85]`.  The outer
sum remembers the literal degree arm of `[68]`; the inner boundary remembers
the first Type B ledger edge that still needs the enclosing branch's global
accounting.  Both indices contain every fact actually proved on that arm. -/
private abbrev TypeBContinuationBoundary
    (selected : EGInput.{u}) (known : FactKeys EGInput.{u}) :=
  Sum
    (Assembly.Internal.TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .compatiblePairTypeBRouting,
        K .fanClosedPortTypeBRouting, K .compatiblePairFanClosure,
        K .fanClosedPort, K .typeBFanLocalDichotomy,
        K .sameCenterOpenPortCompatibility, K .typeBFanHeavyCentre,
        K .typeBFanSafe, K .highCentreNormalForm] ++ known))
    (Assembly.Internal.TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .triangularPortTypeBRouting,
        K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort,
        K .triangularCrossShoulder,
        K .triangularFirstLanding,
        K .triangularPortReturn,
        K .triangularShoulderCompletion,
        K .triangularFanCore,
        K .typeBFanDegreeFourProfile, K .typeBFanDegreeFourCentres,
        K .typeBFanSafe, K .highCentreNormalForm] ++ known))

/- The same boundary when node `[67]` is already present on the incoming
ledger.  This is the literal situation at `[144]`: the bottleneck audit needs
the object-wide normal form before it constructs the same-token handoff, so
the common Type B continuation must resume at `[68]` without appending a
duplicate key. -/
private abbrev TypeBAfterNormalFormBoundary
    (selected : EGInput.{u}) (known : FactKeys EGInput.{u}) :=
  Sum
    (Assembly.Internal.TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .compatiblePairTypeBRouting,
        K .fanClosedPortTypeBRouting, K .compatiblePairFanClosure,
        K .fanClosedPort, K .typeBFanLocalDichotomy,
        K .sameCenterOpenPortCompatibility, K .typeBFanHeavyCentre,
        K .typeBFanSafe] ++ known))
    (Assembly.Internal.TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .triangularPortTypeBRouting,
        K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort,
        K .triangularCrossShoulder,
        K .triangularFirstLanding,
        K .triangularPortReturn,
        K .triangularShoulderCompletion,
        K .triangularFanCore,
        K .typeBFanDegreeFourProfile, K .typeBFanDegreeFourCentres,
        K .typeBFanSafe] ++ known))

/-- The common Type B continuation after `[67]` has already been published on
the same exact ledger.  No fact is reconstructed: `[68]` and every subsequent
owner read their inputs from `history`. -/
private noncomputable def selectedTypeBAfterNormalFormContinuation
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
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known)
    (localFresh : K .typeBFanLocalDichotomy ∉ known)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (triangularCoreFresh : K .triangularFanCore ∉ known)
    (capFresh : K .fanCertificateCap ∉ known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by
      simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by
      simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      simp [K_eq_iff])
    (fanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      simp [K_eq_iff]) :
    TypeBAfterNormalFormBoundary selected known := by
  let fanSafe :=
    (typeBFanSafeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, fanSafeFresh])
  match typeBFanDegreeDichotomy (data := spineData) fanSafe
      (by simp [K_eq_iff, heavyFresh])
      (by simp [K_eq_iff, degreeFourFresh]) with
  | .left heavyHistory =>
      let compatible :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by simp [K_eq_iff, compatibilityFresh])
      let localHistory :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatible (by simp [K_eq_iff, localFresh])
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix localHistory
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, capFresh])
      exact Sum.inl (Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting capped
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
        (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh]))
  | .right degreeFourHistory =>
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, profileFresh])
      let triangular :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, triangularCoreFresh])
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangular (by simp [K_eq_iff, shoulderCompletionFresh])
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by simp [K_eq_iff, portReturnFresh])
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by simp [K_eq_iff, firstLandingFresh])
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by simp [K_eq_iff, crossShoulderFresh])
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix crossShouldered
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, triangularRoutingFresh])
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by simp [K_eq_iff, capFresh])
      exact Sum.inr (Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting capped
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
        (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh]))

/-- **The common Type B continuation `[67]`--`[85]`.**

This is the literal continuation shared by the ordinary `[64]`, same-token
`[144]`, and absorbed-germ `[177]` entries at node `[65]`.  It reads only the
paper facts used by these nodes.  In particular it does not manufacture a
`cubicBaseline`, canonical negative support, route-8 rate, or near-cubic bridge
estimate for carriers that do not have those facts. -/
noncomputable def selectedTypeBContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [fanEntryHas : FactKeys.Has (K .typeBFanEntry) known]
    [selectionHas : FactKeys.Has (K .selection) known]
    [bridgelessHas : FactKeys.Has (K .bridgeless) known]
    [replacementHas : FactKeys.Has (K .replacementExclusion) known]
    [tightHas : FactKeys.Has (K .tightEndpoint) known]
    [uncompressibleHas : FactKeys.Has (K .uncompressible) known]
    [remainderHas : FactKeys.Has (K .remainderNormalized) known]
    [relabelingEntropyHas : FactKeys.Has (K .remainderRelabelingEntropy) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known)
    (localFresh : K .typeBFanLocalDichotomy ∉ known)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (triangularCoreFresh : K .triangularFanCore ∉ known)
    (capFresh : K .fanCertificateCap ∉ known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by
      simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by
      simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      simp [K_eq_iff])
    (fanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      simp [K_eq_iff]) :
    TypeBContinuationBoundary selected known := by
  -- `[67]`, `lem:heavy-neighbourhood-normal-form`, is already object-wide and
  -- uses exactly the selection and tight-endpoint facts in its manifest.
  let normal :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, normalFormFresh])
  letI : FactKeys.Has (K .typeBFanEntry)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail fanEntryHas.member⟩
  letI : FactKeys.Has (K .selection)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail selectionHas.member⟩
  letI : FactKeys.Has (K .bridgeless)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail bridgelessHas.member⟩
  letI : FactKeys.Has (K .replacementExclusion)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail replacementHas.member⟩
  letI : FactKeys.Has (K .tightEndpoint)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail tightHas.member⟩
  letI : FactKeys.Has (K .uncompressible)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail uncompressibleHas.member⟩
  letI : FactKeys.Has (K .remainderNormalized)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail remainderHas.member⟩
  letI : FactKeys.Has (K .remainderRelabelingEntropy)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail relabelingEntropyHas.member⟩
  exact selectedTypeBAfterNormalFormContinuation
      (known := [K .highCentreNormalForm] ++ known) normal
    (by simp [K_eq_iff, heavyFresh])
    (by simp [K_eq_iff, degreeFourFresh])
    (by simp [K_eq_iff, compatibilityFresh])
    (by simp [K_eq_iff, localFresh])
    (by simp [K_eq_iff, profileFresh])
    (by simp [K_eq_iff, triangularCoreFresh])
    (by simp [K_eq_iff, capFresh])
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
    (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
    (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
    (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
    (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
    (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
    (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
    (portReturnFresh := by simp [K_eq_iff, portReturnFresh])
    (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
    (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
    (fanSafeFresh := by simp [K_eq_iff, fanSafeFresh])
    (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])

end HypostructureErdos64EG
