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
abbrev TypeBAfterNormalFormBoundary
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
noncomputable def selectedTypeBAfterNormalFormContinuation
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
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by
      key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by
      key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      key_fresh)
    (fanSafeFresh : K .typeBFanSafe ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      key_fresh) :
    TypeBAfterNormalFormBoundary selected known := by
  let fanSafe :=
    (typeBFanSafeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match typeBFanDegreeDichotomy (data := spineData) fanSafe
      (by key_fresh)
      (by key_fresh) with
  | .left heavyHistory =>
      let compatible :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by key_fresh)
      let localHistory :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatible (by key_fresh)
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix localHistory
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by key_fresh)
      exact Sum.inl (Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting capped
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
        (globalLocalBridgeFresh := by key_fresh))
  | .right degreeFourHistory =>
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by key_fresh)
      let triangular :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by key_fresh)
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangular (by key_fresh)
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by key_fresh)
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by key_fresh)
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by key_fresh)
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix crossShouldered
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by key_fresh)
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by key_fresh)
      exact Sum.inr (Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting capped
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
        (globalLocalBridgeFresh := by key_fresh))

/-- **The common Type B continuation `[67]`--`[85]`.**

This is the literal continuation run from the absorbed-germ `[177]` entry at
node `[65]` (`Absorbed/FanCharge.lean`).  The same-token `[144a]` leaf does not
run it: the manuscript stops that endpoint at the fan entry.  It reads only the
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
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by
      key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by
      key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      key_fresh)
    (fanSafeFresh : K .typeBFanSafe ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      key_fresh) :
    TypeBContinuationBoundary selected known := by
  -- `[67]`, `lem:heavy-neighbourhood-normal-form`, is already object-wide and
  -- uses exactly the selection and tight-endpoint facts in its manifest.
  let normal :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
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
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (by key_fresh)
    (fanClosedFresh := by key_fresh)
    (compatibleClosureFresh := by key_fresh)
    (fanClosedRoutingFresh := by key_fresh)
    (compatibleRoutingFresh := by key_fresh)
    (triangularRoutingFresh := by key_fresh)
    (shoulderCompletionFresh := by key_fresh)
    (portReturnFresh := by key_fresh)
    (firstLandingFresh := by key_fresh)
    (crossShoulderFresh := by key_fresh)
    (fanSafeFresh := by key_fresh)
    (globalLocalBridgeFresh := by key_fresh)

end HypostructureErdos64EG
