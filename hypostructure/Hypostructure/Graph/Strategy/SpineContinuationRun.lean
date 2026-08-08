import Hypostructure.Graph.Strategy.SurplusRun

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

inductive BudgetContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | windowJoinPressure
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger
        (Input BranchState Presentation presentation data) selected
          (residualCWindowJoinPressureKeys known))
  | negativeSupport
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger
        (Input BranchState Presentation presentation data) selected
          (residualCNegativeSupportKeys known))

inductive TypeAContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | unsaturated
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        typeAUnsaturatedReceiverKeys)
  | peeled {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (peeledKeys known))
  | exitFour {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (exitFourKeys known))
  | exitFiveTraceLevel
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (exitFiveTraceLevelKeys known))
  | free {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (route8FreeKeys known))

inductive TypeBContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | exclusionResidual
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        typeBExclusionResidualKeys)
  | overlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        typeBOverlapObstructionMassKeys)
  | certificateResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        typeBCertificateResidualMassKeys)
  | degreeFourResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        degreeFourResidualMassKeys)
  | degreeFourExclusionResidual
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        degreeFourExclusionResidualKeys)
  | degreeFourOverlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        degreeFourOverlapObstructionMassKeys)
  | fanCertificateResidualMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (fanCertResidualMassKeys known))
  | fanExcluded {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (fanExcludedKeys (fanMarkedKeys known)))
  | fanExclusionResidual
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (fanExclusionResidualKeys (fanMarkedKeys known)))
  | fanOverlapObstructionMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (fanOverlapObstructionMassKeys (fanMarkedKeys known)))
  | exitSevenHandoff
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (exitSevenHandoffKeys known))

inductive ColdContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | windowPackage
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        surplusAboveColdKeys)
  | atOrBelowPackage
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        atOrBelowColdKeys)

inductive ChapterOneContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | budget (next : BudgetContinuation selected)
  | typeA (next : TypeAContinuation selected)
  | typeB (next : TypeBContinuation selected)
  | cold (next : ColdContinuation selected)

section Run

variable {BranchState : FiniteObject → Type v}
variable {Presentation : Type} {presentation : Presentation} {data : Data}
variable {selected : Input BranchState Presentation presentation data}

private theorem eliminateClosed
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger
      (Input BranchState Presentation presentation data) selected known)
    [FactKeys.Has
      (closed : FactKey (Input BranchState Presentation presentation data)) known] :
    False := by
  apply ExactLedger.elimClosed
    (system := factSystem BranchState Presentation presentation data) history
  rw [closureKey_eq_closed]
  infer_instance

private noncomputable def normalizeRoute8
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (result : Route8Result selected known) : ChapterOneContinuation selected :=
  match result with
  | .peeled history => .typeA (.peeled history)
  | .exitFour history => .typeA (.exitFour history)
  | .exitFiveClosed history => (eliminateClosed history).elim
  | .exitFiveTraceLevel history => .typeA (.exitFiveTraceLevel history)
  | .exitSixProper history => (eliminateClosed history).elim
  | .exitSixGlobal history => (eliminateClosed history).elim
  | .exitSevenHandoff history => .typeB (.exitSevenHandoff history)
  | .free history => .typeA (.free history)
  | .closed history => (eliminateClosed history).elim

private noncomputable def normalizeSaturatedExits
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (result : SaturatedExitResult selected known) : ChapterOneContinuation selected :=
  match result with
  | .exitOneClosed history => (eliminateClosed history).elim
  | .exitTwoClosed history => (eliminateClosed history).elim
  | .exitThreeClosed history => (eliminateClosed history).elim
  | .segment route => normalizeRoute8 route

private noncomputable def normalizeFanLedger
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (result : TypeBFanLedgerResult selected known) : ChapterOneContinuation selected :=
  match result with
  | .certificateResidualMass history => .typeB (.fanCertificateResidualMass history)
  | .directCycleClosed history => (eliminateClosed history).elim
  | .excluded history => .typeB (.fanExcluded history)
  | .exclusionResidual history => .typeB (.fanExclusionResidual history)
  | .overlapObstructionMass history => .typeB (.fanOverlapObstructionMass history)

private noncomputable def normalizeSurplus
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (result : SurplusResult selected known) : ChapterOneContinuation selected :=
  match result with
  | .sparsePairExit history => (eliminateClosed history).elim
  | .nearCubic history => (eliminateClosed history).elim
  | .windowCapsClosed history => (eliminateClosed history).elim
  | .windowBottleneck fan => normalizeFanLedger fan
  | .remainderCapsClosed history => (eliminateClosed history).elim
  | .remainderBottleneck fan => normalizeFanLedger fan
  | .primitiveCapsClosed history => (eliminateClosed history).elim
  | .primitiveBottleneck fan => normalizeFanLedger fan

set_option maxHeartbeats 4000000 in
/-- Run the Chapter 1 graph from its one opened scope.

`runCore` is invoked exactly once.  Its four continuation-bearing arms are
consumed immediately by their canonical generic runners; every already-closed
arm is eliminated from the closure evidence stored in the same ledger. -/
noncomputable def runChapterOne
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection)) :
    ChapterOneContinuation opened.selected := by
  classical
  match runCore T targetPredicate opened with
  | .surplusAbove aboveHistory =>
      match windowPackageDichotomy aboveHistory (K .windowPackageSeparated)
          (K .windowPackageCollided) (fun separated => ⟨separated⟩)
          (fun collided => ⟨collided⟩) (by simp) (by simp) with
      | .left packageHistory =>
          exact normalizeSurplus (runSurplusBranch packageHistory)
      | .right coldHistory =>
          exact .cold (.windowPackage
            (runCold coldHistory (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp)))
  | .windowPackageCollided coldHistory =>
      exact .cold (.atOrBelowPackage
        (runCold coldHistory (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp)))
  | .typeAVisibleEntry visible =>
      exact normalizeSaturatedExits
        (runSaturatedExits visible (returnFresh := by simp)
          (oneFreeFresh := by simp) (thetaFresh := by simp)
          (twoFreeFresh := by simp) (collisionFresh := by simp)
          (threeFreeFresh := by simp) (entryFresh := by simp)
          (peelFresh := by simp) (noPeelFresh := by simp)
          (peeledChargeFresh := by simp) (compressionFresh := by simp)
          (traceLevelFresh := by simp) (exitFourFresh := by simp)
          (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
          (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
          (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
          (exitSixGlobalFresh := by simp) (exitSevenHandoffFresh := by simp)
          (exitSevenFreeFresh := by simp) (residualFresh := by simp)
          (freeFresh := by simp) (burdenFresh := by simp) (coreFresh := by simp)
          (censusFresh := by simp) (descentFresh := by simp)
          (closedFresh := by simp) (closureFresh := by simp))
  | .typeAVisibleFirstExcess silent =>
      exact normalizeRoute8
        (runRouteEight silent (peelFresh := by simp) (noPeelFresh := by simp)
          (peeledChargeFresh := by simp) (compressionFresh := by simp)
          (traceLevelFresh := by simp) (exitFourFresh := by simp)
          (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
          (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
          (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
          (exitSixGlobalFresh := by simp) (exitSevenHandoffFresh := by simp)
          (exitSevenFreeFresh := by simp) (residualFresh := by simp)
          (freeFresh := by simp) (burdenFresh := by simp) (coreFresh := by simp)
          (censusFresh := by simp) (descentFresh := by simp)
          (closedFresh := by simp) (closureFresh := by simp))
  | .barrierOverflow history => exact (eliminateClosed history).elim
  | .contextDefect history => exact (eliminateClosed history).elim
  | .atomCompression history => exact (eliminateClosed history).elim
  | .properDelocalization history => exact (eliminateClosed history).elim
  | .rankDropClosed history => exact (eliminateClosed history).elim
  | .windowJoinPressure history =>
      exact .budget (.windowJoinPressure history)
  | .negativeSupport history => exact .budget (.negativeSupport history)
  | .entropyCapActive history => exact (eliminateClosed history).elim
  | .typeAUnsaturatedReceivers history => exact .typeA (.unsaturated history)
  | .typeBDirectCycleClosed history => exact (eliminateClosed history).elim
  | .typeBBranchKill history => exact (eliminateClosed history).elim
  | .typeBExclusionResidual history => exact .typeB (.exclusionResidual history)
  | .typeBOverlapObstructionMass history =>
      exact .typeB (.overlapObstructionMass history)
  | .typeBCertificateResidualMass history =>
      exact .typeB (.certificateResidualMass history)
  | .degreeFourResidualMass history => exact .typeB (.degreeFourResidualMass history)
  | .degreeFourDirectCycleClosed history => exact (eliminateClosed history).elim
  | .degreeFourBranchKill history => exact (eliminateClosed history).elim
  | .degreeFourExclusionResidual history =>
      exact .typeB (.degreeFourExclusionResidual history)
  | .degreeFourOverlapObstructionMass history =>
      exact .typeB (.degreeFourOverlapObstructionMass history)

end Run

end Hypostructure.Graph.Strategy.Spine
