import Hypostructure.Graph.Strategy.SurplusRun

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

inductive TypeAContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | exitOneFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known)))

inductive TypeBContinuation
    {BranchState : FiniteObject → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data}
    (selected : Input BranchState Presentation presentation data) where
  | exclusionResidual
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (residualCTypeBExclusionResidualKeys known))
  | overlapObstructionMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (residualCTypeBOverlapObstructionMassKeys known))
  | certificateResidualMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (residualCTypeBCertificateResidualMassKeys known))
  | degreeFourResidualMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (residualCDegreeFourResidualMassKeys known))
  | degreeFourExclusionResidual
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (residualCDegreeFourExclusionResidualKeys known))
  | degreeFourOverlapObstructionMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data) selected
        (residualCDegreeFourOverlapObstructionMassKeys known))
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


end Run

end Hypostructure.Graph.Strategy.Spine
