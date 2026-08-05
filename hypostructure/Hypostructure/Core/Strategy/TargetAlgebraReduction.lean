import Hypostructure.CT1.Automation
import Hypostructure.Core.Residual.Query

/-!
# Target-algebra reduction

This is the domain-neutral Strategy for an inherited target-avoiding residual
whose target has a CT1 certificate presentation.  CT1 performs the target
decision and validation.  The inherited ledger query discharges the target
arm, and CT1 appends its exact avoiding successor to the literal predecessor.
-/

namespace Hypostructure.Core.Strategy.TargetAlgebraReduction

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uCode uResidual

/-- Complete framework input.  It contains target semantics and a typed read
of the already-established avoidance fact, but no executor or route. -/
structure Contract (Previous : Type uPrevious) where
  PublicTarget : Previous → Prop
  encoding :
    CT1.CertificateEncoding.{uPrevious, uCode} Previous PublicTarget
  avoids : Query Previous fun previous => Not (PublicTarget previous)

namespace Contract

/-- Exact successor after CT1 has selected its terminal and Core has
discharged the impossible target arm. -/
abbrev Stage (contract : Contract.{uPrevious, uCode} Previous) :=
  CT1.CertificateEncoding.AvoidingSuccessorStage contract.encoding

/-- Execute CT1 once and retain its exact check count and both canonical
ledger extensions. -/
noncomputable def executeCounted
    (contract : Contract.{uPrevious, uCode} Previous)
    (previous : Previous) : Core.Counted contract.Stage :=
  let result := contract.encoding.runPublicTarget previous
  { value := contract.encoding.continueAvoiding result.stage
      (contract.avoids previous)
    checks := result.checks }

/-- Uncounted projection of the exact accumulated successor. -/
noncomputable def execute
    (contract : Contract.{uPrevious, uCode} Previous)
    (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

@[simp] theorem execute_previous_previous
    (contract : Contract.{uPrevious, uCode} Previous)
    (previous : Previous) :
    (contract.execute previous).previous.previous = previous :=
  rfl

/-- The Strategy cannot replace or reconstruct the incoming residual. -/
@[simp] theorem residual_execute
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (contract : Contract.{uPrevious, uCode} Previous)
    (previous : Previous) :
    residualOf (contract.execute previous) = residualOf previous :=
  rfl

/-- Read CT1's exact avoidance evidence from the newest ledger entry. -/
def avoidanceQuery
    (contract : Contract.{uPrevious, uCode} Previous) :
    Query contract.Stage fun stage =>
      CT1.CertificateEncoding.AvoidingEvidence
        contract.encoding stage.previous :=
  Query.latest

/-- Recover target avoidance only from CT1's stored evidence. -/
def notTargetQuery
    (contract : Contract.{uPrevious, uCode} Previous) :
    Query contract.Stage fun stage =>
      Not (contract.PublicTarget stage.previous.previous) :=
  contract.avoidanceQuery.map fun _stage evidence => evidence.avoids

end Contract

end Hypostructure.Core.Strategy.TargetAlgebraReduction
