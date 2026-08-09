import Hypostructure.Core.Strategy.FactOnlyStrategy

/-!
# Sealed exhaustive branch decisions

An atomic decision reads only its declared prerequisites and proves exactly one
of two distinct semantic facts.  Core publishes the selected fact on the
literal incoming `ExactLedger`; the unselected fact is absent from that
branch's type-level index.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uResidual uSubject uKey uValue

/-- Exact input and branch-output contract for an exhaustive binary decision. -/
structure DecisionManifest
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    extends FactRequirements Residual where
  left : FactKey Residual
  right : FactKey Residual
  distinct : left ≠ right
  left_ne_closure : left ≠ system.closureKey
  right_ne_closure : right ≠ system.closureKey

/-- A sealed exhaustive decision.  Its implementation receives the same
manifest-restricted `FactInputs` view as an atomic CT. -/
structure AtomicDecision
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] where
  private mk ::
  id : Lean.Name
  manifest : DecisionManifest Residual
  private decide : (inputs : FactInputs manifest.toFactRequirements) →
    Sum (manifest.left.At inputs.current) (manifest.right.At inputs.current)

namespace AtomicDecision

/-- Framework construction boundary for exhaustive decisions. -/
abbrev create
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (_authority : FrameworkToken)
    (id : Lean.Name) (manifest : DecisionManifest Residual)
    (decide : (inputs : FactInputs manifest.toFactRequirements) →
      Sum (manifest.left.At inputs.current) (manifest.right.At inputs.current)) :
    AtomicDecision Residual :=
  .mk id manifest decide

/-- Framework execution boundary.  Both alternatives extend the same
immutable prefix, and only the selected key is published. -/
noncomputable def run
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (_authority : FrameworkToken)
    {current : Residual} {known : FactKeys Residual}
    (decision : AtomicDecision Residual)
    [FactKeys.Available decision.manifest.Requires known]
    (previous : ExactLedger Residual current known)
    (leftFresh : decision.manifest.left ∉ known := by decide)
    (rightFresh : decision.manifest.right ∉ known := by decide) :
    Decision decision.manifest.left decision.manifest.right previous :=
  let inputs := FactInputs.ofLedger exactLedgerInternal%
    decision.manifest.toFactRequirements previous
  Decision.run previous decision.manifest.left decision.manifest.right
    decision.id (decision.decide inputs) leftFresh rightFresh

end AtomicDecision

end Hypostructure.Core.Strategy
