import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Finite.Enumeration

/-!
# Finite-schedule capacity semantics

Residual-indexed primitive data for the reusable CT6 → CT5 → CT14 Strategy.
The registration contains no query, ledger, execution result, terminal,
route, or selected outcome.
-/

namespace Hypostructure.Core.Strategy.FiniteScheduleCapacity

universe uResidual uData

/-- Inert residual presentation consumed by CT6, CT5, and CT14. -/
structure Registration (Residual : Type uResidual) where
  Index : Residual → Type uData
  FailureData : (residual : Residual) → Index residual → Type uData
  failureOrder : (residual : Residual) →
    Core.Finite.Enumeration (Index residual)
  Failure : (residual : Residual) → Index residual → Prop
  failureData : (residual : Residual) → (index : Index residual) →
    Failure residual index → FailureData residual index
  failureDecidable : (residual : Residual) → (index : Index residual) →
    Decidable (Failure residual index)
  rowContribution : (residual : Residual) → Index residual → Nat
  budget : Core.ResourceBudget.{uData}
  Site : Residual → Type uData
  Witness : (residual : Residual) → Site residual → Type uData
  family : (residual : Residual) →
    Core.Finite.DependentEnumeration (Site residual) (Witness residual)
  Active : (residual : Residual) → Site residual → Prop
  Supports : (residual : Residual) → (site : Site residual) →
    Witness residual site → Prop
  witnessContribution : (residual : Residual) → (site : Site residual) →
    Witness residual site → budget.Resource
  required : Residual → budget.Resource
  capacity : Residual → budget.Resource
  activeDecidable : (residual : Residual) → (site : Site residual) →
    Decidable (Active residual site)
  supportsDecidable : (residual : Residual) → (site : Site residual) →
    (witness : Witness residual site) →
      Decidable (Supports residual site witness)
  resourceLEDecidable : (left right : budget.Resource) →
    Decidable (left ≤ right)
  Member : Residual → Type uData
  Label : Residual → Type uData
  members : (residual : Residual) →
    Core.Finite.Enumeration (Member residual)
  memberLowerMass : (residual : Residual) → Member residual → Nat
  memberCapacity : (residual : Residual) → Member residual → Option Nat
  memberLabel : (residual : Residual) →
    Member residual → Option (Label residual)
  labelDecidableEq : (residual : Residual) → DecidableEq (Label residual)

end Hypostructure.Core.Strategy.FiniteScheduleCapacity
