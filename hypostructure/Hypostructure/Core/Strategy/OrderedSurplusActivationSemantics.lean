import Hypostructure.Core.Strategy.BaselineDemandAccountingSemantics

/-!
# Ordered surplus activation semantics

The registration contains the residual-owned CT6 audit and the residual-owned
CT5 account that follows its exact ledger extension.
-/

namespace Hypostructure.Core.Strategy.OrderedSurplusActivation

universe uResidual uIndex uData uSite uWitness uResource

structure Registration (Residual : Type uResidual) where
  Index : Residual → Type uIndex
  FailureData : (residual : Residual) → Index residual → Type uData
  order : (residual : Residual) →
    Core.Finite.Enumeration (Index residual)
  Failure : (residual : Residual) → Index residual → Prop
  failureData : (residual : Residual) → (index : Index residual) →
    Failure residual index → FailureData residual index
  failureDecidable : (residual : Residual) → (index : Index residual) →
    Decidable (Failure residual index)
  contribution : (residual : Residual) → Index residual → Nat
  accounting :
    BaselineDemandAccounting.Registration.{
      uResidual, uSite, uWitness, uResource} Residual

end Hypostructure.Core.Strategy.OrderedSurplusActivation
