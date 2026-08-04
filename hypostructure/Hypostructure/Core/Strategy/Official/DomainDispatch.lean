/-!
# Typed output of framework-owned domain dispatch

This file is the dependency-inversion seam between the closed Core syntax and
domain-owned interpreters.  It contains no resolver, callback, registration
hook, or fallback operation.  A domain interpreter may only return either a
proof of the declared target or its own exact typed residual and ledger.
-/

namespace Hypostructure.Core.Strategy.Official

universe uTarget uResidual uLedger

/-- Lossless result of one closed domain compiler.  The target constructor is
proof-carrying; the residual constructor preserves the domain's exact residual
and accumulated ledger without coercing either to an untyped Core payload. -/
inductive DomainReduction
    (Target : Prop) (Residual : Type uResidual) (Ledger : Type uLedger) where
  | target (proof : Target)
  | residual (residual : Residual) (ledger : Ledger)

namespace DomainReduction

variable {Target : Prop} {Residual : Type uResidual} {Ledger : Type uLedger}

theorem target_or_typed_residual
    (result : DomainReduction Target Residual Ledger) :
    Target ∨ Nonempty (Residual × Ledger) := by
  cases result with
  | target proof => exact Or.inl proof
  | residual residual ledger => exact Or.inr ⟨(residual, ledger)⟩

end DomainReduction

end Hypostructure.Core.Strategy.Official
