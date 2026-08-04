import Hypostructure.Core.Residual.Ledger

/-!
# Minimal Strategy execution boundary

The executable record is kept independent of registered strategy data so
small Strategy implementations do not acquire the entire compiler dependency
graph merely to expose their typed execution.
-/

namespace Hypostructure.Core.Strategy

universe uPrevious uTerminal uPayload

inductive CompletedTerminal where
  | completed
  deriving DecidableEq, Repr

structure CTExecution (Previous : Type uPrevious) where
  Terminal : Type uTerminal
  Output : Previous → Type uPayload
  run : (previous : Previous) → Output previous
  terminal : (previous : Previous) → Output previous → Terminal
  checks : Previous → Nat
  work : Previous → Nat

end Hypostructure.Core.Strategy
