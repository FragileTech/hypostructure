import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT17 → CT14 composition: finite state budget

Replaces the detached `FiniteStateBudget` feature executor.  Core realises
packed state coordinates through CT17 (ClosedCodeExhaustion), then compares
the exact demand/capacity totals through CT14 (CapacityAccounting).  The
composition retains the complete accumulated ledger and exposes only the
exhaustive terminals: target hit, exhausted/entropy contradiction, or
survivor/capacity residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteStateBudget

/-- Complete accumulated ledger across CT17 and CT14. -/
structure Terminal where
  stateSlot : FunctionTableSlot
  capacitySlot : NatTableSlot
  ct17 : ClosedCodeExhaustion.Terminal stateSlot
  ct14 : CapacityAccounting.Terminal capacitySlot
  totalWork : Nat
  totalWork_eq : totalWork = ct17.work.bound + ct14.work.bound

def execute
    (stateSlot : FunctionTableSlot)
    (capacitySlot : NatTableSlot) : Terminal :=
  let ct17 := ClosedCodeExhaustion.execute stateSlot
  let ct14 := CapacityAccounting.execute capacitySlot
  { stateSlot := stateSlot
    capacitySlot := capacitySlot
    ct17 := ct17
    ct14 := ct14
    totalWork := ct17.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteStateBudget
