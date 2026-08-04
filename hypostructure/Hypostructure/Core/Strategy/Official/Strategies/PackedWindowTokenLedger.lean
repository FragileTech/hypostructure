import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT4 → CT14 composition: packed window token ledger

Replaces the detached `PackedWindowTokenLedger` Graph feature executor.
Core assigns each queried incidence to its canonical eligible token
through CT4 (CapacityAccounting) and retains the exact labelled
subtotals through CT14 (CapacityAccounting).  The composition retains
the complete accumulated ledger.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.PackedWindowTokenLedger

structure Terminal where
  assignmentSlot : NatTableSlot
  aggregateSlot : NatTableSlot
  ct4 : CapacityAccounting.Terminal assignmentSlot
  ct14 : CapacityAccounting.Terminal aggregateSlot
  totalWork : Nat
  totalWork_eq : totalWork = ct4.work.bound + ct14.work.bound

def execute
    (assignmentSlot : NatTableSlot)
    (aggregateSlot : NatTableSlot) : Terminal :=
  let ct4 := CapacityAccounting.execute assignmentSlot
  let ct14 := CapacityAccounting.execute aggregateSlot
  { assignmentSlot := assignmentSlot
    aggregateSlot := aggregateSlot
    ct4 := ct4
    ct14 := ct14
    totalWork := ct4.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.PackedWindowTokenLedger
