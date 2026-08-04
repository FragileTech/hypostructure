import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT6 → CT5 → CT14 composition: finite error coefficient schedule

Replaces the detached `FiniteErrorCoefficientSchedule` feature executor.
Core scans formula rows through CT6 (OrderedExhaustion), evaluates
contributions through CT5 (CapacityAccounting), and compares the aggregate
through CT14 (CapacityAccounting).  The composition retains the complete
accumulated ledger and exposes only the exhaustive terminals: first invalid
row, aggregate bound, or capacity residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteErrorCoefficientSchedule

/-- Complete accumulated ledger across CT6, CT5, and CT14. -/
structure Terminal where
  formulaSlot : ScheduleSlot
  coefficientSlot : NatTableSlot
  aggregateSlot : NatTableSlot
  ct6 : OrderedExhaustion.Terminal formulaSlot
  ct5 : CapacityAccounting.Terminal coefficientSlot
  ct14 : CapacityAccounting.Terminal aggregateSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct6.work.bound + ct5.work.bound + ct14.work.bound

def execute
    (formulaSlot : ScheduleSlot)
    (coefficientSlot : NatTableSlot)
    (aggregateSlot : NatTableSlot) : Terminal :=
  let ct6 := OrderedExhaustion.execute formulaSlot
  let ct5 := CapacityAccounting.execute coefficientSlot
  let ct14 := CapacityAccounting.execute aggregateSlot
  { formulaSlot := formulaSlot
    coefficientSlot := coefficientSlot
    aggregateSlot := aggregateSlot
    ct6 := ct6
    ct5 := ct5
    ct14 := ct14
    totalWork := ct6.work.bound + ct5.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteErrorCoefficientSchedule
