import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT6 → CT5 → CT14 composition: multiplicative rate table

Replaces the detached `MultiplicativeRateTable` feature executor.  Core
scans all factor rows through CT6 (OrderedExhaustion), evaluates each
factor contribution through CT5 (CapacityAccounting), and compares the
final product-rate through CT14 (CapacityAccounting).  The composition
retains the complete accumulated ledger and exposes only the exhaustive
terminals: invalid row, certified rate bound, or capacity residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.MultiplicativeRateTable

/-- Complete accumulated ledger across CT6, CT5, and CT14. -/
structure Terminal where
  factorSlot : ScheduleSlot
  contributionSlot : NatTableSlot
  aggregateSlot : NatTableSlot
  ct6 : OrderedExhaustion.Terminal factorSlot
  ct5 : CapacityAccounting.Terminal contributionSlot
  ct14 : CapacityAccounting.Terminal aggregateSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct6.work.bound + ct5.work.bound + ct14.work.bound

def execute
    (factorSlot : ScheduleSlot)
    (contributionSlot : NatTableSlot)
    (aggregateSlot : NatTableSlot) : Terminal :=
  let ct6 := OrderedExhaustion.execute factorSlot
  let ct5 := CapacityAccounting.execute contributionSlot
  let ct14 := CapacityAccounting.execute aggregateSlot
  { factorSlot := factorSlot
    contributionSlot := contributionSlot
    aggregateSlot := aggregateSlot
    ct6 := ct6
    ct5 := ct5
    ct14 := ct14
    totalWork := ct6.work.bound + ct5.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.MultiplicativeRateTable
