import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT6 → CT13 → CT14 composition: finite obstruction accounting

Replaces the detached `FiniteObstructionAccounting` feature executor.  Core
queries obstruction and payer schedules through CT6 (OrderedExhaustion),
reconciles primary/fallback payers through CT13 (CapacityAccounting), and
compares the total account through CT14 (CapacityAccounting).  The
composition retains the complete accumulated ledger and exposes only the
exhaustive terminals: tier-one/overlap/deficit residual or reconciled
ledger.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteObstructionAccounting

/-- Complete accumulated ledger across CT6, CT13, and CT14. -/
structure Terminal where
  obstructionSlot : ScheduleSlot
  payerSlot : NatTableSlot
  aggregateSlot : NatTableSlot
  ct6 : OrderedExhaustion.Terminal obstructionSlot
  ct13 : CapacityAccounting.Terminal payerSlot
  ct14 : CapacityAccounting.Terminal aggregateSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct6.work.bound + ct13.work.bound + ct14.work.bound

def execute
    (obstructionSlot : ScheduleSlot)
    (payerSlot : NatTableSlot)
    (aggregateSlot : NatTableSlot) : Terminal :=
  let ct6 := OrderedExhaustion.execute obstructionSlot
  let ct13 := CapacityAccounting.execute payerSlot
  let ct14 := CapacityAccounting.execute aggregateSlot
  { obstructionSlot := obstructionSlot
    payerSlot := payerSlot
    aggregateSlot := aggregateSlot
    ct6 := ct6
    ct13 := ct13
    ct14 := ct14
    totalWork := ct6.work.bound + ct13.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteObstructionAccounting
