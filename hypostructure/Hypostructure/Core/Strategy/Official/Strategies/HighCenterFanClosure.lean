import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting
import Hypostructure.Core.Strategy.Official.Strategies.RankBudget

/-!
# Canonical CT6 → CT5 → CT14 → CT1 composition: high center fan closure

Replaces the detached `HighCenterFanClosure` Graph feature executor.
Core queries high-centre fan arms and incidences through CT6
(OrderedExhaustion), evaluates contributions through CT5
(CapacityAccounting), compares the aggregate through CT14
(CapacityAccounting), and consumes only a genuine target realization
through CT1 (targetDecision).  The composition retains the complete
accumulated ledger and exposes only the exhaustive terminals: target,
fan defect, aggregate contradiction, or bounded fan.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.HighCenterFanClosure

structure Terminal where
  fanSlot : ScheduleSlot
  incidenceSlot : NatTableSlot
  aggregateSlot : NatTableSlot
  ct6 : OrderedExhaustion.Terminal fanSlot
  ct5 : CapacityAccounting.Terminal incidenceSlot
  ct14 : CapacityAccounting.Terminal aggregateSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct6.work.bound + ct5.work.bound + ct14.work.bound

def execute
    (fanSlot : ScheduleSlot)
    (incidenceSlot : NatTableSlot)
    (aggregateSlot : NatTableSlot) : Terminal :=
  let ct6 := OrderedExhaustion.execute fanSlot
  let ct5 := CapacityAccounting.execute incidenceSlot
  let ct14 := CapacityAccounting.execute aggregateSlot
  { fanSlot := fanSlot
    incidenceSlot := incidenceSlot
    aggregateSlot := aggregateSlot
    ct6 := ct6
    ct5 := ct5
    ct14 := ct14
    totalWork := ct6.work.bound + ct5.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.HighCenterFanClosure
