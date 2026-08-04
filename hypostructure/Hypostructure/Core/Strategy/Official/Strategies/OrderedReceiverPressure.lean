import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT12 → CT13 → CT14 composition: ordered receiver pressure

Replaces the detached `OrderedReceiverPressure` feature executor.  Core
queries the receiver order and loads through CT12 (OrderedExhaustion),
reconciles the fallback payer through CT13 (CapacityAccounting), and
compares the pressure total through CT14 (CapacityAccounting).  The
composition retains the complete accumulated ledger and exposes only the
exhaustive terminals: receiver exit residual, pressure contradiction, or
bounded continuation.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.OrderedReceiverPressure

/-- Complete accumulated ledger across CT12, CT13, and CT14. -/
structure Terminal where
  receiverSlot : ScheduleSlot
  payerSlot : NatTableSlot
  pressureSlot : NatTableSlot
  ct12 : OrderedExhaustion.Terminal receiverSlot
  ct13 : CapacityAccounting.Terminal payerSlot
  ct14 : CapacityAccounting.Terminal pressureSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct12.work.bound + ct13.work.bound + ct14.work.bound

def execute
    (receiverSlot : ScheduleSlot)
    (payerSlot : NatTableSlot)
    (pressureSlot : NatTableSlot) : Terminal :=
  let ct12 := OrderedExhaustion.execute receiverSlot
  let ct13 := CapacityAccounting.execute payerSlot
  let ct14 := CapacityAccounting.execute pressureSlot
  { receiverSlot := receiverSlot
    payerSlot := payerSlot
    pressureSlot := pressureSlot
    ct12 := ct12
    ct13 := ct13
    ct14 := ct14
    totalWork := ct12.work.bound + ct13.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.OrderedReceiverPressure
