import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion

/-!
# Canonical CT12 composition: receiver exhaustion

Replaces the detached `ReceiverExhaustion` feature executor.  Core queries
the entire finite receiver table through CT12 (OrderedExhaustion) and exposes
only the declared surviving receiver ports.  Target/internal contradiction
exits are consumed inside CT12 and never become DAG ports.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.ReceiverExhaustion

/-- CT12 terminal retained as the complete composed output. -/
structure Terminal (slot : ScheduleSlot) where
  ct12 : OrderedExhaustion.Terminal slot
  work : Strategies.StaticWork slot.rows.length

def execute (slot : ScheduleSlot) : Terminal slot :=
  { ct12 := OrderedExhaustion.execute slot
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.ReceiverExhaustion
