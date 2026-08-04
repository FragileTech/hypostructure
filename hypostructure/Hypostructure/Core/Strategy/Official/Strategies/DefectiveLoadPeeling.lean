import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion

/-!
# Canonical CT12 composition: defective load peeling

Replaces the detached `DefectiveLoadPeeling` feature executor.  Core queries
pending loads and restoration/peel rows through CT12 (OrderedExhaustion) and
retains every strict feedback step.  The external result is CT12's
exhausted/demand/tier terminals; `Unit` is not a sufficient semantic terminal.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.DefectiveLoadPeeling

/-- CT12 terminal retained as the complete composed output. -/
structure Terminal (slot : ScheduleSlot) where
  ct12 : OrderedExhaustion.Terminal slot
  work : Strategies.StaticWork slot.rows.length

def execute (slot : ScheduleSlot) : Terminal slot :=
  { ct12 := OrderedExhaustion.execute slot
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.DefectiveLoadPeeling
