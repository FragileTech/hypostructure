import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion

/-!
# Canonical CT12 composition: measured finite peel

Replaces the detached `MeasuredFinitePeel` feature executor.  Core inspects
the complete predecessor-owned peel schedule through CT12 (OrderedExhaustion)
and exposes only the exhaustive trace and strict deletion/replacement witness.
`Unit` is not a sufficient semantic terminal.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.MeasuredFinitePeel

/-- CT12 terminal retained as the complete composed output. -/
structure Terminal (slot : ScheduleSlot) where
  ct12 : OrderedExhaustion.Terminal slot
  work : Strategies.StaticWork slot.rows.length

def execute (slot : ScheduleSlot) : Terminal slot :=
  { ct12 := OrderedExhaustion.execute slot
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.MeasuredFinitePeel
