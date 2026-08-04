import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

/-!
# Canonical CT6 → CT7 composition: finite trace separator

Replaces the detached `FiniteTraceSeparator` feature executor.  Core scans
aligned traces in canonical coordinate order through CT6 (OrderedExhaustion),
then compares the first unequal coordinate's exact response distinction
through CT7 (ResponseClassification).  The composition retains the complete
accumulated ledger and exposes only the exhaustive terminals: equal/neutral
trace certificate or first-separator residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteTraceSeparator

/-- Complete accumulated ledger across CT6 and CT7. -/
structure Terminal where
  traceSlot : ScheduleSlot
  responseSlot : FunctionTableSlot
  ct6 : OrderedExhaustion.Terminal traceSlot
  ct7 : ResponseClassification.Terminal responseSlot
  totalWork : Nat
  totalWork_eq : totalWork = ct6.work.bound + ct7.work.bound

def execute
    (traceSlot : ScheduleSlot)
    (responseSlot : FunctionTableSlot) : Terminal :=
  let ct6 := OrderedExhaustion.execute traceSlot
  let ct7 := ResponseClassification.execute responseSlot
  { traceSlot := traceSlot
    responseSlot := responseSlot
    ct6 := ct6
    ct7 := ct7
    totalWork := ct6.work.bound + ct7.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteTraceSeparator
