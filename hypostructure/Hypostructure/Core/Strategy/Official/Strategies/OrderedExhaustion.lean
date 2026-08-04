import Hypostructure.Core.Strategy.Official.Strategies.Common

namespace Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion

/-- Exact terminal: Core inspected the complete predecessor-owned schedule,
in its declared order, without an application-authored stopping rule. -/
structure Terminal (slot : ScheduleSlot) where
  trace : List slot.carrier.Carrier
  trace_eq : trace = slot.rows
  exhaustive : ∀ x, x ∈ trace
  work : Strategies.StaticWork trace.length

def execute (slot : ScheduleSlot) : Terminal slot :=
  { trace := slot.rows
    trace_eq := rfl
    exhaustive := slot.covers
    work := Strategies.exactWork slot.rows.length }

@[simp] theorem execute_trace (slot : ScheduleSlot) :
    (execute slot).trace = slot.rows := rfl

end Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
