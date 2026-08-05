import Hypostructure.Graph.Object

/-!
# The registered load/capacity parameters of a graph problem

A discharging argument fixes three numbers before it starts: the degree
baseline it measures against, the overload factor at which a receiver is
declared saturated, and the denominator of the per-vertex entropy threshold at
which a remainder is declared low-entropy.  None of the three is measured from
a graph — choosing them *is* part of choosing the argument — so they belong to
the problem presentation a `Core.Problem` registers, not to a strategy.

This module is only that record.  The geometry the baseline and the overload
factor are used on lives in `Hypostructure.Graph.ReceiverRouting`, which takes
both as ordinary parameters and never reads a presentation.
-/

namespace Hypostructure.Graph.ReceiverLoad

open Hypostructure

/-- The registered numeric parameters of a finite load/capacity ledger.  A
problem supplies them once, as the value it registers in
`Core.Problem.presentation`, and every use site reads them from there instead
of writing a numeral. -/
structure LoadCapacityProfile where
  /-- The degree baseline the argument measures internal degrees against. -/
  baselineDegree : Nat
  /-- The overload factor `1/α`: a receiver carrying this multiple of its own
  missing ports is saturated. -/
  loadMultiplier : Nat
  /-- Denominator of the per-vertex remainder-entropy threshold: remainders
  with per-vertex skeleton entropy below `(1/d)·log₂ n` are the low-entropy
  branch.  Clearing denominators turns that comparison into the purely
  arithmetic one a finite-state capacity step decides. -/
  remainderEntropyThresholdDenominator : Nat

end Hypostructure.Graph.ReceiverLoad
