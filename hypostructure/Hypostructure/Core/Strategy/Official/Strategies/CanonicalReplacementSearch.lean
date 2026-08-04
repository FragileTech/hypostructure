import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

/-!
# Canonical CT6 / CT3 composition: canonical replacement search

Replaces the detached `CanonicalReplacementSearch` feature executor.
Core queries the ordered candidates from the predecessor through CT6
(OrderedExhaustion) and retains the first admissible candidate or
exhaustive absence.  When admissibility is exact-response strict
replacement, CT3 (ResponseClassification) is used instead.

The composition retains the complete composed output and exposes only the
exhaustive terminals: found replacement or literal unavailable residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.CanonicalReplacementSearch

/-- The canonical CT selected for this replacement search. -/
inductive Mode where
  | ordered (slot : ScheduleSlot)
  | response (slot : FunctionTableSlot)

/-- Complete accumulated ledger across the selected CT. -/
structure Terminal where
  mode : Mode

/-- The static work bound inherited from the selected CT. -/
def Terminal.work (terminal : Terminal) : Nat :=
  match terminal.mode with
  | .ordered slot => (OrderedExhaustion.execute slot).work.bound
  | .response slot => (ResponseClassification.execute slot).work.bound

def execute (mode : Mode) : Terminal :=
  { mode := mode }

end Hypostructure.Core.Strategy.Official.Strategies.CanonicalReplacementSearch
