import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

/-!
# Canonical CT3 composition: strict replacement search

Replaces the detached `StrictReplacement` feature executor.  Core classifies
the exact response table through CT3 (ResponseClassification) and exposes
only the four exhaustive terminals: compression, distinction, known row, and
novel row.  No `Option`-erasing classifier or caller-selected branch exists.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.StrictReplacement

/-- CT3 terminal retained as the complete composed output. -/
structure Terminal (slot : FunctionTableSlot) where
  ct3 : ResponseClassification.Terminal slot
  work : Strategies.StaticWork slot.rows.length

def execute (slot : FunctionTableSlot) : Terminal slot :=
  { ct3 := ResponseClassification.execute slot
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.StrictReplacement
