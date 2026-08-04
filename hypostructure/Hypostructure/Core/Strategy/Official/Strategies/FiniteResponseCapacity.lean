import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT3 → CT9 → CT14 composition: finite response capacity

Replaces the detached `FiniteResponseCapacity` feature executor.  Core
classifies the exact response table through CT3 (ResponseClassification),
partitions the response fibres through CT9 (CapacityAccounting), and
compares the total capacity through CT14 (CapacityAccounting).  The
composition retains the complete accumulated ledger and exposes only the
exhaustive terminals: novel/distinguishing response, overload, or bounded
response ledger.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteResponseCapacity

/-- Complete accumulated ledger across CT3, CT9, and CT14. -/
structure Terminal where
  responseSlot : FunctionTableSlot
  capacitySlot : NatTableSlot
  aggregateSlot : NatTableSlot
  ct3 : ResponseClassification.Terminal responseSlot
  ct9 : CapacityAccounting.Terminal capacitySlot
  ct14 : CapacityAccounting.Terminal aggregateSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct3.work.bound + ct9.work.bound + ct14.work.bound

def execute
    (responseSlot : FunctionTableSlot)
    (capacitySlot : NatTableSlot)
    (aggregateSlot : NatTableSlot) : Terminal :=
  let ct3 := ResponseClassification.execute responseSlot
  let ct9 := CapacityAccounting.execute capacitySlot
  let ct14 := CapacityAccounting.execute aggregateSlot
  { responseSlot := responseSlot
    capacitySlot := capacitySlot
    aggregateSlot := aggregateSlot
    ct3 := ct3
    ct9 := ct9
    ct14 := ct14
    totalWork := ct3.work.bound + ct9.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteResponseCapacity
