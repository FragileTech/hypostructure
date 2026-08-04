import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT6 → CT5 composition: sparse surplus

Replaces the detached `SparseSurplus` Graph feature executor.  Core
queries graph vertices and degree baseline through CT6 (OrderedExhaustion)
and retains the exact surplus ledger through CT5 (CapacityAccounting).
The composition retains the complete accumulated ledger and exposes only
the exhaustive terminals: first sparse-surplus defect or complete ledger.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.SparseSurplus

structure Terminal where
  vertexSlot : ScheduleSlot
  surplusSlot : NatTableSlot
  ct6 : OrderedExhaustion.Terminal vertexSlot
  ct5 : CapacityAccounting.Terminal surplusSlot
  totalWork : Nat
  totalWork_eq : totalWork = ct6.work.bound + ct5.work.bound

def execute
    (vertexSlot : ScheduleSlot)
    (surplusSlot : NatTableSlot) : Terminal :=
  let ct6 := OrderedExhaustion.execute vertexSlot
  let ct5 := CapacityAccounting.execute surplusSlot
  { vertexSlot := vertexSlot
    surplusSlot := surplusSlot
    ct6 := ct6
    ct5 := ct5
    totalWork := ct6.work.bound + ct5.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.SparseSurplus
