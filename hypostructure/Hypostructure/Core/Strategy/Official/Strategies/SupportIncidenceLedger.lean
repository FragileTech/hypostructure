import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT11 → CT5 composition: support incidence ledger

Replaces the detached `SupportIncidenceLedger` Graph feature executor.
Core queries selected support/complement and graph darts through CT11
(SupportLocalization) and retains the exact incidence accounts through
CT5 (CapacityAccounting).  The composition retains the complete
accumulated ledger and exposes only the exhaustive terminals: admissibility
gap, local deficit, or complete incidence ledger.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.SupportIncidenceLedger

structure Terminal where
  supportSlot : RelationSlot
  incidenceSlot : NatTableSlot
  ct11 : SupportLocalization.Terminal supportSlot
  ct5 : CapacityAccounting.Terminal incidenceSlot
  totalWork : Nat
  totalWork_eq : totalWork = ct11.work.bound + ct5.work.bound

def execute
    (supportSlot : RelationSlot)
    (incidenceSlot : NatTableSlot) : Terminal :=
  let ct11 := SupportLocalization.execute supportSlot
  let ct5 := CapacityAccounting.execute incidenceSlot
  { supportSlot := supportSlot
    incidenceSlot := incidenceSlot
    ct11 := ct11
    ct5 := ct5
    totalWork := ct11.work.bound + ct5.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.SupportIncidenceLedger
