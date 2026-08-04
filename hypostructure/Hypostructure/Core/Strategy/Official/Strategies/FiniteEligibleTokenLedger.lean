import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

/-!
# Canonical CT4 → CT9 composition: finite eligible token ledger

Replaces the detached `FiniteEligibleTokenLedger` feature executor.  Core
assigns each queried demand to its canonical first-eligible token through
CT4 (CapacityAccounting), then partitions the token fibres through CT9
(CapacityAccounting).  The composition retains the complete accumulated
ledger and exposes only the exhaustive terminals: missing payer, overloaded
fibre, or bounded token ledger.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteEligibleTokenLedger

/-- Complete accumulated ledger across CT4 and CT9. -/
structure Terminal where
  demandSlot : NatTableSlot
  fibreSlot : NatTableSlot
  ct4 : CapacityAccounting.Terminal demandSlot
  ct9 : CapacityAccounting.Terminal fibreSlot
  totalWork : Nat
  totalWork_eq : totalWork = ct4.work.bound + ct9.work.bound

def execute
    (demandSlot : NatTableSlot)
    (fibreSlot : NatTableSlot) : Terminal :=
  let ct4 := CapacityAccounting.execute demandSlot
  let ct9 := CapacityAccounting.execute fibreSlot
  { demandSlot := demandSlot
    fibreSlot := fibreSlot
    ct4 := ct4
    ct9 := ct9
    totalWork := ct4.work.bound + ct9.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteEligibleTokenLedger
