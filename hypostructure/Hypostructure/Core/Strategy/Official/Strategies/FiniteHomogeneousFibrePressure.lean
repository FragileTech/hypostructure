import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

/-!
# Canonical CT9 → CT7 → CT13 → CT14 composition: finite homogeneous fibre
pressure

Replaces the detached `FiniteHomogeneousFibrePressure` feature executor.
Core queries labelled fibres through CT9 (CapacityAccounting), realises
the homogeneous response through CT7 (ResponseClassification), reconciles
the fallback payer through CT13 (CapacityAccounting), and compares the
pressure total through CT14 (CapacityAccounting).  The composition retains
the complete accumulated ledger and exposes only the exhaustive terminals:
distinguishing response, pressure contradiction, or bounded homogeneous
fibre.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteHomogeneousFibrePressure

/-- Complete accumulated ledger across CT9, CT7, CT13, and CT14. -/
structure Terminal where
  fibreSlot : NatTableSlot
  responseSlot : FunctionTableSlot
  payerSlot : NatTableSlot
  pressureSlot : NatTableSlot
  ct9 : CapacityAccounting.Terminal fibreSlot
  ct7 : ResponseClassification.Terminal responseSlot
  ct13 : CapacityAccounting.Terminal payerSlot
  ct14 : CapacityAccounting.Terminal pressureSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct9.work.bound + ct7.work.bound + ct13.work.bound + ct14.work.bound

def execute
    (fibreSlot : NatTableSlot)
    (responseSlot : FunctionTableSlot)
    (payerSlot : NatTableSlot)
    (pressureSlot : NatTableSlot) : Terminal :=
  let ct9 := CapacityAccounting.execute fibreSlot
  let ct7 := ResponseClassification.execute responseSlot
  let ct13 := CapacityAccounting.execute payerSlot
  let ct14 := CapacityAccounting.execute pressureSlot
  { fibreSlot := fibreSlot
    responseSlot := responseSlot
    payerSlot := payerSlot
    pressureSlot := pressureSlot
    ct9 := ct9
    ct7 := ct7
    ct13 := ct13
    ct14 := ct14
    totalWork := ct9.work.bound + ct7.work.bound + ct13.work.bound + ct14.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteHomogeneousFibrePressure
