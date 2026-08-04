import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization

/-!
# Canonical CT9 → CT13 → CT11 composition: finite overload geometry

Replaces the detached `FiniteOverloadGeometry` feature executor.  Core
queries classes and geometry through CT9 (CapacityAccounting), reconciles
the fallback geometry through CT13 (CapacityAccounting), and localizes the
negative support through CT11 (SupportLocalization).  The composition
retains the complete accumulated ledger and exposes only the exhaustive
terminals: bounded partition, overlap/deficit, or localized overload
support.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteOverloadGeometry

/-- Complete accumulated ledger across CT9, CT13, and CT11. -/
structure Terminal where
  classSlot : NatTableSlot
  geometrySlot : NatTableSlot
  supportSlot : RelationSlot
  ct9 : CapacityAccounting.Terminal classSlot
  ct13 : CapacityAccounting.Terminal geometrySlot
  ct11 : SupportLocalization.Terminal supportSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct9.work.bound + ct13.work.bound + ct11.work.bound

def execute
    (classSlot : NatTableSlot)
    (geometrySlot : NatTableSlot)
    (supportSlot : RelationSlot) : Terminal :=
  let ct9 := CapacityAccounting.execute classSlot
  let ct13 := CapacityAccounting.execute geometrySlot
  let ct11 := SupportLocalization.execute supportSlot
  { classSlot := classSlot
    geometrySlot := geometrySlot
    supportSlot := supportSlot
    ct9 := ct9
    ct13 := ct13
    ct11 := ct11
    totalWork := ct9.work.bound + ct13.work.bound + ct11.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteOverloadGeometry
