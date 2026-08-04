import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization

/-!
# Canonical CT7 → CT3 → CT2 composition: finite context quotient

Replaces the detached `FiniteContextQuotient` feature executor.  Core
realises context equivalence through CT7 (ResponseClassification),
compresses the quotient response through CT3 (ResponseClassification),
and derives strict replacement criticality through CT2
(SupportLocalization).  The composition retains the complete accumulated
ledger and exposes only the exhaustive terminals: compression closure or
exact quotient residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteContextQuotient

/-- Complete accumulated ledger across CT7, CT3, and CT2. -/
structure Terminal where
  contextSlot : FunctionTableSlot
  quotientSlot : FunctionTableSlot
  supportSlot : RelationSlot
  ct7 : ResponseClassification.Terminal contextSlot
  ct3 : ResponseClassification.Terminal quotientSlot
  ct2 : SupportLocalization.Terminal supportSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct7.work.bound + ct3.work.bound + ct2.work.bound

def execute
    (contextSlot : FunctionTableSlot)
    (quotientSlot : FunctionTableSlot)
    (supportSlot : RelationSlot) : Terminal :=
  let ct7 := ResponseClassification.execute contextSlot
  let ct3 := ResponseClassification.execute quotientSlot
  let ct2 := SupportLocalization.execute supportSlot
  { contextSlot := contextSlot
    quotientSlot := quotientSlot
    supportSlot := supportSlot
    ct7 := ct7
    ct3 := ct3
    ct2 := ct2
    totalWork := ct7.work.bound + ct3.work.bound + ct2.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteContextQuotient
