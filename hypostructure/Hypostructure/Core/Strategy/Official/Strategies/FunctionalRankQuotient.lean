import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.RankBudget
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization

/-!
# Canonical CT15 → CT3 → CT2 composition: functional rank quotient

Replaces the detached `FunctionalRankQuotient` Graph feature executor.
Core queries graph response coordinates through CT15 (RankBudget),
compresses the quotient response through CT3 (ResponseClassification),
and derives strict decrease through CT2 (SupportLocalization).  The
composition retains the complete accumulated ledger and exposes only
the exhaustive terminals: quotient closure or full-rank graph residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FunctionalRankQuotient

structure Terminal where
  rankSlot : NatTableSlot
  quotientSlot : FunctionTableSlot
  supportSlot : RelationSlot
  ct15 : RankBudget.Terminal rankSlot
  ct3 : ResponseClassification.Terminal quotientSlot
  ct2 : SupportLocalization.Terminal supportSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct15.work.bound + ct3.work.bound + ct2.work.bound

def execute
    (rankSlot : NatTableSlot)
    (quotientSlot : FunctionTableSlot)
    (supportSlot : RelationSlot) : Terminal :=
  let ct15 := RankBudget.execute rankSlot
  let ct3 := ResponseClassification.execute quotientSlot
  let ct2 := SupportLocalization.execute supportSlot
  { rankSlot := rankSlot
    quotientSlot := quotientSlot
    supportSlot := supportSlot
    ct15 := ct15
    ct3 := ct3
    ct2 := ct2
    totalWork := ct15.work.bound + ct3.work.bound + ct2.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FunctionalRankQuotient
