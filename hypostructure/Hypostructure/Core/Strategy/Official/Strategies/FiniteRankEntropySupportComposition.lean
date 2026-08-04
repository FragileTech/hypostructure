import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.RankBudget
import Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization

/-!
# Canonical CT15 → CT17 → CT11 composition: finite rank entropy support
composition

Replaces the detached `FiniteRankEntropySupportComposition` feature
executor.  Core queries the rank table through CT15 (RankBudget), realises
state demand/survivors through CT17 (ClosedCodeExhaustion), and localizes
the support through CT11 (SupportLocalization).  The composition retains
the complete accumulated ledger and exposes only the exhaustive terminals:
rank drop, target/entropy closure, or localized survivor residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteRankEntropySupportComposition

/-- Complete accumulated ledger across CT15, CT17, and CT11. -/
structure Terminal where
  rankSlot : NatTableSlot
  stateSlot : FunctionTableSlot
  supportSlot : RelationSlot
  ct15 : RankBudget.Terminal rankSlot
  ct17 : ClosedCodeExhaustion.Terminal stateSlot
  ct11 : SupportLocalization.Terminal supportSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct15.work.bound + ct17.work.bound + ct11.work.bound

def execute
    (rankSlot : NatTableSlot)
    (stateSlot : FunctionTableSlot)
    (supportSlot : RelationSlot) : Terminal :=
  let ct15 := RankBudget.execute rankSlot
  let ct17 := ClosedCodeExhaustion.execute stateSlot
  let ct11 := SupportLocalization.execute supportSlot
  { rankSlot := rankSlot
    stateSlot := stateSlot
    supportSlot := supportSlot
    ct15 := ct15
    ct17 := ct17
    ct11 := ct11
    totalWork := ct15.work.bound + ct17.work.bound + ct11.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteRankEntropySupportComposition
