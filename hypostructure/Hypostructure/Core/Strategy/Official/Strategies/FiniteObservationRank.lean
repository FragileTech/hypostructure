import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.RankBudget
import Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion

/-!
# Canonical CT10 → CT15 → CT16 composition: finite observation rank

Replaces the detached `FiniteObservationRank` feature executor.  Core
scans complete observations/coordinates through CT10 (ClosedCodeExhaustion),
derives the minimal rank carrier through CT15 (RankBudget), and proves
whole-support realization through CT16 (ClosedCodeExhaustion).  The
composition retains the complete accumulated ledger and exposes only the
exhaustive terminals: rank drop/proper support, exact full-rank code, or
mismatch residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteObservationRank

/-- Complete accumulated ledger across CT10, CT15, and CT16. -/
structure Terminal where
  observationSlot : FunctionTableSlot
  rankSlot : NatTableSlot
  codeSlot : FunctionTableSlot
  ct10 : ClosedCodeExhaustion.Terminal observationSlot
  ct15 : RankBudget.Terminal rankSlot
  ct16 : ClosedCodeExhaustion.Terminal codeSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct10.work.bound + ct15.work.bound + ct16.work.bound

def execute
    (observationSlot : FunctionTableSlot)
    (rankSlot : NatTableSlot)
    (codeSlot : FunctionTableSlot) : Terminal :=
  let ct10 := ClosedCodeExhaustion.execute observationSlot
  let ct15 := RankBudget.execute rankSlot
  let ct16 := ClosedCodeExhaustion.execute codeSlot
  { observationSlot := observationSlot
    rankSlot := rankSlot
    codeSlot := codeSlot
    ct10 := ct10
    ct15 := ct15
    ct16 := ct16
    totalWork := ct10.work.bound + ct15.work.bound + ct16.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteObservationRank
