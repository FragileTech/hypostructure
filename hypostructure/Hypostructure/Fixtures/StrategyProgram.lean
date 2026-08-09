import Hypostructure.Core.Strategy.StrategyProgram
import Hypostructure.Fixtures.ClosingProgram

/-!
# Partial strategy frontier fixture

The fixture pins the distinction between unresolved topology and executable
closure.  In particular, closing one decision arm removes only that arm from
the frontier, and no theorem boundary exists until every arm is closed.
-/

namespace Hypostructure.Fixtures.StrategyProgram

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Fixtures.ClosingProgram

noncomputable abbrev deferredLeft :
    StrategyProgram (ProblemInput problem)
      [isTrue, prepared, selection] [[isTrue, prepared, selection]] :=
  StrategyProgram.defer

noncomputable abbrev closedRight :
    StrategyProgram (ProblemInput problem) [isFalse, prepared, selection] [] :=
  StrategyProgram.closeIncompatible selection isFalse

/-- The closed right arm contributes no entry; the open left arm remains
branch-local and exact. -/
noncomputable abbrev partialAfterPreparation :
    StrategyProgram (ProblemInput problem) [prepared, selection]
      [[isTrue, prepared, selection]] :=
  StrategyProgram.branch split deferredLeft closedRight

/-- Atomic execution preserves the unresolved frontier verbatim. -/
noncomputable abbrev partialProgram :
    StrategyProgram (ProblemInput problem) [selection]
      [[isTrue, prepared, selection]] :=
  StrategyProgram.atomic prepare partialAfterPreparation
    (fresh := by
      rw [List.singleton_disjoint]
      simp only [List.mem_singleton]
      intro same
      change FactVocabulary.WithClosure.fact (vocabulary := vocabulary) Key.prepared =
        FactVocabulary.WithClosure.fact (vocabulary := vocabulary) Key.selection at same
      injection same with key_eq
      cases key_eq)

noncomputable abbrev totalProgram :
    StrategyProgram (ProblemInput problem) [selection] [] :=
  StrategyProgram.ofClosing program

noncomputable def partialDag :
    StrategyDag target [[isTrue, prepared, selection]] :=
  StrategyDag.ofCounterexampleScope target scope partialProgram

noncomputable def totalDag : StrategyDag target [] :=
  StrategyDag.ofCounterexampleScope target scope totalProgram

noncomputable def sealedDag : ClosingDag target := totalDag.complete

theorem certified_statement : target.Statement := sealedDag.statement

/-! ## Sealing and isolation pins -/

/-- error: Unknown constant `Hypostructure.Core.Strategy.StrategyProgram.mk` -/
#guard_msgs (error) in
#check StrategyProgram.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.StrategyProgram.body` -/
#guard_msgs (error) in
#check StrategyProgram.body

/-- error: Unknown constant `Hypostructure.Core.Strategy.StrategyDag.mk` -/
#guard_msgs (error) in
#check StrategyDag.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.StrategyDag.program` -/
#guard_msgs (error) in
#check StrategyDag.program

/--
error: Application type mismatch: The argument
  partialProgram
has type
  StrategyProgram (ProblemInput problem) [selection] [[ClosingProgram.isTrue, prepared, selection]]
but is expected to have type
  StrategyProgram (ProblemInput problem) [selection] []
in the application
  partialProgram.complete
-/
#guard_msgs (error) in
noncomputable example : ClosingProgram (ProblemInput problem) [selection] :=
  StrategyProgram.complete partialProgram

/-- error: Unknown constant `Hypostructure.Core.Strategy.StrategyDag.statement` -/
#guard_msgs (error) in
#check StrategyDag.statement

#print axioms certified_statement

end Hypostructure.Fixtures.StrategyProgram
