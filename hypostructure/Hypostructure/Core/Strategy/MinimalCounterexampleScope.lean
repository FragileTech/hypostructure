import Hypostructure.Core.Strategy.ProblemResidual

/-!
# Node `[1]`--`[4]`: opening the minimal-counterexample scope

The manuscript assumes a counterexample exists, chooses one lexicographically
minimal for a registered well-founded order, and argues about that fixed object
from then on.  This is the one step of a structural spine that *replaces* the
object under discussion, so it is the one step the canonical ledger admits only
through framework-owned first-scope initialization: it consumes a history whose
fact index is exactly empty and is therefore unusable once any fact exists.

Everything after it is a proved refinement, so no fact committed here can be
archived, rebased, or dropped.

`Core.AvoidingContext.exists_minimalCounterexample` owns the selection: its
counterexample predicate is `P.Baseline G ∧ ¬ Target G` and its minimality is
`progress.wellFounded_smaller.has_min`.  Nothing here re-proves that; this
module only opens the scope and commits the selected context as the branch's
first fact.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uAmbient uBranch uMeasure uKey uValue

variable {P : Core.Problem.{uAmbient, uBranch}}

/-- The problem input carried by a selected minimal-counterexample context. -/
def selectedInput
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    (context : Core.MinimalCounterexampleContext P Target progress) :
    Strategy.ProblemInput P where
  object := context.G
  baseline := context.baseline
  branchState := context.state

variable [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
  (Strategy.ProblemInput P)]

/-- The result of opening the scope: the selected residual together with the
canonical history whose sole fact is the selection. -/
structure OpenedScope (key : FactKey (Strategy.ProblemInput P)) where
  selected : Strategy.ProblemInput P
  history : ExactLedger (Strategy.ProblemInput P) selected [key]

/-- **Nodes `[1]`--`[4]`.**  From any input that avoids the target, select a
counterexample minimal for the registered progress order and open the branch
scope on it, committing the selected context as the first fact.

The avoiding hypothesis is the manuscript's own branch condition; the target
arm of node `[2]` is closed by the caller before this is reached, exactly as
`[3]` is drawn. -/
noncomputable def openMinimalCounterexampleScope
    (T : Core.Target P)
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P)
    (stateOf : (G : P.Ambient) → P.BranchState G)
    (key : FactKey (Strategy.ProblemInput P))
    (encode : (context :
        Core.MinimalCounterexampleContext P T.Predicate progress) →
      key.At (selectedInput context))
    (input : Strategy.ProblemInput P)
    (avoids : ¬ T.Predicate input.object) :
    OpenedScope key :=
  let initial : Core.AvoidingContext P T.Predicate :=
    Core.AvoidingContext.ofBranch
      { G := input.object
        baseline := input.baseline
        state := input.branchState } avoids
  let context :=
    Classical.choice (initial.exists_minimalCounterexample progress stateOf)
  { selected := selectedInput context
    history :=
      ExactLedger.initializeScope exactLedgerInternal%
        (ExactLedger.root exactLedgerInternal% input)
        (selectedInput context)
        (.cons (key := key) (encode context) .nil)
        (by simp) (by simp)
        { producer := `Hypostructure.Core.Strategy.minimalCounterexampleScope } }

end Hypostructure.Core.Strategy
