import Hypostructure.Core.Problem

/-!
# Canonical strategy problem input

The initial typed input is defined independently of the strategy-data
registry so semantic registration modules can refer to it without importing
the registry and creating an import cycle.
-/

namespace Hypostructure.Core.Strategy

/-- One ambient object together with the baseline theorem and branch state
registered by its `Core.Problem`. -/
structure ProblemInput (P : Core.Problem) where
  object : P.Ambient
  baseline : P.Baseline object
  branchState : P.BranchState object

end Hypostructure.Core.Strategy
