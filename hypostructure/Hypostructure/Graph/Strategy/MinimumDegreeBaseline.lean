import Hypostructure.Core.Strategy.Data
import Hypostructure.Graph.DeletionCriticality

/-!
# Minimum-degree problem-input projection

This adapter exposes the baseline theorem already carried by Core's typed
problem input for the canonical finite-graph minimum-degree problem.  It adds
no application data and performs no strategy work: the conclusion is the
literal registered baseline proposition.
-/

namespace Hypostructure.Graph.Strategy

open Hypostructure

universe uVertex uBranch

/-- The threshold of a canonical minimum-degree graph problem, exposed as a
residual query.  The value is reconstructed from the problem constructor; an
application does not register a second numeric field or a proof callback. -/
def minimumDegreeThresholdQuery
    {k : Nat}
    {BranchState : Graph.FiniteObject.{uVertex} → Type uBranch}
    {Presentation : Type} {presentation : Presentation} :
    Core.Residual.Query
      (Core.Strategy.ProblemInput
        (Graph.problemWithPresentation
          (Graph.MinimumDegreeAtLeast k) BranchState
          Presentation presentation))
      fun _ => Nat :=
  Core.Residual.Query.ofFunction fun _ => k

/-- A Core problem input for the canonical minimum-degree graph problem
already contains the corresponding minimum-degree theorem. -/
theorem minimumDegreeAtLeast_of_problemInput
    {k : Nat}
    {BranchState : Graph.FiniteObject.{uVertex} → Type uBranch}
    {Presentation : Type} {presentation : Presentation}
    (input : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation)) :
    k ≤ input.object.minDegree :=
  input.baseline

/-- The backend-owned threshold query is bounded by the minimum degree of the
same literal problem input.  This is the query-shaped form consumed by Graph
strategies, and is merely the registered baseline theorem. -/
theorem minimumDegreeThresholdQuery_le_minDegree
    {k : Nat}
    {BranchState : Graph.FiniteObject.{uVertex} → Type uBranch}
    {Presentation : Type} {presentation : Presentation}
    (input : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation)) :
    (minimumDegreeThresholdQuery
      (k := k) (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)).read input
        ≤ input.object.minDegree :=
  minimumDegreeAtLeast_of_problemInput input

end Hypostructure.Graph.Strategy
