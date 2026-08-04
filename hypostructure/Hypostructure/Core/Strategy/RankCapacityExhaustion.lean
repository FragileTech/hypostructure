import Hypostructure.CTAdapters

/-!
# Rank-capacity exhaustion strategy

This is the reusable CT recipe behind proofs that pass from target-relative
rank through completion/incidence accounting to a capacity or deficit
alternative and a localized final frontier.  Graph and PDE applications
supply only CT specifications, capabilities, and terminal semantics.  Core
owns every execution, dependent ledger extension, accumulated check count,
and composition.
-/

namespace Hypostructure.Core.Strategy.RankCapacityExhaustion

open Hypostructure
open Hypostructure.Core.Residual

universe u

/-- A typed, predecessor-preserving rank-capacity recipe. -/
structure Recipe (Previous : Type u) where
  execution : Core.Strategy.CTExecution.{u, 0, u} Previous
  components : List Core.Documentation := []

/-- Mandatory rank-forcing entry phase, executed by CT15. -/
noncomputable def startRank {Previous : Type u}
    {spec : CT15.Spec Previous} (capability : CT15.Capability spec)
    (metadata : Core.Documentation := { name := "target-relative rank" }) :
    Recipe Previous where
  execution := CTAdapters.ct15 capability
  components := [metadata]

/-- Add CT4 compatible-completion or missing-demand accounting. -/
noncomputable def Recipe.thenCompletionAccounting
    (pipeline : Recipe Previous)
    {spec : CT4.Spec (Ledger.Extension Previous pipeline.execution.Output)}
    (capability : CT4.Capability spec)
    (metadata : Core.Documentation := { name := "completion accounting" }) :
    Recipe Previous where
  execution := pipeline.execution.compose (CTAdapters.ct4 capability)
  components := pipeline.components ++ [metadata]

/-- Add CT5 local incidence/response classification. -/
noncomputable def Recipe.thenIncidenceClassification
    (pipeline : Recipe Previous)
    {spec : CT5.Spec (Ledger.Extension Previous pipeline.execution.Output)}
    (capability : CT5.Capability spec)
    (metadata : Core.Documentation := { name := "incidence classification" }) :
    Recipe Previous where
  execution := pipeline.execution.compose (CTAdapters.ct5 capability)
  components := pipeline.components ++ [metadata]

/-- Add CT9 capacity, overload, or compatible-class accounting. -/
noncomputable def Recipe.thenCapacityAccounting
    (pipeline : Recipe Previous)
    {spec : CT9.Spec (Ledger.Extension Previous pipeline.execution.Output)}
    (capability : CT9.Capability spec)
    (metadata : Core.Documentation := { name := "capacity accounting" }) :
    Recipe Previous where
  execution := pipeline.execution.compose (CTAdapters.ct9 capability)
  components := pipeline.components ++ [metadata]

/-- Add CT14 mass/deficit comparison. -/
noncomputable def Recipe.thenDeficitComparison
    (pipeline : Recipe Previous)
    {spec : CT14.Spec (Ledger.Extension Previous pipeline.execution.Output)}
    (capability : CT14.Capability spec)
    (metadata : Core.Documentation := { name := "deficit comparison" }) :
    Recipe Previous where
  execution := pipeline.execution.compose (CTAdapters.ct14 capability)
  components := pipeline.components ++ [metadata]

/-- Add CT11 negative-support localization. -/
noncomputable def Recipe.thenSupportLocalization
    (pipeline : Recipe Previous)
    {spec : CT11.Spec (Ledger.Extension Previous pipeline.execution.Output)}
    (capability : CT11.Capability spec)
    (metadata : Core.Documentation := { name := "support localization" }) :
    Recipe Previous where
  execution := pipeline.execution.compose (CTAdapters.ct11 capability)
  components := pipeline.components ++ [metadata]

/-- Expose the completed CT recipe as the public two-regime exhaustion
strategy.  The interpreter consumes the literal final CT output; it cannot
manufacture or replace the execution ledger. -/
noncomputable def Recipe.toStrategy
    {P : Core.Problem} {T : Core.Target P}
    (pipeline : Recipe (Core.Strategy.ProblemInput P))
    (Left Right : Core.Strategy.ProblemInput P -> Type u)
    (interpret : (input : Core.Strategy.ProblemInput P) ->
      pipeline.execution.Output input ->
        Sum (PLift (T.Predicate input.object))
          (Sum (Left input) (Right input)))
    (targetSide : (input : Core.Strategy.ProblemInput P) ->
      pipeline.execution.Output input -> Bool := fun _ _ => false)
    (metadata : Core.Documentation := {})
    (leftMetadata : Core.Documentation := {})
    (rightMetadata : Core.Documentation := {}) :
    Core.Strategy.RankCapacityExhaustion P T pipeline.execution where
  Left := Left
  Right := Right
  interpret := interpret
  targetSide := targetSide
  metadata := metadata
  components := pipeline.components
  leftMetadata := leftMetadata
  rightMetadata := rightMetadata

end Hypostructure.Core.Strategy.RankCapacityExhaustion
