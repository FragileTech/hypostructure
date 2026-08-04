import Hypostructure.Core.Strategy.ScaleThresholdDichotomySemantics
import Hypostructure.Core.Strategy.Data
import Hypostructure.Graph.Finite

/-!
# Graph scale-threshold observations

This module supplies the canonical finite-graph interpretation of Core's
scale-threshold strategy.  It derives size and degree surplus from the
literal graph residual.  Core remains the sole owner of CT14 execution,
branch classification, routing, work, and ledger extension.
-/

namespace Hypostructure.Graph.Strategy.ScaleThresholdDichotomy

open Hypostructure
open Hypostructure.Core.Strategy.Official.Features

universe uVertex uBranch

/-- Canonical scale-threshold registration for a finite graph problem.
The table and baseline degree are inert mathematical presentation data;
graph size and degree surplus are always recomputed from the current
residual. -/
noncomputable def degreeSurplusRegistration
    (Baseline : Graph.FiniteObject.{uVertex} → Prop)
    (BranchState : Graph.FiniteObject.{uVertex} → Type uBranch)
    (Presentation : Type) (presentation : Presentation)
    (baselineDegree : Nat) (table : ScaleDependentThreshold.Table) :
    Core.Strategy.ScaleThresholdDichotomy.Registration
      (Core.Strategy.ProblemInput
        (Graph.problemWithPresentation
          Baseline BranchState Presentation presentation)) where
  table := fun _ => table
  size := fun input => input.object.vertexCount
  load := fun input => input.object.degreeSurplus baselineDegree

end Hypostructure.Graph.Strategy.ScaleThresholdDichotomy
