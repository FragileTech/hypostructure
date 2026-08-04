import Hypostructure.Core.Strategy.Data

/-!
# Thin Graph continuation of Core minimal-counterexample selection

For Graph, the exact selected minimal context is already a valid local graph
residual: it contains the selected graph, its baseline proof, target
avoidance, and minimality.  This adapter merely registers that interpretation.
Selection and ledger handling remain in Core.
-/

namespace Hypostructure.Graph.Strategy.CounterexampleLocalization

open Hypostructure

universe uAmbient uBranch uMeasure

/-- Register an existing graph progress presentation.  Core derives and
retains the exact selected context; Graph supplies no output hook. -/
def registration
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (selection :
      Core.MinimalCounterexampleSelectionData.{
        uAmbient, uBranch, uMeasure} P) :
    Core.CounterexampleLocalizationData.{
      uAmbient, uBranch, uMeasure} P T where
  selection := selection

end Hypostructure.Graph.Strategy.CounterexampleLocalization
