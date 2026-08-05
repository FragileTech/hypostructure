import Mathlib.Combinatorics.SimpleGraph.Copy
import Hypostructure.Graph.Finite

/-!
# Graph obstructions

The graph layer exposes induced-copy obstructions as a parameterized semantic
target.  Applications supply only the forbidden pattern; CT1 owns the focused
branching, residual extension, trace, and work accounting.
-/

namespace Hypostructure.Graph

universe uPrevious uPattern uVertex

/-- A graph contains the induced obstruction `pattern`. -/
def HasInducedObstruction {PatternVertex : Type uPattern}
    (pattern : SimpleGraph PatternVertex)
    (object : FiniteObject.{uVertex}) : Prop :=
  SimpleGraph.IsIndContained pattern object.graph

/-- A graph is free of the induced obstruction `pattern`. -/
def InducedObstructionFree {PatternVertex : Type uPattern}
    (pattern : SimpleGraph PatternVertex)
    (object : FiniteObject.{uVertex}) : Prop :=
  Not (HasInducedObstruction pattern object)

end Hypostructure.Graph
