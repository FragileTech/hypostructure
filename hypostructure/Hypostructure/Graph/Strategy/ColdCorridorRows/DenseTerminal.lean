import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdMass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[162]`, `lem:dense-cold-pass`: terminality of the return corridors

The row reads G's retained corridor state, node `[27]`'s normalization and the
hot/cold split, and publishes the paper's claim that every return corridor is
terminal (`Contracts.Spine.denseColdCorridorsTerminal_of_state`).  The paper's
reason -- the pieces of `R` have bounded diameter -- does not reach corridors
of `G − X_cold` that cross hot or non-ambient-cubic cold windows: OPEN-CONSTRUCTION
[162] tex:7694 (`lean-vs-paper-discrepancies.md#open-constructions`). -/
@[reducible] noncomputable def denseColdCorridorsTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.denseColdCorridorsTerminal
    { Requires := [K .coldCorridorState, K .remainderNormalized,
        K .hotColdPartition, K .cubicBaseline]
      Produces := [K .denseColdCorridorsTerminal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .denseColdCorridorsTerminal)
        ⟨Contracts.Spine.denseColdCorridorsTerminal_of_state data.toParameters
          inputs.current.object
          (three_le_windowOrder_of_census data.toParameters
            (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.1)
          (inputs.get (K .coldCorridorState)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
