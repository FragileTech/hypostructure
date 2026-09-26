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

/-! ## Node `[162]`, `lem:dense-cold-pass`: terminality in the remainder

The corridor producer records that its component and selected path lie in the
normalized remainder of the fixed maximal packing.  This row consumes that
literal state together with node `[27]`'s normalization fact.  The canonical
path is shortest by `FinitePathSelection.selectOfReachable_length_le`; an
induced-`P_windowOrder`-free remainder therefore bounds its length by
`windowOrder - 2`, which is below the registered cold-state bound
(`Contracts.Spine.denseColdCorridorsTerminal_of_state`). -/
@[reducible] noncomputable def denseColdCorridorsTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.denseColdCorridorsTerminal
    { Requires := [K .coldCorridorState, K .remainderNormalized,
        K .hotColdPartition]
      Produces := [K .denseColdCorridorsTerminal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .denseColdCorridorsTerminal)
        ⟨Contracts.Spine.denseColdCorridorsTerminal_of_state data.toParameters
          inputs.current.object data.three_le_windowOrder
          (inputs.get (K .coldCorridorState)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
