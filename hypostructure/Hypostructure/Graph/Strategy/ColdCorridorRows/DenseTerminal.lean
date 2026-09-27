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

The row reads G's retained first-failure occurrence, (★) (`[153]`'s
distinct-states arm), `[162]`'s decided heavy-entry test, target avoidance and
uncompressibility, and proves that every retained return corridor of G is
terminal (`Contracts.Spine.denseColdCorridorsTerminal_of_distinct`).  The
paper's reason -- the pieces of `R` have bounded diameter -- is not used: it
does not reach corridors of `G − X_cold` that cross hot or non-ambient-cubic
cold windows. -/
@[reducible] noncomputable def denseColdCorridorsTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.denseColdCorridorsTerminal
    { Requires := [K .coldFirstFailureOccurrence, K .coldCutStatesDistinct,
        K .coldHeavyEntryTerminal, K .selection, K .uncompressible]
      Produces := [K .denseColdCorridorsTerminal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .denseColdCorridorsTerminal)
        ⟨Contracts.Spine.denseColdCorridorsTerminal_of_distinct data.toParameters
          inputs.current.object
          (inputs.get (K .coldFirstFailureOccurrence)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .uncompressible)).down
          (inputs.get (K .coldCutStatesDistinct)).down
          (inputs.get (K .coldHeavyEntryTerminal)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
