import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdNeutral

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[153]`, `def:cold-corridor-first-failure`: the cold return corridors

*"Order the boundary stubs of `K` lexicographically … choose inside `K` the
lexicographically first simple path joining the outside endpoint of `hᵢ` to the
outside endpoint of `hᵢ₊₁`.  Together with the two boundary stubs this path is
the cold return corridor of `ε`.  Thus each selected branch-excess half-edge has
exactly one corridor."*  The two-stub clause is `lem:bridgeless` read from the
ledger; the connection is the component's own. -/
@[reducible] noncomputable def coldReturnCorridorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldReturnCorridors
    { Requires := [K .bridgeless, K .hotColdPartition]
      Produces := [K .coldReturnCorridors]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldReturnCorridors)
        ⟨Contracts.Spine.coldReturnCorridors_of_bridgeless data.toParameters
          inputs.current.object (inputs.get (K .bridgeless)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
