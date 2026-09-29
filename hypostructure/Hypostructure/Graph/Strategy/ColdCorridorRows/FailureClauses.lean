import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdFirstFailure

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[153]`, (F2), `lem:cold-corridor-first-failure` (ii) read at G: the
test is decided at G -- no segment of G's retained corridor of any selected
half-edge carries (F2), because G's two readings of a prefix, glued into G's own
surroundings, are subgraphs of G and G avoids the target (`K .selection`,
`Contracts.Spine.coldFailureDefectRoutes_of_avoids`).  Lean improvement: the
(F2) arm is empty at G. -/
@[reducible] noncomputable def coldFailureDefectRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
    { Requires := [K .selection]
      Produces := [K .coldFailureDefectRoute]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureDefectRoute)
        ⟨Contracts.Spine.coldFailureDefectRoutes_of_avoids data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1⟩ .nil)

/-- Node `[153]`, (F1): the selected residual contains no target cycle. -/
@[reducible] noncomputable def coldFailureCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCycle
    { Requires := [K .selection]
      Produces := [K .coldFailureCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureCycle)
        ⟨Contracts.Spine.coldFailureCycle_of_avoids data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1⟩
        .nil)

/-- Node `[153]`, (F3), read at G: a smaller proper representative with G's
target response in `G − J` is a target-complete compression of a proper support
(target avoidance, `K .selection`), which uncompressibility excludes
(`K .uncompressible`). -/
@[reducible] noncomputable def coldFailureCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
    { Requires := [K .uncompressible, K .selection]
      Produces := [K .coldFailureCompression]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureCompression)
        ⟨Contracts.Spine.coldFailureCompression_of_uncompressible
          data.toParameters inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .uncompressible)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
