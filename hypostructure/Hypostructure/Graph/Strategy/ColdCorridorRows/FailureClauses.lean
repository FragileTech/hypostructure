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

set_option maxHeartbeats 1600000 in
/-- Node `[153]`, (F2): register the concrete sparse-exit route and the
F2-free context equivalence on the current object
(`Contracts.Spine.coldFailureDefectFact`). -/
@[reducible] noncomputable def coldFailureDefectRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
    { Requires := []
      Produces := [K .coldFailureDefect, K .coldFailureDefectRoute]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureDefect)
        ⟨Contracts.Spine.coldFailureDefectFact data.toParameters
          inputs.current.object⟩
        (.cons (key := K .coldFailureDefectRoute)
          ⟨Contracts.Spine.coldFailureDefectRoutes data.toParameters
            inputs.current.object⟩ .nil))

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

/-- Node `[153]`, (F3): uncompressibility excludes a smaller proper
representative on the current residual. -/
@[reducible] noncomputable def coldFailureCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
    { Requires := [K .uncompressible]
      Produces := [K .coldFailureCompression]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureCompression)
        ⟨Contracts.Spine.coldFailureCompression_of_uncompressible
          data.toParameters inputs.current.object
          (inputs.get (K .uncompressible)).down⟩
        .nil)

/-- Node `[153]`, (F4): a declared Type-B/route-8 support is returned to
the already-declared handoff ledger. -/
@[reducible] noncomputable def coldFailureHandoffRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureHandoff
    { Requires := []
      Produces := [K .coldFailureHandoff]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureHandoff)
        ⟨Contracts.Spine.coldFailureHandoff_holds inputs.current.object⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
