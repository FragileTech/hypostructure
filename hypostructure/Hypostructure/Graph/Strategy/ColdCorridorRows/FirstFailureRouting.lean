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

/-! Node `[153]`: eliminate (F1)--(F4) on the literal surviving-cold
residual and retain the manuscript's (F5) conclusion
(`Contracts.Spine.coldFailureRouting_of_failures`). -/

@[reducible] noncomputable def coldFirstFailureRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureRouting
    { Requires := [K .coldFirstFailureOccurrence, K .coldFailureCycle,
        K .coldFailureDefectRoute,
        K .coldFailureCompression, K .coldFailureHandoff,
        K .sparseSurplusSurvivor]
      Produces := [K .coldFailureRouting]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureRouting)
        ⟨Contracts.Spine.coldFailureRouting_of_failures data.toParameters
          inputs.current.object
          (inputs.get (K .coldFirstFailureOccurrence)).down
          (inputs.get (K .coldFailureCycle)).down
          (inputs.get (K .coldFailureDefectRoute)).down
          (inputs.get (K .coldFailureCompression)).down
          (inputs.get (K .coldFailureHandoff)).down
          (inputs.get (K .sparseSurplusSurvivor)).down⟩
        .nil)


end Hypostructure.Graph.Strategy.Spine
