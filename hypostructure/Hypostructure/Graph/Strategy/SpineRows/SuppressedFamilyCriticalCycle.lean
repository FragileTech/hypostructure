import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.OpenPort

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- `lem:suppressed-family-critical-cycle`. -/
@[reducible] noncomputable def suppressedFamilyCriticalCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.suppressedFamilyCriticalCycle
    { Requires := [K .selection, K .openPortSuppressionSafe, K .cubicBaseline]
      Produces := [K .suppressedFamilyCriticalCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .suppressedFamilyCriticalCycle)
        ⟨Contracts.TypeB.suppressedFamilyCriticalCycle (inputs.get (K .selection)).down.1
          (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .openPortSuppressionSafe)).down
          (inputs.get (K .cubicBaseline)).down.1.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
