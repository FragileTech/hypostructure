import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.SmallCore

/-!
# Node `[116]`: exits `(4)`--`(7)` occur

On the yes arm of node `[115]`, `lem:typeA-one-terminal-collapse` publishes the
trace-basin alternative realized by the zero/one-core entry.  The terminal is
the framework's closure: every alternative is `Incompatible` with the
target-complete minimality of the true route-`8` residual.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[116]`**: the zero/one-core collapse on the yes arm of node
`[115]`. -/
@[reducible] noncomputable def route8SmallCoreExitRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8SmallCoreExit
    { Requires := [K .route8TrueResidual, K .route8SmallCoreEntry,
          K .route8CarrierCutParity]
      Produces := [K .route8SmallCoreCollapse]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8SmallCoreCollapse)
        ⟨Graph.Contracts.RouteEight.route8SmallCoreCollapse data.toParameters
          inputs.current.object (inputs.get (K .route8TrueResidual)).down
          (inputs.get (K .route8SmallCoreEntry)).down
          (inputs.get (K .route8CarrierCutParity)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[116]`**: the collapse alternatives against the true route-`8`
residual's target-complete minimality. -/
noncomputable instance instIncompatibleRoute8TrueResidualSmallCoreCollapse :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8TrueResidual) (K .route8SmallCoreCollapse) where
  contradiction := fun input trueResidual collapse =>
    Graph.Contracts.RouteEight.route8TrueResidual_smallCoreCollapse_false
      data.toParameters input.object trueResidual.down collapse.down

end Hypostructure.Graph.Strategy.Spine
