import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.WindowShadow

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The signature test of `def:typeA-window-attachment-shadow` is exactly the
failure of singleton window-label safety. -/
@[reducible] noncomputable def windowShadowSignatureRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowSignature
    { Requires := []
      Produces := [K .windowShadowSignature]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowSignature)
        ⟨Graph.Contracts.RouteEight.windowShadowSignature data.toParameters inputs.current.object
          data.lengthOK_iff_powerOfTwo⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
