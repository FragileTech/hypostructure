import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Local

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[67]`, `lem:heavy-neighbourhood-normal-form`, at every high centre of the
object: the selection excludes the two quadrilaterals and the tight-endpoint
law makes every neighbour cubic. -/
@[reducible] noncomputable def highCentreNormalFormRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm
    { Requires := [K .selection, K .tightEndpoint]
      Produces := [K .highCentreNormalForm]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highCentreNormalForm)
        ⟨Contracts.TypeB.highCentreNormalForm (inputs.get (K .selection)).down.1 data.quadrilateralAccepted
          (inputs.get (K .tightEndpoint)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
