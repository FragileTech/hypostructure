import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineMinimalClosure

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Two-terminal closure (no manuscript label; not a manuscript statement) -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def gadgetClosureRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.gadgetClosure
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .gadgetClosure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .gadgetClosure)
        ⟨Contracts.Spine.gadgetClosure_of_selection data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down (inputs.get (K .cubicBaseline)).down
          data.lengthOK_iff_powerOfTwo⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
