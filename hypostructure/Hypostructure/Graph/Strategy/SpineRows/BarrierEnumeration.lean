import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineWindows

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

/-! ## Node `[21]`: the finite barrier enumeration

`lem:curv-enum` is already computed by the registered certified presentation.
This row reads no predecessor fact (`Requires := []`, exactly as `lem:labels`
at node `[18]`) and publishes the safe, curvature-positive, and flat counts
and their exact logarithmic entropy ratio on the literal incoming ledger.  It
performs no second enumeration, copies no numerical answer, and constructs no
label carrier.  `lem:curv-enum` is projected directly from the registered
presentation.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def barrierEnumerationRow :
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
    `Hypostructure.Graph.Strategy.Spine.barrierEnumeration
    { Requires := []
      Produces := [K .barrierEnumeration]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _inputs =>
      .cons (key := K .barrierEnumeration)
        ⟨Contracts.Spine.barrierEnumeration data.toParameters⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
