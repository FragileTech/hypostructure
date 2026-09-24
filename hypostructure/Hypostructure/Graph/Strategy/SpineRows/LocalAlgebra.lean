import Hypostructure.Graph.Strategy.SpineVocabulary

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

/-! ## Node `[18]`: the exact finite local algebra

For every induced window of the literal active object, the row publishes
exactly the two assertions of `lem:labels`: the cardinality of the legal-label
set and its displayed size distribution.  The manuscript's `C_s` and `Ω₂` are
already the definitions `WindowCurvature.Safe` and
`WindowCurvature.curvatureTwo`; they are deliberately not republished as
reflection theorems outside the registered legal-label schedule.

No predecessor fact is needed: the direct enumeration depends only on the
registered window order, while the produced proposition is indexed by the
active object's actual induced-window supports.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def localAlgebraRow :
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
    `Hypostructure.Graph.Strategy.Spine.localAlgebra
    { Requires := []
      Produces := [K .localAlgebra]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      .cons (key := K .localAlgebra)
        (show Value BranchState Presentation presentation data
            .localAlgebra inputs.current from
          ⟨fun (_support : Finset object.Vertex) _window =>
            ⟨data.labelCount, data.labelSizeDistribution⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
