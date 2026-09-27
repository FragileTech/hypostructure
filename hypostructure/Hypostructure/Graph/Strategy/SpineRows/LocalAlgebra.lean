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

The row publishes exactly the two assertions of `lem:labels`: the cardinality of
the legal-label set and its displayed size distribution.  Both are laws of the
registered presentation, published once at the entry in the presentation-law
fact `K .cubicBaseline`; the row reads them from that fact.  The manuscript's
`C_s` and `Ω₂` are already the definitions `WindowCurvature.Safe` and
`WindowCurvature.curvatureTwo`; they are deliberately not republished as
reflection theorems outside the registered legal-label schedule.
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
    { Requires := [K .cubicBaseline]
      Produces := [K .localAlgebra]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .localAlgebra)
        (show Value BranchState Presentation presentation data
            .localAlgebra inputs.current from
          ⟨(inputs.get (K .cubicBaseline)).down.1.2.2.2.2⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
