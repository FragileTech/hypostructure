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

/-! ## Node `[72]`: canonical fan-closed-port definition

This row publishes the manuscript definition by exposing the already proved
`TypeBFanClosedPorts.Profile.IsFanClosed` predicate.  It does not introduce a
second predicate or repeat any graph argument. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def fanClosedPortRow :
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
    `Hypostructure.Graph.Strategy.Spine.fanClosedPort
    { Requires := []
      Produces := [K .fanClosedPort]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fanClosedPort) ⟨by
        change FanClosedPortStatement data inputs.current.object
        intro profile endpoint
        constructor
        · intro closed
          exact ⟨closed.1, closed.2,
            fun shoulder member =>
              closed.incidence_classified member⟩
        · rintro ⟨remainder, envelope, _classified⟩
          exact ⟨remainder, envelope⟩
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
