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

/-! ## Node `[72]`: compatible open pairs close in the assigned fan -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def compatiblePairFanClosureRow :
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
    `Hypostructure.Graph.Strategy.Spine.compatiblePairFanClosure
    { Requires := [K .fanClosedPort]
      Produces := [K .compatiblePairFanClosure]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fanClosedDefinition := (inputs.get (K .fanClosedPort)).down
      .cons (key := K .compatiblePairFanClosure) ⟨by
        change CompatiblePairFanClosureStatement data inputs.current.object
        intro profile left right compatible leftRemainder rightRemainder
          leftAssigned rightAssigned
        have closed := Graph.TypeBFanClosedPorts.compatiblePairFanClosure
          profile compatible leftRemainder rightRemainder leftAssigned
            rightAssigned
        exact ⟨(fanClosedDefinition profile left).2
            ((fanClosedDefinition profile left).1 closed.1),
          (fanClosedDefinition profile right).2
            ((fanClosedDefinition profile right).1 closed.2.1),
          closed.2.2⟩
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
