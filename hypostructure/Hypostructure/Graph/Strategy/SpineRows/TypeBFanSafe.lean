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

/-! ## Standing Type B fan-safe interface

`def:typeB-fan-safe` is a standing interface definition used by both ordinary
Type B supports and decorated handoffs.  Its four non-geometric failure
predicates remain separate, so later producers instantiate them with their
literal label, target-defect, compression, and delocalization exits. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBFanSafeRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBFanSafe
    { Requires := []
      Produces := [K .typeBFanSafe]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanSafe) ⟨by
        change TypeBFanSafeStatement data inputs.current.object
        simp [TypeBFanSafeStatement, Graph.DecoratedHandoff.FanSafe]
      ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
