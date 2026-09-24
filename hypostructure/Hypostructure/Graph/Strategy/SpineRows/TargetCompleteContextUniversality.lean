import Hypostructure.Graph.Strategy.SpineRows.Basic

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

/-! ## Node `[12]`: context-universality

`lem:context-universality`.  Condition (b) of
`def:target-complete-quotient` says that every target-complete identification
has the same target response in every outside context.  Like node `[11]`, this
is a field projection from the paper's target-completeness hypothesis.  The
row is source-free, publishes exactly that semantic fact, and appends it to the
literal ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def targetCompleteContextUniversalityRow :
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
    `Hypostructure.Graph.Strategy.Spine.targetCompleteContextUniversality
    (sourceFreeManifest (K .targetCompleteContextUniversality))
    (fun inputs =>
      .cons (key := K .targetCompleteContextUniversality)
        (show Value BranchState Presentation presentation data
            .targetCompleteContextUniversality inputs.current from
          ⟨fun _support _left _right complete => complete.contextEquivalent⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
