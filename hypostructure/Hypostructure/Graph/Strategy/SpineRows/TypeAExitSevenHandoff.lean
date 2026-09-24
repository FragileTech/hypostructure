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

/-! ## Nodes `[107]`--`[109]` and dashed input `[66]`

The predecessor is the exact selected no-exit-`(6)` fact.  Node `[107]`
decides only whether that same selected saturated handoff state produces a
decorated handoff envelope.  Node `[108]` records that produced envelope as the
Type B handoff.  Node `[65]` then proves `lem:decorated-fan-admissibility` from
that exact handoff and the inherited selection, normalization, and
uncompressibility facts.  The dashed Part VI input `[66]` passes the same
`K .typeAExitSevenHandoff` fact unchanged from `[108]` to `[65]`; it is a
routing edge, so it deliberately makes no duplicate ledger commit.
Node `[109]` routes the selected no-handoff residual unchanged into Part IX;
node `[110]` is the first new route-8 publication.
-/

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExitSevenHandoffRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenHandoff
    { Requires := [K .typeAExitSevenProduced]
      Produces := [K .typeAExitSevenHandoff]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let produced :=
        (inputs.get (K .typeAExitSevenProduced)).down
      .cons (key := K .typeAExitSevenHandoff)
        (show Value BranchState Presentation presentation data
            .typeAExitSevenHandoff inputs.current from
          ⟨produced⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
