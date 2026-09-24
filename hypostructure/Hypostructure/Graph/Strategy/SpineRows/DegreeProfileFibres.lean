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

/-! ## Node `[11]`: boundary-degree fibres

`lem:degree-profile-fibres`.  Condition (a) of
`def:target-complete-quotient` says that every target-complete identification
of two boundaried pieces has the same boundary-degree profile.  Equivalently,
two states in different fibres cannot be quotient-merged.  The statement is
about every target-complete identification, not only the narrower admissible
rank quotients represented by `Graph.DeclaredQuotient`.

The manuscript proof only unfolds that condition.  Accordingly this row has
no predecessor requirement, but its produced proposition is indexed by
`inputs.current.object`; the field projection is performed inside the sealed
executor and the residual instance is appended to the literal ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def degreeProfileFibresRow :
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
    `Hypostructure.Graph.Strategy.Spine.degreeProfileFibres
    (sourceFreeManifest (K .degreeProfileFibres))
    (fun inputs =>
      .cons (key := K .degreeProfileFibres)
        (show Value BranchState Presentation presentation data
            .degreeProfileFibres inputs.current from
          ⟨fun _support _left _right complete => complete.profile_eq⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
