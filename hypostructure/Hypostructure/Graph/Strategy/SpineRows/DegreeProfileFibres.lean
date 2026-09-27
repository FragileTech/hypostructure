import Hypostructure.Graph.Strategy.SpineRows.Basic
import Hypostructure.Graph.Contracts.Spine.SpineSelection

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

/-! ## Node `[11]`: boundaried pieces and the boundary degree profile

`lem:degree-profile-fibres` (tex 6088), at G's own boundaried pieces: an
admissible rank quotient of the declared coordinates of a region of G never
identifies two realizations of its support that lie in different
boundary-degree fibres.  The paper's proof unfolds condition (a) of
`def:target-complete-quotient`, which `def:admissible-rank-quotient` requires of
every quotient of the system; the row has no predecessor fact, and its
proposition is indexed by `inputs.current.object`. -/
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
        ⟨Contracts.Spine.degreeProfileFibres_holds data.toParameters
          inputs.current.object⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
