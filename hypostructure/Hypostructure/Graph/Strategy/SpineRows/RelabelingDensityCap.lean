import Hypostructure.Graph.Strategy.SpineRows.Basic
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

/- Exact finite invariant-state cap for relabellings fixing the packed window
support pointwise.  All class, state, invariance, and stabilizer data are bound
inside the published proposition. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def relabelingDensityCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.relabelingDensityCap
    (sourceFreeManifest (K .relabelingDensityCap))
    (fun inputs =>
      .cons (key := K .relabelingDensityCap)
        ⟨Contracts.Spine.relabelingDensityCap_of_orbitCount data.toParameters
          inputs.current.object⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
