import Hypostructure.Graph.Strategy.SpineVocabulary
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

/-! ## Nodes `[13]`--`[14]`: interface replacement

`lem:replacement` and `cor:uncompressible`, stated about G.  A replacement of a
proper support `Z` of G is a `∂Z`-boundaried piece `X'` (not a reading of G)
with G's boundary-degree profile at `Z`, such that `G' = glue X' (G − Z)` meets
the baseline, is strictly smaller than G and has no power-of-two cycle.
Minimality gives `G'` a power-of-two cycle, so no such replacement exists.

Node `[13]` records the exclusion itself.  Its proof is performed at the
literal residual and reads nothing but the selection fact's minimality. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def replacementExclusionRow :
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
    `Hypostructure.Graph.Strategy.Spine.replacementExclusion
    { Requires := [K .selection]
      Produces := [K .replacementExclusion]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .replacementExclusion)
        ⟨Contracts.Spine.replacementExclusion_of_selection data.toParameters
          inputs.current.object (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
