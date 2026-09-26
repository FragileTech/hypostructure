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

`lem:replacement` and `cor:uncompressible`.  A target-complete compression of a
proper atom would produce a strictly smaller baseline object whose obstruction
profile is contained in the original's; minimality gives that object the target,
context-universality carries the target back through the shared outside
context, and the reconstruction is isomorphic to the selected object, which
avoids the target.

Node `[13]` records the one-way replacement exclusion itself.  Its proof is
performed at the literal residual: the four represented replacement hypotheses
construct the replacement, and the selection fact supplies precisely
minimality and target avoidance.

The node `[13]` executor spells out its argument locally and reads nothing but
the selected context's `avoids` and `target_of_smaller`.  It therefore consumes
the selection fact and nothing else; no closure record, registration, or
payload stands between the fact and its consequence. -/
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
          inputs.current.object inputs.current.baseline inputs.current.branchState
          (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
