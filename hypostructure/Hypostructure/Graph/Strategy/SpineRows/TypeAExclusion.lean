import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exclusion

/-! # Node `[86]`, `lem:typeA-exclusion`

*"Consequently a Type A support with `N₀(X) < 0` must carry an admissible
route-8 residual profile, produce the Type B handoff, or contain an exit-(4)
witness for a routed load."*  Stated at the negative zero-surplus canonical
pieces of `G`'s fixed packing `P₀`, the pieces `thm:branch-kill` classifies.
Thin adapter of `Contracts.TypeA.typeAExclusion`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExclusion
    { Requires := [K .selection, K .replacementExclusion, K .remainderNormalized]
      Produces := [K .typeAExclusion]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      .cons (key := K .typeAExclusion)
        ⟨Graph.Contracts.TypeA.typeAExclusion data.toParameters
          inputs.current.object selection.1 selection.2
          (inputs.get (K .replacementExclusion)).down
          (inputs.get (K .remainderNormalized)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
