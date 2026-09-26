import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exclusion

/-! # Node `[86]`, `lem:typeA-exclusion`

*"Consequently a Type A support with `N₀(X) < 0` must carry an admissible
route-8 residual profile, produce the Type B handoff, or contain an exit-(4)
witness for a routed load."*  Stated over every connected admissible sub-support
of a maximal packing's remainder.  Thin adapter of
`Contracts.TypeA.typeAExclusion`; the cubic baseline is read from
`K .cubicBaseline`. -/

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
    { Requires := [K .selection, K .replacementExclusion, K .cubicBaseline]
      Produces := [K .typeAExclusion]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      .cons (key := K .typeAExclusion)
        ⟨Graph.Contracts.TypeA.typeAExclusion data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.1
          data.degenerateClosureRejected selection.1 selection.2
          (inputs.get (K .replacementExclusion)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
