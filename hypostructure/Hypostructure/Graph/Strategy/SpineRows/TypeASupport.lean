import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[86]`: the Type A support

On the `[62]` no arm the negative support of node `[61]` has `σ(X) = 0`
(`def:typeA-support`), and its negative net charge reads
`s·def⁺(X) < |V(X)|`.  Thin adapter of `Contracts.TypeA.typeASupport`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeASupportRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeASupport
    { Requires := [K .negativeSupport, K .typeALowSurplus]
      Produces := [K .typeASupport]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASupport)
        ⟨Graph.Contracts.TypeA.typeASupport data.toParameters inputs.current.object
          (inputs.get (K .negativeSupport)).down
          (inputs.get (K .typeALowSurplus)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
