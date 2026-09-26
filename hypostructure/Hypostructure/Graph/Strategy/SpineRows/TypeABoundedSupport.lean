import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[87]`: the bounded Type A support

The Type A support of node `[86]` is `P_windowOrder`-free by node `[27]`; its
shortest internal paths are induced, so they have at most `windowOrder − 2`
edges, and the subcubic breadth-first count bounds it by
`1 + threshold·(2^(windowOrder − 2) − 1)` — `diam(X) ≤ 11` and `|X| ≤ 6142` in
the registered presentation.  Thin adapter of
`Contracts.TypeA.typeABoundedSupport`; the cubic baseline is read from
`K .cubicBaseline`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeABoundedSupportRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeABoundedSupport
    { Requires := [K .cubicBaseline, K .negativeSupport, K .remainderNormalized,
        K .typeALowSurplus]
      Produces := [K .typeABoundedSupport]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeABoundedSupport)
        ⟨Graph.Contracts.TypeA.typeABoundedSupport data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.1
          data.three_le_windowOrder inputs.current.baseline
          (inputs.get (K .negativeSupport)).down
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .typeALowSurplus)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
