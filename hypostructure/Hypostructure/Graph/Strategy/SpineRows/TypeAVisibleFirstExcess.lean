import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[94]`: the visible-first excess

`lem:typeA-silent-excess-count` on the `[93]` no arm: no saturated receiver has
an overloaded completion port, so the visible-first excess is silent and
`S_sil^exc(X) ≥ s·D_A(X)`, cleared of division and subtraction as
`|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`.  Thin adapter of
`Contracts.TypeA.typeAVisibleFirstExcess`; the discharge scale is read from
`K .cubicBaseline`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAVisibleFirstExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAVisibleFirstExcess
    { Requires := [K .cubicBaseline, K .negativeSupport, K .typeAReceiverRouting,
        K .typeALowSurplus, K .typeASaturatedReceiver, K .typeANoVisibleEntry]
      Produces := [K .typeAVisibleFirstExcess]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAVisibleFirstExcess)
        ⟨Graph.Contracts.TypeA.typeAVisibleFirstExcess data.toParameters
          inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.2.1; omega)
          inputs.current.baseline (inputs.get (K .negativeSupport)).down
          (inputs.get (K .typeAReceiverRouting)).down
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeASaturatedReceiver)).down
          (inputs.get (K .typeANoVisibleEntry)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
