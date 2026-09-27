import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # `lem:typeA-port-return`

Every completion port of every receiver of the saturated Type A support carries
an anchored return (`lem:bridgeless` on the selected minimal counterexample).
This makes every saturated port test of nodes `[95]`--`[107]` nonvacuous.
Thin adapter of `Contracts.TypeA.typeAPortReturn`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAPortReturnRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPortReturn
    { Requires := [K .cubicBaseline, K .selection, K .typeASaturatedReceiver]
      Produces := [K .typeAPortReturn]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      .cons (key := K .typeAPortReturn)
        ⟨Graph.Contracts.TypeA.typeAPortReturn data.toParameters
          inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.1.1; omega)
          inputs.current.baseline selection.1 selection.2
          (inputs.get (K .typeASaturatedReceiver)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
