import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Nodes `[90]`--`[92]`: the unsaturated discharge and its closure

`[91]`, `lem:typeA-unsaturated-discharge`: at a Type A support all of whose
receivers are unsaturated (`[90]`), the `3/7/11` discharging gives
`|V(X)| ≤ s·def⁺(X)`.  `[92]`: this contradicts the Type A support's
`s·def⁺(X) < |V(X)|` from node `[86]`; the framework closes the branch from
the two committed facts. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAUnsaturatedDischargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischarge
    { Requires := [K .typeAReceiverRouting, K .typeALowSurplus,
        K .typeAUnsaturatedReceivers]
      Produces := [K .typeAUnsaturatedDischarge]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAUnsaturatedDischarge)
        ⟨Graph.Contracts.TypeA.typeAUnsaturatedDischarge data.toParameters
          inputs.current.object
          (inputs.get (K .typeAReceiverRouting)).down
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeAUnsaturatedReceivers)).down⟩
        .nil)

/-- **Node `[92]`**: the unsaturated charge bound contradicts the Type A
support's negative net charge. -/
noncomputable instance typeAUnsaturatedDischargeClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .typeASupport)
      (K (data := data) .typeAUnsaturatedDischarge) where
  contradiction := fun input support discharge =>
    Graph.Contracts.TypeA.typeASupport_unsaturatedDischarge_contradiction
      data.toParameters input.object support.down discharge.down

end Hypostructure.Graph.Strategy.Spine
