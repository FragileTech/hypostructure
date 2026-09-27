import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Terminal

/-!
# Node `[124]`: the local exclusion of the two-support route-8 obstruction

`thm:typeA-two-carrier-nogo`: a terminal two-support route-`8` entry has no
exit-`(4)` witness, while `lem:typeA-carrier-deletion-exit` turns its
carrier-deletion quotient into the canonical Q5 witness.  The second fact is
published by a row on each collection that reaches node `[124]` -- the
route-`8` collection `𝒳_A` (through node `[118]`) and the unified collection
(through nodes `[123]` and `[181]`) -- and the closure is the framework's
`Incompatible` against the terminal entry fact.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[124]` on `𝒳_A`, at `ι₂`**: the two-support entry fixed by node
`[117]` carries its canonical exit-`(4)` witness, built from its declared
deletion witnesses (T5, node `[118]`).  The true route-`8` residual supplies
its selected basin, the node-`[115]` no-arm supplies `α ≥ 2`. -/
@[reducible] noncomputable def route8TwoCarrierExitRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8TwoCarrierExit
    { Requires := [K .route8TrueResidual, K .route8NoSmallCoreEntry,
        K .route8CarrierDeletionWitnesses, K .cubicBaseline]
      Produces := [K .route8TwoCarrierExit]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8TwoCarrierExit)
        ⟨Graph.Contracts.RouteEight.route8SurvivorTwoCarrierExit
          data.toParameters inputs.current.object inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.2.1; omega)
          (inputs.get (K .route8TrueResidual)).down
          (inputs.get (K .route8NoSmallCoreEntry)).down
          (inputs.get (K .route8CarrierDeletionWitnesses)).down⟩ .nil)
    0 0

/-- **Node `[124]` on the unified collection, at the terminal entry `ξ`**:
`ξ`'s (T1)--(T4) clauses (node `[334]`) give its canonical exit-`(4)`
witness. -/
@[reducible] noncomputable def route8UnifiedTwoCarrierExitRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedTwoCarrierExit
    { Requires := [K .route8UnifiedTrueTwoCarrierEntry]
      Produces := [K .route8UnifiedTwoCarrierExit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedTwoCarrierExit)
        ⟨Graph.Contracts.RouteEight.route8UnifiedTwoCarrierExit
          data.toParameters inputs.current.object
          (inputs.get (K .route8UnifiedTrueTwoCarrierEntry)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **`thm:typeA-two-carrier-nogo` after node `[118]`**: the selected true
two-support entry of `𝒳_A` has no exit-`(4)` witness, node `[124]` gives it
one. -/
noncomputable instance instIncompatibleRoute8TrueTwoCarrierEntryTwoCarrierExit :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8TrueTwoCarrierEntry) (K .route8TwoCarrierExit) where
  contradiction := fun input trueEntry exit =>
    Graph.Contracts.RouteEight.route8TrueTwoCarrierEntry_false
      data.toParameters input.object trueEntry.down exit.down

/-- **`thm:typeA-two-carrier-nogo` on the unified collection**: the terminal
true two-support entry has no exit-`(4)` witness, node `[124]` gives it one. -/
noncomputable instance
    instIncompatibleRoute8UnifiedTrueTwoCarrierEntryUnifiedTwoCarrierExit :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8UnifiedTrueTwoCarrierEntry)
      (K .route8UnifiedTwoCarrierExit) where
  contradiction := fun input trueEntry exit =>
    Graph.Contracts.RouteEight.route8UnifiedTrueTwoCarrierEntry_false
      data.toParameters input.object trueEntry.down exit.down

end Hypostructure.Graph.Strategy.Spine
