import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-!
# The switch at the separator, stated about G (nodes `[102]` and `[108]`)

G repair (R3b).  The identification of two separated response coordinates is
the switch at their separator `z`, constructed from G: the two configurations
exchange their continuations after `z`'s next incidences
(`DecoratedHandoff.Separation.switched`).  On the exit-(4) arm the canonical
witness is a Q4 member at G and its switched graph carries an accepted cycle
through an exchanged edge; on the exit-(7) arm the canonical surviving
separation's switched graph has no accepted cycle, keeps every degree and the
edge count, and is a counterexample of G's size.  No decision.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[102]` at G**: the exit-(4) peel is a switch peel. -/
@[reducible] noncomputable def typeAExitFourSwitchCycleRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourSwitchCycle
    { Requires := [K .typeASaturatedHandoffExitFour, K .selection]
      Produces := [K .typeAExitFourSwitchCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourSwitchCycle)
        ⟨Graph.Contracts.TypeA.typeAExitFourSwitchCycle data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .typeASaturatedHandoffExitFour)).down⟩ .nil)
    0 0

/-- **Node `[108]` at G**: the surviving separator's switch is a target-free
counterexample of G's size. -/
@[reducible] noncomputable def typeAExitSevenSwitchRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitSevenSwitch
    { Requires := [K .typeAExitSevenEnvelope, K .selection]
      Produces := [K .typeAExitSevenSwitch]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSevenSwitch)
        ⟨Graph.Contracts.TypeA.typeAExitSevenSwitch data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          inputs.current.baseline
          (fun smaller lt base =>
            (inputs.get (K .selection)).down.2.refinedMinimal smaller lt base)
          (inputs.get (K .typeAExitSevenEnvelope)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
