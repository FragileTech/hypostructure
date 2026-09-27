import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exclusion

/-!
# The closures of the saturated Type A exits

`lem:typeA-exits-discharged`: exits `(1)`--`(3)`, `(5)` and `(6)` are closed
exits.  Each closure is registered here as a semantic incompatibility between
the committed exit fact and a committed upstream invariant, so Core's
`closeIncompatible` appends the closure key from the two facts; the
contradiction itself is the contract lemma of `Graph.Contracts.TypeA`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[96]`**: a Mersenne anchored return against the return-avoidance
invariant of nodes `[5]`--`[7]`. -/
noncomputable instance typeAExitOneReturnClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .returnAvoidance)
      (K (data := data) .typeAExitOneReturn) where
  contradiction := fun input avoidance exit =>
    Graph.Contracts.TypeA.typeAExitOneReturn_contradiction data.toParameters
      input.object avoidance.down exit.down

/-- **Node `[98]`**: a power-of-two common-port theta against the selection's
target avoidance. -/
noncomputable instance typeAExitTwoThetaClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection)
      (K (data := data) .typeAExitTwoTheta) where
  contradiction := fun input selected exit =>
    Graph.Contracts.TypeA.typeAExitTwoTheta_contradiction data.toParameters
      input.object selected.down.1 exit.down

/-- **Node `[100]`**: the accepted cycle closed by the exit-`(3)` label
collision (on the first pass or after peeling) against the selection's target
avoidance. -/
noncomputable instance typeAExitThreeCycleClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection)
      (K (data := data) .typeAExitThreeCycle) where
  contradiction := fun input selected cycle =>
    Graph.Contracts.TypeA.typeAExitThreeCycle_contradiction
      data.toParameters input.object selected.down.1 cycle.down

/-- **Node `[96]` after peeling**: a Mersenne anchored return through the
overloaded port of the terminal state against the return-avoidance invariant. -/
noncomputable instance typeAPeeledExitOneReturnClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .returnAvoidance)
      (K (data := data) .typeAPeeledExitOneReturn) where
  contradiction := fun input avoidance exit =>
    Graph.Contracts.TypeA.typeAPeeledExitOneReturn_contradiction
      data.toParameters input.object avoidance.down exit.down

/-- **Node `[98]` after peeling**: a power-of-two common-port theta at the
terminal state against the selection's target avoidance. -/
noncomputable instance typeAPeeledExitTwoThetaClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection)
      (K (data := data) .typeAPeeledExitTwoTheta) where
  contradiction := fun input selected exit =>
    Graph.Contracts.TypeA.typeAPeeledExitTwoTheta_contradiction
      data.toParameters input.object selected.down.1 exit.down

/-- **Node `[104]`**: the exit-`(5)` compression against `cor:uncompressible`. -/
noncomputable instance typeAExitFiveClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .uncompressible)
      (K (data := data) .typeAExitFive) where
  contradiction := fun input uncompressible exit =>
    Graph.Contracts.TypeA.typeAExitFive_contradiction data.toParameters
      input.object uncompressible.down exit.down

/-- **Node `[106]`, proper scope**: `lem:proper-smearing`'s replacement against
`lem:replacement`. -/
noncomputable instance typeAExitSixProperClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .replacementExclusion)
      (K (data := data) .typeAExitSixProper) where
  contradiction := fun input exclusion exit =>
    Graph.Contracts.TypeA.typeAExitSixProper_contradiction data.toParameters
      input.object exclusion.down exit.down

/-- **Node `[106]`, whole-graph scope**: `lem:no-silent-global-smearing`'s
strictly smaller closed representative against the selection's minimality. -/
noncomputable instance typeAExitSixGlobalClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection)
      (K (data := data) .typeAExitSixGlobal) where
  contradiction := fun input selected exit =>
    Graph.Contracts.TypeA.typeAExitSixGlobal_contradiction data.toParameters
      input.object selected.down.1
      (fun representative smaller base => selected.down.2 representative smaller base)
      exit.down

end Hypostructure.Graph.Strategy.Spine
