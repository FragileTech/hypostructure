import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[180]`, direct arithmetic arm.  The row applies the canonical serial
spectrum API, recovers the actual simple cycle stored by `[179]`, proves its
exponent is at least two from simple-cycle length, and publishes the accepted
cycle. -/
@[reducible] noncomputable def pairPowerOfTwoCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairPowerOfTwoCycle
    { Requires := [K .pairSerialArithmetic, K .surplusPresentation]
      Produces := [K .pairPowerOfTwoCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairPowerOfTwoCycle)
        ⟨Graph.Contracts.SurplusPair.pairPowerOfTwoCycle_of_arithmetic (inputs.get (K .pairSerialArithmetic)).down
          (inputs.get (K .surplusPresentation)).down.2.2.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
