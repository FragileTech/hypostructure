import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[180]`'s accepted cycle is incompatible with the selected
counterexample fact already present on the same ExactLedger. -/
noncomputable instance instIncompatibleSelectionPairPowerOfTwoCycle :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .pairPowerOfTwoCycle) where
  contradiction := fun _current selection cycle =>
    selection.down.1 cycle.down

/-- Node `[133]`: a named sparse surplus exit is incompatible with node
`[125]`'s survivor fact, which is exactly the absence of every such exit. -/
noncomputable instance instIncompatibleSparseSurplusSurvivorSparsePairExit :
    Incompatible (Input BranchState Presentation presentation data)
      (K .sparseSurplusSurvivor) (K .sparsePairExit) where
  contradiction := fun _current survivor exit => survivor.down exit.down

/-- Node `[19]`'s strict lower bound `σ(G) > C_sp ⌈√n⌉` is incompatible with a
spine surplus estimate `σ(G) ≤ C_sp ⌈√n⌉` on the same object. -/
noncomputable instance instIncompatibleSurplusAboveSpineSurplusEstimate :
    Incompatible (Input BranchState Presentation presentation data)
      (K .surplusAbove) (K .spineSurplusEstimate) where
  contradiction := fun current above estimate => by
    have lower : data.surplusThreshold current.object.vertexCount <
        current.object.degreeSurplus data.threshold := above.down
    have upper : current.object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt current.object.vertexCount :=
      estimate.down
    exact Nat.not_lt_of_ge (by
      simpa [Parameters.surplusThreshold] using upper) lower

end Hypostructure.Graph.Strategy.Spine
