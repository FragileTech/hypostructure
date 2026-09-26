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

/-! ## Node `[178]`: normalize the first failed pair extension

The two count-failure routes retain different pair sets, but both now carry
the same mathematical datum: an actually realized baseline code and the least
pair extension at which the mixed count fails.  These rows read that witness
from the route's exact key and attach the failed pair's canonical connected
response support `X_π`. -/

/-- Node `[178]` on the full pair schedule selected at `[131]`. -/
@[reducible] noncomputable def freePairOverlapFirstFailureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairOverlapFirstFailure
    { Requires := [K .freePairCodeUnrealized, K .noProperBaseline]
      Produces := [K .pairOverlapFirstFailure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapFirstFailure)
        ⟨Graph.Contracts.SurplusPair.pairOverlapFirstFailure_of_freeCodeUnrealized
          (inputs.get (K .freePairCodeUnrealized)).down
          (inputs.get (K .noProperBaseline)).down⟩
        .nil)

/-- Node `[178]` on the literal capacity-free side selected at `[137]`. -/
@[reducible] noncomputable def blockedPairOverlapFirstFailureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairOverlapFirstFailure
    { Requires := [K .blockedPairCodeUnrealized, K .noProperBaseline]
      Produces := [K .pairOverlapFirstFailure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapFirstFailure)
        ⟨Graph.Contracts.SurplusPair.pairOverlapFirstFailure_of_blockedCodeUnrealized
          (inputs.get (K .blockedPairCodeUnrealized)).down
          (inputs.get (K .noProperBaseline)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
