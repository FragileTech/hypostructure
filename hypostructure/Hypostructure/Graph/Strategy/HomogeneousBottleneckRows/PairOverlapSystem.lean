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

/-- **`def:pair-overlap-system` at node `[178]`.**

Both count-failure routes have already been normalized to the same exact
first-failure key.  This row reads that key and the retained connectivity fact,
selects every canonical pair support `X_π`, and publishes the manuscript's
literal conditional-fibre overlap system. -/
@[reducible] noncomputable def pairOverlapSystemRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairOverlapSystem
    { Requires := [K .pairOverlapFirstFailure, K .noProperBaseline]
      Produces := [K .pairOverlapSystem]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapSystem)
        ⟨Graph.Contracts.SurplusPair.pairOverlapSystem_of_firstFailure
          (inputs.get (K .pairOverlapFirstFailure)).down
          (inputs.get (K .noProperBaseline)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
