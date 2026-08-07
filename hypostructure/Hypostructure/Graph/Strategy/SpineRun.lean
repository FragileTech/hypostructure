import Hypostructure.Graph.Strategy.SurplusRun

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def run
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection)) :
    SpineWithSurplusResult opened.selected :=
  runWithSurplusBranch T targetPredicate opened

end Hypostructure.Graph.Strategy.Spine
