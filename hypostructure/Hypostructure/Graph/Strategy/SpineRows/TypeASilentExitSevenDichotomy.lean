import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[109]`: the provenance of the route-`8` residual

The route-`8` residual either sits at a receiver whose Type A support has the
node-`[94]` silent-excess origin (`K .typeASilentExitSevenFree`), or it does
not (`K .typeAExitEightNotSilent`, the exact negation).  The silent-origin arm
is closed at node `[184]` against `lem:typeA-unified-visible-ownership`; the
other arm continues through Part IX. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeASilentExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (silentFresh : K .typeASilentExitSevenFree ∉ known)
    (notSilentFresh : K .typeAExitEightNotSilent ∉ known) :
    Decision (K .typeASilentExitSevenFree) (K .typeAExitEightNotSilent)
      previous :=
  Decision.run previous (K .typeASilentExitSevenFree)
    (K .typeAExitEightNotSilent)
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitSevenDichotomy
    (by
      classical
      by_cases silent :
          SelectedSilentExitSevenFree data.toParameters current.object
      · exact .inl ⟨silent⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitEightNotSilent_of_not_silent
          data.toParameters current.object silent⟩)
    silentFresh notSilentFresh

end Hypostructure.Graph.Strategy.Spine
