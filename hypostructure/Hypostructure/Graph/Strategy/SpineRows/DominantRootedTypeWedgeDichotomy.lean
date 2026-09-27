import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.DominantType

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! The dominant type has exactly the manuscript's next local dichotomy: the
root of the canonical dominant type `canonicalDominantRootedType?` that node
`[431]` fixed contains an internal wedge or it does not.  Both arms name that
one pair. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def dominantRootedTypeWedgeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .dominantRootedType) known]
    (wedgeFresh : K .dominantRootedWedgeType ∉ known)
    (wedgeFreeFresh : K .dominantRootedTypeWedgeFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .dominantRootedWedgeType) (K .dominantRootedTypeWedgeFree) previous :=
  let dominantInput := (@ExactLedger.get
    (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    current known previous (K .dominantRootedType)).down
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .dominantRootedWedgeType) (K .dominantRootedTypeWedgeFree)
    `Hypostructure.Graph.Strategy.Spine.dominantRootedTypeWedgeDichotomy
    (by
      classical
      exact if wedge :
          DominantRootedWedgeTypeStatement data.toParameters current.object then
        .inl ⟨wedge⟩
      else
        .inr ⟨(Contracts.Spine.dominantRootedWedgeType_or_wedgeFree
          data.toParameters current.object dominantInput).resolve_left wedge⟩)
    wedgeFresh wedgeFreeFresh

end Hypostructure.Graph.Strategy.Spine
