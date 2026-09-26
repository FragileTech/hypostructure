import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BranchD

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

/-! ## Node `[32]`: the finite circuit form of the rank split

The paragraph immediately after `lem:target-rank-circuit` states the exact
finite implication `r_Ω(R) < W₂(R) ⇒` a raw curvature coordinate is
target-dependent.  The complementary finite arm is `r_Ω(R) = W₂(R)`;
`lem:full-rank` later records its weaker asymptotic consequence
`r_Ω(R) ≥ W₂(R) - o(W₂(R))`.  This decision publishes precisely those
two finite branch facts on the concrete remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def curvatureRankDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .targetRankCircuit) known]
    (dropFresh : K .curvatureRankDrop ∉ known)
    (fullFresh : K .curvatureFullRank ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .curvatureRankDrop) (K .curvatureFullRank) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .curvatureRankDrop) (K .curvatureFullRank)
    `Hypostructure.Graph.Strategy.Spine.curvatureRankDichotomy
    (by
      classical
      -- `lem:target-rank-circuit` at the manuscript's fixed maximal packing.
      let circuit := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .targetRankCircuit)).down
      let packing := canonicalWindowPacking data.toParameters current.object
      by_cases below :
          remainderCurvatureTargetRank data.toParameters current.object packing <
            remainderWedgeSupply current.object packing
      · exact .inl ⟨Contracts.Spine.curvatureRankDrop_of_rankBelow data.toParameters
          current.object circuit below⟩
      · exact .inr ⟨Contracts.Spine.curvatureFullRank_of_not_rankBelow
          data.toParameters current.object below⟩)
    dropFresh fullFresh

end Hypostructure.Graph.Strategy.Spine
