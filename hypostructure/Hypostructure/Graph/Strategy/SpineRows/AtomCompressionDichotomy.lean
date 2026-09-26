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

/-! ## Nodes `[38]`--`[46]`: the rest of Branch D, and why every arm closes

`lem:curvature-dependence-routing` routes a determination certificate into three
cases and Part III's diagram closes each one:

* `[38]`/`[39]` -- the determination holds already at the proper atom `C`, so
  `q` is a target-complete rank-reducing quotient of `C` and
  `def:admissible-rank-quotient` supplies a strictly smaller proper
  representative.  `cor:uncompressible` forbids it.
* `[40]`--`[42]` -- it holds only after adjoining a connected `Z ⊋ C`, and
  `Z ⊊ G`.  `lem:proper-smearing`: `Z` is a proper boundaried support, so the
  dependence is target-defective or a target-complete compression of `Z`, both
  forbidden.
* `[43]`--`[46]` -- `Z = G`.  `lem:no-silent-global-smearing`: the closed clause
  of `def:admissible-rank-quotient` supplies a strictly smaller admissible closed
  representative `G_q`, which is finite, simple, meets the baseline, and cannot
  contain an accepted cycle because `G` does not.  So `G_q` is a strictly
  smaller counterexample, contradicting minimality.

The two refutations are the same two the manuscript uses, and
`Graph.DeclaredQuotient.localize` is the scope split between them. -/

/-! ### Node `[38]`: is the determination certified already at `C`?

*"Target-complete with smaller proper representative?"*  The yes arm is the
terminal `[39]`, proper atom compression -- case (ii): *"if it holds for every
outside context already with support `C`, then `q` is a target-complete
rank-reducing quotient of the proper boundaried piece `C`"*.  The no arm is node `[40]`: the
determination reaches outside `C`, so the connected support it needs strictly
contains `C`, which is case (iii)'s entry. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def atomCompressionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .contextUniversal) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .maximalPacking) known]
    (compressionFresh : K .atomCompression ∉ known)
    (delocalizedFresh : K .delocalizedSupport ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .atomCompression) (K .delocalizedSupport) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .atomCompression) (K .delocalizedSupport)
    `Hypostructure.Graph.Strategy.Spine.atomCompressionDichotomy
    (by
      classical
      let universal := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .contextUniversal)).down
      let maximal := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .maximalPacking)).down
      exact if compression :
          AtomCompressionStatement data.toParameters current.object then
        .inl ⟨compression⟩
      else
        .inr ⟨(Contracts.Spine.atomCompression_or_delocalizedSupport
          data.toParameters current.object universal
          maximal.1).resolve_left compression⟩)
    compressionFresh delocalizedFresh

end Hypostructure.Graph.Strategy.Spine
