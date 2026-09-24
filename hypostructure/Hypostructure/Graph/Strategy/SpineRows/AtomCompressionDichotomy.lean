import Hypostructure.Graph.Strategy.SpineVocabulary

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
      (K .degreeProfileFibres) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .targetCompleteContextUniversality) known]
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
      let inherited := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .contextUniversal)).down
      let packing := Classical.choose inherited
      have packingSpec := Classical.choose_spec inherited
      have valid := packingSpec.1
      have packingCard := packingSpec.2.1
      let test := Classical.choose packingSpec.2.2
      have testSpec := Classical.choose_spec packingSpec.2.2
      let determiners := Classical.choose testSpec
      have determinersSpec := Classical.choose_spec testSpec
      let quotient := Classical.choose determinersSpec
      have quotientSpec := Classical.choose_spec determinersSpec
      let supportData := Classical.choose quotientSpec
      have selected := Classical.choose_spec quotientSpec
      have certified := selected.1
      have universal := selected.2.2
      have packingPositive :=
        (@ExactLedger.get
          (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .maximalPacking)).down.1
      have complete : TargetCompleteAt data quotient := by
        intro left right identified
        have targetComplete : Graph.Response.TargetComplete
            Graph.BoundaryPiece.boundaryDegreeProfile
            (Graph.HasCycleWithLength data.LengthOK) left right :=
          ⟨quotient.fibrewise left right identified,
            universal left right identified⟩
        exact ⟨(@ExactLedger.get
              (Input BranchState Presentation presentation data) _
              (factSystem BranchState Presentation presentation data)
              current known previous (K .degreeProfileFibres)).down
                quotient.support left right targetComplete,
          (@ExactLedger.get
            (Input BranchState Presentation presentation data) _
            (factSystem BranchState Presentation presentation data)
            current known previous
              (K .targetCompleteContextUniversality)).down
              quotient.support left right targetComplete⟩
      by_cases inside :
          quotient.support ⊆ current.object.remainderSupport packing
      · have packingNonempty : packing.Nonempty :=
          Finset.card_pos.mp (packingCard ▸ packingPositive)
        let member := Classical.choose packingNonempty
        have memberMem := Classical.choose_spec packingNonempty
        have windowNonempty :=
          current.object.nonempty_of_inducesWindow data.windowOrder_pos
            (valid.1 member memberMem)
        let vertex := Classical.choose windowNonempty
        have vertexMem := Classical.choose_spec windowNonempty
        have supportProper : ∃ vertex, vertex ∉ quotient.support := by
          refine ⟨vertex, ?_⟩
          intro vertexInSupport
          have vertexInRemainder := inside vertexInSupport
          exact
            (current.object.notMem_windowSupport_of_mem_remainderSupport
              vertexInRemainder)
              (current.object.mem_windowSupport memberMem vertexMem)
        have reducing : quotient.toRankQuotient.RankReducingOn
            ↑(remainderCurvatureTests current.object packing) :=
          certified.2.2.2.2.2.1
        have replacement := quotient.properRepresentative supportProper reducing
        exact .inl ⟨⟨packing, valid, quotient,
          ⟨test, determiners, supportData, certified⟩, complete, inside,
          replacement⟩⟩
      · exact .inr ⟨⟨packing, valid, quotient,
          ⟨test, determiners, supportData, certified⟩, complete, inside,
          remainderSupport_ssubset_delocalizationSupport data quotient
            inside⟩⟩)
    compressionFresh delocalizedFresh

end Hypostructure.Graph.Strategy.Spine
