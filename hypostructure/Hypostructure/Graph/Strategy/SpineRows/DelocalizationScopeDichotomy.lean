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

/-! ### Node `[41]`: is the enlarged support proper in `G`?

The yes arm is the terminal `[42]`, `lem:proper-smearing`: *"Regard `Z` as a
boundaried graph ... Since `Z ⊊ G`, it is a proper boundaried support.  If the
dependence fails against some outside `∂Z`-context, it is target-defective.  If
it succeeds against every outside context, it is a nontrivial target-complete
compression of the proper support `Z`, forbidden by `cor:uncompressible`."*  The
no arm is node `[43]`, whole-graph delocalization. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def delocalizationScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .delocalizedSupport) known]
    (properFresh : K .properDelocalization ∉ known)
    (globalFresh : K .globalDelocalization ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .properDelocalization) (K .globalDelocalization) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .properDelocalization) (K .globalDelocalization)
    `Hypostructure.Graph.Strategy.Spine.delocalizationScopeDichotomy
    (by
      classical
      let inherited := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .delocalizedSupport)).down
      let packing := Classical.choose inherited
      have packingSpec := Classical.choose_spec inherited
      have valid := packingSpec.1
      let quotient := Classical.choose packingSpec.2
      have quotientSpec := Classical.choose_spec packingSpec.2
      have certificate := quotientSpec.1
      have complete := quotientSpec.2.1
      have outside := quotientSpec.2.2.1
      -- The paper's `Z` is the quotient's connected determination support.
      -- Classifying any enlarged bookkeeping union here would not establish
      -- the empty-boundary closed exact profile required at node `[43]`.
      by_cases proper : ∃ vertex, vertex ∉ quotient.support
      · let vertex := Classical.choose proper
        have vertexOutside := Classical.choose_spec proper
        let test := Classical.choose certificate
        have testSpec := Classical.choose_spec certificate
        let determiners := Classical.choose testSpec
        have determinersSpec := Classical.choose_spec testSpec
        let supportData := Classical.choose determinersSpec
        have certified := Classical.choose_spec determinersSpec
        have reducing : quotient.toRankQuotient.RankReducingOn
            ↑(remainderCurvatureTests current.object packing) :=
          certified.2.2.2.2.2.1
        have replacement := quotient.properRepresentative proper reducing
        exact .inl ⟨⟨packing, valid, quotient,
          ⟨test, determiners, supportData, certified⟩, complete, outside,
          vertex, vertexOutside, replacement⟩⟩
      · push Not at proper
        exact .inr ⟨⟨packing, valid, quotient, certificate, complete, outside,
          proper⟩⟩)
    properFresh globalFresh

end Hypostructure.Graph.Strategy.Spine
