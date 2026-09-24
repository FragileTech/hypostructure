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

/-! ## Node `[36]`: the context-validity test

The literal post-`[35]` ledger retains the one inclusion-minimal determination
certificate selected at `[33]` and now also carries `lem:separated-testers`.
Node `[36]` asks the paper's exact question of that certificate: does its
determination remain valid against every outside context?  The no arm exhibits
an identified pair and a distinguishing context; the yes arm records context
universality for that same certificate.  Boundary-fibre preservation is already
part of the admissible quotient and is not a second test here. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def contextValidityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .branchDependence) known]
    (defectFresh : K .contextDefect ∉ known)
    (universalFresh : K .contextUniversal ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .contextDefect) (K .contextUniversal) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .contextDefect) (K .contextUniversal)
    `Hypostructure.Graph.Strategy.Spine.contextValidityDichotomy
    (by
      classical
      let inherited := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .branchDependence)).down
      let packing := Classical.choose inherited
      have packingSpec := Classical.choose_spec inherited
      let test := Classical.choose packingSpec.2.2.2
      have testSpec := Classical.choose_spec packingSpec.2.2.2
      dsimp only at testSpec
      let determiners := Classical.choose testSpec
      have determinersSpec := Classical.choose_spec testSpec
      let quotient := Classical.choose determinersSpec
      have quotientSpec := Classical.choose_spec determinersSpec
      let supportData := Classical.choose quotientSpec
      have selected := Classical.choose_spec quotientSpec
      have certified := selected.1
      have minimal := selected.2
      have valid := packingSpec.1
      have packingCard := packingSpec.2.1
      by_cases universal :
          ∀ left right, Identified quotient left right →
            Graph.Response.ContextEquivalent
              (Graph.HasCycleWithLength data.LengthOK) left right
      · exact .inr ⟨⟨packing, valid, packingCard, test, determiners, quotient,
          supportData, certified, minimal, universal⟩⟩
      · refine .inl ⟨⟨packing, valid, packingCard, test, determiners, quotient,
          supportData, certified, minimal, ?_⟩⟩
        push Not at universal
        obtain ⟨left, right, identified, failure⟩ := universal
        exact ⟨left, right, identified,
          Graph.Response.targetDefect_of_not_contextEquivalent failure⟩)
    defectFresh universalFresh

end Hypostructure.Graph.Strategy.Spine
