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

/-! The rate reading as a decision (`rem:route8-carrier-margin` on an arm whose
density fact does not decide it): `K .route8Rate` or its exact complement. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8RateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .selection) known]
    (rateFresh : K .route8Rate ∉ known)
    (failsFresh : K .route8RateFails ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8Rate) (K .route8RateFails) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8Rate) (K .route8RateFails)
    `Hypostructure.Graph.Strategy.Spine.route8RateDichotomy
    (by
      classical
      let _selected := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .selection)).down
      exact if rate : Graph.Route8Census.Rate current.object
          (canonicalWindowPacking data current.object) data.threshold data.dischargeScale
          (data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold current.object.vertexCount) then
        .inl ⟨rate⟩
      else
        .inr ⟨rate⟩)
    rateFresh failsFresh

end Hypostructure.Graph.Strategy.Spine
