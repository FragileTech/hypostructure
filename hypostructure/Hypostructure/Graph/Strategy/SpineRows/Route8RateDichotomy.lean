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

/-! The rate reading as a decision (G's exact strong rate `s·|∂R| + F·s·T < |R|`, which the
manuscript's `τ < 3/13` implies): `K .route8Rate` or its exact complement,
read after the arm's density fact (`[24]` or `[56]`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8RateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    (density : Key)
    (densityArm : density = .netDeficiencyCap ∨ density = .denseDeficiencyBelow)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K density) known]
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
      letI : FactSystem (Input BranchState Presentation presentation data) :=
        factSystem BranchState Presentation presentation data
      -- The predecessor is the arm's density fact (`[24]`'s cap
      -- `K .netDeficiencyCap`, or `[56]`'s `K .denseDeficiencyBelow`); it does
      -- not decide the rate, which is tested at G's fixed packing `P₀`.
      have _density := (previous.get (K density)).down
      have _arm := densityArm
      exact if rate : Graph.Route8Census.StrongRate current.object
          (canonicalWindowPacking data.toParameters current.object) data.dischargeScale
          (data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold current.object.vertexCount) then
        .inl ⟨rate⟩
      else
        .inr ⟨rate⟩)
    rateFresh failsFresh

end Hypostructure.Graph.Strategy.Spine
