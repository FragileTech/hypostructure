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

omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8LargeBudgetDeficitRow
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (failsFresh : K .route8LargeBudgetDeficitFails ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8LargeBudgetDeficit) (K .route8LargeBudgetDeficitFails) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8LargeBudgetDeficit) (K .route8LargeBudgetDeficitFails)
    `Hypostructure.Graph.Strategy.Spine.route8LargeBudgetDeficit
    (by
      classical
      letI : DecidableEq current.object.Vertex := current.object.vertices.decEq
      let packing := canonicalWindowPacking data current.object
      let support := current.object.remainderSupport packing
      let routeEight := (current.object.canonicalPieces support).filter
        (Route8Survives data current.object packing)
      by_cases lower : support.card ≤
          Graph.TypeBEnvelopeCharge.route8Deficit current.object support
              data.threshold data.dischargeScale routeEight +
            data.dischargeScale * current.object.boundaryIncidence support +
            data.bridgeMassFactor * data.dischargeScale *
              data.surplusThreshold current.object.vertexCount
      · exact .inl ⟨lower⟩
      · exact .inr ⟨lower⟩)
    deficitFresh failsFresh

end Hypostructure.Graph.Strategy.Spine
