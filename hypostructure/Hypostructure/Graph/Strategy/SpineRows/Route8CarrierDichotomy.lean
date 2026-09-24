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
noncomputable def route8CarrierDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8TwoCarrierEntry) (K .route8NoTwoCarrierEntry) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8TwoCarrierEntry) (K .route8NoTwoCarrierEntry)
    `Hypostructure.Graph.Strategy.Spine.route8CarrierDichotomy
    (by
      classical
      let packing := canonicalWindowPacking data current.object
      let support := current.object.remainderSupport packing
      let routeEight := (current.object.canonicalPieces support).filter
        (Route8Survives data current.object packing)
      exact if twoCarrier : ∃ index ∈
            Graph.Route8Census.entriesOfComponents current.object packing
              routeEight data.threshold data.dischargeScale,
          Graph.Route8Census.CollectionTwoCarrierEntry current.object packing
            routeEight data.threshold data.dischargeScale data.LengthOK index then
        .inl ⟨twoCarrier⟩
      else
        .inr ⟨by
          intro index indexMem two
          exact twoCarrier ⟨index, indexMem, two⟩⟩)
    twoFresh noTwoFresh

end Hypostructure.Graph.Strategy.Spine
