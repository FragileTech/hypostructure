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
noncomputable def route8SmallCoreCollapseRow
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8CarrierCore) known]
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8SmallCoreEntry) (K .route8NoSmallCoreEntry) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8SmallCoreEntry) (K .route8NoSmallCoreEntry)
    `Hypostructure.Graph.Strategy.Spine.route8SmallCoreCollapse
    (by
      classical
      let core := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .route8CarrierCore)).down
      letI : DecidableEq current.object.Vertex := current.object.vertices.decEq
      let packing := canonicalWindowPacking data current.object
      let support := current.object.remainderSupport packing
      let routeEight := (current.object.canonicalPieces support).filter
        (Route8Survives data current.object packing)
      by_cases small : ∃ component ∈ routeEight,
          let piece := current.object.pieceSupport support component
          ∃ receiver ∈ Graph.VisibleEntry.saturatedReceivers current.object piece
              data.threshold data.dischargeScale,
            ∃ load ∈ Graph.VisibleEntry.silentExcess current.object piece
                data.threshold data.dischargeScale receiver,
              let index : Graph.Route8Census.Index current.object :=
                (piece, receiver, load)
              ((Graph.Route8Census.presented current.object data.threshold
                  data.LengthOK index).toEntry
                (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1
      · exact .inl ⟨⟨core, small⟩⟩
      · exact .inr ⟨⟨core, by
          dsimp only
          intro component componentMem
          intro receiver receiverMem
          intro load loadMem alphaSmall
          apply small
          refine ⟨component, componentMem, ?_⟩
          refine ⟨receiver, receiverMem, ?_⟩
          exact ⟨load, loadMem, alphaSmall⟩⟩⟩)
    smallFresh noSmallFresh

end Hypostructure.Graph.Strategy.Spine
