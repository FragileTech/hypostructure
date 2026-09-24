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

/-! The dominant type has exactly the manuscript's next local dichotomy: its
root contains an internal wedge or it does not.  Both outputs retain the same
packing, dominant fibre, root, count, and type-equality witnesses. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def dominantRootedTypeWedgeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .dominantRootedType) known]
    (wedgeFresh : K .dominantRootedWedgeType ∉ known)
    (wedgeFreeFresh : K .dominantRootedTypeWedgeFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .dominantRootedWedgeType) (K .dominantRootedTypeWedgeFree) previous :=
  let dominantInput := (@ExactLedger.get
    (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    current known previous (K .dominantRootedType)).down
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .dominantRootedWedgeType) (K .dominantRootedTypeWedgeFree)
    `Hypostructure.Graph.Strategy.Spine.dominantRootedTypeWedgeDichotomy
    (by
      classical
      let packing := Classical.choose dominantInput
      have packingSpec := Classical.choose_spec dominantInput
      have valid := packingSpec.1
      have maximal := packingSpec.2.1
      have rankEq := packingSpec.2.2.1
      have dominantData := packingSpec.2.2.2
      dsimp only at dominantData
      let dominant := Classical.choose dominantData
      have dominantSpec := Classical.choose_spec dominantData
      let root := Classical.choose dominantSpec
      have rootSpec := Classical.choose_spec dominantSpec
      let dominantSubset := Classical.choose rootSpec
      have dominantSubsetSpec := Classical.choose_spec rootSpec
      let rootMem := Classical.choose dominantSubsetSpec
      have payload := Classical.choose_spec dominantSubsetSpec
      have count := payload.1
      have sameType := payload.2.1
      let subcubic := remainderSubcubicSupport data current.object packing
      by_cases wedge : DominantRootWedgeClause current.object subcubic root
      · exact .inl ⟨packing, valid, maximal, rankEq, dominant, root,
          dominantSubset, rootMem, count, sameType, wedge⟩
      · exact .inr ⟨packing, valid, maximal, rankEq, dominant, root,
          dominantSubset, rootMem, count, sameType, wedge⟩)
    wedgeFresh wedgeFreeFresh

end Hypostructure.Graph.Strategy.Spine
