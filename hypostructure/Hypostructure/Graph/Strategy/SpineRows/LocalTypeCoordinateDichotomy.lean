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

/-! ## Node `[50]`, the manuscript's second low-entropy split

The scalar entropy test does not imply a dominant rooted type.  On its low
arm, `prop:two-budget` next tests the literal maximum-packing radius-two type
coordinate for structural repetitiveness.  These two facts are exact
complements on the same packing selected by the incoming full-rank residual. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def localTypeCoordinateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .remainderEntropyLow) known]
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .curvatureFullRank) known]
    (repetitiveFresh : K .localTypeCoordinateRepetitive ∉ known)
    (nonrepetitiveFresh : K .localTypeCoordinateNonrepetitive ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .localTypeCoordinateRepetitive)
      (K .localTypeCoordinateNonrepetitive) previous :=
  let _low := (@ExactLedger.get
    (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    current known previous (K .remainderEntropyLow)).down
  let fullRank := (@ExactLedger.get
    (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    current known previous (K .curvatureFullRank)).down
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .localTypeCoordinateRepetitive)
      (K .localTypeCoordinateNonrepetitive)
    `Hypostructure.Graph.Strategy.Spine.localTypeCoordinateDichotomy
    (by
      classical
      let packing := Classical.choose fullRank
      have fullRankSpec := Classical.choose_spec fullRank
      have valid := fullRankSpec.1
      have maximal := fullRankSpec.2.1
      have rankEq := fullRankSpec.2.2
      by_cases repetitive :
          RemainderTypeCoordinateRepetitive data current.object packing
      · exact .inl ⟨packing, valid, maximal, rankEq, repetitive⟩
      · exact .inr ⟨packing, valid, maximal, rankEq, repetitive⟩)
    repetitiveFresh nonrepetitiveFresh

end Hypostructure.Graph.Strategy.Spine
