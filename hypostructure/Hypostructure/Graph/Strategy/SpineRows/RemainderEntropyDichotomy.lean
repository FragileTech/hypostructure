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

/-! ## Nodes `[49]`--`[50]`: the per-vertex remainder entropy split

`def:remainder-entropy` and the decision `prop:two-budget` opens with.  `𝒢(R)`
is the labelled class carrying the constraints node `[27]` has already imposed,
and `η(R) = log₂|𝒢(R)|/|R|`; the split asks `η(R) ≥ (1/d)·log₂ n`.

Exponentiating both sides by `d·|R|` turns that into `n^{|R|} ≤ |𝒢(R)|^d`, an
integer comparison, so no logarithm, division, or rounding is written.  The two
arms are the two halves of one excluded middle, so they are exhaustive and
mutually exclusive by construction, and the arm not taken is absent from the
taken branch's key index. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def remainderEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .forcedCurvatureCost) known]
    (highFresh : K .remainderEntropyHigh ∉ known)
    (lowFresh : K .remainderEntropyLow ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .remainderEntropyHigh) (K .remainderEntropyLow) previous :=
  -- Node `[49]` is asked of the residual carrying node `[48]`'s forced cost.
  let _cost := (@ExactLedger.get (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    current known previous (K .forcedCurvatureCost)).down
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .remainderEntropyHigh) (K .remainderEntropyLow)
    `Hypostructure.Graph.Strategy.Spine.remainderEntropyDichotomy
    (by
      classical
      -- `[50]` is asked of the remainder of the fixed maximum packing.
      let packing := canonicalWindowPacking data.toParameters current.object
      have valid : current.object.IsWindowPacking data.windowOrder packing :=
        (Classical.choose_spec
          (current.object.exists_windowPacking_card_eq data.windowOrder)).1
      by_cases high :
            Graph.AtLeastEntropyRate current.object.vertexCount
              data.entropyDenominator data.windowOrder data.threshold
              (current.object.positiveDeficiency
                (current.object.remainderSupport packing) data.threshold)
              (current.object.internalEdgeCount
                (current.object.remainderSupport packing))
              (current.object.remainderSupport packing).card
      · exact .inl ⟨⟨packing, rfl, valid, high⟩⟩
      · exact .inr ⟨⟨packing, rfl, valid,
          (Graph.not_atLeastEntropyRate_iff _ _ _ _ _ _ _).mp high⟩⟩)
    highFresh lowFresh

end Hypostructure.Graph.Strategy.Spine
