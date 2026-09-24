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

/-! ## Node `[59]`: the net-charge sign test

`N₀(R) ≥ 0?`  Here `R` is the complement of the one maximum packing selected
at node `[27]`, not a quantifier over every maximal packing.  The executor reads
that witness from `K .maximalPacking`, decides its exact integer charge, and
carries the same packing in either branch fact.  The yes arm is the manuscript's
node `[60]`; the no arm is node `[61]`, where a connected negative support is
selected.  The decision itself does not close `[60]`: that terminal additionally
uses the strict net-cap estimate of `prop:negative-net-charge`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def netChargeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .maximalPacking) known]
    (nonNegativeFresh : K .netChargeNonNegative ∉ known)
    (negativeFresh : K .netChargeNegative ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .netChargeNonNegative) (K .netChargeNegative) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .netChargeNonNegative) (K .netChargeNegative)
    `Hypostructure.Graph.Strategy.Spine.netChargeDichotomy
    (by
      classical
      have selected :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .maximalPacking)).down
      let packing := canonicalWindowPacking data current.object
      have packingSpec := Classical.choose_spec
        (current.object.exists_windowPacking_card_eq data.windowOrder)
      have valid := packingSpec.1
      have cardinality := packingSpec.2
      have maximal : ∀ window : Finset current.object.Vertex,
          current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member :=
        fun window windowMem =>
          current.object.exists_mem_not_disjoint_of_card_eq
            data.windowOrder_pos valid cardinality windowMem
      by_cases nonNegative : current.object.NonNegativeNetCharge
          (current.object.remainderSupport packing) data.threshold
          data.dischargeScale
      · exact .inl ⟨packing, rfl, valid, cardinality, maximal, nonNegative⟩
      · exact .inr ⟨packing, rfl, valid, cardinality, maximal,
          Nat.lt_of_not_le nonNegative⟩)
    nonNegativeFresh negativeFresh

end Hypostructure.Graph.Strategy.Spine
