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

/-! ## Node `[61]`: the selected connected negative support

`prop:negative-net-charge`.  The negative arm of node `[59]` already contains
the canonical maximal packing and its negative remainder.  Node `[57]`--`[58]`
localizes that charge through the canonical component decomposition.  This row
reads exactly those two facts and appends only the selected connected negative
piece and its containment in the same remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def negativeSupportRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.negativeSupport
    { Requires := [K .netChargeNegative, K .netChargeLocalization]
      Produces := [K .negativeSupport]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .negativeSupport)
        (show Value BranchState Presentation presentation data
            .negativeSupport inputs.current from ⟨by
          let negativeFact := (inputs.get (K .netChargeNegative)).down
          let packing := Classical.choose negativeFact
          have packingSpec := Classical.choose_spec negativeFact
          have canonical := packingSpec.1
          have valid := packingSpec.2.1
          have maximal := packingSpec.2.2.2.1
          have negative := packingSpec.2.2.2.2
          obtain ⟨component, present, charge⟩ :=
            (inputs.get (K .netChargeLocalization)).down packing valid negative
          exact ⟨packing, canonical, valid, maximal, component, present, charge⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
