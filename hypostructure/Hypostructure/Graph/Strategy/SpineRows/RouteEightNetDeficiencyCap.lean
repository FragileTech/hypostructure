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

/-! ## Node `[56]`, the large-budget net-deficiency cap (route-8 arm).

On the `[147]` arm the strict cap of `prop:negative-net-charge` is read from
`K .coldRoute8Below` -- the route-8 carrier inequality `τ(θ) < 3/13 < 1/4` in
its exact form `(δs+1)·(stubs·p + T(n)) + δ·F·s·T(n) < δ·(n − order·p)` -- rather
than from the density cap; it implies the cap
`s·(δ·order·p + T(n)) < s·2(order−1)·p + |R|` outright, with the surplus
allowance already inside the route-8 inequality. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def routeEightNetDeficiencyCapRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.routeEightNetDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .coldRoute8Below]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _residual := (inputs.get (K .largeBudgetResidual)).down
      let below := (inputs.get (K .coldRoute8Below)).down
      .cons (key := K .netDeficiencyCap)
        (show Value BranchState Presentation presentation data
            .netDeficiencyCap inputs.current from
          ⟨by
            intro packing valid cardinality _large
            have canonicalCard :
                (canonicalWindowPacking data inputs.current.object).card =
                  inputs.current.object.windowPackingNumber data.windowOrder :=
              (Classical.choose_spec
                (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)).2
            change (data.threshold * data.dischargeScale + 1) *
                (coldExternalStubCount data *
                  (canonicalWindowPacking data inputs.current.object).card +
                  data.surplusThreshold inputs.current.object.vertexCount) +
                data.threshold * (data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold inputs.current.object.vertexCount) <
              data.threshold * (inputs.current.object.vertexCount -
                data.windowOrder * (canonicalWindowPacking data inputs.current.object).card)
              at below
            rw [canonicalCard, ← cardinality] at below
            have cardinality' :
                (inputs.current.object.remainderSupport packing).card +
                    data.windowOrder * packing.card =
                  inputs.current.object.vertexCount :=
              inputs.current.object.remainderSupport_card_add_eq valid
            have remEq : inputs.current.object.vertexCount -
                data.windowOrder * packing.card =
                (inputs.current.object.remainderSupport packing).card := by omega
            have three := data.threshold_eq_three
            simp only [coldExternalStubCount, Data.surplusThreshold] at below ⊢
            rw [three, remEq] at below
            rw [three]
            obtain ⟨o, ho⟩ : ∃ o, data.windowOrder = o + 1 :=
              ⟨data.windowOrder - 1, by have := data.windowOrder_pos; omega⟩
            rw [ho] at below ⊢
            have stubsEq : 3 * (o + 1) - 2 * (o + 1 - 1) = o + 3 := by omega
            rw [stubsEq] at below
            simp only [Nat.add_sub_cancel] at below ⊢
            nlinarith [below, Nat.zero_le ((o + 3) * packing.card),
              Nat.zero_le (data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount),
              Nat.zero_le (data.bridgeMassFactor * data.dischargeScale *
                (data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount))]⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
