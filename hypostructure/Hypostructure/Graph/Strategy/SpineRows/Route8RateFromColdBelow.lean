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

/-! ## Nodes `[120]`--`[122]`, the private-carrier rate of the route-8 census

`rem:route8-carrier-margin`, `prop:typeA-route8-carrier-reduction`: the rate
`(δs+1)·|∂R| + δ·F·s·T(n) < δ·|R|` (`τ < 3/13` with the `o(|R|)` allowances of the
near-cubic spine).  On the `[147]` arm it is exactly `K .coldRoute8Below` read
through `|∂R| = e(R,W) ≤ stubs·p + σ_W ≤ stubs·p + T(n)`
(`lem:surplus-aware-window-stub`, `Route8.card_cutEdges_eq_boundaryIncidence`,
`σ_W ≤ σ(G) ≤ T(n)`).  On the other spine arms it is decided
(`route8RateDichotomy`): the density cap decides it only for sufficiently large
`n`, and the dense arm's `τ < 1/4` does not decide it at all — the manuscript's
delicate density interval (row 2 of `tab:cold-branch-ledger`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8RateFromColdBelowRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8RateFromColdBelow
    { Requires := [K .coldRoute8Below, K .surplusAtOrBelow]
      Produces := [K .route8Rate]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let below := (inputs.get (K .coldRoute8Below)).down
      let ceiling := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .route8Rate)
        (show Value BranchState Presentation presentation data
            .route8Rate inputs.current from
          ⟨by
            set object := inputs.current.object with hobj
            set packing := canonicalWindowPacking data object with hpack
            have valid : object.IsWindowPacking data.windowOrder packing :=
              (Classical.choose_spec
                (object.exists_windowPacking_card_eq data.windowOrder)).1
            have baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (object.minDegree_le_degree vertex)
            -- `lem:surplus-aware-window-stub`'s capacity link, read off the object
            -- (the same derivation node `[28]` publishes).
            have capacity := object.boundaryIncidence_add_internal_mass_le valid baseline
            have windowSurplus :
                object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
                    data.threshold ≤ data.surplusThreshold object.vertexCount :=
              le_trans (object.ambientSurplus_le_degreeSurplus _ data.threshold baseline)
                ceiling
            have supplyEq := Graph.Route8Census.card_supply object packing
            have remainder := object.remainderSupport_card_add_eq valid
            change (data.threshold * data.dischargeScale + 1) *
                (coldExternalStubCount data * packing.card +
                  data.surplusThreshold object.vertexCount) +
                data.threshold * (data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold object.vertexCount) <
              data.threshold * (object.vertexCount - data.windowOrder * packing.card) at below
            change (data.threshold * data.dischargeScale + 1) *
                (Graph.Route8Census.supply object packing).card +
                data.threshold * (data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold object.vertexCount) <
              data.threshold * (object.remainderSupport packing).card
            rw [supplyEq]
            have remEq : object.vertexCount - data.windowOrder * packing.card =
                (object.remainderSupport packing).card := by omega
            rw [remEq] at below
            have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
              have := data.three_le_threshold
              have := Nat.mul_le_mul_right data.windowOrder this
              omega
            have prod : coldExternalStubCount data * packing.card =
                data.threshold * (data.windowOrder * packing.card) -
                  2 * (data.windowOrder - 1) * packing.card := by
              simp only [coldExternalStubCount]
              rw [Nat.sub_mul, Nat.mul_assoc]
            have debit' : 2 * (data.windowOrder - 1) * packing.card ≤
                data.threshold * (data.windowOrder * packing.card) := by
              have := Nat.mul_le_mul_right packing.card debit
              rw [Nat.mul_assoc data.threshold] at this
              exact this
            have supplyLe : object.boundaryIncidence (object.remainderSupport packing) ≤
                coldExternalStubCount data * packing.card +
                  data.surplusThreshold object.vertexCount := by
              rw [prod]
              omega
            have := Nat.mul_le_mul_left (data.threshold * data.dischargeScale + 1) supplyLe
            omega⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
