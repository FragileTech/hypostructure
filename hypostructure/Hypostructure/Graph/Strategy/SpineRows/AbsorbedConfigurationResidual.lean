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

/-! ## Node `[174]`: the absorbed-configuration residual

`lem:exact-collision-test`, the failure consequence.  At the failure witness
packing `P` of `[173]` the remainder has nonnegative net charge,
`|R| + s·σ_R ≤ s·def⁺(R)`.  The manuscript's stub supply of node `[29]` is
exact on the object — `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`,
which is `K .boundaryDemand` (not `K .stubSupply`, whose allowance is the
scale threshold `T(n)` rather than `σ_W`) — and `|R| + order·p = n`.  With
`p = |𝒫_hot| + |𝒫_cold|` from the hot/cold ledger, the failed collision
rearranges to the manuscript's `C ≥ (n − 73|𝒫_hot| − 4(σ_W − σ_R))/73`,
published subtraction-free as
`n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W` with `A = netChargeCoefficient`,
the registered `s·(δ·order − 2(order−1)) + order`.  The residual's position on
the bounded arm of `[153]` is the ledger fact `K .coldMassBounded` where that
node ran; the row publishes only the arithmetic the lemma derives. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def absorbedConfigurationResidualRow :
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
    `Hypostructure.Graph.Strategy.Spine.absorbedConfigurationResidual
    { Requires :=
        [K .exactCollisionFails, K .boundaryDemand, K .hotColdPartition]
      Produces := [K .absorbedConfigurationResidual]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fails := (inputs.get (K .exactCollisionFails)).down
      let demand := (inputs.get (K .boundaryDemand)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .absorbedConfigurationResidual)
        (show Value BranchState Presentation presentation data
            .absorbedConfigurationResidual inputs.current from
          ⟨by
            classical
            obtain ⟨packing, valid, cardinality, nonneg⟩ := fails
            refine ⟨packing, valid, cardinality, nonneg, ?_⟩
            obtain ⟨deficiencyLe, incidenceLe⟩ := demand packing valid
            have sizes := inputs.current.object.remainderSupport_card_add_eq valid
            obtain ⟨_, canonicalCard, _, _, _, disjoint, cover⟩ := split
            -- `p = |𝒫_hot| + |𝒫_cold|`: the fixed packing is the disjoint union.
            have union :
                canonicalWindowPacking data inputs.current.object =
                  canonicalHotWindows data inputs.current.object ∪
                    canonicalColdWindows data inputs.current.object := by
              ext window
              simp only [Finset.mem_union]
              exact cover window
            have countEq :
                packing.card =
                  (canonicalHotWindows data inputs.current.object).card +
                    (canonicalColdWindows data inputs.current.object).card := by
              rw [cardinality, ← canonicalCard, union,
                Finset.card_union_of_disjoint disjoint]
            rw [← countEq]
            unfold Graph.FiniteObject.NonNegativeNetCharge at nonneg
            unfold Data.netChargeCoefficient
            -- `e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`, in both truncation cases.
            have assoc :
                data.threshold * data.windowOrder * packing.card =
                  data.threshold * (data.windowOrder * packing.card) :=
              Nat.mul_assoc _ _ _
            have supply :
                inputs.current.object.boundaryIncidence
                    (inputs.current.object.remainderSupport packing) ≤
                  (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) *
                      packing.card +
                    inputs.current.object.ambientSurplus
                      (Graph.FiniteObject.windowSupport packing) data.threshold := by
              rcases Nat.le_total (2 * (data.windowOrder - 1))
                  (data.threshold * data.windowOrder) with small | large
              · have recombine :
                    (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) *
                        packing.card +
                      2 * (data.windowOrder - 1) * packing.card =
                      data.threshold * data.windowOrder * packing.card := by
                  rw [← Nat.add_mul, Nat.sub_add_cancel small]
                omega
              · rw [Nat.sub_eq_zero_of_le large, Nat.zero_mul, Nat.zero_add]
                have := Nat.mul_le_mul_right packing.card large
                omega
            have scaledDeficiency := Nat.mul_le_mul_left data.dischargeScale deficiencyLe
            have scaledSupply := Nat.mul_le_mul_left data.dischargeScale supply
            rw [Nat.mul_add] at scaledSupply
            rw [Nat.add_mul, Nat.mul_assoc]
            omega⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
