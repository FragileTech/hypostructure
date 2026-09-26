import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.NetCharge

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
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .absorbedConfigurationResidual)
        ⟨Contracts.Spine.absorbedConfigurationResidual_of_exactCollisionFails
          data.toParameters inputs.current.object
          (inputs.get (K .exactCollisionFails)).down
          (inputs.get (K .boundaryDemand)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
