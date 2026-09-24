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

/-! ## Nodes `[47]`--`[48]`: the forced curvature cost

`cor:forced-curvature-cost`, whose proof invokes `lem:full-rank` and
`lem:wedge-lower`.  Both are already ledger facts on this branch: the exact
full rank `r_Ω(R) = W₂(R)` of node `[34]` and the demand floor of node `[30]`
(`K .wedgeSupply`'s "in particular").  The row substitutes the equality into
the floor and applies the registered cost to both sides.

The registered cost is the *only* thing this row reads that is not on the
branch, and `rem:closure-robust` records that the closure outside the explicit
residuals holds for every nonnegative value of it. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def forcedCurvatureCostRow :
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
    `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost
    { Requires := [K .wedgeSupply, K .curvatureFullRank]
      Produces := [K .forcedCurvatureCost]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- `lem:wedge-lower`'s "in particular": node `[30]`'s demand floor.
      let floor := (inputs.get (K .wedgeSupply)).down.2
      let rank := (inputs.get (K .curvatureFullRank)).down
      .cons (key := K .forcedCurvatureCost)
        (show Value BranchState Presentation presentation data
            .forcedCurvatureCost inputs.current from ⟨by
          rcases rank with ⟨packing, valid, maximal, rankEq⟩
          refine ⟨packing, valid, maximal, ?_⟩
          have demand := floor packing valid
          -- `W₂(R) ≤ r_Ω(R)`, from the exact full-rank ledger fact.
          have supply :
              remainderWedgeSupply inputs.current.object packing ≤
                remainderCurvatureTargetRank data inputs.current.object packing :=
            rankEq.ge
          calc data.curvatureCost *
                (data.threshold *
                    (inputs.current.object.remainderSupport packing).card +
                  2 * (2 * (data.windowOrder - 1) * packing.card))
              ≤ data.curvatureCost *
                  (remainderCurvatureTargetRank data inputs.current.object
                        packing +
                    2 * (data.threshold * (data.windowOrder * packing.card) +
                      data.surplusThreshold inputs.current.object.vertexCount)) :=
                Nat.mul_le_mul_left _
                  (le_trans demand (Nat.add_le_add_right supply _))
            _ = _ := by ring⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
