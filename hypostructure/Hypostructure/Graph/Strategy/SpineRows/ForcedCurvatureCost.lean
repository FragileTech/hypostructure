import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.RemainderEntropy

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
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .forcedCurvatureCost)
        ⟨Contracts.Spine.forcedCurvatureCost_of_fullRank data.toParameters
          inputs.current.object (inputs.get (K .wedgeSupply)).down
          (inputs.get (K .curvatureFullRank)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
