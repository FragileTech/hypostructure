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

/-- **Node `[160]`, `lem:dense-deficiency-routing`, first comparison**: on the
dense-packing residual `[159]`, decide the exact `τ(θ) < 1/4` deficiency test of
node `[56]` (`K .denseDeficiencyBelow`) against its exact complement
(`K .denseDeficiencyAtOrAbove`).  The second comparison of `[160]`, the
private-carrier rate, is `route8RateDichotomy` on the yes-arm only. -/
noncomputable def denseDeficiencyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (belowFresh : K .denseDeficiencyBelow ∉ known)
    (atOrAboveFresh : K .denseDeficiencyAtOrAbove ∉ known) :
    Decision (K .denseDeficiencyBelow) (K .denseDeficiencyAtOrAbove) previous := by
  classical
  exact Decision.run previous (K .denseDeficiencyBelow) (K .denseDeficiencyAtOrAbove)
    `Hypostructure.Graph.Strategy.Spine.denseDeficiencyDichotomy
    (if below : DenseDeficiencyBelowStatement data.toParameters current.object then
      .inl ⟨below⟩
    else
      .inr ⟨below⟩)
    belowFresh atOrAboveFresh

/-- **`[146]` yes on `[160]`'s first complement** (`lem:dense-cold-pass`,
`def:cold-window-ledger`): the dense hot/cold pass `[162]` runs `[146]` on the
arm that retains `τ(θ) ≥ 1/4`, and `θ < 1/78` gives `τ(θ) < 3/13 < 1/4`
(`Contracts.Spine.denseDeficiencyBelow_of_coldRoute8Below`), the literal
negation of the retained failure; Core closes the pair. -/
noncomputable instance instIncompatibleDenseDeficiencyAtOrAboveColdRoute8Below :
    Incompatible (Input BranchState Presentation presentation data)
      (K .denseDeficiencyAtOrAbove) (K .coldRoute8Below) where
  contradiction := fun residual atOrAbove below =>
    atOrAbove.down (Contracts.Spine.denseDeficiencyBelow_of_coldRoute8Below
      data.toParameters residual.object below.down)

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[56]`, the large-budget net-deficiency cap (dense arm).

On the `[21]` unrealized residual the manuscript's `τ(θ) < 1/4` reading of
`prop:negative-net-charge` is a decision of its own (`K .denseDeficiencyBelow`,
the exact strict comparison at the fixed maximal packing); this row is node
`[56]` on its yes arm: the same conditional cap for every maximal packing, read
off that decision (all maximal packings have the same size and the same
remainder count `n − order·p`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def denseNetDeficiencyCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.denseNetDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .denseDeficiencyBelow]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- `[55]` → `[56]`: the Residual C ledger fact is this node's predecessor.
      let _residualC := (inputs.get (K .largeBudgetResidual)).down
      .cons (key := K .netDeficiencyCap)
        ⟨Contracts.Spine.netDeficiencyCap_of_denseDeficiencyBelow data.toParameters
          inputs.current.object (inputs.get (K .denseDeficiencyBelow)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
