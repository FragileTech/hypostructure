import Hypostructure.Graph.Strategy.SpineRows.Basic
import Hypostructure.Graph.Contracts.Spine.SpineSelection

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

/-! ## `lem:cycle-rank`: the selected graph's rank lower bound

The manuscript defines `β(G) = m - n + 1` and proves
`β(G) ≥ n/2 + 1` from the handshake inequality `3n ≤ 2m`.  The ExactLedger
stores the division-free Nat statement `n + 2 ≤ 2β(G)`.  Its only input is
the active residual's registered minimum-degree baseline; no earlier proof is
reopened and no numerical graph data are supplied separately. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def cycleRankConstraintRow :
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
    `Hypostructure.Graph.Strategy.Spine.cycleRankConstraint
    { Requires := [K .cubicBaseline]
      Produces := [K .cycleRankConstraint]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .cycleRankConstraint)
        ⟨Contracts.Spine.cycleRankConstraint_of_baseline data.toParameters
          inputs.current.object inputs.current.baseline
          (Nat.le_of_eq (inputs.get (K .cubicBaseline)).down.1.symm)⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
