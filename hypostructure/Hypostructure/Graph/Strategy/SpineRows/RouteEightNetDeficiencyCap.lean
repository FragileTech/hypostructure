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
    { Requires := [K .largeBudgetResidual, K .coldRoute8Below, K .cubicBaseline]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- `[55]` → `[56]`: the Residual C ledger fact is this node's predecessor.
      let _residualC := (inputs.get (K .largeBudgetResidual)).down
      .cons (key := K .netDeficiencyCap)
        ⟨Contracts.Spine.netDeficiencyCap_of_coldRoute8Below data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .coldRoute8Below)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
