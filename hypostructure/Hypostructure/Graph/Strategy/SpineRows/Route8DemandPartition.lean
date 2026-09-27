import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.DemandLedger

/-!
# The exit-(4) demand ledger at the failed-rate stage of node `[123]`

`def:typeA-pressure-ledger` on the unified collection, run at the failed
reduced-rate stage of `thm:large-budget-route8-only` on the way to node
`[181]`.  Clause (L1) pins every minimal entry with `δ` private essential
incidences; the manuscript runs the ledger unconditionally at this stage.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The maximal pinned `2/3`-demand ledger with its no-overcount inequalities
and the canonical demand records of the unpaid target-defect entries. -/
@[reducible] noncomputable def route8DemandLedgerRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8DemandLedger
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .route8DemandLedger]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8DemandLedger)
        ⟨Graph.Contracts.RouteEight.route8DemandLedger data.toParameters
          inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.1; omega)
          (inputs.get (K .selection)).down.1⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
