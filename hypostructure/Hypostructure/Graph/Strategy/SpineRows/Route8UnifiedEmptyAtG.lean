import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.UnifiedDeficit

/-!
# Node `[123]` stated about G: the quotient-free arm is empty

Lean improvement (G repair).  Read in G's own surroundings `G − B_u`, every
carrier set of a graph-owned route-`8` entry is target-complete, so its
essential core is empty and `α(ξ) = 0`.  On the quotient-free arm of the
unified ledger the census publishes `2 ≤ α(ξ)` at every unified entry
(`lem:typeA-unified-carriers`), so there is no unified entry; the stage
accounting of the node-`[123]` descent clears the unified deficit, and
`lem:typeA-unified-deficit` leaves `|R| ≤ s·|∂R| + F·s·T(n)`, which the
private-carrier rate `K .route8Rate` refutes.  The row publishes the fact; the
closure is the framework's `Incompatible` against the rate.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[123]`, stated about G**: the unified entry family is empty and the
unified deficit is cleared (`Route8UnifiedEmptyAtGStatement`). -/
@[reducible] noncomputable def route8UnifiedEmptyAtGRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedEmptyAtG
    { Requires := [K .route8UnifiedEntryCensus, K .selection,
        K .route8PeelingDescent, K .route8UnifiedDeficit]
      Produces := [K .route8UnifiedEmptyAtG]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedEmptyAtG)
        ⟨Graph.Contracts.RouteEight.route8UnifiedEmptyAtG data.toParameters
          inputs.current.object
          (inputs.get (K .route8UnifiedEntryCensus)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .route8PeelingDescent)).down
          (inputs.get (K .route8UnifiedDeficit)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[123]`, stated about G, closed**: the private-carrier rate
`(δ·s + 1)·|∂R| + δ·F·s·T(n) < δ·|R|` against `|R| ≤ s·|∂R| + F·s·T(n)`.
Lean improvement: the quotient-free arm of `[348]` is empty at G. -/
noncomputable instance instIncompatibleRoute8RateUnifiedEmptyAtG :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8Rate) (K .route8UnifiedEmptyAtG) where
  contradiction := fun input rate empty =>
    Graph.Contracts.RouteEight.route8UnifiedEmptyAtG_contradiction
      data.toParameters input.object rate.down empty.down

end Hypostructure.Graph.Strategy.Spine
