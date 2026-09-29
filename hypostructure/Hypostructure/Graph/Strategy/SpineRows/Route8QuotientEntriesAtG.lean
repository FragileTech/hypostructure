import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.QuotientSize

/-!
# Node `[348]` stated about G: the quotient test is decided at G

Lean improvement (G audit of `Route8QuotientOutcome`).  Alternative (b) of
`def:typeA-trace-basin`, read in G's own surroundings `G − B_u`, is present at
every routed load of G (forgetting every declared coordinate is a nontrivial
target-complete quotient), so the failure of quotient freeness is exactly the
non-emptiness of the unified entry family.  The manuscript's step "(b) implies
exit `(5)`" needs a strictly smaller representative; at G none exists: the
canonical representative of G's piece at `B_u` has the size of the piece (the
minimality of G), and `cor:uncompressible` excludes the exit-`(5)` datum.  The
row publishes these facts at every unified entry from G's selection (target
avoidance and minimality) and the uncompressibility of G, and, from the stage
accounting of the descent, the unified deficit and the private-carrier rate,
the inequality `|∂R| < δ·|\\tilde\\Xi|` that the entry family carries.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[348]`, stated about G** (`Route8QuotientEntriesAtGStatement`). -/
@[reducible] noncomputable def route8QuotientEntriesAtGRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8QuotientEntriesAtG
    { Requires := [K .selection, K .uncompressible, K .route8PeelingDescent,
        K .route8UnifiedDeficit, K .route8Rate]
      Produces := [K .route8QuotientEntriesAtG]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8QuotientEntriesAtG)
        ⟨Graph.Contracts.RouteEight.route8QuotientEntriesAtG data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .selection)).down.1
          (inputs.get (K .selection)).down.2
          (inputs.get (K .uncompressible)).down
          (inputs.get (K .route8PeelingDescent)).down
          (inputs.get (K .route8UnifiedDeficit)).down
          (inputs.get (K .route8Rate)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
