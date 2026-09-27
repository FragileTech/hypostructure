import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineRemainder

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

/-! ## Node `[30]`: the wedge lower bound

`lem:wedge-lower`.  A region `X` of the remainder carries
`W₂(X) = Σ_{v∈X} C(d_X(v), 2)` internal length-two wedges -- a wedge being a
choice of two distinct neighbours of a common centre inside `X` -- and the
manuscript's degree count bounds that below by the region's own size:

  `W₂(X) ≥ δ|X| − 2 def⁺(X)`,

committed subtraction-free.  The manuscript states it for a component `C` of
`R` and then sums over the components of `R`, using that `d_C = d_R` inside a
component.  The count is pointwise, so
`Graph.FiniteObject.baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency`
holds at *every* region, and both of the lemma's displayed inequalities are
instances of it: the componentwise one at a component, its sum at `R` itself.
No component decomposition is built, and none is needed to connect them.

The node exists for its "in particular", and that is the second clause.
Substituting the boundary-demand ceiling of nodes `[28]`--`[29]` for `def⁺(R)`
turns the bound into the demand floor of the final collision -- invariant 28 --
which is why this row consumes `stubSupply`: the manuscript's own
`Requires` cell for `[30]` names `cor:stub-boundary-supply`.  Where the
manuscript substitutes the asymptotic `def⁺(R) ≤ (τ_win + o(1))|R|`, the row
substitutes the exact inequality the ledger actually carries, and the two
doubled terms of the conclusion are literally twice that inequality's two
sides.

`3 ≤ δ` is spent here a second time and for an unrelated reason: the skeleton
budget needed it as Stirling's `⌈e⌉`, and the wedge count needs it because a
vertex sitting exactly at the baseline contributes only `C(δ,2)`.
`baseline_one_insufficient` and `baseline_two_insufficient` prove it is the
exact threshold rather than a constant copied from a manuscript. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def wedgeSupplyRow :
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
    `Hypostructure.Graph.Strategy.Spine.wedgeSupply
    { Requires := [K .stubSupply, K .cubicBaseline]
      Produces := [K .wedgeSupply]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .wedgeSupply)
        ⟨Contracts.Spine.wedgeSupply_of_stubSupply data.toParameters
          inputs.current.object (Nat.le_of_eq (inputs.get (K .cubicBaseline)).down.1.symm)
          (inputs.get (K .stubSupply)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
