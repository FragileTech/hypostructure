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

/-! ## Node `[24]`: `prop:p13-density`, after the cold branch closes

The manuscript's `[24]` reads "bounded cold-mass return from [153]:
`θ ≤ θ_win + o(1)`; high entropy: `θ ≤ 0.01198542083…`".  The finite density cap `K .densityCap` is
produced after the cold branch has closed on the literal residual.  Its
consumers require that exact ledger fact. -/

/-! ## Nodes `[25]`--`[27]`: the packed-window remainder

`sec:remainder`.  With `W` the union of a maximal packing and `R = G − W`, the
manuscript asserts that `R` carries no induced window -- "since any such copy
would extend `𝒫`" -- and that no subgraph of `R` has minimum degree at least the
baseline.  The second is the cited external law applied at its own interface:
the induced closure of such a subgraph is still window-free, so it has an
accepted cycle, and a cycle of an induced subgraph is a cycle of the selected
object, which avoids the target.

The row is stated at the remainder `R₀` of G's fixed packing `P₀`.  It reads
`selection` (the avoidance half) and the cited closure law at G's induced
subgraphs from `K .cubicBaseline`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def remainderNormalizationRow :
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
    `Hypostructure.Graph.Strategy.Spine.remainderNormalization
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .remainderNormalized]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .remainderNormalized)
        ⟨Contracts.Spine.remainderNormalized_of_selection data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.2.2.2.2.1
          (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
