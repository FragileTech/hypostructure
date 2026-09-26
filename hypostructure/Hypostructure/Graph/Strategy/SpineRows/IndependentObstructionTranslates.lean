import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.DominantType

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

/-! ## Nodes `[51]`--`[52]`: independent obstruction translates

`lem:translates-independent` is not an entropy inequality.  On the literal
full-rank remainder, a dominant rooted radius-`r` type containing an internal
root wedge supplies a translated raw wedge at every dominant centre.  Choose a
maximum `2r`-separated set of those centres.  Maximality covers the dominant set
by radius-`2r` balls; the radius-`r` balls are pairwise disjoint; and
`SubcubicReach.card_reach_le` gives the manuscript's exact bound
`b' = 1 + 3(2^(2r)-1)`.  Distinct centres give distinct raw wedge labels, and
the full-rank equality carried by the dominant-wedge fact identifies their
supply with `r_Ω(R)`.  The row is a thin adapter for
`Contracts.Spine.independentObstructionTranslates_of_dominantRootedWedgeType`.

The committed statement is the division-free finite form
`|R| ≤ b'·r_Ω(R) + T(n)`, where the already registered near-cubic
threshold `T(n)` is the finite representative of the manuscript's `o(|R|)`
set.  No unbounded existential error is admitted. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def independentObstructionTranslatesRow :
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
    `Hypostructure.Graph.Strategy.Spine.independentObstructionTranslates
    { Requires := [K .dominantRootedWedgeType]
      Produces := [K .independentObstructionTranslates]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .independentObstructionTranslates)
        ⟨Contracts.Spine.independentObstructionTranslates_of_dominantRootedWedgeType
          data.toParameters inputs.current.object data.threshold_eq_three
          (inputs.get (K .dominantRootedWedgeType)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
