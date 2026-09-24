import Hypostructure.Graph.Strategy.SpineVocabulary

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

/-! ## Node `[31]`: the curvature target-rank of the remainder

`def:exact-response-profile`, `def:admissible-rank-quotient`,
`def:functional-rank-quotient`, `def:curvature-target-rank`, at the atom
remainder `R` of every maximal packing.

* The declared raw curvature coordinates of `R` (clause (D4) of
  `def:declared-coordinate-signature`) are its internal length-two wedges,
  `𝒲₂(R)`; the profile is *exact* — "two distinct coordinate labels remain
  distinct entries even if their numerical values in the embedded graph
  coincide" — so the labelled family has exactly `W₂(R)` entries
  (`internalWedgeFamily_card`).
* An admissible rank quotient of that family (`remainderQuotient`, i.e.
  `Graph.CurvatureQuotient`) carries the connected determination support, the
  boundary-degree fibre and all-context target-completeness clauses of
  `def:target-complete-quotient`, and the two representative clauses of
  `def:admissible-rank-quotient`; a rank-reducing one is therefore represented
  by a strictly smaller proper representative or a strictly smaller admissible
  closed representative (`DeclaredQuotient.localize`).  That routing is
  published at the definition's own generality — every declared family on every
  connected support carrying it — because `DeclaredQuotient.localize` is stated
  there and the manuscript applies the definition well outside the remainder;
  the raw curvature reading this row needs is one instance.
* The admissible quotient system used to compute target rank consists of the
  admissible quotients that are functional on the family
  (`RankQuotient.FunctionalOn`); a subfamily survives it when every such
  quotient is label-injective on it, and `r_Ω(R)` is the maximum size of a
  surviving subfamily — attained, and an upper bound for every surviving
  subfamily (`exists_attaining_curvatureTargetRank`,
  `card_le_curvatureTargetRank`).

This is the quotient-system obstruction rank of
`def:curvature-target-rank`.  It does not assert that a surviving family
realizes every Boolean target-response assignment, nor does it apply
`lem:independent-target-entropy`: the manuscript identifies quotient survival
with the full target code only on the surviving hot residual entering node
`[47]`.  Publishing either conclusion here would add a fact to node `[31]`
that the paper does not yet provide.

The row is run after the remainder has been fixed, but these three facts are
definitions and finite attainment facts about the literal active object.  None
of their proofs uses the induced-window or internal-core conclusions of nodes
`[25]`--`[27]`.  Its manifest therefore has `Requires := []`: chronology comes
from passing the same `ExactLedger` to this row, not from declaring and
discarding an unrelated semantic prerequisite.  `lem:target-rank-circuit` is
the next row. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def curvatureTargetRankRow :
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
    `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank
    { Requires := []
      Produces := [K .exactResponseProfile, K .admissibleRankQuotient,
        K .curvatureTargetRank]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .exactResponseProfile)
        (show Value BranchState Presentation presentation data
            .exactResponseProfile inputs.current from
          ⟨fun packing _valid _card =>
            Graph.FiniteObject.internalWedgeFamily_card inputs.current.object
              (inputs.current.object.remainderSupport packing)⟩)
        (.cons (key := K .admissibleRankQuotient)
          (show Value BranchState Presentation presentation data
              .admissibleRankQuotient inputs.current from
            ⟨fun _Coordinate _family _coordinateSupport quotient reducing =>
              quotient.localize reducing⟩)
          (.cons (key := K .curvatureTargetRank)
            (show Value BranchState Presentation presentation data
                .curvatureTargetRank inputs.current from
              ⟨fun packing _valid _card =>
                ⟨Graph.FiniteObject.exists_attaining_curvatureTargetRank
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                    (inputs.current.object.remainderSupport packing),
                  fun _candidate subset survives =>
                    Graph.FiniteObject.card_le_curvatureTargetRank
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                      (inputs.current.object.remainderSupport packing) subset survives⟩⟩)
            .nil)))
    0 0

end Hypostructure.Graph.Strategy.Spine
