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

/-! ## Node `[8]`: no proper subgraph satisfies the baseline

`lem:no-proper-core`.  A proper subgraph is strictly smaller in the registered
order, so minimality forces it to have an accepted cycle; but every cycle of a
proper subgraph is a cycle of the ambient graph
(`Graph.cycleProperSubgraphTargetMonotone`), which the selected object does not
have.  So no proper subgraph satisfies the baseline. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def noProperBaselineRow :
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
    `Hypostructure.Graph.Strategy.Spine.noProperBaseline
    { Requires := [K .selection]
      Produces := [K .noProperBaseline]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fact := inputs.get (K .selection)
      let noProper : ∀ subgraph : Graph.ProperSubgraph inputs.current.object,
          ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value :=
        fun subgraph baseline =>
          fact.down.1
            ((Graph.cycleProperSubgraphTargetMonotone data.LengthOK).map subgraph
              (fact.down.2 subgraph.value subgraph.decreases baseline))
      .cons (key := K .noProperBaseline)
        (show Value BranchState Presentation presentation data
            .noProperBaseline inputs.current from
          ⟨noProper,
            inputs.current.object.connected_of_noProperBaseline data.threshold
              (lt_of_lt_of_le (by omega) data.three_le_threshold)
              inputs.current.baseline noProper⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
