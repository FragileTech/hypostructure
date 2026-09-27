import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdGermRouting

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy

On the absorbed-configuration residual every selected branch-excess half-edge
`ε` of an ambient-cubic cold window has a return corridor (`lem:bridgeless`)
and a first-failure exchange germ; the lemma's dichotomy is *per half-edge*,
by whether the germ's support `J` meets a vertex above the threshold.  Case
(i): `J` is subcubic, so `ε`'s germ is a candidate of `lem:cold-germ-extraction`
and is charged in full.  Case (ii): `J` contains a vertex `z` above the
threshold; node `[10]` (`K .slackIndependent`) makes every neighbour of `z`
sit exactly at the threshold, so `z` is a heavy centre.  The row publishes
that dichotomy for every selected half-edge, on the literal residual; the
exhaustive object-level decision that follows (`absorbedGermDichotomy`) only
chooses which continuation closes the branch. -/
@[reducible] noncomputable def absorbedGermSplitRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermSplit
    { Requires := [K .coldGermCandidates, K .coldHandoffTransfer,
        K .slackIndependent]
      Produces := [K .absorbedGermSplit]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .absorbedGermSplit)
        ⟨Contracts.Spine.absorbedGermSplit_of_handoff data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .coldGermCandidates)).down
          (inputs.get (K .coldHandoffTransfer)).down
          (inputs.get (K .slackIndependent)).down⟩
        .nil)

/-! ## Nodes `[174]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ split

On the absorbed-germ residual (`[173]`'s no arm), node `[175]` asks whether a
selected corridor avoids the high-degree vertices, i.e. whether the literal
case-(i) occurrence class is nonempty.  The yes arm records exactly that
predicate as `K .coldPositiveGerm`; the no arm is its exact negation
`K .coldNoPositiveGerm`: every selected corridor meets a high-degree vertex.
Independently of the test, `absorbedGermSplitRow` retains the per-half-edge
case-(i)/(ii) dichotomy, and `absorbedGermFanDataRow` publishes the case-(ii)
fan data for every occurrence outside the candidate set on both arms, so mixed
families continue through both paper routes. -/
noncomputable def absorbedGermDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .absorbedGermSplit) known]
    (positiveFresh : K .coldPositiveGerm ∉ known)
    (emptyFresh : K .coldNoPositiveGerm ∉ known) :
    Decision (K .coldPositiveGerm) (K .coldNoPositiveGerm) previous := by
  classical
  exact Decision.run previous (K .coldPositiveGerm) (K .coldNoPositiveGerm)
    `Hypostructure.Graph.Strategy.Spine.absorbedGermDichotomy
    (if positive : ColdPositiveGermStatement data.toParameters current.object then
      .inl ⟨positive⟩
    else
      .inr ⟨positive⟩)
    positiveFresh emptyFresh

/-- Node `[177]`: the per-incidence split of `[175]` supplies the least-high
witness on the complement of node `[153]`'s routed candidate set.  The
candidate/loss accounting stays node `[153]`'s own ledger fact
(`K .coldGermCandidates`, at its canonical extraction); it is not copied here.
It is run before the decorated-envelope owner. -/
@[reducible] noncomputable def absorbedGermFanDataRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanData
    { Requires := [K .absorbedGermSplit]
      Produces := [K .absorbedGermFanData]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .absorbedGermFanData)
        ⟨Contracts.Spine.absorbedGermFanData_of_split data.toParameters
          inputs.current.object (inputs.get (K .absorbedGermSplit)).down⟩
        .nil)

/-- Node `[176]`: the positive class chosen at `[175]` is the exact candidate
set inside node `[153]`'s retained extraction.  Hence the already-published
greedy extraction theorem makes that same disjoint family nonempty. -/
@[reducible] noncomputable def absorbedGermFamilyPositiveRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFamilyPositive
    { Requires := [K .coldPositiveGerm, K .coldGermCandidates]
      Produces := [K .coldGermFamilyPositive]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldGermFamilyPositive)
        ⟨Contracts.Spine.coldGermFamilyPositive_of_positiveGerm data.toParameters
          inputs.current.object (inputs.get (K .coldPositiveGerm)).down
          (inputs.get (K .coldGermCandidates)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
