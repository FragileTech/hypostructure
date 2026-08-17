import Hypostructure.Graph.Strategy.SpineRows

/-!
# Node `[54]`: the entropy cap closes

`prop:entropy-high-theta`: on the arm where the remaining non-curvature budget
is strictly smaller than the forced curvature cost (`K .entropyCapActive`,
`eq:entropy-cap`), *"the window package of `lem:p13-window-package`, the
remainder bits, and the forced-curvature bits together strictly exceed the
near-cubic skeleton budget.  These bits form one independently target-testable
coordinate family, so the number of realized target-complete states would
exceed the number of labelled skeletons, contradicting
`lem:independent-target-entropy`, `lem:skeleton-dominates`."*

The premise "form one independently target-testable coordinate family" is
`def:target-rank`'s realization of the joint code by the labelled skeletons of
the current class — the exact-code equality `def:curvature-target-rank` says is
retained on the surviving hot residual entering node `[47]`, "its failure
[being] the complementary cold residual".  The framework asks that exact
question on the literal `[53]` residual: `jointCodeDichotomy` commits either
`K .jointCodeRealized` (the joint demand is realized by an assignment of states
to skeletons) or its exact complement `K .jointCodeUnrealized`.  On the
realized arm the terminal is a plain contradiction of three ledger facts:
`K .entropyCapActive` (`budget < demand`), `K .jointCodeRealized`
(`demand ≤ #realized states`) and `K .skeletonDominates`
(`#realized states ≤ budget`).  No numeral, threshold or rate is written here.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[54]`'s exact question on the `[53]` yes-residual**: is the joint
code of the entropy comparison realized by the labelled skeletons of the
current class (`def:target-rank`, `lem:independent-target-entropy`)? -/
noncomputable def jointCodeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .entropyCapActive) known]
    (realizedFresh : K .jointCodeRealized ∉ known)
    (unrealizedFresh : K .jointCodeUnrealized ∉ known) :
    Decision (K .jointCodeRealized) (K .jointCodeUnrealized) previous := by
  classical
  let _active := (previous.get (K .entropyCapActive)).down
  exact Decision.run previous (K .jointCodeRealized) (K .jointCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.jointCodeDichotomy
    (if realized : JointCodeRealized data current.object then
      .inl ⟨realized⟩
    else
      .inr ⟨fun State stateOf => by
        by_contra le
        exact realized ⟨State, stateOf, Nat.le_of_not_lt le⟩⟩)
    realizedFresh unrealizedFresh

/-- **The terminal `[54]`** (`prop:entropy-high-theta`): on the realized arm the
joint demand is at most the number of realized states, which
`lem:skeleton-dominates` bounds by the labelled skeleton budget, which
`eq:entropy-cap` says is strictly smaller than the joint demand. -/
theorem entropyCap_closes
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .jointCodeRealized) known]
    [FactKeys.Has (K .entropyCapActive) known]
    [FactKeys.Has (K .skeletonDominates) known] : False := by
  have realized := (history.get (K .jointCodeRealized)).down
  have active := (history.get (K .entropyCapActive)).down
  have dominates := (history.get (K .skeletonDominates)).down
  obtain ⟨State, stateOf, demandLe⟩ := realized
  have packingSpec := Classical.choose_spec
    (current.object.exists_windowPacking_card_eq data.windowOrder)
  have overflow := active (canonicalWindowPacking data current.object) packingSpec.1
  have rangeLe := dominates.2 State stateOf
  exact absurd (le_trans demandLe rangeLe) (Nat.not_le.mpr overflow)

end Hypostructure.Graph.Strategy.Spine
