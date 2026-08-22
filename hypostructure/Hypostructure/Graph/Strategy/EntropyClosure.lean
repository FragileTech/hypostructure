import Hypostructure.Graph.Strategy.SpineRows

/-!
# Window-entropy terminals: nodes `[23]` and `[54]`

Node `[23]` closes the live-hot overflow arm.  The retained hot-window package,
the certified package-rate inequality, and the canonical state-count bound are
read from the literal residual by one atomic row; that row publishes the
opposite cap fact, and the framework closes the resulting cap/overflow pair.

`prop:entropy-high-theta`: on the arm where the remaining non-curvature budget
is strictly smaller than the forced curvature cost (`K .entropyCapActive`,
`eq:entropy-cap`), *"the window package of `lem:p13-window-package`, the
remainder bits, and the forced-curvature bits together strictly exceed the
near-cubic skeleton budget.  These bits form one independently target-testable
coordinate family, so the number of realized target-complete states would
exceed the number of labelled skeletons, contradicting
`lem:independent-target-entropy`, `lem:skeleton-dominates`."*

The premise "form one independently target-testable coordinate family" is a
property of the residual, carried by node `[22]`'s hot/cold split
(`K .hotColdPartition`): the canonical entropy comparison *retains* the hot
windows' full packages together with the remainder states and the exact
curvature code of the fixed packing (`WindowFamilyRealized` = `retainedCode`
realized by the labelled skeletons of the class), which is `def:target-rank`'s
"independently target-testable … arising canonically from graphs in the
labelled class" and the exact-code equality `def:curvature-target-rank` says is
retained on the surviving hot residual entering node `[47]`.  The terminal is
then a plain contradiction of ledger facts:
`K .entropyCapActive` (`budget < demand`), `K .hotColdPartition`
(`demand ≤ retainedCode 𝒫_hot ≤ #realized states`, using
`K .windowPackageSeparated`'s `rate · scales ≤ bits`), and
`K .skeletonDominates` (`#realized states ≤ budget`).  No numeral, threshold or
rate is written here.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The two numeric arms of node `[22]` are exact negations.  On node `[23]`'s
overflow ledger, the atomic row establishes the cap arm from the paper's
retained-package premises.  This registration puts the visible upstream arm
first and the row's sole output second, exactly as
`AtomicCT.runAndCloseIncompatible` expects. -/
noncomputable instance instIncompatibleBarrierOverflowCap :
    Incompatible (Input BranchState Presentation presentation data)
      (K .barrierOverflow) (K .barrierCap) where
  contradiction := fun _residual overflow cap =>
    (Nat.not_lt_of_ge cap.down) overflow.down

/-- The joint package demand of nodes `[52]`--`[53]` is at most the code the
comparison retains for the hot family: the registered rate never exceeds the
package width (`lem:p13-window-package`, read from `K .windowPackageSeparated`). -/
theorem jointPackageDemand_le_retainedCode (object : Graph.FiniteObject.{u})
    (rateLe : data.windowRate * data.separatedScaleCount object.vertexCount ≤
      windowPackageBits data object) :
    jointPackageDemand data object ≤
      retainedCode data object (canonicalHotWindows data object) := by
  unfold jointPackageDemand retainedCode
  calc 2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
          (canonicalHotWindows data object).card) *
        remainderStates data object (canonicalWindowPacking data object)
      ≤ 2 ^ (windowPackageBits data object * (canonicalHotWindows data object).card) *
          remainderStates data object (canonicalWindowPacking data object) :=
        Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ rateLe))
    _ = 2 ^ (windowPackageBits data object * (canonicalHotWindows data object).card) *
          remainderStates data object (canonicalWindowPacking data object) * 1 := by
        rw [Nat.mul_one]
    _ ≤ 2 ^ (windowPackageBits data object * (canonicalHotWindows data object).card) *
          remainderStates data object (canonicalWindowPacking data object) *
        2 ^ (data.curvatureCost *
          remainderCurvatureTargetRank data object (canonicalWindowPacking data object)) :=
        Nat.mul_le_mul_left _ Nat.one_le_two_pow

/-- **The remainder-only demand is within the budget** (`RemainderGlue`): with no
hot window retained, the joint demand of `[52]`--`[53]` is the remainder class of
the fixed maximal packing, which glues injectively into the object's labelled
skeleton class. -/
theorem jointPackageDemand_le_skeletonBudget_of_allCold (object : Graph.FiniteObject.{u})
    (allCold : canonicalHotWindows data object = ∅) :
    jointPackageDemand data object ≤ Graph.skeletonBudget object := by
  unfold jointPackageDemand
  rw [allCold, Finset.card_empty, Nat.mul_zero, pow_zero, Nat.one_mul]
  exact Graph.RemainderGlue.remainderStateCount_le_skeletonBudget _ _ _ _

/-- **The terminal `[54]`** (`prop:entropy-high-theta`), on the residual whose
canonical comparison retains the hot family's code: the joint demand is at most
the retained code, which the labelled skeletons realize, which
`lem:skeleton-dominates` bounds by the skeleton budget, which `eq:entropy-cap`
says is strictly smaller than the joint demand. -/
theorem entropyCap_closes
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .entropyCapActive) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    (retained : WindowFamilyRealized data current.object
      (canonicalHotWindows data current.object)) : False := by
  have active := (history.get (K .entropyCapActive)).down
  have dominates := (history.get (K .skeletonDominates)).down
  have package := (history.get (K .windowPackageSeparated)).down
  obtain ⟨_packing, _valid, _card, _maximal, _packageCard, _disjoint, _familyCard,
    rateLe, _⟩ := package
  obtain ⟨State, stateOf, _packageLe, codeLe⟩ := retained
  have demandLe := jointPackageDemand_le_retainedCode (data := data) current.object rateLe
  have rangeLe := dominates.2 State stateOf
  exact absurd (le_trans demandLe (le_trans codeLe rangeLe)) (Nat.not_le.mpr active)

/-- **The terminal `[54]` on the all-cold residual.**  When the canonical
comparison retains no window (`𝒫_hot = ∅`, `def:curvature-target-rank`'s
"complementary cold residual"), the joint demand is the remainder class alone,
which the glue `H ↦ G[R := H]` bounds by the labelled skeleton budget
(`lem:skeleton-dominates` at `def:remainder-entropy`'s inherited vertex set and
edge count), while `eq:entropy-cap` says the budget is strictly smaller. -/
theorem entropyCap_closes_of_allCold
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .entropyCapActive) known]
    (allCold : canonicalHotWindows data current.object = ∅) : False := by
  have active := (history.get (K .entropyCapActive)).down
  exact absurd (jointPackageDemand_le_skeletonBudget_of_allCold (data := data)
    current.object allCold) (Nat.not_le.mpr active)

/-- The retained-code clause of `K .hotColdPartition` at the residual's own hot
family: either the hot family's code is realized, or every window is cold
because not even the empty family's remainder-and-curvature code is realized
(`def:curvature-target-rank`: "its failure is the complementary cold
residual"). -/
theorem hotFamily_retained_or_cold
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known] :
    WindowFamilyRealized data current.object (canonicalHotWindows data current.object) ∨
      (canonicalHotWindows data current.object = ∅ ∧
        ¬ WindowFamilyRealized data current.object ∅) := by
  have split := (history.get (K .hotColdPartition)).down
  obtain ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint, _cover⟩ := split
  exact hotFacts.2.1

end Hypostructure.Graph.Strategy.Spine
