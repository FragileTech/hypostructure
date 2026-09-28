import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.RemainderEntropy

/-!
# Window-entropy terminals: nodes `[23]` and `[54]`

Node `[23]` closes the live-hot overflow arm.  The retained hot-window package,
the certified package-rate inequality, and the canonical state-count bound are
read from the literal residual by one atomic row; that row publishes the
opposite cap fact, and the framework closes the resulting cap/overflow pair.

`prop:entropy-high-theta`: on the arm where the remaining non-obstruction
budget is strictly smaller than the forced obstruction cost `K|R| − o(|R|)` of
node `[48]` (`K .entropyCapActive`, `eq:entropy-cap`), *"the window package of `lem:p13-window-package`, the
remainder bits, and the forced obstruction bits together strictly exceed the
near-cubic skeleton budget.  These bits form one independently target-testable
coordinate family, so the number of realized target-complete states would
exceed the number of labelled skeletons, contradicting
`lem:independent-target-entropy`, `lem:skeleton-dominates`."*

The premise "form one independently target-testable coordinate family" is the
joint realization inequality `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` at G (in its finite
form, `jointRealization_iff_entropyCapBound`).  Node `[54]` is the exact
decision on it (`entropyJointRealizationDichotomy`).  On the arm where it holds
the sealed row `entropyCapBoundRow` publishes `K .entropyCapBound`, and Core
closes it against `K .entropyCapActive`, its strict negation.  On the arm where
it fails the explicitly constructed configuration at G
(`K .allColdEntropyResidual`: the unretained package of `P₀`, the remainder
glue, the outer room, the forced bits and the failing inequality) is the
returned residual.  No numeral, threshold, rate, or out-of-ledger branch
witness is supplied here.
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

/-- **Node `[22]`, the live-hot entropy cap test** (`def:cold-window-ledger`):
does the canonical hot family's package overflow the labelled skeleton budget,
`skeletonBudget < 2^{rate·scales·|𝒫_hot|}` (`K .barrierOverflow`, node `[23]`),
or fit it (`K .barrierCap`, the no-edge continuing at `[145]`)?  The two keys
are exact complements on the same canonical hot family; the split itself is
node `[22]`'s `K .hotColdPartition`. -/
noncomputable def barrierDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (capFresh : K .barrierCap ∉ known)
    (overflowFresh : K .barrierOverflow ∉ known) :
    Decision (K .barrierCap) (K .barrierOverflow) previous := by
  classical
  -- The decision reads its predecessor fact at the one object it splits.
  have _predecessor := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .barrierCap) (K .barrierOverflow)
    `Hypostructure.Graph.Strategy.Spine.barrierDichotomy
    (if overflow : BarrierOverflowStatement data.toParameters current.object then
      .inr ⟨overflow⟩
    else
      .inl ⟨Nat.le_of_not_lt overflow⟩)
    capFresh overflowFresh

/-- Node `[54]`'s active comparison and its exact skeleton bound cannot coexist.
The two facts are retrieved only by Core's closure boundary. -/
noncomputable instance instIncompatibleEntropyCapActiveBound :
    Incompatible (Input BranchState Presentation presentation data)
      (K .entropyCapActive) (K .entropyCapBound) where
  contradiction := fun _residual active bound =>
    (Nat.not_lt_of_ge bound.down) active.down

/-- The same pair registered with the skeleton bound visible upstream and the
active comparison as a row's sole output, as
`AtomicCT.runAndCloseIncompatible` expects. -/
noncomputable instance instIncompatibleEntropyCapBoundActive :
    Incompatible (Input BranchState Presentation presentation data)
      (K .entropyCapBound) (K .entropyCapActive) where
  contradiction := fun _residual bound active =>
    (Nat.not_lt_of_ge bound.down) active.down

/-- `[54]`'s returned residual and the joint realization inequality cannot
coexist (`Contracts.Spine.not_jointRealization_of_residual`). -/
noncomputable instance instIncompatibleAllColdEntropyJoint :
    Incompatible (Input BranchState Presentation presentation data)
      (K .allColdEntropyResidual) (K .entropyJointRealization) where
  contradiction := fun _residual residual joint =>
    Contracts.Spine.not_jointRealization_of_residual data.toParameters _
      residual.down joint.down

/-- **Node `[54]`, the exact decision** (`prop:entropy-high-theta`, tex 9921):
on `[53]`'s active arm (`K .entropyCapActive`, read here), does the paper's
joint realization inequality `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` hold at G
(`K .entropyJointRealization`)?  If not, the configuration at G is constructed
(`Contracts.Spine.allColdEntropyResidual_of_not_jointRealization`, from the
package rate `K .windowPackageSeparated`, the skeleton count
`K .skeletonDominates` and node `[48]`'s cost `K .forcedCurvatureCost`) and
published as `K .allColdEntropyResidual`. -/
noncomputable def entropyJointRealizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .entropyCapActive) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    (jointFresh : K .entropyJointRealization ∉ known)
    (residualFresh : K .allColdEntropyResidual ∉ known) :
    Decision (K .entropyJointRealization) (K .allColdEntropyResidual) previous := by
  classical
  -- The decision reads its predecessor fact at the one object it splits.
  have _active := (previous.get (K .entropyCapActive)).down
  exact Decision.run previous (K .entropyJointRealization) (K .allColdEntropyResidual)
    `Hypostructure.Graph.Strategy.Spine.entropyJointRealizationDichotomy
    (if joint : EntropyJointRealizationStatement data.toParameters current.object then
      .inl ⟨joint⟩
    else
      .inr ⟨Contracts.Spine.allColdEntropyResidual_of_not_jointRealization
        data.toParameters current.object
        (previous.get (K .windowPackageSeparated)).down
        (previous.get (K .skeletonDominates)).down
        (previous.get (K .forcedCurvatureCost)).down joint⟩)
    jointFresh residualFresh

/-! **The sealed proof row for terminal `[54]`** (`prop:entropy-high-theta`), on
the joint-realization arm of node `[54]`'s decision: the joint realization
inequality at G, read through `jointRealization_iff_entropyCapBound` (the
finite form of `lem:independent-target-entropy` with `lem:skeleton-dominates`),
is the bound `K .entropyCapBound`.  The terminal itself is Core's
incompatibility closure against `K .entropyCapActive`. -/
@[reducible] noncomputable def entropyCapBoundRow :
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
    `Hypostructure.Graph.Strategy.Spine.entropyCapBound
    { Requires := [K .entropyJointRealization, K .skeletonDominates]
      Produces := [K .entropyCapBound]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .entropyCapBound)
        ⟨Contracts.Spine.entropyCapBound_of_jointRealization data.toParameters
          inputs.current.object
          (inputs.get (K .skeletonDominates)).down
          (inputs.get (K .entropyJointRealization)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
