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
(`K .hotColdPartition`).  A sealed fact row reads that split, the package-rate
inequality, and the skeleton state-count bound.  On the retained arm it proves
`demand ≤ retainedCode 𝒫_hot ≤ #realized states ≤ budget`; on the complementary
all-cold arm the demand is the remainder class alone and `RemainderGlue` proves
the same bound.  The row publishes only `K .entropyCapBound`, the exact
inequality `demand ≤ budget`.  Core then closes it against
`K .entropyCapActive`, its strict negation.  No numeral, threshold, rate, or
out-of-ledger branch witness is supplied here.
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

/-- Node `[54]`'s active comparison and its exact skeleton bound cannot coexist.
The two facts are retrieved only by Core's closure boundary. -/
noncomputable instance instIncompatibleEntropyCapActiveBound :
    Incompatible (Input BranchState Presentation presentation data)
      (K .entropyCapActive) (K .entropyCapBound) where
  contradiction := fun _residual active bound =>
    (Nat.not_lt_of_ge bound.down) active.down

/-! **The sealed proof row for terminal `[54]`** (`prop:entropy-high-theta`).

The row follows the two alternatives already stored in the active residual's
`K .hotColdPartition`.  If the hot family is retained, the registered package
rate puts the joint demand below its retained code, and the realized-code and
skeleton-dominance clauses put that code below the labelled skeleton budget.
If no family is retained, the canonical hot family is empty and the remainder
glue gives the same bound.  Both alternatives therefore produce exactly
`K .entropyCapBound`; the terminal itself is Core's incompatibility closure
against `K .entropyCapActive`. -/
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
    { Requires :=
        [K .hotColdPartition, K .windowPackageSeparated, K .skeletonDominates]
      Produces := [K .entropyCapBound]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .entropyCapBound)
        (show Value BranchState Presentation presentation data
            .entropyCapBound inputs.current from
          ⟨by
            let object := inputs.current.object
            change jointPackageDemand data object ≤ Graph.skeletonBudget object
            have split := (inputs.get (K .hotColdPartition)).down
            have package := (inputs.get (K .windowPackageSeparated)).down
            have dominates := (inputs.get (K .skeletonDominates)).down
            obtain ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint,
              _cover⟩ := split
            obtain ⟨_packing, _packingValid, _packingCard, _packingMaximal,
              _packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
            rcases hotFacts.2.1 with retained | allCold
            · obtain ⟨State, stateOf, _packageStates, retainedCodeLe⟩ := retained
              have demandLe : jointPackageDemand data object ≤
                  retainedCode data object (canonicalHotWindows data object) := by
                unfold jointPackageDemand retainedCode
                calc
                  2 ^ (data.windowRate *
                        data.separatedScaleCount object.vertexCount *
                        (canonicalHotWindows data object).card) *
                      remainderStates data object
                        (canonicalWindowPacking data object)
                      ≤ 2 ^ (windowPackageBits data object *
                            (canonicalHotWindows data object).card) *
                          remainderStates data object
                            (canonicalWindowPacking data object) :=
                        Nat.mul_le_mul_right _
                          (Nat.pow_le_pow_right (by omega)
                            (Nat.mul_le_mul_right _ rateLe))
                  _ = 2 ^ (windowPackageBits data object *
                            (canonicalHotWindows data object).card) *
                          remainderStates data object
                            (canonicalWindowPacking data object) * 1 := by
                        rw [Nat.mul_one]
                  _ ≤ 2 ^ (windowPackageBits data object *
                            (canonicalHotWindows data object).card) *
                          remainderStates data object
                            (canonicalWindowPacking data object) *
                          2 ^ (data.curvatureCost *
                            remainderCurvatureTargetRank data object
                              (canonicalWindowPacking data object)) :=
                        Nat.mul_le_mul_left _ Nat.one_le_two_pow
              exact demandLe.trans
                (retainedCodeLe.trans (dominates.2 State stateOf))
            · unfold jointPackageDemand
              rw [allCold.1, Finset.card_empty, Nat.mul_zero, pow_zero,
                Nat.one_mul]
              exact Graph.RemainderGlue.remainderStateCount_le_skeletonBudget
                _ _ _ _⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
