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

/-! ## Node `[23]`: the live-hot window overflow -/

/-! **Node `[23]`, the live-hot entropy comparison.**  On the literal overflow
residual, `def:cold-window-ledger` says that the canonical hot family either
has its full package realized by labelled skeletons or is empty.  In the first
case `lem:p13-window-package` converts the registered rate into a lower bound
on the realized state count and `lem:skeleton-dominates` bounds that count by
the skeleton budget.  In the empty case the required package has one state,
while the selected object's skeleton class is nonempty.  Thus the exact cap
opposite to the overflow arm holds.

All three manuscript premises are read through `FactInputs.get`, and the
statement is indexed by `inputs.current`; no detached graph or proof payload is
accepted by the row. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def liveHotBarrierCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.liveHotBarrierCap
    { Requires :=
        [K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated]
      Produces := [K .barrierCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .barrierCap)
        (show Value BranchState Presentation presentation data
            .barrierCap inputs.current from
          ⟨by
            let object := inputs.current.object
            change 2 ^ (data.windowRate *
                data.separatedScaleCount object.vertexCount *
                (canonicalHotWindows data object).card) ≤
              Graph.skeletonBudget object
            have split := (inputs.get (K .hotColdPartition)).down
            have dominates := (inputs.get (K .skeletonDominates)).down
            have package := (inputs.get (K .windowPackageSeparated)).down
            obtain
              ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint, _cover⟩ :=
                split
            obtain ⟨_hotSubset, retained, _hotMaximal⟩ := hotFacts
            obtain ⟨_packing, _packingValid, _packingCard, _packingMaximal,
              _packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
            have exponentLe :
                data.windowRate * data.separatedScaleCount object.vertexCount *
                    (canonicalHotWindows data object).card ≤
                  windowPackageBits data object *
                    (canonicalHotWindows data object).card :=
              Nat.mul_le_mul_right _ rateLe
            rcases retained with
              ⟨State, stateOf, packageStates, _retainedCode⟩ |
                ⟨hotEmpty, _emptyUnrealized⟩
            · have realizedBound := dominates.2 State stateOf
              exact (Nat.pow_le_pow_right (by norm_num) exponentLe).trans
                (packageStates.trans realizedBound)
            · rw [hotEmpty]
              simp only [Finset.card_empty, Nat.mul_zero, pow_zero]
              exact Graph.skeletonBudget_pos object⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
