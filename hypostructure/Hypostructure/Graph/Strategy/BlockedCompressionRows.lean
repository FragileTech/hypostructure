import Hypostructure.Graph.Strategy.ColdCorridorRows

/-!
# Node `[170]`: `lem:scale-additivity`

`lem:scale-additivity` decides, on the trivial neutral germ residual of node
`[169]` (`K .blockedClassMember`, `def:blocked-class`), whether the conditional
savings of the barrier states add at every fixed scale.  The barrier states
themselves, their completion supports and their conditional fibres are
`Graph/BarrierOverlapSystem.lean`; `W_{a,b}`/`F_{a,b}` are the registered
barrier table's two columns and `c₁₃` its certified `binaryRateFloor`, so no
numeral occurs here.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[170]`: the scale-additivity decision -/

/-- **Node `[170]`, `lem:scale-additivity`**, on the literal `[169]` residual:
either the conditional savings of the barrier states add at every fixed scale
(the encoding of `lem:blocked-graphs-compress`) or they do not, and
`lem:barrier-failure-overlap` supplies a minimal same-scale overlap
obstruction. -/
noncomputable def scaleAdditivityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .blockedClassMember) known]
    (additiveFresh : K .blockedScaleAdditive ∉ known)
    (overlapFresh : K .blockedBarrierOverlap ∉ known) :
    Decision (K .blockedScaleAdditive) (K .blockedBarrierOverlap) previous := by
  classical
  let _blocked := (previous.get (K .blockedClassMember)).down
  exact Decision.run previous (K .blockedScaleAdditive) (K .blockedBarrierOverlap)
    `Hypostructure.Graph.Strategy.Spine.scaleAdditivityDichotomy
    (if additive : BlockedScaleAdditivityStatement data current.object then
      .inl ⟨additive⟩
    else
      .inr ⟨additive⟩)
    additiveFresh overlapFresh


/-! ## Node `[159]`: the exact dense-packing residual -/

/-- **Node `[159]`, `def:window-realization-test`.**  The no-arm of `[158]`
denies precisely the window-package realization clause.  The identity map on
the labelled skeleton class has range equal to the exact skeleton budget, so
`lem:skeleton-dominates` turns that denial into the manuscript's single strict
display.  The stronger remainder-and-curvature retained code remains solely in
`K .hotColdPartition`; it is not bundled into this node. -/
@[reducible] noncomputable def densePackingOverflowRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.densePackingOverflow
    { Requires := [K .windowPackageUnrealized, K .skeletonDominates]
      Produces := [K .densePackingOverflow]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let unrealized := (inputs.get (K .windowPackageUnrealized)).down
      let dominates := (inputs.get (K .skeletonDominates)).down
      .cons (key := K .densePackingOverflow)
        ⟨by
          classical
          by_contra notDense
          have packageLe :
              2 ^ (windowPackageBits data inputs.current.object *
                (canonicalWindowPacking data inputs.current.object).card) ≤
                Graph.skeletonBudget inputs.current.object :=
            Nat.le_of_not_gt notDense
          apply unrealized
          refine ⟨ULift.{u} (Graph.PackedWindowRealization.Skeleton
            inputs.current.object.vertexCount inputs.current.object.edgeCount),
            ULift.up, ?_⟩
          have range : Nat.card (Set.range (ULift.up.{u} :
              Graph.PackedWindowRealization.Skeleton
                inputs.current.object.vertexCount inputs.current.object.edgeCount → _)) =
              Graph.skeletonBudget inputs.current.object := by
            rw [Set.range_eq_univ.2 (fun state => ⟨state.down, rfl⟩),
              Nat.card_univ, Nat.card_ulift]
            exact dominates.1
          rwa [range]⟩
        .nil)

/-! ## Node `[171]`: `lem:blocked-graphs-compress` -/

/-- **Node `[171]`, `lem:blocked-graphs-compress`.**  `lem:scale-additivity`'s
additive arm supplies `card 𝓑(𝒫) · 2^{c₁₃p₁₃log₂n} ≤ card 𝒢_{n,m}`, and
`def:blocked-class`'s last sentence puts the object's own skeleton in `𝓑(𝒫)`.
On the dense-packing residual `[159]`, where `2^{c₁₃p₁₃log₂n} > card 𝒢_{n,m}`,
the two give `card 𝓑(𝒫) < 1`: "a class with fewer than one element is empty;
`G ∈ 𝓑(𝒫)` is then impossible". -/
theorem blockedClassCompressionCloses
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .blockedClassMember) known]
    [FactKeys.Has (K .blockedScaleAdditive) known]
    [FactKeys.Has (K .densePackingOverflow) known] :
    False := by
  classical
  have dense := (previous.get (K .densePackingOverflow)).down
  obtain ⟨minDegree, isBlocked, _cardLe⟩ := (previous.get (K .blockedClassMember)).down
  obtain ⟨_fibre, saving⟩ := (previous.get (K .blockedScaleAdditive)).down
  -- `def:blocked-class`, last sentence: the object's own skeleton is in `𝓑(𝒫)`.
  have member : blockedClassAt data current.object :=
    ⟨⟨Graph.BlockedClass.objectSkeletonMember current.object, minDegree⟩, isBlocked⟩
  have positive : 0 < Nat.card (blockedClassAt data current.object) :=
    Nat.pos_of_ne_zero fun zero =>
      (Nat.card_eq_zero.1 zero).elim (fun empty => empty.false member)
        fun infinite => (not_infinite_iff_finite.2 inferInstance) infinite
  have one := Nat.le_mul_of_pos_left
    (2 ^ (windowPackageBits data current.object *
      (canonicalWindowPacking data current.object).card)) positive
  -- `lem:skeleton-dominates`: the near-cubic class is inside the skeleton budget.
  have nearCubic := Graph.BlockedClass.card_nearCubicSkeleton_le
    current.object.vertexCount current.object.edgeCount data.threshold
  exact absurd (lt_of_le_of_lt (le_trans (le_trans one saving) nearCubic) dense) (lt_irrefl _)

end Hypostructure.Graph.Strategy.Spine
