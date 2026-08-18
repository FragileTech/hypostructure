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


/-! ## Node `[171]`: `lem:blocked-graphs-compress` -/

/-- **Node `[159]`, `def:window-realization-test` read on the ledger.**  The
realization test is "there is an assignment of target-complete states to
labelled skeletons whose range has at least `2^{c₁₃p₁₃log₂n}` elements"; by
`lem:skeleton-dominates` (`K .skeletonDominates`) no assignment beats the
identity, whose range is the whole labelled class.  So the no-branch gives the
definition's own display `2^{c₁₃p₁₃log₂n} > card 𝒢_{n,m}` — the dense-packing
residual `[159]` — beside the retained-code clause that the same Lean key
carries for node `[22]`. -/
theorem denseOrJointCodeOverflow
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .skeletonDominates) known] :
    Graph.skeletonBudget current.object <
        2 ^ (windowPackageBits data current.object *
          (canonicalWindowPacking data current.object).card) ∨
      Graph.skeletonBudget current.object <
        retainedCode data current.object (canonicalWindowPacking data current.object) := by
  classical
  have unrealized := (previous.get (K .windowPackageUnrealized)).down
  have dominates := (previous.get (K .skeletonDominates)).down
  by_contra contra
  push_neg at contra
  refine unrealized ⟨ULift.{u} (Graph.PackedWindowRealization.Skeleton
    current.object.vertexCount current.object.edgeCount), ULift.up, ?_, ?_⟩ <;>
  · have range : Nat.card (Set.range (ULift.up.{u} :
        Graph.PackedWindowRealization.Skeleton
          current.object.vertexCount current.object.edgeCount → _)) =
        Graph.skeletonBudget current.object := by
      rw [Set.range_eq_univ.2 (fun state => ⟨state.down, rfl⟩), Nat.card_univ,
        Nat.card_ulift]
      exact dominates.1
    rw [range]
    first
      | exact contra.1
      | exact contra.2

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
    (dense : Graph.skeletonBudget current.object <
      2 ^ (windowPackageBits data current.object *
        (canonicalWindowPacking data current.object).card)) :
    False := by
  classical
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
