import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BlockedCompression

/-!
# Node `[170]`: `lem:scale-additivity`

`lem:scale-additivity` decides, on the trivial neutral-configuration residual of node
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
either every conditional graph fibre satisfies the denominator-cleared
`F_{a,b}/W_{a,b}` bound, or the no-arm retains the first exposure coordinate,
its fixed outside record and prefix, and the two graph fibres witnessing the
failure.  Constructing the minimal connected overlap support is the next lemma;
it is not smuggled into this decision. -/
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
  exact Decision.run previous (K .blockedScaleAdditive) (K .blockedBarrierOverlap)
    `Hypostructure.Graph.Strategy.Spine.scaleAdditivityDichotomy
    (if additive : ∀ coordinate : blockedCoordinate data.toParameters current.object,
        BlockedRelativeFibreBoundAt data.toParameters current.object coordinate then
      .inl ⟨Contracts.Spine.blockedScaleAdditive_of_relative data.toParameters
        current.object data.lengthOK_iff_powerOfTwo data.degenerateClosureRejected
        data.windowBarrierLabel data.windowBarrierLabel_mem
        data.windowBarrierLabel_injective data.windowBarrierLabel_surjective
        data.windowBarrier_left_semantic data.windowBarrier_right_semantic
        data.windowBarrier_sum_semantic additive⟩
    else
      .inr ⟨Contracts.Spine.blockedBarrierFailure_of_not_relative data.toParameters
        current.object data.lengthOK_iff_powerOfTwo data.degenerateClosureRejected
        data.windowBarrierLabel data.windowBarrierLabel_mem
        data.windowBarrierLabel_injective data.windowBarrierLabel_surjective
        data.windowBarrier_left_semantic data.windowBarrier_right_semantic
        data.windowBarrier_sum_semantic additive⟩)
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
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .densePackingOverflow)
        ⟨Contracts.Spine.densePackingOverflow_of_unrealized data.toParameters
          inputs.current.object (inputs.get (K .windowPackageUnrealized)).down
          (inputs.get (K .skeletonDominates)).down.1⟩
        .nil)

/-! ## Node `[171]`: `lem:blocked-graphs-compress` -/

/-- **Node `[171]`, `lem:blocked-graphs-compress`.**  Expose the exact
near-cubic graph class in the manuscript's canonical scale/window/barrier
order.  The `K .blockedScaleAdditive` ratios multiply over realized prefixes;
the registered barrier table then converts their product into the exact
package-bit saving.  The row publishes both the denominator-cleared
compression inequality and its skeleton-budget consequence. -/
@[reducible] noncomputable def blockedCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedCompression
    { Requires := [K .blockedClassMember, K .blockedScaleAdditive]
      Produces := [K .blockedCompressionBound, K .blockedCompressionCap]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let compressionBound :=
        Contracts.Spine.blockedCompressionBound_of_additive data.toParameters
          inputs.current.object (inputs.get (K .blockedScaleAdditive)).down
      .cons (key := K .blockedCompressionBound) ⟨compressionBound⟩
        (.cons (key := K .blockedCompressionCap)
          ⟨Contracts.Spine.blockedCompressionCap_of_bound data.toParameters
            inputs.current.object (inputs.get (K .blockedClassMember)).down
            compressionBound⟩ .nil))

/-- The dense-packing residual is the strict reverse of node `[171]`'s
published terminal budget consequence. -/
noncomputable instance instIncompatibleDensePackingOverflowCompressionCap :
    Incompatible (Input BranchState Presentation presentation data)
      (K .densePackingOverflow) (K .blockedCompressionCap) where
  contradiction := fun _input overflow cap =>
    (Nat.not_lt_of_ge cap.down) overflow.down

end Hypostructure.Graph.Strategy.Spine
