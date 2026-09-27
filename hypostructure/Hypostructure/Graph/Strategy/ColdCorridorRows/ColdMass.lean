import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdMass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! Node `[149]`: the live-hot overflow arm closes by the entropy comparison.
The density cap is available after the cold branch closes. -/

/-- Node `[150]`: derive the exact cleared cold-mass inequality. -/
@[reducible] noncomputable def coldMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldMass
    { Requires := [K .hotColdPartition, K .coldHotEntropyCap]
      Produces := [K .coldMass]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldMass)
        ⟨Contracts.Spine.coldMass_of_hotCap data.toParameters
          inputs.current.object (inputs.get (K .hotColdPartition)).down
          (inputs.get (K .coldHotEntropyCap)).down⟩
        .nil)

/-- Node `[151]`: charge each non-ambient-cubic cold window injectively to a
positive-surplus vertex of the current object. -/
@[reducible] noncomputable def coldAmbientCubicRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldAmbientCubic
    { Requires := [K .hotColdPartition, K .surplusAtOrBelow]
      Produces := [K .coldAmbientCubic]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldAmbientCubic)
        ⟨Contracts.Spine.coldAmbientCubic_of_split data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .hotColdPartition)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩
        .nil)

/-- Node `[152]`: derive the branch-excess inequality from node `[151]`. -/
@[reducible] noncomputable def coldStubExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldStubExcess
    { Requires := [K .hotColdPartition, K .coldAmbientCubic, K .cubicBaseline]
      Produces := [K .coldSelectedBranchExcess,
        K .coldAmbientCubicStubExcess, K .coldStubExcess]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .coldSelectedBranchExcess)
        ⟨Contracts.Spine.coldSelectedBranchExcess_of_split data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.1.1
          data.three_le_windowOrder split⟩
        (.cons (key := K .coldAmbientCubicStubExcess)
          ⟨Contracts.Spine.coldAmbientCubicStubExcess_of_split data.toParameters
            inputs.current.object split⟩
          (.cons (key := K .coldStubExcess)
            ⟨Contracts.Spine.coldStubExcess_of_ambientCubic data.toParameters
              inputs.current.object (inputs.get (K .coldAmbientCubic)).down⟩
            .nil)))

/-! ## Node `[153]`: the exact finite form of "positive for all sufficiently large `n`"

`lem:cold-germ-extraction`, with node `[168]`'s endpoint repair, bounds the
selected interior germ family below by `9C/D_cold − o(n)`;
`thm:cold-branch-quantitative-closure` uses that "the
displayed lower bound is positive for all sufficiently large `n`".  In exact
finite form the two `o(n)` losses of `[151]`--`[153]` are `perWindow·σ(G)` (the
non-ambient-cubic windows) and `(threshold+1)·B_cold·σ(G)` (the oriented
high-to-subcubic candidate loss), so the branch that forces a germ is
`(perWindow + (threshold+1)·B_cold)·σ(G) < perWindow·C`, and
its complement is where the spine continues to `[24]`. -/

/-- Node `[153]`'s exhaustive comparison on the literal `[152]` residual. -/
noncomputable def coldMassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldStubExcess) known]
    (linearFresh : K .coldMassLinear ∉ known)
    (boundedFresh : K .coldMassBounded ∉ known) :
    Decision (K .coldMassLinear) (K .coldMassBounded) previous := by
  classical
  exact Decision.run previous (K .coldMassLinear) (K .coldMassBounded)
    `Hypostructure.Graph.Strategy.Spine.coldMassDichotomy
    (if linear : ColdMassLinearStatement data.toParameters current.object then
      .inl ⟨linear⟩
    else
      .inr ⟨Contracts.Spine.coldMassBounded_of_not_linear data.toParameters
        current.object linear⟩)
    linearFresh boundedFresh

end Hypostructure.Graph.Strategy.Spine
