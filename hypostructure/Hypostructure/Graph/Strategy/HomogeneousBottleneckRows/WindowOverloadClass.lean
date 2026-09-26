import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.OverloadClass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[139]`, "token in `𝔗_W`?": exact case analysis on the window-class
overload predicate.  The no arm is its literal negation. -/
noncomputable def windowOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (windowFresh : K .windowClassOverload ∉ known)
    (absentFresh : K .windowClassAbsent ∉ known) :
    Decision (K .windowClassOverload) (K .windowClassAbsent) previous := by
  classical
  exact Decision.run previous (K .windowClassOverload) (K .windowClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.windowOverloadClassDichotomy
    (if window : Holds BranchState Presentation presentation data
        .windowClassOverload current.object then
      .inl ⟨window⟩
    else
      .inr ⟨window⟩)
    windowFresh absentFresh

/-- Node `[141]`, "token in `𝔗_R`?": exact case analysis on the
remainder-class overload predicate.  The no arm is its literal negation. -/
noncomputable def remainderOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (remainderFresh : K .remainderClassOverload ∉ known)
    (absentFresh : K .remainderClassAbsent ∉ known) :
    Decision (K .remainderClassOverload) (K .remainderClassAbsent) previous := by
  classical
  exact Decision.run previous (K .remainderClassOverload)
    (K .remainderClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.remainderOverloadClassDichotomy
    (if remainder : Holds BranchState Presentation presentation data
        .remainderClassOverload current.object then
      .inl ⟨remainder⟩
    else
      .inr ⟨remainder⟩)
    remainderFresh absentFresh

/-- Node `[143]`'s entry: on the no arms of `[139]` and `[141]` the overloading
token of `[137]` is primitive. -/
@[reducible] noncomputable def primitiveClassOverloadRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveClassOverload
    { Requires := [K .sparsePressureOverload, K .windowClassAbsent,
        K .remainderClassAbsent]
      Produces := [K .primitiveClassOverload]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .primitiveClassOverload)
        ⟨Graph.Contracts.SurplusPair.primitiveClassOverload_of_classesAbsent
          (inputs.get (K .sparsePressureOverload)).down
          (inputs.get (K .windowClassAbsent)).down
          (inputs.get (K .remainderClassAbsent)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
