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

/-- Node `[139]`, "token in `𝔗_W`?": read node `[137]`'s overload arm (its
predecessor key), which exhibits G's canonical overloading token, and decide
whether that token's class is `𝔗_W`.  Both arms are about that one token. -/
noncomputable def windowOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .sparsePressureOverload) known]
    (windowFresh : K .windowClassOverload ∉ known)
    (absentFresh : K .windowClassAbsent ∉ known) :
    Decision (K .windowClassOverload) (K .windowClassAbsent) previous :=
  Decision.run previous (K .windowClassOverload) (K .windowClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.windowOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .windowClassOverload).At current ⊕
          (K .windowClassAbsent).At current) from by
      obtain ⟨value, classified⟩ :=
        Graph.Contracts.SurplusPair.canonicalOverloadClass_of_overload
          (previous.get (K .sparsePressureOverload)).down
      by_cases window : value = .windowIncidence
      · subst window
        exact ⟨.inl ⟨classified⟩⟩
      · exact ⟨.inr ⟨value, classified, window⟩⟩))
    windowFresh absentFresh

/-- Node `[141]`, "token in `𝔗_R`?": read node `[139]`'s no arm (its
predecessor key), the class of G's overloading token outside `𝔗_W`, and decide
whether it is `𝔗_R`.  Both arms are about that one token. -/
noncomputable def remainderOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .windowClassAbsent) known]
    (remainderFresh : K .remainderClassOverload ∉ known)
    (absentFresh : K .remainderClassAbsent ∉ known) :
    Decision (K .remainderClassOverload) (K .remainderClassAbsent) previous :=
  Decision.run previous (K .remainderClassOverload)
    (K .remainderClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.remainderOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .remainderClassOverload).At current ⊕
          (K .remainderClassAbsent).At current) from by
      obtain ⟨value, classified, _notWindow⟩ :=
        (previous.get (K .windowClassAbsent)).down
      by_cases remainder : value = .remainderSurplus
      · subst remainder
        exact ⟨.inl ⟨classified⟩⟩
      · exact ⟨.inr ⟨value, classified, remainder⟩⟩))
    remainderFresh absentFresh

/-- Node `[143]`'s entry: on the no arms of `[139]` and `[141]` the overloading
token of G is primitive. -/
@[reducible] noncomputable def primitiveClassOverloadRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveClassOverload
    { Requires := [K .windowClassAbsent, K .remainderClassAbsent]
      Produces := [K .primitiveClassOverload]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .primitiveClassOverload)
        ⟨Graph.Contracts.SurplusPair.primitiveClassOverload_of_classesAbsent
          (inputs.get (K .windowClassAbsent)).down
          (inputs.get (K .remainderClassAbsent)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
