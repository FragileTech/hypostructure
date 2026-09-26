import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[106]`: the scope of the exit-`(6)` support dependence

The committed exit-`(6)` state (`K .typeAExitSix`) has one canonical
delocalization (`canonicalExitSixDelocalizationAt`, d2ded0e: the one
delocalization of that state).  The decision splits on its enlarging support
`Z`: proper (`K .typeAExitSixProperScope`, closed by `lem:proper-smearing`
against the replacement exclusion) or all of `G`
(`K .typeAExitSixGlobalScope`, closed by `lem:no-silent-global-smearing`
against the selection's minimality). -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[106]`, decided at the canonical delocalization of the exit-`(6)` state. -/
noncomputable def typeAExitSixScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAExitSix) known]
    (properFresh : K .typeAExitSixProperScope ∉ known)
    (globalFresh : K .typeAExitSixGlobalScope ∉ known) :
    Decision (K .typeAExitSixProperScope) (K .typeAExitSixGlobalScope) previous :=
  Decision.run previous (K .typeAExitSixProperScope) (K .typeAExitSixGlobalScope)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitSixProperScope).At current ⊕ (K .typeAExitSixGlobalScope).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, _state, six⟩ :=
        (previous.get (K .typeAExitSix)).down
      obtain ⟨delocalization, found⟩ := canonicalExitSixDelocalizationAt_spec six
      by_cases proper : ∃ vertex, vertex ∉ delocalization.2.quotient.support
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, delocalization, found,
          proper⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, delocalization, found,
          fun vertex => by
            by_contra outside
            exact proper ⟨vertex, outside⟩⟩⟩⟩))
    properFresh globalFresh

/-- `lem:proper-smearing` on the proper-scope arm. -/
@[reducible] noncomputable def typeAExitSixProperRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitSixProper
    { Requires := [K .typeAExitSixProperScope]
      Produces := [K .typeAExitSixProper]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSixProper)
        ⟨Graph.Contracts.TypeA.typeAExitSixProper_of_scope data.toParameters
          inputs.current.object (inputs.get (K .typeAExitSixProperScope)).down⟩
        .nil)

/-- `lem:no-silent-global-smearing` on the whole-graph arm. -/
@[reducible] noncomputable def typeAExitSixGlobalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitSixGlobal
    { Requires := [K .typeAExitSixGlobalScope]
      Produces := [K .typeAExitSixGlobal]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSixGlobal)
        ⟨Graph.Contracts.TypeA.typeAExitSixGlobal_of_scope data.toParameters
          inputs.current.object (inputs.get (K .typeAExitSixGlobalScope)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
