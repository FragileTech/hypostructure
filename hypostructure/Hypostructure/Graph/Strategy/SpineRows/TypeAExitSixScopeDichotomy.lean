import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[106]`: the scope of the exit-`(6)` support dependence

`lem:typeA-exits-discharged` closes exit `(6)` by `lem:proper-smearing` when
the enlarging support is proper and by `lem:no-silent-global-smearing` when it
is all of `G`.  The scope decision is exact: the yes arm
(`K .typeAExitSixProperScope`) is a proper enlarging support, the no arm
(`K .typeAExitSixGlobalScope`) its negation.  Each arm then commits the
smearing lemma's conclusion, which the framework closes against the
replacement exclusion, respectively the selection's minimality. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitSixScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (properFresh : K .typeAExitSixProperScope ∉ known)
    (globalFresh : K .typeAExitSixGlobalScope ∉ known) :
    Decision (K .typeAExitSixProperScope) (K .typeAExitSixGlobalScope)
      previous :=
  Decision.run previous (K .typeAExitSixProperScope)
    (K .typeAExitSixGlobalScope)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy
    (by
      classical
      by_cases proper :
          TypeAExitSixProperScopeStatement data.toParameters current.object
      · exact .inl ⟨proper⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitSixGlobalScope_of_not_proper
          data.toParameters current.object proper⟩)
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
    { Requires := [K .typeAExitSix, K .typeAExitSixGlobalScope]
      Produces := [K .typeAExitSixGlobal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSixGlobal)
        ⟨Graph.Contracts.TypeA.typeAExitSixGlobal_of_scope data.toParameters
          inputs.current.object (inputs.get (K .typeAExitSix)).down
          (inputs.get (K .typeAExitSixGlobalScope)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
