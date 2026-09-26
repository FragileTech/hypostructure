import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.PairCode
import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[178]`: the manuscript's conditional-factorization test, decided by
exact case analysis on its predicate.  The positive arm is the sole input of
`lem:pair-failure-overlap`; the negative arm is its literal negation, from
which `pairFactorizationResidualRow` publishes the open node-`[182]` residual. -/
noncomputable def pairConditionalFactorizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (factorizationFresh : K .pairConditionalFactorization ∉ known)
    (failsFresh : K .pairFactorizationFails ∉ known) :
    Decision (K .pairConditionalFactorization)
      (K .pairFactorizationFails) previous := by
  classical
  exact Decision.run previous (K .pairConditionalFactorization)
    (K .pairFactorizationFails)
    `Hypostructure.Graph.Strategy.Spine.pairConditionalFactorizationDichotomy
    (if factorization : Holds BranchState Presentation presentation data
        .pairConditionalFactorization current.object then
      .inl ⟨factorization⟩
    else
      .inr ⟨factorization⟩)
    factorizationFresh failsFresh

/-- Node `[182]` from `[178]`: the failed factorization test retains the
literal pair overlap system as the uncovered pair-code residual. -/
@[reducible] noncomputable def pairFactorizationResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairFactorizationResidual
    { Requires := [K .pairFactorizationFails, K .pairOverlapSystem]
      Produces := [K .pairConditionalFactorizationResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairConditionalFactorizationResidual)
        ⟨Graph.Contracts.SurplusPair.pairUncovered_of_factorizationFails
          (inputs.get (K .pairOverlapSystem)).down
          (inputs.get (K .pairFactorizationFails)).down⟩
        .nil)

/-- **`lem:pair-failure-overlap` at node `[178]`.**

The row reads the exact failed response system together with the affirmative
conditional-factorization fact from the ledger.  It proves only the paper's
inclusion-minimal overlap conclusion.  A nonfactorizing system cannot enter
this row; it remains at node `[182]`. -/
@[reducible] noncomputable def pairFailureOverlapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairFailureOverlap
    { Requires := [K .pairConditionalFactorization]
      Produces := [K .pairFailureOverlap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairFailureOverlap)
        ⟨Graph.Contracts.SurplusPair.pairFailureOverlap_of_factorization
          (inputs.get (K .pairConditionalFactorization)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
