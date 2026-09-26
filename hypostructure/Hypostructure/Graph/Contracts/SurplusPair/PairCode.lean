import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contract lemmas: the pair-code chain `[178]`--`[180]`

Proof-agnostic statements of what each arm of the three pair-code tests
yields.  Every lemma is stated over a finite object and the registered
`Parameters`, with the paper's assumptions as explicit hypotheses; none
mentions keys, ledgers, branches or node numbers in its statement.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The conditional-factorization test failing on an object that carries a pair
overlap system retains that system as an uncovered pair-code residual. -/
theorem pairUncovered_of_factorizationFails
    (system : PairOverlapSystemStatement data object)
    (fails : PairFactorizationFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨system⟩ := system
  exact ⟨.factorization system fun factorization =>
    fails ⟨⟨system, factorization⟩⟩⟩

/-- The realizability test failing on an object that carries canonical demand
returns retains those returns as an uncovered pair-code residual. -/
theorem pairUncovered_of_realizabilityFails
    (returns : PairDemandReturnsStatement data object)
    (fails : PairRealizabilityFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨returns⟩ := returns
  exact ⟨.systemRealizability returns fun covered =>
    fails ⟨⟨returns, covered⟩⟩⟩

/-- The increment test failing on an object that carries a serial demand system
retains that system as an uncovered pair-code residual. -/
theorem pairUncovered_of_incrementFails
    (serial : PairSerialDemandSystemStatement data object)
    (fails : PairIncrementFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨serial⟩ := serial
  exact ⟨.incrementArithmetic serial fun covered =>
    fails ⟨⟨serial, covered⟩⟩⟩

/-- `lem:pair-system-realizability`, serial alternative: when the five
alternatives are covered and none of (i)--(iv) holds, alternative (v) supplies
a graph-realized serial demand system. -/
theorem pairSerialDemandSystem_of_noEarlyOutcome
    (covered : PairSystemRealizabilityStatement data object)
    (noEarly : PairSystemNoEarlyOutcomeStatement data object) :
    PairSerialDemandSystemStatement data object := by
  obtain ⟨⟨_returns, ⟨outcome⟩⟩⟩ := covered
  cases outcome with
  | early early => exact (noEarly ⟨early⟩).elim
  | serial serial _same => exact ⟨serial⟩

/-- `lem:pair-system-increment-arithmetic`, arithmetic alternative: when the
increment response is covered and neither periodic route holds, the corrected
full-modulus arithmetic input exists. -/
theorem pairSerialArithmetic_of_noEarlyOutcome
    (covered : PairIncrementCoveredStatement data object)
    (noEarly : PairIncrementNoEarlyOutcomeStatement data object) :
    PairSerialArithmeticStatement data object := by
  obtain ⟨⟨serial, ⟨outcome⟩⟩⟩ := covered
  cases outcome with
  | arithmetic arithmetic => exact ⟨⟨serial, ⟨arithmetic⟩⟩⟩
  | early early => exact (noEarly ⟨early⟩).elim

/-- Alternatives (i)--(iv) of `lem:pair-system-realizability` on an object with
no accepted cycle that survives the sparse exits: only alternative (iv), the
same-token Type B handoff of `lem:same-token-bottleneck-routing`, remains. -/
theorem sameTokenHandoff_of_pairSystemEarlyOutcome
    (early : PairSystemEarlyOutcomeStatement data object)
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (survives : SparseSurplusSurvivorStatement data object) :
    SameTokenTypeBHandoffStatement data object := by
  obtain ⟨early⟩ := early
  cases early with
  | targetCycle cycle => exact (noCycle cycle).elim
  | sparseExit exit => exact (survives exit).elim
  | typeB handoff => exact handoff

/-- The periodic alternatives of `lem:pair-system-increment-arithmetic` on an
object surviving the sparse exits: only the same-token Type B handoff
remains. -/
theorem sameTokenHandoff_of_pairIncrementEarlyOutcome
    (early : PairIncrementEarlyOutcomeStatement data object)
    (survives : SparseSurplusSurvivorStatement data object) :
    SameTokenTypeBHandoffStatement data object := by
  obtain ⟨early⟩ := early
  cases early with
  | sparseExit exit => exact (survives exit).elim
  | typeB handoff => exact handoff

end Hypostructure.Graph.Contracts.SurplusPair
