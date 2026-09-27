import Hypostructure.Graph.Statements.SurplusPairCode

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

/-- The conditional-factorization test failing at G's canonical overlap system
retains that system as the uncovered pair-code residual. -/
theorem pairUncovered_of_factorizationFails
    (system : PairOverlapSystemStatement data object)
    (fails : PairFactorizationFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨system, selected⟩ := system
  exact ⟨.factorization system selected fun factorization =>
    fails ⟨system, selected, factorization⟩⟩

/-- The realizability test failing at G's canonical return system retains
those returns as the uncovered pair-code residual. -/
theorem pairUncovered_of_realizabilityFails
    (returns : PairDemandReturnsStatement data object)
    (fails : PairRealizabilityFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨returns, selected⟩ := returns
  exact ⟨.systemRealizability returns selected fun covered =>
    fails ⟨returns, selected, covered⟩⟩

/-- The increment test failing at G's canonical serial system retains that
system as the uncovered pair-code residual. -/
theorem pairUncovered_of_incrementFails
    (serial : PairSerialDemandSystemStatement data object)
    (fails : PairIncrementFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨serial, selected⟩ := serial
  exact ⟨.incrementArithmetic serial selected fun covered =>
    fails ⟨serial, selected, covered⟩⟩

/-- `lem:pair-system-realizability`, serial alternative: when G's canonical
return system is covered and its canonical outcome is not one of (i)--(iv),
that outcome is alternative (v), G's canonical serial demand system. -/
theorem pairSerialDemandSystem_of_noEarlyOutcome
    (covered : PairSystemRealizabilityStatement data object)
    (noEarly : PairSystemNoEarlyOutcomeStatement data object) :
    PairSerialDemandSystemStatement data object := by
  obtain ⟨returns, returnsSelected, covered⟩ := covered
  obtain ⟨outcome, outcomeSelected⟩ :=
    canonicalRealizabilityOutcome_spec data object returns covered
  cases outcome with
  | early early => exact (noEarly ⟨returns, early, returnsSelected, outcomeSelected⟩).elim
  | serial serial _same =>
      exact ⟨serial, by
        rw [canonicalPairSerialSystem, returnsSelected, Option.bind_some]
        simp only [outcomeSelected]⟩

/-- `lem:pair-system-increment-arithmetic`, arithmetic alternative: when G's
canonical serial system is covered and its canonical outcome is not periodic,
that outcome is the corrected full-modulus arithmetic input. -/
theorem pairSerialArithmetic_of_noEarlyOutcome
    (covered : PairIncrementCoveredStatement data object)
    (noEarly : PairIncrementNoEarlyOutcomeStatement data object) :
    PairSerialArithmeticStatement data object := by
  obtain ⟨serial, serialSelected, covered⟩ := covered
  obtain ⟨outcome, outcomeSelected⟩ :=
    canonicalIncrementOutcome_spec data object serial covered
  cases outcome with
  | arithmetic arithmetic => exact ⟨serial, arithmetic, serialSelected, outcomeSelected⟩
  | early early => exact (noEarly ⟨serial, early, serialSelected, outcomeSelected⟩).elim

/-- The obstruction's response coordinates lie in G's full pair-response family
at the obstruction's activation. -/
theorem obstructionCoordinates_subset (returns : PairDemandReturns data object) :
    returns.obstructionCoordinates ⊆
      (Graph.pairResponseActivation returns.overlap.system.first.active).pairFamily
        (object.portPairSchedule data.threshold) := by
  classical
  unfold PairDemandReturns.obstructionCoordinates
    Graph.FiniteObject.DemandActivation.pairFamily
  apply Finset.image_subset_image
  intro pair member
  obtain ⟨retained, -, rfl⟩ := Finset.mem_image.mp member
  exact returns.overlap.system.first.pairSet_subset_schedule retained.2

/-- Alternatives (ii) and (iii) about the obstruction's own coordinates and
support are sparse surplus exits of G's declared family. -/
theorem declaredSparseSurplusExit_of_obstructionDefect
    (returns : PairDemandReturns data object)
    (defect : Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK)
      object returns.obstructionCoordinates pairCoordinateSupport) :
    DeclaredSparseSurplusExit data object :=
  declaredSparseSurplusExit_of_pairDefect data object
    returns.overlap.system.first.active (obstructionCoordinates_subset returns)
    defect

/-- Alternatives (i)--(iv) of `lem:pair-system-realizability` for G's canonical
return system, on an object with no accepted cycle that survives the sparse
exits of its declared family: only alternative (iv), the same-token Type B
handoff of G (`lem:same-token-bottleneck-routing`), remains. -/
theorem sameTokenHandoff_of_pairSystemEarlyOutcome
    (early : PairSystemEarlyOutcomeStatement data object)
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (survives : SparseSurplusSurvivorStatement data object) :
    SameTokenTypeBHandoffStatement data object := by
  obtain ⟨returns, early, -, -⟩ := early
  cases early with
  | targetCycle cycle => exact (noCycle cycle).elim
  | targetDefect defect =>
      exact (survives (declaredSparseSurplusExit_of_obstructionDefect returns
        defect)).elim
  | compression support _inside replacement =>
      exact (survives (.compression support replacement)).elim
  | typeB handoff => exact handoff

/-- The periodic alternatives of `lem:pair-system-increment-arithmetic` for G's
canonical serial system, on an object surviving the sparse exits of its
declared family: only the same-token Type B handoff of G remains. -/
theorem sameTokenHandoff_of_pairIncrementEarlyOutcome
    (early : PairIncrementEarlyOutcomeStatement data object)
    (survives : SparseSurplusSurvivorStatement data object) :
    SameTokenTypeBHandoffStatement data object := by
  obtain ⟨serial, early, -, -⟩ := early
  cases early with
  | targetDefect defect =>
      exact (survives (declaredSparseSurplusExit_of_obstructionDefect
        serial.returns defect)).elim
  | compression support _inside replacement =>
      exact (survives (.compression support replacement)).elim
  | typeB handoff => exact handoff

end Hypostructure.Graph.Contracts.SurplusPair
