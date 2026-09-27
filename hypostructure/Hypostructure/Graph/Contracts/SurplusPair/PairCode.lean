import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.Statements.TypeBLanes

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
    (_returns : PairDemandReturnsStatement data object)
    (fails : PairRealizabilityFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨returns, selected, failure⟩ := fails
  exact ⟨.systemRealizability returns selected failure⟩

/-- The increment test failing at G's canonical serial system retains that
system as the uncovered pair-code residual. -/
theorem pairUncovered_of_incrementFails
    (_serial : PairSerialDemandSystemStatement data object)
    (fails : PairIncrementFailsStatement data object) :
    PairConditionalFactorizationResidualStatement data object := by
  obtain ⟨serial, selected, failure⟩ := fails
  exact ⟨.incrementArithmetic serial selected failure⟩

/-- `lem:pair-system-realizability`, serial alternative: when G's canonical
return system is covered and none of alternatives (i)--(iv) occurs for it, the
covering outcome is alternative (v), so G's canonical serial demand system on
those returns exists. -/
theorem pairSerialDemandSystem_of_noEarlyOutcome
    (covered : PairSystemRealizabilityStatement data object)
    (noEarly : PairSystemNoEarlyOutcomeStatement data object) :
    PairSerialDemandSystemStatement data object := by
  obtain ⟨returns, returnsSelected, ⟨outcome⟩⟩ := covered
  obtain ⟨returns', returnsSelected', noEarly⟩ := noEarly
  have same : returns = returns' :=
    Option.some.inj (returnsSelected.symm.trans returnsSelected')
  subst same
  cases outcome with
  | early early => exact (noEarly ⟨early⟩).elim
  | serial system same =>
      obtain ⟨serial, selected, -⟩ :=
        canonicalPairSerialSystem_spec data object returnsSelected same
      exact ⟨serial, selected⟩

/-- `lem:pair-system-increment-arithmetic`, arithmetic alternative: when G's
canonical serial system is covered and no periodic routed alternative occurs
for it, the covering outcome is the corrected full-modulus arithmetic input. -/
theorem pairSerialArithmetic_of_noEarlyOutcome
    (covered : PairIncrementCoveredStatement data object)
    (noEarly : PairIncrementNoEarlyOutcomeStatement data object) :
    PairSerialArithmeticStatement data object := by
  obtain ⟨serial, serialSelected, ⟨outcome⟩⟩ := covered
  obtain ⟨serial', serialSelected', noEarly⟩ := noEarly
  have same : serial = serial' :=
    Option.some.inj (serialSelected.symm.trans serialSelected')
  subst same
  cases outcome with
  | arithmetic arithmetic => exact ⟨serial, serialSelected, ⟨arithmetic⟩⟩
  | early early => exact (noEarly ⟨early⟩).elim

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
exits of its declared family: only alternative (iv) remains, the first-separator
handoff of that return system's own obstruction. -/
theorem pairObstructionHandoff_of_pairSystemEarlyOutcome
    (early : PairSystemEarlyOutcomeStatement data object)
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (survives : SparseSurplusSurvivorStatement data object) :
    ∃ returns, canonicalPairDemandReturns data object = some returns ∧
      PairObstructionHandoff data object returns := by
  obtain ⟨returns, returnsSelected, ⟨early⟩⟩ := early
  cases early with
  | targetCycle cycle => exact (noCycle cycle).elim
  | targetDefect defect =>
      exact (survives (declaredSparseSurplusExit_of_obstructionDefect returns
        defect)).elim
  | compression support _inside replacement =>
      exact (survives (.compression support replacement)).elim
  | typeB handoff => exact ⟨returns, returnsSelected, handoff⟩

/-- G's canonical serial system is built on G's canonical return system. -/
theorem canonicalPairDemandReturns_of_serial
    {serial : PairSerialDemandSystem data object}
    (selected : canonicalPairSerialSystem data object = some serial) :
    canonicalPairDemandReturns data object = some serial.returns := by
  unfold canonicalPairSerialSystem at selected
  cases hReturns : canonicalPairDemandReturns data object with
  | none => simp [hReturns] at selected
  | some returns =>
      rw [hReturns, Option.bind_some] at selected
      rw [canonicalChoice_spec_of_eq_some selected]

/-- The periodic alternatives of `lem:pair-system-increment-arithmetic` for G's
canonical serial system, on an object surviving the sparse exits of its
declared family: only the first-separator handoff of the serial system's own
obstruction remains. -/
theorem pairObstructionHandoff_of_pairIncrementEarlyOutcome
    (early : PairIncrementEarlyOutcomeStatement data object)
    (survives : SparseSurplusSurvivorStatement data object) :
    ∃ returns, canonicalPairDemandReturns data object = some returns ∧
      PairObstructionHandoff data object returns := by
  obtain ⟨serial, serialSelected, ⟨early⟩⟩ := early
  cases early with
  | targetDefect defect =>
      exact (survives (declaredSparseSurplusExit_of_obstructionDefect
        serial.returns defect)).elim
  | compression support _inside replacement =>
      exact (survives (.compression support replacement)).elim
  | typeB handoff =>
      exact ⟨serial.returns, canonicalPairDemandReturns_of_serial serialSelected,
        handoff⟩

/-- Node `[179]`/`[180]` → `[65]`: the first-separator handoff of G's retained
pair obstruction, on the strict-surplus arm of `[19]`, enters the common Type B
entry at the obstruction's canonical handoff support. -/
theorem typeBFanEntry_of_pairObstructionHandoff
    (above : SurplusAboveStatement data object)
    (handoff : ∃ returns, canonicalPairDemandReturns data object = some returns ∧
      PairObstructionHandoff data object returns) :
    TypeBFanEntryStatement data object := by
  obtain ⟨returns, returnsSelected, core, centres, handoffAt⟩ := handoff
  obtain ⟨⟨core', centres'⟩, selected, handoffAt'⟩ :=
    canonicalChoice_spec (spec := fun support : Finset object.Vertex × Finset object.Vertex =>
      PairObstructionHandoffAt data object returns support.1 support.2)
      ⟨(core, centres), handoffAt⟩
  exact Or.inr ⟨above, Or.inr ⟨returns, returnsSelected, core', centres', selected,
    handoffAt'⟩⟩

end Hypostructure.Graph.Contracts.SurplusPair
