import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap
import Hypostructure.Graph.Statements.PairCorrelation

/-!
# Contract lemmas: the three coverage tests of `[178]`--`[180]` decided at G

Each test of the pair-code chain is restated about G's canonical objects.  Its
arms that cannot hold at G are empty there, so the test reduces to the arm that
can:

* `[178]`: the test is decided at G's canonical minimal obstruction `F₀`
  (`PairOverlapSystem.ConditionalFactorization`); its failure has the exact
  shape of `PairOverlapSystem.not_conditionalFactorization_iff` -- a product
  failure among mutually non-overlapping response supports.
* `[179]`: the target-cycle alternative is empty at G, so coverage is exactly
  the Type B handoff of the retained return system or a serial demand system
  on it.
* `[180]`: the arithmetic arm is empty at G (it would produce an accepted cycle
  of G), so coverage is exactly the Type B handoff of the serial system's
  returns.

None of the statements mentions keys, ledgers, branches or node numbers.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[180]`, arithmetic arm: at G's canonical serial system there is no
full-modulus arithmetic input, since it would produce an accepted cycle of G. -/
theorem not_pairSerialArithmetic_of_avoids
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length)
    {serial : PairSerialDemandSystem data object}
    (selected : canonicalPairSerialSystem data object = some serial) :
    ¬ Nonempty (PairSerialArithmetic serial) := by
  rintro ⟨input⟩
  exact avoids (pairPowerOfTwoCycle_of_arithmetic
    ⟨serial, selected, ⟨input⟩⟩ lengthOK_iff)

/-- Node `[179]`, decided at G: for G's return system, coverage of
`lem:pair-system-realizability` is exactly the Type B handoff of the retained
obstruction or a serial demand system on those returns.  The target cycle
alternative is empty at G. -/
theorem pairSystemRealizabilityOutcome_iff
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (returns : PairDemandReturns data object) :
    Nonempty (PairSystemRealizabilityOutcome returns) ↔
      PairObstructionHandoff data object returns ∨
        ∃ serial : PairSerialDemandSystem data object, serial.returns = returns := by
  constructor
  · rintro ⟨outcome⟩
    cases outcome with
    | early early =>
        cases early with
        | targetCycle cycle => exact (avoids cycle).elim
        | typeB handoff => exact Or.inl handoff
    | serial system same => exact Or.inr ⟨system, same⟩
  · rintro (handoff | ⟨serial, same⟩)
    · exact ⟨.early (.typeB handoff)⟩
    · exact ⟨.serial serial same⟩

/-- Node `[179]`, the failed coverage in G-form: no Type B handoff of the
retained obstruction and no serial demand system on G's return system. -/
theorem not_pairSystemRealizabilityOutcome_iff
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (returns : PairDemandReturns data object) :
    ¬ Nonempty (PairSystemRealizabilityOutcome returns) ↔
      ¬ PairObstructionHandoff data object returns ∧
        ∀ serial : PairSerialDemandSystem data object, serial.returns ≠ returns := by
  rw [not_congr (pairSystemRealizabilityOutcome_iff avoids returns)]
  push Not
  exact Iff.rfl

/-- Node `[180]`, decided at G: for G's canonical serial system, coverage of
`lem:pair-system-increment-arithmetic` is exactly the Type B handoff of the
serial system's returns.  The arithmetic arm is empty at G
(`not_pairSerialArithmetic_of_avoids`). -/
theorem pairIncrementOutcome_iff_handoff
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length)
    {serial : PairSerialDemandSystem data object}
    (selected : canonicalPairSerialSystem data object = some serial) :
    Nonempty (PairIncrementOutcome serial) ↔
      PairObstructionHandoff data object serial.returns := by
  constructor
  · rintro ⟨outcome⟩
    cases outcome with
    | arithmetic input =>
        exact (not_pairSerialArithmetic_of_avoids avoids lengthOK_iff selected
          ⟨input⟩).elim
    | early early =>
        cases early with
        | typeB handoff => exact handoff
  · intro handoff
    exact ⟨.early (.typeB handoff)⟩

/-- Node `[178]`, the failed factorization in G-form: at G's canonical overlap
system, the canonical minimal obstruction `F₀` has pairwise separated response
supports, or splits into two nonempty blocks with no cross-overlap, each
realized.  Either way it is a product failure among mutually non-overlapping
response supports. -/
theorem pairFactorizationFails_shape
    (fails : PairFactorizationFailsStatement data object)
    (system : PairOverlapSystemStatement data object) :
    ∃ system : PairOverlapSystem data object,
      canonicalPairOverlapSystem data object = some system ∧
      (system.PairwiseSeparated system.obstructionFamily ∨
        ∃ left right, left.Nonempty ∧ right.Nonempty ∧ Disjoint left right ∧
          system.familyUnion left right = system.obstructionFamily ∧
          (∀ leftPair, leftPair ∈ left → ∀ rightPair, rightPair ∈ right →
            ¬ system.overlaps leftPair rightPair) ∧
          system.realizingOrder left ∧ system.realizingOrder right) := by
  obtain ⟨system, selected⟩ := system
  exact ⟨system, selected, (system.not_conditionalFactorization_iff).1
    fun factorization => fails ⟨system, selected, factorization⟩⟩

/-- Nodes `[179]`--`[180]`, coverage decided at G, as one fact about G's canonical
return system and canonical serial system. -/
theorem pairCoverage_of_demandReturns
    (returns : PairDemandReturnsStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    PairCoverageStatement data object := by
  obtain ⟨returns, selected⟩ := returns
  exact ⟨returns, selected, pairSystemRealizabilityOutcome_iff avoids returns,
    fun serial serialSelected =>
      ⟨not_pairSerialArithmetic_of_avoids avoids lengthOK_iff serialSelected,
        pairIncrementOutcome_iff_handoff avoids lengthOK_iff serialSelected⟩⟩

/-- Node `[180]`: at G's canonical serial system the full-modulus arithmetic built
from the serial system's own increments (Frobenius filling of the central range)
does not hold: it would realize a power of two, an accepted cycle of G. -/
theorem pairFullModulus_of_serial
    (serial : PairSerialDemandSystemStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    PairFullModulusStatement data object := by
  obtain ⟨serial, selected⟩ := serial
  refine ⟨serial, selected, fun arithmetic => ?_⟩
  obtain ⟨exponent, realized⟩ := arithmetic.exists_pow_realized
  let cycle := Classical.choice realized
  have threeLe : 3 ≤ 2 ^ exponent := by
    rw [← cycle.length_eq]
    exact cycle.isCycle.three_le_length
  have exponentLower : 2 ≤ exponent := by
    by_contra lower
    have cases : exponent = 0 ∨ exponent = 1 := by omega
    rcases cases with zero | one
    · have powerEq : 2 ^ exponent = 1 := by simp [zero]
      omega
    · have powerEq : 2 ^ exponent = 2 := by simp [one]
      omega
  have accepted : data.LengthOK (2 ^ exponent) :=
    (lengthOK_iff (2 ^ exponent)).2
      (Core.DyadicLength.powerOfTwoLength_of_exists ⟨exponent, exponentLower, rfl⟩)
  exact avoids ⟨{ vertex := cycle.vertex
                  walk := cycle.walk
                  isCycle := cycle.isCycle
                  length_ok := by simpa [cycle.length_eq] using accepted }⟩

end Hypostructure.Graph.Contracts.SurplusPair
