import Hypostructure.Graph.Statements.SurplusPairRouting
import Hypostructure.Graph.Statements.CanonicalPairHandoff

/-!
# Statements: the outcomes of `lem:pair-system-realizability` and
`lem:pair-system-increment-arithmetic` (nodes `[179]`, `[180]`)

The alternatives of the pair-system lemmas for G's canonical return system and
serial system.  Their Type B alternative is the first-separator handoff of the
retained obstruction's own overlap support toward its two demands, at `P₀`
(`PairObstructionHandoff`, `Statements/CanonicalPairHandoff.lean`).

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The response coordinates `r_π` of the pairs of the minimal overlap
obstruction retained by the demand returns, at the obstruction's own
activation: the coordinates alternatives (ii)/(iii) of
`lem:pair-system-realizability` speak about. -/
noncomputable def PairDemandReturns.obstructionCoordinates
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    Finset object.PairCoordinate := by
  classical
  exact (Graph.pairResponseActivation returns.overlap.system.first.active).pairFamily
    (returns.overlap.family.image Subtype.val)

/-- The declared support `X_π` of a pair response coordinate. -/
noncomputable abbrev pairCoordinateSupport {object : Graph.FiniteObject.{u}}
    (coordinate : object.PairCoordinate) : Finset object.Vertex :=
  @Graph.DeclaredSignature.Coordinate.support _ _ object.vertices.decEq coordinate

/-- The already-closed alternatives (i)--(iv) of
`lem:pair-system-realizability` (tex 5110-5130) for the retained return system
of the minimal overlap obstruction: (i) a target cycle; (ii) two of the
obstruction's own response coordinates read on G's piece at their canonical
support are distinguished by G's own surroundings `G − Z` (a target-defective
quotient, clause (b) of `def:named-surplus-exits`, stated about G; empty at a target-avoiding G,
`Graph.not_residualTargetDefect_of_avoids`); (iii) a target-complete proper-support representative inside the
obstruction's overlap support (clause (c) of `def:named-surplus-exits`); (iv) the first nonserial
intersection is a routed bottleneck whose first separator is a high-degree
vertex: the first-separator handoff of the obstruction's own overlap support
toward its two demands, at `P₀` (`PairObstructionHandoff`). -/
inductive PairSystemEarlyOutcome {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) : Type (u + 1) where
  | targetCycle (cycle : Graph.HasCycleWithLength data.LengthOK object)
  | targetDefect (defect : Graph.ResidualTargetDefect
      (Graph.HasCycleWithLength data.LengthOK) object
      returns.obstructionCoordinates pairCoordinateSupport)
  | compression (support : Finset object.Vertex)
      (inside : support ⊆
        returns.overlap.system.overlapSupport returns.overlap.family)
      (replacement : Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)
  | typeB (handoff : PairObstructionHandoff data object returns)

/-- The five alternatives of `lem:pair-system-realizability`, tied to the
literal overlap obstruction read from the ledger. -/
inductive PairSystemRealizabilityOutcome {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) : Type (u + 1) where
  | early (outcome : PairSystemEarlyOutcome returns)
  | serial (system : PairSerialDemandSystem data object)
      (same_returns : system.returns = returns)

/-- The exact arithmetic input of node `[180]`.  Its spectrum is obtained by
the canonical `SerialSystem.System.spectrum` constructor from the graph-realized
node-`[179]` system.  Thus the doubling-orbit theorem is applied to actual
cycles and to its full-modulus/range hypotheses, not to a raw odd projection. -/
structure PairSerialArithmetic {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (serial : PairSerialDemandSystem data object) : Type (u + 1) where
  base : Fin serial.cells → Nat
  base_mem : ∀ index, base index ∈ serial.lengths index
  modulus : Nat
  modulus_neZero : NeZero modulus
  frequent : Finset (Fin serial.cells)
  increment : ∀ index ∈ frequent,
    base index + modulus ∈ serial.lengths index
  smear : Nat
  offsets : ∀ residue ≤ smear, residue ∈ serial.offsets
  wide : smear + 1 ≤ modulus
  criterion : modulus - (smear + 1) < orderOf (2 : ZMod modulus)
  spanning :
    let spectrum := (serial.toSystem.spectrum base base_mem modulus frequent
      increment smear offsets)
    @Graph.SerialSystem.Spectrum.ScaleSpanning spectrum modulus_neZero

namespace PairSerialArithmetic

noncomputable def spectrum {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    {serial : PairSerialDemandSystem data object}
    (arithmetic : PairSerialArithmetic serial) : Graph.SerialSystem.Spectrum :=
  serial.toSystem.spectrum arithmetic.base arithmetic.base_mem
    arithmetic.modulus arithmetic.frequent arithmetic.increment
    arithmetic.smear arithmetic.offsets

end PairSerialArithmetic

/-- The periodic-response alternatives of node `[180]` that are already
routed by the paper (`lem:pair-system-increment-arithmetic`, tex 5207-5220),
for the exact serial system: two equal-residue states distinguished by G's own
surroundings `G − Z` -- a target-defective identification of the obstruction's
own response coordinates (clause (b) of `def:named-surplus-exits`, stated about G; empty at a
target-avoiding G); a target-complete proper representative inside
the overlap support (clause (c) of `def:named-surplus-exits`); or a class reaching a routed bottleneck,
whose first-separator reading is the Type B handoff of the serial system's own
obstruction at `P₀` (`PairObstructionHandoff`). -/
inductive PairIncrementEarlyOutcome {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (serial : PairSerialDemandSystem data object) : Type (u + 1) where
  | targetDefect (defect : Graph.ResidualTargetDefect
      (Graph.HasCycleWithLength data.LengthOK) object
      serial.returns.obstructionCoordinates pairCoordinateSupport)
  | compression (support : Finset object.Vertex)
      (inside : support ⊆ serial.returns.overlap.system.overlapSupport
        serial.returns.overlap.family)
      (replacement : Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)
  | typeB (handoff : PairObstructionHandoff data object serial.returns)

/-- The exhaustive conclusion claimed by
`lem:pair-system-increment-arithmetic`: either the corrected full-modulus
arithmetic applies, or the periodic response has one of its two routed forms. -/
inductive PairIncrementOutcome {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (serial : PairSerialDemandSystem data object) : Type (u + 1) where
  | arithmetic (input : PairSerialArithmetic serial)
  | early (outcome : PairIncrementEarlyOutcome serial)

end Hypostructure.Graph.Strategy.Spine
