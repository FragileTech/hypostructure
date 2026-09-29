import Hypostructure.Graph.PairArms.Generic

/-!
# Arm B, generic layer, part 2: the serial routes and the exact `[182]` arms

* G6  every route of the serial system closes an actual cycle, so under
      `¬ HasCycle` no realized route length is accepted;
* G7  the exact content of `¬ Nonempty (PairSystemRealizabilityOutcome returns)`
      and of `¬ Nonempty (PairIncrementOutcome serial)` (under `¬ HasCycle`, the
      `2^k` law and `ReplacementExclusion`), as separate facts.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **G6.** Every route choice of a serial system closes an actual simple cycle
of G, so on `¬ HasCycle` no realized route length is accepted. -/
theorem serial_lengths_not_accepted (serial : PairSerialDemandSystem data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (choice : Fin serial.cells → Nat) (mem : ∀ i, choice i ∈ serial.lengths i)
    (offset : Nat) (offMem : offset ∈ serial.offsets) :
    ¬ data.LengthOK (serial.closing + (∑ i, choice i) + offset) := by
  intro ok
  obtain ⟨cycle⟩ := serial.realized_route choice mem offset offMem
  exact avoid ⟨{ vertex := cycle.vertex
                 walk := cycle.walk
                 isCycle := cycle.isCycle
                 length_ok := by rw [cycle.length_eq]; exact ok }⟩

/-- **G7(ii).** The exact content of the `[182]` systemRealizability arm: no
target defect among the obstruction coordinates, no obstruction handoff, no
target cycle, no compression inside `U`, and no serial system on these returns;
hence every disjoint connector-route pair with forward route in `U` is
trivial. -/
theorem realizabilityFails_content (returns : PairDemandReturns data object)
    (fails : ¬ Nonempty (PairSystemRealizabilityOutcome returns)) :
    ¬ Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
        returns.obstructionCoordinates pairCoordinateSupport ∧
      ¬ PairObstructionHandoff data object returns ∧
      (∀ serial : PairSerialDemandSystem data object, serial.returns ≠ returns) ∧
      (∀ routes : PairDemandReturns.ConnectorRoutes returns,
        (∀ v ∈ routes.forward.support,
          v ∈ returns.overlap.system.overlapSupport returns.overlap.family) →
        (∀ v ∈ routes.forward.support, v ∉ routes.backward.support) →
        routes.forward.length = 0 ∧ routes.backward.length = 0) := by
  refine ⟨fun d => fails ⟨.early (.targetDefect d)⟩,
    fun h => fails ⟨.early (.typeB h)⟩,
    fun serial e => fails ⟨.serial serial e⟩, ?_⟩
  intro routes inside disj
  exact disjointRoutes_trivial_of_fails returns fails routes inside disj

/-- **G7(ii), endpoints.** On the systemRealizability arm, a disjoint
connector-route pair with forward route in `U` exists only when the two
demands are one edge in opposite orientations: `d_p.2 = d_q.1`, `d_q.2 = d_p.1`. -/
theorem realizabilityFails_reversed (returns : PairDemandReturns data object)
    (fails : ¬ Nonempty (PairSystemRealizabilityOutcome returns))
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (inside : ∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family)
    (disj : ∀ v ∈ routes.forward.support, v ∉ routes.backward.support) :
    returns.leftDemand.2 = returns.rightDemand.1 ∧
      returns.rightDemand.2 = returns.leftDemand.1 := by
  obtain ⟨f0, b0⟩ := disjointRoutes_trivial_of_fails returns fails routes inside disj
  exact ⟨SimpleGraph.Walk.eq_of_length_eq_zero f0,
    SimpleGraph.Walk.eq_of_length_eq_zero b0⟩

/-- **G7(ii), both ends high.** In that reversed case both ends of the one
edge are centres of selected ports, so both have degree `> δ`. -/
theorem realizabilityFails_reversed_high (returns : PairDemandReturns data object)
    (fails : ¬ Nonempty (PairSystemRealizabilityOutcome returns))
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (inside : ∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family)
    (disj : ∀ v ∈ routes.forward.support, v ∉ routes.backward.support) :
    data.threshold < object.degree returns.leftDemand.1 ∧
      data.threshold < object.degree returns.leftDemand.2 := by
  obtain ⟨e₁, -⟩ := realizabilityFails_reversed returns fails routes inside disj
  refine ⟨object.centre_high_of_mem_excessPorts returns.left_active, ?_⟩
  rw [e₁]
  exact object.centre_high_of_mem_excessPorts returns.right_active

/-- **G7(iii).** The exact content of the `[182]` incrementArithmetic arm: no
target defect among the serial system's obstruction coordinates and no handoff
of its obstruction (the arithmetic arm is excluded by `¬ HasCycle` and is not
recorded). -/
theorem incrementFails_content (serial : PairSerialDemandSystem data object)
    (fails : ¬ Nonempty (PairIncrementOutcome serial)) :
    ¬ Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
        serial.returns.obstructionCoordinates pairCoordinateSupport ∧
      ¬ PairObstructionHandoff data object serial.returns :=
  ⟨fun d => fails ⟨.early (.targetDefect d)⟩, fun h => fails ⟨.early (.typeB h)⟩⟩

end Hypostructure.Graph.PairArms
