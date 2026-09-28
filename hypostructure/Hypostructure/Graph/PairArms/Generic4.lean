import Hypostructure.Graph.PairArms.Generic3

/-!
# Arm B, generic layer, part 4: the demand ends and `U`

* G10 `serialOfPiece`: the piece of a serial system need NOT be the connector's
      forward route.  Any path `P : d_p.2 ⇝ d_q.1` inside `U` that is
      vertex-disjoint from the backward route of some connector-route pair, and
      not both trivial, builds a one-cell serial system.
* G11 every serial system on `returns` has both demand ends `d_p.2`, `d_q.1`
      in `U` (its first piece starts at `d_p.2`, its last piece ends at `d_q.1`,
      and pieces lie in `U`); so if an end is outside `U` there is no serial
      system at all on these returns.
* G12 on the systemRealizability arm under slack independence, EVERY path in `U`
      from `d_p.2` to `d_q.1` meets EVERY backward connector route; and when both
      ends are in `U` such a path exists (`U` is connected).
* G13 under slack independence and the baseline, each demand end `d.2` of a
      selected port has degree exactly `δ` (its centre is above `δ`).
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **G10.** One-cell serial system from a `U`-path disjoint from a backward
connector route. -/
noncomputable def serialOfPiece (returns : PairDemandReturns data object)
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (P : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1)
    (hP : P.IsPath)
    (inside : ∀ v ∈ P.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family)
    (disj : ∀ v ∈ P.support, v ∉ routes.backward.support)
    (pos : 0 < P.length + routes.backward.length) :
    PairSerialDemandSystem data object :=
  let interfaces : Fin 2 → object.Vertex := fun j =>
    if j.val = 0 then returns.leftDemand.2 else returns.rightDemand.1
  have h₁ : ∀ i : Fin 1, returns.leftDemand.2 = interfaces i.castSucc := by
    intro i
    have : (i.castSucc : Fin 2).val = 0 := by
      have := i.isLt; simp only [Fin.coe_castSucc]; omega
    simp only [interfaces, this, if_true]
  have h₂ : ∀ i : Fin 1, returns.rightDemand.1 = interfaces i.succ := by
    intro i
    have : (i.succ : Fin 2).val ≠ 0 := by simp
    simp only [interfaces, this, if_false]
  { returns := returns
    cells := 1
    cells_pos := Nat.one_pos
    interfaces := interfaces
    lengths := fun _ => {P.length}
    lengths_nonempty := fun _ => Finset.singleton_nonempty _
    piece := fun i _ _ => P.copy (h₁ i) (h₂ i)
    piece_isPath := fun i _ _ => by
      rw [SimpleGraph.Walk.isPath_copy]; exact hP
    piece_length := fun i length member => by
      rw [SimpleGraph.Walk.length_copy]; exact (Finset.mem_singleton.mp member).symm
    piece_inside := fun i _ _ v hv => by
      rw [SimpleGraph.Walk.support_copy] at hv; exact inside v hv
    cell_internal_disjoint := fun i left leftMem right rightMem ne => by
      exact absurd ((Finset.mem_singleton.mp leftMem).trans
        (Finset.mem_singleton.mp rightMem).symm) ne
    cells_internal_disjoint := fun l r ne => by
      exact absurd (Subsingleton.elim l r) ne
    routes := routes
    start_eq := by simp [interfaces]
    end_eq := by simp [interfaces]
    closing := routes.backward.length + 2
    closing_eq := rfl
    closing_internal_disjoint := fun i _ _ v hb hp => by
      rw [SimpleGraph.Walk.support_copy] at hp; exact disj v hp hb
    offsets := {0}
    offsets_nonempty := Finset.singleton_nonempty _
    increments_bounded := fun i left leftMem right rightMem => by
      rw [Finset.mem_singleton.mp leftMem, Finset.mem_singleton.mp rightMem,
        Nat.dist_self]
      exact Nat.zero_le _
    realized_route := fun choice mem offset offMem => by
      have c0 : choice 0 = P.length := Finset.mem_singleton.mp (mem 0)
      have o0 : offset = 0 := Finset.mem_singleton.mp offMem
      rw [Fin.sum_univ_one, c0, o0]
      exact ⟨{ vertex := returns.leftDemand.1
               walk := SimpleGraph.Walk.cons returns.leftDemand_adj
                 (P.append
                   (SimpleGraph.Walk.cons returns.rightDemand_adj routes.backward))
               isCycle := cycle_of_disjoint _ _ _ _ hP routes.backward_isPath disj pos
               length_eq := by
                 simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append]
                 omega }⟩ }

/-- **G11.** Both demand ends of every serial system lie in `U`. -/
theorem serial_ends_mem (serial : PairSerialDemandSystem data object) :
    serial.returns.leftDemand.2 ∈
        serial.returns.overlap.system.overlapSupport serial.returns.overlap.family ∧
      serial.returns.rightDemand.1 ∈
        serial.returns.overlap.system.overlapSupport serial.returns.overlap.family := by
  constructor
  · let i : Fin serial.cells := ⟨0, serial.cells_pos⟩
    obtain ⟨ℓ, hℓ⟩ := serial.lengths_nonempty i
    have hstart := (serial.piece i ℓ hℓ).start_mem_support
    have e : serial.interfaces i.castSucc = serial.returns.leftDemand.2 := by
      rw [← serial.start_eq]; rfl
    have m := serial.piece_inside i ℓ hℓ _ hstart
    rw [e] at m
    exact m
  · let i : Fin serial.cells := ⟨serial.cells - 1, by have := serial.cells_pos; omega⟩
    obtain ⟨ℓ, hℓ⟩ := serial.lengths_nonempty i
    have hend := (serial.piece i ℓ hℓ).end_mem_support
    have e : serial.interfaces i.succ = serial.returns.rightDemand.1 := by
      rw [← serial.end_eq]
      congr 1
      ext
      simp only [i, Fin.val_succ, Fin.val_last]
      have := serial.cells_pos
      omega
    have m := serial.piece_inside i ℓ hℓ _ hend
    rw [e] at m
    exact m

/-- **G11, contrapositive.** An end outside `U` rules out every serial system on
these returns. -/
theorem noSerial_of_end_outside (returns : PairDemandReturns data object)
    (outside : returns.leftDemand.2 ∉
        returns.overlap.system.overlapSupport returns.overlap.family ∨
      returns.rightDemand.1 ∉
        returns.overlap.system.overlapSupport returns.overlap.family)
    (serial : PairSerialDemandSystem data object) : serial.returns ≠ returns := by
  rintro rfl
  obtain ⟨h₁, h₂⟩ := serial_ends_mem serial
  rcases outside with o | o
  · exact o h₁
  · exact o h₂

/-- **G12.** On the systemRealizability arm, under slack independence, every
path inside `U` from `d_p.2` to `d_q.1` meets every backward connector route. -/
theorem realizabilityFails_path_meets (returns : PairDemandReturns data object)
    (slack : SlackIndependentStatement data object)
    (fails : ¬ Nonempty (PairSystemRealizabilityOutcome returns))
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (P : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1)
    (hP : P.IsPath)
    (inside : ∀ v ∈ P.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family) :
    ∃ v ∈ P.support, v ∈ routes.backward.support := by
  by_contra h
  push_neg at h
  by_cases pos : 0 < P.length + routes.backward.length
  · exact fails ⟨.serial (serialOfPiece returns routes P hP inside h pos) rfl⟩
  · have hP0 : P.length = 0 := by omega
    have e := SimpleGraph.Walk.eq_of_length_eq_zero hP0
    have high₁ := object.centre_high_of_mem_excessPorts returns.left_active
    have high₂ := object.centre_high_of_mem_excessPorts returns.right_active
    rw [← e] at high₂
    exact slack _ _ high₁ high₂ returns.leftDemand_adj

/-- **G12, existence.** When both demand ends are in `U`, a path inside `U`
joins them (`U` is connected). -/
theorem exists_U_path (returns : PairDemandReturns data object)
    (h₁ : returns.leftDemand.2 ∈
        returns.overlap.system.overlapSupport returns.overlap.family)
    (h₂ : returns.rightDemand.1 ∈
        returns.overlap.system.overlapSupport returns.overlap.family) :
    ∃ P : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1, P.IsPath ∧
      ∀ v ∈ P.support, v ∈ returns.overlap.system.overlapSupport returns.overlap.family :=
  returns.overlap.connected.2 h₁ h₂

/-- **G13.** A selected port's endpoint has degree exactly `δ`, under slack
independence and the baseline. -/
theorem port_end_degree {d : object.Vertex × object.Vertex}
    (active : d ∈ object.excessPorts data.threshold)
    (slack : SlackIndependentStatement data object)
    (baseline : ∀ v, data.threshold ≤ object.degree v) :
    object.degree d.2 = data.threshold := by
  have hc := object.centre_high_of_mem_excessPorts active
  have adj := object.adj_of_mem_excessPorts active
  have := baseline d.2
  by_contra ne
  exact slack _ _ hc (by omega) adj

end Hypostructure.Graph.PairArms
