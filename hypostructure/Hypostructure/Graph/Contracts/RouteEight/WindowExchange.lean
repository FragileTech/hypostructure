import Hypostructure.Graph.Statements.Route8WindowExchange
import Hypostructure.Graph.WindowExchange.DoubleLanding
import Hypostructure.Graph.WindowExchange.Arms

/-!
# Contracts: exchanges at one window of `P₀` (keys `9810`–`9811`)

Both facts read `canonicalWindowPacking_spec` (`P₀` is a maximum window packing); key `9810`
also reads G's target avoidance (no cycle of power-of-two length).  They instantiate
`WindowExchange.legal_of_double_landing` and `WindowExchange.false_of_two_arms_one_window` at
G's canonical data.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Key `9810`**: legal double landings of `X15` on one window of `P₀`
(`WindowExchange.legal_of_double_landing`: a forbidden cycle of the configuration, or two
disjoint windows inside `P ∪ R` against the exchange with `Q = {P}`). -/
theorem route8X15DoubleLanding (data : Parameters) (object : FiniteObject.{u})
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    Route8X15DoubleLandingStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  unfold Route8X15DoubleLandingStatement
  dsimp only
  intro order P hP p hp e inR a b ha hb hab i j land
  have valid : object.IsWindowPacking 13 (canonicalWindowPacking data object) :=
    order ▸ spec.1
  have maximum : (canonicalWindowPacking data object).card = object.windowPackingNumber 13 :=
    order ▸ spec.2.1
  have legal := WindowExchange.legal_of_double_landing avoid lengthLaw valid maximum hP hp e
    inR ha hb hab i j land
  unfold WindowExchange.dlLegal at legal
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem,
    decide_eq_true_eq] at legal
  exact legal

/-- **Key `9811`**: two arms on one window of `P₀` at positions `i < j`, of lengths at least
`(order − 1 − i, j)`, trigger (`WindowExchange.false_of_two_arms_one_window`). -/
theorem route8ArmPairTrigger (data : Parameters) (object : FiniteObject.{u}) :
    Route8ArmPairTriggerStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  unfold Route8ArmPairTriggerStatement
  dsimp only
  intro P hP p hp a b α β hα hβ αβ i j ij longα longβ ex ey onlyx onlyy
  exact WindowExchange.false_of_two_arms_one_window data.windowOrder_pos spec.1 spec.2.1 hP hp
    hα hβ αβ i j ij longα longβ ex ey onlyx onlyy

end Hypostructure.Graph.Contracts.RouteEight
