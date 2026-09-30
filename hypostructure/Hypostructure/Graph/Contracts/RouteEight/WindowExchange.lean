import Hypostructure.Graph.Statements.Route8WindowExchange
import Hypostructure.Graph.WindowExchange.DoubleLanding
import Hypostructure.Graph.WindowExchange.Arms
import Hypostructure.Graph.WindowExchange.HeavyPair

/-!
# Contracts: exchanges at one window of `P₀` (keys `9810`–`9812`)

Keys `9810`–`9811` read `canonicalWindowPacking_spec` (`P₀` is a maximum window packing);
keys `9810` and `9812` read G's target avoidance (no cycle of power-of-two length); key
`9812` reads only that the windows of `P₀` are disjoint and avoid `R`.  They instantiate
`WindowExchange.legal_of_double_landing`, `WindowExchange.false_of_two_arms_one_window` and
`WindowExchange.rungCount_le` at G's canonical data.
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

/-- **Key `9812`**: the rung bound for a copy of `X15` with exits on two windows of `P₀`
(`WindowExchange.rungCount_le`: every list of 7, resp. 9, rungs meets a certified cycle of
power-of-two length or a window vertex of degree at least 4). -/
theorem route8X15HeavyPair (data : Parameters) (object : FiniteObject.{u})
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    Route8X15HeavyPairStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  unfold Route8X15HeavyPairStatement
  dsimp only
  intro _ P hP Q hQ PQ p q hp hq cubic e inR x y hx hy hxy a b ex ey
  have out : ∀ M ∈ canonicalWindowPacking data object, ∀ v ∈
      object.remainderSupport (canonicalWindowPacking data object), v ∉ M := fun M hM v hv hvM =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport hv
      (FiniteObject.mem_windowSupport hM hvM)
  exact WindowExchange.rungCount_le avoid lengthLaw (out P hP) (out Q hQ)
    (spec.1.2 P hP Q hQ PQ) hp hq e inR hx hy hxy ex ey cubic

end Hypostructure.Graph.Contracts.RouteEight
