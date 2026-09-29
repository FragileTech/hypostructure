import Hypostructure.Graph.Statements.Route8PackingExchange
import Hypostructure.Graph.PackingExchange

/-!
# Contracts: exchange at the maximum packing `P₀` (keys `9800`–`9802`)

All three facts read only `canonicalWindowPacking_spec` (`P₀` is a maximum window packing)
and instantiate the generic `PackingExchange` lemmas at G's canonical data.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Key `9800`**: the `k`-fold exchange (`PackingExchange.card_le_of_subset_union_remainder`
at `P₀`). -/
theorem route8PackingExchange (data : Parameters) (object : FiniteObject.{u}) :
    Route8PackingExchangeStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  unfold Route8PackingExchangeStatement
  dsimp only
  intro Q sub W packed inside
  exact PackingExchange.card_le_of_subset_union_remainder data.windowOrder_pos spec.1
    spec.2.1 sub packed inside

/-- **Key `9801`**: arm exchange, `PackingExchange.false_of_two_arm_segments` at `P₀`:
`α ∪ p[lx, lx+mx]` and `β ∪ p[ly, ly+my]` are two disjoint windows inside `P ∪ R`. -/
theorem route8ArmExchange (data : Parameters) (object : FiniteObject.{u}) :
    Route8ArmExchangeStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  unfold Route8ArmExchangeStatement
  dsimp only
  intro P hP p hp a b α β hα hβ αβ i j lx mx ly my bx byy ei ej sep sx sy ex ey onlyx onlyy
  exact PackingExchange.false_of_two_arm_segments data.windowOrder_pos spec.1 spec.2.1 hP hp
    hα hβ αβ i j lx mx ly my bx byy ei ej sep sx sy ex ey onlyx onlyy

/-- **Key `9802`**: full arms landing on two distinct positions of one window intersect —
key `9801` with the singleton runs `{i}`, `{j}`. -/
theorem route8FullArmLandingCap (data : Parameters) (object : FiniteObject.{u}) :
    Route8FullArmLandingCapStatement data object := by
  have arm := route8ArmExchange data object
  unfold Route8ArmExchangeStatement at arm
  unfold Route8FullArmLandingCapStatement
  dsimp only at arm ⊢
  intro P hP p hp a α β size hα hβ i j ij ex ey onlyx onlyy
  by_contra meet
  have none : ∀ k k', α k ≠ β k' := fun k k' e => meet ⟨k, k', e⟩
  have ij' : i.1 ≠ j.1 := fun e => ij (Fin.ext e)
  exact arm P hP p hp a a α β hα hβ none i j i.1 0 j.1 0 (by omega) (by omega)
    (Or.inl rfl) (Or.inl rfl) (by omega) (by omega) (by omega) ex ey
    (fun k t h1 h2 adj => by
      have et : t = i := Fin.ext (by omega)
      subst et
      exact ⟨onlyx k adj, rfl⟩)
    (fun k t h1 h2 adj => by
      have et : t = j := Fin.ext (by omega)
      subst et
      exact ⟨onlyy k adj, rfl⟩)

end Hypostructure.Graph.Contracts.RouteEight
