import Hypostructure.Graph.Statements.TypeBLanes
import Hypostructure.Graph.Statements.Spine

/-!
# Statements: the mass of the negative hub pieces of the remainder (route 8, key `9803`)

`R` is the remainder of `P₀ = canonicalWindowPacking`, and its canonical pieces `X` are the
components of `G[R]`.  A *negative hub piece* is a canonical piece of `R` with negative net
charge and positive ambient surplus `σ_X > 0`.  For such a piece the Type B residual mass is
`m(X) = |X| + s·σ_X − s·def⁺(X)` (truncated subtraction in `ℕ`), with `s = dischargeScale`,
`F = bridgeMassFactor`.

`Route8HubPieceMassStatement` (key `9803`):

* per piece: `m(X) ≤ F·s·σ_X`;
* summed: `Σ_X m(X) ≤ F·s·Σ_X σ_X`;
* `Σ_X σ_X ≤ σ(R) ≤ σ(G)` (`σ(G) = degreeSurplus threshold`);
* hence `Σ_X m(X) ≤ F·s·σ(G)`, and a fortiori `Σ_X m(X) ≤ 2·F·s·σ(G)`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open scoped BigOperators

universe u

open scoped Classical in
/-- **The negative hub pieces of the remainder of `P₀`**: the canonical pieces `X` of
`R = G − W(P₀)` with negative net charge and positive ambient surplus. -/
noncomputable def route8NegativeHubPieces (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  (object.canonicalPieces remainder).filter fun component =>
    object.NegativeNetCharge (object.pieceSupport remainder component)
        data.threshold data.dischargeScale ∧
      0 < object.ambientSurplus (object.pieceSupport remainder component) data.threshold

/-- **Key `9803`: the hub-piece mass.**  Over the negative hub pieces `X` of the remainder
of `P₀`, with `m(X) = |X| + s·σ_X − s·def⁺(X)` in `ℕ`:
`m(X) ≤ F·s·σ_X` for each piece, `Σ m(X) ≤ F·s·Σ σ_X`, `Σ σ_X ≤ σ(R) ≤ σ(G)`, hence
`Σ m(X) ≤ F·s·σ(G) ≤ 2·F·s·σ(G)`. -/
def Route8HubPieceMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  let hubs := route8NegativeHubPieces data object
  let mass := fun component =>
    (object.pieceSupport remainder component).card +
        data.dischargeScale *
          object.ambientSurplus (object.pieceSupport remainder component) data.threshold -
      data.dischargeScale *
        object.positiveDeficiency (object.pieceSupport remainder component) data.threshold
  (∀ component ∈ hubs,
      mass component ≤
        data.bridgeMassFactor * data.dischargeScale *
          object.ambientSurplus (object.pieceSupport remainder component) data.threshold) ∧
    ∑ component ∈ hubs, mass component ≤
      data.bridgeMassFactor * data.dischargeScale *
        ∑ component ∈ hubs,
          object.ambientSurplus (object.pieceSupport remainder component) data.threshold ∧
    ∑ component ∈ hubs,
        object.ambientSurplus (object.pieceSupport remainder component) data.threshold ≤
      object.ambientSurplus remainder data.threshold ∧
    object.ambientSurplus remainder data.threshold ≤ object.degreeSurplus data.threshold ∧
    ∑ component ∈ hubs, mass component ≤
      data.bridgeMassFactor * data.dischargeScale * object.degreeSurplus data.threshold ∧
    ∑ component ∈ hubs, mass component ≤
      2 * (data.bridgeMassFactor * data.dischargeScale * object.degreeSurplus data.threshold)

end Hypostructure.Graph.Strategy.Spine
