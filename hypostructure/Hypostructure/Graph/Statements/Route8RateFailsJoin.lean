import Hypostructure.Graph.Statements.DensityOrder
import Hypostructure.Graph.WindowJoinIdentity
import Hypostructure.Graph.NetCharge

/-!
# Statements: the failed private-carrier rate with the cross-window incidences

`Graph.Route8Census.Rate` fails at G's canonical packing `P₀`.  Its supply is
the cut `|∂R| = e(R,W)` of G's remainder, and node `[146]`'s no arm
(`densityOrderLower_of_coldRoute8AtOrAbove`) bounds that cut by `β·p + T(n)`
alone, which forgets the cross-window incidences `2e_×(W)` of `P₀`.  This
statement keeps them: it is the exact window-join identity at `P₀`
(`lem:exact-window-join-identity`), and the failed rate read against it.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The failed rate against the exact window join, at G's canonical packing.**
With `p = |P₀|`, `X = |I_×(W)| = 2e_×(W)` the cross-window incidences of `P₀`,
and `e(R,W) = |∂R|`:

* the exact join identity `e(R,W) + 2(order − 1)p + X = δ·order·p + σ_W`;
* the failed rate `(δs+1)·e(R,W) + δ·F·s·T(n) ≥ δ·|R|` with `e(R,W)` replaced
  by the join identity:

  `δ·n + (δs+1)·X ≤ A·p + (δs+1)·σ_W + δ·F·s·T(n)`   (`A = 234` at the
  registered presentation), the `[146]`-no lower bound with the cross-window
  term kept and G's own window surplus `σ_W` in place of its ceiling. -/
noncomputable def Route8RateFailsJoinStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let cross := (object.crossWindowIncidences packing).card
  (object.boundaryIncidence (object.remainderSupport packing) +
      (2 * (data.windowOrder - 1) * packing.card + cross) =
    data.threshold * (data.windowOrder * packing.card) +
      object.ambientSurplus (object.windowSupport packing) data.threshold) ∧
  data.threshold * object.vertexCount +
      (data.threshold * data.dischargeScale + 1) * cross ≤
    densityOrderPackingCoeff data * packing.card +
      (data.threshold * data.dischargeScale + 1) *
        object.ambientSurplus (object.windowSupport packing) data.threshold +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount)

/-- **The failed rate on the connected pieces of G's remainder** (`H03`, the
connected negative support of `prop:negative-net-charge`, read at the rate).
The canonical pieces of `R = V(G) − W(P₀)` (the components of `G[R]`) partition
both currencies of the rate exactly, `Σ_i |X_i| = |R|` and
`Σ_i |∂X_i| = |∂R|` (a vertex of a piece has the same neighbours in the piece
as in `R`), and when `R` is nonempty the failed rate leaves a piece whose own
rate charge is nonpositive up to its equal share of the slack:

  `m·δ·|X| ≤ m·(δs+1)·|∂X| + δ·F·s·T(n)`,   `m` the number of pieces. -/
noncomputable def Route8RateFailsPieceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let pieces := object.canonicalPieces remainder
  (∑ piece ∈ pieces, (object.pieceSupport remainder piece).card = remainder.card) ∧
  (∑ piece ∈ pieces, object.boundaryIncidence (object.pieceSupport remainder piece) =
    object.boundaryIncidence remainder) ∧
  (remainder.Nonempty →
    ∃ piece ∈ pieces,
      pieces.card * (data.threshold * (object.pieceSupport remainder piece).card) ≤
        pieces.card * ((data.threshold * data.dischargeScale + 1) *
          object.boundaryIncidence (object.pieceSupport remainder piece)) +
        data.threshold * (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount))

/-- **The cross-window incidences against the density cap, at G.**  The failed
rate against the join (`Route8RateFailsJoinStatement`) and the density cap
`2·rate·log₂n·p ≤ (log₂n+1)(δn+T) + densitySlack·rate·log₂n·T` combine at
`P₀` into the `[146]`-no combined order bound with the cross-window term kept
on the left:

  `2·r·L·(δ·n + (δs+1)·X) ≤ A·((L+1)(δ·n+T)) + L·T·(A·S + 2·r·D)`. -/
noncomputable def Route8RateFailsCrossBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  2 * data.windowRate * Nat.log2 object.vertexCount *
      (data.threshold * object.vertexCount +
        (data.threshold * data.dischargeScale + 1) *
          (object.crossWindowIncidences (canonicalWindowPacking data object)).card) ≤
    densityOrderPackingCoeff data *
        ((Nat.log2 object.vertexCount + 1) *
          (data.threshold * object.vertexCount +
            data.surplusThreshold object.vertexCount)) +
      Nat.log2 object.vertexCount * data.surplusThreshold object.vertexCount *
        (densityOrderPackingCoeff data * boundedDensityOrderSlack data +
          2 * data.windowRate * densityOrderSurplusCoeff data)

end Hypostructure.Graph.Strategy.Spine
