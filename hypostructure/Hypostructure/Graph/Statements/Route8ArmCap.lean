import Hypostructure.Graph.Statements.Route8BlobStructure
import Hypostructure.Graph.CleanLanding

/-!
# Statements: the net-cap excess, clean landings, and the arm-closure residual (keys `9804`–`9807`)

`P₀ = canonicalWindowPacking` (maximum), `R` its remainder, `X` the canonical pieces of `G[R]`,
`E(X) = |cutEdges X|`, `δ = threshold`, `s = dischargeScale`, `a = δs + 1`,
`slack = F·s·T(n)` (as in key `9902`), and
`L = s·(δ·W·p + spine·⌈√n⌉) − s·2(W−1)·p` the right-hand gap of the net-deficiency cap
(key `222`, `W = windowOrder`, `p = |P₀|`).  The excess of a piece is
`δ(X) = |X| − s·E(X)` (in `ℤ`).  A *long landing* of `X` on a placed window `(P, p)` is a clean
`(W−2)`- or `(W−1)`-landing (`PackingExchange.LongLanding`).

* `Route8NetCapExcessStatement` (key `9804`): under `SufficientlyLargeForNetCap`,
  `L + s·δ·slack < a·(|R| − s·|∂R|)`.  At `spineData` (`δ = 3`, `s = 4`, `W = 13`, `F = 8`):
  `13·(|R| − 4|∂R|) > 60p + 384T + K`.
* `Route8CleanLandingRulesStatement` (key `9805`): on each placed window of `P₀`, long landings
  of distinct pieces land at one position, or at `{0,1}`, or at `{W−2, W−1}`; and two clean
  landings of distinct pieces at one position `p e` with `a + b ≥ W − 1` exclude a clean landing
  of a third piece with a run of complementary size avoiding `e`.
* `Route8CleanLandingCapStatement` (key `9806`): `Λ(P) ≤ (δ − 1) + σ_P` per placed window
  (`Λ(P)` = pieces with a long landing on `(P, p)`, `σ_P = Σ_{v∈P}(d(v) − δ)`), and for every
  placement system of `P₀`, `Σ_P Λ(P) ≤ (δ − 1)·p + σ_W`.
* `Route8ArmClosureResidualStatement` (key `9807`): for every placement system and every
  `c`, `L + s·δ·slack − c·((δ−1)·p + σ_W) < Σ_{X : δ(X) > 0} (a·δ(X) − c·ν(X))`, with
  `ν(X)` the windows of `P₀` on which `X` has a long landing.  At `spineData`, `c = 30`:
  `384T + K − 30σ_W < Σ_{δ(X)>0} (13δ(X) − 30ν(X))`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open scoped BigOperators

universe u

/-- **Key `9804`: the net-cap excess.**  Under `SufficientlyLargeForNetCap`,
`L + s·δ·slack < (δs+1)·(|R| − s·|∂R|)` in `ℤ`, with `L` the right-hand gap of key `222`. -/
noncomputable def Route8NetCapExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let slack := data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount
  Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
      data.dischargeScale data.windowOrder data.windowRate
      data.spineScale data.densitySlack object.vertexCount →
    ((data.dischargeScale *
          (data.threshold * (data.windowOrder * packing.card) +
            data.spineScale * Core.ceilSqrt object.vertexCount) : Nat) : ℤ) -
        ((data.dischargeScale * (2 * (data.windowOrder - 1) * packing.card) : Nat) : ℤ) +
        ((data.dischargeScale * data.threshold * slack : Nat) : ℤ) <
      ((data.threshold * data.dischargeScale + 1 : Nat) : ℤ) *
        ((remainder.card : ℤ) -
          (data.dischargeScale : ℤ) * (Graph.Route8.cutEdges object remainder).card)

/-- **Key `9805`: the landing rules on a window of `P₀`** (`4 ≤ W`).  For every window `P ∈ P₀`
with a placement `p`:

* (pair) long landings `x ∈ X`, `y ∈ Y` of distinct pieces at positions `i`, `j` satisfy
  `i = j`, or `{i, j} = {0, 1}` (`i + j = 1`), or `{i, j} = {W−2, W−1}` (`i + j + 3 = 2W`);
* (triple) for pairwise distinct pieces `X, Y, Z`, clean `a`- and `b`-landings of `X`, `Y` at
  one position `e` (`a, b ≤ W − 1`, `a + b ≥ W − 1`) and a clean `c`-landing of `Z` at `k` with
  a run `[l, l+m]` (`k` an end, `c + m + 1 = W`) avoiding `e` do not coexist. -/
def Route8CleanLandingRulesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let pieces := object.canonicalPieces remainder
  4 ≤ data.windowOrder →
  ∀ P ∈ packing, ∀ p : Fin data.windowOrder → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    (∀ X ∈ pieces, ∀ Y ∈ pieces, X ≠ Y →
      ∀ (i j : Fin data.windowOrder) (x y : object.Vertex),
        Graph.PackingExchange.LongLanding object (object.pieceSupport remainder X) p i x →
        Graph.PackingExchange.LongLanding object (object.pieceSupport remainder Y) p j y →
        i = j ∨ i.1 + j.1 = 1 ∨ i.1 + j.1 + 3 = 2 * data.windowOrder) ∧
    (∀ X ∈ pieces, ∀ Y ∈ pieces, ∀ Z ∈ pieces, X ≠ Y → X ≠ Z → Y ≠ Z →
      ∀ (e k : Fin data.windowOrder) (x y z : object.Vertex) (a b c l m : Nat),
        Graph.PackingExchange.CleanLanding object (object.pieceSupport remainder X) p e x a →
        Graph.PackingExchange.CleanLanding object (object.pieceSupport remainder Y) p e y b →
        a + 1 ≤ data.windowOrder → b + 1 ≤ data.windowOrder → data.windowOrder ≤ a + b + 1 →
        Graph.PackingExchange.CleanLanding object (object.pieceSupport remainder Z) p k z c →
        l + m < data.windowOrder → (k.1 = l ∨ k.1 = l + m) → c + (m + 1) = data.windowOrder →
        (e.1 < l ∨ l + m < e.1) → False)

open scoped Classical in
/-- `Λ(P, p)`: the canonical pieces of `R` with a long landing on the placed window `(P, p)`. -/
noncomputable def route8LongLandingCount (data : Parameters) (object : Graph.FiniteObject.{u})
    (p : Fin data.windowOrder → object.Vertex) : Nat :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ((object.canonicalPieces remainder).filter fun X =>
    ∃ i x, Graph.PackingExchange.LongLanding object (object.pieceSupport remainder X) p i x).card

open scoped Classical in
/-- `ν(X)`: the windows of `P₀`, placed by `place`, on which the piece `X` has a long
landing. -/
noncomputable def route8LongLandingWindows (data : Parameters) (object : Graph.FiniteObject.{u})
    (place : Finset object.Vertex → Fin data.windowOrder → object.Vertex)
    (X : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) : Nat :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ((canonicalWindowPacking data object).filter fun P =>
    ∃ i x, Graph.PackingExchange.LongLanding object (object.pieceSupport remainder X)
      (place P) i x).card

/-- **Key `9806`: the clean-landing cap** (`4 ≤ W`).  Per placed window of `P₀`,
`Λ(P, p) ≤ (δ − 1) + σ_P`; and for every placement system `place` of `P₀`,
`Σ_{P ∈ P₀} Λ(P, place P) ≤ (δ − 1)·|P₀| + σ_W` (`σ_W` the ambient surplus of the covered
support). -/
noncomputable def Route8CleanLandingCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  4 ≤ data.windowOrder →
  (∀ P ∈ packing, ∀ p : Fin data.windowOrder → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    route8LongLandingCount data object p ≤
      (data.threshold - 1) + object.ambientSurplus P data.threshold) ∧
  ∀ place : Finset object.Vertex → Fin data.windowOrder → object.Vertex,
    (∀ P ∈ packing, Graph.LocalRigidity.IsWindowPlacement object P (place P)) →
    ∑ P ∈ packing, route8LongLandingCount data object (place P) ≤
      (data.threshold - 1) * packing.card +
        object.ambientSurplus (Graph.FiniteObject.windowSupport packing) data.threshold

open scoped Classical in
/-- **Key `9807`: the arm-closure residual** (`4 ≤ W`, `SufficientlyLargeForNetCap`).  For
every placement system `place` of `P₀` and every `c`,
`L + s·δ·slack − c·((δ−1)·|P₀| + σ_W) < Σ_{X : δ(X) > 0} (a·δ(X) − c·ν(X))`
with `δ(X) = |X| − s·E(X)` and `ν(X)` the windows of `P₀` on which `X` has a long landing.
At `spineData` with `c = 30`: `384T + K − 30σ_W < Σ_{δ(X)>0} (13δ(X) − 30ν(X))`. -/
noncomputable def Route8ArmClosureResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let pieces := object.canonicalPieces remainder
  let slack := data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount
  let excess := fun X => ((object.pieceSupport remainder X).card : ℤ) -
    (data.dischargeScale : ℤ) *
      (Graph.Route8.cutEdges object (object.pieceSupport remainder X)).card
  4 ≤ data.windowOrder →
  Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
      data.dischargeScale data.windowOrder data.windowRate
      data.spineScale data.densitySlack object.vertexCount →
  ∀ place : Finset object.Vertex → Fin data.windowOrder → object.Vertex,
    (∀ P ∈ packing, Graph.LocalRigidity.IsWindowPlacement object P (place P)) →
    ∀ c : Nat,
      ((data.dischargeScale *
            (data.threshold * (data.windowOrder * packing.card) +
              data.spineScale * Core.ceilSqrt object.vertexCount) : Nat) : ℤ) -
          ((data.dischargeScale * (2 * (data.windowOrder - 1) * packing.card) : Nat) : ℤ) +
          ((data.dischargeScale * data.threshold * slack : Nat) : ℤ) -
          (c : ℤ) * (((data.threshold - 1) * packing.card +
            object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
              data.threshold : Nat) : ℤ) <
        ∑ X ∈ pieces.filter (fun X => 0 < excess X),
          (((data.threshold * data.dischargeScale + 1 : Nat) : ℤ) * excess X -
            (c : ℤ) * route8LongLandingWindows data object place X)

end Hypostructure.Graph.Strategy.Spine
