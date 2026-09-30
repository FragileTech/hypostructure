import Hypostructure.Graph.Statements.Route8ArmCap
import Hypostructure.Graph.Statements.Route8HubPieceMass
import Hypostructure.Graph.DensityCert.Basic

/-!
# Statements: the density theorem at the pieces of `R` and the arm closure (keys `9700`–`9706`)

`P₀ = canonicalWindowPacking`, `R` its remainder, `X` the canonical pieces of `G[R]` with
vertex sets `S_X`, `σ_X = Σ_{v∈S_X}(d(v) − δ)` the ambient surplus of a piece (a piece is
*hub-free* when `σ_X = 0`), `excess X = |S_X| − s·|∂S_X|` (as in key `9807`), and `ν(X)` the
windows of `P₀` on which `X` has a long landing (`route8LongLandingWindows`).

* `9700` (hub-free density): a hub-free piece has `excess ≤ 0` or `G[S_X]` is a copy of `X15`.
* `9701` (`X15` long landings): a hub-free copy of `X15` has `ν(X) ≥ 2` for every placement
  system of `P₀`.
* `9702` (`Π` for hub-free pieces): a hub-free piece with positive excess has
  `(δs+1)·excess X ≤ 30·ν(X)`.
* `9703` (hub-piece excess): a piece with `σ_X > 0` has `excess X ≤ (F − 1)·s·σ_X`.
* `9704` (arm closure): with the hub margin `F ≤ 14`, `SufficientlyLargeForNetCap` is false.
* `9705` / `9706`: the exact size split, `F ≤ 14 ∧ SufficientlyLargeForNetCap` and its negation.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open scoped BigOperators

universe u

/-- `excess X = |S_X| − s·|∂S_X|` (in `ℤ`) of a canonical piece of the remainder of `P₀`. -/
noncomputable def route8PieceExcess (data : Parameters) (object : Graph.FiniteObject.{u})
    (X : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) : ℤ :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ((object.pieceSupport remainder X).card : ℤ) -
    (data.dischargeScale : ℤ) *
      (Graph.Route8.cutEdges object (object.pieceSupport remainder X)).card

/-- `σ_X`: the ambient surplus of a canonical piece of the remainder of `P₀`. -/
noncomputable def route8PieceSurplus (data : Parameters) (object : Graph.FiniteObject.{u})
    (X : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) : Nat :=
  object.ambientSurplus
    (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) X)
    data.threshold

/-- **Key `9700`: the density theorem at the hub-free pieces.**  Every canonical piece `X` of
`R` with `σ_X = 0` has `excess X ≤ 0`, or `G[S_X]` is a copy of `X15`. -/
def Route8HubFreeDensityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ∀ X ∈ object.canonicalPieces remainder,
    route8PieceSurplus data object X = 0 →
    route8PieceExcess data object X ≤ 0 ∨
      Graph.DensityCert.EmbOnto Graph.DensityCert.CG.x15.graph object.graph
        (object.pieceSupport remainder X)

/-- **Key `9701`: the long landings of a hub-free `X15` piece.**  For every placement system
of `P₀`, a canonical piece `X` with `σ_X = 0` that is a copy of `X15` has a long landing on at
least two windows of `P₀`. -/
def Route8X15LongLandingsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ place : Finset object.Vertex → Fin data.windowOrder → object.Vertex,
    (∀ P ∈ packing, Graph.LocalRigidity.IsWindowPlacement object P (place P)) →
    ∀ X ∈ object.canonicalPieces remainder,
      route8PieceSurplus data object X = 0 →
      Graph.DensityCert.EmbOnto Graph.DensityCert.CG.x15.graph object.graph
        (object.pieceSupport remainder X) →
      2 ≤ route8LongLandingWindows data object place X

/-- **Key `9702`: `Π` at the hub-free pieces.**  For every placement system of `P₀`, a
canonical piece `X` with `σ_X = 0` and positive excess has `(δs+1)·excess X ≤ 30·ν(X)`. -/
def Route8HubFreePiStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ place : Finset object.Vertex → Fin data.windowOrder → object.Vertex,
    (∀ P ∈ packing, Graph.LocalRigidity.IsWindowPlacement object P (place P)) →
    ∀ X ∈ object.canonicalPieces remainder,
      route8PieceSurplus data object X = 0 →
      0 < route8PieceExcess data object X →
      ((data.threshold * data.dischargeScale + 1 : Nat) : ℤ) * route8PieceExcess data object X ≤
        30 * (route8LongLandingWindows data object place X : ℤ)

/-- **Key `9703`: the excess of a hub piece.**  Every canonical piece `X` of `R` with
`σ_X > 0` has `excess X ≤ (F − 1)·s·σ_X`. -/
def Route8HubPieceExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ∀ X ∈ object.canonicalPieces remainder,
    0 < route8PieceSurplus data object X →
    route8PieceExcess data object X ≤
      (((data.bridgeMassFactor - 1) * data.dischargeScale : Nat) : ℤ) *
        (route8PieceSurplus data object X : ℤ)

/-- **Key `9704`: the arm closure.**  With the hub margin `F ≤ 14`
(`(δs+1)·(F−1)·s ≤ s + δs·Fs` at `δ = 3`, `s = 4`), `SufficientlyLargeForNetCap` fails at G. -/
def Route8ArmClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  data.bridgeMassFactor ≤ 14 →
    Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
      data.dischargeScale data.windowOrder data.windowRate
      data.spineScale data.densitySlack object.vertexCount →
    False

/-- **Key `9705`: the large arm of the net-cap size split**: the hub margin `F ≤ 14` and
`SufficientlyLargeForNetCap` at G's order. -/
def Route8NetCapLargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  data.bridgeMassFactor ≤ 14 ∧
    Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
      data.dischargeScale data.windowOrder data.windowRate
      data.spineScale data.densitySlack object.vertexCount

/-- **Key `9706`: the small arm of the net-cap size split**, the exact negation of key
`9705`. -/
def Route8NetCapSmallStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ Route8NetCapLargeStatement data object

end Hypostructure.Graph.Strategy.Spine
