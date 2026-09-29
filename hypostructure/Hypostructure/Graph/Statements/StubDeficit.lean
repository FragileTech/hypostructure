import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.StubDeficit

/-!
# Statements: the stub-deficit identity and the cycle spectrum of `R₀`

Two facts of G at its canonical packing `P₀ = canonicalWindowPacking` and
remainder `R₀ = R(P₀)`, published on the arms of `[54]` (the joint realization
test of `prop:entropy-high-theta` counts exactly `R₀`'s states, its
`e(G[R₀])`, its `def⁺` and its boundary):

* `StubDeficitIdentityStatement`: the incidence identity
  `e(R₀,W) + exc(R₀) = σ(R₀) + def⁺(R₀)`, the handshake
  `2·e(G[R₀]) + e(R₀,W) = δ|R₀| + σ(R₀)`, and the canonical assignment of the
  `def⁺(R₀)` deficit units to distinct boundary stubs, fixed by G's vertex order
  (`FiniteObject.stubAssignment`).
* `RemainderCycleSpectrumStatement`: the induced subgraph `G[R₀]` carries no cycle
  of an accepted length (its cycle-length spectrum lies in the complement of
  the accepted set), read off G's own avoidance of the target.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The stub-deficit identity at `R₀`.**  For G meeting the baseline `δ`:
`e(R₀,W) + exc(R₀) = σ(R₀) + def⁺(R₀)`; `2·e(G[R₀]) + e(R₀,W) = δ|R₀| + σ(R₀)`;
the deficit units of `R₀` (their number is `def⁺(R₀)`) are assigned, by G's
vertex order, to pairwise distinct boundary stubs of `R₀`. -/
noncomputable def StubDeficitIdentityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.MinimumDegreeAtLeast data.threshold object →
    let remainder := object.remainderSupport (canonicalWindowPacking data object)
    object.boundaryIncidence remainder + object.internalExcess remainder data.threshold =
        object.ambientSurplus remainder data.threshold +
          object.positiveDeficiency remainder data.threshold ∧
      2 * object.internalEdgeCount remainder + object.boundaryIncidence remainder =
        data.threshold * remainder.card + object.ambientSurplus remainder data.threshold ∧
      (object.deficitUnits remainder data.threshold).card =
        object.positiveDeficiency remainder data.threshold ∧
      (∀ unit ∈ object.deficitUnits remainder data.threshold,
        ∃ stub ∈ object.boundaryStubs remainder,
          object.stubAssignment remainder unit = some stub) ∧
      (∀ u ∈ object.deficitUnits remainder data.threshold,
        ∀ v ∈ object.deficitUnits remainder data.threshold,
          ∀ stub, object.stubAssignment remainder u = some stub →
            object.stubAssignment remainder v = some stub → u = v)

/-- **The cycle spectrum of `R₀`**: `G[R₀]` has no cycle whose length is accepted
(a power of two), and neither has any induced subgraph of `R₀`. -/
noncomputable def RemainderCycleSpectrumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ support : Finset object.Vertex,
    support ⊆ object.remainderSupport (canonicalWindowPacking data object) →
      ¬ Graph.HasCycleWithLength data.LengthOK (object.induce support)

end Hypostructure.Graph.Strategy.Spine
