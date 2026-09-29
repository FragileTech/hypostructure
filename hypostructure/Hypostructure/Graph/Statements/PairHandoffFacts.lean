import Hypostructure.Graph.Statements.PairHandoffSupport
import Hypostructure.Graph.Statements.HubLinks
import Hypostructure.Graph.Statements.LocalRigidity
import Hypostructure.Graph.Statements.SparseExitReadings
import Hypostructure.Graph.Statements.SwitchForcedPaths
import Hypostructure.Graph.PairCorrelation

/-!
# Statements: the structure of G at the pair-obstruction handoff (residual `[187]`)

Five facts about G at the canonical handoff of its retained pair obstruction (the returns
`R`, the obstruction family `𝒰`, its overlap support `U`, the canonical first separator `h`, the
core `Y = {d_p.2, d_q.2}`).  Every choice is the `canonicalChoice` of its spec, fixed by G's data.

* `PairHandoffHubChargeStatement` (flow-cut support of the capacity charge at `h`): every pair of
  the obstruction family is charged to the port token of one of its own ports (a high centre),
  `h` has `d(h) - δ` port tokens, and the pairs of the family charged to them are bounded by
  their new loads.
* `PairHandoffBoundaryTypeStatement` (boundaried type of `G[U]`): the boundary vertices of `U`,
  the exact degree identity `e(U, G−U) + Σ_U d_U = δ|U| + σ(U)`, `σ(U) ≥ 1`, and the response of
  every reading of `U` glued into `G − U` (negative: no accepted cycle).
* `PairHandoffCriticalCoordinateStatement` (fibre-size count at the coordinate `h` decides): every
  coordinate of `𝒰` is critical: the order exposing it last doubles at every earlier level and
  fails to double exactly at it; the canonical members whose supports contain `h`, `a`, `b` exist.
* `PairObstructionDescentStatement` (demand descent): `2 ≤ |𝒰| ≤ |Π|`, `𝒰` is not realizing, and
  peeling any one member leaves a realizing family.
* `PairHandoffHubForcesStatement` (what the ledger's hub facts say at `h`): the vertex split, the
  same-vertex switch, the endpoint switch at cubic neighbours, the length-3 fan and the chain
  `3, 3, 3`, instantiated at `h`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.CapacityFreeSide
open Hypostructure.Graph.LocalRigidity
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

open Classical in
/-- **Flow-cut support of the capacity charge, at the handoff centre `h`.**  Each pair of the
obstruction family, being free, is charged by the extended charge to the port token of one of
its own ports, whose centre is a high vertex; `h`'s own tokens are its `d(h) - δ` excess ports,
and the number of pairs of the family charged to them is at most the sum of their new loads. -/
noncomputable def PairHandoffHubChargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ (routes : PairObstructionRoutes object) (split : SameTokenFirstSeparator object),
      canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
      ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
        (∀ pair ∈ returns.overlap.family, ∃ port ∈ pair.1,
          port ∈ object.excessPorts data.threshold ∧
            data.threshold < object.degree port.1 ∧
            extCharge data.LengthOK c pair.1 = some (portToken port)) ∧
        ((object.excessPorts data.threshold).filter
            (fun port => port.1 = split.separator)).card =
          object.degree split.separator - data.threshold ∧
        (returns.overlap.family.filter (fun pair => ∃ port ∈ pair.1,
            port.1 = split.separator ∧
              extCharge data.LengthOK c pair.1 = some (portToken port))).card ≤
          ∑ port ∈ (object.excessPorts data.threshold).filter
              (fun port => port.1 = split.separator),
            ((sparseHighDegreeCount data object - 1) +
              (if TriPortAt object port then object.degreeSurplus data.threshold else 0))

/-- **Boundaried type of `G[U]`.** -/
noncomputable def PairHandoffBoundaryTypeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ U : Finset object.Vertex,
      U = returns.overlap.system.overlapSupport returns.overlap.family ∧
      U.Nonempty ∧ Graph.SupportComponents.Connected.ConnectedOn object U ∧
      object.boundaryIncidence U =
        ∑ v ∈ U.filter (fun v => object.internalDegree U v < object.degree v),
          (object.degree v - object.internalDegree U v) ∧
      object.boundaryIncidence U + ∑ v ∈ U, object.internalDegree U v =
        data.threshold * U.card + object.ambientSurplus U data.threshold ∧
      1 ≤ object.ambientSurplus U data.threshold ∧
      (∀ X : Finset object.Vertex,
        ¬ Graph.HasCycleWithLength data.LengthOK (ActualContext.actualGlue object U X))

/-- The deficit of an exposure order sits exactly at coordinate `pair`: `pair` is its last
coordinate, all earlier levels double, and adding `pair` does not. -/
def CriticalCoordinateAt {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object)
    (pair : {pair // pair ∈ returns.overlap.system.first.pairSet}) : Prop :=
  ∃ (order : Fin returns.overlap.family.card ≃ {pair // pair ∈ returns.overlap.family})
    (level : Nat) (last : level < returns.overlap.family.card),
    returns.overlap.family.card = level + 1 ∧
      (order ⟨level, last⟩).1 = pair ∧
      returns.overlap.system.toSkeletonModel.signatureCount (LengthOK := data.LengthOK)
          returns.overlap.family order level =
        2 ^ level * returns.overlap.system.toSkeletonModel.signatureCount
          (LengthOK := data.LengthOK) returns.overlap.family order 0 ∧
      returns.overlap.system.toSkeletonModel.signatureCount (LengthOK := data.LengthOK)
          returns.overlap.family order returns.overlap.family.card <
        2 * returns.overlap.system.toSkeletonModel.signatureCount (LengthOK := data.LengthOK)
          returns.overlap.family order level

/-- **The exposure coordinate the handoff decides.**  Every coordinate of the obstruction is
critical (the deficit of the order that exposes it last sits exactly there), and the canonical
members of the family whose response supports contain the first separator `h` and its two next
vertices `a`, `b` exist. -/
noncomputable def PairHandoffCriticalCoordinateStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    (∀ pair ∈ returns.overlap.family, CriticalCoordinateAt returns pair) ∧
    ∃ (routes : PairObstructionRoutes object) (split : SameTokenFirstSeparator object),
      canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
      ∀ vertex, (vertex = split.separator ∨ vertex = split.nextFirst ∨
          vertex = split.nextSecond) →
        ∃ pair, canonicalChoice (fun pair : {pair // pair ∈
            returns.overlap.system.first.pairSet} => pair ∈ returns.overlap.family ∧
              vertex ∈ returns.overlap.system.responseSupport pair) = some pair ∧
          pair ∈ returns.overlap.family ∧
          vertex ∈ returns.overlap.system.responseSupport pair

open Classical in
/-- **Demand descent of the obstruction.** -/
noncomputable def PairObstructionDescentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    2 ≤ returns.overlap.family.card ∧
    returns.overlap.family.card ≤ returns.overlap.system.first.pairSet.card ∧
    ¬ returns.overlap.system.realizingOrder returns.overlap.family ∧
    ∀ member ∈ returns.overlap.family, (returns.overlap.family.erase member).Nonempty →
      returns.overlap.system.realizingOrder (returns.overlap.family.erase member)

/-- **The hub facts of the ledger at the handoff centre `h`.** -/
noncomputable def PairHandoffHubForcesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ (routes : PairObstructionRoutes object) (split : SameTokenFirstSeparator object),
      canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
      (∃ (v : object.Vertex)
          (c : (object.graph ⊔ Graph.SwitchForcedPaths.antiPairs object split.separator).Walk v v),
          c.IsCycle ∧ data.LengthOK c.length ∧ split.separator ∉ c.support ∧
            ∃ e ∈ c.edges, e ∈ (Graph.SwitchForcedPaths.antiPairs object split.separator).edgeSet ∧
              e ∉ object.graph.edgeSet) ∧
      (∀ ⦃u₁ u₂ : object.Vertex⦄,
        object.graph.Adj split.separator u₁ → object.graph.Adj split.separator u₂ → u₁ ≠ u₂ →
        ¬ object.graph.Adj u₁ u₂ → data.threshold + 2 ≤ object.degree split.separator →
        ∃ p : (object.graph.deleteEdges
            {s(split.separator, u₁), s(split.separator, u₂)}).Walk u₁ u₂,
          p.IsPath ∧ data.LengthOK (p.length + 1) ∧
            ((split.separator ∉ p.support ∧ ¬ data.LengthOK (p.length + 2)) ∨
              ∃ ℓ₁ ℓ₂, ℓ₁ + ℓ₂ = p.length ∧ ¬ data.LengthOK (ℓ₁ + 1) ∧
                ¬ data.LengthOK (ℓ₂ + 1))) ∧
      (∀ c : object.Vertex, object.degree c = data.threshold →
        object.graph.Adj split.separator c →
        (data.threshold + 2 ≤ object.degree split.separator ∧
            ∃ u, object.graph.Adj split.separator u ∧ u ≠ c ∧ ¬ object.graph.Adj c u ∧
              ∃ p : (object.graph.deleteEdges
                  {s(split.separator, c), s(split.separator, u)}).Walk c u,
                p.IsPath ∧ data.LengthOK (p.length + 1)) ∨
          ∃ h₂ u₂, h₂ ≠ split.separator ∧ data.threshold + 1 ≤ object.degree h₂ ∧
            object.graph.Adj u₂ h₂ ∧ u₂ ≠ c ∧ ¬ object.graph.Adj c u₂ ∧
            ∃ p : (object.graph.deleteEdges {s(c, split.separator), s(u₂, h₂)}).Walk c u₂,
              p.IsPath ∧ data.LengthOK (p.length + 1)) ∧
      (∀ ⦃a b c p₁ p₂ q₁ q₂ : object.Vertex⦄,
        object.graph.Adj split.separator a → object.graph.Adj split.separator b →
        object.graph.Adj split.separator c → b ≠ c →
        ThreePath object.graph a p₁ p₂ b → ThreePath object.graph a q₁ q₂ c →
        split.separator ≠ p₁ → split.separator ≠ p₂ → split.separator ≠ q₁ →
        split.separator ≠ q₂ → p₁ = q₁ ∧ p₂ ≠ q₂ ∧ p₂ ≠ c ∧ q₂ ≠ b) ∧
      (∀ ⦃a b c d p₁ p₂ r₁ r₂ q₁ q₂ : object.Vertex⦄,
        object.graph.Adj split.separator a → object.graph.Adj split.separator b →
        object.graph.Adj split.separator c → object.graph.Adj split.separator d →
        a ≠ c → b ≠ d →
        ThreePath object.graph a p₁ p₂ b → ThreePath object.graph b r₁ r₂ c →
        ThreePath object.graph c q₁ q₂ d →
        split.separator ≠ p₁ → split.separator ≠ p₂ → split.separator ≠ r₁ →
        split.separator ≠ r₂ → split.separator ≠ q₁ → split.separator ≠ q₂ →
        r₁ = p₂ ∧ r₂ = q₁)

end Hypostructure.Graph.Strategy.Spine
