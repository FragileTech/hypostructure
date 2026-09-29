import Hypostructure.Graph.Statements.PairHandoffSupport
import Hypostructure.Graph.Statements.HubLinks
import Hypostructure.Graph.Statements.LocalRigidity
import Hypostructure.Graph.Statements.SparseExitReadings
import Hypostructure.Graph.Statements.SwitchForcedPaths

/-!
# Statements: the structure of G at the pair-obstruction handoff (residual `[187]`)

Five facts about G at the canonical handoff of its retained pair obstruction (the returns
`R`, the obstruction family `𝒰`, its overlap support `U`, the canonical first separator `h`, the
core `Y = {d_p.2, d_q.2}`).  Every choice is the `canonicalChoice` of its spec, fixed by G's data.

* `PairHandoffFlowCutStatement` (flow-cut support of the capacity charge): the extended charge
  sends every pair of the obstruction family to a token of G's canonical capacity (an integral
  flow of the demand of `𝒰`), and, when the pair-deficit coefficient is positive, the canonical
  overloaded token `t*` and its charged pair set are a Hall violator (`load > M₀`).
* `PairHandoffBoundaryTypeStatement` (boundaried type of `G[U]`): the boundary vertices of `U`,
  the exact degree identity `e(U, G−U) + Σ_U d_U = δ|U| + σ(U)`, `σ(U) ≥ 1`, and the response of
  every reading of `U` glued into `G − U` (negative: no accepted cycle).
* `PairObstructionCountDeficitStatement` (fibre-size count): for every exposure order of `𝒰`
  some level has strictly fewer than twice as many realized signatures as the level before.
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

/-- **Flow-cut support of the capacity charge at the obstruction.** -/
noncomputable def PairHandoffFlowCutStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ c : SurplusCapacity data object, canonicalCapacity data object = some c ∧
      (∀ pair ∈ returns.overlap.system.first.pairSet,
        ∃ t ∈ c.tokens, extCharge data.LengthOK c pair = some t) ∧
      (0 < pairDeficitCoefficient data →
        ∃ t, canonicalChoice (fun t => t ∈ c.tokens ∧
            homogeneousTokenCap data.routingLabelBound < extLoad data.LengthOK c t) = some t ∧
          t ∈ c.tokens ∧ homogeneousTokenCap data.routingLabelBound < extLoad data.LengthOK c t ∧
          extLoad data.LengthOK c t =
            ((object.portPairSchedule data.threshold).filter fun pair =>
              extCharge data.LengthOK c pair = some t).card)

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

/-- **Fibre-size count of the obstruction.** -/
noncomputable def PairObstructionCountDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∀ order : Fin returns.overlap.family.card ≃ {pair // pair ∈ returns.overlap.family},
      ∃ (level : Nat) (bound : level + 1 ≤ returns.overlap.family.card),
        returns.overlap.system.toSkeletonModel.signatureCount (LengthOK := data.LengthOK)
            returns.overlap.family order (level + 1) bound <
          2 * returns.overlap.system.toSkeletonModel.signatureCount (LengthOK := data.LengthOK)
            returns.overlap.family order level (Nat.le_of_succ_le bound)

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
