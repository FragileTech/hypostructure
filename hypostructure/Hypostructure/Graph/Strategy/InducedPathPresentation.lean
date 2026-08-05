import Hypostructure.Core.Residual.Query
import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.Induced
import Hypostructure.Graph.Strategy.MinimumDegreeBaseline

/-!
# Closed induced-path presentation

This record is the single inert Graph boundary shared by induced-path
obstruction packing and support-complement normalization.  It stores only
residual-owned queries and the already registered mathematical closure law.
It contains no packing result, strategy stage, CT output, route, or ledger.
-/

namespace Hypostructure.Graph.Strategy

open Hypostructure

universe uResidual uVertex

/-- Residual-owned induced-path data from which Graph derives both the Core
packing semantics and its dependent normalization profile. -/
structure InducedPathPresentation
    (Residual : Type uResidual) (Target : Residual → Prop) where
  object : Core.Residual.Query Residual fun _ => FiniteObject.{uVertex}
  order : Core.Residual.Query Residual fun _ => Nat
  order_pos : ∀ residual, 0 < order residual
  baselineDegree : Core.Residual.Query Residual fun _ => Nat
  freeForcesTarget : ∀ residual,
    InducedPathFree (object residual) (order residual) →
      Target residual
  componentFreeForcesTarget : ∀ residual
    (support : Finset (object residual).Vertex),
      baselineDegree residual ≤
          ((object residual).induce support).minDegree →
        InducedPathFree ((object residual).induce support)
          (order residual) →
          Target residual

end Hypostructure.Graph.Strategy
