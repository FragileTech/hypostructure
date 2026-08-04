/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT6).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.Strategy.Official.Features.MinimalCounterexampleConsequences

/-!
# Canonical activation of excess ports

This Graph-owned feature is the reusable implementation used for paper nodes
`[127]--[129]` in the EG program.  It consumes the exact excess-port family
from deletion criticality and, for each port, either records the literal
bridge obstruction or selects the first finite simple return path after
deleting the port edge.  No path, branch, or outcome is supplied by an
application.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.CanonicalExcessPortActivation

open Hypostructure.Graph
open scoped Sym2

universe u v

abbrev Port
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) :=
  ExcessPortExtraction.Port profile object

variable
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}

/-- The graph obtained by deleting one selected excess-port edge. -/
def deletedGraph (port : Port profile ctx.G) : SimpleGraph ctx.G.Vertex :=
  ctx.G.graph.deleteEdges {s(port.center, port.endpoint)}

/-- A simple endpoint-to-centre return path in the edge-deleted graph. -/
structure ReturnPath (port : Port profile ctx.G) where
  walk : (deletedGraph port).Walk port.endpoint port.center
  simple : walk.IsPath

/-- Exhaustive graph-derived activation of one selected port. -/
inductive PortActivation (port : Port profile ctx.G) where
  | bridge
      (obstruction :
        ctx.G.graph.IsBridge s(port.center, port.endpoint))
  | active
      (endpointTight : ctx.G.degree port.endpoint = profile.threshold)
      (returnPath : ReturnPath port)

/-- Framework-owned activation.  The path is selected from the finite graph
only after the bridge predicate has been decided. -/
noncomputable def activate
    (criticality : DeletionCriticalityCertificate profile ctx)
    (port : Port profile ctx.G) :
    PortActivation port := by
  classical
  by_cases bridge :
      ctx.G.graph.IsBridge s(port.center, port.endpoint)
  · exact .bridge bridge
  · have reachable :
        (deletedGraph port).Reachable port.center port.endpoint := by
      rw [SimpleGraph.isBridge_iff] at bridge
      exact Classical.byContradiction fun notReachable => bridge notReachable
    let pathExists := reachable.symm.exists_isPath
    let walk := Classical.choose pathExists
    have simple : walk.IsPath := Classical.choose_spec pathExists
    exact .active
      (ExcessPortExtraction.endpoint_tight
        criticality port)
      ⟨walk, simple⟩

/-- Complete canonical activation schedule in the exact excess-port order. -/
noncomputable def activations
    (criticality : DeletionCriticalityCertificate profile ctx) :
    List (Σ port : Port profile ctx.G, PortActivation port) :=
  (ExcessPortExtraction.ports
      profile ctx.G).map fun port => ⟨port, activate criticality port⟩

/-- Activation preserves the exact number of excess ports. -/
theorem activations_length
    (criticality : DeletionCriticalityCertificate profile ctx) :
    (activations criticality).length =
      (DegreeSurplusLedger.derive ctx.G
        (ExcessPortExtraction.surplusBaseline
          (profile := profile) ctx)).total := by
  rw [activations, List.length_map]
  exact ExcessPortExtraction.ports_length_eq_total_surplus ctx

end Hypostructure.Graph.Strategy.Official.Features.CanonicalExcessPortActivation
