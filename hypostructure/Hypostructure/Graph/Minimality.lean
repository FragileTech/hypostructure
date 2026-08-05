import Hypostructure.Core.Minimality
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Target

/-!
# Proper-subgraph minimality

This module re-exports the graph minimality API as a thin specialization of the
generic core minimality executor. Domain-specific objects (`ProperSubgraph`,
cycle target transport, and focused stage wrappers) are retained here; all core
logic and routing stays in `Hypostructure.Core.Minimality`.
-/

namespace Hypostructure.Graph

universe u v uPrevious

namespace ProperSubgraph

/-- The injective graph homomorphism carried by a proper-subgraph certificate. -/
def hom {source : FiniteObject.{u}} (subgraph : ProperSubgraph source) :
    subgraph.value.graph →g source.graph where
  toFun := subgraph.vertexEmbedding
  map_rel' := by
    intro left right adjacent
    exact subgraph.included ((SimpleGraph.map_adj_apply).2 adjacent)

theorem hom_injective {source : FiniteObject.{u}}
    (subgraph : ProperSubgraph source) :
    Function.Injective subgraph.hom :=
  subgraph.vertexEmbedding.injective

end ProperSubgraph

/-- Target transport required by the proper-subgraph minimality pattern. -/
structure ProperSubgraphTargetMonotone
    (Target : FiniteObject.{u} -> Prop) : Prop where
  map : forall {source : FiniteObject.{u}}
    (subgraph : ProperSubgraph source), Target subgraph.value -> Target source

/-- Accepted cycles map injectively from every certified proper subgraph. -/
def cycleProperSubgraphTargetMonotone (LengthOK : Nat -> Prop) :
    ProperSubgraphTargetMonotone (HasCycleWithLength LengthOK) where
  map := by
    intro source subgraph target
    rcases target with ⟨certificate⟩
    exact ⟨certificate.mapHom subgraph.hom subgraph.hom_injective⟩

/-- The complete, domain-generic "recursive step" of the minimal-degree
minimal-counterexample argument: deleting a *safe* vertex (degree at most
`k`, with every neighbour of degree strictly above `k`) both (a) keeps the
minimum-degree-`k` baseline on the smaller graph, and (b) transports any
registered cycle target found on the smaller graph back to the original —
for free, via `cycleProperSubgraphTargetMonotone`, since a cycle in an
induced subgraph is already a cycle in the source.  Neither fact depends on
any particular application (graph size, target length predicate, etc.).

What this lemma does *not* supply — and cannot, since it is real
mathematical content specific to the minimum-counterexample argument for a
given problem, not routing/recursion plumbing — is a proof that *some*
safe vertex always exists in a minimal counterexample (or a handling for
the case where none does).  That is exactly the remaining gap for a full
closure of any strategy built on this step. -/
theorem target_of_safeVertexDeletion (LengthOK : Nat -> Prop) (k : Nat)
    (object : FiniteObject.{u}) (vertex neighbor : object.Vertex)
    (hadj : object.graph.Adj vertex neighbor)
    (baseline : k ≤ object.minDegree)
    (safe : ∀ w, object.graph.Adj vertex w -> k < object.degree w)
    (smaller : HasCycleWithLength LengthOK (object.deleteVertex vertex)) :
    k ≤ (object.deleteVertex vertex).minDegree ∧ HasCycleWithLength LengthOK object :=
  ⟨object.minDegree_deleteVertex_of_safe k vertex neighbor hadj baseline safe,
   (cycleProperSubgraphTargetMonotone LengthOK).map
     (ProperSubgraph.deleteVertex object vertex) smaller⟩

/-- Graph-level profile for applying strict-progress minimality to proper
subgraphs. -/
structure ProperSubgraphMinimalityProfile
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (Target : FiniteObject.{u} -> Prop) where
  targetMonotone : ProperSubgraphTargetMonotone Target
  stateOf : (object : FiniteObject.{u}) -> BranchState object

/-- The graph minimality profile read as Core's subobject profile.  `toAmbient`
is the underlying graph of the certified proper subgraph, so every Core node
indexed by this profile speaks about the literal subgraph the graph layer
produced. -/
def toCoreProfile
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target) :
    Core.Minimality.SubobjectMinimalityProfile
      (P := problem Baseline BranchState)
      Target
      (lexicographicProgress Baseline BranchState)
      ProperSubgraph :=
  { toAmbient := fun subgraph => subgraph.value
    smaller := fun subgraph =>
      subgraph.smaller Baseline BranchState
    targetMonotone := fun subgraph target =>
      profile.targetMonotone.map subgraph target
    stateOf := profile.stateOf
  }

/-- Framework-owned no-proper-baseline result. Every subgraph exclusion is
tagged by Core's strict-progress mechanism. -/
structure NoProperBaselineCertificate
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) where
  private mk ::
  closure : ∀ (subgraph : ProperSubgraph ctx.G), Baseline subgraph.value ->
    Core.Closure.Result False
  mechanism : ∀ (subgraph : ProperSubgraph ctx.G) (baseline : Baseline subgraph.value),
    (closure subgraph baseline).mechanism =
      Core.Closure.Mechanism.strictProgress

namespace NoProperBaselineCertificate

/-- No certified proper subgraph can retain the baseline. -/
theorem excludes
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (certificate : NoProperBaselineCertificate ctx)
    (subgraph : ProperSubgraph ctx.G) : Not (Baseline subgraph.value) := by
  intro baseline
  exact (certificate.closure subgraph baseline).proof

end NoProperBaselineCertificate

/-- Execute the generic proper-subgraph strict-progress closure. -/
def deriveNoProperBaseline
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :
    NoProperBaselineCertificate ctx :=
  let certificate :
      Core.Minimality.NoSubobjectBaselineCertificate
        (P := problem Baseline BranchState)
        (Target := Target)
        (progress := lexicographicProgress Baseline BranchState)
        (Subobject := ProperSubgraph)
        (profile := toCoreProfile profile) ctx :=
    Core.Minimality.deriveNoSubobjectBaseline
      (P := problem Baseline BranchState)
      (Target := Target)
      (progress := lexicographicProgress Baseline BranchState)
      (Subobject := ProperSubgraph)
      (profile := toCoreProfile profile) ctx
  { closure := certificate.closure
    mechanism := certificate.mechanism }

/-- Cycle-target specialization used by minimum-degree counterexamples. -/
def cycleProperSubgraphMinimalityProfile
    (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (LengthOK : Nat -> Prop)
    (stateOf : (object : FiniteObject.{u}) -> BranchState object) :
    ProperSubgraphMinimalityProfile Baseline BranchState
      (HasCycleWithLength LengthOK) where
  targetMonotone := cycleProperSubgraphTargetMonotone LengthOK
  stateOf := stateOf

end Hypostructure.Graph
