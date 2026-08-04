import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.FinitePathSelection
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger

/-!
DEPRECATED: migrated to canonical CT composition strategy
(composite family: CT2 -> CT11; CT6 -> CT3; CT14; CT1 -> CT6).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.

# Canonical consequences of graph minimality

This module contains only graph semantics.  Every schedule is reconstructed
from the packed finite graph.  Failed structural or target laws remain typed
residuals; no application can choose a branch or supply a selected witness.
-/

namespace Hypostructure.Graph.Strategy.Official.Features

open Hypostructure.Graph
open scoped Sym2

universe u v

namespace SparseDeletionEnvelope

private def decisionBool {proposition : Prop}
    (decision : Decidable proposition) : Bool :=
  match decision with
  | isTrue _ => true
  | isFalse _ => false

/-- The baseline-relative degeneracy bound, derived from the profile
threshold rather than supplied independently. -/
def degeneracyBound (threshold : Nat) : Nat := threshold - 1

/-- A literal degeneracy certificate for the graph left after deleting a
tight vertex.  The sparse envelope is retained explicitly, so a failure of
the general implication is observable rather than assumed. -/
structure Certificate
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) where
  vertex : object.Vertex
  tight : object.degree vertex = profile.threshold
  deletedDegenerate :
    ∀ support : List (object.deleteVertex vertex).Vertex,
      support.Nodup → support ≠ [] →
      ∃ selected ∈ support,
        (support.filter fun other =>
          decisionBool
            ((object.deleteVertex vertex).decideAdj selected other)).length ≤
            degeneracyBound profile.threshold
  edgeEnvelope :
    (object.deleteVertex vertex).edgeCount ≤
      degeneracyBound profile.threshold *
        (object.deleteVertex vertex).vertexCount

/-- Exact unresolved information.  It distinguishes absence of a tight
vertex from failure of the structural degeneracy/envelope implication. -/
inductive Residual
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) where
  | noTightVertex :
      (∀ vertex, object.degree vertex ≠ profile.threshold) → Residual profile object
  | degeneracyLawMissing :
      (vertex : object.Vertex) →
      object.degree vertex = profile.threshold →
      (¬ (∀ support : List (object.deleteVertex vertex).Vertex,
          support.Nodup → support ≠ [] →
          ∃ selected ∈ support,
            (support.filter fun other =>
              decisionBool
                ((object.deleteVertex vertex).decideAdj selected other)).length ≤
                degeneracyBound profile.threshold) ∨
       ¬ (object.deleteVertex vertex).edgeCount ≤
          degeneracyBound profile.threshold *
            (object.deleteVertex vertex).vertexCount) →
      Residual profile object

inductive Result
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) where
  | certified (certificate : Certificate profile object)
  | unresolved (residual : Residual profile object)

/-- First tight vertex in the graph's own order. -/
noncomputable def firstTight?
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) : Option object.Vertex :=
  object.orderedVertices.find? fun vertex =>
    object.degree vertex = profile.threshold

noncomputable def execute
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) : Result profile object := by
  classical
  by_cases existsTight :
      ∃ vertex : object.Vertex, object.degree vertex = profile.threshold
  · let vertex := Classical.choose existsTight
    have tight := Classical.choose_spec existsTight
    by_cases degenerate :
        ∀ support : List (object.deleteVertex vertex).Vertex,
          support.Nodup → support ≠ [] →
          ∃ selected ∈ support,
            (support.filter fun other =>
              decisionBool
                ((object.deleteVertex vertex).decideAdj selected other)).length ≤
                degeneracyBound profile.threshold
    · by_cases envelope :
          (object.deleteVertex vertex).edgeCount ≤
            degeneracyBound profile.threshold *
              (object.deleteVertex vertex).vertexCount
      · exact .certified ⟨vertex, tight, degenerate, envelope⟩
      · exact .unresolved (.degeneracyLawMissing vertex tight (Or.inr envelope))
    · exact .unresolved (.degeneracyLawMissing vertex tight (Or.inl degenerate))
  · exact .unresolved (.noTightVertex (by simpa only [not_exists] using existsTight))

/-- Exact number of finite structural checks represented by the presentation. -/
def work
    {Baseline : FiniteObject.{u} → Prop}
    (_profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) : Nat :=
  object.vertexCount + 2 ^ (object.vertexCount - 1) + 1

end SparseDeletionEnvelope

namespace CanonicalBridgeQuotient

/-- A bridge together with its canonical two-valued component quotient after
deleting that edge. -/
structure Quotient (object : FiniteObject.{u}) where
  dart : object.graph.Dart
  isBridge : object.graph.IsBridge dart.edge
  side : object.Vertex → Bool

/-- The target laws available to bridge reasoning.  Isomorphism invariance
and proper-subgraph heredity are mathematical target-interface laws. -/
structure TargetLaws (Target : FiniteObject.{u} → Prop) : Type (u + 1) where
  invariant : TargetInterface Target
  hereditary : ProperSubgraphTargetMonotone Target

inductive Result (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) where
  | bridgeless (certificate : ∀ dart : object.graph.Dart,
      ¬ object.graph.IsBridge dart.edge)
  | quotient (value : Quotient object) (laws : TargetLaws Target)
  | targetLawMissing (value : Quotient object)

noncomputable def firstBridge? (object : FiniteObject.{u}) :
    Option object.graph.Dart := by
  classical
  exact object.orderedDarts.find? fun dart =>
    object.graph.IsBridge dart.edge

/-- Framework-owned bridge scan.  A quotient is always canonical; lack of
target heredity is exposed as a residual instead of being silently assumed. -/
noncomputable def execute (Target : FiniteObject.{u} → Prop)
    (laws : Option (TargetLaws Target)) (object : FiniteObject.{u}) :
    Result Target object := by
  classical
  by_cases bridge : ∃ dart : object.graph.Dart,
      object.graph.IsBridge dart.edge
  · let dart := Classical.choose bridge
    let quotient : Quotient object :=
      ⟨dart, Classical.choose_spec bridge, fun vertex =>
        if (object.graph.deleteEdges {dart.edge}).Reachable dart.fst vertex
        then true else false⟩
    cases laws with
    | none => exact .targetLawMissing quotient
    | some targetLaws => exact .quotient quotient targetLaws
  · exact .bridgeless (by simpa only [not_exists] using bridge)

def work (object : FiniteObject.{u}) : Nat :=
  object.orderedDarts.length * object.vertexCount

end CanonicalBridgeQuotient

namespace ExcessPortExtraction

open DegreeSurplusLedger

/-- A graph-derived incidence at a vertex whose degree exceeds the critical
threshold. -/
structure Port
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) where
  center : object.Vertex
  centerHigh : profile.threshold < object.degree center
  endpoint : object.Vertex
  adjacent : object.graph.Adj center endpoint

/-- Canonical centres, selected solely from the packed graph's degree table. -/
def centers
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) : List object.Vertex :=
  object.orderedVertices.filter fun vertex =>
    decide (profile.threshold < object.degree vertex)

/-- Canonical excess half-edge ports, generated from the graph order.
At a centre of degree `d`, the first `profile.threshold` neighbours form the
baseline family and exactly `d - profile.threshold` remaining neighbours are
selected.  This is the literal excess-port operation used at paper nodes
`[125]--[126]`; it does not select every edge incident with a high centre. -/
def ports
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
  (object : FiniteObject.{u}) : List (Port profile object) :=
  (centers profile object).attach.flatMap fun center =>
    ((object.orderedNeighbors center.1).drop profile.threshold).attach.map
      fun endpoint =>
      ⟨center.1, (by
          simpa [centers] using center.2),
        endpoint.1,
        (object.mem_orderedNeighbors_iff center.1 endpoint.1).mp
          (List.mem_of_mem_drop endpoint.2)⟩

/-- Exact size of the canonical excess-port family.  Every summand and the
selection order are derived from the graph and deletion threshold. -/
theorem ports_length
    {Baseline : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) :
    (ports profile object).length =
      ((centers profile object).map fun center =>
        object.degree center - profile.threshold).sum := by
  classical
  unfold ports
  simp [List.length_flatMap, FiniteObject.orderedNeighbors_length]

/-- Deletion criticality forces the non-centre endpoint of every selected
excess port to be tight at the baseline threshold. -/
theorem endpoint_tight
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (criticality : DeletionCriticalityCertificate profile ctx)
    (port : Port profile ctx.G) :
    ctx.G.degree port.endpoint = profile.threshold := by
  have endpoint :=
    criticality.tightEndpoint
      (⟨(port.center, port.endpoint), port.adjacent⟩ : ctx.G.graph.Dart)
  change
    ctx.G.degree port.center = profile.threshold ∨
      ctx.G.degree port.endpoint = profile.threshold at endpoint
  rcases endpoint with centerTight | endpointTight
  · exact (Nat.ne_of_gt port.centerHigh centerTight).elim
  · exact endpointTight

/-- The threshold baseline reconstructed from the current minimal
counterexample and deletion profile. -/
def surplusBaseline
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :
    MinimumDegreeBaseline ctx.G where
  degree := profile.threshold
  lower := fun vertex =>
    (profile.degreeLowerBound ctx.baseline).trans
      (ctx.G.minDegree_le_degree vertex)

/-- Paper nodes `[125]--[126]`: the canonical excess-port family has exactly
the graph's total degree surplus above the deletion threshold. -/
theorem ports_length_eq_total_surplus
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :
    (ports profile ctx.G).length =
      (DegreeSurplusLedger.derive ctx.G
        (surplusBaseline (profile := profile) ctx)).total := by
  rw [ports_length, DegreeSurplusLedger.total_derive]
  unfold centers
  change
    ((ctx.G.orderedVertices.filter fun vertex =>
        decide (profile.threshold < ctx.G.degree vertex)).map fun center =>
      ctx.G.degree center - profile.threshold).sum =
      (ctx.G.orderedVertices.map fun vertex =>
        ctx.G.degree vertex - profile.threshold).sum
  let lower : ∀ vertex : ctx.G.Vertex,
      profile.threshold ≤ ctx.G.degree vertex :=
    (surplusBaseline (profile := profile) ctx).lower
  induction ctx.G.orderedVertices with
  | nil => simp
  | cons vertex tail inductionHypothesis =>
      by_cases high : profile.threshold < ctx.G.degree vertex
      · simp [high, inductionHypothesis]
      · have tight : ctx.G.degree vertex = profile.threshold := by
          exact Nat.le_antisymm (Nat.le_of_not_gt high) (lower vertex)
        simp [tight, inductionHypothesis]

/-- Exact deletion-critical residual.  Both schedules are retained with
definitional provenance, so neither can be supplied by an application. -/
structure Certificate
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)} where
  criticality : DeletionCriticalityCertificate profile ctx
  centers : List ctx.G.Vertex
  centers_eq : centers = ExcessPortExtraction.centers profile ctx.G
  ports : List (Port profile ctx.G)
  ports_eq : ports = ExcessPortExtraction.ports profile ctx.G

def execute
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (criticality : DeletionCriticalityCertificate profile ctx) :
    Certificate (profile := profile) (ctx := ctx) :=
  ⟨criticality, centers profile ctx.G, rfl, ports profile ctx.G, rfl⟩

end ExcessPortExtraction

namespace LexicographicPathSelection

abbrev pathSchedule :=
  Hypostructure.Graph.FinitePathSelection.pathSchedule

abbrev SelectedPath :=
  Hypostructure.Graph.FinitePathSelection.SelectedPath

noncomputable abbrev select? :=
  Hypostructure.Graph.FinitePathSelection.select?

/-- One canonical return-path row. -/
structure ReturnRow (object : FiniteObject.{u}) where
  dart : object.graph.Dart
  selected : Option (by
    letI : FinEnum object.Vertex := object.vertices
    letI : Fintype object.Vertex := by infer_instance
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel
        (object.graph.deleteEdges {dart.edge}).Adj := by
      exact Classical.decRel _
    exact SelectedPath
      (object.graph.deleteEdges {dart.edge}) dart.snd dart.fst)

/-- Canonical return paths are selected in the edge-deleted graph. -/
noncomputable def returnPaths (object : FiniteObject.{u}) :
    List (ReturnRow object) :=
  object.orderedDarts.map fun dart => by
    letI : FinEnum object.Vertex := object.vertices
    letI : Fintype object.Vertex := by infer_instance
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel
        (object.graph.deleteEdges {dart.edge}).Adj := Classical.decRel _
    exact ⟨dart,
      select? (object.graph.deleteEdges {dart.edge}) dart.snd dart.fst⟩

/-- Canonical support path between two supplied graph-derived endpoints. -/
noncomputable def supportPath? (object : FiniteObject.{u})
    (left right : object.Vertex) :
    Option (by
      letI : FinEnum object.Vertex := object.vertices
      letI : Fintype object.Vertex := by infer_instance
      letI : DecidableEq object.Vertex := object.vertices.decEq
      letI : DecidableRel object.graph.Adj := object.decideAdj
      exact SelectedPath object.graph left right) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := by infer_instance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact Hypostructure.Graph.FinitePathSelection.supportPath? object left right

def work (object : FiniteObject.{u}) : Nat :=
  object.orderedDarts.length * (object.vertexCount + 1) *
    2 ^ object.vertexCount

end LexicographicPathSelection

end Hypostructure.Graph.Strategy.Official.Features
