import Hypostructure.Graph.Minimality

/-!
# Edge-deletion criticality

This module packages the graph-generic argument that an edge-minimal object
with minimum degree at least `k` cannot contain an edge whose two endpoints
both have one unit of degree slack.  The exact one-edge degree accounting and
baseline preservation are owned by Graph.

The two *conclusions* are not.  They are manuscript nodes `[9]`--`[10]`
(`lem:deletion-critical`) and Core owns both:
`Core.Strategy.CriticalModificationStructure.criticalityNode` derives universal
atomic criticality from the inherited no-subobject certificate, and
`slackIncompatibilityNode` derives carrier incompatibility from that appended
entry.  This module supplies the graph semantics those two nodes consume
(`DeletionCriticalityProfile.criticalModificationSemantics`) and reads the two
appended entries back as a `DeletionCriticalityCertificate`.  The certificate
has exactly one constructor and it is that ledger read; nothing here re-proves
either node.

The abstract profile supports baselines with additional graph properties.  Its
concrete minimum-degree specialization requires only the threshold `k`; a
caller never supplies the endpoint conclusion or the one-edge accounting.
-/

namespace Hypostructure.Graph

open Finset

universe u v

namespace FiniteObject

/-- The certified undirected edge underlying a Mathlib dart. -/
def edgeOfDart (object : FiniteObject.{u})
    (dart : object.graph.Dart) : object.graph.edgeSet :=
  ⟨dart.edge, dart.edge_mem⟩

@[simp]
theorem edgeOfDart_value (object : FiniteObject.{u})
    (dart : object.graph.Dart) :
    (object.edgeOfDart dart).1 = dart.edge :=
  rfl

end FiniteObject

private theorem mk_fst_eq_edge_iff {V : Type u} {G : SimpleGraph V}
    (dart : G.Dart) (vertex : V) :
    s(dart.fst, vertex) = dart.edge ↔ vertex = dart.snd := by
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff']
  simp [eq_comm]

private theorem mk_snd_eq_edge_iff {V : Type u} {G : SimpleGraph V}
    (dart : G.Dart) (vertex : V) :
    s(dart.snd, vertex) = dart.edge ↔ vertex = dart.fst := by
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff']
  simp [eq_comm]

private theorem mk_ne_edge_of_ne {V : Type u} {G : SimpleGraph V}
    (dart : G.Dart) {vertex other : V}
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    s(vertex, other) ≠ dart.edge := by
  intro equal
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff'] at equal
  rcases equal with equal | equal
  · exact notFst equal.1.symm
  · exact notSnd equal.2.symm

private theorem neighborFinset_deleteEdge_fst
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).neighborFinset dart.fst =
      (G.neighborFinset dart.fst).erase dart.snd := by
  ext vertex
  simp [SimpleGraph.deleteEdges_adj, mk_fst_eq_edge_iff, and_comm]

private theorem neighborFinset_deleteEdge_snd
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).neighborFinset dart.snd =
      (G.neighborFinset dart.snd).erase dart.fst := by
  ext vertex
  simp [SimpleGraph.deleteEdges_adj, mk_snd_eq_edge_iff, and_comm]

private theorem neighborFinset_deleteEdge_other
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) (vertex : V)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (G.deleteEdges {dart.edge}).neighborFinset vertex =
      G.neighborFinset vertex := by
  ext other
  simp [SimpleGraph.deleteEdges_adj,
    mk_ne_edge_of_ne dart notFst notSnd]

private theorem degree_deleteEdge_fst_add_one
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).degree dart.fst + 1 =
      G.degree dart.fst := by
  change #((G.deleteEdges {dart.edge}).neighborFinset dart.fst) + 1 =
    #(G.neighborFinset dart.fst)
  rw [neighborFinset_deleteEdge_fst]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset dart.fst dart.snd).2 dart.adj)

private theorem degree_deleteEdge_snd_add_one
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).degree dart.snd + 1 =
      G.degree dart.snd := by
  change #((G.deleteEdges {dart.edge}).neighborFinset dart.snd) + 1 =
    #(G.neighborFinset dart.snd)
  rw [neighborFinset_deleteEdge_snd]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset dart.snd dart.fst).2 dart.adj.symm)

private theorem degree_deleteEdge_other
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) (vertex : V)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (G.deleteEdges {dart.edge}).degree vertex = G.degree vertex := by
  change #((G.deleteEdges {dart.edge}).neighborFinset vertex) =
    #(G.neighborFinset vertex)
  rw [neighborFinset_deleteEdge_other dart vertex notFst notSnd]

private theorem deleteEdge_preserves_minDegree_aux
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (dart : G.Dart) (bound : Nat)
    (baseline : bound ≤ G.minDegree)
    (fstSlack : bound + 1 ≤ G.degree dart.fst)
    (sndSlack : bound + 1 ≤ G.degree dart.snd) :
    bound ≤ (G.deleteEdges {dart.edge}).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro vertex
  by_cases isFst : vertex = dart.fst
  · subst vertex
    have drop := degree_deleteEdge_fst_add_one dart
    omega
  · by_cases isSnd : vertex = dart.snd
    · subst vertex
      have drop := degree_deleteEdge_snd_add_one dart
      omega
    · rw [degree_deleteEdge_other dart vertex isFst isSnd]
      exact baseline.trans (G.minDegree_le_degree vertex)

namespace FiniteObject

/-- Deleting an actual edge lowers its first endpoint degree by exactly one. -/
theorem degree_deleteEdge_fst_add_one (object : FiniteObject.{u})
    (dart : object.graph.Dart) :
    (object.deleteEdge (object.edgeOfDart dart)).degree dart.fst + 1 =
      object.degree dart.fst := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {dart.edge}).degree dart.fst + 1 =
    object.graph.degree dart.fst
  exact _root_.Hypostructure.Graph.degree_deleteEdge_fst_add_one dart

/-- Deleting an actual edge lowers its second endpoint degree by exactly one. -/
theorem degree_deleteEdge_snd_add_one (object : FiniteObject.{u})
    (dart : object.graph.Dart) :
    (object.deleteEdge (object.edgeOfDart dart)).degree dart.snd + 1 =
      object.degree dart.snd := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {dart.edge}).degree dart.snd + 1 =
    object.graph.degree dart.snd
  exact _root_.Hypostructure.Graph.degree_deleteEdge_snd_add_one dart

/-- Every non-endpoint degree is unchanged by one-edge deletion. -/
theorem degree_deleteEdge_other (object : FiniteObject.{u})
    (dart : object.graph.Dart) (vertex : object.Vertex)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (object.deleteEdge (object.edgeOfDart dart)).degree vertex =
      object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {dart.edge}).degree vertex =
    object.graph.degree vertex
  exact _root_.Hypostructure.Graph.degree_deleteEdge_other
    dart vertex notFst notSnd

/-- Endpoint slack is sufficient to preserve a minimum-degree lower bound
under deletion of the dart's undirected edge. -/
theorem deleteEdge_preserves_minDegree (object : FiniteObject.{u})
    (dart : object.graph.Dart) (bound : Nat)
    (baseline : bound ≤ object.minDegree)
    (fstSlack : bound + 1 ≤ object.degree dart.fst)
    (sndSlack : bound + 1 ≤ object.degree dart.snd) :
    bound ≤ (object.deleteEdge (object.edgeOfDart dart)).minDegree := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : Nonempty object.Vertex := ⟨dart.fst⟩
  change bound ≤ (object.graph.deleteEdges {dart.edge}).minDegree
  exact deleteEdge_preserves_minDegree_aux dart bound baseline
    fstSlack sndSlack

end FiniteObject

/-- Graph-specific inputs needed to turn no-proper-baseline minimality into
pointwise edge-deletion criticality.  The fields describe only the baseline;
they do not allow a caller to provide the endpoint conclusion. -/
structure DeletionCriticalityProfile
    (Baseline : FiniteObject.{u} → Prop) where
  threshold : Nat
  degreeLowerBound : ∀ {object : FiniteObject.{u}},
    Baseline object → threshold ≤ object.minDegree
  deleteEdgePreserves : ∀ {object : FiniteObject.{u}}
    (dart : object.graph.Dart),
    Baseline object →
    threshold + 1 ≤ object.degree dart.fst →
    threshold + 1 ≤ object.degree dart.snd →
    Baseline (object.deleteEdge (object.edgeOfDart dart))

/-- The canonical graph baseline at minimum-degree threshold `k`. -/
def MinimumDegreeAtLeast (k : Nat) (object : FiniteObject.{u}) : Prop :=
  k ≤ object.minDegree

/-- Fully graph-owned profile for the pure minimum-degree baseline. -/
def minimumDegreeDeletionCriticalityProfile (k : Nat) :
    DeletionCriticalityProfile (MinimumDegreeAtLeast k) where
  threshold := k
  degreeLowerBound := fun baseline => baseline
  deleteEdgePreserves := by
    intro object dart baseline fstSlack sndSlack
    exact object.deleteEdge_preserves_minDegree dart k baseline
      fstSlack sndSlack

/-! ## Edge-deletion criticality

For a minimum-degree threshold, an edge is critical when one endpoint has
degree exactly the threshold.  Vertices at least one above the threshold are
the slack carriers, and their comparison relation is adjacency. -/

namespace DeletionCriticalityProfile

variable {Baseline : FiniteObject.{u} → Prop}

/-- The atomic modification of an edge-deletion profile is critical exactly
when one of its endpoints already sits at the threshold. -/
abbrev Critical (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) (dart : object.graph.Dart) : Prop :=
  object.degree dart.fst = profile.threshold ∨
    object.degree dart.snd = profile.threshold

/-- The carriers compared by the incompatibility node: the vertices holding at
least one unit of degree slack above the threshold. -/
abbrev Carrier (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) : Type u :=
  { vertex : object.Vertex // profile.threshold + 1 ≤ object.degree vertex }

/-- Deleting a non-critical dart preserves the baseline: both endpoints keep a
unit of slack, so the profile's own one-edge accounting applies. -/
theorem baseline_of_not_critical (profile : DeletionCriticalityProfile Baseline)
    {object : FiniteObject.{u}} (baseline : Baseline object)
    (dart : object.graph.Dart) (noncritical : ¬ profile.Critical object dart) :
    Baseline (object.deleteEdge (object.edgeOfDart dart)) := by
  have fstLower : profile.threshold ≤ object.degree dart.fst :=
    (profile.degreeLowerBound baseline).trans
      (object.minDegree_le_degree dart.fst)
  have sndLower : profile.threshold ≤ object.degree dart.snd :=
    (profile.degreeLowerBound baseline).trans
      (object.minDegree_le_degree dart.snd)
  have fstNe : object.degree dart.fst ≠ profile.threshold :=
    fun equal => noncritical (Or.inl equal)
  have sndNe : object.degree dart.snd ≠ profile.threshold :=
    fun equal => noncritical (Or.inr equal)
  exact profile.deleteEdgePreserves dart baseline (by omega) (by omega)

/-- An edge joining two slack carriers is a non-critical dart. -/
theorem noncritical_of_related (profile : DeletionCriticalityProfile Baseline)
    {object : FiniteObject.{u}} (tight slack : profile.Carrier object)
    (adjacent : object.graph.Adj tight.1 slack.1) :
    ¬ profile.Critical object ⟨(tight.1, slack.1), adjacent⟩ := by
  intro critical
  rcases critical with tightAt | slackAt
  · exact (Nat.not_succ_le_self profile.threshold) (tight.2.trans_eq tightAt)
  · exact (Nat.not_succ_le_self profile.threshold) (slack.2.trans_eq slackAt)

end DeletionCriticalityProfile

/-- Graph-coordinate projection of the criticality and slack-incompatibility
entries appended by Core. -/
structure DeletionCriticalityCertificate
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) : Prop where
  private mk ::
  /-- Every dart has an endpoint at the threshold. -/
  tightEndpoint : ∀ dart : ctx.G.graph.Dart,
    ctx.G.degree dart.fst = profile.threshold ∨
      ctx.G.degree dart.snd = profile.threshold
  /-- Vertices at least one above the threshold are pairwise nonadjacent. -/
  slackVerticesIndependent : ∀ {left right : ctx.G.Vertex},
    profile.threshold + 1 ≤ ctx.G.degree left →
    profile.threshold + 1 ≤ ctx.G.degree right →
    Not (ctx.G.graph.Adj left right)

end Hypostructure.Graph
