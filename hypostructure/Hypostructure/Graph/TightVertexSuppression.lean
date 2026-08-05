import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths
import Hypostructure.Graph.Minimality

/-!
# Tight-vertex suppression

This file implements the finite-graph operation that removes a tight
degree-three vertex and joins its two non-central neighbours.  The operation
is independent of any cycle-length family.  Its target-facing theorem uses
only Graph's registered lexicographic minimality and cycle target.
-/

namespace Hypostructure.Graph

open scoped Sym2

universe u v

namespace FiniteObject

/-- Add one undirected edge while retaining the incoming finite vertex
schedule.  Simplicity is inherited from Mathlib's `SimpleGraph.edge` and
lattice supremum. -/
abbrev addEdge (object : FiniteObject.{u})
    (left right : object.Vertex) : FiniteObject.{u} where
  Vertex := object.Vertex
  graph := object.graph ⊔ SimpleGraph.edge left right
  vertices := object.vertices
  decideAdj := by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel object.graph.Adj := object.decideAdj
    infer_instance

@[simp]
theorem addEdge_adj (object : FiniteObject.{u})
    (left right u w : object.Vertex) :
    (object.addEdge left right).graph.Adj u w ↔
      object.graph.Adj u w ∨
        (((u = left ∧ w = right) ∨ (u = right ∧ w = left)) ∧ u ≠ w) := by
  simp only [addEdge, SimpleGraph.sup_adj, SimpleGraph.edge_adj]

theorem addEdge_adj_of_ne (object : FiniteObject.{u})
    (left right u w : object.Vertex) (different : left ≠ right) :
    (object.addEdge left right).graph.Adj u w ↔
      object.graph.Adj u w ∨
        (u = left ∧ w = right) ∨ (u = right ∧ w = left) := by
  rw [addEdge_adj]
  constructor
  · rintro (old | ⟨new, _⟩)
    · exact Or.inl old
    · exact Or.inr new
  · rintro (old | new)
    · exact Or.inl old
    · refine Or.inr ⟨new, ?_⟩
      rintro rfl
      rcases new with ⟨rfl, equality⟩ | ⟨rfl, equality⟩
      · exact different equality
      · exact different equality.symm

@[simp]
theorem vertexCount_addEdge (object : FiniteObject.{u})
    (left right : object.Vertex) :
    (object.addEdge left right).vertexCount = object.vertexCount :=
  rfl

private theorem neighborSet_addEdge_left
    (object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right) :
    (object.addEdge left right).graph.neighborSet left =
      insert right (object.graph.neighborSet left) := by
  ext vertex
  rw [SimpleGraph.mem_neighborSet,
    addEdge_adj_of_ne object left right left vertex different]
  change
    (object.graph.Adj left vertex ∨
      (left = left ∧ vertex = right) ∨
      (left = right ∧ vertex = left)) ↔
        vertex = right ∨ object.graph.Adj left vertex
  constructor
  · rintro (old | same | impossible)
    · exact Or.inr old
    · exact Or.inl same.2
    · exact (different impossible.1).elim
  · rintro (new | old)
    · exact Or.inr (Or.inl ⟨rfl, new⟩)
    · exact Or.inl old

theorem degree_addEdge_left
    (object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right) (missing : ¬ object.graph.Adj left right) :
    (object.addEdge left right).degree left = object.degree left + 1 := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change
    (object.graph ⊔ SimpleGraph.edge left right).degree left =
      object.graph.degree left + 1
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard]
  change
    ((object.addEdge left right).graph.neighborSet left).ncard =
      (object.graph.neighborSet left).ncard + 1
  rw [neighborSet_addEdge_left object left right different]
  exact Set.ncard_insert_of_notMem
    (by
      intro member
      exact missing ((object.graph.mem_neighborSet left right).mp member))
    ((Set.finite_univ (α := object.Vertex)).subset (Set.subset_univ _))

theorem degree_addEdge_right
    (object : FiniteObject.{u}) (left right : object.Vertex)
    (different : left ≠ right) (missing : ¬ object.graph.Adj left right) :
    (object.addEdge left right).degree right = object.degree right + 1 := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have neighborSetEq :
      (object.addEdge left right).graph.neighborSet right =
        insert left (object.graph.neighborSet right) := by
    ext vertex
    rw [SimpleGraph.mem_neighborSet,
      addEdge_adj_of_ne object left right right vertex different]
    change
      (object.graph.Adj right vertex ∨
        (right = left ∧ vertex = right) ∨
        (right = right ∧ vertex = left)) ↔
          vertex = left ∨ object.graph.Adj right vertex
    constructor
    · rintro (old | impossible | same)
      · exact Or.inr old
      · exact (different impossible.1.symm).elim
      · exact Or.inl same.2
    · rintro (new | old)
      · exact Or.inr (Or.inr ⟨rfl, new⟩)
      · exact Or.inl old
  change
    (object.graph ⊔ SimpleGraph.edge left right).degree right =
      object.graph.degree right + 1
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard]
  change
    ((object.addEdge left right).graph.neighborSet right).ncard =
      (object.graph.neighborSet right).ncard + 1
  rw [neighborSetEq]
  exact Set.ncard_insert_of_notMem
      (s := object.graph.neighborSet right)
      (a := left)
      (by
        intro member
        exact missing ((object.graph.mem_neighborSet right left).mp member).symm)
      ((Set.finite_univ (α := object.Vertex)).subset (Set.subset_univ _))

theorem degree_addEdge_of_ne
    (object : FiniteObject.{u}) (left right vertex : object.Vertex)
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right) :
    (object.addEdge left right).degree vertex = object.degree vertex := by
  rw [(object.addEdge left right).degree_eq_ncard_neighborSet,
    object.degree_eq_ncard_neighborSet]
  congr 1
  ext other
  rw [SimpleGraph.mem_neighborSet,
    addEdge_adj object left right vertex other]
  constructor
  · rintro (old | ⟨leftCase | rightCase, _⟩)
    · exact old
    · exact (notLeft leftCase.1).elim
    · exact (notRight rightCase.1).elim
  · exact Or.inl

/-- A non-neighbour keeps its exact degree after vertex deletion. -/
theorem degree_deleteVertex_of_not_adj
    (object : FiniteObject.{u}) (vertex : object.Vertex)
    (remaining : (object.deleteVertex vertex).Vertex)
    (notAdjacent : ¬ object.graph.Adj vertex remaining.1) :
    (object.deleteVertex vertex).degree remaining =
      object.degree remaining.1 := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have closed :
      object.graph.neighborSet remaining.1 ⊆
        (@Finset.erase object.Vertex object.vertices.decEq
          object.vertexFinset vertex : Set object.Vertex) := by
    intro other adjacent
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
      object.mem_vertexFinset, Set.mem_singleton_iff, true_and]
    rintro rfl
    exact notAdjacent adjacent.symm
  exact object.degree_induce_of_neighborSet_subset
    (@Finset.erase object.Vertex object.vertices.decEq
      object.vertexFinset vertex) remaining closed

end FiniteObject

namespace TightVertexSuppression

/-- Literal local data for suppressing a degree-three vertex.  The three
neighbours are named and pairwise distinct; `neighbors` excludes every fourth
neighbour.  The centre is the only endpoint allowed to lose one unit of
degree. -/
structure Configuration (object : FiniteObject.{u}) where
  vertex : object.Vertex
  center : object.Vertex
  left : object.Vertex
  right : object.Vertex
  vertex_center : object.graph.Adj vertex center
  vertex_left : object.graph.Adj vertex left
  vertex_right : object.graph.Adj vertex right
  neighbors : ∀ other, object.graph.Adj vertex other →
    other = center ∨ other = left ∨ other = right
  center_ne_left : center ≠ left
  center_ne_right : center ≠ right
  left_ne_right : left ≠ right
  shoulder_missing : ¬ object.graph.Adj left right

variable {object : FiniteObject.{u}}

namespace Configuration

def deleted (configuration : Configuration object) : FiniteObject.{u} :=
  object.deleteVertex configuration.vertex

def centerVertex (configuration : Configuration object) :
    configuration.deleted.Vertex :=
  ⟨configuration.center, by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact Finset.mem_erase.mpr
      ⟨(object.graph.ne_of_adj configuration.vertex_center).symm,
        object.mem_vertexFinset configuration.center⟩⟩

def leftVertex (configuration : Configuration object) :
    configuration.deleted.Vertex :=
  ⟨configuration.left, by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact Finset.mem_erase.mpr
      ⟨(object.graph.ne_of_adj configuration.vertex_left).symm,
        object.mem_vertexFinset configuration.left⟩⟩

def rightVertex (configuration : Configuration object) :
    configuration.deleted.Vertex :=
  ⟨configuration.right, by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact Finset.mem_erase.mpr
      ⟨(object.graph.ne_of_adj configuration.vertex_right).symm,
        object.mem_vertexFinset configuration.right⟩⟩

/-- Delete the tight vertex and add its missing shoulder edge. -/
abbrev suppressed (configuration : Configuration object) : FiniteObject.{u} :=
  configuration.deleted.addEdge
    configuration.leftVertex configuration.rightVertex

/-- The suppression operation changes only the graph on the deleted vertex
type, so every suppressed vertex is canonically a deleted-graph vertex. -/
def toDeleted (configuration : Configuration object)
    (vertex : configuration.suppressed.Vertex) :
    configuration.deleted.Vertex := by
  change configuration.deleted.Vertex at vertex
  exact vertex

@[simp]
theorem toDeleted_val (configuration : Configuration object)
    (vertex : configuration.suppressed.Vertex) :
    (configuration.toDeleted vertex).1 = vertex.1 :=
  rfl

@[simp]
theorem deleted_adj (configuration : Configuration object)
    (u w : configuration.deleted.Vertex) :
    configuration.deleted.graph.Adj u w ↔ object.graph.Adj u.1 w.1 := by
  simp [deleted, FiniteObject.deleteVertex, FiniteObject.induce]

@[simp]
theorem suppressed_adj (configuration : Configuration object)
    (u w : configuration.suppressed.Vertex) :
    configuration.suppressed.graph.Adj u w ↔
      object.graph.Adj u.1 w.1 ∨
        (u.1 = configuration.left ∧ w.1 = configuration.right) ∨
        (u.1 = configuration.right ∧ w.1 = configuration.left) := by
  change
    (configuration.deleted.addEdge
      configuration.leftVertex configuration.rightVertex).graph.Adj u w ↔ _
  rw [FiniteObject.addEdge_adj_of_ne _ _ _ _ _
    (by
      intro equality
      exact configuration.left_ne_right (congrArg Subtype.val equality))]
  rw [deleted_adj]
  constructor
  · rintro (old | leftRight | rightLeft)
    · exact Or.inl old
    · exact Or.inr (Or.inl
        ⟨congrArg Subtype.val leftRight.1,
          congrArg Subtype.val leftRight.2⟩)
    · exact Or.inr (Or.inr
        ⟨congrArg Subtype.val rightLeft.1,
          congrArg Subtype.val rightLeft.2⟩)
  · rintro (old | leftRight | rightLeft)
    · exact Or.inl old
    · exact Or.inr (Or.inl
        ⟨Subtype.ext leftRight.1, Subtype.ext leftRight.2⟩)
    · exact Or.inr (Or.inr
        ⟨Subtype.ext rightLeft.1, Subtype.ext rightLeft.2⟩)

theorem leftVertex_ne_rightVertex (configuration : Configuration object) :
    configuration.leftVertex ≠ configuration.rightVertex := by
  intro equality
  exact configuration.left_ne_right (congrArg Subtype.val equality)

theorem shoulder_missing_deleted (configuration : Configuration object) :
    ¬ configuration.deleted.graph.Adj
      configuration.leftVertex configuration.rightVertex := by
  change ¬ object.graph.Adj configuration.left configuration.right
  exact configuration.shoulder_missing

@[simp]
theorem vertexCount_suppressed (configuration : Configuration object) :
    configuration.suppressed.vertexCount + 1 = object.vertexCount := by
  change
    (configuration.deleted.addEdge
      configuration.leftVertex configuration.rightVertex).vertexCount + 1 =
      object.vertexCount
  rw [FiniteObject.vertexCount_addEdge]
  exact object.vertexCount_deleteVertex_add_one configuration.vertex

theorem vertexCount_suppressed_lt (configuration : Configuration object) :
    configuration.suppressed.vertexCount < object.vertexCount := by
  have exactDrop := configuration.vertexCount_suppressed
  omega

theorem lexicographicallySmaller (configuration : Configuration object) :
    configuration.suppressed.LexicographicallySmaller object :=
  FiniteObject.lexicographicallySmaller_of_vertexCount_lt
    configuration.vertexCount_suppressed_lt

private theorem degree_left (configuration : Configuration object) :
    configuration.suppressed.degree configuration.leftVertex =
      object.degree configuration.left := by
  change
    (configuration.deleted.addEdge
      configuration.leftVertex configuration.rightVertex).degree
        configuration.leftVertex = _
  rw [configuration.deleted.degree_addEdge_left
      configuration.leftVertex configuration.rightVertex
      configuration.leftVertex_ne_rightVertex
      configuration.shoulder_missing_deleted]
  have deletionDrop :=
    object.degree_deleteVertex_of_adj configuration.vertex
      configuration.leftVertex configuration.vertex_left
  change configuration.deleted.degree configuration.leftVertex + 1 =
    object.degree configuration.left at deletionDrop
  omega

private theorem degree_right (configuration : Configuration object) :
    configuration.suppressed.degree configuration.rightVertex =
      object.degree configuration.right := by
  change
    (configuration.deleted.addEdge
      configuration.leftVertex configuration.rightVertex).degree
        configuration.rightVertex = _
  rw [configuration.deleted.degree_addEdge_right
      configuration.leftVertex configuration.rightVertex
      configuration.leftVertex_ne_rightVertex
      configuration.shoulder_missing_deleted]
  have deletionDrop :=
    object.degree_deleteVertex_of_adj configuration.vertex
      configuration.rightVertex configuration.vertex_right
  change configuration.deleted.degree configuration.rightVertex + 1 =
    object.degree configuration.right at deletionDrop
  omega

private theorem degree_center (configuration : Configuration object) :
    configuration.suppressed.degree configuration.centerVertex + 1 =
      object.degree configuration.center := by
  change
    (configuration.deleted.addEdge
      configuration.leftVertex configuration.rightVertex).degree
        configuration.centerVertex + 1 = _
  rw [configuration.deleted.degree_addEdge_of_ne
      configuration.leftVertex configuration.rightVertex
      configuration.centerVertex]
  · exact object.degree_deleteVertex_of_adj configuration.vertex
      configuration.centerVertex configuration.vertex_center
  · exact fun equality =>
      configuration.center_ne_left (congrArg Subtype.val equality)
  · exact fun equality =>
      configuration.center_ne_right (congrArg Subtype.val equality)

/-- Suppression preserves an arbitrary minimum-degree threshold provided the
centre has one unit of strict slack.  Since the suppressed vertex has exactly
three distinct neighbours, any realizable threshold is automatically at most
three; no problem-specific constant is built into the operation. -/
theorem minimumDegree_preserved (configuration : Configuration object)
    (threshold : Nat)
    (baseline : threshold ≤ object.minDegree)
    (centerSlack : threshold < object.degree configuration.center) :
    threshold ≤ configuration.suppressed.minDegree := by
  letI : Nonempty configuration.suppressed.Vertex :=
    ⟨configuration.leftVertex⟩
  apply configuration.suppressed.le_minDegree_of_forall_le_degree threshold
  intro remaining
  by_cases leftCase : remaining.1 = configuration.left
  · have same : remaining = configuration.leftVertex := Subtype.ext leftCase
    subst remaining
    rw [configuration.degree_left]
    exact baseline.trans (object.minDegree_le_degree configuration.left)
  by_cases rightCase : remaining.1 = configuration.right
  · have same : remaining = configuration.rightVertex := Subtype.ext rightCase
    subst remaining
    rw [configuration.degree_right]
    exact baseline.trans (object.minDegree_le_degree configuration.right)
  by_cases centerCase : remaining.1 = configuration.center
  · have same : remaining = configuration.centerVertex := Subtype.ext centerCase
    subst remaining
    have drop := configuration.degree_center
    omega
  · have notAdjacent : ¬ object.graph.Adj configuration.vertex remaining.1 := by
      intro adjacent
      rcases configuration.neighbors remaining.1 adjacent with
        center | left | right
      · exact centerCase center
      · exact leftCase left
      · exact rightCase right
    change
      threshold ≤
        (configuration.deleted.addEdge
          configuration.leftVertex configuration.rightVertex).degree remaining
    rw [configuration.deleted.degree_addEdge_of_ne
        configuration.leftVertex configuration.rightVertex remaining]
    · change threshold ≤
        configuration.deleted.degree
          (configuration.toDeleted remaining)
      have exactDegree :=
        object.degree_deleteVertex_of_not_adj
          configuration.vertex (configuration.toDeleted remaining)
          (by simpa only [toDeleted_val] using notAdjacent)
      change configuration.deleted.degree (configuration.toDeleted remaining) =
        object.degree remaining.1 at exactDegree
      exact exactDegree.symm ▸
        baseline.trans (object.minDegree_le_degree remaining.1)
    · exact fun equality => leftCase (congrArg Subtype.val equality)
    · exact fun equality => rightCase (congrArg Subtype.val equality)

/-- The suppressed object meets the target, from the standing baseline and the
selected object's own minimality.

Minimality is taken in its raw graph form -- every lexicographically smaller
object meeting the baseline has an accepted cycle -- rather than through a
registered problem, so the theorem applies at any problem presentation whose
progress is the canonical lexicographic one. -/
theorem target_on_suppressed_of_minimal
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (baseline : threshold ≤ object.minDegree)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller)
    (configuration : Configuration object)
    (centerSlack : threshold < object.degree configuration.center) :
    HasCycleWithLength LengthOK configuration.suppressed :=
  minimal configuration.suppressed configuration.lexicographicallySmaller
    (configuration.minimumDegree_preserved threshold baseline centerSlack)

theorem target_on_suppressed_of_minimality
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (configuration : Configuration context.G)
    (centerSlack : threshold < context.G.degree configuration.center) :
    HasCycleWithLength LengthOK configuration.suppressed :=
  target_on_suppressed_of_minimal context.baseline
    (fun _ smaller baseline => context.target_of_smaller smaller baseline)
    configuration centerSlack

/-- Every suppressed edge other than the newly inserted shoulder edge is an
edge of the literal vertex-deleted graph. -/
theorem oldEdge_of_ne_shoulder
    (configuration : Configuration object)
    {edge : Sym2 configuration.suppressed.Vertex}
    (member : edge ∈ configuration.suppressed.graph.edgeSet)
    (different : edge ≠
      s(configuration.leftVertex, configuration.rightVertex)) :
    edge ∈ configuration.deleted.graph.edgeSet := by
  change edge ∈
    (configuration.deleted.graph ⊔
      SimpleGraph.edge configuration.leftVertex
        configuration.rightVertex).edgeSet at member
  rw [SimpleGraph.edgeSet_sup,
    SimpleGraph.edgeSet_edge_of_ne
      configuration.leftVertex_ne_rightVertex] at member
  rcases member with old | added
  · exact old
  · exact (different (Set.mem_singleton_iff.mp added)).elim

/-- If the source avoids the cycle target, every accepted cycle supplied by
minimality on the suppressed graph must use the inserted shoulder edge. -/
theorem cycle_uses_shoulder
    {LengthOK : Nat → Prop}
    (configuration : Configuration object)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate :
      CycleCertificate configuration.suppressed LengthOK) :
    s(configuration.leftVertex, configuration.rightVertex) ∈
      certificate.walk.edges := by
  by_contra avoidsShoulder
  have edgesOld :
      ∀ edge, edge ∈ certificate.walk.edges →
        edge ∈ configuration.deleted.graph.edgeSet := by
    intro edge member
    exact configuration.oldEdge_of_ne_shoulder
      (certificate.walk.edges_subset_edgeSet member)
      (fun equality => avoidsShoulder (equality ▸ member))
  let deletedWalk :=
    certificate.walk.transfer configuration.deleted.graph edgesOld
  have deletedCycle : deletedWalk.IsCycle :=
    certificate.isCycle.transfer edgesOld
  let deletedCertificate :
      CycleCertificate configuration.deleted LengthOK := {
    vertex := certificate.vertex
    walk := deletedWalk
    isCycle := deletedCycle
    length_ok := by
      change LengthOK deletedWalk.length
      rw [SimpleGraph.Walk.length_transfer]
      exact certificate.length_ok
  }
  let embedding := object.deleteVertexEmbedding configuration.vertex
  let sourceCertificate :
      CycleCertificate object LengthOK :=
    deletedCertificate.mapHom embedding.toHom embedding.injective
  exact avoids ⟨sourceCertificate⟩

private theorem exists_orientedCycle
    (configuration : Configuration object)
    {start : configuration.suppressed.Vertex}
    (cycle : configuration.suppressed.graph.Walk start start)
    (isCycle : cycle.IsCycle)
    (uses : s(configuration.leftVertex, configuration.rightVertex) ∈
      cycle.edges) :
    ∃ oriented :
        configuration.suppressed.graph.Walk
          configuration.leftVertex configuration.leftVertex,
      oriented.IsCycle ∧
        oriented.length = cycle.length ∧
        oriented.snd = configuration.rightVertex := by
  letI : DecidableEq configuration.suppressed.Vertex :=
    configuration.suppressed.vertices.decEq
  have leftMember :
      configuration.leftVertex ∈ cycle.support :=
    cycle.fst_mem_support_of_mem_edges uses
  let forward := cycle.rotate configuration.leftVertex leftMember
  have forwardCycle : forward.IsCycle :=
    isCycle.rotate leftMember
  have forwardUses :
      s(configuration.leftVertex, configuration.rightVertex) ∈
        forward.edges :=
    (cycle.rotate_edges configuration.leftVertex leftMember).mem_iff.mpr uses
  have forwardLength : forward.length = cycle.length :=
    cycle.length_rotate configuration.leftVertex leftMember
  by_cases firstIsRight : forward.snd = configuration.rightVertex
  · exact ⟨forward, forwardCycle, forwardLength, firstIsRight⟩
  · have forwardNotNil : ¬ forward.Nil := forwardCycle.not_nil
    have rebuilt :
        (SimpleGraph.Walk.cons (forward.adj_snd forwardNotNil)
          forward.tail).IsCycle := by
      rw [forward.cons_tail_eq forwardNotNil]
      exact forwardCycle
    have tailData :
        forward.tail.IsPath ∧
          s(configuration.leftVertex, forward.snd) ∉
            forward.tail.edges :=
      (SimpleGraph.Walk.cons_isCycle_iff forward.tail
        (forward.adj_snd forwardNotNil)).mp rebuilt
    have tailNotNil : ¬ forward.tail.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      have cycleLength := forwardCycle.three_le_length
      have exactDrop := forward.length_tail_add_one forwardNotNil
      omega
    have tailUses :
        s(configuration.leftVertex, configuration.rightVertex) ∈
          forward.tail.edges := by
      have split := forwardUses
      rw [← forward.cons_tail_eq forwardNotNil,
        SimpleGraph.Walk.edges_cons, List.mem_cons] at split
      rcases split with first | later
      · have rightIsSnd : configuration.rightVertex = forward.snd := by
          rw [Sym2.eq_iff] at first
          rcases first with same | reversed
          · exact same.2
          · exact (configuration.leftVertex_ne_rightVertex
              reversed.2.symm).elim
        exact (firstIsRight rightIsSnd.symm).elim
      · exact later
    have rightIsPenultimate :
        configuration.rightVertex = forward.tail.penultimate :=
      tailData.1.eq_penultimate_of_mem_edges tailUses
    have forwardPenultimate :
        forward.penultimate = forward.tail.penultimate := by
      calc
        forward.penultimate =
            (SimpleGraph.Walk.cons (forward.adj_snd forwardNotNil)
              forward.tail).penultimate := by
                rw [forward.cons_tail_eq forwardNotNil]
        _ = forward.tail.penultimate :=
          SimpleGraph.Walk.penultimate_cons_of_not_nil
            (forward.adj_snd forwardNotNil) forward.tail tailNotNil
    have reverseSnd :
        forward.reverse.snd = configuration.rightVertex := by
      rw [SimpleGraph.Walk.snd_reverse, forwardPenultimate]
      exact rightIsPenultimate.symm
    exact
      ⟨forward.reverse, forwardCycle.reverse,
        by simpa only [SimpleGraph.Walk.length_reverse] using forwardLength,
        reverseSnd⟩

/-- The exact path obtained by removing the inserted shoulder edge from one
suppressed cycle.  It lives in the literal vertex-deleted graph, remains
simple, and has predecessor length. -/
structure ReconstructedPath
    (configuration : Configuration object)
    {LengthOK : Nat → Prop}
    (certificate :
      CycleCertificate configuration.suppressed LengthOK) where
  path : configuration.deleted.graph.Walk
    configuration.leftVertex configuration.rightVertex
  isPath : path.IsPath
  length_add_one : path.length + 1 = certificate.walk.length
  length_eq_predecessor : path.length = certificate.walk.length - 1
  restored_length_ok : LengthOK (path.length + 1)

/-- Rotate a cycle to the inserted shoulder edge, delete that first edge, and
transfer every remaining old edge into `G-x`. -/
noncomputable def reconstructPath
    {LengthOK : Nat → Prop}
    (configuration : Configuration object)
    (certificate :
      CycleCertificate configuration.suppressed LengthOK)
    (uses : s(configuration.leftVertex, configuration.rightVertex) ∈
      certificate.walk.edges) :
    ReconstructedPath configuration certificate := by
  classical
  have orientedExists :=
    configuration.exists_orientedCycle certificate.walk
      certificate.isCycle uses
  let oriented := Classical.choose orientedExists
  have orientedData := Classical.choose_spec orientedExists
  have orientedCycle : oriented.IsCycle := orientedData.1
  have orientedLength : oriented.length = certificate.walk.length :=
    orientedData.2.1
  have orientedSnd : oriented.snd = configuration.rightVertex :=
    orientedData.2.2
  have orientedNotNil : ¬ oriented.Nil := orientedCycle.not_nil
  have rebuilt :
      (SimpleGraph.Walk.cons (oriented.adj_snd orientedNotNil)
        oriented.tail).IsCycle := by
    rw [oriented.cons_tail_eq orientedNotNil]
    exact orientedCycle
  have tailData :
      oriented.tail.IsPath ∧
        s(configuration.leftVertex, oriented.snd) ∉
          oriented.tail.edges :=
    (SimpleGraph.Walk.cons_isCycle_iff oriented.tail
      (oriented.adj_snd orientedNotNil)).mp rebuilt
  let returnWalk :
      configuration.suppressed.graph.Walk
        configuration.rightVertex configuration.leftVertex :=
    oriented.tail.copy orientedSnd rfl
  let shoulderPath :
      configuration.suppressed.graph.Walk
        configuration.leftVertex configuration.rightVertex :=
    returnWalk.reverse
  have shoulderPathIsPath : shoulderPath.IsPath := by
    dsimp [shoulderPath, returnWalk]
    apply SimpleGraph.Walk.IsPath.reverse
    exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr tailData.1
  have shoulderPathAvoids :
      s(configuration.leftVertex, configuration.rightVertex) ∉
        shoulderPath.edges := by
    dsimp [shoulderPath, returnWalk]
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse,
      SimpleGraph.Walk.edges_copy]
    simpa only [orientedSnd] using tailData.2
  have oldEdges :
      ∀ edge, edge ∈ shoulderPath.edges →
        edge ∈ configuration.deleted.graph.edgeSet := by
    intro edge member
    exact configuration.oldEdge_of_ne_shoulder
      (shoulderPath.edges_subset_edgeSet member)
      (fun equality => shoulderPathAvoids (equality ▸ member))
  let path :=
    shoulderPath.transfer configuration.deleted.graph oldEdges
  have pathIsPath : path.IsPath :=
    shoulderPathIsPath.transfer oldEdges
  have shoulderLength :
      shoulderPath.length + 1 = certificate.walk.length := by
    dsimp [shoulderPath, returnWalk]
    rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_copy]
    have exactDrop := oriented.length_tail_add_one orientedNotNil
    omega
  have pathLength : path.length + 1 = certificate.walk.length := by
    dsimp [path]
    rw [SimpleGraph.Walk.length_transfer]
    exact shoulderLength
  exact {
    path := path
    isPath := pathIsPath
    length_add_one := pathLength
    length_eq_predecessor := by omega
    restored_length_ok := by
      rw [pathLength]
      exact certificate.length_ok
  }

/-- **`lem:single-open-port-suppression-witness`**, at the raw graph
hypotheses: the standing baseline, the selected object's own avoidance, and its
own minimality.  Minimality supplies the cycle in the suppressed object, target
avoidance forces that cycle to use the inserted shoulder edge, and cycle
reconstruction returns the exact predecessor-length simple path in `G - x`
joining the two shoulders. -/
theorem singleSuppressionWitness_of_minimal
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (baseline : threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller)
    (configuration : Configuration object)
    (centerSlack : threshold < object.degree configuration.center) :
    ∃ certificate :
        CycleCertificate configuration.suppressed LengthOK,
      Nonempty (ReconstructedPath configuration certificate) := by
  obtain ⟨certificate⟩ :=
    configuration.target_on_suppressed_of_minimal baseline minimal centerSlack
  have uses := configuration.cycle_uses_shoulder avoids certificate
  exact ⟨certificate, ⟨configuration.reconstructPath certificate uses⟩⟩

/-- Complete singleton suppression witness generated by the framework:
minimality supplies the cycle, target avoidance forces the new edge, and
cycle reconstruction returns its exact predecessor-length path in `G-x`. -/
theorem singleSuppressionWitness_of_minimality
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (configuration : Configuration context.G)
    (centerSlack : threshold < context.G.degree configuration.center) :
    ∃ certificate :
        CycleCertificate configuration.suppressed LengthOK,
      Nonempty (ReconstructedPath configuration certificate) :=
  singleSuppressionWitness_of_minimal context.baseline context.avoids
    (fun _ smaller baseline => context.target_of_smaller smaller baseline)
    configuration centerSlack

end Configuration

end TightVertexSuppression

end Hypostructure.Graph
