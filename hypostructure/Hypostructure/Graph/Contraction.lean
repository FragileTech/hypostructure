import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths
import Hypostructure.Graph.Deletion
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Target

/-!
# Edge contraction and the return of every ordered edge

This file implements the finite-graph operation that contracts one edge: the
head of an ordered edge is deleted and its remaining incidences are transplanted
onto the tail.  The operation is independent of any cycle-length family.

Its target-facing theorem is the graph-theoretic statement that an object with
no accepted cycle, meeting a baseline, and minimal for the registered
lexicographic order has a simple return for every ordered edge whose two
endpoints pay for the merged vertex: the tail and the head stay joined after the
edge itself is deleted.  Equivalently, no such edge is a bridge.

The argument is the one contraction supports and nothing more.  Assume some
ordered edge has no return.  Then

* the two endpoints have no common neighbour, so the contraction preserves every
  degree away from the tail and gives the tail the sum of the two endpoint
  degrees less two, which is the file's standing degree hypothesis;
* the contraction has one vertex fewer, so minimality supplies it an accepted
  cycle;
* a cycle of the contraction meets the tail in two edges, each of which is
  either an original tail incidence or a transplanted head incidence.  A mixed
  pair would splice into a return, so the two are of the same kind, and the
  cycle is then read back into the source either along the vertex-deletion
  embedding or along the map that sends the tail to the head.

That accepted cycle contradicts avoidance.
-/

namespace Hypostructure.Graph

open scoped Sym2

universe u v

namespace FiniteObject

/-- Contract the ordered edge `(tail, head)`: delete `head` and transplant its
incidences onto `tail`.  The irreflexivity guard of `SimpleGraph.fromRel` is
what discards the contracted edge itself. -/
abbrev contractEdge (object : FiniteObject.{u}) (tail head : object.Vertex) :
    FiniteObject.{u} where
  Vertex := (object.deleteVertex head).Vertex
  graph := SimpleGraph.fromRel fun left right =>
    object.graph.Adj left.1 right.1 ∨
      (left.1 = tail ∧ object.graph.Adj head right.1)
  vertices := (object.deleteVertex head).vertices
  decideAdj := by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidableRel object.graph.Adj := object.decideAdj
    letI : DecidableEq (object.deleteVertex head).Vertex :=
      (object.deleteVertex head).vertices.decEq
    intro left right
    rw [SimpleGraph.fromRel_adj]
    infer_instance

@[simp]
theorem contractEdge_adj (object : FiniteObject.{u})
    (tail head : object.Vertex)
    (left right : (object.contractEdge tail head).Vertex) :
    (object.contractEdge tail head).graph.Adj left right ↔
      left ≠ right ∧
        (object.graph.Adj left.1 right.1 ∨
          (left.1 = tail ∧ object.graph.Adj head right.1) ∨
          (right.1 = tail ∧ object.graph.Adj head left.1)) := by
  change (SimpleGraph.fromRel _).Adj left right ↔ _
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨different, (old | new) | (old | new)⟩
    · exact ⟨different, Or.inl old⟩
    · exact ⟨different, Or.inr (Or.inl new)⟩
    · exact ⟨different, Or.inl old.symm⟩
    · exact ⟨different, Or.inr (Or.inr new)⟩
  · rintro ⟨different, old | new | reversed⟩
    · exact ⟨different, Or.inl (Or.inl old)⟩
    · exact ⟨different, Or.inl (Or.inr new)⟩
    · exact ⟨different, Or.inr (Or.inr reversed)⟩

@[simp]
theorem vertexCount_contractEdge (object : FiniteObject.{u})
    (tail head : object.Vertex) :
    (object.contractEdge tail head).vertexCount =
      (object.deleteVertex head).vertexCount :=
  rfl

end FiniteObject

/-- One ordered edge of a finite object, read as the contraction datum: the
`head` is the endpoint that disappears and the `tail` is the endpoint that
absorbs its incidences. -/
structure EdgeContraction (object : FiniteObject.{u}) where
  /-- The endpoint that survives the contraction. -/
  tail : object.Vertex
  /-- The endpoint that is absorbed into the tail. -/
  head : object.Vertex
  /-- The two endpoints span an edge. -/
  adjacent : object.graph.Adj tail head

namespace EdgeContraction

variable {object : FiniteObject.{u}}

/-- The contracted object. -/
abbrev contracted (contraction : EdgeContraction object) : FiniteObject.{u} :=
  object.contractEdge contraction.tail contraction.head

/-- The surviving endpoint, as a vertex of the contracted object. -/
def tailVertex (contraction : EdgeContraction object) :
    contraction.contracted.Vertex :=
  ⟨contraction.tail, by
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact Finset.mem_erase.mpr
      ⟨contraction.adjacent.ne, object.mem_vertexFinset contraction.tail⟩⟩

@[simp]
theorem tailVertex_val (contraction : EdgeContraction object) :
    contraction.tailVertex.1 = contraction.tail :=
  rfl

theorem ne_head (contraction : EdgeContraction object)
    (vertex : contraction.contracted.Vertex) : vertex.1 ≠ contraction.head := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.ne_of_mem_erase vertex.2

@[simp]
theorem contracted_adj (contraction : EdgeContraction object)
    (left right : contraction.contracted.Vertex) :
    contraction.contracted.graph.Adj left right ↔
      left ≠ right ∧
        (object.graph.Adj left.1 right.1 ∨
          (left.1 = contraction.tail ∧
            object.graph.Adj contraction.head right.1) ∨
          (right.1 = contraction.tail ∧
            object.graph.Adj contraction.head left.1)) :=
  FiniteObject.contractEdge_adj object contraction.tail contraction.head
    left right

/-- Away from the tail the contracted object is the source object. -/
theorem contracted_adj_of_ne_tail (contraction : EdgeContraction object)
    {left right : contraction.contracted.Vertex}
    (leftNe : left ≠ contraction.tailVertex)
    (rightNe : right ≠ contraction.tailVertex) :
    contraction.contracted.graph.Adj left right ↔
      object.graph.Adj left.1 right.1 := by
  rw [contraction.contracted_adj]
  constructor
  · rintro ⟨_, old | ⟨isTail, _⟩ | ⟨isTail, _⟩⟩
    · exact old
    · exact (leftNe (Subtype.ext isTail)).elim
    · exact (rightNe (Subtype.ext isTail)).elim
  · intro old
    exact ⟨fun equality => old.ne (congrArg Subtype.val equality), Or.inl old⟩

/-- At the tail the contracted object carries exactly the two transplanted
incidence families. -/
theorem contracted_adj_tail (contraction : EdgeContraction object)
    (vertex : contraction.contracted.Vertex) :
    contraction.contracted.graph.Adj contraction.tailVertex vertex ↔
      vertex ≠ contraction.tailVertex ∧
        (object.graph.Adj contraction.tail vertex.1 ∨
          object.graph.Adj contraction.head vertex.1) := by
  rw [contraction.contracted_adj]
  constructor
  · rintro ⟨different, old | ⟨_, transplanted⟩ | ⟨isTail, _⟩⟩
    · exact ⟨fun equality => different equality.symm, Or.inl old⟩
    · exact ⟨fun equality => different equality.symm, Or.inr transplanted⟩
    · exact (different (Subtype.ext isTail.symm)).elim
  · rintro ⟨different, old | transplanted⟩
    · exact ⟨fun equality => different equality.symm, Or.inl old⟩
    · exact ⟨fun equality => different equality.symm,
        Or.inr (Or.inl ⟨rfl, transplanted⟩)⟩

/-! ## The severed object and the return of an ordered edge -/

/-- The source graph with the contracted edge itself deleted. -/
def severed (contraction : EdgeContraction object) :
    SimpleGraph object.Vertex :=
  object.graph.deleteEdges {s(contraction.tail, contraction.head)}

/-- **`R_e(G)`**: a simple path from the tail of the ordered edge back to its
head after that edge is deleted. -/
def HasReturn (contraction : EdgeContraction object) : Prop :=
  Nonempty (contraction.severed.Path contraction.tail contraction.head)

theorem severed_adj (contraction : EdgeContraction object)
    {left right : object.Vertex} :
    contraction.severed.Adj left right ↔
      object.graph.Adj left right ∧
        s(left, right) ≠ s(contraction.tail, contraction.head) := by
  simp [severed, SimpleGraph.deleteEdges_adj]

/-- An edge of the source survives severing as soon as one of its endpoints is
neither endpoint of the contracted edge. -/
theorem severed_adj_of_avoids (contraction : EdgeContraction object)
    {left right : object.Vertex} (adjacent : object.graph.Adj left right)
    (avoids : (left ≠ contraction.tail ∧ left ≠ contraction.head) ∨
      (right ≠ contraction.tail ∧ right ≠ contraction.head)) :
    contraction.severed.Adj left right := by
  refine contraction.severed_adj.mpr ⟨adjacent, ?_⟩
  intro equality
  rw [Sym2.eq_iff] at equality
  rcases equality with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩ <;>
    rcases avoids with ⟨notTail, notHead⟩ | ⟨notTail, notHead⟩
  · exact notTail leftEq
  · exact notHead rightEq
  · exact notHead leftEq
  · exact notTail rightEq

/-- Without a return, no walk at all joins the two endpoints after severing. -/
theorem false_of_severed_walk (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn)
    (walk : contraction.severed.Walk contraction.tail contraction.head) :
    False := by
  classical
  exact noReturn ⟨walk.toPath⟩

/-- **Without a return the two endpoints have no common neighbour.**  A common
neighbour is a triangle on the contracted edge, and a triangle is a return. -/
theorem not_common_neighbour (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn) {vertex : object.Vertex}
    (notTail : vertex ≠ contraction.tail)
    (notHead : vertex ≠ contraction.head)
    (fromTail : object.graph.Adj contraction.tail vertex)
    (fromHead : object.graph.Adj contraction.head vertex) : False := by
  refine contraction.false_of_severed_walk noReturn
    (SimpleGraph.Walk.cons (v := vertex) ?_
      (SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil))
  · exact contraction.severed_adj_of_avoids fromTail (Or.inr ⟨notTail, notHead⟩)
  · exact contraction.severed_adj_of_avoids fromHead.symm
      (Or.inl ⟨notTail, notHead⟩)

/-! ## Degrees of the contracted object -/

theorem image_neighborSet_of_ne_tail (contraction : EdgeContraction object)
    {vertex : contraction.contracted.Vertex}
    (notTail : vertex ≠ contraction.tailVertex)
    (notFromHead : ¬ object.graph.Adj contraction.head vertex.1) :
    Subtype.val '' (contraction.contracted.graph.neighborSet vertex) =
      object.graph.neighborSet vertex.1 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  ext other
  constructor
  · rintro ⟨candidate, adjacent, rfl⟩
    replace adjacent : contraction.contracted.graph.Adj vertex candidate :=
      adjacent
    rw [contraction.contracted_adj] at adjacent
    rcases adjacent with ⟨_, old | ⟨isTail, _⟩ | ⟨_, fromHead⟩⟩
    · exact old
    · exact (notTail (Subtype.ext isTail)).elim
    · exact (notFromHead fromHead).elim
  · intro member
    replace member : object.graph.Adj vertex.1 other := member
    have notHead : other ≠ contraction.head := by
      rintro rfl
      exact notFromHead member.symm
    have memErase : other ∈ object.vertexFinset.erase contraction.head :=
      Finset.mem_erase.mpr ⟨notHead, object.mem_vertexFinset other⟩
    refine ⟨⟨other, memErase⟩, ?_, rfl⟩
    show contraction.contracted.graph.Adj vertex ⟨other, memErase⟩
    rw [contraction.contracted_adj]
    exact ⟨fun equality => member.ne (congrArg Subtype.val equality),
      Or.inl member⟩

theorem image_neighborSet_of_adj_head (contraction : EdgeContraction object)
    {vertex : contraction.contracted.Vertex}
    (notTail : vertex ≠ contraction.tailVertex)
    (fromHead : object.graph.Adj contraction.head vertex.1) :
    Subtype.val '' (contraction.contracted.graph.neighborSet vertex) =
      insert contraction.tail
        (object.graph.neighborSet vertex.1 \ {contraction.head}) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  ext other
  constructor
  · rintro ⟨candidate, adjacent, rfl⟩
    replace adjacent : contraction.contracted.graph.Adj vertex candidate :=
      adjacent
    rw [contraction.contracted_adj] at adjacent
    rcases adjacent with ⟨_, old | ⟨isTail, _⟩ | ⟨isTail, _⟩⟩
    · exact Set.mem_insert_of_mem _ ⟨old, contraction.ne_head candidate⟩
    · exact (notTail (Subtype.ext isTail)).elim
    · exact isTail ▸ Set.mem_insert _ _
  · intro member
    rcases Set.mem_insert_iff.mp member with rfl | ⟨adjacent, notHead⟩
    · refine ⟨contraction.tailVertex, ?_, rfl⟩
      show contraction.contracted.graph.Adj vertex contraction.tailVertex
      rw [contraction.contracted_adj]
      exact ⟨notTail, Or.inr (Or.inr ⟨rfl, fromHead⟩)⟩
    · have memErase : other ∈ object.vertexFinset.erase contraction.head :=
        Finset.mem_erase.mpr ⟨notHead, object.mem_vertexFinset other⟩
      refine ⟨⟨other, memErase⟩, ?_, rfl⟩
      show contraction.contracted.graph.Adj vertex ⟨other, memErase⟩
      rw [contraction.contracted_adj]
      exact ⟨fun equality => adjacent.ne (congrArg Subtype.val equality),
        Or.inl adjacent⟩

theorem image_neighborSet_tail (contraction : EdgeContraction object) :
    Subtype.val ''
        (contraction.contracted.graph.neighborSet contraction.tailVertex) =
      (object.graph.neighborSet contraction.tail \ {contraction.head}) ∪
        (object.graph.neighborSet contraction.head \ {contraction.tail}) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  ext other
  constructor
  · rintro ⟨candidate, adjacent, rfl⟩
    replace adjacent :
        contraction.contracted.graph.Adj contraction.tailVertex candidate :=
      adjacent
    rw [contraction.contracted_adj_tail] at adjacent
    obtain ⟨different, fromTail | fromHead⟩ := adjacent
    · exact Or.inl ⟨fromTail, contraction.ne_head candidate⟩
    · exact Or.inr ⟨fromHead, fun equality =>
        different (Subtype.ext equality)⟩
  · intro member
    have notHead : other ≠ contraction.head := by
      rcases member with ⟨_, notHead⟩ | ⟨adjacent, _⟩
      · exact notHead
      · exact fun equality => (equality ▸ adjacent).ne rfl
    have notTail : other ≠ contraction.tail := by
      rcases member with ⟨adjacent, _⟩ | ⟨_, notTail⟩
      · exact fun equality => (equality ▸ adjacent).ne rfl
      · exact notTail
    have memErase : other ∈ object.vertexFinset.erase contraction.head :=
      Finset.mem_erase.mpr ⟨notHead, object.mem_vertexFinset other⟩
    refine ⟨⟨other, memErase⟩, ?_, rfl⟩
    show contraction.contracted.graph.Adj contraction.tailVertex
      ⟨other, memErase⟩
    rw [contraction.contracted_adj_tail]
    refine ⟨fun equality => notTail (congrArg Subtype.val equality), ?_⟩
    rcases member with ⟨adjacent, _⟩ | ⟨adjacent, _⟩
    · exact Or.inl adjacent
    · exact Or.inr adjacent

theorem degree_contracted_of_ne_tail (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn)
    {vertex : contraction.contracted.Vertex}
    (notTail : vertex ≠ contraction.tailVertex) :
    contraction.contracted.degree vertex = object.degree vertex.1 := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  have imageCard :
      contraction.contracted.degree vertex =
        (Subtype.val ''
          (contraction.contracted.graph.neighborSet vertex)).ncard := by
    rw [FiniteObject.degree_eq_ncard_neighborSet,
      Set.ncard_image_of_injective _ Subtype.val_injective]
    rfl
  rw [imageCard, FiniteObject.degree_eq_ncard_neighborSet]
  by_cases fromHead : object.graph.Adj contraction.head vertex.1
  · rw [contraction.image_neighborSet_of_adj_head notTail fromHead]
    have valNe : vertex.1 ≠ contraction.tail := fun equality =>
      notTail (Subtype.ext equality)
    have notFromTail : ¬ object.graph.Adj contraction.tail vertex.1 := by
      intro fromTail
      exact contraction.not_common_neighbour noReturn valNe
        (fun equality => (equality ▸ fromHead).ne rfl) fromTail fromHead
    have tailNotMem :
        contraction.tail ∉
          object.graph.neighborSet vertex.1 \ {contraction.head} := by
      rintro ⟨adjacent, _⟩
      exact notFromTail adjacent.symm
    have headMem : contraction.head ∈ object.graph.neighborSet vertex.1 :=
      fromHead.symm
    rw [Set.ncard_insert_of_notMem tailNotMem (Set.toFinite _)]
    have restore :
        (object.graph.neighborSet vertex.1 \ {contraction.head}).ncard + 1 =
          (object.graph.neighborSet vertex.1).ncard :=
      Set.ncard_sdiff_singleton_add_one headMem (Set.toFinite _)
    omega
  · rw [contraction.image_neighborSet_of_ne_tail notTail fromHead]

theorem degree_contracted_tail (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn) :
    contraction.contracted.degree contraction.tailVertex + 2 =
      object.degree contraction.tail + object.degree contraction.head := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  have imageCard :
      contraction.contracted.degree contraction.tailVertex =
        (Subtype.val ''
          (contraction.contracted.graph.neighborSet
            contraction.tailVertex)).ncard := by
    rw [FiniteObject.degree_eq_ncard_neighborSet,
      Set.ncard_image_of_injective _ Subtype.val_injective]
    rfl
  have disjoint :
      Disjoint
        (object.graph.neighborSet contraction.tail \ {contraction.head})
        (object.graph.neighborSet contraction.head \ {contraction.tail}) := by
    rw [Set.disjoint_left]
    rintro other ⟨fromTail, notHead⟩ ⟨fromHead, notTail⟩
    exact contraction.not_common_neighbour noReturn notTail notHead
      fromTail fromHead
  have tailDrop :
      (object.graph.neighborSet contraction.tail \
          {contraction.head}).ncard + 1 =
        (object.graph.neighborSet contraction.tail).ncard :=
    Set.ncard_sdiff_singleton_add_one contraction.adjacent (Set.toFinite _)
  have headDrop :
      (object.graph.neighborSet contraction.head \
          {contraction.tail}).ncard + 1 =
        (object.graph.neighborSet contraction.head).ncard :=
    Set.ncard_sdiff_singleton_add_one contraction.adjacent.symm (Set.toFinite _)
  rw [imageCard, contraction.image_neighborSet_tail,
    Set.ncard_union_eq disjoint (Set.toFinite _) (Set.toFinite _),
    FiniteObject.degree_eq_ncard_neighborSet,
    FiniteObject.degree_eq_ncard_neighborSet]
  omega

/-- **The contraction meets the same baseline.**  Every vertex other than the
tail keeps its source degree, and the tail carries both endpoint degrees less
the contracted edge counted once at each end. -/
theorem minDegree_contracted (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn) (threshold : Nat)
    (degreeSum : threshold + 2 ≤
      object.degree contraction.tail + object.degree contraction.head)
    (baseline : threshold ≤ object.minDegree) :
    threshold ≤ contraction.contracted.minDegree := by
  letI : Nonempty contraction.contracted.Vertex := ⟨contraction.tailVertex⟩
  refine contraction.contracted.le_minDegree_of_forall_le_degree threshold ?_
  intro vertex
  by_cases isTail : vertex = contraction.tailVertex
  · subst isTail
    have tailDegree := contraction.degree_contracted_tail noReturn
    omega
  · rw [contraction.degree_contracted_of_ne_tail noReturn isTail]
    exact le_trans baseline (object.minDegree_le_degree vertex.1)

/-! ## Reading a cycle of the contraction back into the source -/

/-- The source object pulled back along a relabelling of the contracted
vertices.  Two relabellings are used: the inclusion, which returns the
vertex-deleted object, and `merge`, which identifies the tail with the head. -/
abbrev pullback (contraction : EdgeContraction object)
    (label : contraction.contracted.Vertex → object.Vertex) :
    FiniteObject.{u} where
  Vertex := contraction.contracted.Vertex
  graph := SimpleGraph.comap label object.graph
  vertices := contraction.contracted.vertices
  decideAdj := fun left right => object.decideAdj (label left) (label right)

@[simp]
theorem pullback_adj (contraction : EdgeContraction object)
    (label : contraction.contracted.Vertex → object.Vertex)
    (left right : contraction.contracted.Vertex) :
    (contraction.pullback label).graph.Adj left right ↔
      object.graph.Adj (label left) (label right) :=
  Iff.rfl

/-- The relabelling, read as a homomorphism out of the pulled-back object. -/
def pullbackHom (contraction : EdgeContraction object)
    (label : contraction.contracted.Vertex → object.Vertex) :
    (contraction.pullback label).graph →g object.graph where
  toFun := label
  map_rel' := id

/-- The map that identifies the tail with the head: it is the inclusion away
from the tail, and it is injective because the head is not a vertex of the
contraction. -/
def merge (contraction : EdgeContraction object)
    (vertex : contraction.contracted.Vertex) : object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  if vertex.1 = contraction.tail then contraction.head else vertex.1

@[simp]
theorem merge_tailVertex (contraction : EdgeContraction object) :
    contraction.merge contraction.tailVertex = contraction.head := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [merge]

theorem merge_of_ne_tail (contraction : EdgeContraction object)
    {vertex : contraction.contracted.Vertex}
    (notTail : vertex ≠ contraction.tailVertex) :
    contraction.merge vertex = vertex.1 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have valNe : vertex.1 ≠ contraction.tail := fun equality =>
    notTail (Subtype.ext equality)
  simp [merge, valNe]

theorem merge_injective (contraction : EdgeContraction object) :
    Function.Injective contraction.merge := by
  intro left right equality
  by_cases leftTail : left = contraction.tailVertex <;>
    by_cases rightTail : right = contraction.tailVertex
  · rw [leftTail, rightTail]
  · rw [leftTail, contraction.merge_tailVertex,
      contraction.merge_of_ne_tail rightTail] at equality
    exact (contraction.ne_head right equality.symm).elim
  · rw [rightTail, contraction.merge_tailVertex,
      contraction.merge_of_ne_tail leftTail] at equality
    exact (contraction.ne_head left equality).elim
  · rw [contraction.merge_of_ne_tail leftTail,
      contraction.merge_of_ne_tail rightTail] at equality
    exact Subtype.ext equality

theorem severed_adj_of_ne_head (contraction : EdgeContraction object)
    {left right : object.Vertex} (adjacent : object.graph.Adj left right)
    (leftNe : left ≠ contraction.head) (rightNe : right ≠ contraction.head) :
    contraction.severed.Adj left right := by
  refine contraction.severed_adj.mpr ⟨adjacent, ?_⟩
  intro equality
  rw [Sym2.eq_iff] at equality
  rcases equality with ⟨_, rightEq⟩ | ⟨leftEq, _⟩
  · exact rightNe rightEq
  · exact leftNe leftEq

/-- A walk of the contraction that avoids the tail is a walk of the source with
the contracted edge deleted: none of its edges was transplanted, and none of its
vertices is either endpoint of that edge. -/
theorem severedWalk_of_avoids_tail (contraction : EdgeContraction object)
    {source target : contraction.contracted.Vertex}
    (walk : contraction.contracted.graph.Walk source target)
    (avoidsTail : contraction.tailVertex ∉ walk.support) :
    Nonempty (contraction.severed.Walk source.1 target.1) := by
  have kept : ∀ edge ∈ walk.edges,
      edge ∈ (contraction.pullback Subtype.val).graph.edgeSet := by
    intro edge member
    revert member
    induction edge using Sym2.ind with
    | _ left right =>
      intro member
      have leftNe : left ≠ contraction.tailVertex := by
        rintro rfl
        exact avoidsTail (walk.fst_mem_support_of_mem_edges member)
      have rightNe : right ≠ contraction.tailVertex := by
        rintro rfl
        exact avoidsTail (walk.snd_mem_support_of_mem_edges member)
      have adjacent : contraction.contracted.graph.Adj left right :=
        walk.edges_subset_edgeSet member
      exact (contraction.contracted_adj_of_ne_tail leftNe rightNe).mp adjacent
  let mapped :=
    (walk.transfer _ kept).map (contraction.pullbackHom Subtype.val)
  have severedEdges : ∀ edge ∈ mapped.edges,
      edge ∈ contraction.severed.edgeSet := by
    intro edge member
    revert member
    induction edge using Sym2.ind with
    | _ left right =>
      intro member
      have adjacent : object.graph.Adj left right :=
        mapped.edges_subset_edgeSet member
      have images : mapped.support =
          (walk.transfer _ kept).support.map
            (contraction.pullbackHom Subtype.val) :=
        SimpleGraph.Walk.support_map
          (f := contraction.pullbackHom Subtype.val) (p := walk.transfer _ kept)
      refine contraction.severed_adj_of_ne_head adjacent ?_ ?_
      · obtain ⟨candidate, _, image⟩ := List.mem_map.1
          (images ▸ mapped.fst_mem_support_of_mem_edges member)
        exact image ▸ contraction.ne_head candidate
      · obtain ⟨candidate, _, image⟩ := List.mem_map.1
          (images ▸ mapped.snd_mem_support_of_mem_edges member)
        exact image ▸ contraction.ne_head candidate
  exact ⟨mapped.transfer _ severedEdges⟩

/-- **A cycle of the contraction cannot change kind at the tail.**  If one of
its two tail incidences is an original tail edge and the other is a transplanted
head edge, splicing them along the rest of the cycle is a return of the
contracted edge. -/
theorem false_of_mixed_incidences (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn)
    {source target : contraction.contracted.Vertex}
    (walk : contraction.contracted.graph.Walk source target)
    (avoidsTail : contraction.tailVertex ∉ walk.support)
    (fromHead : object.graph.Adj contraction.head source.1)
    (fromTail : object.graph.Adj contraction.tail target.1) : False := by
  obtain ⟨image⟩ := contraction.severedWalk_of_avoids_tail walk avoidsTail
  have sourceNotTail : source.1 ≠ contraction.tail := by
    intro equality
    have isTail : source = contraction.tailVertex := Subtype.ext equality
    exact avoidsTail (isTail ▸ walk.start_mem_support)
  have firstEdge : contraction.severed.Adj contraction.tail target.1 :=
    contraction.severed_adj_of_ne_head fromTail
      (fun equality => contraction.adjacent.ne equality)
      (contraction.ne_head target)
  have lastEdge : contraction.severed.Adj source.1 contraction.head :=
    contraction.severed_adj_of_avoids fromHead.symm
      (Or.inl ⟨sourceNotTail, contraction.ne_head source⟩)
  exact contraction.false_of_severed_walk noReturn
    (SimpleGraph.Walk.cons firstEdge
      (image.reverse.append
        (SimpleGraph.Walk.cons lastEdge SimpleGraph.Walk.nil)))

/-- A cycle of the contraction all of whose edges are edges of the source under
one injective relabelling is a cycle of the source of the same length. -/
def certificateOfPullback {LengthOK : Nat → Prop}
    (contraction : EdgeContraction object)
    (label : contraction.contracted.Vertex → object.Vertex)
    (injective : Function.Injective label)
    (certificate : CycleCertificate contraction.contracted LengthOK)
    (labelled : ∀ edge ∈ certificate.walk.edges,
      edge ∈ (contraction.pullback label).graph.edgeSet) :
    CycleCertificate object LengthOK :=
  CycleCertificate.mapHom (contraction.pullbackHom label) injective
    { vertex := certificate.vertex
      walk := certificate.walk.transfer _ labelled
      isCycle := certificate.isCycle.transfer labelled
      length_ok := by
        rw [SimpleGraph.Walk.length_transfer]
        exact certificate.length_ok }


theorem vertexCount_contracted_lt (contraction : EdgeContraction object) :
    contraction.contracted.vertexCount < object.vertexCount := by
  have exactDrop := object.vertexCount_deleteVertex_add_one contraction.head
  change contraction.contracted.vertexCount + 1 = object.vertexCount at exactDrop
  omega

theorem lexicographicallySmaller (contraction : EdgeContraction object) :
    contraction.contracted.LexicographicallySmaller object :=
  FiniteObject.lexicographicallySmaller_of_vertexCount_lt
    contraction.vertexCount_contracted_lt

/-! ## Bridgelessness -/

/-- **`lem:bridgeless`.**  A minimal object avoiding the cycle target has a
simple return for every ordered edge whose two endpoint degrees pay for the
contraction: after deleting that edge its endpoints are still joined.
Equivalently, no such edge is a bridge, so every one of them lies on a cycle.

The degree hypothesis is exactly what the merged vertex costs -- the contracted
edge is counted once at each endpoint -- and at the manuscript's baseline of
three it is implied by the baseline alone.

The contraction of the edge is smaller, meets the same baseline, and therefore
carries an accepted cycle; that cycle is a cycle of the source unless it changes
kind at the tail, which would itself be the return. -/
theorem hasReturn_of_minimal {LengthOK : Nat → Prop} {threshold : Nat}
    (contraction : EdgeContraction object)
    (degreeSum : threshold + 2 ≤
      object.degree contraction.tail + object.degree contraction.head)
    (baseline : threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller) :
    contraction.HasReturn := by
  classical
  by_contra noReturn
  obtain ⟨certificate⟩ :=
    minimal contraction.contracted contraction.lexicographicallySmaller
      (contraction.minDegree_contracted noReturn threshold degreeSum baseline)
  refine avoids ?_
  by_cases tailMem : contraction.tailVertex ∈ certificate.walk.support
  case neg =>
    refine ⟨contraction.certificateOfPullback Subtype.val
      Subtype.val_injective certificate ?_⟩
    intro edge member
    revert member
    induction edge using Sym2.ind with
    | _ left right =>
      intro member
      have leftNe : left ≠ contraction.tailVertex := by
        rintro rfl
        exact tailMem (certificate.walk.fst_mem_support_of_mem_edges member)
      have rightNe : right ≠ contraction.tailVertex := by
        rintro rfl
        exact tailMem (certificate.walk.snd_mem_support_of_mem_edges member)
      exact (contraction.contracted_adj_of_ne_tail leftNe rightNe).mp
        (certificate.walk.edges_subset_edgeSet member)
  case pos =>
    -- Rotate the cycle to the tail and read its two tail incidences.
    let rotated := certificate.walk.rotate contraction.tailVertex tailMem
    have rotatedCycle : rotated.IsCycle := certificate.isCycle.rotate tailMem
    have rotatedLength : rotated.length = certificate.walk.length :=
      certificate.walk.length_rotate contraction.tailVertex tailMem
    let rotatedCertificate :
        CycleCertificate contraction.contracted LengthOK :=
      { vertex := contraction.tailVertex
        walk := rotated
        isCycle := rotatedCycle
        length_ok := rotatedLength ▸ certificate.length_ok }
    have notNil : ¬ rotated.Nil := rotatedCycle.not_nil
    have firstAdj :
        contraction.contracted.graph.Adj contraction.tailVertex rotated.snd :=
      rotated.adj_snd notNil
    have rebuilt : (SimpleGraph.Walk.cons firstAdj rotated.tail).IsCycle := by
      rw [rotated.cons_tail_eq notNil]
      exact rotatedCycle
    have forwardData :=
      (SimpleGraph.Walk.cons_isCycle_iff rotated.tail firstAdj).mp rebuilt
    let back := rotated.tail.reverse
    have backPath : back.IsPath := forwardData.1.reverse
    have backNotNil : ¬ back.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      have three := rotatedCycle.three_le_length
      have drop := rotated.length_tail_add_one notNil
      have reversed : back.length = rotated.tail.length :=
        SimpleGraph.Walk.length_reverse rotated.tail
      omega
    have secondAdj :
        contraction.contracted.graph.Adj contraction.tailVertex back.snd :=
      back.adj_snd backNotNil
    have backRebuilt : (SimpleGraph.Walk.cons secondAdj back.tail).IsPath := by
      rw [back.cons_tail_eq backNotNil]
      exact backPath
    have backData :=
      (SimpleGraph.Walk.cons_isPath_iff secondAdj back.tail).mp backRebuilt
    -- Every edge of the rotated cycle is one of the two tail incidences or an
    -- edge of the remaining path, which avoids the tail.
    have edgeCases : ∀ edge ∈ rotated.edges,
        edge = s(contraction.tailVertex, rotated.snd) ∨
          edge = s(contraction.tailVertex, back.snd) ∨
            edge ∈ back.tail.edges := by
      intro edge member
      rw [← rotated.cons_tail_eq notNil, SimpleGraph.Walk.edges_cons,
        List.mem_cons] at member
      rcases member with first | later
      · exact Or.inl first
      · have inBack : edge ∈ back.edges := by
          change edge ∈ rotated.tail.reverse.edges
          rw [SimpleGraph.Walk.edges_reverse]
          exact List.mem_reverse.mpr later
        rw [← back.cons_tail_eq backNotNil, SimpleGraph.Walk.edges_cons,
          List.mem_cons] at inBack
        rcases inBack with second | inner
        · exact Or.inr (Or.inl second)
        · exact Or.inr (Or.inr inner)
    have inner : ∀ label : contraction.contracted.Vertex → object.Vertex,
        (∀ vertex : contraction.contracted.Vertex,
          vertex ≠ contraction.tailVertex → label vertex = vertex.1) →
        ∀ edge ∈ back.tail.edges,
          edge ∈ (contraction.pullback label).graph.edgeSet := by
      intro label agrees edge member
      revert member
      induction edge using Sym2.ind with
      | _ left right =>
        intro member
        have leftNe : left ≠ contraction.tailVertex := by
          rintro rfl
          exact backData.2 (back.tail.fst_mem_support_of_mem_edges member)
        have rightNe : right ≠ contraction.tailVertex := by
          rintro rfl
          exact backData.2 (back.tail.snd_mem_support_of_mem_edges member)
        have adjacent : object.graph.Adj left.1 right.1 :=
          (contraction.contracted_adj_of_ne_tail leftNe rightNe).mp
            (back.tail.edges_subset_edgeSet member)
        show object.graph.Adj (label left) (label right)
        rw [agrees left leftNe, agrees right rightNe]
        exact adjacent
    obtain ⟨forwardNotTail, forwardKind⟩ :=
      (contraction.contracted_adj_tail rotated.snd).mp firstAdj
    obtain ⟨backNotTail, backKind⟩ :=
      (contraction.contracted_adj_tail back.snd).mp secondAdj
    rcases forwardKind with forwardTail | forwardHead
    · rcases backKind with backTail | backHead
      · -- Both incidences survived the contraction.
        refine ⟨contraction.certificateOfPullback Subtype.val
          Subtype.val_injective rotatedCertificate ?_⟩
        intro edge member
        rcases edgeCases edge member with first | second | later
        · exact first ▸ forwardTail
        · exact second ▸ backTail
        · exact inner Subtype.val (fun _ _ => rfl) edge later
      · -- Mixed: the rest of the cycle splices into a return.
        exact (contraction.false_of_mixed_incidences noReturn back.tail
          backData.2 backHead forwardTail).elim
    · rcases backKind with backTail | backHead
      · -- Mixed in the other orientation.
        refine (contraction.false_of_mixed_incidences noReturn
          back.tail.reverse ?_ forwardHead backTail).elim
        rw [SimpleGraph.Walk.support_reverse]
        exact fun member => backData.2 (List.mem_reverse.mp member)
      · -- Both incidences were transplanted from the head.
        refine ⟨contraction.certificateOfPullback contraction.merge
          contraction.merge_injective rotatedCertificate ?_⟩
        intro edge member
        rcases edgeCases edge member with first | second | later
        · rw [first]
          show object.graph.Adj (contraction.merge contraction.tailVertex)
            (contraction.merge rotated.snd)
          rw [contraction.merge_tailVertex,
            contraction.merge_of_ne_tail forwardNotTail]
          exact forwardHead
        · rw [second]
          show object.graph.Adj (contraction.merge contraction.tailVertex)
            (contraction.merge back.snd)
          rw [contraction.merge_tailVertex,
            contraction.merge_of_ne_tail backNotTail]
          exact backHead
        · exact inner contraction.merge
            (fun _ notTail => contraction.merge_of_ne_tail notTail) edge later

/-- `lem:bridgeless` at a registered minimal-counterexample context: the same
statement with the baseline, the avoidance and the minimality read off the
context rather than passed separately. -/
theorem hasReturn_of_minimality
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (contraction : EdgeContraction context.G)
    (degreeSum : threshold + 2 ≤
      context.G.degree contraction.tail + context.G.degree contraction.head) :
    contraction.HasReturn :=
  contraction.hasReturn_of_minimal degreeSum context.baseline context.avoids
    (fun _ smaller baseline => context.target_of_smaller smaller baseline)

end EdgeContraction

end Hypostructure.Graph
