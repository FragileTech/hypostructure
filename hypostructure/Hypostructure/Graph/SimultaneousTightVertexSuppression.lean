import Hypostructure.Graph.TightVertexSuppression

/-!
# Finite compatible suppression families

This file contains the graph-theoretic content of simultaneous suppression.
It is independent of any particular accepted set of cycle lengths.
-/

namespace Hypostructure.Graph

open scoped Sym2

universe u v

namespace TightVertexSuppression

variable {object : FiniteObject.{u}}

/-- A finite family of tight configurations in one graph.  Compatibility is
stated entirely in terms of literal vertices and shoulder chords. -/
structure CompatibleFamily (object : FiniteObject.{u}) where
  Index : Type u
  indices : FinEnum Index
  configuration : Index → Configuration object
  vertex_injective : Function.Injective (fun i => (configuration i).vertex)
  support_disjoint :
    ∀ ⦃i j⦄, i ≠ j →
      Disjoint
        ({(configuration i).vertex, (configuration i).left,
          (configuration i).right} : Set object.Vertex)
        {(configuration j).vertex, (configuration j).left,
          (configuration j).right}
  center_outside_support :
    ∀ i j,
      (configuration i).center ≠ (configuration j).vertex ∧
      (configuration i).center ≠ (configuration j).left ∧
      (configuration i).center ≠ (configuration j).right
  chord_injective :
    Function.Injective
      (fun i => s((configuration i).left, (configuration i).right))

namespace CompatibleFamily

noncomputable section

local instance : Fintype object.Vertex :=
  @FinEnum.instFintype _ object.vertices

local instance : DecidableEq object.Vertex :=
  object.vertices.decEq

local instance : DecidableRel object.graph.Adj :=
  object.decideAdj

instance (family : CompatibleFamily object) : Fintype family.Index :=
  @FinEnum.instFintype _ family.indices

instance (family : CompatibleFamily object) : DecidableEq family.Index :=
  family.indices.decEq

noncomputable def deletedVertices
    (family : CompatibleFamily object) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.univ.image (fun i => (family.configuration i).vertex)

noncomputable def remainingVertices
    (family : CompatibleFamily object) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact object.vertexFinset \ family.deletedVertices

noncomputable def suppressedGraph (family : CompatibleFamily object) :
    SimpleGraph {x // x ∈ family.remainingVertices} :=
  SimpleGraph.fromRel
    (fun x y =>
      object.graph.Adj x.1 y.1 ∨
      ∃ i,
        (x.1 = (family.configuration i).left ∧
          y.1 = (family.configuration i).right) ∨
        (x.1 = (family.configuration i).right ∧
          y.1 = (family.configuration i).left))

/-- Delete every selected tight vertex and add every selected shoulder
chord.  `SimpleGraph` supplies looplessness, so simplicity is a theorem of the
construction rather than an application obligation. -/
noncomputable def suppressed (family : CompatibleFamily object) : FiniteObject.{u} where
  Vertex := {x // x ∈ family.remainingVertices}
  graph := family.suppressedGraph
  vertices := by
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableEq object.Vertex := object.vertices.decEq
    letI : DecidablePred (fun x : object.Vertex =>
        x ∈ family.remainingVertices) := by
      intro x
      infer_instance
    exact FinEnum.Subtype.finEnum
      (fun x : object.Vertex => x ∈ family.remainingVertices)
  decideAdj := by
    classical
    infer_instance

def toRemaining (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    {x // x ∈ family.remainingVertices} := by
  change {x // x ∈ family.remainingVertices} at vertex
  exact vertex

@[simp]
theorem toRemaining_val (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    (family.toRemaining vertex).1 = vertex.1 :=
  rfl

@[simp]
theorem suppressed_adj (family : CompatibleFamily object)
    (x y : {x // x ∈ family.remainingVertices}) :
    family.suppressedGraph.Adj x y ↔
      object.graph.Adj x.1 y.1 ∨
      ∃ i,
        (x.1 = (family.configuration i).left ∧
          y.1 = (family.configuration i).right) ∨
        (x.1 = (family.configuration i).right ∧
          y.1 = (family.configuration i).left) := by
  rw [suppressedGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, forward | backward⟩
    · exact forward
    · rcases backward with old | ⟨i, lr | rl⟩
      · exact Or.inl old.symm
      · exact Or.inr ⟨i, Or.inr ⟨lr.2, lr.1⟩⟩
      · exact Or.inr ⟨i, Or.inl ⟨rl.2, rl.1⟩⟩
  · intro adjacent
    refine ⟨?_, Or.inl adjacent⟩
    rintro equality
    subst y
    rcases adjacent with old | ⟨i, lr | rl⟩
    · exact object.graph.loopless.irrefl _ old
    · exact (family.configuration i).left_ne_right
        (lr.1.symm.trans lr.2)
    · exact (family.configuration i).left_ne_right
        (rl.2.symm.trans rl.1)

theorem card_deletedVertices (family : CompatibleFamily object) :
    family.deletedVertices.card = Fintype.card family.Index := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp only [deletedVertices]
  calc
    (Finset.univ.image
        (fun i => (family.configuration i).vertex)).card =
        Finset.univ.card :=
      Finset.card_image_of_injective Finset.univ family.vertex_injective
    _ = Fintype.card family.Index := Finset.card_univ

theorem deletedVertices_subset (family : CompatibleFamily object) :
    family.deletedVertices ⊆ object.vertexFinset := by
  classical
  intro x hx
  simp only [deletedVertices, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  exact object.mem_vertexFinset _

theorem vertexCount_suppressed (family : CompatibleFamily object) :
    family.suppressed.vertexCount + Fintype.card family.Index =
      object.vertexCount := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [← object.card_vertexFinset]
  change family.suppressed.vertices.card +
    Fintype.card family.Index = object.vertexFinset.card
  rw [show family.suppressed.vertices.card =
      family.remainingVertices.card by
    simp [suppressed, FinEnum.card_eq_fintypeCard]]
  rw [remainingVertices, Finset.card_sdiff]
  have intersection :
      family.deletedVertices ∩ object.vertexFinset =
        family.deletedVertices :=
    Finset.inter_eq_left.mpr family.deletedVertices_subset
  have countLe :
      family.deletedVertices.card ≤ object.vertexFinset.card :=
    Finset.card_le_card family.deletedVertices_subset
  have countEq :
      family.deletedVertices.card = Fintype.card family.Index :=
    family.card_deletedVertices
  rw [intersection]
  omega

theorem vertexCount_suppressed_lt (family : CompatibleFamily object)
    [Nonempty family.Index] :
    family.suppressed.vertexCount < object.vertexCount := by
  have positive : 0 < Fintype.card family.Index := Fintype.card_pos
  have exactCount := family.vertexCount_suppressed
  omega

theorem lexicographicallySmaller (family : CompatibleFamily object)
    [Nonempty family.Index] :
    family.suppressed.LexicographicallySmaller object :=
  FiniteObject.lexicographicallySmaller_of_vertexCount_lt
    family.vertexCount_suppressed_lt

/-- Minimality is consumed only after Graph has established the literal
minimum-degree baseline for the simultaneously suppressed object. -/
theorem target_on_suppressed_of_minimality
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (family : CompatibleFamily context.G)
    [Nonempty family.Index]
    (preserved : threshold ≤ family.suppressed.minDegree) :
    HasCycleWithLength LengthOK family.suppressed :=
  context.target_of_smaller family.lexicographicallySmaller preserved

/-- Number of selected tight vertices whose deleted centre edge is incident
with `vertex`.  This is computed from the literal family schedule. -/
noncomputable def centerLoad (family : CompatibleFamily object)
    (vertex : object.Vertex) : Nat := by
  classical
  exact (Finset.univ.filter fun i =>
    (family.configuration i).center = vertex).card

/-- Literal post-suppression neighbour schedule of a surviving source
vertex.  It mentions only source vertices, deleted vertices, and shoulder
chords; in particular it is independently finite-checkable before packaging
the suppressed graph. -/
noncomputable def resultingNeighbors (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset object.Vertex := by
  classical
  exact family.remainingVertices.filter fun other =>
    object.graph.Adj vertex other ∨
    ∃ i,
      (vertex = (family.configuration i).left ∧
        other = (family.configuration i).right) ∨
      (vertex = (family.configuration i).right ∧
        other = (family.configuration i).left)

/-- The only threshold-specific input: the computed number of selected
centre edges fits in the literal degree slack. -/
def CenterCapacity (family : CompatibleFamily object)
    (threshold : Nat) : Prop :=
  ∀ vertex, vertex ∈ family.remainingVertices →
    family.centerLoad vertex ≤ object.degree vertex - threshold

instance centerCapacityDecidable (family : CompatibleFamily object)
    (threshold : Nat) : Decidable (family.CenterCapacity threshold) := by
  classical
  infer_instance

private theorem supportVertex_not_mem_deleted
    (family : CompatibleFamily object) (i : family.Index)
    {supportVertex : object.Vertex}
    (inSupport :
      supportVertex = (family.configuration i).left ∨
      supportVertex = (family.configuration i).right) :
    supportVertex ∉ family.deletedVertices := by
  classical
  intro member
  simp only [deletedVertices, Finset.mem_image, Finset.mem_univ,
    true_and] at member
  obtain ⟨j, deleted⟩ := member
  by_cases same : i = j
  · subst j
    rcases inSupport with rfl | rfl
    · exact (object.graph.ne_of_adj
        (family.configuration i).vertex_left) deleted
    · exact (object.graph.ne_of_adj
        (family.configuration i).vertex_right) deleted
  · have disjoint := Set.disjoint_left.mp (family.support_disjoint same)
    have hi : supportVertex ∈
        ({(family.configuration i).vertex,
          (family.configuration i).left,
          (family.configuration i).right} : Set object.Vertex) := by
      rcases inSupport with rfl | rfl <;> simp
    have hj : supportVertex ∈
        ({(family.configuration j).vertex,
          (family.configuration j).left,
          (family.configuration j).right} : Set object.Vertex) := by
      rw [← deleted]
      simp
    exact disjoint hi hj

private theorem center_not_mem_deleted
    (family : CompatibleFamily object) (i : family.Index) :
    (family.configuration i).center ∉ family.deletedVertices := by
  classical
  intro member
  simp only [deletedVertices, Finset.mem_image, Finset.mem_univ,
    true_and] at member
  obtain ⟨j, deleted⟩ := member
  exact (family.center_outside_support i j).1 deleted.symm

private theorem supportVertex_mem_remaining
    (family : CompatibleFamily object) (i : family.Index)
    {supportVertex : object.Vertex}
    (inSupport :
      supportVertex = (family.configuration i).left ∨
      supportVertex = (family.configuration i).right) :
    supportVertex ∈ family.remainingVertices := by
  classical
  simp only [remainingVertices, Finset.mem_sdiff,
    object.mem_vertexFinset, true_and]
  exact family.supportVertex_not_mem_deleted i inSupport

def leftRemaining (family : CompatibleFamily object)
    (i : family.Index) : {x // x ∈ family.remainingVertices} :=
  ⟨(family.configuration i).left,
    family.supportVertex_mem_remaining i (Or.inl rfl)⟩

def rightRemaining (family : CompatibleFamily object)
    (i : family.Index) : {x // x ∈ family.remainingVertices} :=
  ⟨(family.configuration i).right,
    family.supportVertex_mem_remaining i (Or.inr rfl)⟩

def leftSuppressed (family : CompatibleFamily object)
    (i : family.Index) : family.suppressed.Vertex := by
  change {x // x ∈ family.remainingVertices}
  exact family.leftRemaining i

def rightSuppressed (family : CompatibleFamily object)
    (i : family.Index) : family.suppressed.Vertex := by
  change {x // x ∈ family.remainingVertices}
  exact family.rightRemaining i

def chord (family : CompatibleFamily object)
    (i : family.Index) : Sym2 family.suppressed.Vertex :=
  s(family.leftSuppressed i, family.rightSuppressed i)

noncomputable def usedChords (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (cycle : family.suppressed.graph.Walk left right) : Finset family.Index := by
  classical
  exact Finset.univ.filter fun i => family.chord i ∈ cycle.edges

noncomputable def centerIndices (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset family.Index := by
  classical
  exact Finset.univ.filter fun i =>
    (family.configuration i).center = vertex

noncomputable def shoulderIndices (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset family.Index := by
  classical
  exact Finset.univ.filter fun i =>
    vertex = (family.configuration i).left ∨
    vertex = (family.configuration i).right

noncomputable def selectedNeighborIndices
    (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset family.Index := by
  classical
  exact Finset.univ.filter fun i =>
    (family.configuration i).center = vertex ∨
    vertex = (family.configuration i).left ∨
    vertex = (family.configuration i).right

noncomputable def deletedOldNeighbors
    (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset object.Vertex := by
  classical
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.neighborFinset vertex ∩ family.deletedVertices

noncomputable def retainedOldNeighbors
    (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset object.Vertex := by
  classical
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.neighborFinset vertex \ family.deletedVertices

noncomputable def oppositeShoulder (family : CompatibleFamily object)
    (vertex : object.Vertex) (i : family.Index) : object.Vertex := by
  classical
  exact if vertex = (family.configuration i).left then
      (family.configuration i).right
    else
      (family.configuration i).left

noncomputable def addedNeighbors (family : CompatibleFamily object)
    (vertex : object.Vertex) : Finset object.Vertex := by
  classical
  exact (family.shoulderIndices vertex).image
    (family.oppositeShoulder vertex)

private theorem oppositeShoulder_mem_support
    (family : CompatibleFamily object)
    {vertex : object.Vertex} {i : family.Index}
    (shoulder : i ∈ family.shoulderIndices vertex) :
    family.oppositeShoulder vertex i =
        (family.configuration i).left ∨
      family.oppositeShoulder vertex i =
        (family.configuration i).right := by
  classical
  simp only [shoulderIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at shoulder
  rcases shoulder with left | right
  · simp [oppositeShoulder, left]
  · by_cases isLeft : vertex = (family.configuration i).left
    · simp [oppositeShoulder, isLeft]
    · simp [oppositeShoulder, isLeft]

private theorem oppositeShoulder_is_other
    (family : CompatibleFamily object)
    {vertex : object.Vertex} {i : family.Index}
    (shoulder : i ∈ family.shoulderIndices vertex) :
    (vertex = (family.configuration i).left ∧
        family.oppositeShoulder vertex i =
          (family.configuration i).right) ∨
      (vertex = (family.configuration i).right ∧
        family.oppositeShoulder vertex i =
          (family.configuration i).left) := by
  classical
  simp only [shoulderIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at shoulder
  rcases shoulder with left | right
  · exact Or.inl ⟨left, by simp [oppositeShoulder, left]⟩
  · by_cases isLeft : vertex = (family.configuration i).left
    · exact Or.inl ⟨isLeft, by simp [oppositeShoulder, isLeft]⟩
    · exact Or.inr ⟨right, by simp [oppositeShoulder, isLeft]⟩

private theorem oppositeShoulder_injective
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    Set.InjOn (family.oppositeShoulder vertex)
      (family.shoulderIndices vertex : Set family.Index) := by
  intro i hi j hj equality
  by_contra different
  have disjoint := Set.disjoint_left.mp
    (family.support_disjoint different)
  have hiMem : family.oppositeShoulder vertex i ∈
      ({(family.configuration i).vertex,
        (family.configuration i).left,
        (family.configuration i).right} : Set object.Vertex) := by
    rcases family.oppositeShoulder_mem_support hi with h | h
    · simp [h]
    · simp [h]
  have hjMem : family.oppositeShoulder vertex i ∈
      ({(family.configuration j).vertex,
        (family.configuration j).left,
        (family.configuration j).right} : Set object.Vertex) := by
    rw [equality]
    rcases family.oppositeShoulder_mem_support hj with h | h
    · simp [h]
    · simp [h]
  exact disjoint hiMem hjMem

private theorem deletedOldNeighbors_eq_image
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    family.deletedOldNeighbors vertex =
      (family.selectedNeighborIndices vertex).image
        (fun i => (family.configuration i).vertex) := by
  classical
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ext other
  simp only [deletedOldNeighbors, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset, deletedVertices, Finset.mem_image,
    Finset.mem_univ, true_and, selectedNeighborIndices,
    Finset.mem_filter]
  constructor
  · rintro ⟨adjacent, ⟨i, rfl⟩⟩
    have role := (family.configuration i).neighbors vertex adjacent.symm
    exact ⟨i, by
      rcases role with center | left | right
      · exact ⟨Or.inl center.symm, rfl⟩
      · exact ⟨Or.inr (Or.inl left), rfl⟩
      · exact ⟨Or.inr (Or.inr right), rfl⟩⟩
  · rintro ⟨i, ⟨role, rfl⟩⟩
    refine ⟨?_, ⟨i, rfl⟩⟩
    rcases role with center | left | right
    · simpa [center] using (family.configuration i).vertex_center.symm
    · simpa [left] using (family.configuration i).vertex_left.symm
    · simpa [right] using (family.configuration i).vertex_right.symm

private theorem selectedNeighborIndices_disjoint_union
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    family.selectedNeighborIndices vertex =
      family.centerIndices vertex ∪ family.shoulderIndices vertex := by
  classical
  ext i
  simp [selectedNeighborIndices, centerIndices, shoulderIndices]

private theorem centerIndices_disjoint_shoulderIndices
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    Disjoint (family.centerIndices vertex)
      (family.shoulderIndices vertex) := by
  classical
  rw [Finset.disjoint_left]
  intro i center shoulder
  simp only [centerIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at center
  simp only [shoulderIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at shoulder
  rcases shoulder with left | right
  · exact (family.center_outside_support i i).2.1
      (center.trans left)
  · exact (family.center_outside_support i i).2.2
      (center.trans right)

private theorem card_deletedOldNeighbors
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    (family.deletedOldNeighbors vertex).card =
      family.centerLoad vertex +
        (family.shoulderIndices vertex).card := by
  classical
  rw [family.deletedOldNeighbors_eq_image]
  rw [Finset.card_image_of_injOn family.vertex_injective.injOn]
  rw [family.selectedNeighborIndices_disjoint_union,
    Finset.card_union_of_disjoint
      (family.centerIndices_disjoint_shoulderIndices vertex)]
  simp [centerLoad, centerIndices]

private theorem card_addedNeighbors
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    (family.addedNeighbors vertex).card =
      (family.shoulderIndices vertex).card := by
  classical
  rw [addedNeighbors,
    Finset.card_image_iff.mpr (family.oppositeShoulder_injective vertex)]

private theorem resultingNeighbors_eq_union
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    family.resultingNeighbors vertex =
      family.retainedOldNeighbors vertex ∪
        family.addedNeighbors vertex := by
  classical
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ext other
  simp only [resultingNeighbors, Finset.mem_filter,
    retainedOldNeighbors, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset, Finset.mem_union]
  constructor
  · rintro ⟨remaining, old | ⟨i, leftRight | rightLeft⟩⟩
    · exact Or.inl ⟨old, by
        simpa [remainingVertices] using remaining⟩
    · right
      simp only [addedNeighbors, Finset.mem_image]
      refine ⟨i, ?_, ?_⟩
      · simp [shoulderIndices, leftRight.1]
      · simpa [oppositeShoulder, leftRight.1] using leftRight.2.symm
    · right
      simp only [addedNeighbors, Finset.mem_image]
      refine ⟨i, ?_, ?_⟩
      · simp [shoulderIndices, rightLeft.1]
      · have notLeft :
          vertex ≠ (family.configuration i).left := by
          intro left
          exact (family.configuration i).left_ne_right
            (left.symm.trans rightLeft.1)
        simpa [oppositeShoulder, notLeft] using rightLeft.2.symm
  · rintro (retained | added)
    · exact ⟨by
        simp [remainingVertices, retained.2],
        Or.inl retained.1⟩
    · simp only [addedNeighbors, Finset.mem_image] at added
      obtain ⟨i, shoulder, rfl⟩ := added
      have support := family.oppositeShoulder_mem_support shoulder
      refine ⟨family.supportVertex_mem_remaining i support, Or.inr ?_⟩
      exact ⟨i, family.oppositeShoulder_is_other shoulder⟩

private theorem retainedOldNeighbors_disjoint_addedNeighbors
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    Disjoint (family.retainedOldNeighbors vertex)
      (family.addedNeighbors vertex) := by
  classical
  rw [Finset.disjoint_left]
  intro other retained added
  simp only [retainedOldNeighbors, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset] at retained
  simp only [addedNeighbors, Finset.mem_image] at added
  obtain ⟨i, shoulder, equality⟩ := added
  rcases family.oppositeShoulder_is_other shoulder with lr | rl
  · have old : object.graph.Adj
        (family.configuration i).left
        (family.configuration i).right := by
      have adjacent := retained.1
      rw [lr.1, ← equality, lr.2] at adjacent
      exact adjacent
    exact (family.configuration i).shoulder_missing old
  · have old : object.graph.Adj
        (family.configuration i).left
        (family.configuration i).right := by
      have adjacent := retained.1
      rw [rl.1, ← equality, rl.2] at adjacent
      exact adjacent.symm
    exact (family.configuration i).shoulder_missing old

private theorem card_resultingNeighbors
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    (family.resultingNeighbors vertex).card =
      (family.retainedOldNeighbors vertex).card +
        (family.shoulderIndices vertex).card := by
  classical
  rw [family.resultingNeighbors_eq_union,
    Finset.card_union_of_disjoint
      (family.retainedOldNeighbors_disjoint_addedNeighbors vertex),
    family.card_addedNeighbors]

private theorem card_neighborFinset_partition
    (family : CompatibleFamily object) (vertex : object.Vertex) :
    object.degree vertex =
      (family.retainedOldNeighbors vertex).card +
        (family.deletedOldNeighbors vertex).card := by
  classical
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change object.graph.degree vertex =
    (family.retainedOldNeighbors vertex).card +
      (family.deletedOldNeighbors vertex).card
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have partition :
      object.graph.neighborFinset vertex =
        family.retainedOldNeighbors vertex ∪
          family.deletedOldNeighbors vertex := by
    ext other
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union]
    constructor
    · intro adjacent
      by_cases deleted : other ∈ family.deletedVertices
      · exact Or.inr (by
          simp [deletedOldNeighbors, adjacent, deleted])
      · exact Or.inl (by
          simp [retainedOldNeighbors, adjacent, deleted])
    · rintro (retained | deleted)
      · have data := retained
        simp only [retainedOldNeighbors, Finset.mem_sdiff,
          SimpleGraph.mem_neighborFinset] at data
        exact data.1
      · have data := deleted
        simp only [deletedOldNeighbors, Finset.mem_inter,
          SimpleGraph.mem_neighborFinset] at data
        exact data.1
  have disjoint :
      Disjoint (family.retainedOldNeighbors vertex)
        (family.deletedOldNeighbors vertex) := by
    rw [Finset.disjoint_left]
    intro other retained deleted
    have notDeleted : other ∉ family.deletedVertices := by
      have data := retained
      simp only [retainedOldNeighbors, Finset.mem_sdiff,
        SimpleGraph.mem_neighborFinset] at data
      exact data.2
    have isDeleted : other ∈ family.deletedVertices := by
      have data := deleted
      simp only [deletedOldNeighbors, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset] at data
      exact data.2
    exact notDeleted isDeleted
  rw [partition, Finset.card_union_of_disjoint disjoint]

theorem resultingNeighbors_card_add_centerLoad
    (family : CompatibleFamily object)
    (vertex : object.Vertex) :
    (family.resultingNeighbors vertex).card +
        family.centerLoad vertex =
      object.degree vertex := by
  rw [family.card_resultingNeighbors,
    family.card_neighborFinset_partition,
    family.card_deletedOldNeighbors]
  omega

theorem degree_suppressed_eq_resultingNeighbors
    (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    family.suppressed.degree vertex =
      (family.resultingNeighbors (family.toRemaining vertex).1).card := by
  classical
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  change
    (family.suppressed.graph.neighborSet vertex).ncard =
      (family.resultingNeighbors vertex.1).card
  let value : family.suppressed.Vertex → object.Vertex :=
    fun other => (family.toRemaining other).1
  have valueInjective : Function.Injective value := by
    intro left right equality
    apply Subtype.ext
    exact equality
  rw [← (Set.injOn_of_injective valueInjective).ncard_image]
  have setEquality :
      value '' family.suppressed.graph.neighborSet vertex =
        (family.resultingNeighbors
          (family.toRemaining vertex).1 : Set object.Vertex) := by
    ext other
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet,
      Finset.mem_coe, value]
    rw [show
      (other ∈ family.resultingNeighbors
        (family.toRemaining vertex).1) ↔
        other ∈ family.remainingVertices ∧
          (object.graph.Adj (family.toRemaining vertex).1 other ∨
            ∃ i,
              ((family.toRemaining vertex).1 =
                  (family.configuration i).left ∧
                other = (family.configuration i).right) ∨
              ((family.toRemaining vertex).1 =
                  (family.configuration i).right ∧
                other = (family.configuration i).left)) by
      simp [resultingNeighbors]]
    constructor
    · rintro ⟨remaining, adjacent, rfl⟩
      exact ⟨remaining.2,
        (family.suppressed_adj
          (family.toRemaining vertex) remaining).mp adjacent⟩
    · rintro ⟨remaining, adjacent⟩
      exact ⟨⟨other, remaining⟩,
        (family.suppressed_adj (family.toRemaining vertex)
          ⟨other, remaining⟩).mpr adjacent, rfl⟩
  rw [setEquality, Set.ncard_coe_finset]
  simp only [toRemaining_val]

/-- Exact centre-load degree formula.  Shoulder losses are compensated by
their missing chords; the only uncompensated losses are the selected edges at
their common centres. -/
theorem degree_add_centerLoad
    (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    family.suppressed.degree vertex + family.centerLoad vertex.1 =
      object.degree vertex.1 := by
  rw [family.degree_suppressed_eq_resultingNeighbors]
  exact family.resultingNeighbors_card_add_centerLoad
    (family.toRemaining vertex).1

/-- Simultaneous suppression preserves an arbitrary threshold when every
centre has enough literal degree slack for its computed family load. -/
theorem minimumDegree_preserved
    (family : CompatibleFamily object)
    (threshold : Nat)
    (baseline : threshold ≤ object.minDegree)
    (capacity : CenterCapacity family threshold)
    [Nonempty family.suppressed.Vertex] :
    threshold ≤ family.suppressed.minDegree := by
  classical
  apply family.suppressed.le_minDegree_of_forall_le_degree threshold
  intro vertex
  have oldLower :
      threshold ≤ object.degree vertex.1 :=
    baseline.trans (object.minDegree_le_degree vertex.1)
  have loadBound :=
    capacity vertex.1 vertex.2
  have balance :=
    family.degree_add_centerLoad vertex
  omega

/-- The old-edge graph on the surviving vertex type. -/
def retainedGraph (family : CompatibleFamily object) :
    SimpleGraph family.suppressed.Vertex where
  Adj left right :=
    object.graph.Adj
      (family.toRemaining left).1 (family.toRemaining right).1
  symm.symm := by
    intro left right adjacent
    exact adjacent.symm
  loopless.irrefl := by
    intro vertex adjacent
    exact object.graph.loopless.irrefl _ adjacent

def retainedEmbedding (family : CompatibleFamily object) :
    family.retainedGraph →g object.graph where
  toFun := fun vertex => (family.toRemaining vertex).1
  map_rel' := by
    intro left right adjacent
    exact adjacent

theorem retainedEmbedding_injective (family : CompatibleFamily object) :
    Function.Injective family.retainedEmbedding.toFun := by
  intro left right equality
  apply Subtype.ext
  exact equality

private theorem oldAdj_of_cycleEdge_of_not_used
    (family : CompatibleFamily object)
    {start : family.suppressed.Vertex}
    (cycle : family.suppressed.graph.Walk start start)
    (noneUsed : family.usedChords cycle = ∅)
    {left right : family.suppressed.Vertex}
    (adjacent : family.suppressed.graph.Adj left right)
    (onCycle : s(left, right) ∈ cycle.edges) :
    family.retainedGraph.Adj left right := by
  classical
  have classified :=
    (family.suppressed_adj
      (family.toRemaining left) (family.toRemaining right)).mp adjacent
  rcases classified with old | ⟨i, lr | rl⟩
  · exact old
  · have chordEq : family.chord i = s(left, right) := by
      apply Sym2.eq_iff.mpr
      left
      constructor
      · apply Subtype.ext
        exact lr.1.symm
      · apply Subtype.ext
        exact lr.2.symm
    have used : i ∈ family.usedChords cycle := by
      simp [usedChords, chordEq, onCycle]
    rw [noneUsed] at used
    simp at used
  · have chordEq : family.chord i = s(left, right) := by
      apply Sym2.eq_iff.mpr
      right
      constructor
      · apply Subtype.ext
        exact rl.2.symm
      · apply Subtype.ext
        exact rl.1.symm
    have used : i ∈ family.usedChords cycle := by
      simp [usedChords, chordEq, onCycle]
    rw [noneUsed] at used
    simp at used

theorem usedChords_nonempty_of_avoids
    (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate : CycleCertificate family.suppressed LengthOK) :
    (family.usedChords certificate.walk).Nonempty := by
  classical
  by_contra empty
  rw [Finset.not_nonempty_iff_eq_empty] at empty
  have oldEdges :
      ∀ edge, edge ∈ certificate.walk.edges →
        edge ∈ family.retainedGraph.edgeSet := by
    intro edge member
    induction edge using Sym2.inductionOn with
    | _ left right =>
        rw [SimpleGraph.mem_edgeSet]
        exact family.oldAdj_of_cycleEdge_of_not_used
          certificate.walk empty
          (certificate.walk.edges_subset_edgeSet member) member
  let retainedWalk :=
    certificate.walk.transfer family.retainedGraph oldEdges
  have retainedCycle : retainedWalk.IsCycle :=
    certificate.isCycle.transfer oldEdges
  let sourceWalk :=
    retainedWalk.map family.retainedEmbedding
  have sourceCycle : sourceWalk.IsCycle :=
    retainedCycle.map family.retainedEmbedding_injective
  apply avoids
  exact ⟨{
    vertex := family.retainedEmbedding.toFun certificate.vertex
    walk := sourceWalk
    isCycle := sourceCycle
    length_ok := by
      dsimp [sourceWalk, retainedWalk]
      rw [SimpleGraph.Walk.length_map,
        SimpleGraph.Walk.length_transfer]
      exact certificate.length_ok
  }⟩

/-- Expansion of one suppressed edge into either its old source edge or the
two-edge source path through the uniquely selected tight vertex. -/
structure ExpandedEdge (family : CompatibleFamily object)
    (left right : family.suppressed.Vertex) where
  path : object.graph.Walk
    (family.toRemaining left).1 (family.toRemaining right).1
  used : Option family.Index
  used_iff :
    ∀ i, used = some i ↔ family.chord i = s(left, right)
  length_eq : path.length = if used.isSome then 2 else 1
  support_none :
    used = none →
      path.support =
        [(family.toRemaining left).1,
          (family.toRemaining right).1]
  support_some :
    ∀ i, used = some i →
      path.support =
        [(family.toRemaining left).1,
          (family.configuration i).vertex,
          (family.toRemaining right).1]

private theorem chordSuppressed_injective
    (family : CompatibleFamily object) :
    Function.Injective family.chord := by
  intro i j equality
  apply family.chord_injective
  simpa [chord, leftSuppressed, rightSuppressed,
    leftRemaining, rightRemaining] using congrArg
      (Sym2.map fun vertex : family.suppressed.Vertex =>
        (family.toRemaining vertex).1) equality

private theorem exists_expandEdge (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (adjacent : family.suppressed.graph.Adj left right) :
    Nonempty (ExpandedEdge family left right) := by
  classical
  have classified :=
    (family.suppressed_adj
      (family.toRemaining left) (family.toRemaining right)).mp adjacent
  rcases classified with old | ⟨i, lr | rl⟩
  · let path :=
      SimpleGraph.Walk.cons old (SimpleGraph.Walk.nil)
    refine ⟨{
      path := path
      used := none
      used_iff := ?_
      length_eq := by simp [path]
      support_none := by intro; simp [path]
      support_some := by intro i impossible; contradiction
    }⟩
    intro j
    constructor
    · intro impossible
      contradiction
    · intro chordEq
      have added :
          ((family.toRemaining left).1 =
              (family.configuration j).left ∧
            (family.toRemaining right).1 =
              (family.configuration j).right) ∨
          ((family.toRemaining left).1 =
              (family.configuration j).right ∧
            (family.toRemaining right).1 =
              (family.configuration j).left) := by
        rw [chord, Sym2.eq_iff] at chordEq
        rcases chordEq with direct | reverse
        · exact Or.inl
            ⟨(congrArg (fun vertex : family.suppressed.Vertex =>
                (family.toRemaining vertex).1) direct.1).symm,
              (congrArg (fun vertex : family.suppressed.Vertex =>
                (family.toRemaining vertex).1) direct.2).symm⟩
        · exact Or.inr
            ⟨(congrArg (fun vertex : family.suppressed.Vertex =>
                (family.toRemaining vertex).1) reverse.2).symm,
              (congrArg (fun vertex : family.suppressed.Vertex =>
                (family.toRemaining vertex).1) reverse.1).symm⟩
      rcases added with direct | reverse
      · exact False.elim ((family.configuration j).shoulder_missing
          (by
            have source := old
            rw [direct.1, direct.2] at source
            exact source))
      · exact False.elim ((family.configuration j).shoulder_missing
          (by
            have source := old
            rw [reverse.1, reverse.2] at source
            exact source.symm))
  · let shoulderPath :
        object.graph.Walk
          (family.configuration i).left
          (family.configuration i).right :=
      SimpleGraph.Walk.cons
        (family.configuration i).vertex_left.symm
        (SimpleGraph.Walk.cons
          (family.configuration i).vertex_right
          SimpleGraph.Walk.nil)
    let path := shoulderPath.copy lr.1.symm lr.2.symm
    refine ⟨{
      path := path
      used := some i
      used_iff := ?_
      length_eq := by simp [path, shoulderPath]
      support_none := by intro impossible; contradiction
      support_some := by
        intro j equality
        have same : i = j := Option.some.inj equality
        subst j
        simp [path, shoulderPath]
        exact ⟨lr.1.symm, lr.2.symm⟩
    }⟩
    intro j
    constructor
    · intro equality
      have same : i = j := Option.some.inj equality
      subst j
      apply Sym2.eq_iff.mpr
      exact Or.inl ⟨Subtype.ext lr.1.symm, Subtype.ext lr.2.symm⟩
    · intro equality
      have chordI : family.chord i = s(left, right) := by
        apply Sym2.eq_iff.mpr
        exact Or.inl ⟨Subtype.ext lr.1.symm, Subtype.ext lr.2.symm⟩
      exact congrArg some
        (family.chordSuppressed_injective (chordI.trans equality.symm))
  · let shoulderPath :
        object.graph.Walk
          (family.configuration i).right
          (family.configuration i).left :=
      SimpleGraph.Walk.cons
        (family.configuration i).vertex_right.symm
        (SimpleGraph.Walk.cons
          (family.configuration i).vertex_left
          SimpleGraph.Walk.nil)
    let path := shoulderPath.copy rl.1.symm rl.2.symm
    refine ⟨{
      path := path
      used := some i
      used_iff := ?_
      length_eq := by simp [path, shoulderPath]
      support_none := by intro impossible; contradiction
      support_some := by
        intro j equality
        have same : i = j := Option.some.inj equality
        subst j
        simp [path, shoulderPath]
        exact ⟨rl.1.symm, rl.2.symm⟩
    }⟩
    intro j
    constructor
    · intro equality
      have same : i = j := Option.some.inj equality
      subst j
      apply Sym2.eq_iff.mpr
      exact Or.inr ⟨Subtype.ext rl.2.symm, Subtype.ext rl.1.symm⟩
    · intro equality
      have chordI : family.chord i = s(left, right) := by
        apply Sym2.eq_iff.mpr
        exact Or.inr ⟨Subtype.ext rl.2.symm, Subtype.ext rl.1.symm⟩
      exact congrArg some
        (family.chordSuppressed_injective (chordI.trans equality.symm))

noncomputable def expandEdge (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (adjacent : family.suppressed.graph.Adj left right) :
    ExpandedEdge family left right :=
  Classical.choice (family.exists_expandEdge adjacent)

noncomputable def expandWalk (family : CompatibleFamily object) :
    {left right : family.suppressed.Vertex} →
      family.suppressed.graph.Walk left right →
      object.graph.Walk
        (family.toRemaining left).1 (family.toRemaining right).1
  | _, _, .nil => .nil
  | _, _, .cons adjacent tail =>
      (family.expandEdge adjacent).path.append
        (family.expandWalk tail)

noncomputable def usedSequence (family : CompatibleFamily object) :
    {left right : family.suppressed.Vertex} →
      family.suppressed.graph.Walk left right → List family.Index
  | _, _, .nil => []
  | _, _, .cons adjacent tail =>
      (family.expandEdge adjacent).used.toList ++
        family.usedSequence tail

@[simp]
theorem expandWalk_nil (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    family.expandWalk
      (SimpleGraph.Walk.nil :
        family.suppressed.graph.Walk vertex vertex) =
      (SimpleGraph.Walk.nil :
        object.graph.Walk
          (family.toRemaining vertex).1
          (family.toRemaining vertex).1) :=
  rfl

@[simp]
theorem expandWalk_cons (family : CompatibleFamily object)
    {left middle right : family.suppressed.Vertex}
    (adjacent : family.suppressed.graph.Adj left middle)
    (tail : family.suppressed.graph.Walk middle right) :
    family.expandWalk (SimpleGraph.Walk.cons adjacent tail) =
      (family.expandEdge adjacent).path.append
        (family.expandWalk tail) :=
  rfl

@[simp]
theorem usedSequence_nil (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    family.usedSequence
      (SimpleGraph.Walk.nil :
        family.suppressed.graph.Walk vertex vertex) = [] :=
  rfl

@[simp]
theorem usedSequence_cons (family : CompatibleFamily object)
    {left middle right : family.suppressed.Vertex}
    (adjacent : family.suppressed.graph.Adj left middle)
    (tail : family.suppressed.graph.Walk middle right) :
    family.usedSequence (SimpleGraph.Walk.cons adjacent tail) =
      (family.expandEdge adjacent).used.toList ++
        family.usedSequence tail :=
  rfl

theorem length_expandWalk (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (walk : family.suppressed.graph.Walk left right) :
    (family.expandWalk walk).length =
      walk.length + (family.usedSequence walk).length := by
  induction walk with
  | nil => simp
  | @cons left middle right adjacent tail ih =>
      rw [family.expandWalk_cons, SimpleGraph.Walk.length_append,
        family.usedSequence_cons, List.length_append, ih,
        (family.expandEdge adjacent).length_eq]
      cases used : (family.expandEdge adjacent).used <;>
        simp
      all_goals omega

theorem mem_usedSequence_iff (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (walk : family.suppressed.graph.Walk left right)
    (i : family.Index) :
    i ∈ family.usedSequence walk ↔ family.chord i ∈ walk.edges := by
  induction walk with
  | nil => simp
  | @cons left middle right adjacent tail ih =>
      rw [family.usedSequence_cons, List.mem_append, ih,
        SimpleGraph.Walk.edges_cons, List.mem_cons]
      have edgeIff :=
        (family.expandEdge adjacent).used_iff i
      have optionIff :
          i ∈ (family.expandEdge adjacent).used.toList ↔
            (family.expandEdge adjacent).used = some i := by
        cases (family.expandEdge adjacent).used <;> simp [eq_comm]
      exact or_congr (optionIff.trans edgeIff) Iff.rfl

theorem usedSequence_nodup_of_edges_nodup
    (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (walk : family.suppressed.graph.Walk left right)
    (edgesNodup : walk.edges.Nodup) :
    (family.usedSequence walk).Nodup := by
  induction walk with
  | nil => simp
  | @cons left middle right adjacent tail ih =>
      rw [family.usedSequence_cons]
      rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at edgesNodup
      have tailNodup := ih edgesNodup.2
      cases used : (family.expandEdge adjacent).used with
      | none =>
          simpa [used] using tailNodup
      | some i =>
          simp only [Option.toList_some, List.singleton_append,
            List.nodup_cons]
          refine ⟨?_, tailNodup⟩
          intro member
          have chordInTail :
              family.chord i ∈ tail.edges :=
            (family.mem_usedSequence_iff tail i).mp member
          have chordHead :
              family.chord i = s(left, middle) :=
            ((family.expandEdge adjacent).used_iff i).mp used
          exact edgesNodup.1 (chordHead ▸ chordInTail)

theorem usedSequence_toFinset (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (walk : family.suppressed.graph.Walk left right) :
    (family.usedSequence walk).toFinset = family.usedChords walk := by
  classical
  ext i
  simp [family.mem_usedSequence_iff, usedChords]

theorem usedSequence_length_eq_usedChords_card
    (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (walk : family.suppressed.graph.Walk left right)
    (isTrail : walk.IsTrail) :
    (family.usedSequence walk).length =
      (family.usedChords walk).card := by
  rw [← family.usedSequence_toFinset walk]
  exact (List.toFinset_card_of_nodup
    (family.usedSequence_nodup_of_edges_nodup walk
      isTrail.edges_nodup)).symm

def sourceVertex (family : CompatibleFamily object) :
    family.suppressed.Vertex → object.Vertex :=
  fun vertex => (family.toRemaining vertex).1

theorem sourceVertex_injective (family : CompatibleFamily object) :
    Function.Injective family.sourceVertex := by
  intro left right equality
  apply Subtype.ext
  exact equality

theorem expandWalk_tail_support_multiset
    (family : CompatibleFamily object)
    {left right : family.suppressed.Vertex}
    (walk : family.suppressed.graph.Walk left right) :
    ((family.expandWalk walk).support.tail :
        Multiset object.Vertex) =
      (walk.support.tail.map family.sourceVertex :
        Multiset object.Vertex) +
      (family.usedSequence walk).map
        (fun i => (family.configuration i).vertex) := by
  induction walk with
  | nil => simp
  | @cons left middle right adjacent tail ih =>
      rw [family.expandWalk_cons,
        SimpleGraph.Walk.tail_support_append,
        family.usedSequence_cons]
      rw [← Multiset.coe_add, ih, List.map_append,
        ← Multiset.coe_add]
      cases used : (family.expandEdge adjacent).used with
      | none =>
          have supportEq :=
            (family.expandEdge adjacent).support_none used
          rw [supportEq]
          have mappedSupport :
              tail.support.map family.sourceVertex =
                family.sourceVertex middle ::
                  tail.support.tail.map family.sourceVertex := by
            rw [show tail.support =
                middle :: tail.support.tail from
                  tail.cons_tail_support.symm]
            rfl
          simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
          rw [mappedSupport]
          simp [sourceVertex]
      | some i =>
          have supportEq :=
            (family.expandEdge adjacent).support_some i used
          rw [supportEq]
          have mappedSupport :
              tail.support.map family.sourceVertex =
                family.sourceVertex middle ::
                  tail.support.tail.map family.sourceVertex := by
            rw [show tail.support =
                middle :: tail.support.tail from
                  tail.cons_tail_support.symm]
            rfl
          simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
          rw [mappedSupport]
          simpa [sourceVertex, List.append_assoc] using
            (List.perm_middle
              (a := (family.configuration i).vertex)
              (l₁ := family.sourceVertex middle ::
                tail.support.tail.map family.sourceVertex)
              (l₂ := (family.usedSequence tail).map
                (fun j => (family.configuration j).vertex))).symm

theorem expandWalk_tail_support_nodup
    (family : CompatibleFamily object)
    {start : family.suppressed.Vertex}
    (cycle : family.suppressed.graph.Walk start start)
    (isCycle : cycle.IsCycle) :
    (family.expandWalk cycle).support.tail.Nodup := by
  classical
  let surviving :=
    cycle.support.tail.map family.sourceVertex
  let inserted :=
    (family.usedSequence cycle).map
      (fun i => (family.configuration i).vertex)
  have survivingNodup : surviving.Nodup := by
    exact isCycle.support_nodup.map family.sourceVertex_injective
  have insertedNodup : inserted.Nodup := by
    exact (family.usedSequence_nodup_of_edges_nodup cycle
      isCycle.isTrail.edges_nodup).map family.vertex_injective
  have separated : surviving.Disjoint inserted := by
    rw [List.disjoint_left]
    intro vertex inSurviving inInserted
    simp only [surviving, List.mem_map] at inSurviving
    simp only [inserted, List.mem_map] at inInserted
    obtain ⟨remaining, _, rfl⟩ := inSurviving
    obtain ⟨i, _, equality⟩ := inInserted
    have notDeleted :
        family.sourceVertex remaining ∉ family.deletedVertices := by
      have property := (family.toRemaining remaining).2
      change family.sourceVertex remaining ∈
        object.vertexFinset \ family.deletedVertices at property
      exact (Finset.mem_sdiff.mp property).2
    apply notDeleted
    simp only [deletedVertices, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨i, equality⟩
  have combinedNodup : (surviving ++ inserted).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨survivingNodup, insertedNodup, ?_⟩
    intro left leftMem right rightMem equality
    exact separated leftMem (equality ▸ rightMem)
  have multisetEquality :=
    family.expandWalk_tail_support_multiset cycle
  have permutation : List.Perm
      (family.expandWalk cycle).support.tail
      (surviving ++ inserted) := by
    apply Multiset.coe_eq_coe.mp
    simpa [surviving, inserted, ← Multiset.coe_add] using
      multisetEquality
  exact permutation.nodup_iff.mpr combinedNodup

theorem expandWalk_isCycle
    (family : CompatibleFamily object)
    {start : family.suppressed.Vertex}
    (cycle : family.suppressed.graph.Walk start start)
    (isCycle : cycle.IsCycle) :
    (family.expandWalk cycle).IsCycle := by
  classical
  let expanded := family.expandWalk cycle
  have expandedLength :
      cycle.length ≤ expanded.length := by
    have exactLength :
        expanded.length =
          cycle.length + (family.usedSequence cycle).length :=
      family.length_expandWalk cycle
    omega
  have expandedNotNil : ¬ expanded.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact lt_of_lt_of_le (by
      have := isCycle.three_le_length
      omega) expandedLength
  have tailPath : expanded.tail.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [expanded.support_tail_of_not_nil expandedNotNil]
    exact family.expandWalk_tail_support_nodup cycle isCycle
  have firstEdgeAvoided :
      s(family.sourceVertex start, expanded.snd) ∉
        expanded.tail.edges := by
    intro member
    have swapped :
        s(expanded.snd, family.sourceVertex start) ∈
          expanded.tail.edges := by
      rwa [Sym2.eq_swap] at member
    have one := tailPath.length_eq_one_of_mem_edges swapped
    have tailDrop := expanded.length_tail_add_one expandedNotNil
    have lower := isCycle.three_le_length
    omega
  have rebuilt :
      SimpleGraph.Walk.cons (expanded.adj_snd expandedNotNil)
        expanded.tail = expanded :=
    expanded.cons_tail_eq expandedNotNil
  change expanded.IsCycle
  rw [← rebuilt]
  exact (SimpleGraph.Walk.cons_isCycle_iff
    expanded.tail (expanded.adj_snd expandedNotNil)).mpr
      ⟨tailPath, firstEdgeAvoided⟩

/-- The source cycle obtained by simultaneously replacing every used
shoulder chord. -/
structure ExpandedCycle (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (certificate : CycleCertificate family.suppressed LengthOK) where
  walk : object.graph.Walk
    (family.sourceVertex certificate.vertex)
    (family.sourceVertex certificate.vertex)
  isCycle : walk.IsCycle
  length_eq :
    walk.length =
      certificate.walk.length +
        (family.usedChords certificate.walk).card

noncomputable def expandCycle (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (certificate : CycleCertificate family.suppressed LengthOK) :
    ExpandedCycle family certificate := by
  let walk := family.expandWalk certificate.walk
  refine {
    walk := walk
    isCycle := family.expandWalk_isCycle
      certificate.walk certificate.isCycle
    length_eq := ?_
  }
  dsimp [walk]
  calc
    (family.expandWalk certificate.walk).length =
        certificate.walk.length +
          (family.usedSequence certificate.walk).length :=
      family.length_expandWalk certificate.walk
    _ = certificate.walk.length +
          (family.usedChords certificate.walk).card := by
      rw [family.usedSequence_length_eq_usedChords_card
        certificate.walk certificate.isCycle.isTrail]

/-- Complete suppressed-family conclusion: avoidance forces a nonempty used
chord set, and simultaneous expansion gives a simple source cycle with one
extra edge per used chord. -/
theorem suppressedFamilyExpansion
    (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate : CycleCertificate family.suppressed LengthOK) :
    (family.usedChords certificate.walk).Nonempty ∧
      ∃ expanded : ExpandedCycle family certificate,
        expanded.walk.length =
          certificate.walk.length +
            (family.usedChords certificate.walk).card := by
  exact ⟨family.usedChords_nonempty_of_avoids avoids certificate,
    ⟨family.expandCycle certificate,
      (family.expandCycle certificate).length_eq⟩⟩

end

end CompatibleFamily

end TightVertexSuppression

end Hypostructure.Graph
