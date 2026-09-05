import Hypostructure.Graph.BoundaryOverlap
import Hypostructure.Graph.HighCentreNormalForm
import Hypostructure.Graph.TightVertexSuppression

/-!
# An internal-vertex fold of a boundaried graph

This is the graph operation used by the visible-entry Q1 producer.  Two
distinct *internal* vertices of one existing boundary piece are identified;
the labelled boundary and every outside context are left literally unchanged.
The operation is defined on the incoming piece, rather than supplied as a
replacement by a caller.
-/

namespace Hypostructure.Graph

open scoped Sym2

universe u

namespace FiniteObject

variable {object : FiniteObject.{u}}

/-- A common neighbour of the two vertices that are to be folded. -/
def IsCommonNeighbor (left right common : object.Vertex) : Prop :=
  object.graph.Adj left common ∧ object.graph.Adj right common

/-- Four named vertices, with all pairwise inequalities exposed. -/
structure DistinctFour (first second third fourth : object.Vertex) : Prop where
  first_second : first ≠ second
  first_third : first ≠ third
  first_fourth : first ≠ fourth
  second_third : second ≠ third
  second_fourth : second ≠ fourth
  third_fourth : third ≠ fourth

/-- Membership in the literal four-vertex origin set. -/
def IsOneOfFour (first second third fourth vertex : object.Vertex) : Prop :=
  vertex = first ∨ vertex = second ∨ vertex = third ∨ vertex = fourth

/-- The exact local plan for an internal two-origin fold.  In the first arm no
vertex loses an incidence.  In the second arm `common` is the sole possible
incidence loss and `repair` is a surviving full origin to which the missing
edge may be added. -/
structure FoldPlan (first second third fourth : object.Vertex) where
  keep : object.Vertex
  remove : object.Vertex
  keep_origin : IsOneOfFour first second third fourth keep
  remove_origin : IsOneOfFour first second third fourth remove
  different : keep ≠ remove
  repair :
    (∀ common, ¬ object.IsCommonNeighbor keep remove common) ∨
      ∃ common repair,
        object.IsCommonNeighbor keep remove common ∧
          IsOneOfFour first second third fourth repair ∧
          repair ≠ keep ∧ repair ≠ remove ∧ repair ≠ common ∧
          ¬ object.graph.Adj common repair

/-- In a graph without an accepted quadrilateral, two distinct vertices have
at most one common neighbour. -/
theorem commonNeighbor_unique {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (four : LengthOK 4) {left right x y : object.Vertex}
    (different : left ≠ right)
    (xCommon : object.IsCommonNeighbor left right x)
    (yCommon : object.IsCommonNeighbor left right y) : x = y := by
  by_contra xNeY
  exact not_quadrilateral avoids four xCommon.1 xCommon.2.symm
    yCommon.2 yCommon.1.symm different xNeY

/-- Three distinct displayed neighbours exhaust a cubic vertex. -/
theorem neighbor_eq_of_degree_three
    {centre first second third other : object.Vertex}
    (degreeThree : object.degree centre = 3)
    (firstAdj : object.graph.Adj centre first)
    (secondAdj : object.graph.Adj centre second)
    (thirdAdj : object.graph.Adj centre third)
    (firstSecond : first ≠ second) (firstThird : first ≠ third)
    (secondThird : second ≠ third)
    (otherAdj : object.graph.Adj centre other) :
  other = first ∨ other = second ∨ other = third := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let neighbours := object.graph.neighborFinset centre
  have displayedSubset : ({first, second, third} : Finset object.Vertex) ⊆
      neighbours := by
    intro vertex member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with equality | equality | equality
    · subst vertex
      change first ∈ object.graph.neighborFinset centre
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 firstAdj
    · subst vertex
      change second ∈ object.graph.neighborFinset centre
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 secondAdj
    · subst vertex
      change third ∈ object.graph.neighborFinset centre
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 thirdAdj
  have displayedCard : ({first, second, third} : Finset object.Vertex).card = 3 := by
    simp [firstSecond, firstThird, secondThird]
  have neighbourCard : neighbours.card = 3 := by
    simpa [neighbours, FiniteObject.degree,
      SimpleGraph.card_neighborFinset_eq_degree] using degreeThree
  have equal : ({first, second, third} : Finset object.Vertex) = neighbours :=
    Finset.eq_of_subset_of_card_le displayedSubset (by omega)
  have otherMember : other ∈ ({first, second, third} : Finset object.Vertex) := by
    rw [equal]
    change other ∈ object.graph.neighborFinset centre
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 otherAdj
  simpa only [Finset.mem_insert, Finset.mem_singleton] using otherMember

/-- The four cubic origins always contain a foldable pair.  This is the exact
finite C4-free exhaustion used by the visible-entry producer. -/
theorem exists_foldPlan_of_distinctFour_of_cubic
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (fourAccepted : LengthOK 4)
    {first second third fourth : object.Vertex}
    (distinct : DistinctFour first second third fourth)
    (neighbourCubic : ∀ origin,
      IsOneOfFour first second third fourth origin →
      ∀ neighbour, object.graph.Adj origin neighbour →
        object.degree neighbour = 3) :
    Nonempty (FoldPlan (object := object) first second third fourth) := by
  classical
  let common := fun left right vertex =>
    object.IsCommonNeighbor left right vertex
  by_cases firstSecondCommon : ∃ x, common first second x
  · obtain ⟨x, xCommon⟩ := firstSecondCommon
    by_cases xEqThird : x = third
    · subst x
      by_cases thirdFourth : object.graph.Adj third fourth
      · -- The selected-star corner: switch to the adjacent pair `(third,first)`.
        by_cases switchedCommon : ∃ y, common third first y
        · obtain ⟨y, yCommon⟩ := switchedCommon
          have thirdCubic : object.degree third = 3 :=
            neighbourCubic first (Or.inl rfl) third xCommon.1
          have yCases : y = first ∨ y = second ∨ y = fourth :=
            object.neighbor_eq_of_degree_three thirdCubic xCommon.1.symm
              xCommon.2.symm thirdFourth
              distinct.first_second distinct.first_fourth
              distinct.second_fourth yCommon.1
          rcases yCases with yEq | yEq | yEq
          · subst y
            exact (object.graph.loopless.irrefl _ yCommon.2).elim
          · subst y
            have fourthNotAdjacent : ¬ object.graph.Adj second fourth := by
              intro edge
              exact not_quadrilateral avoids fourAccepted
                yCommon.2 edge thirdFourth.symm xCommon.1.symm
                distinct.first_fourth distinct.second_third
            exact ⟨{
              keep := third
              remove := first
              keep_origin := Or.inr (Or.inr (Or.inl rfl))
              remove_origin := Or.inl rfl
              different := distinct.first_third.symm
              repair := Or.inr ⟨second, fourth, yCommon,
                Or.inr (Or.inr (Or.inr rfl)), distinct.third_fourth.symm,
                distinct.first_fourth.symm, distinct.second_fourth.symm,
                fourthNotAdjacent⟩ }⟩
          · subst y
            have secondNotAdjacent : ¬ object.graph.Adj fourth second := by
              intro edge
              exact not_quadrilateral avoids fourAccepted
                yCommon.2 edge xCommon.2 xCommon.1.symm
                distinct.first_second distinct.third_fourth.symm
            exact ⟨{
              keep := third
              remove := first
              keep_origin := Or.inr (Or.inr (Or.inl rfl))
              remove_origin := Or.inl rfl
              different := distinct.first_third.symm
              repair := Or.inr ⟨fourth, second, yCommon,
                Or.inr (Or.inl rfl), distinct.second_third,
                distinct.first_second.symm, distinct.second_fourth,
                secondNotAdjacent⟩ }⟩
        · exact ⟨{
            keep := third
            remove := first
            keep_origin := Or.inr (Or.inr (Or.inl rfl))
            remove_origin := Or.inl rfl
            different := distinct.first_third.symm
            repair := Or.inl (not_exists.1 switchedCommon) }⟩
      · exact ⟨{
          keep := first
          remove := second
          keep_origin := Or.inl rfl
          remove_origin := Or.inr (Or.inl rfl)
          different := distinct.first_second
          repair := Or.inr ⟨third, fourth, xCommon,
            Or.inr (Or.inr (Or.inr rfl)), distinct.first_fourth.symm,
            distinct.second_fourth.symm, distinct.third_fourth.symm,
            thirdFourth⟩ }⟩
    · by_cases xEqFourth : x = fourth
      · subst x
        by_cases fourthThird : object.graph.Adj fourth third
        · -- Symmetric selected-star corner.
          by_cases switchedCommon : ∃ y, common fourth first y
          · obtain ⟨y, yCommon⟩ := switchedCommon
            have fourthCubic : object.degree fourth = 3 :=
              neighbourCubic first (Or.inl rfl) fourth xCommon.1
            have yCases : y = first ∨ y = second ∨ y = third :=
              object.neighbor_eq_of_degree_three fourthCubic xCommon.1.symm
                xCommon.2.symm fourthThird distinct.first_second distinct.first_third
                distinct.second_third yCommon.1
            rcases yCases with yEq | yEq | yEq
            · subst y
              exact (object.graph.loopless.irrefl _ yCommon.2).elim
            · subst y
              have thirdNotAdjacent : ¬ object.graph.Adj second third := by
                intro edge
                exact not_quadrilateral avoids fourAccepted
                  yCommon.2 edge fourthThird.symm xCommon.1.symm
                  distinct.first_third distinct.second_fourth
              exact ⟨{
                keep := fourth
                remove := first
                keep_origin := Or.inr (Or.inr (Or.inr rfl))
                remove_origin := Or.inl rfl
                different := distinct.first_fourth.symm
                repair := Or.inr ⟨second, third, yCommon,
                  Or.inr (Or.inr (Or.inl rfl)), distinct.third_fourth,
                  distinct.first_third.symm, distinct.second_third.symm,
                  thirdNotAdjacent⟩ }⟩
            · subst y
              have secondNotAdjacent : ¬ object.graph.Adj third second := by
                intro edge
                exact not_quadrilateral avoids fourAccepted
                  yCommon.2 edge xCommon.2 xCommon.1.symm
                  distinct.first_second distinct.third_fourth
              exact ⟨{
                keep := fourth
                remove := first
                keep_origin := Or.inr (Or.inr (Or.inr rfl))
                remove_origin := Or.inl rfl
                different := distinct.first_fourth.symm
                repair := Or.inr ⟨third, second, yCommon,
                  Or.inr (Or.inl rfl), distinct.second_fourth,
                  distinct.first_second.symm, distinct.second_third,
                  secondNotAdjacent⟩ }⟩
          · exact ⟨{
              keep := fourth
              remove := first
              keep_origin := Or.inr (Or.inr (Or.inr rfl))
              remove_origin := Or.inl rfl
              different := distinct.first_fourth.symm
              repair := Or.inl (not_exists.1 switchedCommon) }⟩
        · exact ⟨{
            keep := first
            remove := second
            keep_origin := Or.inl rfl
            remove_origin := Or.inr (Or.inl rfl)
            different := distinct.first_second
            repair := Or.inr ⟨fourth, third, xCommon,
              Or.inr (Or.inr (Or.inl rfl)), distinct.first_third.symm,
              distinct.second_third.symm, distinct.third_fourth,
              fourthThird⟩ }⟩
      · have xCubic : object.degree x = 3 :=
          neighbourCubic first (Or.inl rfl) x xCommon.1
        by_cases xThird : object.graph.Adj x third
        · have xFourth : ¬ object.graph.Adj x fourth := by
            intro adjacent
            have cases := object.neighbor_eq_of_degree_three xCubic
              xCommon.1.symm xCommon.2.symm xThird
              distinct.first_second distinct.first_third distinct.second_third
              adjacent
            rcases cases with equality | equality | equality
            · exact distinct.first_fourth equality.symm
            · exact distinct.second_fourth equality.symm
            · exact distinct.third_fourth equality.symm
          exact ⟨{
            keep := first
            remove := second
            keep_origin := Or.inl rfl
            remove_origin := Or.inr (Or.inl rfl)
            different := distinct.first_second
            repair := Or.inr ⟨x, fourth, xCommon,
              Or.inr (Or.inr (Or.inr rfl)), distinct.first_fourth.symm,
              distinct.second_fourth.symm, Ne.symm xEqFourth, xFourth⟩ }⟩
        · exact ⟨{
            keep := first
            remove := second
            keep_origin := Or.inl rfl
            remove_origin := Or.inr (Or.inl rfl)
            different := distinct.first_second
            repair := Or.inr ⟨x, third, xCommon,
              Or.inr (Or.inr (Or.inl rfl)), distinct.first_third.symm,
            distinct.second_third.symm, Ne.symm xEqThird, xThird⟩ }⟩
  · exact ⟨{
      keep := first
      remove := second
      keep_origin := Or.inl rfl
      remove_origin := Or.inr (Or.inl rfl)
      different := distinct.first_second
      repair := Or.inl (not_exists.1 firstSecondCommon) }⟩

end FiniteObject

namespace BoundaryPiece

variable {boundary : Boundary.{u}}

/-- The internal carrier after `remove` has been identified with another
internal vertex. -/
abbrev InternalExcept (piece : BoundaryPiece boundary)
    (remove : piece.Internal) := {vertex : piece.Internal // vertex ≠ remove}

/-- Decode the folded carrier into the source carrier. -/
def foldDecode (piece : BoundaryPiece boundary) (remove : piece.Internal) :
    boundary.Vertex ⊕ piece.InternalExcept remove →
      boundary.Vertex ⊕ piece.Internal
  | .inl vertex => .inl vertex
  | .inr vertex => .inr vertex.1

/-- Identify `remove` with `keep`, discarding loops and duplicate incidences
through `SimpleGraph.fromRel`.  No boundary vertex is removed or renamed. -/
noncomputable abbrev identifyInternal (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    BoundaryPiece boundary where
  Internal := piece.InternalExcept remove
  internalVertices := by
    letI : FinEnum piece.Internal := piece.internalVertices
    infer_instance
  graph := SimpleGraph.fromRel fun left right =>
    piece.graph.Adj (piece.foldDecode remove left) (piece.foldDecode remove right) ∨
      (piece.foldDecode remove left = .inr keep ∧
        piece.graph.Adj (.inr remove) (piece.foldDecode remove right))
  decideAdj := by
    letI : DecidableEq piece.Internal := piece.internalVertices.decEq
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    letI : DecidableRel piece.graph.Adj := piece.decideAdj
    infer_instance

/-- The surviving image of `keep`. -/
def foldedKeep (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    boundary.Vertex ⊕ (piece.identifyInternal keep remove different).Internal :=
  .inr ⟨keep, different⟩

/-- A source carrier vertex other than the removed internal vertex has a
canonical representative after the fold. -/
def foldRetain (piece : BoundaryPiece boundary) (remove : piece.Internal)
    (vertex : boundary.Vertex ⊕ piece.Internal)
    (survives : vertex ≠ .inr remove) :
    boundary.Vertex ⊕ piece.InternalExcept remove := by
  cases vertex with
  | inl boundaryVertex => exact .inl boundaryVertex
  | inr internal =>
      exact .inr ⟨internal, fun equality => survives (congrArg Sum.inr equality)⟩

@[simp] theorem foldDecode_foldedKeep (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    piece.foldDecode remove (piece.foldedKeep keep remove different) = .inr keep :=
  rfl

@[simp] theorem foldDecode_foldRetain (piece : BoundaryPiece boundary)
    (remove : piece.Internal) (vertex : boundary.Vertex ⊕ piece.Internal)
    (survives : vertex ≠ .inr remove) :
    piece.foldDecode remove (piece.foldRetain remove vertex survives) = vertex := by
  cases vertex <;> simp [foldRetain, foldDecode]

@[simp] theorem identifyInternal_adj (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (left right : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal) :
    (piece.identifyInternal keep remove different).graph.Adj left right ↔
      left ≠ right ∧
        (piece.graph.Adj (piece.foldDecode remove left)
            (piece.foldDecode remove right) ∨
          (piece.foldDecode remove left = .inr keep ∧
            piece.graph.Adj (.inr remove) (piece.foldDecode remove right)) ∨
          (piece.foldDecode remove right = .inr keep ∧
            piece.graph.Adj (.inr remove) (piece.foldDecode remove left))) := by
  change (SimpleGraph.fromRel _).Adj left right ↔ _
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨ne, (old | moved) | (old | moved)⟩
    · exact ⟨ne, Or.inl old⟩
    · exact ⟨ne, Or.inr (Or.inl moved)⟩
    · exact ⟨ne, Or.inl old.symm⟩
    · exact ⟨ne, Or.inr (Or.inr moved)⟩
  · rintro ⟨ne, old | moved | moved⟩
    · exact ⟨ne, Or.inl (Or.inl old)⟩
    · exact ⟨ne, Or.inl (Or.inr moved)⟩
    · exact ⟨ne, Or.inr (Or.inr moved)⟩

/-- Decoding the surviving folded carrier is injective. -/
theorem foldDecode_injective (piece : BoundaryPiece boundary)
    (remove : piece.Internal) : Function.Injective (piece.foldDecode remove) := by
  intro left right equality
  cases left with
  | inl leftBoundary =>
      cases right with
      | inl rightBoundary => exact congrArg Sum.inl (Sum.inl.inj equality)
      | inr rightInternal =>
          change Sum.inl leftBoundary = Sum.inr rightInternal.1 at equality
          exact (Sum.inl_ne_inr equality).elim
  | inr leftInternal =>
      cases right with
      | inl rightBoundary =>
          change Sum.inr leftInternal.1 = Sum.inl rightBoundary at equality
          exact (Sum.inr_ne_inl equality).elim
      | inr rightInternal =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact Sum.inr.inj equality

/-- No folded carrier decodes to the removed source vertex. -/
theorem foldDecode_ne_remove (piece : BoundaryPiece boundary)
    (remove : piece.Internal)
    (vertex : boundary.Vertex ⊕ piece.InternalExcept remove) :
    piece.foldDecode remove vertex ≠ .inr remove := by
  cases vertex with
  | inl boundaryVertex => exact Sum.inl_ne_inr
  | inr internal =>
      intro equality
      exact internal.2 (Sum.inr.inj equality)

/-- The image of the folded vertex's neighbourhood is the union of the two
source neighbourhoods, with the two identified endpoints removed. -/
theorem image_neighborSet_foldedKeep (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    piece.foldDecode remove ''
        ((piece.identifyInternal keep remove different).graph.neighborSet
          (piece.foldedKeep keep remove different)) =
      (piece.graph.neighborSet (.inr keep) \ {.inr remove}) ∪
        (piece.graph.neighborSet (.inr remove) \ {.inr keep}) := by
  classical
  ext other
  constructor
  · rintro ⟨candidate, adjacent, rfl⟩
    rw [SimpleGraph.mem_neighborSet] at adjacent
    rw [piece.identifyInternal_adj keep remove different] at adjacent
    obtain ⟨ne, old | moved | reversed⟩ := adjacent
    · exact Or.inl ⟨by simpa using old, piece.foldDecode_ne_remove remove candidate⟩
    · exact Or.inr ⟨moved.2, fun equality =>
        have decoded : piece.foldDecode remove candidate =
            (.inr keep : boundary.Vertex ⊕ piece.Internal) := by
          simpa using equality
        ne (piece.foldDecode_injective remove (by
          simpa using decoded.symm))⟩
    · exact (ne (piece.foldDecode_injective remove (by
        simpa [reversed.1]))).elim
  · intro member
    have notRemove : other ≠ (.inr remove : boundary.Vertex ⊕ piece.Internal) := by
      rcases member with ⟨_, notRemove⟩ | ⟨adjacent, _⟩
      · exact notRemove
      · rw [SimpleGraph.mem_neighborSet] at adjacent
        exact fun equality => (equality ▸ adjacent).ne rfl
    let retained := piece.foldRetain remove other notRemove
    refine ⟨retained, ?_, piece.foldDecode_foldRetain remove other notRemove⟩
    rw [SimpleGraph.mem_neighborSet]
    rw [piece.identifyInternal_adj keep remove different]
    refine ⟨?_, ?_⟩
    · intro equality
      have decoded : other = (.inr keep : boundary.Vertex ⊕ piece.Internal) := by
        have := congrArg (piece.foldDecode remove) equality
        simpa [retained] using this.symm
      rcases member with ⟨adjacent, _⟩ | ⟨adjacent, notKeep⟩
      all_goals rw [SimpleGraph.mem_neighborSet] at adjacent
      · exact adjacent.ne decoded.symm
      · exact notKeep (by simpa using decoded)
    · rcases member with ⟨adjacent, _⟩ | ⟨adjacent, _⟩
      all_goals rw [SimpleGraph.mem_neighborSet] at adjacent
      · exact Or.inl (by simpa [retained] using adjacent)
      · exact Or.inr (Or.inl ⟨by simp [retained], by simpa [retained] using adjacent⟩)

/-- Away from the folded vertex, a vertex not adjacent to the removed origin
keeps exactly its source neighbourhood. -/
theorem image_neighborSet_of_not_adj_remove (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (vertex : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal)
    (notKeep : vertex ≠ piece.foldedKeep keep remove different)
    (notFromRemove :
      ¬ piece.graph.Adj (.inr remove) (piece.foldDecode remove vertex)) :
    piece.foldDecode remove ''
        ((piece.identifyInternal keep remove different).graph.neighborSet vertex) =
      piece.graph.neighborSet (piece.foldDecode remove vertex) := by
  classical
  ext other
  constructor
  · rintro ⟨candidate, adjacent, rfl⟩
    rw [SimpleGraph.mem_neighborSet] at adjacent
    rw [piece.identifyInternal_adj keep remove different] at adjacent
    rcases adjacent with ⟨_, old | moved | moved⟩
    · exact (SimpleGraph.mem_neighborSet _ _ _).2 old
    · exact (notKeep (piece.foldDecode_injective remove
        (moved.1.trans (piece.foldDecode_foldedKeep keep remove different).symm))).elim
    · exact (notFromRemove moved.2).elim
  · intro adjacent
    rw [SimpleGraph.mem_neighborSet] at adjacent
    have notRemove : other ≠ (.inr remove : boundary.Vertex ⊕ piece.Internal) := by
      rintro rfl
      exact notFromRemove adjacent.symm
    let retained := piece.foldRetain remove other notRemove
    refine ⟨retained, ?_, piece.foldDecode_foldRetain remove other notRemove⟩
    rw [SimpleGraph.mem_neighborSet]
    rw [piece.identifyInternal_adj keep remove different]
    refine ⟨?_, Or.inl (by simpa [retained] using adjacent)⟩
    intro equality
    have decoded := congrArg (piece.foldDecode remove) equality
    have same : piece.foldDecode remove vertex = other := by
      simpa [retained] using decoded
    exact adjacent.ne same

/-- Away from the folded vertex, a source neighbour of the removed origin is
replaced by the surviving folded vertex. -/
theorem image_neighborSet_of_adj_remove (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (vertex : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal)
    (notKeep : vertex ≠ piece.foldedKeep keep remove different)
    (fromRemove :
      piece.graph.Adj (.inr remove) (piece.foldDecode remove vertex)) :
    piece.foldDecode remove ''
        ((piece.identifyInternal keep remove different).graph.neighborSet vertex) =
      insert (.inr keep)
        (piece.graph.neighborSet (piece.foldDecode remove vertex) \ {.inr remove}) := by
  classical
  ext other
  constructor
  · rintro ⟨candidate, adjacent, rfl⟩
    rw [SimpleGraph.mem_neighborSet] at adjacent
    rw [piece.identifyInternal_adj keep remove different] at adjacent
    rcases adjacent with ⟨_, old | moved | moved⟩
    · exact Set.mem_insert_of_mem _
        ⟨(SimpleGraph.mem_neighborSet _ _ _).2 old,
          piece.foldDecode_ne_remove remove candidate⟩
    · exact (notKeep (piece.foldDecode_injective remove
        (moved.1.trans (piece.foldDecode_foldedKeep keep remove different).symm))).elim
    · exact moved.1.symm ▸ Set.mem_insert _ _
  · intro member
    rcases Set.mem_insert_iff.mp member with equality | ⟨adjacent, notRemove⟩
    · refine ⟨piece.foldedKeep keep remove different, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet,
          piece.identifyInternal_adj keep remove different]
        exact ⟨notKeep, Or.inr (Or.inr ⟨rfl, fromRemove⟩)⟩
      · simpa using equality.symm
    · let retained := piece.foldRetain remove other notRemove
      rw [SimpleGraph.mem_neighborSet] at adjacent
      refine ⟨retained, ?_, piece.foldDecode_foldRetain remove other notRemove⟩
      rw [SimpleGraph.mem_neighborSet,
        piece.identifyInternal_adj keep remove different]
      refine ⟨?_, Or.inl (by simpa [retained] using adjacent)⟩
      intro same
      have decoded := congrArg (piece.foldDecode remove) same
      have equality : piece.foldDecode remove vertex = other := by
        simpa [retained] using decoded
      exact adjacent.ne equality

/-- Every nonfolded vertex which is not a common neighbour keeps its exact
degree under the identification. -/
theorem degree_identifyInternal_of_not_common (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (vertex : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal)
    (notKeep : vertex ≠ piece.foldedKeep keep remove different)
    (notCommon : ¬ (piece.graph.Adj (.inr keep)
        (piece.foldDecode remove vertex) ∧
      piece.graph.Adj (.inr remove) (piece.foldDecode remove vertex))) :
    (piece.identifyInternal keep remove different).pack.degree vertex =
      piece.pack.degree (piece.foldDecode remove vertex) := by
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) :=
    @FinEnum.instFintype _ piece.pack.vertices
  have imageCard :
      (piece.identifyInternal keep remove different).pack.degree vertex =
        (piece.foldDecode remove ''
          ((piece.identifyInternal keep remove different).graph.neighborSet
            vertex)).ncard := by
    rw [FiniteObject.degree_eq_ncard_neighborSet,
      Set.ncard_image_of_injective _ (piece.foldDecode_injective remove)]
    rfl
  by_cases fromRemove :
      piece.graph.Adj (.inr remove) (piece.foldDecode remove vertex)
  · have notFromKeep :
        ¬ piece.graph.Adj (.inr keep) (piece.foldDecode remove vertex) :=
      fun adjacent => notCommon ⟨adjacent, fromRemove⟩
    rw [imageCard, piece.image_neighborSet_of_adj_remove keep remove different
      vertex notKeep fromRemove]
    have keepNotMem : (.inr keep : boundary.Vertex ⊕ piece.Internal) ∉
        piece.graph.neighborSet (piece.foldDecode remove vertex) \ {.inr remove} := by
      rintro ⟨adjacent, _⟩
      exact notFromKeep adjacent.symm
    rw [Set.ncard_insert_of_notMem keepNotMem (Set.toFinite _)]
    have removeMem : (.inr remove : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (piece.foldDecode remove vertex) :=
      fromRemove.symm
    have drop := Set.ncard_sdiff_singleton_add_one removeMem
      (Set.toFinite (piece.graph.neighborSet (piece.foldDecode remove vertex)))
    have sourceCard : piece.pack.degree (piece.foldDecode remove vertex) =
        (piece.graph.neighborSet (piece.foldDecode remove vertex)).ncard := by
      simpa [BoundaryPiece.pack] using
        piece.pack.degree_eq_ncard_neighborSet (piece.foldDecode remove vertex)
    rw [sourceCard]
    omega
  · rw [imageCard,
      piece.image_neighborSet_of_not_adj_remove keep remove different vertex
        notKeep fromRemove,
      FiniteObject.degree_eq_ncard_neighborSet]
    rfl

/-- A common neighbour loses exactly one incidence under the identification. -/
theorem degree_identifyInternal_of_common (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (vertex : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal)
    (notKeep : vertex ≠ piece.foldedKeep keep remove different)
    (common : piece.graph.Adj (.inr keep) (piece.foldDecode remove vertex) ∧
      piece.graph.Adj (.inr remove) (piece.foldDecode remove vertex)) :
    (piece.identifyInternal keep remove different).pack.degree vertex + 1 =
      piece.pack.degree (piece.foldDecode remove vertex) := by
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) :=
    @FinEnum.instFintype _ piece.pack.vertices
  have imageCard :
      (piece.identifyInternal keep remove different).pack.degree vertex =
        (piece.foldDecode remove ''
          ((piece.identifyInternal keep remove different).graph.neighborSet
            vertex)).ncard := by
    rw [FiniteObject.degree_eq_ncard_neighborSet,
      Set.ncard_image_of_injective _ (piece.foldDecode_injective remove)]
    rfl
  rw [imageCard, piece.image_neighborSet_of_adj_remove keep remove different
    vertex notKeep common.2]
  have keepMem : (.inr keep : boundary.Vertex ⊕ piece.Internal) ∈
      piece.graph.neighborSet (piece.foldDecode remove vertex) \ {.inr remove} := by
    exact ⟨common.1.symm, by simpa using different⟩
  rw [Set.insert_eq_of_mem keepMem]
  have removeMem : (.inr remove : boundary.Vertex ⊕ piece.Internal) ∈
      piece.graph.neighborSet (piece.foldDecode remove vertex) := common.2.symm
  have drop := Set.ncard_sdiff_singleton_add_one removeMem
    (Set.toFinite (piece.graph.neighborSet (piece.foldDecode remove vertex)))
  have sourceCard : piece.pack.degree (piece.foldDecode remove vertex) =
      (piece.graph.neighborSet (piece.foldDecode remove vertex)).ncard := by
    simpa [BoundaryPiece.pack] using
      piece.pack.degree_eq_ncard_neighborSet (piece.foldDecode remove vertex)
  rw [sourceCard]
  exact drop

/-- Folding two cubic vertices with at most one common neighbour leaves the
surviving folded vertex with degree at least three. -/
theorem three_le_degree_identifyInternal_foldedKeep
    (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (keepCubic : piece.pack.degree (.inr keep) = 3)
    (removeCubic : piece.pack.degree (.inr remove) = 3)
    (commonUnique : ∀ x y,
      (piece.graph.Adj (.inr keep) x ∧ piece.graph.Adj (.inr remove) x) →
      (piece.graph.Adj (.inr keep) y ∧ piece.graph.Adj (.inr remove) y) →
      x = y) :
    3 ≤ (piece.identifyInternal keep remove different).pack.degree
      (piece.foldedKeep keep remove different) := by
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) :=
    @FinEnum.instFintype _ piece.pack.vertices
  let leftSet := piece.graph.neighborSet (.inr keep) \ {.inr remove}
  let rightSet := piece.graph.neighborSet (.inr remove) \ {.inr keep}
  have imageCard :
      (piece.identifyInternal keep remove different).pack.degree
          (piece.foldedKeep keep remove different) =
        (leftSet ∪ rightSet).ncard := by
    rw [FiniteObject.degree_eq_ncard_neighborSet]
    calc
      _ = (piece.foldDecode remove ''
          ((piece.identifyInternal keep remove different).graph.neighborSet
            (piece.foldedKeep keep remove different))).ncard := by
        exact (Set.ncard_image_of_injective _
          (piece.foldDecode_injective remove)).symm
      _ = _ := by rw [piece.image_neighborSet_foldedKeep keep remove different]
  have leftCard : 2 ≤ leftSet.ncard := by
    have keepCard : (piece.graph.neighborSet (.inr keep)).ncard = 3 := by
      calc
        _ = piece.pack.degree (.inr keep) := by
          symm
          simpa [BoundaryPiece.pack] using
            piece.pack.degree_eq_ncard_neighborSet (.inr keep)
        _ = 3 := keepCubic
    by_cases adjacent : piece.graph.Adj (.inr keep) (.inr remove)
    · have drop := Set.ncard_sdiff_singleton_add_one adjacent
        (Set.toFinite (piece.graph.neighborSet (.inr keep)))
      change leftSet.ncard + 1 =
        (piece.graph.neighborSet (.inr keep)).ncard at drop
      rw [keepCard] at drop
      omega
    · have missing : (.inr remove : boundary.Vertex ⊕ piece.Internal) ∉
          piece.graph.neighborSet (.inr keep) := fun member => adjacent member
      have same : leftSet = piece.graph.neighborSet (.inr keep) :=
        Set.sdiff_singleton_eq_self missing
      rw [same, keepCard]
      omega
  have rightCard : 2 ≤ rightSet.ncard := by
    have removeCard : (piece.graph.neighborSet (.inr remove)).ncard = 3 := by
      calc
        _ = piece.pack.degree (.inr remove) := by
          symm
          simpa [BoundaryPiece.pack] using
            piece.pack.degree_eq_ncard_neighborSet (.inr remove)
        _ = 3 := removeCubic
    by_cases adjacent : piece.graph.Adj (.inr remove) (.inr keep)
    · have drop := Set.ncard_sdiff_singleton_add_one adjacent
        (Set.toFinite (piece.graph.neighborSet (.inr remove)))
      change rightSet.ncard + 1 =
        (piece.graph.neighborSet (.inr remove)).ncard at drop
      rw [removeCard] at drop
      omega
    · have missing : (.inr keep : boundary.Vertex ⊕ piece.Internal) ∉
          piece.graph.neighborSet (.inr remove) := fun member => adjacent member
      have same : rightSet = piece.graph.neighborSet (.inr remove) :=
        Set.sdiff_singleton_eq_self missing
      rw [same, removeCard]
      omega
  have intersectionCard : (leftSet ∩ rightSet).ncard ≤ 1 := by
    by_cases empty : leftSet ∩ rightSet = ∅
    · simp [empty]
    · obtain ⟨witness, witnessMem⟩ := Set.nonempty_iff_ne_empty.mpr empty
      have subset : leftSet ∩ rightSet ⊆ {witness} := by
        intro other otherMem
        have equality := commonUnique other witness
          ⟨otherMem.1.1, otherMem.2.1⟩
          ⟨witnessMem.1.1, witnessMem.2.1⟩
        simpa [equality]
      exact le_trans (Set.ncard_le_ncard subset (Set.toFinite _)) (by simp)
  have unionEquation := Set.ncard_union_add_ncard_inter leftSet rightSet
    (Set.toFinite leftSet) (Set.toFinite rightSet)
  rw [imageCard]
  omega

/-- Identification of internal vertices never changes a boundary--boundary
edge. -/
theorem boundaryGraph_identifyInternal (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    (piece.identifyInternal keep remove different).boundaryGraph =
      piece.boundaryGraph := by
  ext left right
  change (piece.identifyInternal keep remove different).graph.Adj
      (.inl left) (.inl right) ↔ piece.graph.Adj (.inl left) (.inl right)
  rw [piece.identifyInternal_adj keep remove different]
  simp only [foldDecode, Sum.inl.injEq, Sum.inl_ne_inr, false_and,
    or_false]
  constructor
  · rintro ⟨_, adjacent⟩
    exact adjacent
  · intro adjacent
    refine ⟨?_, adjacent⟩
    intro equality
    exact adjacent.ne (congrArg (fun vertex =>
      (Sum.inl vertex : boundary.Vertex ⊕ piece.Internal))
        (Sum.inl.inj equality))

/-- The internal fold removes exactly one internal vertex. -/
theorem internalVertexCount_identifyInternal_add_one
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) :
    (piece.identifyInternal keep remove different).internalVertexCount + 1 =
      piece.internalVertexCount := by
  letI : FinEnum piece.Internal := piece.internalVertices
  simp only [internalVertexCount, identifyInternal]
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  letI : Fintype piece.Internal := FinEnum.instFintype
  have complement := Fintype.card_subtype_compl
    (p := fun vertex : piece.Internal => vertex = remove)
  have singleton : Fintype.card {vertex : piece.Internal // vertex = remove} = 1 := by
    letI : Unique {vertex : piece.Internal // vertex = remove} :=
      { default := ⟨remove, rfl⟩
        uniq := fun vertex => Subtype.ext vertex.2 }
    exact Fintype.card_unique
  have complement' :
      Fintype.card {vertex : piece.Internal // vertex ≠ remove} =
        Fintype.card piece.Internal - 1 := by
    simpa [singleton] using complement
  have positive : 0 < Fintype.card piece.Internal :=
    Fintype.card_pos_iff.mpr ⟨remove⟩
  change Fintype.card {vertex : piece.Internal // vertex ≠ remove} + 1 =
    Fintype.card piece.Internal
  omega

/-- Consequently the fold is a strict local lexicographic decrease, before
any optional edge repair. -/
theorem identifyInternal_locallySmaller
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) :
    (piece.identifyInternal keep remove different).LocallySmaller piece := by
  rw [locallySmaller_iff]
  left
  have count := piece.internalVertexCount_identifyInternal_add_one
    keep remove different
  omega

/-- Add one repair edge to a boundary piece without changing its carrier or
its boundary labels. -/
noncomputable abbrev addEdge (piece : BoundaryPiece boundary)
    (left right : boundary.Vertex ⊕ piece.Internal) : BoundaryPiece boundary where
  Internal := piece.Internal
  internalVertices := piece.internalVertices
  graph := piece.graph ⊔ SimpleGraph.edge left right
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    letI : DecidableEq piece.Internal := piece.internalVertices.decEq
    letI : DecidableRel piece.graph.Adj := piece.decideAdj
    infer_instance

@[simp] theorem addEdge_adj (piece : BoundaryPiece boundary)
    (left right u v : boundary.Vertex ⊕ piece.Internal) :
    (piece.addEdge left right).graph.Adj u v ↔
      piece.graph.Adj u v ∨
        (((u = left ∧ v = right) ∨ (u = right ∧ v = left)) ∧ u ≠ v) := by
  simp only [addEdge, SimpleGraph.sup_adj, SimpleGraph.edge_adj]

/-- Adding an edge with an internal endpoint never changes a
boundary--boundary edge. -/
theorem boundaryGraph_addEdge_internalRight (piece : BoundaryPiece boundary)
    (left : boundary.Vertex ⊕ piece.Internal) (right : piece.Internal) :
    (piece.addEdge left (.inr right)).boundaryGraph = piece.boundaryGraph := by
  ext u v
  change (piece.addEdge left (.inr right)).graph.Adj (.inl u) (.inl v) ↔
    piece.graph.Adj (.inl u) (.inl v)
  rw [piece.addEdge_adj left (.inr right)]
  constructor
  · rintro (old | added)
    · exact old
    · rcases added with ⟨directions, _⟩
      rcases directions with direction | direction
      · exact (Sum.inl_ne_inr direction.2).elim
      · exact (Sum.inl_ne_inr direction.1).elim
  · exact Or.inl

/-- Piece-level form of the ordinary degree increment at the left endpoint. -/
theorem degree_addEdge_left (piece : BoundaryPiece boundary)
    (left right : boundary.Vertex ⊕ piece.Internal)
    (different : left ≠ right) (missing : ¬ piece.graph.Adj left right) :
    (piece.addEdge left right).pack.degree left = piece.pack.degree left + 1 := by
  simpa only [BoundaryPiece.addEdge, BoundaryPiece.pack,
    FiniteObject.addEdge] using
    FiniteObject.degree_addEdge_left piece.pack left right different missing

/-- Piece-level form of the ordinary degree increment at the right endpoint. -/
theorem degree_addEdge_right (piece : BoundaryPiece boundary)
    (left right : boundary.Vertex ⊕ piece.Internal)
    (different : left ≠ right) (missing : ¬ piece.graph.Adj left right) :
    (piece.addEdge left right).pack.degree right = piece.pack.degree right + 1 := by
  simpa only [BoundaryPiece.addEdge, BoundaryPiece.pack,
    FiniteObject.addEdge] using
    FiniteObject.degree_addEdge_right piece.pack left right different missing

/-- Every other vertex keeps its degree when the repair edge is added. -/
theorem degree_addEdge_of_ne (piece : BoundaryPiece boundary)
    (left right vertex : boundary.Vertex ⊕ piece.Internal)
    (notLeft : vertex ≠ left) (notRight : vertex ≠ right) :
    (piece.addEdge left right).pack.degree vertex = piece.pack.degree vertex := by
  simpa only [BoundaryPiece.addEdge, BoundaryPiece.pack,
    FiniteObject.addEdge] using
    FiniteObject.degree_addEdge_of_ne piece.pack left right vertex notLeft notRight

@[simp] theorem internalVertexCount_addEdge (piece : BoundaryPiece boundary)
    (left right : boundary.Vertex ⊕ piece.Internal) :
    (piece.addEdge left right).internalVertexCount = piece.internalVertexCount :=
  rfl

/-- Adding an edge after an internal fold does not spend the strict one-vertex
decrease. -/
theorem addEdge_identifyInternal_locallySmaller
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove)
    (left right : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal) :
    ((piece.identifyInternal keep remove different).addEdge left right).LocallySmaller
      piece := by
  rw [locallySmaller_iff]
  left
  rw [internalVertexCount_addEdge]
  have count := piece.internalVertexCount_identifyInternal_add_one
    keep remove different
  omega

end BoundaryPiece

end Hypostructure.Graph
