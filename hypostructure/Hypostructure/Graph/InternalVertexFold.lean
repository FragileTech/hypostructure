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

/-- **Folding two origins with no common neighbour keeps the surviving folded
vertex above the threshold.**  The image of its neighbourhood is the disjoint
union of the two source neighbourhoods minus the two identified endpoints, so
it has at least `(threshold - 1) + (threshold - 1)` members, and
`2 * threshold - 2 >= threshold` exactly when `2 <= threshold`. -/
theorem degree_identifyInternal_foldedKeep_eq (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    (piece.identifyInternal keep remove different).pack.degree
        (piece.foldedKeep keep remove different) =
      ((piece.graph.neighborSet (.inr keep) \ {.inr remove}) ∪
        (piece.graph.neighborSet (.inr remove) \ {.inr keep})).ncard := by
  classical
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) :=
    @FinEnum.instFintype _ piece.pack.vertices
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  calc
    _ = (piece.foldDecode remove ''
        ((piece.identifyInternal keep remove different).graph.neighborSet
          (piece.foldedKeep keep remove different))).ncard :=
      (Set.ncard_image_of_injective _ (piece.foldDecode_injective remove)).symm
    _ = _ := by rw [piece.image_neighborSet_foldedKeep keep remove different]

theorem le_degree_identifyInternal_foldedKeep
    (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (threshold : Nat) (two : 2 ≤ threshold)
    (keepDegree : threshold ≤ piece.pack.degree (.inr keep))
    (removeDegree : threshold ≤ piece.pack.degree (.inr remove))
    (noCommon : ∀ x, ¬ (piece.graph.Adj (.inr keep) x ∧
      piece.graph.Adj (.inr remove) x)) :
    threshold ≤ (piece.identifyInternal keep remove different).pack.degree
      (piece.foldedKeep keep remove different) := by
  classical
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) :=
    @FinEnum.instFintype _ piece.pack.vertices
  let leftSet := piece.graph.neighborSet (.inr keep) \ {.inr remove}
  let rightSet := piece.graph.neighborSet (.inr remove) \ {.inr keep}
  have imageCard :
      (piece.identifyInternal keep remove different).pack.degree
          (piece.foldedKeep keep remove different) =
        (leftSet ∪ rightSet).ncard :=
    piece.degree_identifyInternal_foldedKeep_eq keep remove different
  have leftCard : threshold - 1 ≤ leftSet.ncard := by
    have keepCard : threshold ≤ (piece.graph.neighborSet (.inr keep)).ncard := by
      refine le_trans keepDegree (le_of_eq ?_)
      simpa [BoundaryPiece.pack] using
        piece.pack.degree_eq_ncard_neighborSet (.inr keep)
    by_cases adjacent : piece.graph.Adj (.inr keep) (.inr remove)
    · have drop := Set.ncard_sdiff_singleton_add_one adjacent
        (Set.toFinite (piece.graph.neighborSet (.inr keep)))
      change leftSet.ncard + 1 =
        (piece.graph.neighborSet (.inr keep)).ncard at drop
      omega
    · have missing : (.inr remove : boundary.Vertex ⊕ piece.Internal) ∉
          piece.graph.neighborSet (.inr keep) := fun member => adjacent member
      have same : leftSet = piece.graph.neighborSet (.inr keep) :=
        Set.sdiff_singleton_eq_self missing
      rw [same]
      omega
  have rightCard : threshold - 1 ≤ rightSet.ncard := by
    have removeCard : threshold ≤
        (piece.graph.neighborSet (.inr remove)).ncard := by
      refine le_trans removeDegree (le_of_eq ?_)
      simpa [BoundaryPiece.pack] using
        piece.pack.degree_eq_ncard_neighborSet (.inr remove)
    by_cases adjacent : piece.graph.Adj (.inr remove) (.inr keep)
    · have drop := Set.ncard_sdiff_singleton_add_one adjacent
        (Set.toFinite (piece.graph.neighborSet (.inr remove)))
      change rightSet.ncard + 1 =
        (piece.graph.neighborSet (.inr remove)).ncard at drop
      omega
    · have missing : (.inr keep : boundary.Vertex ⊕ piece.Internal) ∉
          piece.graph.neighborSet (.inr remove) := fun member => adjacent member
      have same : rightSet = piece.graph.neighborSet (.inr remove) :=
        Set.sdiff_singleton_eq_self missing
      rw [same]
      omega
  have disjoint : leftSet ∩ rightSet = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro other ⟨⟨keepAdj, _⟩, ⟨removeAdj, _⟩⟩
    exact noCommon other ⟨keepAdj, removeAdj⟩
  have intersectionCard : (leftSet ∩ rightSet).ncard = 0 := by
    rw [disjoint]
    simp
  have unionEquation := Set.ncard_union_add_ncard_inter leftSet rightSet
    (Set.toFinite leftSet) (Set.toFinite rightSet)
  rw [imageCard]
  omega

/-- **Cubic triangle contraction: the doubly folded vertex keeps the
baseline.**

`keep`, `remove`, `x` are three mutually adjacent internal vertices, each at
least at the baseline, and each pair's common neighbour is the third (which is
what `FiniteObject.commonNeighbor_unique` gives from `K .selection` and
`LengthOK 4`).  Folding `keep` with `remove` and then folding `x` into the
merged vertex leaves it with the three *outside* neighbourhoods
`N(keep) \ {remove, x}`, `N(remove) \ {keep, x}` and `N(x) \ {keep, remove}`,
which are pairwise disjoint and each of size at least `threshold - 2`.  For
`3 ≤ threshold` that is at least `threshold`, so the intermediate degree-two
vertex never has to be repaired. -/
theorem le_degree_triangleContraction (piece : BoundaryPiece boundary)
    (keep remove x : piece.Internal)
    (keepRemove : keep ≠ remove) (xRemove : x ≠ remove)
    (second :
      (⟨keep, keepRemove⟩ :
        (piece.identifyInternal keep remove keepRemove).Internal) ≠
        ⟨x, xRemove⟩)
    (edgeKX : piece.graph.Adj (.inr keep) (.inr x))
    (edgeRX : piece.graph.Adj (.inr remove) (.inr x))
    (edgeKR : piece.graph.Adj (.inr keep) (.inr remove))
    (threshold : Nat) (three : 3 ≤ threshold)
    (keepDegree : threshold ≤ piece.pack.degree (.inr keep))
    (removeDegree : threshold ≤ piece.pack.degree (.inr remove))
    (xDegree : threshold ≤ piece.pack.degree (.inr x))
    (uniqueKR : ∀ y, piece.graph.Adj (.inr keep) y →
      piece.graph.Adj (.inr remove) y → y = .inr x)
    (uniqueKX : ∀ y, piece.graph.Adj (.inr keep) y →
      piece.graph.Adj (.inr x) y → y = .inr remove)
    (uniqueRX : ∀ y, piece.graph.Adj (.inr remove) y →
      piece.graph.Adj (.inr x) y → y = .inr keep) :
    threshold ≤
      ((piece.identifyInternal keep remove keepRemove).identifyInternal
          ⟨keep, keepRemove⟩ ⟨x, xRemove⟩ second).pack.degree
        ((piece.identifyInternal keep remove keepRemove).foldedKeep
          ⟨keep, keepRemove⟩ ⟨x, xRemove⟩ second) := by
  classical
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) :=
    @FinEnum.instFintype _ piece.pack.vertices
  have xKeep : x ≠ keep := by
    intro equal
    exact second (Subtype.ext (by simpa using equal.symm))
  set P1 := piece.identifyInternal keep remove keepRemove with P1def
  -- the exact count at the second fold, inside `P1`
  rw [P1.degree_identifyInternal_foldedKeep_eq ⟨keep, keepRemove⟩ ⟨x, xRemove⟩
    second]
  -- transport the two neighbourhoods down to `piece`
  have inj := piece.foldDecode_injective remove
  have notKeepX :
      (Sum.inr ⟨x, xRemove⟩ : boundary.Vertex ⊕ P1.Internal) ≠
        piece.foldedKeep keep remove keepRemove := by
    intro equal
    exact xKeep (congrArg Subtype.val (Sum.inr.inj equal))
  have fromRemoveX :
      piece.graph.Adj (.inr remove)
        (piece.foldDecode remove (Sum.inr ⟨x, xRemove⟩)) := edgeRX
  have foldedEq :
      (Sum.inr ⟨keep, keepRemove⟩ : boundary.Vertex ⊕ P1.Internal) =
        piece.foldedKeep keep remove keepRemove := rfl
  -- the final neighbourhood, read in `piece`
  set A := piece.graph.neighborSet (.inr keep) \ {.inr remove, .inr x} with Adef
  set B := piece.graph.neighborSet (.inr remove) \ {.inr keep, .inr x} with Bdef
  set C := piece.graph.neighborSet (.inr x) \ {.inr keep, .inr remove} with Cdef
  have imageEq :
      piece.foldDecode remove ''
        ((P1.graph.neighborSet (Sum.inr ⟨keep, keepRemove⟩) \
            {Sum.inr ⟨x, xRemove⟩}) ∪
          (P1.graph.neighborSet (Sum.inr ⟨x, xRemove⟩) \
            {Sum.inr ⟨keep, keepRemove⟩})) = A ∪ B ∪ C := by
    rw [Set.image_union, Set.image_sdiff inj, Set.image_sdiff inj,
      Set.image_singleton, Set.image_singleton, foldedEq,
      piece.image_neighborSet_foldedKeep keep remove keepRemove,
      piece.image_neighborSet_of_adj_remove keep remove keepRemove
        (Sum.inr ⟨x, xRemove⟩) notKeepX fromRemoveX]
    have decodeX : piece.foldDecode remove
        (Sum.inr ⟨x, xRemove⟩ : boundary.Vertex ⊕ P1.Internal) =
        (.inr x : boundary.Vertex ⊕ piece.Internal) := rfl
    have decodeKeep : piece.foldDecode remove
        (piece.foldedKeep keep remove keepRemove) =
        (.inr keep : boundary.Vertex ⊕ piece.Internal) := rfl
    rw [decodeX, decodeKeep]
    ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_insert_iff, SimpleGraph.mem_neighborSet, Adef, Bdef, Cdef]
    constructor
    · rintro (⟨inU, yNeX⟩ | ⟨yIn, yNeKeep⟩)
      · rcases inU with ⟨keepAdj, yNeRemove⟩ | ⟨removeAdj, yNeKeep⟩
        · exact Or.inl (Or.inl ⟨keepAdj, by simp [yNeRemove, yNeX]⟩)
        · exact Or.inl (Or.inr ⟨removeAdj, by simp [yNeKeep, yNeX]⟩)
      · rcases yIn with rfl | ⟨xAdj, yNeRemove⟩
        · exact absurd rfl yNeKeep
        · exact Or.inr ⟨xAdj, by simp [yNeKeep, yNeRemove]⟩
    · rintro ((⟨keepAdj, yOut⟩ | ⟨removeAdj, yOut⟩) | ⟨xAdj, yOut⟩)
      · simp only [not_or] at yOut
        exact Or.inl ⟨Or.inl ⟨keepAdj, yOut.1⟩, yOut.2⟩
      · simp only [not_or] at yOut
        exact Or.inl ⟨Or.inr ⟨removeAdj, yOut.1⟩, yOut.2⟩
      · simp only [not_or] at yOut
        exact Or.inr ⟨Or.inr ⟨xAdj, yOut.2⟩, yOut.1⟩
  have countEq :
      ((P1.graph.neighborSet (Sum.inr ⟨keep, keepRemove⟩) \
            {Sum.inr ⟨x, xRemove⟩}) ∪
          (P1.graph.neighborSet (Sum.inr ⟨x, xRemove⟩) \
            {Sum.inr ⟨keep, keepRemove⟩})).ncard = (A ∪ B ∪ C).ncard := by
    rw [← imageEq, Set.ncard_image_of_injective _ inj]
  rw [countEq]
  -- the three outside neighbourhoods are pairwise disjoint
  have disjointAB : A ∩ B = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro y ⟨⟨keepAdj, yOutA⟩, ⟨removeAdj, _⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at yOutA
    exact yOutA.2 (uniqueKR y keepAdj removeAdj)
  have disjointAC : A ∩ C = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro y ⟨⟨keepAdj, yOutA⟩, ⟨xAdj, _⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at yOutA
    exact yOutA.1 (uniqueKX y keepAdj xAdj)
  have disjointBC : B ∩ C = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro y ⟨⟨removeAdj, _⟩, ⟨xAdj, yOutC⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at yOutC
    exact yOutC.1 (uniqueRX y removeAdj xAdj)
  have disjointABC : (A ∪ B) ∩ C = ∅ := by
    rw [Set.union_inter_distrib_right, disjointAC, disjointBC, Set.union_self]
  -- each outside neighbourhood loses exactly the two triangle partners
  have cardA : A.ncard + 2 = piece.pack.degree (.inr keep) := by
    have degEq : piece.pack.degree (.inr keep) =
        (piece.graph.neighborSet (.inr keep)).ncard := by
      simpa [BoundaryPiece.pack] using
        piece.pack.degree_eq_ncard_neighborSet (.inr keep)
    have removeMem : (.inr remove : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (.inr keep) := edgeKR
    have dropRemove := Set.ncard_sdiff_singleton_add_one removeMem
      (Set.toFinite (piece.graph.neighborSet (.inr keep)))
    have xMem : (.inr x : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (.inr keep) \ {.inr remove} :=
      ⟨edgeKX, by simpa using xRemove⟩
    have dropX := Set.ncard_sdiff_singleton_add_one xMem
      (Set.toFinite (piece.graph.neighborSet (.inr keep) \ {.inr remove}))
    have sdiffEq : A = (piece.graph.neighborSet (.inr keep) \ {.inr remove}) \
        {.inr x} := by
      rw [Adef]; ext y; simp [and_assoc]
    rw [degEq, sdiffEq]
    omega
  have cardB : B.ncard + 2 = piece.pack.degree (.inr remove) := by
    have degEq : piece.pack.degree (.inr remove) =
        (piece.graph.neighborSet (.inr remove)).ncard := by
      simpa [BoundaryPiece.pack] using
        piece.pack.degree_eq_ncard_neighborSet (.inr remove)
    have keepMem : (.inr keep : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (.inr remove) := edgeKR.symm
    have dropKeep := Set.ncard_sdiff_singleton_add_one keepMem
      (Set.toFinite (piece.graph.neighborSet (.inr remove)))
    have xMem : (.inr x : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (.inr remove) \ {.inr keep} :=
      ⟨edgeRX, by simpa using xKeep⟩
    have dropX := Set.ncard_sdiff_singleton_add_one xMem
      (Set.toFinite (piece.graph.neighborSet (.inr remove) \ {.inr keep}))
    have sdiffEq : B = (piece.graph.neighborSet (.inr remove) \ {.inr keep}) \
        {.inr x} := by
      rw [Bdef]; ext y; simp [and_assoc]
    rw [degEq, sdiffEq]
    omega
  have cardC : C.ncard + 2 = piece.pack.degree (.inr x) := by
    have degEq : piece.pack.degree (.inr x) =
        (piece.graph.neighborSet (.inr x)).ncard := by
      simpa [BoundaryPiece.pack] using
        piece.pack.degree_eq_ncard_neighborSet (.inr x)
    have keepMem : (.inr keep : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (.inr x) := edgeKX.symm
    have dropKeep := Set.ncard_sdiff_singleton_add_one keepMem
      (Set.toFinite (piece.graph.neighborSet (.inr x)))
    have removeMem : (.inr remove : boundary.Vertex ⊕ piece.Internal) ∈
        piece.graph.neighborSet (.inr x) \ {.inr keep} :=
      ⟨edgeRX.symm, by simpa using Ne.symm keepRemove⟩
    have dropRemove := Set.ncard_sdiff_singleton_add_one removeMem
      (Set.toFinite (piece.graph.neighborSet (.inr x) \ {.inr keep}))
    have sdiffEq : C = (piece.graph.neighborSet (.inr x) \ {.inr keep}) \
        {.inr remove} := by
      rw [Cdef]; ext y; simp [and_assoc]
    rw [degEq, sdiffEq]
    omega
  -- add the three disjoint counts
  have unionAB := Set.ncard_union_add_ncard_inter A B
    (Set.toFinite A) (Set.toFinite B)
  have unionABC := Set.ncard_union_add_ncard_inter (A ∪ B) C
    (Set.toFinite (A ∪ B)) (Set.toFinite C)
  rw [disjointAB] at unionAB
  rw [disjointABC] at unionABC
  simp only [Set.ncard_empty] at unionAB unionABC
  omega

/-- **The second fold of a contracted triangle has no common neighbour at
all.**  A common neighbour of the merged vertex and of `x` would be a second
common neighbour of one of the three triangle pairs, which
`FiniteObject.commonNeighbor_unique` forbids. -/
theorem noCommon_second_of_triangle (piece : BoundaryPiece boundary)
    (keep remove x : piece.Internal)
    (keepRemove : keep ≠ remove) (xRemove : x ≠ remove) (xKeep : x ≠ keep)
    (edgeRX : piece.graph.Adj (.inr remove) (.inr x))
    (uniqueKX : ∀ y, piece.graph.Adj (.inr keep) y →
      piece.graph.Adj (.inr x) y → y = .inr remove)
    (uniqueRX : ∀ y, piece.graph.Adj (.inr remove) y →
      piece.graph.Adj (.inr x) y → y = .inr keep) :
    ∀ y, ¬ ((piece.identifyInternal keep remove keepRemove).graph.Adj
          (.inr ⟨keep, keepRemove⟩) y ∧
        (piece.identifyInternal keep remove keepRemove).graph.Adj
          (.inr ⟨x, xRemove⟩) y) := by
  classical
  have notKeepX :
      (Sum.inr ⟨x, xRemove⟩ : boundary.Vertex ⊕
        (piece.identifyInternal keep remove keepRemove).Internal) ≠
        piece.foldedKeep keep remove keepRemove := by
    intro equal
    exact xKeep (congrArg Subtype.val (Sum.inr.inj equal))
  have fromRemoveX :
      piece.graph.Adj (.inr remove)
        (piece.foldDecode remove
          (Sum.inr ⟨x, xRemove⟩ : boundary.Vertex ⊕
            (piece.identifyInternal keep remove keepRemove).Internal)) := edgeRX
  rintro w ⟨mergedAdj, xAdj⟩
  -- the decoded neighbour lies in both images
  have inMerged : piece.foldDecode remove w ∈
      (piece.graph.neighborSet (.inr keep) \ {.inr remove}) ∪
        (piece.graph.neighborSet (.inr remove) \ {.inr keep}) := by
    rw [← piece.image_neighborSet_foldedKeep keep remove keepRemove]
    exact ⟨w, mergedAdj, rfl⟩
  have inX : piece.foldDecode remove w ∈
      insert (.inr keep)
        (piece.graph.neighborSet
          (piece.foldDecode remove (Sum.inr ⟨x, xRemove⟩)) \ {.inr remove}) := by
    rw [← piece.image_neighborSet_of_adj_remove keep remove keepRemove
      (Sum.inr ⟨x, xRemove⟩) notKeepX fromRemoveX]
    exact ⟨w, xAdj, rfl⟩
  have decodeX : piece.foldDecode remove
      (Sum.inr ⟨x, xRemove⟩ : boundary.Vertex ⊕
        (piece.identifyInternal keep remove keepRemove).Internal) =
      (.inr x : boundary.Vertex ⊕ piece.Internal) := rfl
  rw [decodeX] at inX
  -- the merged image never contains `keep` itself
  have notKeepImage : piece.foldDecode remove w ≠
      (.inr keep : boundary.Vertex ⊕ piece.Internal) := by
    intro equal
    rw [equal] at inMerged
    rcases inMerged with ⟨selfAdj, _⟩ | ⟨_, notKeep⟩
    · exact (piece.graph.irrefl selfAdj)
    · exact notKeep rfl
  rcases inX with equalKeep | ⟨xAdjDecoded, notRemove⟩
  · exact notKeepImage equalKeep
  rcases inMerged with ⟨keepAdj, _⟩ | ⟨removeAdj, notKeep⟩
  · exact notRemove (uniqueKX _ keepAdj xAdjDecoded)
  · exact notKeep (uniqueRX _ removeAdj xAdjDecoded)

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

/-! ## The fold as a boundaried replacement: profile, overlap, descent, baseline

`def:typeA-trace-basin` asks a response quotient to be realized by "a boundaried
response state with the same boundary degree profile".  The identification does
that, and -- unlike an edge deletion -- it spends a *vertex* rather than an
edge, so the descent and the minimum-degree baseline stop competing. -/

/-- **The identification preserves the boundary degree profile** exactly when no
boundary *label* is a common neighbour of the two origins.

`def:typeA-trace-basin`: a trace-local and support-internal response quotient
"identifies or forgets entries of the fixed coordinate family, preserves the
full boundary degree profile, and does not delete a boundary incidence".  The
identification spends exactly one incidence, at a common neighbour of the two
origins, so the profile survives precisely when that common neighbour is not
labelled.  A common neighbour interior to the piece costs the profile nothing;
only the internal degrees see it. -/
theorem boundaryDegreeProfile_identifyInternal_of_noCommonLabel
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove)
    (noCommonLabel : ∀ label : boundary.Vertex,
      ¬ (piece.graph.Adj (.inr keep) (.inl label) ∧
        piece.graph.Adj (.inr remove) (.inl label))) :
    (piece.identifyInternal keep remove different).boundaryDegreeProfile =
      piece.boundaryDegreeProfile := by
  funext label
  show (piece.identifyInternal keep remove different).pack.degree (.inl label) =
    piece.pack.degree (.inl label)
  have notKeep : (Sum.inl label :
      boundary.Vertex ⊕ (piece.identifyInternal keep remove different).Internal) ≠
      piece.foldedKeep keep remove different := by
    simp [BoundaryPiece.foldedKeep]
  simpa [BoundaryPiece.foldDecode] using
    piece.degree_identifyInternal_of_not_common keep remove different
      (.inl label) notKeep (noCommonLabel label)

/-- **The repaired identification preserves the boundary degree profile.**

`FiniteObject.FoldPlan`'s second arm: the two origins have a common neighbour
`common`, which the identification costs exactly one incidence
(`degree_identifyInternal_of_common`), and the missing incidence is restored by
joining `common` to a surviving vertex `repair`.  The profile survives exactly
when the repair endpoint is *interior*: a labelled repair endpoint would gain a
boundary degree the source piece never had, and no other label moves because
`common` is the only common neighbour among the labels.  This is
`def:typeA-trace-basin`'s "preserves the full boundary degree profile" read at
the repaired fold. -/
theorem boundaryDegreeProfile_addEdge_identifyInternal_of_common
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove)
    (common : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal)
    (repair : (piece.identifyInternal keep remove different).Internal)
    (commonNotKeep : common ≠ piece.foldedKeep keep remove different)
    (isCommon : piece.graph.Adj (.inr keep) (piece.foldDecode remove common) ∧
      piece.graph.Adj (.inr remove) (piece.foldDecode remove common))
    (uniqueCommonLabel : ∀ label : boundary.Vertex,
      (Sum.inl label : boundary.Vertex ⊕
        (piece.identifyInternal keep remove different).Internal) ≠ common →
      ¬ (piece.graph.Adj (.inr keep) (.inl label) ∧
        piece.graph.Adj (.inr remove) (.inl label)))
    (repairNe : common ≠ .inr repair)
    (repairMissing : ¬ (piece.identifyInternal keep remove different).graph.Adj
      common (.inr repair)) :
    ((piece.identifyInternal keep remove different).addEdge common
        (.inr repair)).boundaryDegreeProfile = piece.boundaryDegreeProfile := by
  funext label
  show ((piece.identifyInternal keep remove different).addEdge common
      (.inr repair)).pack.degree (.inl label) = piece.pack.degree (.inl label)
  by_cases atCommon : (Sum.inl label : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal) = common
  · subst atCommon
    rw [(piece.identifyInternal keep remove different).degree_addEdge_left
      (.inl label) (.inr repair) repairNe repairMissing]
    simpa [BoundaryPiece.foldDecode] using
      piece.degree_identifyInternal_of_common keep remove different (.inl label)
        commonNotKeep isCommon
  · rw [(piece.identifyInternal keep remove different).degree_addEdge_of_ne
      common (.inr repair) (.inl label) atCommon (by simp)]
    have notKeep : (Sum.inl label : boundary.Vertex ⊕
        (piece.identifyInternal keep remove different).Internal) ≠
        piece.foldedKeep keep remove different := by
      simp [BoundaryPiece.foldedKeep]
    simpa [BoundaryPiece.foldDecode] using
      piece.degree_identifyInternal_of_not_common keep remove different
        (.inl label) notKeep (uniqueCommonLabel label atCommon)

end BoundaryPiece

/-- Identification never changes which boundary--boundary edges the piece owns,
so its overlap-degree profile against any context is unchanged. -/
theorem boundaryOverlapDegreeProfile_identifyInternal
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) (outside : OutsideContext boundary) :
    boundaryOverlapDegreeProfile (piece.identifyInternal keep remove different)
        outside =
      boundaryOverlapDegreeProfile piece outside := by
  have graphEq :
      boundaryOverlapGraph (piece.identifyInternal keep remove different)
          outside =
        boundaryOverlapGraph piece outside := by
    unfold boundaryOverlapGraph
    rw [piece.boundaryGraph_identifyInternal keep remove different]
  funext vertex
  show boundaryOverlapDegree (piece.identifyInternal keep remove different)
      outside vertex = boundaryOverlapDegree piece outside vertex
  rw [boundaryOverlapDegree_eq_ncard, boundaryOverlapDegree_eq_ncard, graphEq]

/-- The overlap edge count is unchanged too, for the same reason. -/
theorem boundaryOverlapEdgeCount_identifyInternal
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) (outside : OutsideContext boundary) :
    boundaryOverlapEdgeCount (piece.identifyInternal keep remove different)
        outside =
      boundaryOverlapEdgeCount piece outside := by
  have graphEq :
      boundaryOverlapGraph (piece.identifyInternal keep remove different)
          outside =
        boundaryOverlapGraph piece outside := by
    unfold boundaryOverlapGraph
    rw [piece.boundaryGraph_identifyInternal keep remove different]
  show (boundaryOverlapObject (piece.identifyInternal keep remove different)
      outside).edgeCount = (boundaryOverlapObject piece outside).edgeCount
  rw [FiniteObject.edgeCount_eq_ncard_edgeSet,
    FiniteObject.edgeCount_eq_ncard_edgeSet]
  congr 2

/-- **Descent.**  The fold spends one internal vertex and leaves the overlap
alone, so the gluing is strictly lexicographically smaller -- by VERTEX count,
with no edge-count argument at all. -/
theorem lexicographicallySmaller_glue_identifyInternal
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) (outside : OutsideContext boundary) :
    (glue (piece.identifyInternal keep remove different)
      outside).LexicographicallySmaller (glue piece outside) :=
  glue_lexicographicallySmaller_of_local_of_overlapCount_eq outside
    (piece.identifyInternal_locallySmaller keep remove different)
    (boundaryOverlapEdgeCount_identifyInternal piece keep remove different
      outside)

/-- **Descent, twice.**  Two successive identifications spend two internal
vertices and still leave the boundary--boundary edges alone, so the gluing is
strictly lexicographically smaller — again by vertex count only.  Nothing here
is special to a contracted triangle. -/
theorem lexicographicallySmaller_glue_identifyInternal_twice
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove)
    (keep' remove' : (piece.identifyInternal keep remove different).Internal)
    (different' : keep' ≠ remove') (outside : OutsideContext boundary) :
    (glue ((piece.identifyInternal keep remove different).identifyInternal
      keep' remove' different') outside).LexicographicallySmaller
      (glue piece outside) := by
  refine glue_lexicographicallySmaller_of_local_of_overlapCount_eq outside ?_ ?_
  · rw [BoundaryPiece.locallySmaller_iff]
    left
    have first := piece.internalVertexCount_identifyInternal_add_one keep remove
      different
    have secondCount := (piece.identifyInternal keep remove
      different).internalVertexCount_identifyInternal_add_one keep' remove'
      different'
    omega
  · rw [boundaryOverlapEdgeCount_identifyInternal,
      boundaryOverlapEdgeCount_identifyInternal]

/-- **Baseline.**  Every glued vertex other than the surviving folded vertex
keeps literally the degree it had: a boundary label because the profile and the
overlap are both unchanged, a context-internal vertex because the piece
contributes nothing to it, and a surviving internal vertex by
`degree_identifyInternal_of_not_common`.  The folded vertex is
`le_degree_identifyInternal_foldedKeep`.  Nothing is deleted, so nothing
fights `lexicographicallySmaller_glue_identifyInternal`. -/
theorem le_minDegree_glue_identifyInternal
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) (outside : OutsideContext boundary)
    (threshold : Nat) (two : 2 ≤ threshold)
    (nonempty : Nonempty
      (glue (piece.identifyInternal keep remove different) outside).Vertex)
    (sourceBaseline : threshold ≤ (glue piece outside).minDegree)
    (keepDegree : threshold ≤ piece.pack.degree (.inr keep))
    (removeDegree : threshold ≤ piece.pack.degree (.inr remove))
    (noCommon : ∀ x, ¬ (piece.graph.Adj (.inr keep) x ∧
      piece.graph.Adj (.inr remove) x)) :
    threshold ≤
      (glue (piece.identifyInternal keep remove different) outside).minDegree := by
  classical
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro vertex
  cases vertex with
  | inl label =>
      rw [glue_boundaryDegree_eq_of_local_eq_of_overlap_eq outside
        (piece.boundaryDegreeProfile_identifyInternal_of_noCommonLabel keep remove
          different (fun label => noCommon (.inl label)))
        (boundaryOverlapDegreeProfile_identifyInternal piece keep remove
          different outside) label]
      exact sourceBaseline.trans
        ((glue piece outside).minDegree_le_degree (.inl label))
  | inr internal =>
      cases internal with
      | inl pieceInternal =>
          rw [glue_degree_pieceInternal]
          by_cases folded : pieceInternal = ⟨keep, different⟩
          · subst folded
            exact piece.le_degree_identifyInternal_foldedKeep keep remove
              different threshold two keepDegree removeDegree noCommon
          · have notKeep : (Sum.inr pieceInternal :
                boundary.Vertex ⊕
                  (piece.identifyInternal keep remove different).Internal) ≠
                piece.foldedKeep keep remove different := by
              simp [BoundaryPiece.foldedKeep, folded]
            rw [show (piece.identifyInternal keep remove different).pack.degree
                  (.inr pieceInternal) =
                (piece.identifyInternal keep remove different).pack.degree
                  (Sum.inr pieceInternal) from rfl,
              piece.degree_identifyInternal_of_not_common keep remove different
                (.inr pieceInternal) notKeep (noCommon _)]
            have transferred := sourceBaseline.trans
              ((glue piece outside).minDegree_le_degree
                (.inr (.inl pieceInternal.1)))
            rw [glue_degree_pieceInternal] at transferred
            simpa [BoundaryPiece.foldDecode] using transferred
      | inr contextInternal =>
          rw [glue_degree_contextInternal]
          have transferred := sourceBaseline.trans
            ((glue piece outside).minDegree_le_degree
              (.inr (.inr contextInternal)))
          rwa [glue_degree_contextInternal] at transferred

/-- **The glued baseline survives a cubic triangle contraction.**

Every glued vertex of the doubly folded piece keeps at least the threshold: a
boundary label because both folds preserve the profile and the overlap (the
common neighbours are interior, so no label moves), a surviving internal vertex
because it is a common neighbour in neither fold, the merged vertex by
`le_degree_triangleContraction`, and a context vertex because the piece
contributes nothing to it.  The intermediate degree-two vertex is never
consulted: it is exactly the vertex the second fold removes. -/
theorem le_minDegree_glue_triangleContraction (piece : BoundaryPiece boundary)
    (keep remove x : piece.Internal)
    (keepRemove : keep ≠ remove) (xRemove : x ≠ remove)
    (second :
      (⟨keep, keepRemove⟩ :
        (piece.identifyInternal keep remove keepRemove).Internal) ≠
        ⟨x, xRemove⟩)
    (edgeKX : piece.graph.Adj (.inr keep) (.inr x))
    (edgeRX : piece.graph.Adj (.inr remove) (.inr x))
    (edgeKR : piece.graph.Adj (.inr keep) (.inr remove))
    (outside : OutsideContext boundary)
    (threshold : Nat) (three : 3 ≤ threshold)
    (sourceBaseline : threshold ≤ (glue piece outside).minDegree)
    (uniqueKR : ∀ y, piece.graph.Adj (.inr keep) y →
      piece.graph.Adj (.inr remove) y → y = .inr x)
    (uniqueKX : ∀ y, piece.graph.Adj (.inr keep) y →
      piece.graph.Adj (.inr x) y → y = .inr remove)
    (uniqueRX : ∀ y, piece.graph.Adj (.inr remove) y →
      piece.graph.Adj (.inr x) y → y = .inr keep) :
    threshold ≤
      (glue ((piece.identifyInternal keep remove keepRemove).identifyInternal
        ⟨keep, keepRemove⟩ ⟨x, xRemove⟩ second) outside).minDegree := by
  classical
  have xKeep : x ≠ keep := by
    intro equal
    exact second (Subtype.ext (by simpa using equal.symm))
  set P1 := piece.identifyInternal keep remove keepRemove with P1def
  set m : P1.Internal := ⟨keep, keepRemove⟩ with mdef
  set x' : P1.Internal := ⟨x, xRemove⟩ with x'def
  set P2 := P1.identifyInternal m x' second with P2def
  -- the two fold clauses
  have noCommonFirst : ∀ y, ¬ (piece.graph.Adj (.inr keep) y ∧
      piece.graph.Adj (.inr remove) y) ∨ y = (.inr x : _) := by
    intro y
    by_cases common : piece.graph.Adj (.inr keep) y ∧ piece.graph.Adj (.inr remove) y
    · exact Or.inr (uniqueKR y common.1 common.2)
    · exact Or.inl common
  have noCommonLabelFirst : ∀ label : boundary.Vertex,
      ¬ (piece.graph.Adj (.inr keep) (.inl label) ∧
        piece.graph.Adj (.inr remove) (.inl label)) := by
    intro label common
    exact Sum.inl_ne_inr (uniqueKR _ common.1 common.2)
  have noCommonSecond := piece.noCommon_second_of_triangle keep remove x
    keepRemove xRemove xKeep edgeRX uniqueKX uniqueRX
  have noCommonLabelSecond : ∀ label : boundary.Vertex,
      ¬ (P1.graph.Adj (.inr m) (.inl label) ∧
        P1.graph.Adj (.inr x') (.inl label)) :=
    fun label => noCommonSecond (.inl label)
  -- profile and overlap survive both folds
  have profileTwo : P2.boundaryDegreeProfile = piece.boundaryDegreeProfile :=
    (P1.boundaryDegreeProfile_identifyInternal_of_noCommonLabel m x' second
      noCommonLabelSecond).trans
      (piece.boundaryDegreeProfile_identifyInternal_of_noCommonLabel keep remove
        keepRemove noCommonLabelFirst)
  have overlapTwo : boundaryOverlapDegreeProfile P2 outside =
      boundaryOverlapDegreeProfile piece outside :=
    (boundaryOverlapDegreeProfile_identifyInternal P1 m x' second outside).trans
      (boundaryOverlapDegreeProfile_identifyInternal piece keep remove keepRemove
        outside)
  letI : Nonempty (glue P2 outside).Vertex := ⟨.inr (.inl ⟨m, second⟩)⟩
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro vertex
  cases vertex with
  | inl label =>
      rw [glue_boundaryDegree_eq_of_local_eq_of_overlap_eq outside profileTwo
        overlapTwo label]
      exact sourceBaseline.trans
        ((glue piece outside).minDegree_le_degree (.inl label))
  | inr internal =>
      cases internal with
      | inl pieceInternal =>
          rw [glue_degree_pieceInternal]
          by_cases folded : pieceInternal = ⟨m, second⟩
          · subst folded
            refine le_trans ?_ (le_of_eq rfl)
            exact piece.le_degree_triangleContraction keep remove x keepRemove
              xRemove second edgeKX edgeRX edgeKR threshold three
              (by
                have transferred := sourceBaseline.trans
                  ((glue piece outside).minDegree_le_degree (.inr (.inl keep)))
                rwa [glue_degree_pieceInternal] at transferred)
              (by
                have transferred := sourceBaseline.trans
                  ((glue piece outside).minDegree_le_degree (.inr (.inl remove)))
                rwa [glue_degree_pieceInternal] at transferred)
              (by
                have transferred := sourceBaseline.trans
                  ((glue piece outside).minDegree_le_degree (.inr (.inl x)))
                rwa [glue_degree_pieceInternal] at transferred)
              uniqueKR uniqueKX uniqueRX
          · have notFoldedTwo : (Sum.inr pieceInternal :
                boundary.Vertex ⊕ P2.Internal) ≠ P1.foldedKeep m x' second := by
              simp [BoundaryPiece.foldedKeep, folded]
            have valNeX : pieceInternal.1.1 ≠ x := by
              intro equal
              exact pieceInternal.2 (Subtype.ext equal)
            have notFoldedOne : (Sum.inr pieceInternal.1 :
                boundary.Vertex ⊕ P1.Internal) ≠
                piece.foldedKeep keep remove keepRemove := by
              intro equal
              exact folded (Subtype.ext (Sum.inr.inj equal))
            have notCommonOne : ¬ (piece.graph.Adj (.inr keep)
                  (piece.foldDecode remove (Sum.inr pieceInternal.1)) ∧
                piece.graph.Adj (.inr remove)
                  (piece.foldDecode remove (Sum.inr pieceInternal.1))) := by
              rintro ⟨keepAdj, removeAdj⟩
              exact valNeX (Sum.inr.inj (uniqueKR _ keepAdj removeAdj))
            have step := piece.degree_identifyInternal_of_not_common keep remove
              keepRemove (Sum.inr pieceInternal.1) notFoldedOne notCommonOne
            have chain : P2.pack.degree (Sum.inr pieceInternal) =
                piece.pack.degree (Sum.inr pieceInternal.1.1) :=
              Eq.trans (P1.degree_identifyInternal_of_not_common m x' second
                (.inr pieceInternal) notFoldedTwo (noCommonSecond _)) step
            have transferred := sourceBaseline.trans
              ((glue piece outside).minDegree_le_degree
                (.inr (.inl pieceInternal.1.1)))
            rw [glue_degree_pieceInternal] at transferred
            exact le_of_le_of_eq transferred chain.symm
      | inr contextInternal =>
          rw [glue_degree_contextInternal]
          have transferred := sourceBaseline.trans
            ((glue piece outside).minDegree_le_degree (.inr (.inr contextInternal)))
          rwa [glue_degree_contextInternal] at transferred

end Hypostructure.Graph
