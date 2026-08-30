import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Hypostructure.Graph.Finite
import Hypostructure.Graph.Induced
import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.SubcubicReach

/-!
# Finite rooted-type coordinate repetition

The low-entropy arm of `prop:two-budget` makes a second, genuinely structural
decision: whether the radius-two rooted-type coordinate is repetitive.  The
paper proves dominance by relabelling one realized type vector and applying the
multinomial lower bound.  This file packages the exact finite core of that
argument without logarithms or an asymptotic side channel.

For a finite coordinate vector `code : Vertex → Code`, `coordinateOrbit` is
the set of all vectors obtained by relabelling its vertex positions.  The
number `nonDominantOrbitFloor error` is the least orbit size among coordinate
vectors for which every type fibre misses more than `error` vertices.  Thus an
orbit smaller than that floor has a fibre covering all but `error` vertices.
The definition is deliberately independent of graphs; a graph node supplies
its literal rooted-ball type code and its registered finite `o(n)` allowance.
-/

namespace Hypostructure.Graph.RootedLocalType

open Finset

universe u v

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
variable {Code : Type v} [Fintype Code] [DecidableEq Code]

/-- All coordinate vectors obtained by permuting the labelled vertex slots. -/
def coordinateOrbit (code : Vertex → Code) : Finset (Vertex → Code) :=
  Finset.univ.image fun relabel : Equiv.Perm Vertex =>
    fun vertex => code (relabel.symm vertex)

/-- The vertices carrying the same coordinate value as `root`. -/
def typeFibre (code : Vertex → Code) (root : Vertex) : Finset Vertex :=
  Finset.univ.filter fun vertex => code vertex = code root

/-- No coordinate value covers all but `error` vertices. -/
def NoDominantFibre (code : Vertex → Code) (error : Nat) : Prop :=
  ∀ root, (typeFibre code root).card + error < Fintype.card Vertex

/-- Orbit sizes of all coordinate vectors without an `error`-dominant fibre. -/
noncomputable def nonDominantOrbitCounts (error : Nat) : Finset Nat := by
  classical
  exact
    (Finset.univ.filter fun code : Vertex → Code => NoDominantFibre code error).image
      fun code => (coordinateOrbit code).card

/-- The exact finite relabelling threshold.  The inserted sentinel makes the
minimum total even when no non-dominant vector exists; every coordinate orbit
has size at most the number of vertex permutations, so the sentinel lies
strictly above every possible orbit. -/
noncomputable def nonDominantOrbitFloor (error : Nat) : Nat := by
  classical
  exact
    (insert (Fintype.card (Equiv.Perm Vertex) + 1)
      (nonDominantOrbitCounts (Vertex := Vertex) (Code := Code) error)).min'
        (Finset.insert_nonempty _ _)

/-- The exact finite form of the paper's structurally repetitive coordinate:
its relabelling orbit is smaller than the least orbit forced by absence of an
`error`-dominant type. -/
noncomputable def StructurallyRepetitive (code : Vertex → Code) (error : Nat) : Prop :=
  (coordinateOrbit code).card <
    nonDominantOrbitFloor (Vertex := Vertex) (Code := Code) error

/-- The relabelling/multinomial step of `lem:dominant-type`, in exact finite
form.  No dominance witness occurs in the hypothesis. -/
theorem exists_dominant_of_structurallyRepetitive
    (code : Vertex → Code) (error : Nat)
    (repetitive : StructurallyRepetitive code error) :
    ∃ root, Fintype.card Vertex ≤ (typeFibre code root).card + error := by
  classical
  by_contra absent
  push Not at absent
  have noDominant : NoDominantFibre code error := by
    intro root
    exact absent root
  have orbitMem : (coordinateOrbit code).card ∈
      nonDominantOrbitCounts (Vertex := Vertex) (Code := Code) error := by
    rw [nonDominantOrbitCounts, Finset.mem_image]
    exact ⟨code, Finset.mem_filter.mpr ⟨Finset.mem_univ _, noDominant⟩, rfl⟩
  have floorLe :
      nonDominantOrbitFloor (Vertex := Vertex) (Code := Code) error ≤
        (coordinateOrbit code).card := by
    apply Finset.min'_le
    exact Finset.mem_insert_of_mem orbitMem
  exact (Nat.not_lt_of_ge floorLe) repetitive

end Hypostructure.Graph.RootedLocalType

namespace Hypostructure.Graph

universe w

namespace FiniteObject

/-- The radius-`r` ball inside a declared subcubic support.  `SubcubicReach`
uses only paths whose interior remains in the support, and the final
intersection keeps the endpoint there as well. -/
noncomputable def rootedLocalBall (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat)
    (centre : {vertex // vertex ∈ support}) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact SubcubicReach.reach object.graph support centre.1 radius centre.1 ∩ support

theorem mem_rootedLocalBall_centre (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat)
    (centre : {vertex // vertex ∈ support}) :
    centre.1 ∈ object.rootedLocalBall support radius centre := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [rootedLocalBall]
  exact Finset.mem_inter.mpr
    ⟨SubcubicReach.self_mem_reach object.graph support centre.1 radius centre.1,
      centre.2⟩

/-- Two support vertices carry the same rooted radius-`r` type. -/
def RootedLocalBallIso (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat)
    (left right : {vertex // vertex ∈ support}) : Prop :=
  ∃ iso :
      (object.induce (object.rootedLocalBall support radius left)).graph ≃g
        (object.induce (object.rootedLocalBall support radius right)).graph,
    (iso ⟨left.1, object.mem_rootedLocalBall_centre support radius left⟩).1 =
      right.1

theorem rootedLocalBallIso_refl (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat)
    (centre : {vertex // vertex ∈ support}) :
    object.RootedLocalBallIso support radius centre centre := by
  refine ⟨SimpleGraph.Iso.refl, ?_⟩
  rfl

/-- The rooted radius-two type records whether its centre supports one of the
manuscript's internal wedges.  This is the local predicate transported in
`lem:translates-independent`; it is not a separately supplied witness. -/
def RootedInternalWedgeClause (object : FiniteObject.{w})
    (support : Finset object.Vertex) (centre : object.Vertex) : Prop :=
  ∃ wedge : object.InternalWedge support,
    wedge.1 = centre ∧ wedge ∈ object.internalWedgeFamily support

/-- Regard an internal wedge of a smaller support as the identical raw wedge
of a larger support. -/
noncomputable def internalWedgeOfSubset (object : FiniteObject.{w})
    {small large : Finset object.Vertex} (subset : small ⊆ large) :
    object.InternalWedge small → object.InternalWedge large := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro wedge
  refine ⟨wedge.1, ⟨wedge.2.1, ?_⟩⟩
  have source := Finset.mem_powersetCard.mp wedge.2.2
  rw [Finset.mem_powersetCard]
  refine ⟨?_, source.2⟩
  intro vertex member
  have smallNeighbour := source.1 member
  have split : vertex ∈ object.graph.neighborFinset wedge.1 ∧
      vertex ∈ small := by
    simpa only [internalNeighborFinset, Finset.mem_inter] using smallNeighbour
  simpa only [internalNeighborFinset, Finset.mem_inter] using
    And.intro split.1 (subset split.2)

/-- The support inclusion above sends members of the smaller raw-wedge family
to members of the larger one. -/
theorem internalWedgeOfSubset_mem_family (object : FiniteObject.{w})
    {small large : Finset object.Vertex} (subset : small ⊆ large)
    (wedge : object.InternalWedge small)
    (member : wedge ∈ object.internalWedgeFamily small) :
    object.internalWedgeOfSubset subset wedge ∈
      object.internalWedgeFamily large := by
  classical
  unfold internalWedgeFamily at member ⊢
  rw [Finset.mem_sigma] at member ⊢
  constructor
  · simpa [internalWedgeOfSubset] using subset member.1
  · exact Finset.mem_attach _ _

/-- A finite, equality-testable code for the rooted type.  The Boolean row is
the vertex's equivalence row under rooted-ball isomorphism, and the final bit
is the root-wedge coordinate used at node `[51]`.  Thus equality of this code
retains exactly the local information used by both `lem:dominant-type` and
`lem:translates-independent`, without choosing arbitrary names for isomorphism
classes. -/
noncomputable def rootedLocalTypeCode (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat) :
    {vertex // vertex ∈ support} →
      (({vertex // vertex ∈ support} → Bool) × Bool) := by
  classical
  exact fun centre =>
    (⟨fun other => decide (object.RootedLocalBallIso support radius centre other),
      decide (object.RootedInternalWedgeClause support centre.1)⟩)

/-- Equality of the canonical codes supplies the rooted-ball isomorphism used
by `lem:dominant-type`. -/
theorem rootedLocalBallIso_of_code_eq (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat)
    (left right : {vertex // vertex ∈ support})
    (equal : object.rootedLocalTypeCode support radius left =
      object.rootedLocalTypeCode support radius right) :
    object.RootedLocalBallIso support radius left right := by
  classical
  have atRight := congrFun (congrArg Prod.fst equal) right
  change decide (object.RootedLocalBallIso support radius left right) =
    decide (object.RootedLocalBallIso support radius right right) at atRight
  have rightTrue :
      decide (object.RootedLocalBallIso support radius right right) = true :=
    decide_eq_true (object.rootedLocalBallIso_refl support radius right)
  rw [rightTrue] at atRight
  exact of_decide_eq_true atRight

/-- Equality of the canonical rooted type transports the root-wedge
coordinate.  This is the precise local-type step used to obtain one translated
wedge at every centre of the dominant fibre. -/
theorem rootedInternalWedgeClause_of_code_eq (object : FiniteObject.{w})
    (support : Finset object.Vertex) (radius : Nat)
    (left right : {vertex // vertex ∈ support})
    (equal : object.rootedLocalTypeCode support radius left =
      object.rootedLocalTypeCode support radius right)
    (leftWedge : object.RootedInternalWedgeClause support left.1) :
    object.RootedInternalWedgeClause support right.1 := by
  classical
  have atWedge := congrArg Prod.snd equal
  change decide (object.RootedInternalWedgeClause support left.1) =
    decide (object.RootedInternalWedgeClause support right.1) at atWedge
  rw [decide_eq_true leftWedge] at atWedge
  exact of_decide_eq_true atWedge.symm

end FiniteObject

end Hypostructure.Graph
