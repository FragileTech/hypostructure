import Hypostructure.Graph.WindowAttachmentRealization

/-!
# The separated multi-scale package, realized

`lem:p13-window-package` builds its coordinate family in two steps, and the
second is a *selection*:

> The multi-scale package uses `⌊log₂ n⌋ − O(1)` separated dyadic scales for
> these finite barriers.  The `O(1)` loss absorbs endpoint collisions with the
> finitely many reserved boundary and tie-breaking choices inside the canonical
> packing.

So separation is not something the lemma proves about every scale — it is what
the surviving scales *are*, the colliding ones having been discarded into the
`O(1)`.  Independence then follows exactly as it does across windows: the
manuscript's own reason, "the tester for one window does not change the label
state assigned to another packed window", is that the coordinates read disjoint
parts of the object.

This module is that step, generically.  It takes the separation of the selected
coordinates as the hypothesis it is in the manuscript, and returns the product
the entropy cap consumes.  A caller that cannot separate its coordinates does
not get the product — which is correct, and is why the surrounding node is a
branch.

Nothing here fixes a scale count, a rate, a window order, or a baseline.  The
index of the coordinate family is an arbitrary finite type, so "one coordinate
per packed window per selected scale" is one instance of it and no scale
arithmetic occurs.
-/

namespace Hypostructure.Graph.PackedWindowRealization

open Hypostructure

universe u

variable {object : FiniteObject.{u}} {order : Nat}

/-! ## Separated coordinates -/

/-- **A separated coordinate family.**

`slot` is where each coordinate reads: for coordinate `c`, the vertex it attaches
from and the set of vertices it may attach to.  `separated` is the manuscript's
selection — distinct coordinates read disjoint targets — and `outside` is that
the attaching vertex is not itself one of them.

The manuscript's instance is one coordinate per packed window per selected dyadic
scale, with `reads` the window's own support; the `O(1)` scales whose completions
collide are simply not in `Coordinate`. -/
structure SeparatedFamily (object : FiniteObject.{u}) (Coordinate : Type) where
  /-- The vertex each coordinate attaches from. -/
  source : Coordinate → object.Vertex
  /-- The vertices each coordinate may attach to. -/
  reads : Coordinate → Finset object.Vertex
  /-- **Separation.**  Distinct coordinates read disjoint vertex sets, so setting
  one leaves every other coordinate's reading fixed. -/
  separated : ∀ left right : Coordinate, left ≠ right →
    Disjoint (reads left) (reads right)
  /-- **The testers are rooted outside the package.**  No coordinate's attaching
  vertex is read by any coordinate — the manuscript's outside completions are
  rooted outside the packed windows.  Taking it at every pair, not just the
  diagonal, is what stops one coordinate's root being mistaken for another
  coordinate's target. -/
  sourcesOutside : ∀ coordinate other : Coordinate,
    source coordinate ∉ reads other

namespace SeparatedFamily

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

/-- The state of one coordinate: which of the vertices it reads it attaches to.
This is the manuscript's attachment label of that coordinate's tester. -/
abbrev State (family : SeparatedFamily object Coordinate)
    (coordinate : Coordinate) :=
  {selected : Finset object.Vertex // selected ⊆ family.reads coordinate}

/-- The edge set a joint assignment prescribes. -/
noncomputable def edges (family : SeparatedFamily object Coordinate)
    (assign : ∀ coordinate, family.State coordinate) :
    Set (Sym2 (Fin object.vertexCount)) :=
  {edge | ∃ (coordinate : Coordinate) (target : object.Vertex),
    target ∈ (assign coordinate).1 ∧
      edge = s(vertexLabel object (family.source coordinate),
        vertexLabel object target)}

/-- **The realization.**  One labelled graph per joint assignment. -/
noncomputable def realize (family : SeparatedFamily object Coordinate)
    (assign : ∀ coordinate, family.State coordinate) :
    LabelledOn object.vertexCount :=
  ⟨SimpleGraph.fromEdgeSet (family.edges assign)⟩

/-- **The reading of the realization**, coordinate by coordinate.

Separation is exactly what makes this work: an edge into a vertex that
coordinate `c` reads cannot have come from any other coordinate, because no other
coordinate reads that vertex.  This is the manuscript's "the tester for one
window does not change the label state assigned to another packed window", at the
selected coordinates. -/
theorem adj_realize_iff (family : SeparatedFamily object Coordinate)
    (assign : ∀ coordinate, family.State coordinate)
    (coordinate : Coordinate) {target : object.Vertex}
    (readable : target ∈ family.reads coordinate) :
    (family.realize assign).graph.Adj
        (vertexLabel object (family.source coordinate))
        (vertexLabel object target) ↔ target ∈ (assign coordinate).1 := by
  classical
  constructor
  · intro adjacent
    rw [realize, SimpleGraph.fromEdgeSet_adj] at adjacent
    obtain ⟨⟨other, otherTarget, assigned, edgeEq⟩, _distinct⟩ := adjacent
    have otherReads : otherTarget ∈ family.reads other := (assign other).2 assigned
    rw [Sym2.eq_iff] at edgeEq
    rcases edgeEq with ⟨_sourceEq, targetEq⟩ | ⟨crossOne, _crossTwo⟩
    · -- Same orientation.  Separation names the coordinate.
      have targets : target = otherTarget :=
        (vertexLabel object).injective targetEq
      have sameCoordinate : other = coordinate := by
        by_contra different
        exact (Finset.disjoint_left.mp
          (family.separated other coordinate different) otherReads)
          (targets ▸ readable)
      subst sameCoordinate
      exact targets ▸ assigned
    · -- Crossed orientation: this coordinate's root would be another
      -- coordinate's target, which `sourcesOutside` forbids.
      have rootIsTarget : family.source coordinate = otherTarget :=
        (vertexLabel object).injective crossOne
      exact absurd (rootIsTarget ▸ otherReads)
        (family.sourcesOutside coordinate other)
  · intro assigned
    rw [realize, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨coordinate, target, assigned, rfl⟩, ?_⟩
    intro same
    have rootIsTarget : family.source coordinate = target :=
      (vertexLabel object).injective same
    exact family.sourcesOutside coordinate coordinate (rootIsTarget ▸ readable)

/-- **The realization is injective.**  Two joint assignments differing at any
single coordinate differ as labelled graphs. -/
theorem realize_injective (family : SeparatedFamily object Coordinate) :
    Function.Injective family.realize := by
  classical
  intro left right same
  funext coordinate
  refine Subtype.ext (Finset.ext fun target => ?_)
  by_cases readable : target ∈ family.reads coordinate
  · rw [← adj_realize_iff family left coordinate readable,
      ← adj_realize_iff family right coordinate readable, same]
  · constructor
    · intro member; exact absurd ((left coordinate).2 member) readable
    · intro member; exact absurd ((right coordinate).2 member) readable

/-- **`lem:independent-target-entropy` at a separated family, with every
antecedent discharged.**

The joint state count of the selected coordinates is realized inside the ambient
labelled class.  This is the product the manuscript takes across windows and
across the selected scales, and the only input is the separation the selection
supplies. -/
theorem demand_le_card_labelled (family : SeparatedFamily object Coordinate) :
    Nat.card (∀ coordinate, family.State coordinate) ≤
      Nat.card (LabelledOn object.vertexCount) :=
  Nat.card_le_card_of_injective _ (realize_injective family)

/-- The joint state count is the product of the per-coordinate counts, so the
manuscript's per-coordinate rates add under `log₂`. -/
theorem card_state_pi (family : SeparatedFamily object Coordinate) :
    Nat.card (∀ coordinate, family.State coordinate) =
      ∏ coordinate, Nat.card (family.State coordinate) := by
  letI : FinEnum object.Vertex := object.vertices
  haveI : Finite object.Vertex := Finite.of_equiv _ (FinEnum.equiv (α := object.Vertex)).symm
  haveI : ∀ coordinate : Coordinate, Finite (family.State coordinate) :=
    fun _ => Subtype.finite
  exact Core.FiniteEntropy.card_pi_eq_prod_card _

/-- **The rate form the entropy cap consumes.**  If every selected coordinate
carries at least `2 ^ rate` states, the family realizes at least
`2 ^ (rate · #coordinates)` of them inside the ambient labelled class.

At the manuscript's instance `#coordinates` is one per packed window per selected
scale and `rate` is the audited `c₁₃`, so this is
`2 ^ (c₁₃ · (selected scales) · p) ≤ |𝒢|` — `lem:p13-window-package`'s displayed
bound, with no rate constant named here. -/
theorem two_pow_rate_mul_card_le_card_labelled
    (family : SeparatedFamily object Coordinate) (rate : Nat)
    (local_rate : ∀ coordinate, 2 ^ rate ≤ Nat.card (family.State coordinate)) :
    2 ^ (rate * Fintype.card Coordinate) ≤
      Nat.card (LabelledOn object.vertexCount) := by
  classical
  refine le_trans ?_ (demand_le_card_labelled family)
  rw [card_state_pi family, pow_mul]
  calc (2 ^ rate) ^ Fintype.card Coordinate
      = ∏ _coordinate : Coordinate, 2 ^ rate := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ coordinate, Nat.card (family.State coordinate) :=
        Finset.prod_le_prod' fun coordinate _ => local_rate coordinate

end SeparatedFamily

end Hypostructure.Graph.PackedWindowRealization
