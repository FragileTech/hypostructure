import Hypostructure.Graph.SeparatedPackageRealization

/-!
# The separated package against the fixed-edge-count skeleton class

`lem:skeleton-dominates` is stated at `𝒢_{n,m}`, the labelled graphs on `[n]`
with *exactly* `m` edges, and gives `|𝒢_{n,m}| = C(C(n,2), m)`.
`SeparatedPackageRealization` caps the package's joint state count by `|𝒢_n|`;
this module refines that to `|𝒢_{n,m}|`, which is what every entropy comparison
in the manuscript actually compares against.

The refinement is the manuscript's own reading of `lem:skeleton-dominates`: the
auxiliary structure supplies no degree of freedom beyond the adjacency matrix, so
a realized package may be completed to the ambient edge count in a way that is a
function of the package alone.  Concretely, the coordinates occupy their own
slots, and the completion is drawn from a reserved pool disjoint from them; the
package is recovered by intersecting with the slots, so the completion never has
to be injective and only the coordinates carry information.

Every quantity is derived: the ambient edge count is a parameter, the slots and
the pool are read off the family, and the completion size is the difference.  No
numeral occurs.
-/

namespace Hypostructure.Graph.PackedWindowRealization

open Hypostructure

universe u

variable {object : FiniteObject.{u}} {order : Nat}

namespace SeparatedFamily

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

/-- The slots the coordinates of the package occupy: one unordered pair per
coordinate root and readable target. -/
noncomputable def slots (family : SeparatedFamily object Coordinate) :
    Finset (Sym2 (Fin object.vertexCount)) := by
  classical
  exact Finset.univ.filter fun edge =>
    ∃ (coordinate : Coordinate) (target : object.Vertex),
      target ∈ family.reads coordinate ∧
        edge = s(vertexLabel object (family.source coordinate),
          vertexLabel object target)

/-- The slots one joint assignment actually fills. -/
noncomputable def filled (family : SeparatedFamily object Coordinate)
    (assign : ∀ coordinate, family.State coordinate) :
    Finset (Sym2 (Fin object.vertexCount)) := by
  classical
  exact Finset.univ.filter fun edge =>
    ∃ (coordinate : Coordinate) (target : object.Vertex),
      target ∈ (assign coordinate).1 ∧
        edge = s(vertexLabel object (family.source coordinate),
          vertexLabel object target)

theorem filled_subset_slots (family : SeparatedFamily object Coordinate)
    (assign : ∀ coordinate, family.State coordinate) :
    family.filled assign ⊆ family.slots := by
  classical
  intro edge member
  rw [filled, Finset.mem_filter] at member
  obtain ⟨_universal, coordinate, target, assigned, edgeEq⟩ := member
  rw [slots, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    coordinate, target, (assign coordinate).2 assigned, edgeEq⟩

/-- No coordinate slot is a loop: a coordinate's root is not one of its
targets. -/
theorem not_isDiag_of_mem_slots (family : SeparatedFamily object Coordinate)
    {edge : Sym2 (Fin object.vertexCount)} (member : edge ∈ family.slots) :
    ¬ edge.IsDiag := by
  classical
  rw [slots, Finset.mem_filter] at member
  obtain ⟨_universal, coordinate, target, readable, edgeEq⟩ := member
  subst edgeEq
  rw [Sym2.mk_isDiag_iff]
  intro same
  exact family.sourcesOutside coordinate coordinate
    (((vertexLabel object).injective same) ▸ readable)

/-- The reserved pool: the non-loop slots the coordinates do not occupy. -/
noncomputable def pool (family : SeparatedFamily object Coordinate) :
    Finset (Sym2 (Fin object.vertexCount)) := by
  classical
  exact (Finset.univ.filter fun edge => ¬ edge.IsDiag) \ family.slots

theorem pool_disjoint_slots (family : SeparatedFamily object Coordinate) :
    Disjoint family.pool family.slots := by
  classical
  rw [pool]
  exact Finset.sdiff_disjoint

theorem not_isDiag_of_mem_pool (family : SeparatedFamily object Coordinate)
    {edge : Sym2 (Fin object.vertexCount)} (member : edge ∈ family.pool) :
    ¬ edge.IsDiag := by
  classical
  rw [pool, Finset.mem_sdiff, Finset.mem_filter] at member
  exact member.1.2

/-- The completion of a package to the ambient edge count, drawn from the
reserved pool.  It depends only on how many edges are still needed, so it is a
function of the package and carries no information of its own. -/
noncomputable def completion (family : SeparatedFamily object Coordinate)
    (needed : Nat) : Finset (Sym2 (Fin object.vertexCount)) := by
  classical
  exact if room : needed ≤ family.pool.card then
    (Finset.exists_subset_card_eq room).choose
  else ∅

theorem completion_subset (family : SeparatedFamily object Coordinate)
    {needed : Nat} (room : needed ≤ family.pool.card) :
    family.completion needed ⊆ family.pool := by
  classical
  rw [completion, dif_pos room]
  exact (Finset.exists_subset_card_eq room).choose_spec.1

theorem completion_card (family : SeparatedFamily object Coordinate)
    {needed : Nat} (room : needed ≤ family.pool.card) :
    (family.completion needed).card = needed := by
  classical
  rw [completion, dif_pos room]
  exact (Finset.exists_subset_card_eq room).choose_spec.2

/-- **The realization at the fixed ambient edge count.**  The package's own
slots, completed from the reserved pool. -/
noncomputable def realizeAt (family : SeparatedFamily object Coordinate)
    (edgeCount : Nat) (assign : ∀ coordinate, family.State coordinate) :
    LabelledOn object.vertexCount := by
  classical
  exact ⟨SimpleGraph.fromEdgeSet
    ↑(family.filled assign ∪
      family.completion (edgeCount - (family.filled assign).card))⟩

/-- The package is recovered by intersecting the realized edge set with the
coordinate slots: the completion lies in the pool, which is disjoint from them.
This is why the completion never has to be injective. -/
theorem filled_eq_inter (family : SeparatedFamily object Coordinate)
    (edgeCount : Nat) (assign : ∀ coordinate, family.State coordinate)
    (room : edgeCount - (family.filled assign).card ≤ family.pool.card) :
    (family.filled assign ∪
        family.completion (edgeCount - (family.filled assign).card)) ∩
        family.slots = family.filled assign := by
  classical
  rw [Finset.union_inter_distrib_right]
  have first : family.filled assign ∩ family.slots = family.filled assign :=
    Finset.inter_eq_left.mpr (family.filled_subset_slots assign)
  have second :
      family.completion (edgeCount - (family.filled assign).card) ∩
        family.slots = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun edge member => ?_
    rw [Finset.mem_inter] at member
    exact (Finset.disjoint_left.mp family.pool_disjoint_slots
      (family.completion_subset room member.1)) member.2
  rw [first, second, Finset.union_empty]

/-- The reading of a filled slot, at the `Finset` level.  Separation is what
names the coordinate; `sourcesOutside` is what rules out the crossed
orientation. -/
theorem mem_filled_iff (family : SeparatedFamily object Coordinate)
    (assign : ∀ coordinate, family.State coordinate)
    (coordinate : Coordinate) {target : object.Vertex}
    (readable : target ∈ family.reads coordinate) :
    s(vertexLabel object (family.source coordinate),
        vertexLabel object target) ∈ family.filled assign ↔
      target ∈ (assign coordinate).1 := by
  classical
  constructor
  · intro member
    rw [filled, Finset.mem_filter] at member
    obtain ⟨_universal, other, otherTarget, assigned, edgeEq⟩ := member
    have otherReads : otherTarget ∈ family.reads other := (assign other).2 assigned
    rw [Sym2.eq_iff] at edgeEq
    rcases edgeEq with ⟨_sourceEq, targetEq⟩ | ⟨crossOne, _crossTwo⟩
    · have targets : target = otherTarget :=
        (vertexLabel object).injective targetEq
      have sameCoordinate : other = coordinate := by
        by_contra different
        exact (Finset.disjoint_left.mp
          (family.separated other coordinate different) otherReads)
          (targets ▸ readable)
      subst sameCoordinate
      exact targets ▸ assigned
    · have rootIsTarget : family.source coordinate = otherTarget :=
        (vertexLabel object).injective crossOne
      exact absurd (rootIsTarget ▸ otherReads)
        (family.sourcesOutside coordinate other)
  · intro assigned
    rw [filled, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, coordinate, target, assigned, rfl⟩

/-- The filled slots determine the assignment. -/
theorem assign_eq_of_filled_eq (family : SeparatedFamily object Coordinate)
    {left right : ∀ coordinate, family.State coordinate}
    (same : family.filled left = family.filled right) : left = right := by
  classical
  funext coordinate
  refine Subtype.ext (Finset.ext fun target => ?_)
  by_cases readable : target ∈ family.reads coordinate
  · rw [← mem_filled_iff family left coordinate readable,
      ← mem_filled_iff family right coordinate readable, same]
  · constructor
    · intro member; exact absurd ((left coordinate).2 member) readable
    · intro member; exact absurd ((right coordinate).2 member) readable

/-- The realized edge set has no loop, so `fromEdgeSet` retains all of it. -/
theorem edgeSet_realizeAt (family : SeparatedFamily object Coordinate)
    (edgeCount : Nat) (assign : ∀ coordinate, family.State coordinate)
    (room : edgeCount - (family.filled assign).card ≤ family.pool.card) :
    (family.realizeAt edgeCount assign).graph.edgeSet =
      ↑(family.filled assign ∪
        family.completion (edgeCount - (family.filled assign).card)) := by
  classical
  rw [realizeAt, SimpleGraph.edgeSet_fromEdgeSet]
  refine Set.ext fun edge => ⟨fun member => member.1, fun member => ⟨member, ?_⟩⟩
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at member
  rcases member with filledMember | completionMember
  · exact family.not_isDiag_of_mem_slots
      (family.filled_subset_slots assign filledMember)
  · exact family.not_isDiag_of_mem_pool
      (family.completion_subset room completionMember)

/-- **`lem:skeleton-dominates` at the separated package.**

The package's joint state count is realized inside the labelled graphs on the
object's own order with exactly the ambient edge count, so it is bounded by
`C(C(n,2), m)` — the manuscript's `|𝒢_{n,m}|`.

The two side conditions are the counting conditions and nothing more: the
coordinate slots fit inside the ambient edge count, and the reserved pool is at
least that large. -/
theorem card_state_pi_le_skeletonBudget
    (family : SeparatedFamily object Coordinate) (edgeCount : Nat)
    (slotsFit : family.slots.card ≤ edgeCount)
    (poolRoom : edgeCount ≤ family.pool.card) :
    Nat.card (∀ coordinate, family.State coordinate) ≤
      (object.vertexCount.choose 2).choose edgeCount := by
  classical
  have filledFit : ∀ assign : ∀ coordinate, family.State coordinate,
      (family.filled assign).card ≤ edgeCount :=
    fun assign => le_trans
      (Finset.card_le_card (family.filled_subset_slots assign)) slotsFit
  have room : ∀ assign : ∀ coordinate, family.State coordinate,
      edgeCount - (family.filled assign).card ≤ family.pool.card :=
    fun assign => le_trans (Nat.sub_le _ _) poolRoom
  -- Every realization lands in the fixed-edge-count class.
  have counted : ∀ assign : ∀ coordinate, family.State coordinate,
      Nat.card (family.realizeAt edgeCount assign).graph.edgeSet = edgeCount := by
    intro assign
    have disjointParts :
        Disjoint (family.filled assign)
          (family.completion (edgeCount - (family.filled assign).card)) :=
      Finset.disjoint_of_subset_left (family.filled_subset_slots assign)
        (Finset.disjoint_of_subset_right
          (family.completion_subset (room assign))
          (Disjoint.symm family.pool_disjoint_slots))
    rw [family.edgeSet_realizeAt edgeCount assign (room assign)]
    simp only [Finset.coe_sort_coe, Nat.card_eq_finsetCard]
    rw [Finset.card_union_of_disjoint disjointParts,
      family.completion_card (room assign)]
    have fits := filledFit assign
    omega
  refine le_trans (Nat.card_le_card_of_injective
    (fun assign => (⟨family.realizeAt edgeCount assign, counted assign⟩ :
      Skeleton object.vertexCount edgeCount)) ?_)
    (le_of_eq (card_skeleton object.vertexCount edgeCount))
  intro left right same
  have graphs : family.realizeAt edgeCount left = family.realizeAt edgeCount right :=
    congrArg Subtype.val same
  have edges :
      family.filled left ∪
          family.completion (edgeCount - (family.filled left).card) =
        family.filled right ∪
          family.completion (edgeCount - (family.filled right).card) := by
    have leftSet := family.edgeSet_realizeAt edgeCount left (room left)
    have rightSet := family.edgeSet_realizeAt edgeCount right (room right)
    rw [graphs, rightSet] at leftSet
    exact Finset.coe_injective leftSet.symm
  refine family.assign_eq_of_filled_eq ?_
  rw [← family.filled_eq_inter edgeCount left (room left),
    ← family.filled_eq_inter edgeCount right (room right), edges]

/-- **`lem:p13-window-package` against the manuscript's own budget.**

If every selected coordinate carries at least `2 ^ rate` states, the package
realizes at least `2 ^ (rate · #coordinates)` labelled skeletons of the ambient
edge count.  At the manuscript's instance `#coordinates` is one per packed window
per selected scale and `rate` is the audited `c₁₃`, so this is
`2 ^ (c₁₃ · scales · p) ≤ C(C(n,2), m)` — the comparison the entropy cap makes.
No rate constant, scale count, or numeral is named here. -/
theorem two_pow_rate_mul_card_le_skeletonBudget
    (family : SeparatedFamily object Coordinate) (edgeCount rate : Nat)
    (local_rate : ∀ coordinate, 2 ^ rate ≤ Nat.card (family.State coordinate))
    (slotsFit : family.slots.card ≤ edgeCount)
    (poolRoom : edgeCount ≤ family.pool.card) :
    2 ^ (rate * Fintype.card Coordinate) ≤
      (object.vertexCount.choose 2).choose edgeCount := by
  classical
  refine le_trans ?_
    (family.card_state_pi_le_skeletonBudget edgeCount slotsFit poolRoom)
  rw [family.card_state_pi, pow_mul]
  calc (2 ^ rate) ^ Fintype.card Coordinate
      = ∏ _coordinate : Coordinate, 2 ^ rate := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ coordinate, Nat.card (family.State coordinate) :=
        Finset.prod_le_prod' fun coordinate _ => local_rate coordinate

end SeparatedFamily

end Hypostructure.Graph.PackedWindowRealization
