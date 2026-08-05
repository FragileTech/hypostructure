import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.Induced

/-!
# Maximal packings of induced windows

The manuscript fixes `p₁₃` as "the maximum size of a vertex-disjoint family of
induced copies of `P₁₃` in `G`".  That is a *number read off the object*, in
the same sense as its vertex count, and this module defines it that way: as the
supremum of the cardinalities of the valid packings, over the finitely many
candidate families on the object's own vertex set.

Defining it this way is what lets a spine row commit the packing without
carrying it.  A row proves that the number is positive and that some family
attains it; every later row reads the number off the object again.  No family,
no schedule, and no selection travels between rows, which is exactly what the
canonical ledger's data-free fact values require.

Nothing here is specialized to one manuscript: the window order is a parameter.
-/

namespace Hypostructure.Graph

open Hypostructure

universe u

namespace FiniteObject

/-- A support carries an induced window of the given order when its induced
subgraph contains an induced path on that many vertices. -/
def InducesWindow (object : FiniteObject.{u}) (order : Nat)
    (support : Finset object.Vertex) : Prop :=
  HasInducedPath (object.induce support) order

/-- A window support is nonempty once the registered order is.

The containment supplies an embedding of the path's vertex type into the
induced subgraph's, and the path on a positive number of vertices has one. -/
theorem nonempty_of_inducesWindow (object : FiniteObject.{u}) {order : Nat}
    (positive : 0 < order) {support : Finset object.Vertex}
    (window : object.InducesWindow order support) : support.Nonempty := by
  obtain ⟨embedding⟩ := window
  exact ⟨(embedding ⟨0, positive⟩).1, (embedding ⟨0, positive⟩).2⟩

/-- A vertex-disjoint family of induced windows. -/
def IsWindowPacking (object : FiniteObject.{u}) (order : Nat)
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ support ∈ packing, object.InducesWindow order support) ∧
    ∀ left ∈ packing, ∀ right ∈ packing, left ≠ right → Disjoint left right

theorem isWindowPacking_empty (object : FiniteObject.{u}) (order : Nat) :
    object.IsWindowPacking order ∅ :=
  ⟨by simp, by simp⟩

/-- The finitely many valid packings on the object's own vertex set. -/
noncomputable def windowPackings (object : FiniteObject.{u}) (order : Nat) :
    Finset (Finset (Finset object.Vertex)) := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact Finset.univ.filter (object.IsWindowPacking order)

theorem mem_windowPackings (object : FiniteObject.{u}) (order : Nat)
    (packing : Finset (Finset object.Vertex)) :
    packing ∈ object.windowPackings order ↔
      object.IsWindowPacking order packing := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  simp [windowPackings]

theorem windowPackings_nonempty (object : FiniteObject.{u}) (order : Nat) :
    (object.windowPackings order).Nonempty :=
  ⟨∅, (object.mem_windowPackings order ∅).mpr
    (object.isWindowPacking_empty order)⟩

/-- **`p₁₃`.**  The maximum size of a vertex-disjoint family of induced windows
of the registered order.  It is a function of the object alone. -/
noncomputable def windowPackingNumber (object : FiniteObject.{u})
    (order : Nat) : Nat :=
  (object.windowPackings order).sup Finset.card

theorem card_le_windowPackingNumber (object : FiniteObject.{u}) {order : Nat}
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    packing.card ≤ object.windowPackingNumber order :=
  Finset.le_sup ((object.mem_windowPackings order packing).mpr valid)

/-- Some valid packing attains the packing number. -/
theorem exists_windowPacking_card_eq (object : FiniteObject.{u})
    (order : Nat) :
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking order packing ∧
        packing.card = object.windowPackingNumber order := by
  obtain ⟨packing, member, attains⟩ :=
    Finset.exists_mem_eq_sup (object.windowPackings order)
      (object.windowPackings_nonempty order) Finset.card
  exact ⟨packing, (object.mem_windowPackings order packing).mp member,
    attains.symm⟩

/-- **Maximality.**  A packing of maximum cardinality meets every window: an
unchosen window disjoint from all of its members could be added, and the
enlarged family would be a valid packing of strictly greater cardinality.

This is the manuscript's "every unchosen induced window overlaps a chosen
one", derived rather than assumed. -/
theorem exists_mem_not_disjoint_of_card_eq (object : FiniteObject.{u})
    {order : Nat} (positive : 0 < order)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (attains : packing.card = object.windowPackingNumber order)
    {support : Finset object.Vertex}
    (window : object.InducesWindow order support) :
    ∃ member ∈ packing, ¬ Disjoint support member := by
  classical
  by_contra missed
  push_neg at missed
  -- The unchosen window is not already a member: it is nonempty, so it is not
  -- disjoint from itself, while every member is disjoint from it.
  have fresh : support ∉ packing := fun member =>
    (Finset.not_disjoint_iff.mpr
      (by
        obtain ⟨vertex, inside⟩ :=
          object.nonempty_of_inducesWindow positive window
        exact ⟨vertex, inside, inside⟩))
      (missed support member)
  have enlarged : object.IsWindowPacking order (insert support packing) := by
    refine ⟨?_, ?_⟩
    · intro other member
      rcases Finset.mem_insert.mp member with rfl | member
      · exact window
      · exact valid.1 other member
    · intro left leftMember right rightMember distinct
      rcases Finset.mem_insert.mp leftMember with leftIsSupport | leftInPacking
      · rcases Finset.mem_insert.mp rightMember with rightIsSupport | rightInPacking
        · exact absurd (leftIsSupport.trans rightIsSupport.symm) distinct
        · exact leftIsSupport ▸ missed right rightInPacking
      · rcases Finset.mem_insert.mp rightMember with rightIsSupport | rightInPacking
        · exact rightIsSupport ▸ (missed left leftInPacking).symm
        · exact valid.2 left leftInPacking right rightInPacking distinct
  have larger : (insert support packing).card = packing.card + 1 :=
    Finset.card_insert_of_notMem fresh
  have bounded := object.card_le_windowPackingNumber enlarged
  omega

/-- **`cor:p13-exists`, in counted form.**  An object that carries some induced
window has a positive packing number. -/
theorem windowPackingNumber_pos (object : FiniteObject.{u}) {order : Nat}
    (positive : 0 < order) {support : Finset object.Vertex}
    (window : object.InducesWindow order support) :
    0 < object.windowPackingNumber order := by
  classical
  have valid : object.IsWindowPacking order {support} := by
    refine ⟨?_, ?_⟩
    · intro other member
      rw [Finset.mem_singleton.mp member]
      exact window
    · intro left leftMember right rightMember distinct
      rw [Finset.mem_singleton.mp leftMember,
        Finset.mem_singleton.mp rightMember] at distinct
      exact absurd rfl distinct
  have counted := object.card_le_windowPackingNumber valid
  rw [Finset.card_singleton] at counted
  exact counted

/-- An object with no induced window at all is window-free in the sense the
external closure law consumes. -/
theorem inducedPathFree_of_forall_not_inducesWindow (object : FiniteObject.{u})
    {order : Nat}
    (empty : ∀ support : Finset object.Vertex,
      ¬ object.InducesWindow order support) :
    InducedPathFree object order := by
  rintro ⟨embedding⟩
  letI : FinEnum object.Vertex := object.vertices
  classical
  refine empty (Finset.univ.image fun index : Fin order => embedding index) ?_
  refine ⟨⟨⟨fun index => ⟨embedding index, ?_⟩, ?_⟩, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
  · intro left right same
    exact embedding.injective (congrArg Subtype.val same)
  · intro left right
    exact embedding.map_adj_iff

end FiniteObject

end Hypostructure.Graph
