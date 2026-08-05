import Hypostructure.Graph.PackedWindowRealization

/-!
# Realizing a packed-window package by labelled skeletons

`Graph/PackedWindowRealization.lean` proves every entropy cap the manuscript
needs — `demand_le_card_labelled`, `demand_le_skeletonBudget`, `entropy_cap`,
`two_pow_le_card_labelled` — but each of them takes a *realization* as a
hypothesis: a map from the package's joint state into the labelled class, or a
canonical assignment out of it.  Until this module, nothing in the repository
supplied one, so the whole layer was a set of implications with no antecedent
and no call site.

This is the realization, at the attachment coordinates.

`lem:skeleton-dominates` requires the assignment to be *a function of the
labelled adjacency matrix once a deterministic tie-breaking rule is fixed*, and
`lem:p13-window-package` supplies the independence: "distinct packed windows are
vertex-disjoint, and the canonical assignment of a coordinate records the unique
packed window through which its tester is routed … the tester for one window does
not change the label state assigned to another packed window".

Both are honoured literally.  The coordinate of one window is the set of window
positions a fixed outside vertex attaches to — the manuscript's
`S(x) = {i : x vᵢ ∈ E(G)}` — the tie-breaking rule is the object's own vertex
enumeration, and independence across windows is `supports_pairwise_disjoint`:
the edge slots two distinct windows use are disjoint, so an assignment at one
window leaves every other window's reading untouched.

Nothing here is specialized to a manuscript: the window order, the packing, and
the outside vertex are all parameters, and no numeral occurs.
-/

namespace Hypostructure.Graph.PackedWindowRealization

open Hypostructure

universe u

variable {object : FiniteObject.{u}} {order : Nat}

/-! ## The tie-breaking rule -/

/-- **The object's own vertex enumeration**, as the relabelling
`lem:skeleton-dominates` states the labelled adjacency matrix against.  This is
the deterministic tie-breaking rule; nothing below depends on *which*
enumeration it is, only on its being a bijection. -/
noncomputable def vertexLabel (object : FiniteObject.{u}) :
    object.Vertex ≃ Fin object.vertexCount :=
  object.vertices.equiv

/-! ## The attachment coordinates -/

/-- **The coordinate of one packed window**: the set of window positions an
outside vertex attaches to.  The manuscript's `S(x)`.

It is a plain `Finset (Fin order)`, so the per-window state count is `2 ^ order`
and needs no legality hypothesis.  Legality is what cuts the count down to the
manuscript's `|Labels order|`; the *cap* direction proved here is only helped by
the larger carrier, so nothing is assumed about it. -/
abbrev AttachmentState (_object : FiniteObject.{u}) (order : Nat) : Type :=
  Finset (Fin order)

/-- The edge set a joint assignment prescribes: from the designated outside
vertex to exactly the window positions each window's own coordinate names. -/
noncomputable def attachmentEdges
    (profile : InducedPathMaximalPacking.Profile object order)
    (designated : object.Vertex)
    (assign : ∀ _window : PackedWindow profile, AttachmentState object order) :
    Set (Sym2 (Fin object.vertexCount)) :=
  {edge | ∃ (window : PackedWindow profile) (index : Fin order),
    index ∈ assign window ∧
      edge = s(vertexLabel object designated,
        vertexLabel object (window.1 index))}

/-- **The realization.**  The labelled graph on the object's own order whose only
edges are the attachments the joint assignment prescribes. -/
noncomputable def realizeAttachment
    (profile : InducedPathMaximalPacking.Profile object order)
    (designated : object.Vertex)
    (assign : ∀ _window : PackedWindow profile, AttachmentState object order) :
    LabelledOn object.vertexCount :=
  ⟨SimpleGraph.fromEdgeSet (attachmentEdges profile designated assign)⟩

/-- **The reading of the realization.**  The assignment is recovered from the
realized graph's adjacency, one window at a time.

This is where the two hypotheses do their work.  `outside` makes the attachment
a genuine edge rather than a loop, so `fromEdgeSet` retains it; and
`supports_pairwise_disjoint` is what stops a *different* window from having
produced the same edge — which is the manuscript's "the tester for one window
does not change the label state assigned to another packed window". -/
theorem adj_realizeAttachment_iff
    (profile : InducedPathMaximalPacking.Profile object order)
    (designated : object.Vertex)
    (outside : ∀ window : PackedWindow profile,
      designated ∉ support profile window)
    (assign : ∀ _window : PackedWindow profile, AttachmentState object order)
    (window : PackedWindow profile) (index : Fin order) :
    (realizeAttachment profile designated assign).graph.Adj
        (vertexLabel object designated)
        (vertexLabel object (window.1 index)) ↔ index ∈ assign window := by
  classical
  -- The designated vertex is not any window's vertex, so no attachment is a loop.
  have mem_support : ∀ (other : PackedWindow profile) (position : Fin order),
      other.1 position ∈ support profile other := by
    intro other position
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact Finset.mem_image.mpr ⟨position, Finset.mem_univ _, rfl⟩
  have designated_ne : ∀ (other : PackedWindow profile) (position : Fin order),
      designated ≠ other.1 position := by
    intro other position same
    exact outside other (same ▸ mem_support other position)
  constructor
  · intro adjacent
    rw [realizeAttachment, SimpleGraph.fromEdgeSet_adj] at adjacent
    obtain ⟨⟨other, position, assigned, edgeEq⟩, _distinct⟩ := adjacent
    -- The edge names its own window: `Sym2` equality plus disjoint supports.
    rw [Sym2.eq_iff] at edgeEq
    rcases edgeEq with ⟨designatedEq, vertexEq⟩ | ⟨crossOne, _crossTwo⟩
    · -- Same orientation: the window vertex is determined, hence the window.
      have vertices : window.1 index = other.1 position :=
        (vertexLabel object).injective vertexEq
      have sameWindow : window = other := by
        by_contra different
        have disjointSupports :=
          supports_pairwise_disjoint profile window other different
        exact (Finset.disjoint_left.mp disjointSupports
          (mem_support window index)) (vertices ▸ mem_support other position)
      subst sameWindow
      have positions : index = position := window.1.injective vertices
      subst positions
      exact assigned
    · -- Crossed orientation: the designated vertex would be a window vertex.
      exact absurd ((vertexLabel object).injective crossOne)
        (designated_ne other position)
  · intro assigned
    rw [realizeAttachment, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨window, index, assigned, rfl⟩, ?_⟩
    intro same
    exact designated_ne window index ((vertexLabel object).injective same)

/-- **The realization is injective**, so the package's joint state count is
bounded by the labelled-skeleton count.  Two assignments differing at any single
window differ as graphs, because that window's edge slots are its own. -/
theorem realizeAttachment_injective
    (profile : InducedPathMaximalPacking.Profile object order)
    (designated : object.Vertex)
    (outside : ∀ window : PackedWindow profile,
      designated ∉ support profile window) :
    Function.Injective (realizeAttachment profile designated) := by
  classical
  intro left right same
  funext window
  ext index
  rw [← adj_realizeAttachment_iff profile designated outside left window index,
    ← adj_realizeAttachment_iff profile designated outside right window index,
    same]

/-! ## The entropy cap, with its antecedent discharged -/

/-- The per-window state count of the attachment coordinates. -/
theorem card_attachmentState (object : FiniteObject.{u}) (order : Nat) :
    Nat.card (AttachmentState object order) = 2 ^ order := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]

/-- **`lem:independent-target-entropy` at the attachment coordinates, with no
hypothesis left.**

The package of one attachment coordinate per packed window realizes
`2 ^ (order · p)` distinct labelled graphs, so that many states are available
inside the ambient labelled class.  `p` is the packing's own length, read by
`card_packedWindow`; no rate constant and no numeral is named.

This is the first consumed realization in the tree: it discharges the antecedent
of `demand_le_card_labelled_of_injective`, which until now nothing supplied. -/
theorem two_pow_order_mul_packing_le_card_labelled
    (profile : InducedPathMaximalPacking.Profile object order)
    (designated : object.Vertex)
    (outside : ∀ window : PackedWindow profile,
      designated ∉ support profile window) :
    2 ^ (order * profile.selected.length) ≤
      Nat.card (LabelledOn object.vertexCount) := by
  classical
  have uniform : ∀ window : PackedWindow profile,
      Nat.card (AttachmentState object order) = 2 ^ order :=
    fun _ => card_attachmentState object order
  have demandEq :
      demand (fun _window : PackedWindow profile =>
          AttachmentState object order) =
        (2 ^ order) ^ profile.selected.length :=
    demand_eq_pow_of_uniform _ (2 ^ order) uniform
  have capped :
      demand (fun _window : PackedWindow profile =>
          AttachmentState object order) ≤
        Nat.card (LabelledOn object.vertexCount) :=
    demand_le_card_labelled_of_injective
      (realizeAttachment profile designated)
      (realizeAttachment_injective profile designated outside)
  rw [demandEq, ← pow_mul] at capped
  exact capped

end Hypostructure.Graph.PackedWindowRealization
