import Hypostructure.Graph.RemainderGlue
import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.WindowPacking

/-!
# The blocked class (`def:blocked-class`, node `[169]`)

`def:blocked-class`: fix the vertex set `V(G)`, the edge count `m`, and the fixed
maximal packing `𝒫` with its window positions.  The blocked class
`𝓑(𝒫) ⊆ 𝒢^{δ≥3}_{n,m}` is the set of labelled graphs on `V(G)` with `m` edges
and *minimum degree at least three* that contain every window of `𝒫` as an
induced `P₁₃` at its position and in which no cycle of a target length passes
through any window.  `rem:blocked-class-checks` (a): the minimum-degree clause is
the structure the plain skeleton budget `C(C(n,2),m)` does not charge, so the
class is stated inside the near-cubic skeleton class rather than inside all
labelled graphs with `m` edges.

This module builds exactly that: the near-cubic skeleton class
(`NearCubicSkeleton`), the blocked class as a subtype of it, the counting
bound `card 𝓑(𝒫) ≤ card 𝒢^{δ≥3}_{n,m} ≤ skeletonBudget` (`lem:skeleton-dominates`),
and the membership of the current object's own labelled skeleton in `𝓑(𝒫)`
(the last sentence of `def:blocked-class`: "on the trivial neutral germ
residual, `G ∈ 𝓑(𝒫)`").  The barrier states of a skeleton at a scale — the
input of the encoding of `lem:blocked-graphs-compress` and of the overlap
systems of `def:barrier-overlap-system` — are *not* defined here; the module
supplies the class those statements quantify over.
-/

namespace Hypostructure.Graph.BlockedClass

open Hypostructure
open Hypostructure.Graph.PackedWindowRealization (Skeleton card_skeleton)

universe u

/-! ## The near-cubic skeleton class -/

/-- Minimum degree at least `threshold` for a labelled graph, read pointwise on
neighbour sets (no `Fintype` instance is committed at this level). -/
def MinDegreeAtLeast {n : Nat} (threshold : Nat) (H : LabelledOn n) : Prop :=
  ∀ vertex : Fin n, threshold ≤ Nat.card (H.graph.neighborSet vertex)

/-- **`𝒢^{δ≥3}_{n,m}`**: labelled skeletons on `n` vertices with `m` edges and
minimum degree at least `threshold`. -/
def NearCubicSkeleton (n m threshold : Nat) : Type :=
  {skeleton : Skeleton n m // MinDegreeAtLeast threshold skeleton.1}

instance instFiniteNearCubicSkeleton (n m threshold : Nat) :
    Finite (NearCubicSkeleton n m threshold) :=
  Subtype.finite

/-- The near-cubic class is dominated by the skeleton budget. -/
theorem card_nearCubicSkeleton_le (n m threshold : Nat) :
    Nat.card (NearCubicSkeleton n m threshold) ≤ (n.choose 2).choose m := by
  rw [← card_skeleton n m]
  exact Nat.card_le_card_of_injective (fun s : NearCubicSkeleton n m threshold => s.1)
    Subtype.val_injective

/-! ## Windows and blocked windows of a labelled graph -/

/-- A labelled graph contains a window at a labelled position: the induced
subgraph on that position contains an induced path on `order` vertices, and the
position has `order` vertices (`InducesWindow`, at the labelled graph). -/
def ContainsWindow {n : Nat} (order : Nat) (H : LabelledOn n)
    (window : Finset (Fin n)) : Prop :=
  SimpleGraph.IsIndContained (SimpleGraph.pathGraph order)
      (H.graph.induce (window : Set (Fin n))) ∧
    window.card = order

/-- A cycle of an accepted length passing through a vertex of a window. -/
def CycleThroughWindow {n : Nat} (LengthOK : Nat → Prop) (H : LabelledOn n)
    (window : Finset (Fin n)) : Prop :=
  ∃ vertex ∈ window, ∃ walk : H.graph.Walk vertex vertex,
    walk.IsCycle ∧ LengthOK walk.length

/-- **A blocked skeleton** (`def:blocked-class`): every window of the packing is
present at its position and no accepted cycle passes through any window. -/
structure IsBlocked {n : Nat} (order : Nat) (LengthOK : Nat → Prop)
    (windows : Finset (Finset (Fin n))) (H : LabelledOn n) : Prop where
  present : ∀ window ∈ windows, ContainsWindow order H window
  blocked : ∀ window ∈ windows, ¬ CycleThroughWindow LengthOK H window

/-- **`𝓑(𝒫)`**: the blocked class inside the near-cubic skeleton class. -/
def Blocked (n m threshold order : Nat) (LengthOK : Nat → Prop)
    (windows : Finset (Finset (Fin n))) : Type :=
  {skeleton : NearCubicSkeleton n m threshold // IsBlocked order LengthOK windows skeleton.1.1}

instance instFiniteBlocked (n m threshold order : Nat) (LengthOK : Nat → Prop)
    (windows : Finset (Finset (Fin n))) :
    Finite (Blocked n m threshold order LengthOK windows) :=
  Subtype.finite

/-- **`card 𝓑(𝒫) ≤ card 𝒢^{δ≥3}_{n,m} ≤ C(C(n,2),m)`.** -/
theorem card_blocked_le_nearCubic (n m threshold order : Nat) (LengthOK : Nat → Prop)
    (windows : Finset (Finset (Fin n))) :
    Nat.card (Blocked n m threshold order LengthOK windows) ≤
      Nat.card (NearCubicSkeleton n m threshold) :=
  Nat.card_le_card_of_injective
    (fun s : Blocked n m threshold order LengthOK windows => s.1) Subtype.val_injective

theorem card_blocked_le_choose (n m threshold order : Nat) (LengthOK : Nat → Prop)
    (windows : Finset (Finset (Fin n))) :
    Nat.card (Blocked n m threshold order LengthOK windows) ≤ (n.choose 2).choose m :=
  (card_blocked_le_nearCubic n m threshold order LengthOK windows).trans
    (card_nearCubicSkeleton_le n m threshold)

/-! ## The current object's own skeleton is blocked -/

section Object

variable (object : FiniteObject.{u})

/-- The object's vertex labelling (`RemainderGlue.vertexLabel`). -/
noncomputable abbrev label : object.Vertex ≃ Fin object.vertexCount :=
  RemainderGlue.vertexLabel object

/-- The object's own labelled skeleton: its graph transported to `Fin n`. -/
noncomputable def objectSkeleton : LabelledOn object.vertexCount :=
  ⟨object.graph.map (label object).toEmbedding⟩

/-- The transporting isomorphism. -/
noncomputable def objectIso : object.graph ≃g (objectSkeleton object).graph :=
  SimpleGraph.Iso.map (label object) object.graph

theorem objectIso_apply (vertex : object.Vertex) :
    objectIso object vertex = label object vertex := rfl

/-- The object's skeleton has the object's edge count. -/
theorem card_edgeSet_objectSkeleton :
    Nat.card (objectSkeleton object).graph.edgeSet = object.edgeCount := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have iso := (objectIso object).mapEdgeSet
  rw [← Nat.card_congr iso, object.edgeCount_eq_ncard_edgeSet, Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card, Set.toFinset_card]

/-- The object's skeleton in the skeleton class. -/
noncomputable def objectSkeletonMember : Skeleton object.vertexCount object.edgeCount :=
  ⟨objectSkeleton object, card_edgeSet_objectSkeleton object⟩

/-- Degrees transport along the labelling. -/
theorem card_neighborSet_objectSkeleton (vertex : object.Vertex) :
    Nat.card ((objectSkeleton object).graph.neighborSet (label object vertex)) =
      object.degree vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have e := (objectIso object).mapNeighborSet vertex
  rw [objectIso_apply] at e
  rw [← Nat.card_congr e]
  unfold FiniteObject.degree
  rw [← SimpleGraph.card_neighborSet_eq_degree, Nat.card_eq_fintype_card]

/-- The object's skeleton has minimum degree at least the object's baseline. -/
theorem minDegree_objectSkeleton (threshold : Nat)
    (baseline : Graph.MinimumDegreeAtLeast threshold object) :
    MinDegreeAtLeast threshold (objectSkeleton object) := by
  intro labelled
  obtain ⟨vertex, rfl⟩ := (label object).surjective labelled
  rw [card_neighborSet_objectSkeleton]
  exact le_trans baseline (object.minDegree_le_degree vertex)

/-- The object's skeleton in the near-cubic class. -/
noncomputable def objectNearCubic (threshold : Nat)
    (baseline : Graph.MinimumDegreeAtLeast threshold object) :
    NearCubicSkeleton object.vertexCount object.edgeCount threshold :=
  ⟨objectSkeletonMember object, minDegree_objectSkeleton object threshold baseline⟩

/-- The packing's windows, transported to labelled positions. -/
noncomputable def windowLabels (packing : Finset (Finset object.Vertex)) :
    Finset (Finset (Fin object.vertexCount)) := by
  classical
  exact packing.image fun window => window.map (label object).toEmbedding

/-- An induced window of the object is an induced window of its skeleton at the
transported position. -/
theorem containsWindow_of_inducesWindow (order : Nat) (window : Finset object.Vertex)
    (induces : object.InducesWindow order window) :
    ContainsWindow order (objectSkeleton object) (window.map (label object).toEmbedding) := by
  classical
  obtain ⟨contained, cardEq⟩ := induces
  refine ⟨?_, by simpa using cardEq⟩
  -- The object's induced subgraph on the window embeds into the skeleton's.
  have transport : (object.induce window).graph ↪g
      (objectSkeleton object).graph.induce
        ((window.map (label object).toEmbedding : Finset (Fin object.vertexCount)) :
          Set (Fin object.vertexCount)) := by
    refine ⟨⟨fun vertex => ⟨label object vertex.1, ?_⟩, ?_⟩, ?_⟩
    · simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe]
      exact ⟨vertex.1, vertex.2, rfl⟩
    · intro left right same
      apply Subtype.ext
      have := congrArg Subtype.val same
      exact (label object).injective this
    · intro left right
      change (objectSkeleton object).graph.Adj (label object left.1) (label object right.1) ↔
        object.graph.Adj left.1 right.1
      exact (objectIso object).map_rel_iff
  exact contained.trans ⟨transport⟩

/-- **The object's skeleton is blocked** (`def:blocked-class`, last sentence): the
packing's windows are present at their labelled positions, and, the object
having no accepted cycle at all, no accepted cycle passes through a window. -/
theorem objectSkeleton_blocked (order : Nat) (LengthOK : Nat → Prop)
    (packing : Finset (Finset object.Vertex))
    (valid : object.IsWindowPacking order packing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    IsBlocked order LengthOK (windowLabels object packing) (objectSkeleton object) := by
  classical
  refine ⟨?_, ?_⟩
  · intro window member
    have member' : window ∈ packing.image
        (fun window => window.map (label object).toEmbedding) := by
      simpa [windowLabels] using member
    obtain ⟨source, sourceMem, rfl⟩ := Finset.mem_image.1 member'
    exact containsWindow_of_inducesWindow object order source (valid.1 source sourceMem)
  · rintro window _ ⟨vertex, _, walk, isCycle, ok⟩
    apply avoids
    refine ⟨⟨(objectIso object).symm vertex, walk.map (objectIso object).symm.toHom,
      isCycle.map (objectIso object).symm.injective, ?_⟩⟩
    rw [SimpleGraph.Walk.length_map]
    exact ok

/-- The object's skeleton as a member of `𝓑(𝒫)`. -/
noncomputable def objectBlockedMember (threshold order : Nat) (LengthOK : Nat → Prop)
    (packing : Finset (Finset object.Vertex))
    (baseline : Graph.MinimumDegreeAtLeast threshold object)
    (valid : object.IsWindowPacking order packing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    Blocked object.vertexCount object.edgeCount threshold order LengthOK
      (windowLabels object packing) :=
  ⟨objectNearCubic object threshold baseline,
    objectSkeleton_blocked object order LengthOK packing valid avoids⟩

/-- **`card 𝓑(𝒫) ≤ skeletonBudget`** at the object. -/
theorem card_blocked_le_skeletonBudget (threshold order : Nat) (LengthOK : Nat → Prop)
    (windows : Finset (Finset (Fin object.vertexCount))) :
    Nat.card (Blocked object.vertexCount object.edgeCount threshold order LengthOK windows) ≤
      skeletonBudget object :=
  card_blocked_le_choose _ _ _ _ _ _

end Object

end Hypostructure.Graph.BlockedClass
