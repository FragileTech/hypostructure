import Hypostructure.Graph.ActualContext
import Hypostructure.Graph.InternalVertexFold
import Hypostructure.Graph.FoldCycleLift
import Hypostructure.Graph.RerouteSwap
import Hypostructure.Graph.SpliceLift

/-!
# The pieces constructed from G

A quotient, a trace-basin alternative or an exit-`(4)` family member compares
*realizations* — boundaried pieces that may occupy a support `Z` of G — in the
one outside context of G at `∂Z`, G's own surroundings `G − Z`.  The context is
G's.  The realizations are **pieces constructed from G**: the canonical finite
family `GConstructedPiece G Z` of `∂Z`-pieces obtained from G's own data by the
operations the manuscript uses.  Every member is fixed by G (its parameters are
vertices and vertex sets of G, and G's vertex order), and none of them needs a
choice.

* `own`: G's piece `G[Z]` itself;
* `reading X`: G's reading at `Z`, the edge restriction of `G[Z]` to `X`
  (`SupportAtom.retainedPiece`) — a subgraph of G once glued;
* `fold keep remove`: the identification of two interior vertices of `Z` with
  no common neighbour in G (`BoundaryPiece.identifyInternal`); when the two are
  adjacent this is the contraction of a triangle-free edge;
* `transplant Y`: `G[Z]` with the interior vertices outside `Y` deleted
  (`Transplant.transplant`);
* `swap P Q`: the rerouted swap, `G[Z]` with the interior structure of `P`
  replaced by a fresh copy of the interior structure of `Q`
  (`RerouteSwap.swapPiece`) — not a subgraph of G;
* `splice a b D`: the excision of `D` from `G[Z]` with the shortcut edge
  `a b` (`SpliceLift.splice`, read on `∂Z`) — not a subgraph of G;
* `switch a a' b b'`: the double-edge switch `G − {a a', b b'} + {a b', b a'}`
  read on `G[Z]` (G itself when the switch is not proper) — not a subgraph of G.

A reading glued into `G − Z` is a subgraph of G, so readings alone make every
comparison in `G − Z` trivial at a target-avoiding G.  The other members carry
real content: a fold glued into `G − Z` is a strictly smaller graph that keeps
the degree baseline, so at a minimal G it carries a target cycle
(`response_fold_of_minimal`), and that cycle lifts to an accepted-length path of
G between the two folded vertices (`exists_path_of_response_fold`).

`response L P` is G's target response of the member `P`: `glue P (G − Z)` has
an accepted cycle.  This is G's own signature at `Z`; no other context and no
other graph is quantified.

Nothing here knows a presentation, a ledger, or a manuscript node.
-/

namespace Hypostructure.Graph

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## Two generic builders on G's own vertices -/

section Builders

variable (object : FiniteObject.{u})

/-- **G's piece at `Z` with the adjacency of a graph `H` on `V(G)`**: the
interior and labels of `G[Z]`, the edges of `H` between decoded ends.  At
`H = G` it is `G[Z]`. -/
noncomputable def edgePiece (Z : Finset object.Vertex)
    (H : SimpleGraph object.Vertex) :
    BoundaryPiece (SupportAtom.boundary object Z) where
  Internal := SupportAtom.PieceInternal object Z
  internalVertices := (SupportAtom.piece object Z).internalVertices
  graph := SimpleGraph.comap (SupportAtom.pieceDecode object Z) H
  decideAdj := Classical.decRel _

/-- **The rewiring of `G[Z]` on the kept interior `int(Z) ∩ Y`**: the labels of
`∂Z`, the interior vertices of `Z` in `Y`, the edges of a graph `H` on `V(G)`
between decoded ends.  At `H = G` it is `Transplant.transplant G Z Y`. -/
noncomputable def rewirePiece (Z Y : Finset object.Vertex)
    (H : SimpleGraph object.Vertex) :
    BoundaryPiece (SupportAtom.boundary object Z) where
  Internal := Transplant.TransplantInternal object Z Y
  internalVertices := (Transplant.transplant object Z Y).internalVertices
  graph := SimpleGraph.comap (Transplant.transplantDecode object Z Y) H
  decideAdj := Classical.decRel _

/-- **The splice of G**: `G` with the vertices of `D` isolated and the shortcut
edge `a b` added (`SpliceLift.splice`). -/
noncomputable def spliceGraph (a b : object.Vertex) (D : Finset object.Vertex) :
    SimpleGraph object.Vertex := by
  classical
  exact SpliceLift.splice object.graph a b ↑D

/-- A proper double-edge switch of G at `a a'`, `b b'`: both are edges, the
four ends are distinct, and neither exchanged edge `a b'`, `b a'` is present. -/
def DoubleSwitchValid (a a' b b' : object.Vertex) : Prop :=
  object.graph.Adj a a' ∧ object.graph.Adj b b' ∧ a ≠ b ∧ a ≠ b' ∧ a' ≠ b ∧
    a' ≠ b' ∧ ¬ object.graph.Adj a b' ∧ ¬ object.graph.Adj b a'

/-- **The double-edge switch of G**: `G − {a a', b b'} + {a b', b a'}` when the
switch is proper, and `G` itself otherwise. -/
noncomputable def doubleSwitchGraph (a a' b b' : object.Vertex) :
    SimpleGraph object.Vertex := by
  classical
  exact if DoubleSwitchValid object a a' b b' then
    object.graph.deleteEdges {s(a, a'), s(b, b')} ⊔
      (SimpleGraph.edge a b' ⊔ SimpleGraph.edge b a')
  else object.graph

/-- **The excision piece**: `G[Z]` with the interior vertices in `D` deleted and
the shortcut edge `a b` added, on `∂Z`'s own labels. -/
noncomputable def splicePiece (Z : Finset object.Vertex) (a b : object.Vertex)
    (D : Finset object.Vertex) : BoundaryPiece (SupportAtom.boundary object Z) := by
  classical
  exact rewirePiece object Z (Z \ D) (spliceGraph object a b D)

end Builders

/-! ## The family -/

/-- **The canonical finite family of `∂Z`-pieces constructed from G.**  Every
parameter is a vertex or a vertex set of G; the fold records the two folded
interior vertices together with the facts that make it a fold (distinct, no
common neighbour in G). -/
inductive GConstructedPiece (object : FiniteObject.{u}) (Z : Finset object.Vertex) :
    Type u
  /-- G's own piece `G[Z]`. -/
  | own
  /-- G's reading at `Z`: `G[Z]` restricted to the edges inside `X`. -/
  | reading (X : Finset object.Vertex)
  /-- The fold of two interior vertices of `Z` with no common neighbour in G. -/
  | fold (keep remove : SupportAtom.PieceInternal object Z)
      (different : keep ≠ remove)
      (noCommon : ∀ common : object.Vertex,
        ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common)
  /-- The transplant of `Y`: `G[Z]` with the interior outside `Y` deleted. -/
  | transplant (Y : Finset object.Vertex)
  /-- The rerouted swap: the interior structure of `P` replaced by a fresh copy
  of the interior structure of `Q`. -/
  | swap (P Q : Finset object.Vertex)
  /-- The excision of `D` with the shortcut edge `a b`. -/
  | splice (a b : object.Vertex) (D : Finset object.Vertex)
  /-- The double-edge switch at `a a'`, `b b'`. -/
  | switch (a a' b b' : object.Vertex)

namespace GConstructedPiece

variable {object : FiniteObject.{u}} {Z : Finset object.Vertex}

/-- The `∂Z`-piece a member denotes. -/
noncomputable def toPiece :
    GConstructedPiece object Z → BoundaryPiece (SupportAtom.boundary object Z)
  | own => SupportAtom.piece object Z
  | reading X => SupportAtom.retainedPiece object Z X
  | fold keep remove different _ =>
      (SupportAtom.piece object Z).identifyInternal keep remove different
  | transplant Y => Transplant.transplant object Z Y
  | swap P Q => RerouteSwap.swapPiece object Z P Q
  | splice a b D => splicePiece object Z a b D
  | switch a a' b b' => edgePiece object Z (doubleSwitchGraph object a a' b b')

/-- **G's target response of a constructed piece**: the piece glued into G's
own surroundings `G − Z` carries an accepted cycle. -/
def response (LengthOK : Nat → Prop) (P : GConstructedPiece object Z) : Prop :=
  HasCycleWithLength LengthOK (glue P.toPiece (SupportAtom.outside object Z))

/-- The boundary-degree profile of a constructed piece. -/
noncomputable abbrev profile (P : GConstructedPiece object Z) :=
  P.toPiece.boundaryDegreeProfile

@[simp] theorem toPiece_own :
    (own : GConstructedPiece object Z).toPiece = SupportAtom.piece object Z := rfl

@[simp] theorem toPiece_reading (X : Finset object.Vertex) :
    (reading X : GConstructedPiece object Z).toPiece =
      SupportAtom.retainedPiece object Z X := rfl

@[simp] theorem toPiece_fold (keep remove : SupportAtom.PieceInternal object Z)
    (different : keep ≠ remove)
    (noCommon : ∀ common : object.Vertex,
      ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common) :
    (fold keep remove different noCommon : GConstructedPiece object Z).toPiece =
      (SupportAtom.piece object Z).identifyInternal keep remove different := rfl

/-! ## Members that are subgraphs of G once glued -/

/-- G's own piece glued into `G − Z` is G: no accepted cycle. -/
theorem not_response_own {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L object) :
    ¬ (own : GConstructedPiece object Z).response L :=
  not_target_glue_piece_outside avoids Z

/-- A reading glued into `G − Z` is a subgraph of G: no accepted cycle. -/
theorem not_response_reading {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object) (X : Finset object.Vertex) :
    ¬ (reading X : GConstructedPiece object Z).response L :=
  ActualContext.not_target_actualGlue avoids Z X

/-- A transplant glued into `G − Z` is `G − D`: no accepted cycle. -/
theorem not_response_transplant {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object) (Y : Finset object.Vertex) :
    ¬ (transplant Y : GConstructedPiece object Z).response L :=
  Transplant.not_target_of_linkageIncluded avoids
    (Transplant.transplant_linkageIncluded Z Y)

/-- A rerouted swap whose inserted interior lies in the replaced one is
linkage-included: no accepted cycle. -/
theorem not_response_swap {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object) {P Q : Finset object.Vertex}
    (sub : ∀ v, RerouteSwap.InteriorIn object Z Q v → v ∈ P) :
    ¬ (swap P Q : GConstructedPiece object Z).response L :=
  RerouteSwap.swap_not_target avoids Z P Q
    (RerouteSwap.swap_linkageIncluded_of_subset sub)

/-! ## The fold -/

section Fold

/-- G's piece glued into `G − Z` is G. -/
noncomputable def ownGlueIso :
    (glue (SupportAtom.piece object Z) (SupportAtom.outside object Z)).Iso object :=
  (SupportAtom.decomposition object Z).reconstructionIso

/-- The fold's no-common-neighbour condition, read in the piece `G[Z]`. -/
theorem noCommon_piece (keep remove : SupportAtom.PieceInternal object Z)
    (noCommon : ∀ common : object.Vertex,
      ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common) :
    ∀ x, ¬ ((SupportAtom.piece object Z).graph.Adj (.inr keep) x ∧
      (SupportAtom.piece object Z).graph.Adj (.inr remove) x) := by
  intro x common
  exact noCommon (SupportAtom.pieceDecode object Z x) ⟨common.1, common.2⟩

/-- **A fold keeps G's boundary-degree profile at `Z`.** -/
theorem profile_fold (keep remove : SupportAtom.PieceInternal object Z)
    (different : keep ≠ remove)
    (noCommon : ∀ common : object.Vertex,
      ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common) :
    (fold keep remove different noCommon : GConstructedPiece object Z).profile =
      (own : GConstructedPiece object Z).profile :=
  BoundaryPiece.boundaryDegreeProfile_identifyInternal_of_noCommonLabel
    (SupportAtom.piece object Z) keep remove different (fun label => noCommon_piece keep remove noCommon (.inl label))

/-- **A fold glued into `G − Z` is strictly smaller than G.** -/
theorem fold_glue_smaller (keep remove : SupportAtom.PieceInternal object Z)
    (different : keep ≠ remove) :
    (glue ((SupportAtom.piece object Z).identifyInternal keep remove different)
      (SupportAtom.outside object Z)).LexicographicallySmaller object :=
  (FiniteObject.lexicographicallySmaller_congr_right ⟨ownGlueIso⟩).mp
    (lexicographicallySmaller_glue_identifyInternal (SupportAtom.piece object Z)
      keep remove different (SupportAtom.outside object Z))

/-- **A fold glued into `G − Z` keeps G's degree baseline** (`2 ≤ k`). -/
theorem fold_glue_baseline (keep remove : SupportAtom.PieceInternal object Z)
    (different : keep ≠ remove)
    (noCommon : ∀ common : object.Vertex,
      ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common)
    {k : Nat} (two : 2 ≤ k) (baseline : MinimumDegreeAtLeast k object) :
    MinimumDegreeAtLeast k
      (glue ((SupportAtom.piece object Z).identifyInternal keep remove different)
        (SupportAtom.outside object Z)) := by
  have source : k ≤ (glue (SupportAtom.piece object Z)
      (SupportAtom.outside object Z)).minDegree := by
    have same := FiniteObject.minDegree_eq_of_isomorphic
      (⟨ownGlueIso⟩ : (glue (SupportAtom.piece object Z)
        (SupportAtom.outside object Z)).Isomorphic object)
    unfold MinimumDegreeAtLeast at baseline
    omega
  have origin : ∀ internal : SupportAtom.PieceInternal object Z,
      k ≤ (SupportAtom.piece object Z).pack.degree (.inr internal) := by
    intro internal
    have step := source.trans ((glue (SupportAtom.piece object Z)
      (SupportAtom.outside object Z)).minDegree_le_degree (.inr (.inl internal)))
    rwa [glue_degree_pieceInternal] at step
  exact le_minDegree_glue_identifyInternal (SupportAtom.piece object Z) keep remove
    different (SupportAtom.outside object Z) k two
    ⟨.inr (.inl ⟨keep, different⟩)⟩ source (origin keep) (origin remove)
    (noCommon_piece keep remove noCommon)

/-- **At a minimal G every fold carries a target cycle in `G − Z`**: glued into
`G − Z` it is a strictly smaller graph with the degree baseline. -/
theorem response_fold_of_minimal {L : Nat → Prop} {k : Nat} (two : 2 ≤ k)
    (baseline : MinimumDegreeAtLeast k object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength L H)
    (keep remove : SupportAtom.PieceInternal object Z)
    (different : keep ≠ remove)
    (noCommon : ∀ common : object.Vertex,
      ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common) :
    (fold keep remove different noCommon : GConstructedPiece object Z).response L :=
  minimal _ (fold_glue_smaller keep remove different)
    (fold_glue_baseline keep remove different noCommon two baseline)

/-- **The fold's target cycle lifts to G**: at a target-avoiding G, an accepted
cycle of the fold glued into `G − Z` gives an accepted-length path of G between
the two folded vertices (`FoldCycleLift.foldGlue_path_of_cycle`). -/
theorem exists_path_of_response_fold {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (keep remove : SupportAtom.PieceInternal object Z)
    (different : keep ≠ remove)
    (noCommon : ∀ common : object.Vertex,
      ¬ FiniteObject.IsCommonNeighbor keep.1 remove.1 common)
    (response : (fold keep remove different noCommon :
      GConstructedPiece object Z).response L) :
    ∃ p : object.graph.Walk keep.1 remove.1, p.IsPath ∧ L p.length := by
  have sourceAvoids : ¬ HasCycleWithLength L
      (glue (SupportAtom.piece object Z) (SupportAtom.outside object Z)) :=
    not_target_glue_piece_outside avoids Z
  obtain ⟨p, isPath, length⟩ :=
    FoldCycleLift.foldGlue_path_of_cycle (SupportAtom.piece object Z) keep remove
      different (SupportAtom.outside object Z) L sourceAvoids response
  let iso := (ownGlueIso (object := object) (Z := Z))
  have startEq : iso.toHom (.inr (.inl keep)) = keep.1 := rfl
  have endEq : iso.toHom (.inr (.inl remove)) = remove.1 := rfl
  refine ⟨(p.map iso.toHom).copy startEq endEq, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective iso.injective isPath
  · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
    exact length

end Fold

end GConstructedPiece

end Hypostructure.Graph
