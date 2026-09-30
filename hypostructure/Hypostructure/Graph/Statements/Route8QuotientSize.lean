import Hypostructure.Graph.Statements.RouteEight

/-!
# Statements: the route-8 quotient test stated about G

Node `[348]` / `[113]` (the failure of route-8 quotient freeness of the unified
census), stated about G only.

* `Route8BasinRepresentative`: the canonical representative of the
  cut-state of G's own piece at a basin `B_u` (read in `G − B_u`, the only
  outside context that is part of G) is a valid replacement of exactly the
  size of the piece.  A valid
  replacement of a piece of a minimal counterexample cannot be smaller, so the
  "strictly smaller representative" that the manuscript's step "(b) implies
  exit `(5)`" needs does not exist at G.
* `Route8QuotientEntriesAtGStatement`: what G decides about the test -- the
  unified entry family is nonempty and carries the rate (a two-support entry);
  at every unified entry the selected basin exists, the representative is
  size-preserving, the folds carry accepted cycles and paths, and the exit-`(5)`
  datum (`TraceTargetCompleteCompression`) is absent; at an entry with
  `α(ξ) = 0` the quotient of alternative (b) is present.  Over the realizations
  constructed from G, `α(ξ) = 0` and the presence of (b) at every entry are not
  decided by this statement.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The canonical representative of the (b)-quotient class of G's piece at
`basin`, constructed** (`def:proper-quotient-representative` read at G): the
`Precedes`-least canonical piece with the boundary-degree profile, target
response in `G − basin` and inherited baseline of G's own piece
(`CanonicalPiece.cutStateRepresentativeAt`).  It is a valid replacement --
same profile, degree baseline and no target cycle once glued into `G − basin`
-- of exactly the size of the piece, and its gluing is not lexicographically
smaller than G: a valid replacement cannot be smaller. -/
abbrev Route8BasinRepresentative (data : Parameters)
    (object : Graph.FiniteObject.{u}) (basin : Finset object.Vertex) : Prop :=
  let piece := Graph.Strategy.InterfaceReplacement.SupportAtom.piece object basin
  let outside :=
    Graph.Strategy.InterfaceReplacement.SupportAtom.outside object basin
  let representative := Graph.CanonicalPiece.cutStateRepresentativeAt
    (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant piece outside
  representative.toPiece.boundaryDegreeProfile = piece.boundaryDegreeProfile ∧
    Graph.MinimumDegreeAtLeast data.threshold
      (Graph.glue representative.toPiece outside) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK
      (Graph.glue representative.toPiece outside) ∧
    representative.size = piece.internalVertexCount ∧
    ¬ (Graph.glue representative.toPiece outside).LexicographicallySmaller object

/-- **No trace-response quotient reading of the basin is a smaller valid
replacement**: for every retained set of declared base coordinates, the reading
`retainedReading` (G's own piece with the internal edges of the forgotten
coordinates dropped, replaced by the canonical piece of its cut state), glued
into `G − basin`, is either below the degree baseline or not lexicographically
smaller than G. -/
abbrev Route8QuotientReadingsNotSmaller (data : Parameters)
    (object : Graph.FiniteObject.{u}) (support basin : Finset object.Vertex) :
    Prop :=
  ∀ retained : Finset (Graph.TraceCoordinateSystem.Base.Coordinate object
      support),
    Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue
          (Graph.Route8.PresentedEntry.retainedReading object support basin
            data.threshold data.LengthOK retained)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
            basin)) →
      ¬ (Graph.glue
          (Graph.Route8.PresentedEntry.retainedReading object support basin
            data.threshold data.LengthOK retained)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
            basin)).LexicographicallySmaller object

/-- **The realizations constructed from G do not hold the declared algebra**:
neither the canonical representative of G's piece at the basin, nor any of G's
quotient readings of the basin, nor any fold of two of its interior vertices,
satisfies the declared `u`-supported target algebra
(`def:typeA-trace-basin`) in `G − basin`.  It is stated at `α(ξ) = 0`, where the
declared algebra is empty (`not_declaredAlgebra_of_alpha_zero`). -/
abbrev Route8ConstructedRealizationsUndeclared (data : Parameters)
    (object : Graph.FiniteObject.{u}) (support basin : Finset object.Vertex)
    (receiver load : object.Vertex) : Prop :=
  let piece := Graph.Strategy.InterfaceReplacement.SupportAtom.piece object basin
  let outside :=
    Graph.Strategy.InterfaceReplacement.SupportAtom.outside object basin
  (¬ Graph.Route8.TraceBasin.declaredAlgebra object support basin
      data.threshold data.LengthOK receiver load
      (Graph.CanonicalPiece.cutStateRepresentativeAt
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
        piece outside).toPiece outside) ∧
    (∀ retained : Finset (Graph.TraceCoordinateSystem.Base.Coordinate object
        support),
      ¬ Graph.Route8.TraceBasin.declaredAlgebra object support basin
        data.threshold data.LengthOK receiver load
        (Graph.Route8.PresentedEntry.retainedReading object support basin
          data.threshold data.LengthOK retained) outside) ∧
    (∀ (keep remove : piece.Internal) (different : keep ≠ remove),
      ¬ Graph.Route8.TraceBasin.declaredAlgebra object support basin
        data.threshold data.LengthOK receiver load
        (piece.identifyInternal keep remove different) outside)

/-- **The folds of the basin's piece, constructed from G**: identifying two
interior vertices of G's piece at `basin` that share no neighbour
(`BoundaryPiece.identifyInternal`) gives a piece whose gluing into `G − basin`
meets the degree baseline and is lexicographically smaller than G
(`foldRealization_baseline_and_smaller`), hence -- by the minimality of G --
carries an accepted cycle: the fold is a smaller valid realization that is not
target-complete. -/
abbrev Route8BasinFoldsCarryCycles (data : Parameters)
    (object : Graph.FiniteObject.{u}) (basin : Finset object.Vertex) : Prop :=
  ∀ (connected : Graph.SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove :
      (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).Internal)
    (different : keep ≠ remove),
    (∀ x, ¬ ((Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr keep) x ∧
      (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr remove) x)) →
      Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue
            ((Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
              basin).identifyInternal keep remove different)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
              basin connected proper).decomposition.outside) ∧
        (Graph.glue
          ((Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
            basin).identifyInternal keep remove different)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
            basin connected proper).decomposition.outside).LexicographicallySmaller
          object ∧
        Graph.HasCycleWithLength data.LengthOK
          (Graph.glue
            ((Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
              basin).identifyInternal keep remove different)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
              basin connected proper).decomposition.outside)

/-- **The accepted path that a fold forces, and where it goes.**  For two
interior vertices of the basin's piece that share no neighbour, the fold's
cycle (minimality of G) lifts to an accepted-length path of G between them
(`FoldCycleLift.foldGlue_path_of_cycle`).  Either the path stays in the entry's
support `X`, or it leaves `X` and so uses two distinct edges of the cut of `X`
(edges with exactly one endpoint in `X`, edges of the boundary of the
remainder). -/
abbrev Route8BasinFoldPaths (data : Parameters)
    (object : Graph.FiniteObject.{u}) (support basin : Finset object.Vertex) :
    Prop :=
  basin ⊆ support →
  ∀ (connected : Graph.SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove :
      (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).Internal)
    (different : keep ≠ remove),
    (∀ x, ¬ ((Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr keep) x ∧
      (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr remove) x)) →
      ∃ P : object.graph.Walk
          (Graph.Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
            basin (.inr keep))
          (Graph.Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
            basin (.inr remove)),
        P.IsPath ∧ data.LengthOK P.length ∧
          ((∀ x ∈ P.support, x ∈ support) ∨
            ∃ e1 ∈ P.edges, ∃ e2 ∈ P.edges, e1 ≠ e2 ∧
              e1 ∈ Graph.Route8.cutEdges object support ∧
              e2 ∈ Graph.Route8.cutEdges object support)

/-- **The baseline-essential carriers of an entry, and their map to `∂R`.**
G is at the degree baseline and the piece has zero ambient surplus, so every
vertex of the piece has degree exactly `δ`: no incidence of a basin vertex is
spare, and every edge of the cut of the piece meeting the basin is
baseline-essential.  Those edges lie in the boundary `∂R` of the remainder, and
they are nonempty: the receiver of the entry lies in the basin and has a port
(`internalDegree < δ = degree`). -/
abbrev Route8EntryCarriers (data : Parameters)
    (object : Graph.FiniteObject.{u}) (support basin : Finset object.Vertex) :
    Prop :=
  (∃ e ∈ Graph.Route8.cutEdges object support, ∃ v ∈ e, v ∈ basin) ∧
    ∀ e ∈ Graph.Route8.cutEdges object support, (∃ v ∈ e, v ∈ basin) →
      e ∈ Graph.Route8Census.supply object (canonicalWindowPacking data object) ∧
        ∃ v ∈ e, v ∈ basin ∧ object.degree v = data.threshold

/-- **A path inside the entry's piece is short**: the piece lies in the
remainder `R` of the canonical packing and, having zero ambient surplus, has no
hub (every vertex has degree `3`).  The remainder path bounds
(`K .remainderPathBounds`: paths through `k` hubs have at most `6143k + 6142`
vertices) give every path of G inside the piece at most `6142` vertices.  In
particular an accepted-length fold path (`Route8BasinFoldPaths`) that stays in
the piece has length `2^k ≤ 6141`, so `k ≤ 12`. -/
abbrev Route8InsidePathBound (object : Graph.FiniteObject.{u})
    (support : Finset object.Vertex) : Prop :=
  ∀ {a b : object.Vertex} (P : object.graph.Walk a b), P.IsPath →
    (∀ x ∈ P.support, x ∈ support) → P.length ≤ 6141

/-- **The baseline-essential carriers of an indexed entry** (`def:typeA-route8-carriers`
at G): the edges of the cut of the entry's piece that meet its selected basin.
At G the piece is cubic, so these are the
incidences of the basin that cannot be dropped without breaking the degree
baseline; all lie in `∂R`. -/
noncomputable def route8EntryCarrierSet (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (index : Graph.Route8Census.Index object) : Finset (Sym2 object.Vertex) := by
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  classical
  exact (Graph.Route8.cutEdges object index.1).filter fun e =>
    ∃ v ∈ e, v ∈ Graph.Route8Census.basin object data.threshold index

/-- **The private carriers of an entry** inside the unified collection: carriers
that are carriers of no other entry (`π(ξ)` of `def:typeA-route8-carriers`). -/
noncomputable def route8EntryPrivateCarriers (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (index : Graph.Route8Census.Index object) : Finset (Sym2 object.Vertex) := by
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  classical
  exact SDiff.sdiff (route8EntryCarrierSet data object index)
    (((route8UnifiedEntries data object).erase index).biUnion
      (route8EntryCarrierSet data object))

/-- **`prop:typeA-route8-carrier-reduction` at G**: the unified collection has a
two-support entry, one with fewer than `δ` private baseline-essential carriers.
(Otherwise the disjoint private carrier sets give `δ·|Ξ̃| ≤ |∂R|`.) -/
abbrev Route8TwoSupportEntryExists (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ index ∈ route8UnifiedEntries data object,
    (route8EntryPrivateCarriers data object index).card + 1 ≤ data.threshold

/-- **Node `[348]`, stated about G** (Lean improvement).

1. An empty unified entry family is quotient-free (`Route8QuotientFreeStatement`
   holds vacuously).
2. The unified entry family is nonempty and carries the rate (`K .route8Rate`,
   the manuscript rate `τ < 3/13`, the unified deficit `lem:typeA-unified-deficit`
   and the stage accounting `s·\tilde D_A ≤ |\tilde\Xi|`): the boundary incidence
   supply `|∂R|` is below `δ·|\tilde\Xi|`, and a two-support entry exists.
3. At every unified entry `ξ = (X, w, u)`: the selected basin `B_u` exists; at
   `α(ξ) = 0` its trace-response quotient (alternative (b), G-form) is present and
   the constructed realizations do not hold the declared algebra; the canonical
   representative of G's piece at `B_u` is a valid replacement of the size of the
   piece, not smaller; no quotient reading is a smaller valid replacement; the
   folds of `B_u` carry accepted cycles and paths; the carriers lie in `∂R`; paths
   inside the piece are short; and the exit-`(5)` compression datum at `B_u` is
   absent.

(The realizations of alternative (b) are the pieces constructed from G
(`GConstructedPiece`), so neither `α(ξ) = 0` nor the presence of (b) at every
entry is decided here.  `K .route8Rate` is the manuscript rate, so the rate
clause is unconditional.) -/
noncomputable abbrev Route8QuotientEntriesAtGStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  (route8UnifiedEntries data object = ∅ →
      Route8QuotientFreeStatement data object) ∧
    0 < (route8UnifiedEntries data object).card ∧
    ((Graph.Route8Census.supply object (canonicalWindowPacking data object)).card <
          data.threshold * (route8UnifiedEntries data object).card ∧
        Route8TwoSupportEntryExists data object) ∧
    ∀ index ∈ route8UnifiedEntries data object,
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin ∧
          (((Graph.Route8Census.presented object data.threshold data.LengthOK
              index).toEntry (Graph.HasCycleWithLength data.LengthOK)).alpha = 0 →
            (∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient object
              index.1 data.threshold data.LengthOK index.2.1 index.2.2 basin
              retained) ∧
            Route8ConstructedRealizationsUndeclared data object index.1 basin
              index.2.1 index.2.2) ∧
          Route8BasinRepresentative data object basin ∧
          Route8QuotientReadingsNotSmaller data object index.1 basin ∧
          Route8BasinFoldsCarryCycles data object basin ∧
          Route8BasinFoldPaths data object index.1 basin ∧
          Route8EntryCarriers data object index.1 basin ∧
          Route8InsidePathBound object index.1 ∧
          ¬ Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
            index.1 data.threshold data.LengthOK index.2.1 index.2.2 basin

end Hypostructure.Graph.Strategy.Spine
