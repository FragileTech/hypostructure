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
* `Route8QuotientEntriesAtGStatement`: the test is decided at G -- the quotient
  is trivially present at every entry, so the failure of quotient freeness is
  exactly the non-emptiness of the unified entry family; and at every unified
  entry the essential core is empty, the quotient is present, the
  representative is size-preserving, and the exit-`(5)` datum
  (`TraceTargetCompleteCompression`) is absent.

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

/-- **Every smaller degree-valid realization of the basin carries an undeclared
target cycle**: for any boundaried piece `Q` of the basin's interface whose
gluing into `G − basin` meets the degree baseline and is lexicographically
smaller than G -- a fold or contraction of G's piece, a canonical
representative, any valid replacement -- the gluing has an accepted cycle
(the minimality of G), and the declared `u`-supported target algebra
(`def:typeA-trace-basin`, the only target quotients are tested against) does
not hold at `Q`.  This is the exact gap between the declared-algebra
completeness of alternative (b) and the raw target completeness of the exit-`(5)`
compression: the cycle of a smaller valid realization is never a declared
event. -/
abbrev Route8SmallerRealizationsUndeclared (data : Parameters)
    (object : Graph.FiniteObject.{u}) (support basin : Finset object.Vertex)
    (receiver load : object.Vertex) : Prop :=
  ∀ Q : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object basin),
    Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue Q
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
            basin)) →
      (Graph.glue Q
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
          basin)).LexicographicallySmaller object →
      Graph.HasCycleWithLength data.LengthOK
        (Graph.glue Q
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
            basin)) ∧
        ¬ Graph.Route8.TraceBasin.declaredAlgebra object support basin
          data.threshold data.LengthOK receiver load Q
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object
            basin)

/-- **Node `[348]`, stated about G** (Lean improvement: the quotient test is
decided at G).

1. `Route8QuotientFreeStatement` holds exactly when the unified entry family
   is empty: alternative (b) is present at every routed load of G.
2. The unified entry family carries the private-carrier rate: the boundary
   incidence supply `|∂R|` is below `δ·|\tilde\Xi|` (the rate
   `K .route8Rate`, the unified deficit `lem:typeA-unified-deficit`, and the
   stage accounting `s·\tilde D_A ≤ |\tilde\Xi|`).  In particular the family
   is nonempty.
3. At every unified entry `ξ = (X, w, u)`: `α(ξ) = 0`; the selected basin `B_u`
   exists; its trace-response quotient (alternative (b), G-form) is present;
   the canonical representative of G's piece at `B_u` is a valid replacement
   of the size of the piece, not smaller; no quotient reading is a smaller
   valid replacement; and the exit-`(5)` compression datum at `B_u` is
   absent. -/
noncomputable abbrev Route8QuotientEntriesAtGStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  (Route8QuotientFreeStatement data object ↔
      route8UnifiedEntries data object = ∅) ∧
    (Graph.Route8Census.supply object (canonicalWindowPacking data object)).card <
      data.threshold * (route8UnifiedEntries data object).card ∧
    ∀ index ∈ route8UnifiedEntries data object,
      ((Graph.Route8Census.presented object data.threshold data.LengthOK
        index).toEntry (Graph.HasCycleWithLength data.LengthOK)).alpha = 0 ∧
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin ∧
          (∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient object
            index.1 data.threshold data.LengthOK index.2.1 index.2.2 basin
            retained) ∧
          Route8BasinRepresentative data object basin ∧
          Route8QuotientReadingsNotSmaller data object index.1 basin ∧
          Route8SmallerRealizationsUndeclared data object index.1 basin
            index.2.1 index.2.2 ∧
          ¬ Graph.Route8.TraceBasin.TraceTargetCompleteCompression object
            index.1 data.threshold data.LengthOK index.2.1 index.2.2 basin

end Hypostructure.Graph.Strategy.Spine
