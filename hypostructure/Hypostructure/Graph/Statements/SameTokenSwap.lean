import Hypostructure.Graph.Statements.SameTokenPair
import Hypostructure.Graph.RerouteSwap
import Hypostructure.Graph.ReadingExactness
import Hypostructure.Graph.U2FreeWhole
import Hypostructure.Graph.PortPathCover
import Hypostructure.Graph.LadderG
import Hypostructure.Graph.WalkAttachment

/-!
# Statements: G's pattern pair, tested at G (`[144a]`, G audit S144a)

Facts about G at the canonical objects of the unresolved pair of node `[144a]`:
G's canonical routing, its pattern supports `X_p`, `X_q` and the canonical
support `Z = select?(X_p ∪ X_q)` (`SameTokenPinnedAt`).

* `SameTokenUnresolvedDecidedStatement`: the entry test of `[144a]`, decided at
  G.  Both readings of G at `Z` are subgraphs of G, so both are target-free and
  agree in `G − Z`; the arm "equal profiles, separated by `G − Z`" is empty.
  The pair is unresolved exactly because `r_p ≠ r_q`.
* `SameTokenReadingsExactStatement`: each reading of G at `Z` (edge restriction
  to `X_p`, `X_q`) drops no edge with an interior end, or drops one, is then
  lexicographically smaller than G and fails the baseline.
* `SameTokenSwapStatement`: the rerouted swap `swapPiece G Z P Q` (`P` replaced
  by a copy of `Q`, `RerouteSwap.lean`), in both directions: its conditions
  (i)-(iv) as exact predicates on G, the contact bijection fixed by G's vertex
  order, and the size relation minimality gives.
* `SameTokenSwapExactStatement`: the exact failure of the swaps at G's canonical
  exceptional vertex or at a linkage using a vertex and its copy; and, when both
  swaps are valid, equal interior sizes.
* `SameTokenU2FreeWholeStatement`: in the boundary-free configuration, valid
  transplants of both supports force `X_p = X_q = Z = V(G)`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The canonical objects of the unresolved pair: `X_p`, `X_q` the pattern
supports of G's canonical routing, `Z = select?(X_p ∪ X_q)`. -/
def SameTokenPinnedAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (routing : SameTokenRouting data object) (Xp Xq Z : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Xp = sameTokenPairSupport routing routing.demands.first ∧
    Xq = sameTokenPairSupport routing routing.demands.second ∧
    Graph.CanonicalSupport.select? object (Xp ∪ Xq) = some Z

/-- **The entry test of `[144a]`, decided at G.**  At the canonical objects: the
pattern coordinates differ; both readings of G at `Z` are target-free; they
agree in G's own surroundings `G − Z`; hence the arm "equal boundary profiles,
separated by `G − Z`" is empty. -/
noncomputable def SameTokenUnresolvedDecidedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      sameTokenPairCoordinate routing.capacity routing.demands.first ≠
        sameTokenPairCoordinate routing.capacity routing.demands.second ∧
      ¬ Graph.HasCycleWithLength data.LengthOK (Graph.ActualContext.actualGlue object Z Xp) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK (Graph.ActualContext.actualGlue object Z Xq) ∧
      (Graph.HasCycleWithLength data.LengthOK (Graph.ActualContext.actualGlue object Z Xp) ↔
        Graph.HasCycleWithLength data.LengthOK (Graph.ActualContext.actualGlue object Z Xq)) ∧
      ¬ ((Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object Z
              Xp).boundaryDegreeProfile =
            (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object Z
              Xq).boundaryDegreeProfile ∧
          ¬ (Graph.HasCycleWithLength data.LengthOK
                (Graph.ActualContext.actualGlue object Z Xp) ↔
            Graph.HasCycleWithLength data.LengthOK
                (Graph.ActualContext.actualGlue object Z Xq)))

/-- **A reading `Y` of G at `Z`, exactly.**  Either every edge of `G[Z]` with an
interior end lies in `Y` (the reading is G), or some such edge is dropped, the
reading (all vertices of G, fewer edges) is lexicographically smaller than G,
and it fails the baseline. -/
def ReadingExactAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (Z Y : Finset object.Vertex) : Prop :=
  (∀ x y, object.graph.Adj x y → x ∈ Z → y ∈ Z →
      (x ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z ∨
        y ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
      x ∈ Y ∧ y ∈ Y) ∨
    ∃ x y, object.graph.Adj x y ∧ x ∈ Z ∧ y ∈ Z ∧
      (x ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z ∨
        y ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) ∧
      ¬ (x ∈ Y ∧ y ∈ Y) ∧
      (Graph.ActualContext.actualGlue object Z Y).LexicographicallySmaller object ∧
      ¬ Graph.MinimumDegreeAtLeast data.threshold (Graph.ActualContext.actualGlue object Z Y)

/-- **The two readings of G at `Z`, exactly** (edge restrictions to `X_p`, `X_q`). -/
noncomputable def SameTokenReadingsExactStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      ReadingExactAt data object Z Xp ∧ ReadingExactAt data object Z Xq

/-- **The rerouted swap `P → Q` at G: conditions (i)-(iv).**  `swapPiece G Z P Q`
is G's piece at `Z` with the interior structure of `P` replaced by a copy of the
interior structure of `Q`.

* it has a vertex; (iii) `|int S| + |int Z ∩ P| = |int Z| + |int Z ∩ Q|`;
* (i) the profile of `G[Z]` iff every boundary vertex has as many interior
  neighbours in `Q` as in `P`; and then the copy vertices attached to `b` are
  the images of `b`'s `P`-neighbours under the order bijection of G;
* (ii) the baseline of `glue S (G − Z)` iff no vertex of G is deficient in any
  role (`SwapDegreeCondition`);
* (iv) linkage inclusion, or a linkage using a vertex and its copy; it holds
  when `int Z ∩ Q ⊆ P`; when it holds, `glue S (G − Z)` has no target cycle;
* minimality: baseline and linkage inclusion give `|int Z ∩ P| ≤ |int Z ∩ Q|`;
* descent: baseline and linkage inclusion make the glued swap not
  lexicographically smaller than G (fewer vertices, or equal vertices and fewer
  edges);
* the response: on a target-avoiding G, every accepted cycle of the glued swap
  passes through some vertex of `int Z ∩ Q ∖ P` both as itself and as its copy. -/
def SameTokenSwapAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (Z P Q : Finset object.Vertex) : Prop :=
  (∃ v, ¬ Graph.RerouteSwap.InteriorIn object Z P v ∨ Graph.RerouteSwap.InteriorIn object Z Q v) ∧
    ((Graph.RerouteSwap.swapPiece object Z P Q).internalVertexCount +
        Graph.RerouteSwap.intCount Z P =
      (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object Z).internalVertexCount +
        Graph.RerouteSwap.intCount Z Q) ∧
    ((Graph.RerouteSwap.swapPiece object Z P Q).boundaryDegreeProfile =
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object Z).boundaryDegreeProfile ↔
      ∀ b : (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex,
        {w | object.graph.Adj b.1 w ∧ Graph.RerouteSwap.InteriorIn object Z Q w}.ncard =
          {w | object.graph.Adj b.1 w ∧ Graph.RerouteSwap.InteriorIn object Z P w}.ncard) ∧
    (∀ (b : (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex)
      (hc : {w | object.graph.Adj b.1 w ∧ Graph.RerouteSwap.InteriorIn object Z P w}.ncard =
        {w | object.graph.Adj b.1 w ∧ Graph.RerouteSwap.InteriorIn object Z Q w}.ncard)
      (y : Graph.Transplant.TransplantInternal object Z Q),
      (Graph.RerouteSwap.swapPiece object Z P Q).graph.Adj (.inl b) (.inr (.inr y)) ↔
        ∃ w : {w | object.graph.Adj b.1 w ∧ Graph.RerouteSwap.InteriorIn object Z P w},
          ((Graph.RerouteSwap.orderEquiv _ _ hc) w).1 = y.1) ∧
    (Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) ↔
      Graph.RerouteSwap.SwapDegreeCondition object data.threshold Z P Q) ∧
    (Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z P Q) ∨
      ∃ L : SimpleGraph
          ((Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex ⊕
            Graph.RerouteSwap.SwapInternal object Z P Q),
        Graph.Transplant.IsLinkage (Graph.RerouteSwap.swapPiece object Z P Q) L ∧
          Graph.RerouteSwap.LinkageDoubleUse L) ∧
    ((∀ v, Graph.RerouteSwap.InteriorIn object Z Q v → v ∈ P) →
      Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z P Q)) ∧
    (Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z P Q) →
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z))) ∧
    (Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
      Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z P Q) →
      Graph.RerouteSwap.intCount Z P ≤ Graph.RerouteSwap.intCount Z Q) ∧
    (Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
      Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z P Q) →
      ¬ (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)).LexicographicallySmaller
        object) ∧
    (¬ Graph.HasCycleWithLength data.LengthOK object →
      ∀ cert : Graph.CycleCertificate
          (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z))
          data.LengthOK,
        ∃ (x : Graph.RerouteSwap.RestInternal object Z P)
          (y : Graph.Transplant.TransplantInternal object Z Q), x.1 = y.1 ∧
          (Sum.inr (Sum.inl (Sum.inl x)) :
              (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
                (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)).Vertex) ∈
            cert.walk.support ∧
          (Sum.inr (Sum.inl (Sum.inr y)) :
              (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
                (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)).Vertex) ∈
            cert.walk.support)

/-- **Node `[144a]`: the rerouted swaps of G's pattern supports**, in both
directions (`P → Q` and `Q → P`), at the canonical objects. -/
noncomputable def SameTokenSwapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      SameTokenSwapAt data object Z Xp Xq ∧ SameTokenSwapAt data object Z Xq Xp

/-- **The exact failure of the swap `P → Q`**: valid (no deficient vertex,
linkage-included, `|int Z ∩ P| ≤ |int Z ∩ Q|`); or G's canonical exceptional
vertex exists, lies in `Z` and is deficient in one of the roles rest / copy /
boundary; or a linkage of the swap piece uses a vertex and its copy. -/
def SameTokenSwapExactAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (Z P Q : Finset object.Vertex) : Prop :=
  (Graph.RerouteSwap.swapDeficit object data.threshold Z P Q = none ∧
      Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z P Q) ∧
      Graph.RerouteSwap.intCount Z P ≤ Graph.RerouteSwap.intCount Z Q) ∨
    (∃ v, Graph.RerouteSwap.swapDeficit object data.threshold Z P Q = some v ∧ v ∈ Z ∧
      Graph.RerouteSwap.SwapDeficient object data.threshold Z P Q v) ∨
    ∃ L : SimpleGraph
        ((Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex ⊕
          Graph.RerouteSwap.SwapInternal object Z P Q),
      Graph.Transplant.IsLinkage (Graph.RerouteSwap.swapPiece object Z P Q) L ∧
        Graph.RerouteSwap.LinkageDoubleUse L

/-- **Node `[144a]`: the exact failure of the two rerouted swaps**, and the size
relation when both are valid: equal interior sizes `|int Z ∩ X_p| = |int Z ∩ X_q|`. -/
noncomputable def SameTokenSwapExactStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      SameTokenSwapExactAt data object Z Xp Xq ∧ SameTokenSwapExactAt data object Z Xq Xp ∧
      (Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue (Graph.RerouteSwap.swapPiece object Z Xp Xq)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
        Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z Xp Xq) →
        Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue (Graph.RerouteSwap.swapPiece object Z Xq Xp)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
        Graph.Transplant.LinkageIncluded (Graph.RerouteSwap.swapPiece object Z Xq Xp) →
        Graph.RerouteSwap.intCount Z Xp = Graph.RerouteSwap.intCount Z Xq)

/-- **Node `[144a]`, boundary-free configuration: valid transplants of both
supports force the whole graph.**  If neither support meets `∂Z` and the
gluings of the transplants of `X_q` and of `X_p` into `G − Z` keep the baseline,
then `X_p = X_q = Z`, `∂Z = ∅`, `Z` is every vertex of G, and every vertex of G
outside a pair seed is a cut vertex of G, hence (vertex-deletion shape of G) of
even degree at least `4`; so every degree-`3` vertex lies in both pair seeds,
and if G has no cut vertex both pair seeds are all of `V(G)`. -/
noncomputable def SameTokenU2FreeWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      ((∀ w ∈ Xp, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
        (∀ w ∈ Xq, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
        Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue (Graph.Transplant.transplant object Z Xq)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
        Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue (Graph.Transplant.transplant object Z Xp)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
        Xp = Z ∧ Xq = Z ∧
          (∀ v, v ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) ∧
          (∀ v, v ∈ Z) ∧
          (∀ v, v ∈ Z → v ∉ routing.capacity.activation.pairSeed routing.demands.first →
            ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v)) ∧
          (∀ v, v ∈ Z → v ∉ routing.capacity.activation.pairSeed routing.demands.second →
            ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v)) ∧
          (∀ v, v ∉ routing.capacity.activation.pairSeed routing.demands.first →
            Even (object.degree v) ∧ 4 ≤ object.degree v) ∧
          (∀ v, v ∉ routing.capacity.activation.pairSeed routing.demands.second →
            Even (object.degree v) ∧ 4 ≤ object.degree v) ∧
          (∀ v, object.degree v = 3 →
            v ∈ routing.capacity.activation.pairSeed routing.demands.first ∧
              v ∈ routing.capacity.activation.pairSeed routing.demands.second) ∧
          ((∀ v, Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v)) →
            ∀ v, v ∈ routing.capacity.activation.pairSeed routing.demands.first ∧
              v ∈ routing.capacity.activation.pairSeed routing.demands.second))


/-- **A pair seed is at most `2δ` vertices and two canonical port paths.** -/
def PairSeedCover (data : Parameters) (object : Graph.FiniteObject.{u})
    (seed : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ T P1 P2 : Finset object.Vertex, T.card ≤ 2 * data.threshold ∧
    Graph.PortPathCover.PortPathSupport object data.LengthOK P1 ∧
    Graph.PortPathCover.PortPathSupport object data.LengthOK P2 ∧ seed = T ∪ P1 ∪ P2

/-- **Node `[144a]`: the pair seeds are covered by their canonical port paths.**
At G's canonical routing each pair seed `T(p) ∪ Γ(p) ∪ T(p') ∪ Γ(p')` is at most
`2δ` vertices and the supports of two canonical port paths (a triangular port's
shortest return `R_p` in `G − cx`, an induced path with no chord; an open port's
suppression path `Q_p`), each carrying its chord facts (every chord has an
unaccepted span; every interior degree-`3` vertex has exactly one off-path
edge).  So if every degree-`3` vertex of G lies in both pair seeds, the degree-`3`
vertices of G are covered by at most four canonical port paths and `4δ` vertices,
and (from `5|H| + σ ≤ 2n`) each pair's cover has `3n ≤ 5(|T| + |P₁| + |P₂|)`. -/
noncomputable def SameTokenSeedCoverStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    PairSeedCover data object
        (routing.capacity.activation.pairSeed routing.demands.first) ∧
      PairSeedCover data object
        (routing.capacity.activation.pairSeed routing.demands.second) ∧
      ((∀ v, object.degree v = 3 →
          v ∈ routing.capacity.activation.pairSeed routing.demands.first ∧
            v ∈ routing.capacity.activation.pairSeed routing.demands.second) →
        ∀ v, object.degree v = 3 →
          (by letI : DecidableEq object.Vertex := object.vertices.decEq
              exact ∃ T P1 P2 T' Q1 Q2 : Finset object.Vertex,
                T.card ≤ 2 * data.threshold ∧ T'.card ≤ 2 * data.threshold ∧
                Graph.PortPathCover.PortPathSupport object data.LengthOK P1 ∧
                Graph.PortPathCover.PortPathSupport object data.LengthOK P2 ∧
                Graph.PortPathCover.PortPathSupport object data.LengthOK Q1 ∧
                Graph.PortPathCover.PortPathSupport object data.LengthOK Q2 ∧
                routing.capacity.activation.pairSeed routing.demands.first = T ∪ P1 ∪ P2 ∧
                routing.capacity.activation.pairSeed routing.demands.second = T' ∪ Q1 ∪ Q2 ∧
                v ∈ T ∪ P1 ∪ P2 ∧ v ∈ T' ∪ Q1 ∪ Q2 ∧
                3 * object.vertexCount ≤ 5 * (T.card + P1.card + P2.card) ∧
                3 * object.vertexCount ≤ 5 * (T'.card + Q1.card + Q2.card)))


/-- **Node `[144a]`: the interactions of the canonical port paths.**  At G's canonical
routing the two pair seeds are `T ∪ supp w₁ ∪ supp w₂` and `T' ∪ supp z₁ ∪ supp z₂`
with `w_i`, `z_j` canonical port walks (`PortWalk`: simple, every chord, hub and
closing cycle length unaccepted, one stub per interior cubic vertex), and

* any two segments of two of these walks that are vertex-disjoint and joined by two
  edges (a *rung pair*, parallel or crossed) close a cycle of length
  `|p₂| + |q₂| + 2`, which is not accepted (`RungCycles`; for all six pairs of walks);
* at every cubic vertex interior to two of the walks, the two path edges of one
  walk and the two of the other share an edge (`ShareEdge`; for the four P/Q pairs);
* if every degree-`3` vertex lies in both pair seeds, every neighbour of a hub
  (a vertex of degree `≠ 3`) lies in both pair seeds. -/
noncomputable def SameTokenPathInteractionsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    (by letI : DecidableEq object.Vertex := object.vertices.decEq
        exact ∃ (T T' : Finset object.Vertex) (a1 b1 a2 b2 c1 d1 c2 d2 : object.Vertex)
          (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2)
          (z1 : object.graph.Walk c1 d1) (z2 : object.graph.Walk c2 d2),
          T.card ≤ 2 * data.threshold ∧ T'.card ≤ 2 * data.threshold ∧
          Graph.PortPathCover.PortWalk object data.LengthOK w1 ∧
          Graph.PortPathCover.PortWalk object data.LengthOK w2 ∧
          Graph.PortPathCover.PortWalk object data.LengthOK z1 ∧
          Graph.PortPathCover.PortWalk object data.LengthOK z2 ∧
          routing.capacity.activation.pairSeed routing.demands.first =
            T ∪ w1.support.toFinset ∪ w2.support.toFinset ∧
          routing.capacity.activation.pairSeed routing.demands.second =
            T' ∪ z1.support.toFinset ∪ z2.support.toFinset ∧
          Graph.PathChords.RungCycles data.LengthOK w1 w2 ∧
          Graph.PathChords.RungCycles data.LengthOK z1 z2 ∧
          Graph.PathChords.RungCycles data.LengthOK w1 z1 ∧
          Graph.PathChords.RungCycles data.LengthOK w1 z2 ∧
          Graph.PathChords.RungCycles data.LengthOK w2 z1 ∧
          Graph.PathChords.RungCycles data.LengthOK w2 z2 ∧
          Graph.PathChords.ShareEdge w1 z1 ∧ Graph.PathChords.ShareEdge w1 z2 ∧
          Graph.PathChords.ShareEdge w2 z1 ∧ Graph.PathChords.ShareEdge w2 z2 ∧
          ((∀ v, object.degree v = 3 →
              v ∈ routing.capacity.activation.pairSeed routing.demands.first ∧
                v ∈ routing.capacity.activation.pairSeed routing.demands.second) →
            ∀ h, object.degree h ≠ 3 → ∀ y, object.graph.Adj h y →
              y ∈ routing.capacity.activation.pairSeed routing.demands.first ∧
                y ∈ routing.capacity.activation.pairSeed routing.demands.second))


/-- **The ladder count at one pair seed.**  The seed is `T ∪ supp w₁ ∪ supp w₂` for two
canonical port walks, `|T| ≤ 2δ`, and `|H| ≤ σ`.  When both ports are triangular (the ends of
each walk are adjacent, so each walk is a shortest path of `G − e`) and neither walk uses the
other's end edge:

* if every degree-`3` vertex lies in the seed, `⌊(|wᵢ| − 1)/24⌋ ≤ 16|H| + 12|T| + 30` for
  both walks, `n ≤ |H| + |T| + |w₁| + |w₂| + 2`, hence `n ≤ 769|H| + 577|T| + 1490`;
* if every neighbour of a hub lies in the seed, `σ ≤ (|T| + 5)|H|`. -/
def PairLadderFacts (data : Parameters) (object : Graph.FiniteObject.{u})
    (seed : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
      (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
    T.card ≤ 2 * data.threshold ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w1 ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w2 ∧
    seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset ∧
    (Graph.JointObject.hubs object).card ≤ object.degreeSurplus data.threshold ∧
    (object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
      Graph.LadderG.EndEdgesFree object w1 w2 →
      ((∀ v, object.degree v = 3 → v ∈ seed) →
        Graph.LadderG.LadderCounts object T w1 w2 ∧
        object.vertexCount ≤
          769 * (Graph.JointObject.hubs object).card + 577 * T.card + 1490) ∧
      ((∀ v, object.degree v ≠ 3 → ∀ y, object.graph.Adj v y → y ∈ seed) →
        object.degreeSurplus data.threshold ≤
          (T.card + 5) * (Graph.JointObject.hubs object).card))

/-- **Node `[144a]`: the ladder count of the canonical port walks.**  At G's canonical routing,
for both pair seeds (`PairLadderFacts`).  In the whole-graph arm with both ports of a pair
triangular and neither walk on the other's end edge, the number of hubs is at least
`(n − 577|T| − 1490)/769`: the two shortest-path walks cover the cubic vertices, and a run of
consecutive vertices of one walk joined by their stubs to the other walk, or a bubble between
two common vertices, contains a hub, a vertex joined to a hub, or an end (window lemma
`LadderWindow.window8`, bubble lemma `TwoGeodesics.bubble_exc`, count `ladder_count_geo`). -/
noncomputable def SameTokenLadderCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    PairLadderFacts data object (routing.capacity.activation.pairSeed routing.demands.first) ∧
    PairLadderFacts data object (routing.capacity.activation.pairSeed routing.demands.second)


/-- **The attachment and chain cycles at one pair seed.**  The seed is `T ∪ supp w₁ ∪ supp w₂`
for two canonical port walks, `|T| ≤ 2δ`, and

* (attachment, both walks) a path `r : x ⇝ y` avoiding the segment `wᵢ[i..j]`, with
  `wᵢ(i) ~ x`, `y ~ wᵢ(j)` and `i ≠ j ∨ x ≠ y`, closes a cycle of length `|r| + |i − j| + 2`,
  which is not accepted;
* (chain) routes `r : x ⇝ y`, `r' : x' ⇝ y'` (trivial routes allowed: hubs) off both walks
  and disjoint, and vertex-disjoint segments `w₁[i..i']`, `w₂[j..j']`, with `w₁(i) ~ x`,
  `y ~ w₂(j)`, `w₂(j') ~ x'`, `y' ~ w₁(i')`, close a cycle of length
  `|r| + |r'| + |i − i'| + |j − j'| + 4`, which is not accepted. -/
def PairWalkCycles (data : Parameters) (object : Graph.FiniteObject.{u})
    (seed : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
      (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
    T.card ≤ 2 * data.threshold ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w1 ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w2 ∧
    seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset ∧
    Graph.WalkAttachment.AttachCycles data.LengthOK w1 ∧
    Graph.WalkAttachment.AttachCycles data.LengthOK w2 ∧
    Graph.WalkAttachment.ChainCycles data.LengthOK w1 w2

/-- **Node `[144a]`: the attachment and chain cycles of the canonical port walks.**  At G's
canonical routing, for both pair seeds (`PairWalkCycles`): every route attached to one walk at
two positions, and every chain `w₁ → route → w₂ → route → w₁` through vertex-disjoint
segments, closes a cycle of G, whose length is therefore not accepted
(`WalkAttachment.walk_attach_cycle`, `WalkAttachment.walk_pair_cycle`). -/
noncomputable def SameTokenWalkAttachmentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    PairWalkCycles data object (routing.capacity.activation.pairSeed routing.demands.first) ∧
    PairWalkCycles data object (routing.capacity.activation.pairSeed routing.demands.second)

/-- **Every vertex off one pair seed has a cubic neighbour in `T`.**  The seed is
`T ∪ supp w₁ ∪ supp w₂` for two canonical port walks, `|T| ≤ 2δ`.  In the boundary-free
configuration (the antecedent of `SameTokenU2FreeWholeStatement`) with both ports triangular:
every vertex outside the seed has a degree-`3` neighbour in `T`; hence at most `3|T|`
vertices lie outside the seed, and `n ≤ 4|T| + |w₁| + |w₂| + 2`. -/
def PairSeedAttached (data : Parameters) (object : Graph.FiniteObject.{u})
    (Xp Xq Z seed : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
      (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
    T.card ≤ 2 * data.threshold ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w1 ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w2 ∧
    seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset ∧
    ((∀ w ∈ Xp, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
      (∀ w ∈ Xq, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.Transplant.transplant object Z Xq)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.Transplant.transplant object Z Xp)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
      object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
      (∀ v, v ∉ seed → ∃ t ∈ T, object.graph.Adj v t ∧ object.degree t = 3) ∧
      (object.vertexFinset \ seed).card ≤ 3 * T.card ∧
      object.vertexCount ≤ 4 * T.card + w1.length + w2.length + 2)

/-- **Node `[144a]` (Lean improvement: the separated configuration is empty at G).**  At G's
canonical routing and pinned supports `X_p`, `X_q`, `Z`, for both pair seeds
(`PairSeedAttached`): in the boundary-free configuration with both ports of the pair
triangular, every vertex off the seed has a cubic neighbour in `T`.  (Otherwise such a vertex
`v` is a cut vertex whose neighbours all lie on the two walks; it separates them, every other
off-seed vertex has a `T`-neighbour, every interior walk vertex has a neighbour off both
walks, and the hub-degree bound `|T| + 8` gives `n ≤ 729`, against
`n ≥ C_sp(C_sp + 1) + 9` with `C_sp ≥ 102`.) -/
noncomputable def SameTokenSeparatorExcludedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      PairSeedAttached data object Xp Xq Z
        (routing.capacity.activation.pairSeed routing.demands.first) ∧
      PairSeedAttached data object Xp Xq Z
        (routing.capacity.activation.pairSeed routing.demands.second)

end Hypostructure.Graph.Strategy.Spine
