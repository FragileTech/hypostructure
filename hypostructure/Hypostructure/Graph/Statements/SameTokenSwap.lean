import Hypostructure.Graph.Statements.SameTokenPair
import Hypostructure.Graph.RerouteSwap
import Hypostructure.Graph.ReadingExactness
import Hypostructure.Graph.U2FreeWhole

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
outside a pair seed is a cut vertex of G. -/
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
            ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v)))

end Hypostructure.Graph.Strategy.Spine
