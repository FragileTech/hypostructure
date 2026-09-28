import Hypostructure.Graph.Statements.SurplusPairRouting
import Hypostructure.Graph.ReadingProfiles

/-!
# Statements: G's same-token pattern pair, made exact

Node `[144]` (`lem:same-token-bottleneck-routing`, tex 5585-5620) routes G's
canonical homogeneous pattern at G's canonical routing
(`canonicalSameTokenRouting`); node `[144a]` carries the unresolved pair of
the paper error at `[144]` (tex 5589, 5594).  The statements below are facts
about G at those canonical objects:

* the two pattern supports `X_p`, `X_q` of the canonical routing are the
  canonical selections of their pair seeds, connected, with two distinct
  vertices each (`SameTokenPatternSupportsStatement`);
* the swap of `ret_q` by `ret_p` in G, in both directions, is G itself or
  loses the baseline at a tight endpoint of a private edge
  (`SameTokenPatternSwapStatement`);
* on `[144a]`, the exact partition of the unresolved pair at the canonical
  support `Z = select?(X_p ∪ X_q)` into three regions with their constraints
  (`SameTokenPairPartitionStatement`): (U1) a separating boundary count;
  (U2-free) equal counts and neither support on `∂Z`; (U2-shared) equal counts
  and a boundary vertex in both supports.  The fourth region (U2-onesided:
  equal counts, one support on `∂Z` and no shared boundary vertex) is empty
  at G.

The reading count `c_X(b)` is `Graph.ReadingProfiles.readingCount`.  This
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The declared support `X_π` of a pair `π` at G's canonical routing. -/
noncomputable abbrev sameTokenPairSupport {data : Parameters}
    {object : Graph.FiniteObject.{u}} (routing : SameTokenRouting data object)
    (pair : Finset (object.Vertex × object.Vertex)) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Graph.DeclaredSignature.Coordinate.support (sameTokenPairCoordinate routing.capacity pair)

/-- **The pattern supports of G's canonical routing.**  G's canonical routing
exists, and each of its two pattern pairs `π ∈ {p, q}` has declared support
`X_π = select?(seed(π))`, the canonical selection of its pair seed; `X_π` is
connected and has two distinct vertices. -/
noncomputable def SameTokenPatternSupportsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∀ pair, (pair = routing.demands.first ∨ pair = routing.demands.second) →
      Graph.CanonicalSupport.select? object (routing.capacity.activation.pairSeed pair) =
          some (sameTokenPairSupport routing pair) ∧
        Graph.SupportComponents.Connected.ConnectedOn object
          (sameTokenPairSupport routing pair) ∧
        ∃ a b, a ≠ b ∧ a ∈ sameTokenPairSupport routing pair ∧
          b ∈ sameTokenPairSupport routing pair

/-- The swap of `ret_Y` by `ret_X` in G, exactly: every edge of `G[Y]` lies in
`G[X]` (the swap object is G), or some private edge `xy` of `G[Y]` has an
endpoint `w` whose degree in `G − (E(G[Y]) ∖ E(G[X]))` is at most `δ − 1`, so
the swap object loses the baseline. -/
def SameTokenSwapExact (data : Parameters) (object : Graph.FiniteObject.{u})
    (X Y : Finset object.Vertex) : Prop :=
  (∀ x y, object.graph.Adj x y → x ∈ Y → y ∈ Y → x ∈ X ∧ y ∈ X) ∨
    ∃ x y, object.graph.Adj x y ∧ x ∈ Y ∧ y ∈ Y ∧ ¬ (x ∈ X ∧ y ∈ X) ∧
      ∃ w, (w = x ∨ w = y) ∧
        (Graph.ReadingProfiles.spanning object
            (Graph.ReadingProfiles.swapGraph X Y)).degree w + 1 ≤ data.threshold ∧
        ¬ Graph.MinimumDegreeAtLeast data.threshold
          (Graph.ReadingProfiles.spanning object (Graph.ReadingProfiles.swapGraph X Y))

/-- **The swaps of G's two pattern readings.**  At G's canonical routing, the
swap of `ret_q` by `ret_p` and the swap of `ret_p` by `ret_q` are each exact
in the sense of `SameTokenSwapExact`. -/
noncomputable def SameTokenPatternSwapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    SameTokenSwapExact data object (sameTokenPairSupport routing routing.demands.first)
        (sameTokenPairSupport routing routing.demands.second) ∧
      SameTokenSwapExact data object (sameTokenPairSupport routing routing.demands.second)
        (sameTokenPairSupport routing routing.demands.first)

open Classical in
/-- The separating region (U1) at a boundary vertex `b` of `Z`: the counts of
`X_p` and `X_q` at `b` differ, both are at most `deg b − 1`, and one support
`X`, say with seed `S`, has `c_X(b) > 0`, retains `b` with a neighbour in `X`,
and either `b` is adjacent to `S` or `X ∖ N(b)` is disconnected. -/
def SameTokenSeparatingAt (object : Graph.FiniteObject.{u})
    (Z Xp Xq seedP seedQ : Finset object.Vertex)
    (b : (Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex) : Prop :=
  Graph.ReadingProfiles.readingCount Z Xp b ≠ Graph.ReadingProfiles.readingCount Z Xq b ∧
    Graph.ReadingProfiles.readingCount Z Xp b + 1 ≤ object.degree b.1 ∧
    Graph.ReadingProfiles.readingCount Z Xq b + 1 ≤ object.degree b.1 ∧
    ((0 < Graph.ReadingProfiles.readingCount Z Xp b ∧ b.1 ∈ Xp ∧
        (∃ w ∈ Xp, object.graph.Adj b.1 w) ∧
        ((∃ w ∈ seedP, object.graph.Adj b.1 w) ∨
          ¬ Graph.SupportComponents.Connected.ConnectedOn object
            (Xp.filter fun w => ¬ object.graph.Adj b.1 w))) ∨
      (0 < Graph.ReadingProfiles.readingCount Z Xq b ∧ b.1 ∈ Xq ∧
        (∃ w ∈ Xq, object.graph.Adj b.1 w) ∧
        ((∃ w ∈ seedQ, object.graph.Adj b.1 w) ∨
          ¬ Graph.SupportComponents.Connected.ConnectedOn object
            (Xq.filter fun w => ¬ object.graph.Adj b.1 w))))

open Classical in
/-- The equal-count region (U2) at `Z`: all boundary counts agree; every
boundary vertex of `X_p` with a neighbour in `X_p` lies in `X_q` and
conversely; the readings are context-equivalent; they have the same simple
`a`–`b` path lengths between any two distinct boundary vertices; and either
(U2-free) neither support meets `∂Z`, every boundary vertex of `Z` lies
outside `X_p ∪ X_q` and is a cut vertex of `Z`, and every neighbour of
`X_p ∪ X_q` lies in `Z`, or (U2-shared) some boundary vertex lies in both
supports. -/
def SameTokenEqualCountsAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (Z Xp Xq : Finset object.Vertex) : Prop :=
  (∀ b, Graph.ReadingProfiles.readingCount Z Xp b = Graph.ReadingProfiles.readingCount Z Xq b) ∧
    (∀ b : (Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex, b.1 ∈ Xp →
      ∀ w ∈ Xp, object.graph.Adj b.1 w → b.1 ∈ Xq) ∧
    (∀ b : (Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex, b.1 ∈ Xq →
      ∀ w ∈ Xq, object.graph.Adj b.1 w → b.1 ∈ Xp) ∧
    Graph.Response.ContextEquivalent (Graph.HasCycleWithLength data.LengthOK)
      (Strategy.InterfaceReplacement.SupportAtom.retainedPiece object Z Xp)
      (Strategy.InterfaceReplacement.SupportAtom.retainedPiece object Z Xq) ∧
    (∀ a b : (Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex, a ≠ b →
      ∀ n : Nat,
        (∃ p : (Strategy.InterfaceReplacement.SupportAtom.retainedPiece object Z Xp).graph.Walk
            (.inl a) (.inl b), p.IsPath ∧ p.length = n) ↔
        (∃ p : (Strategy.InterfaceReplacement.SupportAtom.retainedPiece object Z Xq).graph.Walk
            (.inl a) (.inl b), p.IsPath ∧ p.length = n)) ∧
    (((∀ w ∈ Xp, w ∉ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) ∧
        (∀ w ∈ Xq, w ∉ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) ∧
        (∀ b : (Strategy.InterfaceReplacement.SupportAtom.boundary object Z).Vertex,
          b.1 ∉ Xp ∧ b.1 ∉ Xq ∧
            ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase b.1)) ∧
        (∀ w n, (w ∈ Xp ∨ w ∈ Xq) → object.graph.Adj w n → n ∈ Z)) ∨
      ∃ b ∈ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z, b ∈ Xp ∧ b ∈ Xq)

/-- **Node `[144a]`: the exact partition of G's unresolved pattern pair.**  At
G's canonical routing, with pattern coordinates `r_p ≠ r_q`, their
supports `X_p = select?(seed(p))`, `X_q = select?(seed(q))` and the canonical
support `Z = select?(X_p ∪ X_q)`: `X_p, X_q ⊆ Z`, `Z` is connected, and
exactly the regions (U1) (`SameTokenSeparatingAt` at some boundary vertex of
`Z`) or (U2-free)/(U2-shared) (`SameTokenEqualCountsAt`) occur; the one-sided
region is empty. -/
noncomputable def SameTokenPairPartitionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex,
      Xp = sameTokenPairSupport routing routing.demands.first ∧
      Xq = sameTokenPairSupport routing routing.demands.second ∧
      sameTokenPairCoordinate routing.capacity routing.demands.first ≠
        sameTokenPairCoordinate routing.capacity routing.demands.second ∧
      Graph.CanonicalSupport.select? object
          (routing.capacity.activation.pairSeed routing.demands.first) = some Xp ∧
      Graph.CanonicalSupport.select? object
          (routing.capacity.activation.pairSeed routing.demands.second) = some Xq ∧
      Graph.CanonicalSupport.select? object (Xp ∪ Xq) = some Z ∧
      Xp ⊆ Z ∧ Xq ⊆ Z ∧ Graph.SupportComponents.Connected.ConnectedOn object Z ∧
      ((∃ b, SameTokenSeparatingAt object Z Xp Xq
            (routing.capacity.activation.pairSeed routing.demands.first)
            (routing.capacity.activation.pairSeed routing.demands.second) b) ∨
        SameTokenEqualCountsAt data object Z Xp Xq)

end Hypostructure.Graph.Strategy.Spine
