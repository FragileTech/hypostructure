import Hypostructure.Graph.Statements.SameTokenPair
import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.PortPathCover
import Hypostructure.Graph.WalkWindows

/-!
# Statements: induced windows along the canonical port walks; exchange at `P₀`
(`[144a]` exchange attack, Lean improvement)

Facts about G at G's canonical routing (`canonicalSameTokenRouting`) and G's canonical maximum
window packing `P₀ = canonicalWindowPacking` (window order `L = windowOrder = 13`):

* `SameTokenWalkWindowsStatement` (key 9850): for both pair seeds, ONE walk witness
  `T ∪ supp w₁ ∪ supp w₂` (canonical port walks, `|T| ≤ 2δ`) such that for each triangular walk
  (`b ~ a`: a shortest `a`–`b` path of `G − ab`, `GeodesicDetours`) every `L`-segment other
  than the whole walk induces a window and meets a member of `P₀`; `⌊|wᵢ|/L⌋ ≤ ν`; for two
  triangular walks with disjoint supports `⌊|w₁|/L⌋ + ⌊|w₂|/L⌋ ≤ ν`; and the exchange at `P₀`
  for these segments (`PairWalkWindows`);
* `SameTokenWalkExchangeStatement` (key 9851): the exchange at `P₀` for every family of windows
  of G: for `S ⊆ P₀` and a packing `Q` avoiding every member of `P₀` outside `S`, `|Q| ≤ |S|`;
  in particular no member `X ∈ P₀` has two disjoint windows avoiding every other member.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- A **window segment of a triangular walk**: `b ~ a`, and `q` is the `L` consecutive
vertices `w(s), …, w(s + L − 1)` of `w`, other than the whole walk. -/
def TriSegment (object : Graph.FiniteObject.{u}) (L : Nat) {a b : object.Vertex}
    (w : object.graph.Walk a b) (q : Finset object.Vertex) : Prop :=
  object.graph.Adj b a ∧ ∃ s, s + L ≤ w.length + 1 ∧ ¬ (s = 0 ∧ s + L = w.length + 1) ∧
    q = Graph.WalkWindows.seg w s L

/-- **The windows and the exchange of the two port walks at one pair seed.**  The seed is
`T ∪ supp w₁ ∪ supp w₂` for two canonical port walks, `|T| ≤ 2δ`; with `L` the window order,
`P₀` the canonical packing and `ν` the packing number:

* every window segment of a triangular walk (`TriSegment`) induces a window and meets `P₀`;
* `⌊|wᵢ|/L⌋ ≤ ν` for a triangular walk; `⌊|w₁|/L⌋ + ⌊|w₂|/L⌋ ≤ ν` for two triangular walks
  with disjoint supports;
* (exchange) for `S ⊆ P₀` and pairwise disjoint window segments `Q` avoiding every member of
  `P₀` outside `S`, `|Q| ≤ |S|`; two disjoint window segments never both avoid every member
  of `P₀` but one. -/
def PairWalkWindows (data : Parameters) (object : Graph.FiniteObject.{u})
    (seed : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
      (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
    T.card ≤ 2 * data.threshold ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w1 ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w2 ∧
    seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset ∧
    (∀ q, TriSegment object data.windowOrder w1 q ∨ TriSegment object data.windowOrder w2 q →
      object.InducesWindow data.windowOrder q ∧
        ∃ X ∈ canonicalWindowPacking data object, ¬ Disjoint q X) ∧
    (object.graph.Adj b1 a1 →
      w1.length / data.windowOrder ≤ object.windowPackingNumber data.windowOrder) ∧
    (object.graph.Adj b2 a2 →
      w2.length / data.windowOrder ≤ object.windowPackingNumber data.windowOrder) ∧
    (object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
      (∀ v, v ∈ w1.support → v ∉ w2.support) →
      w1.length / data.windowOrder + w2.length / data.windowOrder ≤
        object.windowPackingNumber data.windowOrder) ∧
    (∀ S ⊆ canonicalWindowPacking data object, ∀ Q : Finset (Finset object.Vertex),
      (∀ q ∈ Q, TriSegment object data.windowOrder w1 q ∨
        TriSegment object data.windowOrder w2 q) →
      (∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → Disjoint q q') →
      (∀ q ∈ Q, ∀ p ∈ canonicalWindowPacking data object, p ∉ S → Disjoint q p) →
      Q.card ≤ S.card) ∧
    (∀ X ∈ canonicalWindowPacking data object, ∀ q1 q2 : Finset object.Vertex,
      (TriSegment object data.windowOrder w1 q1 ∨ TriSegment object data.windowOrder w2 q1) →
      (TriSegment object data.windowOrder w1 q2 ∨ TriSegment object data.windowOrder w2 q2) →
      Disjoint q1 q2 →
      ¬ ((∀ p ∈ canonicalWindowPacking data object, p ≠ X → Disjoint q1 p) ∧
        (∀ p ∈ canonicalWindowPacking data object, p ≠ X → Disjoint q2 p)))

/-- **Node `[144a]` (Lean improvement): induced windows along the canonical port walks.**  At
G's canonical routing, for both pair seeds, one walk witness carrying the window, counting and
exchange facts of `PairWalkWindows`. -/
noncomputable def SameTokenWalkWindowsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    PairWalkWindows data object (routing.capacity.activation.pairSeed routing.demands.first) ∧
    PairWalkWindows data object (routing.capacity.activation.pairSeed routing.demands.second)

/-- **Node `[144a]` (Lean improvement): the exchange at G's canonical packing `P₀`.**  For
`S ⊆ P₀` and a packing `Q` of windows of G each disjoint from every member of `P₀` outside
`S`: `|Q| ≤ |S|` (`(P₀ ∖ S) ∪ Q` is a packing and `P₀` is maximum).  In particular no member
`X ∈ P₀` has two disjoint windows avoiding every other member of `P₀`. -/
noncomputable def SameTokenWalkExchangeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∀ S ⊆ canonicalWindowPacking data object, ∀ Q : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder Q →
    (∀ q ∈ Q, ∀ p ∈ canonicalWindowPacking data object, p ∉ S → Disjoint q p) →
    Q.card ≤ S.card) ∧
  (∀ X ∈ canonicalWindowPacking data object, ∀ q1 q2 : Finset object.Vertex,
    object.InducesWindow data.windowOrder q1 → object.InducesWindow data.windowOrder q2 →
    Disjoint q1 q2 →
    ¬ ((∀ p ∈ canonicalWindowPacking data object, p ≠ X → Disjoint q1 p) ∧
      (∀ p ∈ canonicalWindowPacking data object, p ≠ X → Disjoint q2 p)))

end Hypostructure.Graph.Strategy.Spine
