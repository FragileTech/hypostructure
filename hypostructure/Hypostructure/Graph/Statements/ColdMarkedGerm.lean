import Hypostructure.Graph.Statements.ColdGerm
import Hypostructure.Graph.SpliceLift
import Hypostructure.Graph.DoubleSuppress
import Hypostructure.Graph.PairRoute

/-!
# Statements: the marked neutral germ measured at G, node `[157]`

`lem:cold-same-interface-table` closes a row that is not handed off by a
strictly smaller proper representative (`TableRow.admissible`,
`def:admissible-rank-quotient`).  The marked neutral equal-length germ of G
(`markedNeutralGerm?`) is measured against exactly that clause.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The marked neutral germ of G, measured against `[157]`'s compression
clause.**  At node `[406]`'s marked configuration `(Q, E)`:

* `Q` is a connected proper support of at most `M_cold` vertices of G, and `E`
  has the internal size of `Q` (equal length);
* the support does not enter G's (F4) handoff registry (its first-failure
  prefix is subcubic), so the row is not handed off;
* the replacement `glue E (G − Z)` is not strictly smaller than G in
  `(|V|, |E|)`: it has the vertex and edge count of G.

So the `admissible` clause of a table row, which would supply the strictly
smaller proper representative, has no witness at the marked germ: `[157]`'s
compression is unattainable there. -/
noncomputable def ColdMarkedGermUncompressedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    marked.1.support.card ≤ Graph.ColdCorridor.exchangeBound data.coldSignature ∧
    marked.2.size = marked.1.piece.internalVertexCount ∧
    ¬ ColdEntersHandoffRegistry data object marked.1.support ∧
    (Graph.glue marked.2.toPiece marked.1.atom.outside).vertexCount =
      object.vertexCount ∧
    (Graph.glue marked.2.toPiece marked.1.atom.outside).edgeCount =
      object.edgeCount ∧
    ¬ (Graph.glue marked.2.toPiece marked.1.atom.outside).LexicographicallySmaller
      object

open Classical in
/-- **F08 at the marked germ: the excision of any path of G spanning its support.**  For every
path `p : a ⇝ b` of G of length at least `2` whose vertex set is the marked germ's support (the
corridor stretch `intervalSupport left right` of an (F5) repeat is one), with `D` its interior:
the excised object (`D` deleted, `a b` joined, strictly smaller) either misses the baseline, or
G has a cycle of length `L + q` with `L` accepted, `L + q` not accepted, and `q = |p| - 1` the
shift of the excised stretch. -/
noncomputable def ColdMarkedGermStretchExcisionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∀ (a b : object.Vertex) (p : object.graph.Walk a b), p.IsPath → 2 ≤ p.length →
      (∀ v, v ∈ p.support ↔ v ∈ marked.1.support) →
      ¬ Graph.MinimumDegreeAtLeast data.threshold
          (Graph.SpliceLift.spliceObject object a b
            (object.vertexFinset.filter (fun v => v ∈ Graph.SpliceLift.interior p))) ∨
        ∃ (L : Nat) (y : object.Vertex) (d : object.graph.Walk y y),
          data.LengthOK L ∧ ¬ data.LengthOK (L + (p.length - 1)) ∧ d.IsCycle ∧
            d.length = L + (p.length - 1)

/-- **The incidence structure of the marked germ's stretch.**  For every path `p` of G spanning
the marked germ's support, every interior vertex `u` has degree exactly `t` (subcubic support
and the baseline), and exactly `t - 2` neighbours besides its two path neighbours: for the
registered `t = 3`, exactly one extra neighbour, a pendant (outside the support) or a chord
(inside it). -/
noncomputable def ColdMarkedGermStretchIncidenceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∀ (a b : object.Vertex) (p : object.graph.Walk a b), p.IsPath →
      (∀ v, v ∈ p.support ↔ v ∈ marked.1.support) →
      ∀ i, 0 < i → i < p.length →
        object.degree (p.getVert i) = data.threshold ∧
          (object.graph.neighborSet (p.getVert i) \
            {p.getVert (i - 1), p.getVert (i + 1)}).ncard = data.threshold - 2

/-- **F08 at every adjacent interior pair of the marked germ's stretch.**  For every path `p` of G
spanning the marked germ's support and every pair of consecutive interior vertices
`u = p_i`, `v = p_{i+1}` with `N(u) = {pl, v, x}` and `N(v) = {u, y, q}` (`pl = p_{i-1}`,
`q = p_{i+2}`; `x` and `y` are the extra neighbours, pendants or chords): either a short-cycle
obstruction to the suppression holds (`pl x` or `y q` already an edge -- a triangle at `u` or at
`v` -- or the two new edges coincide, a `C4` through `u v`), or G has a cycle of length
`Lk + j` with `Lk` accepted, `j ∈ {1, 2}`, and `Lk + j` not accepted. -/
noncomputable def ColdMarkedGermPairSuppressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∀ (a b : object.Vertex) (p : object.graph.Walk a b), p.IsPath →
      (∀ v, v ∈ p.support ↔ v ∈ marked.1.support) →
      ∀ i, 0 < i → i + 1 < p.length → ∀ x y : object.Vertex,
        (∀ z, object.graph.Adj (p.getVert i) z ↔
          z = p.getVert (i + 1) ∨ z = p.getVert (i - 1) ∨ z = x) →
        (∀ z, object.graph.Adj (p.getVert (i + 1)) z ↔
          z = p.getVert i ∨ z = y ∨ z = p.getVert (i + 2)) →
        x ≠ p.getVert (i - 1) → x ≠ p.getVert (i + 1) →
        y ≠ p.getVert (i + 2) → y ≠ p.getVert i →
        ((object.graph.Adj (p.getVert (i - 1)) x ∨ object.graph.Adj y (p.getVert (i + 2)) ∨
            s(p.getVert (i - 1), x) = s(y, p.getVert (i + 2))) ∨
          ∃ (Lk j : Nat) (w : object.Vertex) (d : object.graph.Walk w w),
            data.LengthOK Lk ∧ (j = 1 ∨ j = 2) ∧ ¬ data.LengthOK (Lk + j) ∧ d.IsCycle ∧
              d.length = Lk + j)

/-- **The Mersenne paths of a suppressed pair.**  For the configuration `u v` with `N(u) = {v, pl,
x}`, `N(v) = {u, y, q}`: an accepted length `Lk` and either a path `pl ⇝ x` of length `Lk - 1`
avoiding `u, v` (Mersenne when `Lk = 2^k`), or a path `y ⇝ q` of length `Lk - 1` avoiding `u, v`, or
a cycle of length `Lk + 2` through the four edges `u pl`, `u x`, `v y`, `v q`; the lengths
`Lk + 1` (resp. `Lk + 2`) are not accepted. -/
def PairMersenne (data : Parameters) (object : Graph.FiniteObject.{u})
    (u v pl x y q : object.Vertex) : Prop :=
  ∃ Lk : Nat, data.LengthOK Lk ∧
    ((∃ M : object.graph.Walk pl x, M.IsPath ∧ u ∉ M.support ∧ v ∉ M.support ∧
        M.length + 1 = Lk ∧ ¬ data.LengthOK (Lk + 1)) ∨
      (∃ M : object.graph.Walk y q, M.IsPath ∧ u ∉ M.support ∧ v ∉ M.support ∧
        M.length + 1 = Lk ∧ ¬ data.LengthOK (Lk + 1)) ∨
      (∃ (z : object.Vertex) (d : object.graph.Walk z z), d.IsCycle ∧ d.length = Lk + 2 ∧
        ¬ data.LengthOK (Lk + 2) ∧ s(u, pl) ∈ d.edges ∧ s(u, x) ∈ d.edges ∧
        s(v, y) ∈ d.edges ∧ s(v, q) ∈ d.edges))

/-- **Every consecutive interior pair of the marked germ's stretch carries a Mersenne path or a
double cycle** (`PairMersenne`), unless a triangle or `C4` obstruction holds. -/
noncomputable def ColdMarkedGermPairMersenneStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∀ (a b : object.Vertex) (p : object.graph.Walk a b), p.IsPath →
      (∀ v, v ∈ p.support ↔ v ∈ marked.1.support) →
      ∀ i, 0 < i → i + 1 < p.length → ∀ x y : object.Vertex,
        (∀ z, object.graph.Adj (p.getVert i) z ↔
          z = p.getVert (i + 1) ∨ z = p.getVert (i - 1) ∨ z = x) →
        (∀ z, object.graph.Adj (p.getVert (i + 1)) z ↔
          z = p.getVert i ∨ z = y ∨ z = p.getVert (i + 2)) →
        x ≠ p.getVert (i - 1) → x ≠ p.getVert (i + 1) →
        y ≠ p.getVert (i + 2) → y ≠ p.getVert i →
        ((object.graph.Adj (p.getVert (i - 1)) x ∨ object.graph.Adj y (p.getVert (i + 2)) ∨
            s(p.getVert (i - 1), x) = s(y, p.getVert (i + 2))) ∨
          PairMersenne data object (p.getVert i) (p.getVert (i + 1)) (p.getVert (i - 1)) x y
            (p.getVert (i + 2)))

open Classical in
/-- **Chords of the marked germ's stretch.**  For every path `p` of G spanning the marked
germ's support and vertices `w1` before `w2` on it that are adjacent although their subpath has
length `>= 2`: the subpath and the chord close a cycle of G of length `span + 1`, which is
therefore not accepted. -/
noncomputable def ColdMarkedGermChordSpanStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∀ (a b : object.Vertex) (p : object.graph.Walk a b), p.IsPath →
      (∀ v, v ∈ p.support ↔ v ∈ marked.1.support) →
      ∀ (w1 w2 : object.Vertex) (h2 : w2 ∈ p.support)
        (h1 : w1 ∈ (p.takeUntil w2 h2).support), object.graph.Adj w1 w2 →
        2 ≤ ((p.takeUntil w2 h2).dropUntil w1 h1).length →
        ¬ data.LengthOK (((p.takeUntil w2 h2).dropUntil w1 h1).length + 1)

end Hypostructure.Graph.Strategy.Spine
