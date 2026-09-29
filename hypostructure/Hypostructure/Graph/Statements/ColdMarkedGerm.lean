import Hypostructure.Graph.Statements.ColdGerm
import Hypostructure.Graph.SpliceLift

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

end Hypostructure.Graph.Strategy.Spine
