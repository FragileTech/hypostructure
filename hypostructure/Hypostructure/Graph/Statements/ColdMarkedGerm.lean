import Hypostructure.Graph.Statements.ColdGerm

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

end Hypostructure.Graph.Strategy.Spine
