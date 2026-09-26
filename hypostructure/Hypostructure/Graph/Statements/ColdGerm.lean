import Hypostructure.Graph.Statements.CanonicalCold

/-!
# Statements: the marked neutral germ, nodes `[163]`--`[168]`

The cold facts downstream of node `[406]` (`def:neutral-equal-length-germ`,
tex ~7700) are statements about **one** configuration of the selected residual
`G`: node `[406]`'s marked neutral equal-length germ and its marked canonical
exchange representative, the canonical object `markedNeutralGerm? data G`
(`Statements/CanonicalCold.lean`, the `Classical.choose` of node `[406]`'s
`∃ germ representative`).

Each statement pins that object in the positive form
`∃ marked, markedNeutralGerm? data G = some marked ∧ Q marked`, which is false
(never vacuously true) when node `[406]`'s configuration is absent, and whose
decision partner is `∃ marked, markedNeutralGerm? data G = some marked ∧ ¬ Q marked`:
an exact complement under node `[406]`.

* `lem:neutral-germ-symmetry` (tex ~7715): `[233]`/`[234]`, the split on a genuine
  second strand of the marked configuration.
* `lem:two-strand-check` (tex ~7759) and `lem:symmetric-pair-endpoint`
  (tex ~7785): `[410]`/`[411]`.
* `lem:refined-minimality-swap` (tex ~7732): `[408]`/`[409]` and the size split
  `[244]`/`[245]`.

The universal forms of these lemmas ("every neutral configuration …") are the
contract lemmas; the published facts are their instances at the marked
configuration.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- Node `[163]`, yes-arm: node `[406]`'s marked neutral equal-length
configuration has its marked representative graph-realized as a genuine second
internally-disjoint strand, with the raw paths, attachment stubs, and finite
configuration consumed by `[167]`--`[168]`. -/
noncomputable def GenuineSecondStrandStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∃ config : Graph.TwoStrand.Configuration,
      GenuineSecondStrandConfiguration data object marked.1 marked.2 config

/-- Node `[163]`, no-arm: the same marked configuration has no genuine
symmetric-pair realization, so it enters the canonical-replacement analysis of
`[165]`--`[166]`. -/
noncomputable def CanonicalNeutralConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ¬ ∃ config : Graph.TwoStrand.Configuration,
      GenuineSecondStrandConfiguration data object marked.1 marked.2 config

/-- Node `[167]`, `lem:two-strand-check`: the marked configuration's genuine
second strand is a survivor of the literal finite enumeration. -/
noncomputable def TwoStrandSurvivorStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ∃ config : Graph.TwoStrand.Configuration,
      GenuineSecondStrandConfiguration data object marked.1 marked.2 config ∧
        config ∈ Graph.TwoStrand.survivors data.windowOrder
          (twoStrandEnumerationBound data)

/-- Node `[168]`, `lem:symmetric-pair-endpoint`: the endpoint/interior stub
count excludes the marked configuration's surviving genuine pair. -/
noncomputable abbrev ColdSymmetricPairExcludedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ TwoStrandSurvivorStatement data object

/-- Node `[165]`, `lem:refined-minimality-swap`, at the marked configuration:
if its marked representative `E` differs from the corridor piece `Q`, gluing
`E` into the retained outside context preserves the baseline, target
avoidance, vertex and edge count, and replaces `Q` by a strict predecessor in
the fixed canonical piece order. -/
noncomputable def CanonicalReplacementSwapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    (marked.2 ≠ marked.1.piece.toCanonical →
      let swapped := Graph.glue marked.2.toPiece marked.1.atom.outside
      Graph.MinimumDegreeAtLeast data.threshold swapped ∧
        ¬ Graph.HasCycleWithLength data.LengthOK swapped ∧
        swapped.vertexCount = object.vertexCount ∧
        swapped.edgeCount = object.edgeCount ∧
        Graph.CanonicalPiece.Precedes marked.2 marked.1.piece.toCanonical ∧
        RefinedLexicographicallySmaller swapped object)

/-- Node `[166]`: the marked configuration has trivial canonical replacement,
`E = Q`. -/
noncomputable def CanonicalReplacementTrivialStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    marked.2 = marked.1.piece.toCanonical

/-- `lem:refined-minimality-swap`, size-reducing case (node `[165]`), at the
marked configuration: the canonical representative of its corridor piece has
strictly fewer internal vertices. -/
noncomputable abbrev ColdCanonicalSwapSmallerStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    (germCanonicalRepresentative data marked.1).size <
      marked.1.piece.internalVertexCount

/-- The exact complement at the same marked configuration: its canonical
representative is not smaller — the same-size tie-break of node `[166]`. -/
noncomputable abbrev ColdCanonicalSwapSameSizeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ marked, markedNeutralGerm? data object = some marked ∧
    ¬ (germCanonicalRepresentative data marked.1).size <
      marked.1.piece.internalVertexCount

end Hypostructure.Graph.Strategy.Spine
