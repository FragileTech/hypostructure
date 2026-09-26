import Hypostructure.Graph.Statements.CanonicalTypeA

/-!
# The dominant rooted type of `R₀` (nodes `[49]`--`[52]`)

`lem:dominant-type` (tex ~9595) produces, on the structurally repetitive
radius-two type coordinate of the remainder `R₀` of the fixed maximum packing
`P₀`, one dominant rooted type: a set `D` of subcubic remainder vertices with a
common radius-two type, covering all but `2T(n)` vertices of `R₀`, and a root
in it.  `prop:two-budget` (b) then tests whether *that* root carries an
internal length-two wedge, and `lem:translates-independent` (tex ~9638) is
applied to that same type at radius two.

A fact value is data-free, so the dominant pair is named here as a canonical
object of `G`: `canonicalDominantRootedType? data G` is the `Classical.choose`
of node `[431]`'s `∃ dominant root`-body at `P₀` (`canonicalChoice`, the design
of `Statements/Canonical*`).  The wedge decision `[428]`/`[432]` splits on that
one pair; neither arm re-chooses it.  This module imports no strategy, row or
vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The `∃ dominant root`-body of `lem:dominant-type` at the fixed maximum
packing `P₀`: `dominant ⊆ subcubic(R₀)`, `root ∈ dominant`,
`|R₀| ≤ |dominant| + 2T(n)`, and every dominant vertex has the root's
radius-two rooted type on the subcubic support. -/
def DominantRootedTypeSpec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dominantRoot : Finset object.Vertex × object.Vertex) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let subcubic := remainderSubcubicSupport data object packing
  exact ∃ dominantSubset : dominantRoot.1 ⊆ subcubic,
    ∃ rootMem : dominantRoot.2 ∈ dominantRoot.1,
      support.card ≤ dominantRoot.1.card +
          2 * data.surplusThreshold object.vertexCount ∧
        ∀ vertex, ∀ vertexMem : vertex ∈ dominantRoot.1,
          object.rootedLocalTypeCode subcubic 2
              ⟨dominantRoot.2, dominantSubset rootMem⟩ =
            object.rootedLocalTypeCode subcubic 2
              ⟨vertex, dominantSubset vertexMem⟩

/-- **The dominant rooted type of `R₀`**: `Classical.choose` of node `[431]`'s
`∃ dominant root` at `P₀`, or `none` when no dominant type exists. -/
noncomputable def canonicalDominantRootedType? (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Finset object.Vertex × object.Vertex) :=
  canonicalChoice (DominantRootedTypeSpec data object)

theorem canonicalDominantRootedType?_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (h : ∃ dominantRoot, DominantRootedTypeSpec data object dominantRoot) :
    ∃ dominantRoot, canonicalDominantRootedType? data object = some dominantRoot ∧
      DominantRootedTypeSpec data object dominantRoot :=
  canonicalChoice_spec h

theorem canonicalDominantRootedType?_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    {dominantRoot : Finset object.Vertex × object.Vertex}
    (h : canonicalDominantRootedType? data object = some dominantRoot) :
    DominantRootedTypeSpec data object dominantRoot :=
  canonicalChoice_spec_of_eq_some h

theorem canonicalDominantRootedType?_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} :
    canonicalDominantRootedType? data object = none ↔
      ¬ ∃ dominantRoot, DominantRootedTypeSpec data object dominantRoot :=
  canonicalChoice_eq_none_iff

/-- Node `[431]`, `lem:dominant-type` (tex ~9595): on the full-rank remainder
`R₀` of `P₀` (`r_Ω(R₀) = W₂(R₀)`), the canonical dominant rooted type exists. -/
noncomputable abbrev DominantRootedTypeSchema
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  let packing := canonicalWindowPacking data object;
  remainderCurvatureTargetRank data object packing =
      object.internalWedgeCount (object.remainderSupport packing) ∧
    ∃ dominantRoot, canonicalDominantRootedType? data object = some dominantRoot

/-- Node `[428]`, `prop:two-budget` (b), yes: the root of the canonical dominant
type contains an internal length-two wedge. -/
noncomputable abbrev DominantRootedWedgeTypeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ dominantRoot, canonicalDominantRootedType? data object = some dominantRoot ∧
    DominantRootWedgeClause object
      (remainderSubcubicSupport data object (canonicalWindowPacking data object))
      dominantRoot.2

/-- Node `[432]`, `prop:two-budget` (b), no: the root of the same canonical
dominant type contains no internal length-two wedge; the manuscript makes no
translate-rank claim and passes this arm to the large-budget analysis. -/
noncomputable abbrev DominantRootedTypeWedgeFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ dominantRoot, canonicalDominantRootedType? data object = some dominantRoot ∧
    ¬ DominantRootWedgeClause object
      (remainderSubcubicSupport data object (canonicalWindowPacking data object))
      dominantRoot.2

/-- Nodes `[51]`--`[52]`, `lem:translates-independent` (tex ~9638) at radius
two, applied to the canonical dominant type with a root wedge: a maximal
`4`-separated family of translates has disjoint radius-two balls and its
radius-four balls cover the dominant centres, so full obstruction rank gives
`|R₀| ≤ (1 + δ((δ−1)^4 − 1))·r_Ω(R₀) + 2T(n)`, the finite form of
`r_Ω(R) ≥ c_2|R| − o(|R|)` (the presentation has `δ = 3`). -/
noncomputable abbrev IndependentObstructionTranslatesStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  let packing := canonicalWindowPacking data object;
  (object.remainderSupport packing).card ≤
    (1 + data.threshold * ((data.threshold - 1) ^ (2 * 2) - 1)) *
        remainderCurvatureTargetRank data object packing +
      2 * data.surplusThreshold object.vertexCount

end Hypostructure.Graph.Strategy.Spine
