import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.DeclaredRankQuotient

/-!
# The curvature target-rank of a region

`def:curvature-target-rank` computes `r_Ω` over the raw internal length-two
curvature tests of an atom, against *the* system of admissible rank quotients
that are functional on that family.  This module builds that system, so `r_Ω`
is a number and not a quantifier.

Every clause is the manuscript's, at the framework object the manuscript names.

* A quotient lives on a connected **determination support** `Z` that carries
  the coordinates under discussion, and its realizations are the boundaried
  graphs that can occupy `Z`'s place — `BoundaryPiece` at the support's own cut
  interface, which is what `def:curvature-target-dependence` means by "a
  realization is a `T`-boundaried support whose exact response profile maps to
  the same quotient data `Q` under `q`".
* `def:target-complete-quotient`: every identification the quotient makes
  preserves (a) the boundary degree profile and (b) the target predicate after
  gluing to every `T`-boundaried context.  Both are stated at
  `BoundaryPiece.boundaryDegreeProfile` and at `glue` against every
  `OutsideContext`, the framework's own gluing.
* `def:admissible-rank-quotient`, proper clause: at `Z ⊊ G` a rank-reducing
  quotient supplies a strictly smaller proper representative.  The manuscript
  says of it that "the five defining properties of a proper representative are
  exactly the five hypotheses of the replacement lemma `lem:replacement` for
  the support `Z`", so the clause *is*
  `InterfaceReplacement.ReplacementSupport`, which is the hypothesis
  `InterfaceReplacement.not_replacementSupport` refutes at a minimal
  counterexample.
* `def:admissible-rank-quotient`, closed clause: at `Z = G` a rank-reducing
  quotient supplies a strictly smaller admissible closed representative `H` —
  finite, simple, meeting the baseline, with
  `profile_∅(H) ⊆ profile_∅(G)`.  With an empty boundary the only context is
  the empty one, so that inclusion is `Target H → Target G`, which is the
  manuscript's own reading of it ("a dyadic cycle in `H` would add the
  corresponding empty-context target event to `profile_∅(H)`, impossible
  because `profile_∅(G)` contains no such event").

Nothing here is specialized to one manuscript: the baseline and the target are
parameters, and the module never mentions a window, a packing, or a numeral.
-/

namespace Hypostructure.Graph

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

namespace FiniteObject

/-- The declared support of a raw internal curvature test: the wedge's centre
together with the two neighbours it joins (`def:declared-coordinate-signature`,
clause (D4) — a raw curvature coordinate is indexed by its internal length-two
wedge, and its support is that wedge). -/
noncomputable def internalWedgeSupport {object : FiniteObject.{u}}
    {region : Finset object.Vertex} (test : object.InternalWedge region) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact insert test.1 test.2.1

end FiniteObject

/-- **`def:admissible-rank-quotient` on the raw curvature tests of a region.**

`r_Ω`'s quotients are the declared-family quotients of
`Graph.DeclaredQuotient` at one particular family: the raw internal length-two
wedges of the region, each carried on its own wedge as clause (D4) of
`def:declared-coordinate-signature` declares.  There is no second structure:
this abbreviation is that instance, so every field, every completeness clause
and the routing `localize` are the ones proved once in
`Graph/DeclaredRankQuotient`. -/
abbrev CurvatureQuotient (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (region : Finset object.Vertex) : Type (u + 2) :=
  DeclaredQuotient Baseline Target object (object.internalWedgeFamily region)
    (FiniteObject.internalWedgeSupport (region := region))

namespace FiniteObject

/-- **The admissible quotient system of `def:curvature-target-rank`.**

`def:functional-rank-quotient`'s closing sentence: "the admissible quotient
system used to compute target-rank consists only of admissible rank quotients
that are functional on the coordinate family under discussion."  Membership is
exactly that conjunction. -/
noncomputable def curvatureQuotientSystem
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (region : Finset object.Vertex) :
    Core.TargetRank.QuotientSystem.{u, u + 1} (object.InternalWedge region)
      (object.internalWedgeFamily region) :=
  declaredQuotientSystem Baseline Target object (object.internalWedgeFamily region)
    (FiniteObject.internalWedgeSupport (region := region))

/-- **`r_Ω(X)`**: the curvature target-rank of a region — the maximum size of a
subfamily of its raw internal curvature tests that survives every functional
admissible rank quotient. -/
noncomputable def curvatureTargetRank
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (region : Finset object.Vertex) : Nat :=
  Core.TargetRank.targetRank (curvatureQuotientSystem Baseline Target object region)

/-- `r_Ω` is the rank calculus at the manuscript's own system, definitionally. -/
theorem curvatureTargetRank_eq_targetRank
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (region : Finset object.Vertex) :
    curvatureTargetRank Baseline Target object region =
      Core.TargetRank.targetRank
        (curvatureQuotientSystem Baseline Target object region) := rfl

/-- `r_Ω(X) ≤ W₂(X)`: the rank never exceeds the number of raw tests. -/
theorem curvatureTargetRank_le_internalWedgeCount
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (region : Finset object.Vertex) :
    curvatureTargetRank Baseline Target object region ≤
      object.internalWedgeCount region := by
  rw [← object.internalWedgeFamily_card region]
  exact Core.TargetRank.targetRank_le_card _

end FiniteObject

end Hypostructure.Graph
