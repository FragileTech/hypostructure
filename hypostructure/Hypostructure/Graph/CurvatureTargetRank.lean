import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Core.TargetRank

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

An admissible rank quotient for the family `𝒲₂(region)`: a quotient of the
exact response profile of a connected determination support carrying the
family, which is target-complete, and which — when it is rank-reducing on the
family — supplies the representative its scope requires.

The two representative clauses are stated against the scope split the framework
already owns (`SupportAtom.classifyScope`): a support with a vertex outside it
is proper, and one covering every vertex is the closed whole graph. -/
structure CurvatureQuotient (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (region : Finset object.Vertex) :
    Type (u + 2) where
  /-- The connected determination support `Z` of the quotient. -/
  support : Finset object.Vertex
  /-- `Z` is connected: `def:admissible-rank-quotient` quantifies over families
  "carried by a connected support `X ⊆ G`". -/
  connected : SupportComponents.Connected.ConnectedOn object support
  /-- `Z` carries the coordinates under discussion. -/
  carries : ∀ test ∈ object.internalWedgeFamily region,
    FiniteObject.internalWedgeSupport test ⊆ support
  /-- The labelled coordinates of the quotient datum `Q`. -/
  Label : Type (u + 1)
  /-- Target-response values. -/
  Value : Type (u + 1)
  /-- The quotient map on the declared coordinate labels. -/
  label : object.InternalWedge region → Label
  /-- The target response a realization gives at a quotient label.  A
  realization is a boundaried graph that can occupy `Z`'s place. -/
  value : BoundaryPiece (SupportAtom.boundary object support) → Label → Value
  /-- `def:target-complete-quotient` (a): two realizations carrying the same
  quotient data lie in the same boundary-degree fibre.  "Two boundaried states
  with different boundary degree profiles are never eligible to be identified
  by a target-complete quotient." -/
  fibrewise : ∀ left right : BoundaryPiece (SupportAtom.boundary object support),
    (∀ test ∈ object.internalWedgeFamily region,
      value left (label test) = value right (label test)) →
    left.boundaryDegreeProfile = right.boundaryDegreeProfile
  /-- `def:target-complete-quotient` (b): and no boundaried context separates
  them.  "Two coordinates may be identified only … when no context `Y ∈ Ctx_T`
  creates a power-of-two cycle from one coordinate and not from the other." -/
  contextUniversal :
    ∀ left right : BoundaryPiece (SupportAtom.boundary object support),
    (∀ test ∈ object.internalWedgeFamily region,
      value left (label test) = value right (label test)) →
    ∀ outside : OutsideContext (SupportAtom.boundary object support),
      (Target (glue left outside) ↔ Target (glue right outside))
  /-- `def:admissible-rank-quotient`, proper clause: at a proper support a
  rank-reducing quotient is represented by a strictly smaller proper
  representative — the five hypotheses of `lem:replacement` at `Z`. -/
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑(object.internalWedgeFamily region) →
    ReplacementSupport Baseline Target object support
  /-- `def:admissible-rank-quotient`, closed clause: at `Z = G` a rank-reducing
  quotient is represented by a strictly smaller admissible closed
  representative. -/
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑(object.internalWedgeFamily region) →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ (Target representative → Target object)

namespace CurvatureQuotient

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {object : FiniteObject.{u}} {region : Finset object.Vertex}

/-- The rank calculus reads an admissible quotient through its labelling and
its responses; this is that reading, and it forgets nothing the calculus
uses. -/
def toRankQuotient (quotient : CurvatureQuotient Baseline Target object region) :
    Core.TargetRank.RankQuotient.{u, u + 1} (object.InternalWedge region) where
  Label := quotient.Label
  Value := quotient.Value
  Realization := BoundaryPiece (SupportAtom.boundary object quotient.support)
  label := quotient.label
  value := quotient.value

@[simp] theorem toRankQuotient_label
    (quotient : CurvatureQuotient Baseline Target object region) :
    quotient.toRankQuotient.label = quotient.label := rfl

/-- **`lem:degree-profile-fibres` and `lem:context-universality`, read off
`def:admissible-rank-quotient`.**

An admissible rank quotient "preserves the boundary degree profile and is
target-complete against all `T`-boundaried contexts", and
`def:target-complete-quotient` spells that as its two clauses: identified states
lie in one boundary-degree fibre, and no outside context creates the target from
one and not the other.  So the pairs an admissible quotient identifies are never
separated -- neither by their profiles, which is `lem:degree-profile-fibres`,
nor by a context, which is `lem:context-universality`.

This is the statement a context-validity test decides, and the reason its
defective alternative is uninhabited: a target-defective identification is by
definition not target-complete, so it is not made by an admissible quotient. -/
theorem targetComplete_of_identified
    (quotient : CurvatureQuotient Baseline Target object region)
    (left right : BoundaryPiece (SupportAtom.boundary object quotient.support))
    (identified : ∀ test ∈ object.internalWedgeFamily region,
      quotient.value left (quotient.label test) =
        quotient.value right (quotient.label test)) :
    left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
      Response.ContextEquivalent Target left right :=
  ⟨quotient.fibrewise left right identified,
    fun outside => quotient.contextUniversal left right identified outside⟩

/-- **`lem:curvature-dependence-routing` for an admissible quotient.**

The manuscript's routing has three cases: a target-defective quotient, a
target-complete compression of a proper atom, and a dependence that becomes
valid only on an enlarged support.  The first cannot occur here — an admissible
quotient is target-complete by definition, which is exactly what
`fibrewise` and `contextUniversal` record — so a rank-reducing admissible
quotient falls in the remaining two by the scope of its determination support:
proper, and then it is a replacement of that support; or the whole graph, and
then it is a smaller closed representative.

Both alternatives are refuted at a selected minimal counterexample —
`InterfaceReplacement.not_replacementSupport` for the first, and the
selection's own minimality for the second — which is how the rank-drop branch
closes. -/
theorem localize (quotient : CurvatureQuotient Baseline Target object region)
    (reducing :
      ¬ Set.InjOn quotient.label ↑(object.internalWedgeFamily region)) :
    ReplacementSupport Baseline Target object quotient.support ∨
      ∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧
            (Target representative → Target object) := by
  match SupportAtom.classifyScope object quotient.support with
  | .proper vertex outside =>
      exact Or.inl (quotient.properRepresentative ⟨vertex, outside⟩ reducing)
  | .closed covers =>
      exact Or.inr (quotient.closedRepresentative covers reducing)

end CurvatureQuotient

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
      (object.internalWedgeFamily region) where
  Member quotient :=
    (∃ admissible : CurvatureQuotient Baseline Target object region,
      admissible.toRankQuotient = quotient) ∧
      quotient.FunctionalOn ↑(object.internalWedgeFamily region)
  functional membership := membership.2

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
