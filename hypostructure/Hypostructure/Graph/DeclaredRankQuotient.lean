import Hypostructure.Core.TargetRank
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# `def:admissible-rank-quotient` at an arbitrary declared coordinate family

`Core.TargetRank` deliberately leaves open which relabellings a system contains:
*"that is a question about supports, contexts, and representatives … and it is
answered where the objects live"*.  This module answers it, once, for every
declared coordinate family the manuscript presents — raw internal curvature
tests at one node, baseline spine coordinates and sparse pair-response
coordinates at another.  The family, its coordinate type and the declared
support of a coordinate are parameters; nothing below knows what a coordinate
is.

Two structures, and they are `def:admissible-rank-quotient` read in its two
directions.

`AttemptedQuotient` is a quotient the proof *tries*: a connected determination
support carrying the family, a relabelling, and the response values a
realization gives.  Its two representative fields are **conditional on
target-completeness**, because that is what the definition says — a rank-reducing
quotient is admissible *only if* it preserves the boundary degree profile, is
target-complete against all contexts, and supplies the representative its scope
requires.  An attempt that fails either completeness clause is simply not
admissible, and the definition then demands nothing of it.

`DeclaredQuotient` is an admissible one: the same data with the two completeness
clauses holding unconditionally, so its representative clauses are unconditional
too.

`AttemptedQuotient.route` is the four-way case analysis every dependence lemma of
the manuscript runs:

> If the determination attempts to identify states with different boundary degree
> profiles, then `lem:degree-profile-fibres` forbids a target-complete
> identification. …  If the determination is not target-complete against all
> `∂Z`-boundaried contexts, then by `lem:context-universality` it is
> target-defective. …  Assume, therefore, that the quotient is target-complete.
> If `Z ⊊ G`, then the admissibility rule supplies a strictly smaller proper
> representative … It remains to consider `Z = G`. …

so its four disjuncts are, in the manuscript's order, the boundary-degree
separation, the context separation, the proper replacement, and the smaller
closed representative.  `DeclaredQuotient.localize` is that routing with the
first two disjuncts discharged by admissibility's own fields.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- **A quotient the proof attempts on a declared coordinate family.**

`def:admissible-rank-quotient` without assuming the attempt succeeds: the two
representative clauses are guarded by the target-completeness the definition
requires before an identification counts as admissible. -/
structure AttemptedQuotient (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) {Coordinate : Type u}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Type (u + 2) where
  /-- The determination support `Z`. -/
  support : Finset object.Vertex
  /-- `Z` is connected: `def:admissible-rank-quotient` quantifies over families
  "carried by a connected support `X ⊆ G`". -/
  connected : SupportComponents.Connected.ConnectedOn object support
  /-- `Z` carries the coordinates under discussion. -/
  carries : ∀ coordinate ∈ family, coordinateSupport coordinate ⊆ support
  /-- The labelled coordinates of the quotient datum `Q`. -/
  Label : Type (u + 1)
  /-- Target-response values. -/
  Value : Type (u + 1)
  /-- The quotient map on the declared coordinate labels. -/
  label : Coordinate → Label
  /-- The target response a realization gives at a quotient label.  A
  realization is a boundaried graph that can occupy `Z`'s place. -/
  value : BoundaryPiece (SupportAtom.boundary object support) → Label → Value
  /-- `def:admissible-rank-quotient`, proper clause.  A rank-reducing quotient at
  a proper support is admissible **only when** it is target-complete, and then it
  is represented by a strictly smaller proper representative — the five
  hypotheses of `lem:replacement` at `Z`. -/
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑family →
    (∀ left right : BoundaryPiece (SupportAtom.boundary object support),
      (∀ coordinate ∈ family, value left (label coordinate) =
        value right (label coordinate)) →
      left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
        Response.ContextEquivalent Target left right) →
    ReplacementSupport Baseline Target object support
  /-- `def:admissible-rank-quotient`, closed clause.  Likewise at `Z = G`: only a
  target-complete rank-reducing quotient is admissible, and then it is
  represented by a strictly smaller admissible closed representative. -/
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑family →
    (∀ left right : BoundaryPiece (SupportAtom.boundary object support),
      (∀ coordinate ∈ family, value left (label coordinate) =
        value right (label coordinate)) →
      left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
        Response.ContextEquivalent Target left right) →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ (Target representative → Target object)

namespace AttemptedQuotient

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {object : FiniteObject.{u}} {Coordinate : Type u}
variable {family : Finset Coordinate}
variable {coordinateSupport : Coordinate → Finset object.Vertex}

/-- Read an attempted declared quotient through the rank calculus.  Unlike a
`DeclaredQuotient`, an attempt need not yet be target-complete; the rank axiom
is therefore retained separately by the sparse-dependence certificate that
uses this projection. -/
def toRankQuotient
    (attempt : AttemptedQuotient Baseline Target object family coordinateSupport) :
    Core.TargetRank.RankQuotient.{u, u + 1} Coordinate where
  Label := attempt.Label
  Value := attempt.Value
  Realization := BoundaryPiece (SupportAtom.boundary object attempt.support)
  label := attempt.label
  value := attempt.value

@[simp] theorem toRankQuotient_label
    (attempt : AttemptedQuotient Baseline Target object family coordinateSupport) :
    attempt.toRankQuotient.label = attempt.label := rfl

/-- Two realizations the attempt does not separate on the declared family. -/
def Identifies (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (left right : BoundaryPiece (SupportAtom.boundary object attempt.support)) :
    Prop :=
  ∀ coordinate ∈ family,
    attempt.value left (attempt.label coordinate) =
      attempt.value right (attempt.label coordinate)

/-- **The routing of every dependence lemma of the manuscript.**

A rank-reducing attempted determination falls into exactly the four cases the
proofs of `lem:sparse-pair-dependence-exit`,
`lem:mixed-sparse-spine-dependence` and
`prop:sparse-entropy-sandwich-with-blockers` run through, in their order:

1. it identifies two realizations with **different boundary degree profiles**,
   which `lem:degree-profile-fibres` forbids a target-complete quotient from
   doing — the offending boundary-degree entry is the blocker of type (d);
2. it identifies two realizations a boundaried context **separates**, so by
   `lem:context-universality` the quotient is target-defective — the
   distinguishing target-response coordinate is the blocker of type (e), and the
   defect is a sparse surplus exit of type (b);
3. it is target-complete on a **proper** support, so admissibility supplies a
   replacement of that support, which `lem:replacement` and `cor:uncompressible`
   forbid at a minimal counterexample — the exit of type (c);
4. it is target-complete on the **whole graph**, so admissibility supplies a
   strictly smaller closed representative, which minimality forbids — the
   delocalization exit.

Nothing is chosen: the split is `SupportAtom.classifyScope` on the determination
support after the completeness test, which is exactly how the manuscript orders
its own cases. -/
theorem route (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family) :
    (∃ left right, attempt.Identifies left right ∧
        left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
      (∃ left right, attempt.Identifies left right ∧
        Response.TargetDefect Target left right) ∨
      ReplacementSupport Baseline Target object attempt.support ∨
      (∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ (Target representative → Target object)) := by
  classical
  by_cases complete :
      ∀ left right : BoundaryPiece (SupportAtom.boundary object attempt.support),
        attempt.Identifies left right →
          left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
            Response.ContextEquivalent Target left right
  · match SupportAtom.classifyScope object attempt.support with
    | .proper vertex outside =>
        exact Or.inr (Or.inr (Or.inl
          (attempt.properRepresentative ⟨vertex, outside⟩ reducing complete)))
    | .closed covers =>
        exact Or.inr (Or.inr (Or.inr
          (attempt.closedRepresentative covers reducing complete)))
  · obtain ⟨left, right, identifies, failure⟩ : ∃ left right,
        attempt.Identifies left right ∧
          ¬ (left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
            Response.ContextEquivalent Target left right) := by
      by_contra absent
      exact complete fun left right identifies => by
        by_contra failure
        exact absent ⟨left, right, identifies, failure⟩
    by_cases profiles :
        left.boundaryDegreeProfile = right.boundaryDegreeProfile
    · refine Or.inr (Or.inl ⟨left, right, identifies, ?_⟩)
      exact Response.targetDefect_of_not_contextEquivalent
        (fun universal => failure ⟨profiles, universal⟩)
    · exact Or.inl ⟨left, right, identifies, profiles⟩

end AttemptedQuotient

/-- **An admissible rank quotient of a declared coordinate family.**

`def:admissible-rank-quotient` with its two target-completeness clauses holding:
identified realizations lie in one boundary-degree fibre
(`lem:degree-profile-fibres`) and no boundaried context separates them
(`lem:context-universality`).  Because the clauses hold, the representative
clauses of an attempt become unconditional. -/
structure DeclaredQuotient (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) {Coordinate : Type u}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Type (u + 2) where
  /-- The connected determination support `Z` of the quotient. -/
  support : Finset object.Vertex
  /-- `Z` is connected. -/
  connected : SupportComponents.Connected.ConnectedOn object support
  /-- `Z` carries the coordinates under discussion. -/
  carries : ∀ coordinate ∈ family, coordinateSupport coordinate ⊆ support
  /-- The labelled coordinates of the quotient datum `Q`. -/
  Label : Type (u + 1)
  /-- Target-response values. -/
  Value : Type (u + 1)
  /-- The quotient map on the declared coordinate labels. -/
  label : Coordinate → Label
  /-- The target response a realization gives at a quotient label. -/
  value : BoundaryPiece (SupportAtom.boundary object support) → Label → Value
  /-- `def:target-complete-quotient` (a): two realizations carrying the same
  quotient data lie in the same boundary-degree fibre. -/
  fibrewise : ∀ left right : BoundaryPiece (SupportAtom.boundary object support),
    (∀ coordinate ∈ family,
      value left (label coordinate) = value right (label coordinate)) →
    left.boundaryDegreeProfile = right.boundaryDegreeProfile
  /-- `def:target-complete-quotient` (b): and no boundaried context separates
  them. -/
  contextUniversal :
    ∀ left right : BoundaryPiece (SupportAtom.boundary object support),
    (∀ coordinate ∈ family,
      value left (label coordinate) = value right (label coordinate)) →
    ∀ outside : OutsideContext (SupportAtom.boundary object support),
      (Target (glue left outside) ↔ Target (glue right outside))
  /-- `def:admissible-rank-quotient`, proper clause. -/
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑family →
    ReplacementSupport Baseline Target object support
  /-- `def:admissible-rank-quotient`, closed clause. -/
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑family →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ (Target representative → Target object)

namespace DeclaredQuotient

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {object : FiniteObject.{u}} {Coordinate : Type u}
variable {family : Finset Coordinate}
variable {coordinateSupport : Coordinate → Finset object.Vertex}

/-- The rank calculus reads an admissible quotient through its labelling and its
responses; this is that reading, and it forgets nothing the calculus uses. -/
def toRankQuotient
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    Core.TargetRank.RankQuotient.{u, u + 1} Coordinate where
  Label := quotient.Label
  Value := quotient.Value
  Realization := BoundaryPiece (SupportAtom.boundary object quotient.support)
  label := quotient.label
  value := quotient.value

@[simp] theorem toRankQuotient_label
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    quotient.toRankQuotient.label = quotient.label := rfl

/-- **`lem:degree-profile-fibres` and `lem:context-universality`, read off
`def:admissible-rank-quotient`.**

The pairs an admissible quotient identifies are never separated — neither by
their boundary-degree profiles nor by an outside context.  This is why a
target-defective identification is not made by an admissible quotient. -/
theorem targetComplete_of_identified
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (left right : BoundaryPiece (SupportAtom.boundary object quotient.support))
    (identified : ∀ coordinate ∈ family,
      quotient.value left (quotient.label coordinate) =
        quotient.value right (quotient.label coordinate)) :
    left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
      Response.ContextEquivalent Target left right :=
  ⟨quotient.fibrewise left right identified,
    fun outside => quotient.contextUniversal left right identified outside⟩

/-- The admissible quotient, read as an attempt.  Its conditional representative
clauses are its unconditional ones, so nothing is added. -/
def toAttempt
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    AttemptedQuotient Baseline Target object family coordinateSupport where
  support := quotient.support
  connected := quotient.connected
  carries := quotient.carries
  Label := quotient.Label
  Value := quotient.Value
  label := quotient.label
  value := quotient.value
  properRepresentative proper reducing _complete :=
    quotient.properRepresentative proper reducing
  closedRepresentative covers reducing _complete :=
    quotient.closedRepresentative covers reducing

/-- **`lem:curvature-dependence-routing` for an admissible quotient.**

The first two disjuncts of `AttemptedQuotient.route` cannot occur here — an
admissible quotient is target-complete by definition, which is what `fibrewise`
and `contextUniversal` record — so a rank-reducing admissible quotient falls in
the remaining two by the scope of its determination support: proper, and then it
is a replacement of that support; or the whole graph, and then it is a smaller
closed representative.

Both alternatives are refuted at a selected minimal counterexample —
`InterfaceReplacement.not_replacementSupport` for the first, and the selection's
own minimality for the second. -/
theorem localize
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (reducing : ¬ Set.InjOn quotient.label ↑family) :
    ReplacementSupport Baseline Target object quotient.support ∨
      ∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ (Target representative → Target object) := by
  match SupportAtom.classifyScope object quotient.support with
  | .proper vertex outside =>
      exact Or.inl (quotient.properRepresentative ⟨vertex, outside⟩ reducing)
  | .closed covers =>
      exact Or.inr (quotient.closedRepresentative covers reducing)

end DeclaredQuotient

end Hypostructure.Graph
