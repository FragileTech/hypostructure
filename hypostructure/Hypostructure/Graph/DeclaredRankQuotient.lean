import Hypostructure.Core.TargetRank
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.ActualContext
import Hypostructure.Graph.GConstructedPiece

/-!
# `def:admissible-rank-quotient` at a declared coordinate family of G

`Core.TargetRank` deliberately leaves open which relabellings a system contains:
*"that is a question about supports, contexts, and representatives … and it is
answered where the objects live"*.  This module answers it, once, for every
declared coordinate family the manuscript presents — raw internal curvature
tests at one node, baseline spine coordinates and sparse pair-response
coordinates at another.  The family, its coordinate type and the declared
support of a coordinate are parameters; nothing below knows what a coordinate
is.

**Everything is stated about G.**  A quotient lives on a connected support
`Z ⊆ V(G)`.  The states it identifies — its *realizations* — are the pieces
constructed from G at `Z` (`GConstructedPiece G Z`: G's piece, its readings,
the folds of two interior vertices with no common neighbour, transplants,
rerouted swaps, splices and double switches), and the one context they are
glued into is G's own rest `G − Z`.  `def:target-complete-quotient` asks two
things of an identification:

* (a) the two realizations lie in one boundary-degree fibre
  (`lem:degree-profile-fibres`) — the quotient's `fibrewise` clause;
* (b) `G − Z` does not separate them (`lem:context-universality`) — the
  quotient's `contextUniversal` clause.  This is a genuine test: a reading of G
  glued into `G − Z` is a subgraph of G (`readings_agree_in_rest`), but a fold
  glued into `G − Z` is a strictly smaller baseline graph, which at a minimal G
  carries a target cycle (`GConstructedPiece.separated_fold_own_of_minimal`).
  An attempt that identifies two separated realizations is target-defective,
  and that is an arm of the routing below.

The representative an admissible rank reduction must supply is the paper's: a
strictly smaller `∂Z`-boundaried piece `X'` — not a reading of G — with G's
boundary-degree profile, the baseline in `glue X' (G − Z)` and no target cycle
there (`ReplacementSupport`); at `Z = G` a strictly smaller closed baseline
graph with no target cycle.  Both are refuted by minimality
(`InterfaceReplacement.not_replacementSupport_of_minimal`), which is why every
admissible quotient of a minimal G is label-injective
(`DeclaredQuotient.labelInjective_of_minimal`).
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## G's readings and their decided agreement in `G − Z` -/

/-- The boundary-degree profile of G's reading `X` at the support `Z`. -/
noncomputable abbrev readingProfile (object : FiniteObject.{u}) (support reading : Finset object.Vertex) :
    BoundaryDegreeProfile (SupportAtom.boundary object support) :=
  (SupportAtom.retainedPiece object support reading).boundaryDegreeProfile

/-- **`lem:context-universality` (b) at G is decided.**  Two readings of G at
`Z`, each glued into G's own rest `G − Z`, have the same target response: both
gluings are subgraphs of G, which avoids the target. -/
theorem readings_agree_in_rest {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (support first second : Finset object.Vertex) :
    HasCycleWithLength LengthOK (ActualContext.actualGlue object support first) ↔
      HasCycleWithLength LengthOK (ActualContext.actualGlue object support second) :=
  iff_of_false (ActualContext.not_target_actualGlue avoids support first)
    (ActualContext.not_target_actualGlue avoids support second)

/-- **A closed representative is excluded by minimality**: a strictly smaller
baseline graph carries the target. -/
theorem not_closedRepresentative_of_minimal {Baseline Target : FiniteObject.{u} → Prop}
    {object : FiniteObject.{u}}
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H) :
    ¬ ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧ Baseline representative ∧
        ¬ Target representative := by
  rintro ⟨representative, smaller, baseline, noTarget⟩
  exact noTarget (minimal representative smaller baseline)

/-! ## Target-completeness at G -/

/-- **`def:target-complete-quotient` at G** for a quotient whose values are read
on the pieces constructed from G at `Z`: every two realizations it identifies
lie in one boundary-degree fibre (a) and have the same target truth in G's own
rest `G − Z` (b). -/
def TargetCompleteAt (Target : FiniteObject.{u} → Prop)
    {object : FiniteObject.{u}} {support : Finset object.Vertex}
    {Coordinate : Type u} (family : Finset Coordinate)
    {Label Value : Type (u + 1)} (label : Coordinate → Label)
    (value : GConstructedPiece object support → Label → Value) : Prop :=
  ∀ first second : GConstructedPiece object support,
    (∀ coordinate ∈ family, value first (label coordinate) =
      value second (label coordinate)) →
    first.profile = second.profile ∧
      (first.targetOf Target ↔ second.targetOf Target)

/-! ## Attempted quotients -/

/-- **A quotient the proof attempts on a declared coordinate family of G.**

`def:admissible-rank-quotient` without assuming the attempt succeeds.  Its
realizations are the pieces constructed from G at the support.  The two
representative clauses are guarded by target-completeness at G
(`TargetCompleteAt`): identified realizations lie in one boundary-degree fibre
and agree in `G − Z`. -/
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
  /-- The value a piece constructed from G at the support gives at a quotient
  label. -/
  value : GConstructedPiece object support → Label → Value
  /-- `def:admissible-rank-quotient`, proper clause.  A rank-reducing
  target-complete quotient at a proper support is represented by a strictly
  smaller proper representative: the hypotheses of `lem:replacement` at `Z`. -/
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑family →
    TargetCompleteAt Target family label value →
    ReplacementSupport Baseline Target object support
  /-- `def:admissible-rank-quotient`, closed clause.  Likewise at `Z = G`: a
  strictly smaller admissible closed representative, a baseline graph with no
  target cycle (`profile_∅(H) ⊆ profile_∅(G) = ∅`). -/
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑family →
    TargetCompleteAt Target family label value →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ ¬ Target representative

namespace AttemptedQuotient

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {object : FiniteObject.{u}} {Coordinate : Type u}
variable {family : Finset Coordinate}
variable {coordinateSupport : Coordinate → Finset object.Vertex}

/-- Read an attempted declared quotient through the rank calculus.  Its
realizations are the pieces constructed from G at the support. -/
def toRankQuotient
    (attempt : AttemptedQuotient Baseline Target object family coordinateSupport) :
    Core.TargetRank.RankQuotient.{u, u + 1} Coordinate where
  Label := attempt.Label
  Value := attempt.Value
  Realization := ULift.{u + 1} (GConstructedPiece object attempt.support)
  label := attempt.label
  value := fun realization => attempt.value realization.down

@[simp] theorem toRankQuotient_label
    (attempt : AttemptedQuotient Baseline Target object family coordinateSupport) :
    attempt.toRankQuotient.label = attempt.label := rfl

/-- Two realizations at the support that the attempt does not separate on the
declared family. -/
def Identifies (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (first second : GConstructedPiece object attempt.support) : Prop :=
  ∀ coordinate ∈ family,
    attempt.value first (attempt.label coordinate) =
      attempt.value second (attempt.label coordinate)

/-- **The routing of every dependence lemma of the manuscript, at G.**

A rank-reducing attempted determination falls into the cases the proofs of
`lem:sparse-pair-dependence-exit`, `lem:mixed-sparse-spine-dependence` and
`prop:sparse-entropy-sandwich-with-blockers` run through, in their order:

1. it identifies two realizations with **different boundary degree profiles**,
   which `lem:degree-profile-fibres` forbids a target-complete quotient from
   doing — the offending boundary-degree entry is the blocker of type (d);
2. it identifies two realizations that **G's own rest `G − Z` separates**
   (`lem:context-universality`) — the identification is target-defective;
3. it is target-complete on a **proper** support, so admissibility supplies a
   replacement of that support — the exit of type (c);
4. it is target-complete on the **whole graph**, so admissibility supplies a
   strictly smaller closed representative — the delocalization exit.

Nothing is chosen: the split is the fibre test, the separation test, then
`SupportAtom.classifyScope` on the determination support. -/
theorem route (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family) :
    (∃ first second, attempt.Identifies first second ∧
        first.profile ≠ second.profile) ∨
      (∃ first second, attempt.Identifies first second ∧
        ¬ (first.targetOf Target ↔ second.targetOf Target)) ∨
      ReplacementSupport Baseline Target object attempt.support ∨
      (∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ ¬ Target representative) := by
  classical
  by_cases fibrewise :
      ∀ first second : GConstructedPiece object attempt.support,
        attempt.Identifies first second → first.profile = second.profile
  · by_cases universal :
        ∀ first second : GConstructedPiece object attempt.support,
          attempt.Identifies first second →
            (first.targetOf Target ↔ second.targetOf Target)
    · have complete : TargetCompleteAt Target family attempt.label attempt.value :=
        fun first second identified =>
          ⟨fibrewise first second identified, universal first second identified⟩
      match SupportAtom.classifyScope object attempt.support with
      | .proper vertex outside =>
          exact Or.inr (Or.inr (Or.inl
            (attempt.properRepresentative ⟨vertex, outside⟩ reducing complete)))
      | .closed covers =>
          exact Or.inr (Or.inr (Or.inr
            (attempt.closedRepresentative covers reducing complete)))
    · refine Or.inr (Or.inl ?_)
      by_contra absent
      exact universal fun first second identifies =>
        Classical.byContradiction fun separated =>
          absent ⟨first, second, identifies, separated⟩
  · refine Or.inl ?_
    by_contra absent
    exact fibrewise fun first second identifies =>
      Classical.byContradiction fun different =>
        absent ⟨first, second, identifies, different⟩

/-- **At a minimal G a rank-reducing attempt has a type-(d) profile blocker or
a target defect in `G − Z`.**  Its replacement and closed-representative arms
are refuted by minimality. -/
theorem defect_of_minimal (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H) :
    (∃ first second, attempt.Identifies first second ∧
        first.profile ≠ second.profile) ∨
      (∃ first second, attempt.Identifies first second ∧
        ¬ (first.targetOf Target ↔ second.targetOf Target)) := by
  rcases attempt.route reducing with blocker | defect | replacement | closed
  · exact Or.inl blocker
  · exact Or.inr defect
  · exact absurd replacement (not_replacementSupport_of_minimal minimal _)
  · exact absurd closed (not_closedRepresentative_of_minimal minimal)

end AttemptedQuotient

/-! ## Admissible quotients -/

/-- **An admissible rank quotient of a declared coordinate family of G.**

`def:admissible-rank-quotient` at G, with the pieces constructed from G at the
support as realizations: identified realizations lie in one boundary-degree
fibre (condition (a), `fibrewise`) and agree in G's own rest `G − Z`
(condition (b), `contextUniversal`); and a rank reduction is represented — at
`Z ⊊ G` by a replacement of `Z` (`ReplacementSupport`), at `Z = G` by a strictly
smaller closed baseline graph with no target cycle. -/
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
  /-- The value a piece constructed from G at the support gives at a quotient
  label. -/
  value : GConstructedPiece object support → Label → Value
  /-- `def:target-complete-quotient` (a): two realizations carrying the same
  quotient data lie in the same boundary-degree fibre. -/
  fibrewise : ∀ first second : GConstructedPiece object support,
    (∀ coordinate ∈ family, value first (label coordinate) =
      value second (label coordinate)) →
    first.profile = second.profile
  /-- `def:target-complete-quotient` (b), at G: two realizations carrying the
  same quotient data have the same target truth in G's own rest `G − Z`. -/
  contextUniversal : ∀ first second : GConstructedPiece object support,
    (∀ coordinate ∈ family, value first (label coordinate) =
      value second (label coordinate)) →
    (first.targetOf Target ↔ second.targetOf Target)
  /-- `def:admissible-rank-quotient`, proper clause. -/
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑family →
    ReplacementSupport Baseline Target object support
  /-- `def:admissible-rank-quotient`, closed clause. -/
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑family →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ ¬ Target representative

namespace DeclaredQuotient

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {object : FiniteObject.{u}} {Coordinate : Type u}
variable {family : Finset Coordinate}
variable {coordinateSupport : Coordinate → Finset object.Vertex}

/-- The rank calculus reads an admissible quotient through its labelling and its
responses on the pieces constructed from G at the support. -/
def toRankQuotient
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    Core.TargetRank.RankQuotient.{u, u + 1} Coordinate where
  Label := quotient.Label
  Value := quotient.Value
  Realization := ULift.{u + 1} (GConstructedPiece object quotient.support)
  label := quotient.label
  value := fun realization => quotient.value realization.down

@[simp] theorem toRankQuotient_label
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    quotient.toRankQuotient.label = quotient.label := rfl

/-- Two realizations at the support that the quotient identifies. -/
def Identifies
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (first second : GConstructedPiece object quotient.support) : Prop :=
  ∀ coordinate ∈ family,
    quotient.value first (quotient.label coordinate) =
      quotient.value second (quotient.label coordinate)

/-- **`lem:degree-profile-fibres` and `lem:context-universality`, at G.**  Two
realizations an admissible quotient identifies lie in one boundary-degree fibre
(its clause (a)) and agree in `G − Z` (its clause (b)). -/
theorem targetComplete_of_identified
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    {first second : GConstructedPiece object quotient.support}
    (identified : quotient.Identifies first second) :
    first.profile = second.profile ∧
      (first.targetOf Target ↔ second.targetOf Target) :=
  ⟨quotient.fibrewise first second identified,
    quotient.contextUniversal first second identified⟩

/-- An admissible quotient is target-complete at G. -/
theorem targetCompleteAt
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    TargetCompleteAt Target family quotient.label quotient.value :=
  fun _first _second identified =>
    quotient.targetComplete_of_identified identified

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

A rank-reducing admissible quotient falls, by the scope of its determination
support, into a replacement of that support (`Z ⊊ G`) or a strictly smaller
closed representative (`Z = G`).  Both are refuted at a minimal G
(`labelInjective_of_minimal`). -/
theorem localize
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (reducing : ¬ Set.InjOn quotient.label ↑family) :
    ReplacementSupport Baseline Target object quotient.support ∨
      ∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ ¬ Target representative := by
  match SupportAtom.classifyScope object quotient.support with
  | .proper vertex outside =>
      exact Or.inl (quotient.properRepresentative ⟨vertex, outside⟩ reducing)
  | .closed covers =>
      exact Or.inr (quotient.closedRepresentative covers reducing)

/-- **Every admissible quotient of a minimal G is label-injective**: a rank
reduction would supply a replacement or a smaller closed representative, and
minimality gives either one the target. -/
theorem labelInjective_of_minimal
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H) :
    Set.InjOn quotient.label ↑family := by
  by_contra reducing
  rcases quotient.localize reducing with replacement | closed
  · exact not_replacementSupport_of_minimal minimal _ replacement
  · exact not_closedRepresentative_of_minimal minimal closed

end DeclaredQuotient

end Hypostructure.Graph
