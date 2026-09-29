import Hypostructure.Core.TargetRank
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.ActualContext

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
`Z ⊆ V(G)`.  The states it identifies are G's own readings at `Z`: for
`X ⊆ V(G)`, the edge restriction `SupportAtom.retainedPiece G Z X` of G's piece
at `Z` to `X`.  `def:target-complete-quotient` asks two things of an
identification:

* (a) the two readings lie in one boundary-degree fibre
  (`lem:degree-profile-fibres`) — a genuine test about G's readings, kept as the
  quotient's `fibrewise` clause and as the guard of an attempt;
* (b) no context separates them (`lem:context-universality`).  About G this is
  **decided**: a reading of G glued into G's own rest `G − Z` is a subgraph of
  G (`ActualContext.not_target_actualGlue`), so any two readings agree there
  (`readings_agree_in_rest`).  The separation arm is empty at G and is not an
  arm of the routing below.

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

/-! ## Attempted quotients -/

/-- **A quotient the proof attempts on a declared coordinate family of G.**

`def:admissible-rank-quotient` without assuming the attempt succeeds.  The
states are G's readings at the support.  The two representative clauses are
guarded by condition (a) of target-completeness — identified readings lie in
one boundary-degree fibre; condition (b) holds at G outright
(`readings_agree_in_rest`). -/
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
  /-- The value G's reading `retainedPiece object support X` gives at a
  quotient label. -/
  value : Finset object.Vertex → Label → Value
  /-- `def:admissible-rank-quotient`, proper clause.  A rank-reducing quotient
  at a proper support whose identifications stay in one boundary-degree fibre
  is represented by a strictly smaller proper representative: the hypotheses
  of `lem:replacement` at `Z`. -/
  properRepresentative : (∃ vertex, vertex ∉ support) →
    ¬ Set.InjOn label ↑family →
    (∀ first second : Finset object.Vertex,
      (∀ coordinate ∈ family, value first (label coordinate) =
        value second (label coordinate)) →
      readingProfile object support first = readingProfile object support second) →
    ReplacementSupport Baseline Target object support
  /-- `def:admissible-rank-quotient`, closed clause.  Likewise at `Z = G`: a
  strictly smaller admissible closed representative, a baseline graph with no
  target cycle (`profile_∅(H) ⊆ profile_∅(G) = ∅`). -/
  closedRepresentative : (∀ vertex, vertex ∈ support) →
    ¬ Set.InjOn label ↑family →
    (∀ first second : Finset object.Vertex,
      (∀ coordinate ∈ family, value first (label coordinate) =
        value second (label coordinate)) →
      readingProfile object support first = readingProfile object support second) →
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ ¬ Target representative

namespace AttemptedQuotient

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {object : FiniteObject.{u}} {Coordinate : Type u}
variable {family : Finset Coordinate}
variable {coordinateSupport : Coordinate → Finset object.Vertex}

/-- Read an attempted declared quotient through the rank calculus.  Its
realizations are G's readings at the support. -/
def toRankQuotient
    (attempt : AttemptedQuotient Baseline Target object family coordinateSupport) :
    Core.TargetRank.RankQuotient.{u, u + 1} Coordinate where
  Label := attempt.Label
  Value := attempt.Value
  Realization := ULift.{u + 1} (Finset object.Vertex)
  label := attempt.label
  value := fun reading => attempt.value reading.down

@[simp] theorem toRankQuotient_label
    (attempt : AttemptedQuotient Baseline Target object family coordinateSupport) :
    attempt.toRankQuotient.label = attempt.label := rfl

/-- Two of G's readings at the support that the attempt does not separate on
the declared family. -/
def Identifies (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (first second : Finset object.Vertex) : Prop :=
  ∀ coordinate ∈ family,
    attempt.value first (attempt.label coordinate) =
      attempt.value second (attempt.label coordinate)

/-- **The routing of every dependence lemma of the manuscript, at G.**

A rank-reducing attempted determination falls into the cases the proofs of
`lem:sparse-pair-dependence-exit`, `lem:mixed-sparse-spine-dependence` and
`prop:sparse-entropy-sandwich-with-blockers` run through, in their order:

1. it identifies two of G's readings with **different boundary degree
   profiles**, which `lem:degree-profile-fibres` forbids a target-complete
   quotient from doing — the offending boundary-degree entry is the blocker of
   type (d);
2. (the manuscript's context-separation case is empty at G: any two readings
   agree in `G − Z`, `readings_agree_in_rest`);
3. it is target-complete on a **proper** support, so admissibility supplies a
   replacement of that support — the exit of type (c);
4. it is target-complete on the **whole graph**, so admissibility supplies a
   strictly smaller closed representative — the delocalization exit.

Nothing is chosen: the split is the fibre test, then
`SupportAtom.classifyScope` on the determination support. -/
theorem route (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family) :
    (∃ first second, attempt.Identifies first second ∧
        readingProfile object attempt.support first ≠
          readingProfile object attempt.support second) ∨
      ReplacementSupport Baseline Target object attempt.support ∨
      (∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ ¬ Target representative) := by
  classical
  by_cases fibrewise :
      ∀ first second : Finset object.Vertex, attempt.Identifies first second →
        readingProfile object attempt.support first =
          readingProfile object attempt.support second
  · match SupportAtom.classifyScope object attempt.support with
    | .proper vertex outside =>
        exact Or.inr (Or.inl
          (attempt.properRepresentative ⟨vertex, outside⟩ reducing fibrewise))
    | .closed covers =>
        exact Or.inr (Or.inr
          (attempt.closedRepresentative covers reducing fibrewise))
  · refine Or.inl ?_
    by_contra absent
    exact fibrewise fun first second identifies =>
      Classical.byContradiction fun different =>
        absent ⟨first, second, identifies, different⟩

/-- **At a minimal G a rank-reducing attempt has a type-(d) profile blocker.**
Its replacement and closed-representative arms are refuted by minimality. -/
theorem fibre_of_minimal (attempt : AttemptedQuotient Baseline Target object family
      coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H) :
    ∃ first second, attempt.Identifies first second ∧
      readingProfile object attempt.support first ≠
        readingProfile object attempt.support second := by
  rcases attempt.route reducing with blocker | replacement | closed
  · exact blocker
  · exact absurd replacement (not_replacementSupport_of_minimal minimal _)
  · exact absurd closed (not_closedRepresentative_of_minimal minimal)

end AttemptedQuotient

/-! ## Admissible quotients -/

/-- **An admissible rank quotient of a declared coordinate family of G.**

`def:admissible-rank-quotient` at G: identified readings lie in one
boundary-degree fibre (condition (a), `fibrewise`); condition (b) is decided at
G (`readings_agree_in_rest`); and a rank reduction is represented — at
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
  /-- The value G's reading `retainedPiece object support X` gives at a
  quotient label. -/
  value : Finset object.Vertex → Label → Value
  /-- `def:target-complete-quotient` (a): two of G's readings carrying the same
  quotient data lie in the same boundary-degree fibre. -/
  fibrewise : ∀ first second : Finset object.Vertex,
    (∀ coordinate ∈ family, value first (label coordinate) =
      value second (label coordinate)) →
    readingProfile object support first = readingProfile object support second
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
responses on G's readings at the support. -/
def toRankQuotient
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    Core.TargetRank.RankQuotient.{u, u + 1} Coordinate where
  Label := quotient.Label
  Value := quotient.Value
  Realization := ULift.{u + 1} (Finset object.Vertex)
  label := quotient.label
  value := fun reading => quotient.value reading.down

@[simp] theorem toRankQuotient_label
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport) :
    quotient.toRankQuotient.label = quotient.label := rfl

/-- Two of G's readings at the support that the quotient identifies. -/
def Identifies
    (quotient : DeclaredQuotient Baseline Target object family coordinateSupport)
    (first second : Finset object.Vertex) : Prop :=
  ∀ coordinate ∈ family,
    quotient.value first (quotient.label coordinate) =
      quotient.value second (quotient.label coordinate)

/-- **`lem:degree-profile-fibres` and `lem:context-universality`, at G.**  Two
readings an admissible quotient identifies lie in one boundary-degree fibre
(its clause (a)) and agree in `G − Z` (decided at G). -/
theorem targetComplete_of_identified {LengthOK : Nat → Prop}
    (quotient : DeclaredQuotient Baseline (HasCycleWithLength LengthOK) object family
      coordinateSupport)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {first second : Finset object.Vertex}
    (identified : quotient.Identifies first second) :
    readingProfile object quotient.support first =
        readingProfile object quotient.support second ∧
      (HasCycleWithLength LengthOK
          (ActualContext.actualGlue object quotient.support first) ↔
        HasCycleWithLength LengthOK
          (ActualContext.actualGlue object quotient.support second)) :=
  ⟨quotient.fibrewise first second identified,
    readings_agree_in_rest avoids quotient.support first second⟩

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
  properRepresentative proper reducing _fibrewise :=
    quotient.properRepresentative proper reducing
  closedRepresentative covers reducing _fibrewise :=
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
