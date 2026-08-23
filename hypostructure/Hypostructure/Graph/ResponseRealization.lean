import Hypostructure.Graph.Route8Residual
import Hypostructure.Graph.DecoratedHandoffEnvelope

/-!
# Response realization of a declared reading

`def:typeA-route8-carriers`, `def:typeA-continuation-classes` and
`def:proper-quotient-representative` all evaluate an identified or restricted
*declared* reading by realizing it as a semantic `BoundaryPiece` on the
interface of the support that carries it, and then testing that realization
against the unrestricted reading with `Graph.glue` and outside contexts.  The
realization must satisfy two clauses before any test is meaningful:

* it keeps **the same boundary-degree profile** as the unrestricted reading —
  the manuscript's *"every carrier restriction is taken inside the original
  boundary-degree fibre"* — so the identification is a candidate for
  target-completeness at all rather than being refuted by
  `lem:degree-profile-fibres`; and
* the target-response comparison (`Response.TargetDefect`,
  `Response.TargetComplete`, `Response.ContextEquivalent`) is stated on one
  labelled interface, against literal gluings with `OutsideContext`s.

This module supplies that realization once, generically: quantified over the
ambient object, the carrying support, the declared coordinate universe with its
declared supports, and — for the canonical (baseline-compatible) form — over
an isomorphism-invariant baseline and target.  The raw realization
(`declaredState`) keeps every boundary incidence and exactly the internal
edges owned by the retained declared supports; the canonical realization
(`canonicalDeclaredState`) replaces it by *the* canonical piece of its cut
state (`Graph/CanonicalRealization`), which is what
`def:proper-quotient-representative` requires when a baseline clause must
survive the restriction — edge-dropping alone falsifies an internal
minimum-degree baseline, and the canonical representative is the piece the
manuscript actually swaps in.

The second half packages the realization for the continuation-switch
consumers: a `DecoratedHandoff.Separation` whose two registered readings are
declared-coordinate realizations (`separationOfDeclared`), and a
`DecoratedHandoff.SwitchReading` whose base realization is the switch
support's own piece and whose proper restrictions are canonical realizations
(`switchReadingOfDeclared`).  The exact vertex accounting of both realizations
against the ambient object is proved (`declaredState_glue_vertexCount`,
`canonicalDeclaredState_glue_vertexCount`), so the strict-descent clause of a
switch reading is reduced to the one datum the declared coordinates genuinely
must supply: strict shrinkage of the canonical representative
(`def:proper-quotient-representative`'s *"strictly smaller"*).

Nothing here is specialized to a manuscript: no numeral occurs, and the
target, baseline, coordinate universe and declared supports are parameters.
-/

namespace Hypostructure.Graph

universe u v

namespace Response

/-- A target defect is indifferent to exchanging the identified side for a
context-equivalent realization: the defect is a property of the response, not
of the chosen realization. -/
theorem targetDefect_congr_left {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} → Prop}
    {left left' right : BoundaryPiece boundary}
    (equiv : ContextEquivalent Target left left') :
    TargetDefect Target left right ↔ TargetDefect Target left' right := by
  constructor
  · rintro ⟨outside, distinguishes⟩
    exact ⟨outside, fun same => distinguishes ((equiv outside).trans same)⟩
  · rintro ⟨outside, distinguishes⟩
    exact ⟨outside, fun same => distinguishes ((equiv outside).symm.trans same)⟩

/-- **The registered-fibre dichotomy.**  Two realizations already lying in one
boundary-degree fibre admit exactly two outcomes: the identification is
target-complete, or a literal outside context distinguishes them.  This is
`lem:separated-testers`' closing clause with the profile half discharged by
the registration instead of assumed. -/
theorem targetComplete_or_targetDefect_of_profile_eq {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} → Prop)
    {left right : BoundaryPiece boundary}
    (profileEq : left.boundaryDegreeProfile = right.boundaryDegreeProfile) :
    TargetComplete BoundaryPiece.boundaryDegreeProfile Target left right ∨
      TargetDefect Target left right := by
  rcases contextEquivalent_or_targetDefect Target left right with
    equivalent | defect
  · exact Or.inl ⟨profileEq, equivalent⟩
  · exact Or.inr defect

end Response

namespace ResponseRealization

variable (object : FiniteObject.{u}) (support : Finset object.Vertex)

/-! ## The raw realization of a retained declared-coordinate set -/

/-- The vertices a set of retained declared coordinates keeps alive: the union
of their declared supports.  A forgotten coordinate stops contributing its
declared support, which is exactly what an identification forgets. -/
noncomputable def declaredVertices {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact retained.biUnion declaredSupport

/-- **The semantic realization of a restricted declared reading.**

Presented on the support's own labelled interface: every boundary incidence is
retained, and an internal edge survives exactly when the retained declared
supports own it.  This is `Route8.PresentedEntry.retainedBasinPiece` driven by
declared coordinate data instead of a raw vertex set, so the route-8 reading is
one instance of it. -/
noncomputable def declaredState {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object support) :=
  Route8.PresentedEntry.retainedBasinPiece object support
    (declaredVertices object declaredSupport retained)

/-- **Every restriction stays in the original boundary-degree fibre.**  The
boundary is untouched and every boundary incidence survives, so the profile is
the unrestricted piece's own. -/
theorem declaredState_boundaryDegreeProfile {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (declaredState object support declaredSupport
        retained).boundaryDegreeProfile =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        support).boundaryDegreeProfile :=
  Route8.PresentedEntry.retainedBasinPiece_boundaryDegreeProfile object support
    (declaredVertices object declaredSupport retained)

/-- Any two restrictions of one declared reading lie in one fibre. -/
theorem declaredState_sameProfile {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (left right : Finset Coordinate) :
    (declaredState object support declaredSupport
        left).boundaryDegreeProfile =
      (declaredState object support declaredSupport
        right).boundaryDegreeProfile :=
  (declaredState_boundaryDegreeProfile object support declaredSupport
    left).trans
    (declaredState_boundaryDegreeProfile object support declaredSupport
      right).symm

/-- The realization lies in the fibre *registered* for the support: the profile
generated by the framework's own atom certificate, whose constructor is
private, so no caller registers a guessed profile. -/
theorem declaredState_registered {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate)
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support) :
    (declaredState object support declaredSupport
        retained).boundaryDegreeProfile =
      (deriveBoundariedAtomProfile
        (Strategy.InterfaceReplacement.SupportAtom.properAtom object support
          connected proper)).boundaryDegreeProfile :=
  (declaredState_boundaryDegreeProfile object support declaredSupport
    retained).trans
    (deriveBoundariedAtomProfile
      (Strategy.InterfaceReplacement.SupportAtom.properAtom object support
        connected proper)).profile_eq.symm

/-- **The identification is testable and exhaustively so**: against literal
gluings with outside contexts, the restricted reading is target-completely
identified with the unrestricted one, or a distinguishing context exists.
There is no third outcome. -/
theorem declaredState_targetComplete_or_targetDefect {Coordinate : Type v}
    (Target : FiniteObject.{u} → Prop)
    (declaredSupport : Coordinate → Finset object.Vertex)
    (left right : Finset Coordinate) :
    Response.TargetComplete BoundaryPiece.boundaryDegreeProfile Target
        (declaredState object support declaredSupport left)
        (declaredState object support declaredSupport right) ∨
      Response.TargetDefect Target
        (declaredState object support declaredSupport left)
        (declaredState object support declaredSupport right) :=
  Response.targetComplete_or_targetDefect_of_profile_eq Target
    (declaredState_sameProfile object support declaredSupport left right)

/-! ## Exact vertex accounting against the ambient object -/

/-- The ambient object is exactly its support decomposition: interface labels,
piece-internal vertices, outside-internal vertices. -/
theorem vertexCount_decomposition :
    object.vertexCount =
      (Strategy.InterfaceReplacement.SupportAtom.boundary object
          support).vertexCount +
        (Strategy.InterfaceReplacement.SupportAtom.piece object
          support).internalVertexCount +
        (Strategy.InterfaceReplacement.SupportAtom.outside object
          support).internalVertexCount := by
  have count := FiniteObject.vertexCount_eq_of_iso
    (Strategy.InterfaceReplacement.SupportAtom.decomposition object
      support).reconstructionIso
  rw [glue_vertexCount] at count
  exact count.symm

/-- The raw realization keeps the internal carrier of the unrestricted piece:
only edges are forgotten, never vertices. -/
theorem declaredState_internalVertexCount {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (declaredState object support declaredSupport
        retained).internalVertexCount =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        support).internalVertexCount :=
  rfl

/-- **Edge-forgetting alone never descends.**  Completing the raw realization
with the support's own outside context reproduces the ambient vertex count
exactly; strict progress must come from the canonical representative, not from
the restriction itself. -/
theorem declaredState_glue_vertexCount {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (glue (declaredState object support declaredSupport retained)
        (Strategy.InterfaceReplacement.SupportAtom.outside object
          support)).vertexCount = object.vertexCount := by
  rw [glue_vertexCount,
    declaredState_internalVertexCount object support declaredSupport retained,
    ← vertexCount_decomposition object support]

/-! ## The canonical realization

`def:proper-quotient-representative`: when the restriction must also carry a
baseline clause at every completion — which raw edge-forgetting falsifies —
the reading is realized by *the* canonical piece of the raw realization's cut
state.  All three clauses of `CanonicalPiece.CutStateReading` transfer below:
the profile, the target response against every outside context, and the
inherited baseline. -/

variable {Baseline Target : FiniteObject.{u} → Prop}

/-- **The canonical realization of a restricted declared reading**: the
canonical cut-state representative of the raw realization, read back as a
piece on the same interface. -/
noncomputable def canonicalDeclaredState
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object support) :=
  (CanonicalPiece.cutStateRepresentative baselineInvariant targetInvariant
    (declaredState object support declaredSupport retained)).toPiece

/-- The canonical realization keeps the unrestricted boundary-degree
profile. -/
theorem canonicalDeclaredState_boundaryDegreeProfile
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (canonicalDeclaredState object support baselineInvariant targetInvariant
        declaredSupport retained).boundaryDegreeProfile =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        support).boundaryDegreeProfile :=
  ((CanonicalPiece.cutStateRepresentative_reading baselineInvariant
      targetInvariant
      (declaredState object support declaredSupport retained)).1).trans
    (declaredState_boundaryDegreeProfile object support declaredSupport
      retained)

/-- The canonical realization is registered in the same generated
certificate fibre as the raw one. -/
theorem canonicalDeclaredState_registered
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate)
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support) :
    (canonicalDeclaredState object support baselineInvariant targetInvariant
        declaredSupport retained).boundaryDegreeProfile =
      (deriveBoundariedAtomProfile
        (Strategy.InterfaceReplacement.SupportAtom.properAtom object support
          connected proper)).boundaryDegreeProfile :=
  (canonicalDeclaredState_boundaryDegreeProfile object support
      baselineInvariant targetInvariant declaredSupport retained).trans
    (deriveBoundariedAtomProfile
      (Strategy.InterfaceReplacement.SupportAtom.properAtom object support
        connected proper)).profile_eq.symm

/-- **The canonical realization answers every context exactly as the raw
one.**  The target-response comparison against gluings is therefore indifferent
to which realization is used. -/
theorem canonicalDeclaredState_contextEquivalent
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    Response.ContextEquivalent Target
      (canonicalDeclaredState object support baselineInvariant targetInvariant
        declaredSupport retained)
      (declaredState object support declaredSupport retained) :=
  (CanonicalPiece.cutStateRepresentative_reading baselineInvariant
    targetInvariant
    (declaredState object support declaredSupport retained)).2.1

/-- A target defect of the canonical realization against any fixed reading is
exactly a target defect of the raw realization. -/
theorem canonicalDeclaredState_targetDefect_iff
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate)
    (other : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object support)) :
    Response.TargetDefect Target
        (canonicalDeclaredState object support baselineInvariant
          targetInvariant declaredSupport retained) other ↔
      Response.TargetDefect Target
        (declaredState object support declaredSupport retained) other :=
  Response.targetDefect_congr_left
    (canonicalDeclaredState_contextEquivalent object support
      baselineInvariant targetInvariant declaredSupport retained)

/-- The canonical realization inherits the baseline of every completion the
raw realization satisfies. -/
theorem canonicalDeclaredState_baseline
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate)
    (outside : OutsideContext
      (Strategy.InterfaceReplacement.SupportAtom.boundary object support))
    (baseline : Baseline
      (glue (declaredState object support declaredSupport retained) outside)) :
    Baseline
      (glue (canonicalDeclaredState object support baselineInvariant
        targetInvariant declaredSupport retained) outside) :=
  (CanonicalPiece.cutStateRepresentative_reading baselineInvariant
    targetInvariant
    (declaredState object support declaredSupport retained)).2.2 outside
    baseline

/-- The canonical realization never grows past the unrestricted piece. -/
theorem canonicalDeclaredState_size_le
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (CanonicalPiece.cutStateRepresentative baselineInvariant targetInvariant
        (declaredState object support declaredSupport retained)).size ≤
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        support).internalVertexCount :=
  CanonicalPiece.cutStateRepresentative_size_le baselineInvariant
    targetInvariant (declaredState object support declaredSupport retained)

/-- Exact vertex accounting of the canonically realized restriction glued to
the support's own outside context. -/
theorem canonicalDeclaredState_glue_vertexCount
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (glue (canonicalDeclaredState object support baselineInvariant
        targetInvariant declaredSupport retained)
        (Strategy.InterfaceReplacement.SupportAtom.outside object
          support)).vertexCount =
      (Strategy.InterfaceReplacement.SupportAtom.boundary object
          support).vertexCount +
        (CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (declaredState object support declaredSupport retained)).size +
        (Strategy.InterfaceReplacement.SupportAtom.outside object
          support).internalVertexCount := by
  rw [canonicalDeclaredState, glue_vertexCount,
    CanonicalPiece.toPiece_internalVertexCount]

/-- **Descent is exactly strict canonical shrinkage.**  The completed canonical
realization is strictly smaller than the ambient object precisely when the
canonical representative has strictly fewer internal vertices than the
unrestricted piece — the *"strictly smaller"* clause of
`def:proper-quotient-representative`. -/
theorem canonicalDeclaredState_glue_vertexCount_lt_iff
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (retained : Finset Coordinate) :
    (glue (canonicalDeclaredState object support baselineInvariant
          targetInvariant declaredSupport retained)
        (Strategy.InterfaceReplacement.SupportAtom.outside object
          support)).vertexCount < object.vertexCount ↔
      (CanonicalPiece.cutStateRepresentative baselineInvariant targetInvariant
          (declaredState object support declaredSupport retained)).size <
        (Strategy.InterfaceReplacement.SupportAtom.piece object
          support).internalVertexCount := by
  rw [canonicalDeclaredState_glue_vertexCount object support baselineInvariant
      targetInvariant declaredSupport retained,
    vertexCount_decomposition object support]
  omega

end ResponseRealization

/-! ## The continuation-switch consumers

`def:typeA-continuation-classes` consumes the realization twice: the two
separated coordinates' declared readings are registered on the switch
support's interface (`Separation.leftReading`/`rightReading`), and the
identification on the switch support is a reading whose base realization is
the support's own piece and whose proper restrictions are realized canonically
(`SwitchReading`).  Both are assembled below from declared data alone. -/

namespace DecoratedHandoff

open Hypostructure

variable {object : FiniteObject.{u}}

/-- **A separation assembled from declared data.**  The structural payload —
two rooted germs through one completion port, their maximal common prefix and
distinct next incidences, and the connected proper switch support carrying
both — is exactly what a finite germ-pair schedule computes; the two
registered boundary readings are the semantic realizations of the two
coordinates' retained declared supports, and their registration in the switch
support's generated certificate is a theorem of the realization rather than a
declared field. -/
noncomputable def separationOfDeclared
    {support : Finset object.Vertex} {receiver port : object.Vertex}
    (left right : RootedGerm object support receiver port)
    (common : List object.Vertex)
    (separator nextLeft nextRight : object.Vertex)
    (tailLeft tailRight : List object.Vertex)
    (leftEq : left.path = common ++ separator :: nextLeft :: tailLeft)
    (rightEq : right.path = common ++ separator :: nextRight :: tailRight)
    (distinct : nextLeft ≠ nextRight)
    (switchSupport : Finset object.Vertex)
    (leftGerm_subset : ∀ vertex ∈ left.path, vertex ∈ switchSupport)
    (rightGerm_subset : ∀ vertex ∈ right.path, vertex ∈ switchSupport)
    (switchConnected :
      Graph.SupportComponents.Connected.ConnectedOn object switchSupport)
    (switchProper : ∃ vertex, vertex ∉ switchSupport)
    {Coordinate : Type v}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (leftRetained rightRetained : Finset Coordinate) :
    Separation object support receiver port where
  left := left
  right := right
  common := common
  separator := separator
  nextLeft := nextLeft
  nextRight := nextRight
  tailLeft := tailLeft
  tailRight := tailRight
  leftEq := leftEq
  rightEq := rightEq
  distinct := distinct
  switchSupport := switchSupport
  leftGerm_subset := leftGerm_subset
  rightGerm_subset := rightGerm_subset
  switchConnected := switchConnected
  switchProper := switchProper
  leftReading :=
    Graph.ResponseRealization.declaredState object switchSupport
      declaredSupport leftRetained
  rightReading :=
    Graph.ResponseRealization.declaredState object switchSupport
      declaredSupport rightRetained
  leftRegistered :=
    Graph.ResponseRealization.declaredState_registered object switchSupport
      declaredSupport leftRetained switchConnected switchProper
  rightRegistered :=
    Graph.ResponseRealization.declaredState_registered object switchSupport
      declaredSupport rightRetained switchConnected switchProper

variable {support : Finset object.Vertex} {receiver port : object.Vertex}
variable {Baseline Target : FiniteObject.{u} → Prop}

/-- The realization schedule of a declared switch reading: the base coordinate
set reads the switch support's own piece — a reading *of* the switch support
reads that support — and every other retained set is realized canonically. -/
noncomputable def switchState
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base retained : Finset Coordinate) :
    Graph.BoundaryPiece separation.interface :=
  letI : DecidableEq (Finset Coordinate) := Classical.decEq _
  if retained = base then separation.atom.decomposition.piece
  else
    Graph.ResponseRealization.canonicalDeclaredState object
      separation.switchSupport baselineInvariant targetInvariant
      declaredSupport retained

/-- At the base coordinate set the schedule reads the switch support's own
piece. -/
theorem switchState_base
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base : Finset Coordinate) :
    switchState separation baselineInvariant targetInvariant declaredSupport
        base base =
      separation.atom.decomposition.piece := by
  unfold switchState
  exact if_pos rfl

/-- At every other retained set the schedule reads the canonical realization
of the declared coordinates. -/
theorem switchState_of_ne
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base : Finset Coordinate) {retained : Finset Coordinate}
    (different : retained ≠ base) :
    switchState separation baselineInvariant targetInvariant declaredSupport
        base retained =
      Graph.ResponseRealization.canonicalDeclaredState object
        separation.switchSupport baselineInvariant targetInvariant
        declaredSupport retained := by
  unfold switchState
  exact if_neg different

/-- **The switch reading assembled from declared data.**

The base coordinate set realizes the switch support's own piece — a reading
*of* the switch support reads that support — and every proper restriction is
realized canonically, so the registered-fibre clause is a theorem and the
identification is testable against every outside context.  The one datum the
declared coordinates must genuinely supply is `shrinks`: the canonical
representative of the identified reading is strictly smaller than the switch
support's piece.  Raw edge-forgetting can never provide it
(`ResponseRealization.declaredState_glue_vertexCount`), and it is exactly the
*"strictly smaller"* clause of `def:proper-quotient-representative`, so it
enters here as the declared strict-progress witness and nowhere else. -/
noncomputable def switchReadingOfDeclared
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base reduced : Finset Coordinate)
    (reduced_ssubset : reduced ⊂ base)
    (shrinks :
      (Graph.CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (Graph.ResponseRealization.declaredState object
            separation.switchSupport declaredSupport reduced)).size <
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          separation.switchSupport).internalVertexCount) :
    SwitchReading separation where
  Coordinate := Coordinate
  state :=
    switchState separation baselineInvariant targetInvariant declaredSupport
      base
  base := base
  reduced := reduced
  reduced_ssubset := reduced_ssubset
  registered := by
    intro _internal retained _subset
    by_cases same : retained = base
    · rw [same, switchState_base]
      exact separation.certificate.profile_eq.symm
    · rw [switchState_of_ne separation baselineInvariant targetInvariant
        declaredSupport base same]
      exact Graph.ResponseRealization.canonicalDeclaredState_registered object
        separation.switchSupport baselineInvariant targetInvariant
        declaredSupport retained separation.switchConnected
        separation.switchProper
  baseIsPiece :=
    switchState_base separation baselineInvariant targetInvariant
      declaredSupport base
  descends := by
    have different : reduced ≠ base := by
      intro same
      rw [same] at reduced_ssubset
      exact ssubset_irrefl base reduced_ssubset
    rw [switchState_of_ne separation baselineInvariant targetInvariant
      declaredSupport base different]
    exact (Graph.ResponseRealization.canonicalDeclaredState_glue_vertexCount_lt_iff
      object separation.switchSupport baselineInvariant targetInvariant
      declaredSupport reduced).mpr shrinks

/-- The assembled reading's identified realization is the canonical
realization of the reduced coordinate set. -/
theorem switchReadingOfDeclared_quotient_eq
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base reduced : Finset Coordinate)
    (reduced_ssubset : reduced ⊂ base)
    (shrinks :
      (Graph.CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (Graph.ResponseRealization.declaredState object
            separation.switchSupport declaredSupport reduced)).size <
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          separation.switchSupport).internalVertexCount) :
    (switchReadingOfDeclared separation baselineInvariant targetInvariant
        declaredSupport base reduced reduced_ssubset shrinks).quotient =
      Graph.ResponseRealization.canonicalDeclaredState object
        separation.switchSupport baselineInvariant targetInvariant
        declaredSupport reduced := by
  have different : reduced ≠ base := by
    intro same
    rw [same] at reduced_ssubset
    exact ssubset_irrefl base reduced_ssubset
  exact switchState_of_ne separation baselineInvariant targetInvariant
    declaredSupport base different

/-- The assembled reading's unidentified realization is the switch support's
own piece. -/
theorem switchReadingOfDeclared_full_eq
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base reduced : Finset Coordinate)
    (reduced_ssubset : reduced ⊂ base)
    (shrinks :
      (Graph.CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (Graph.ResponseRealization.declaredState object
            separation.switchSupport declaredSupport reduced)).size <
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          separation.switchSupport).internalVertexCount) :
    (switchReadingOfDeclared separation baselineInvariant targetInvariant
        declaredSupport base reduced reduced_ssubset shrinks).full =
      separation.atom.decomposition.piece := by
  exact switchState_base separation baselineInvariant targetInvariant
    declaredSupport base

/-- Both realizations of the assembled reading lie in one boundary-degree
fibre, with no premise: the registration is a theorem of the realization. -/
theorem switchReadingOfDeclared_fibre
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base reduced : Finset Coordinate)
    (reduced_ssubset : reduced ⊂ base)
    (shrinks :
      (Graph.CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (Graph.ResponseRealization.declaredState object
            separation.switchSupport declaredSupport reduced)).size <
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          separation.switchSupport).internalVertexCount) :
    (switchReadingOfDeclared separation baselineInvariant targetInvariant
        declaredSupport base reduced reduced_ssubset
        shrinks).quotient.boundaryDegreeProfile =
      (switchReadingOfDeclared separation baselineInvariant targetInvariant
        declaredSupport base reduced reduced_ssubset
        shrinks).full.boundaryDegreeProfile := by
  rw [switchReadingOfDeclared_quotient_eq, switchReadingOfDeclared_full_eq]
  exact (Graph.ResponseRealization.canonicalDeclaredState_registered object
      separation.switchSupport baselineInvariant targetInvariant
      declaredSupport reduced separation.switchConnected
      separation.switchProper).trans
    separation.certificate.profile_eq

/-- **The declared identification is absorbed or target-defective, with no
premise and no third outcome.**  This is the exhaustive split the exit-`(4)`
family's continuation-switch clause fires on: in the defect case the assembled
reading *is* the target-defective quotient datum, and in the complete case the
identification is a target-complete response quotient. -/
theorem switchReadingOfDeclared_targetComplete_or_targetDefect
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base reduced : Finset Coordinate)
    (reduced_ssubset : reduced ⊂ base)
    (shrinks :
      (Graph.CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (Graph.ResponseRealization.declaredState object
            separation.switchSupport declaredSupport reduced)).size <
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          separation.switchSupport).internalVertexCount) :
    Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile Target
        (switchReadingOfDeclared separation baselineInvariant targetInvariant
          declaredSupport base reduced reduced_ssubset shrinks).quotient
        (switchReadingOfDeclared separation baselineInvariant targetInvariant
          declaredSupport base reduced reduced_ssubset shrinks).full ∨
      Response.TargetDefect Target
        (switchReadingOfDeclared separation baselineInvariant targetInvariant
          declaredSupport base reduced reduced_ssubset shrinks).quotient
        (switchReadingOfDeclared separation baselineInvariant targetInvariant
          declaredSupport base reduced reduced_ssubset shrinks).full :=
  Response.targetComplete_or_targetDefect_of_profile_eq Target
    (switchReadingOfDeclared_fibre separation baselineInvariant
      targetInvariant declaredSupport base reduced reduced_ssubset shrinks)

/-- **The assembled reading is absorbed** (`def:typeA-continuation-classes`):
the identification on the switch support is target-defective or
target-complete on the nontrivial response quotient, before any enlargement
alternative is even consulted. -/
theorem switchReadingOfDeclared_absorbed
    (separation : Separation object support receiver port)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    {Coordinate : Type u}
    (declaredSupport : Coordinate → Finset object.Vertex)
    (base reduced : Finset Coordinate)
    (reduced_ssubset : reduced ⊂ base)
    (shrinks :
      (Graph.CanonicalPiece.cutStateRepresentative baselineInvariant
          targetInvariant
          (Graph.ResponseRealization.declaredState object
            separation.switchSupport declaredSupport reduced)).size <
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          separation.switchSupport).internalVertexCount)
    (Enlarges : Prop) :
    Absorbed Target
      (switchReadingOfDeclared separation baselineInvariant targetInvariant
        declaredSupport base reduced reduced_ssubset shrinks) Enlarges := by
  rcases switchReadingOfDeclared_targetComplete_or_targetDefect separation
      baselineInvariant targetInvariant declaredSupport base reduced
      reduced_ssubset shrinks with complete | defect
  · exact Or.inr (Or.inl complete)
  · exact Or.inl defect

end DecoratedHandoff

end Hypostructure.Graph
