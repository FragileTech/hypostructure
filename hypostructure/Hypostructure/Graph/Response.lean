import Hypostructure.Core.Response.FiniteTable
import Hypostructure.Graph.Gluing
import Hypostructure.Graph.Target

/-!
# Exact graph responses

Graph evaluates a boundary piece only by gluing it to a caller-supplied
outside context and observing the resulting finite graph.  Core owns response
vectors, finite comparison, symbolic coverage, target-complete equivalence,
orientation, residual decisions, and ledger retention.

No declaration in this module enumerates graphs or outside contexts.  A finite
coordinate schedule is supplied separately by the incoming residual.
-/

namespace Hypostructure.Graph.Response

open Hypostructure.Core

universe u uContext uCoordinate uValue uMeasure uProfile

/-! ## Literal all-context target completeness -/

/-- Two pieces with the same labelled boundary have identical target response
against every literal outside context.  This is symbolic universal coverage;
no context family is enumerated. -/
def ContextEquivalent {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (left right : BoundaryPiece boundary) : Prop :=
  forall outside : OutsideContext boundary,
    Target (glue left outside) <-> Target (glue right outside)

/-- Exact graph target-completeness combines equality in a caller-selected
immutable profile fibre with universal target response.  Context equivalence
alone is not a target-complete identification. -/
structure TargetComplete {boundary : Boundary.{u}}
    {Profile : Type uProfile} (profile : BoundaryPiece boundary -> Profile)
    (Target : FiniteObject.{u} -> Prop)
    (left right : BoundaryPiece boundary) : Prop where
  profile_eq : profile left = profile right
  contextEquivalent : ContextEquivalent Target left right

/-- One literal outside context witnessing failure of target equivalence. -/
def TargetDefect {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (left right : BoundaryPiece boundary) : Prop :=
  exists outside : OutsideContext boundary,
    Not (Target (glue left outside) <-> Target (glue right outside))

/-- Different immutable profile fibres can never be target-completely
identified, independently of every all-context response test. -/
theorem profile_ne_not_targetComplete
    {boundary : Boundary.{u}}
    {Profile : Type uProfile} {profile : BoundaryPiece boundary -> Profile}
    {Target : FiniteObject.{u} -> Prop}
    {left right : BoundaryPiece boundary}
    (different : profile left ≠ profile right) :
    Not (TargetComplete profile Target left right) := by
  intro complete
  exact different complete.profile_eq

/-- Target completeness projects to the context-universality obligation. -/
theorem TargetComplete.contextUniversal
    {boundary : Boundary.{u}}
    {Profile : Type uProfile} {profile : BoundaryPiece boundary -> Profile}
    {Target : FiniteObject.{u} -> Prop}
    {left right : BoundaryPiece boundary}
    (complete : TargetComplete profile Target left right) :
    ContextEquivalent Target left right :=
  complete.contextEquivalent

/-- Failure of the all-context clause produces a typed distinguishing
context.  A profile mismatch alone does not produce such a witness. -/
theorem targetDefect_of_not_contextEquivalent
    {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} -> Prop}
    {left right : BoundaryPiece boundary}
    (failure : Not (ContextEquivalent Target left right)) :
    TargetDefect Target left right := by
  simp only [ContextEquivalent, not_forall] at failure
  obtain ⟨outside, distinguishes⟩ := failure
  exact ⟨outside, distinguishes⟩

/-- **`lem:typeA-internal-quotient-mixed`, the framework mechanism.**

*"Failure of target-completeness gives a compatible outside context and two
realizations ... with the same image in the quotient, but with different target
predicates after gluing.  ...  The two realizations have the same image in the
quotient, so a distinguishing event must use at least one coordinate forgotten
by it."*

When the smaller reading can only realize *fewer* targets -- which is what an
edge-forgetting quotient does to a monotone target -- the distinguishing
context is forced to sit on the larger side: it realizes the target after
gluing `right` and fails to after gluing `left`.  So every witness of the
distinguishing realization uses something `left` forgot.  Nothing here is
specific to carriers; it is the one-sidedness of a defect under a monotone
target. -/
theorem exists_context_of_not_contextEquivalent {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} -> Prop} {left right : BoundaryPiece boundary}
    (monotone : forall outside : OutsideContext boundary,
      Target (glue left outside) -> Target (glue right outside))
    (failure : Not (ContextEquivalent Target left right)) :
    Exists fun outside : OutsideContext boundary =>
      Target (glue right outside) /\ Not (Target (glue left outside)) := by
  obtain ⟨outside, distinguishes⟩ := targetDefect_of_not_contextEquivalent failure
  refine ⟨outside, ?_, ?_⟩
  · by_contra missing
    exact distinguishes ⟨fun realized => absurd realized
      (fun realized => missing (monotone outside realized)),
      fun realized => absurd realized missing⟩
  · intro realized
    exact distinguishes ⟨fun _ => monotone outside realized, fun _ => realized⟩

theorem notTargetComplete_of_targetDefect
    {boundary : Boundary.{u}}
    {Profile : Type uProfile}
    {profile : BoundaryPiece boundary -> Profile}
    {Target : FiniteObject.{u} -> Prop}
    {left right : BoundaryPiece boundary}
    (defect : TargetDefect Target left right) :
    Not (TargetComplete profile Target left right) := by
  intro complete
  rcases defect with ⟨outside, distinguishes⟩
  exact distinguishes (complete.contextEquivalent outside)

/-- Register exact graph responses for a caller-selected family of normalized
outside contexts.  The family can be all outside contexts or a typed family
already owned by the predecessor residual. -/
noncomputable def exactSystem
    {boundary : Boundary.{u}}
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (Value : Type uValue)
    (observe : FiniteObject.{u} -> Value) :
    Core.Response.System (BoundaryPiece boundary) :=
  Core.Response.System.ofDecodedContexts Context Coordinate Value
    (fun piece context => observe (glue piece (outside context))) decode

@[simp]
theorem exactSystem_contextResponse
    {boundary : Boundary.{u}}
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (Value : Type uValue)
    (observe : FiniteObject.{u} -> Value)
    (piece : BoundaryPiece boundary) (context : Context) :
    (exactSystem Context outside Coordinate decode Value observe).contextResponse
        piece context =
      observe (glue piece (outside context)) :=
  rfl

@[simp]
theorem exactSystem_coordinateResponse
    {boundary : Boundary.{u}}
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (Value : Type uValue)
    (observe : FiniteObject.{u} -> Value)
    (piece : BoundaryPiece boundary) (coordinate : Coordinate) :
    (exactSystem Context outside Coordinate decode Value observe).coordinateResponse
        piece coordinate =
      observe (glue piece (outside (decode coordinate))) :=
  rfl

/-- The unrestricted constructor, whose semantic context type is literally
all finite outside contexts at the common boundary. -/
noncomputable def outsideSystem
    {boundary : Boundary.{u}}
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> OutsideContext boundary)
    (Value : Type uValue)
    (observe : FiniteObject.{u} -> Value) :
    Core.Response.System (BoundaryPiece boundary) :=
  exactSystem (OutsideContext boundary) id Coordinate decode Value observe

/-- Exact Boolean responses for an external graph target.  Decidability is an
explicit semantic input; Graph does not search for a target witness here. -/
noncomputable def targetSystem
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    Core.Response.System (BoundaryPiece boundary) :=
  exactSystem Context outside Coordinate decode Bool
    (fun object => @decide (Target object) (decideTarget object))

@[simp]
theorem targetSystem_contextResponse
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (piece : BoundaryPiece boundary) (context : Context) :
    (targetSystem Target decideTarget Context outside Coordinate decode).contextResponse
        piece context =
      @decide (Target (glue piece (outside context)))
        (decideTarget (glue piece (outside context))) :=
  rfl

@[simp]
theorem targetSystem_coordinateResponse
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (piece : BoundaryPiece boundary) (coordinate : Coordinate) :
    (targetSystem Target decideTarget Context outside Coordinate decode).coordinateResponse
        piece coordinate =
      @decide (Target (glue piece (outside (decode coordinate))))
        (decideTarget (glue piece (outside (decode coordinate)))) :=
  rfl

/-! Translate Core's literal Boolean response mismatch into the graph target
defect.  The context and both observations are read from one response system;
the adapter never accepts a pre-built negated target. -/
theorem targetDefect_of_responseDefect
    {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} -> Prop}
    (decideTarget : forall object, Decidable (Target object))
    {Context : Type uContext}
    (outside : Context -> OutsideContext boundary)
    {Coordinate : Type uCoordinate}
    (decode : Coordinate -> Context)
    {representatives : Core.Response.Representatives (BoundaryPiece boundary)}
    (defect : Core.Response.FiniteTable.ResponseDefect
      (targetSystem Target decideTarget Context outside Coordinate decode)
      representatives) :
    TargetDefect Target representatives.source representatives.replacement := by
  rcases defect with ⟨context, mismatch⟩
  refine targetDefect_of_not_contextEquivalent ?_
  intro equivalent
  apply mismatch
  have iffAt := equivalent (outside context)
  change @decide (Target (glue representatives.source (outside context)))
      (decideTarget _) =
    @decide (Target (glue representatives.replacement (outside context)))
      (decideTarget _)
  by_cases left : Target (glue representatives.source (outside context)) <;>
    by_cases right : Target (glue representatives.replacement (outside context)) <;>
      simp_all

/-- The direct target predicate on glued graphs is represented exactly by the
Boolean target response. -/
noncomputable def targetSemantics
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    Core.Response.TargetSemantics
      (targetSystem Target decideTarget Context outside Coordinate decode) := by
  unfold targetSystem exactSystem
  refine {
    TargetResponse := fun piece context =>
      Target (glue piece (outside context))
    Accepts := fun response => response = true
    target_iff_accepts := ?_
  }
  intro piece context
  change Target (glue piece (outside context)) <->
    @decide (Target (glue piece (outside context)))
      (decideTarget (glue piece (outside context))) = true
  exact decide_eq_true_iff.symm

@[simp]
theorem targetSemantics_targetResponse
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (piece : BoundaryPiece boundary) (context : Context) :
    (targetSemantics Target decideTarget Context outside Coordinate decode).TargetResponse
        piece context =
      Target (glue piece (outside context)) :=
  rfl

/-- A target interface transports the response of the extracted piece and
outside context back to the original ambient graph. -/
theorem extractedTarget_iff_accepts
    {Target : FiniteObject.{u} -> Prop}
    (interface : TargetInterface Target)
    (decideTarget : forall object, Decidable (Target object))
    {object : FiniteObject.{u}} (site : OwnedDecomposition object) :
    Target object <->
      @decide (Target (glue site.piece site.outside))
        (decideTarget (glue site.piece site.outside)) = true := by
  have reconstructed :
      Target (glue site.piece site.outside) <-> Target object :=
    interface.isomorphismInvariant.iff_of_iso
      ⟨site.reconstructionIso⟩
  exact reconstructed.symm.trans (by simp)

/-- Exact realization of every semantic context by a scheduled coordinate
implies Core symbolic coverage.  The realization theorem is supplied by the
caller; this constructor does not infer it from an encoding or injectivity. -/
def coverageOfExactContexts
    {boundary : Boundary.{u}}
    {Context : Type uContext}
    {outside : Context -> OutsideContext boundary}
    {Coordinate : Type uCoordinate}
    {decode : Coordinate -> Context}
    {Value : Type uValue}
    {observe : FiniteObject.{u} -> Value}
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (complete : forall context, Exists fun index : Fin schedule.coordinates.length =>
      context = decode (schedule.coordinates.get index)) :
    Core.Response.FiniteTable.SymbolicCoverage
      (exactSystem Context outside Coordinate decode Value observe)
      representatives schedule :=
  Core.Response.FiniteTable.SymbolicCoverage.ofDecodeComplete
    (exactSystem Context outside Coordinate decode Value observe)
    representatives schedule (by
      intro context
      obtain ⟨index, realized⟩ := complete context
      exact ⟨index, realized⟩)

/-! A complete finite context enumeration is the canonical graph-side
specialization of the exact-context coverage API.  Core owns conversion of
the enumeration to an ordered response schedule and the resulting index
witnesses. -/
def coverageOfCompleteContexts
    {boundary : Boundary.{u}}
    {Context : Type uContext}
    (contexts : Core.Finite.CompleteEnumeration Context)
    {outside : Context -> OutsideContext boundary}
    {Value : Type uValue}
    {observe : FiniteObject.{u} -> Value}
    {representatives : Core.Response.Representatives (BoundaryPiece boundary)} :
    Core.Response.FiniteTable.SymbolicCoverage
      (exactSystem Context outside Context id Value observe)
      representatives
      (Core.Response.FiniteTable.ExactSchedule.ofCompleteEnumeration contexts) :=
  Core.Response.FiniteTable.SymbolicCoverage.ofDecodeComplete
    (exactSystem Context outside Context id Value observe)
    representatives
    (Core.Response.FiniteTable.ExactSchedule.ofCompleteEnumeration contexts)
    (by
      intro context
      change ∃ index,
        context = contexts.values[index]
      exact Core.Response.FiniteTable.ExactSchedule.complete_ofCompleteEnumeration
        contexts context)

section TargetCompleteness

variable {boundary : Boundary.{u}}
variable {Target : FiniteObject.{u} -> Prop}
variable {decideTarget : forall object, Decidable (Target object)}
variable {Context : Type uContext}
variable {outside : Context -> OutsideContext boundary}
variable {Coordinate : Type uCoordinate}
variable {decode : Coordinate -> Context}

local notation "targetResponses" =>
  targetSystem Target decideTarget Context outside Coordinate decode

local notation "targetMeaning" =>
  targetSemantics Target decideTarget Context outside Coordinate decode

/-- Finite neutrality yields same-interface target equivalence only after an
explicit symbolic coverage theorem has been supplied. -/
def targetCompleteOfCoverage
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (neutral : Core.Response.FiniteTable.Neutrality
      (Core.Response.FiniteTable.Table.build targetResponses representatives
        schedule))
    (coverage : Core.Response.FiniteTable.SymbolicCoverage targetResponses
      representatives schedule) :
    Core.Response.TargetCompleteEquivalence targetMeaning representatives :=
  neutral.targetComplete coverage targetMeaning

/-- The stronger exact-context completeness certificate is converted to
symbolic coverage before Core derives target-complete equivalence. -/
def targetCompleteOfExactContexts
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (neutral : Core.Response.FiniteTable.Neutrality
      (Core.Response.FiniteTable.Table.build targetResponses representatives
        schedule))
    (complete : forall context, Exists fun index : Fin schedule.coordinates.length =>
      context = decode (schedule.coordinates.get index)) :
    Core.Response.TargetCompleteEquivalence targetMeaning representatives :=
  targetCompleteOfCoverage representatives schedule neutral
    (coverageOfExactContexts representatives schedule complete)

/-- A same-interface exchange is exposed only after target completeness and
independent strict-progress evidence.  Core owns the resulting orientation. -/
noncomputable def exchangeAfterStrictOfCoverage
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (neutral : Core.Response.FiniteTable.Neutrality
      (Core.Response.FiniteTable.Table.build targetResponses representatives
        schedule))
    (coverage : Core.Response.FiniteTable.SymbolicCoverage targetResponses
      representatives schedule)
    (progress : Core.Response.ProgressSystem.{_, uMeasure}
      (BoundaryPiece boundary))
    (direction : Core.Response.Direction)
    (strict : Core.Response.StrictEvidence progress representatives direction) :
    Core.Response.OrientedComparison targetMeaning representatives progress :=
  Core.Response.OrientedComparison.afterStrict
    (targetCompleteOfCoverage representatives schedule neutral coverage) strict

noncomputable def exchangeAfterNonzeroOfCoverage
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (neutral : Core.Response.FiniteTable.Neutrality
      (Core.Response.FiniteTable.Table.build targetResponses representatives
        schedule))
    (coverage : Core.Response.FiniteTable.SymbolicCoverage targetResponses
      representatives schedule)
    (progress : Core.Response.ProgressSystem.{_, uMeasure}
      (BoundaryPiece boundary))
    {signed : Core.Response.SignedIncrement progress representatives}
    (law : Core.Response.NonzeroOrientationLaw progress representatives signed)
    (evidence : Core.Response.NonzeroEvidence signed) :
    Core.Response.OrientedComparison targetMeaning representatives progress :=
  Core.Response.OrientedComparison.afterNonzero
    (targetCompleteOfCoverage representatives schedule neutral coverage)
    law evidence

/-- Exact finite context completeness is sufficient for exchange only when it
is accompanied by independent strict-progress evidence. -/
noncomputable def exchangeAfterStrictOfExactContexts
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (neutral : Core.Response.FiniteTable.Neutrality
      (Core.Response.FiniteTable.Table.build targetResponses representatives
        schedule))
    (complete : forall context, Exists fun index : Fin schedule.coordinates.length =>
      context = decode (schedule.coordinates.get index))
    (progress : Core.Response.ProgressSystem.{_, uMeasure}
      (BoundaryPiece boundary))
    (direction : Core.Response.Direction)
    (strict : Core.Response.StrictEvidence progress representatives direction) :
    Core.Response.OrientedComparison targetMeaning representatives progress :=
  exchangeAfterStrictOfCoverage representatives schedule neutral
    (coverageOfExactContexts representatives schedule complete)
    progress direction strict

/-! A nonzero signed increment follows the same exact-context coverage path.
The increment law and nonzero certificate are independent mathematical
inputs; Core selects the strict orientation and carries its proof. -/
noncomputable def exchangeAfterNonzeroOfExactContexts
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (schedule : Core.Response.FiniteTable.ExactSchedule Coordinate)
    (neutral : Core.Response.FiniteTable.Neutrality
      (Core.Response.FiniteTable.Table.build targetResponses representatives
        schedule))
    (complete : forall context, Exists fun index : Fin schedule.coordinates.length =>
      context = decode (schedule.coordinates.get index))
    (progress : Core.Response.ProgressSystem.{_, uMeasure}
      (BoundaryPiece boundary))
    {signed : Core.Response.SignedIncrement progress representatives}
    (law : Core.Response.NonzeroOrientationLaw progress representatives signed)
    (evidence : Core.Response.NonzeroEvidence signed) :
    Core.Response.OrientedComparison targetMeaning representatives progress :=
  Core.Response.OrientedComparison.afterNonzero
    (targetCompleteOfExactContexts representatives schedule neutral complete)
    law evidence

end TargetCompleteness

end Hypostructure.Graph.Response
