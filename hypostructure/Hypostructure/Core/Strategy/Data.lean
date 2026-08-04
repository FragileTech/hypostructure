import Hypostructure.Core.Problem
import Hypostructure.Core.Progress
import Hypostructure.Core.Strategy.ProblemInput
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Ledger
import Hypostructure.Core.Minimality
import Hypostructure.Core.Strategy.InterfaceReplacement
import Hypostructure.Core.Strategy.ObstructionPackingSemantics
import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebraSemantics
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics
import Hypostructure.Core.Strategy.FiniteDensityBudgetSemantics
import Hypostructure.Core.Strategy.FiniteStateCapacitySemantics
import Hypostructure.Core.Strategy.FiniteScheduleCapacitySemantics
import Hypostructure.Core.Strategy.ScaleThresholdDichotomySemantics
import Hypostructure.Core.Strategy.AtomContextObstructionDichotomySemantics
import Hypostructure.Core.Strategy.OrderedSurplusActivationSemantics
import Hypostructure.Core.Strategy.BaselineDemandAccountingSemantics
import Hypostructure.Core.Strategy.CanonicalPairResponseAccountingSemantics
import Hypostructure.Core.Strategy.CanonicalCapacityTokenAccountingSemantics
import Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressureSemantics
import Hypostructure.Core.Strategy.FiniteBottleneckClassificationSemantics
import Hypostructure.Core.Strategy.HomogeneousBottleneckSemantics
import Hypostructure.Core.Strategy.SupportComplementNormalizationSemantics
import Hypostructure.Core.Strategy.BoundaryDemandAccountingSemantics
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics
import Hypostructure.Core.Strategy.TargetRelativeRankDichotomySemantics
import Hypostructure.Core.Strategy.ColdBranchAggregation
import Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation
import Hypostructure.Core.Strategy.Route8CarrierClosureSemantics

/-!
# Registered problem input and strategy data

The application boundary supplies one Core problem, one target, and one
`StrategyData` record of plain mathematical data: finite schedules, decision
procedures, budgets, classifiers, and certified tables, all indexed by the
initial residual.  Only the private strategy compiler interprets these values
during execution.  No field can produce a stage, route, contract, residual,
outcome, report, or proof of the target statement.
-/

namespace Hypostructure.Core

open Hypostructure.Core.Residual

universe uAmbient uBranch uData

/-- Author-facing documentation carried into diagnostics and exported proof
artifacts.  It is never consumed by a strategy contract or proof. -/
structure Documentation where
  name : String := ""
  note : String := ""
  tags : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- Documentation for a complete registered theorem problem.  The authored
signature and statement complement the automatically captured Lean text. -/
structure ProblemMetadata extends Documentation where
  signature : String := ""
  statement : String := ""
  deriving DecidableEq, Repr, Inhabited

namespace Strategy

abbrev InitStage (P : Core.Problem) :=
  Ledger (ProblemInput P)

structure InitStrategy (P : Core.Problem) where
  run : ProblemInput P -> InitStage P

def InitStrategy.forProblem (P : Core.Problem) : InitStrategy P where
  run input := Ledger.initial input

@[simp] theorem InitStrategy.run_residual
    (P : Core.Problem) (input : ProblemInput P) :
    residualOf ((InitStrategy.forProblem P).run input) = input :=
  rfl

@[simp] theorem InitStrategy.run_object
    (P : Core.Problem) (input : ProblemInput P) :
    (residualOf ((InitStrategy.forProblem P).run input)).object = input.object :=
  rfl

end Strategy

/-! ## Registered strategy data families

Each structure is one registered family of mathematical data for an official
strategy key.  Fields are indexed by the initial residual; the compiler lifts
them to any later ledger stage through `residualOf`, so the residual and
ledger do all data accounting. -/

/-- One registered ordered scan family: a finite, residual-owned schedule of
items with a decidable witness predicate.  Powers `orderedWitnessScan`. -/
structure ScanData (P : Core.Problem.{uAmbient, uBranch}) where
  Item : Strategy.ProblemInput P -> Type uData
  schedule : (input : Strategy.ProblemInput P) -> Finite.Enumeration (Item input)
  witness : (input : Strategy.ProblemInput P) -> Item input -> Prop
  witnessDecidable : (input : Strategy.ProblemInput P) -> (item : Item input) ->
    Decidable (witness input item)
  metadata : Documentation := {}

/-- One registered response classification family.  Powers
`responseClassifier`. -/
structure ResponseData (P : Core.Problem.{uAmbient, uBranch}) where
  Item : Strategy.ProblemInput P -> Type uData
  Response : Strategy.ProblemInput P -> Type uData
  Class : Strategy.ProblemInput P -> Type uData
  schedule : (input : Strategy.ProblemInput P) -> Finite.Enumeration (Item input)
  observe : (input : Strategy.ProblemInput P) -> Item input -> Response input
  classify : (input : Strategy.ProblemInput P) -> Response input -> Class input
  metadata : Documentation := {}

/-- One registered capacity account.  Powers `capacityLedger`. -/
structure CapacityData (P : Core.Problem.{uAmbient, uBranch}) where
  Item : Strategy.ProblemInput P -> Type uData
  Class : Strategy.ProblemInput P -> Type uData
  schedule : (input : Strategy.ProblemInput P) -> Finite.Enumeration (Item input)
  classify : (input : Strategy.ProblemInput P) -> Item input -> Class input
  contribution : (input : Strategy.ProblemInput P) -> Item input -> Nat
  capacity : (input : Strategy.ProblemInput P) -> Class input -> Nat
  totalWithin : forall input item,
    contribution input item <= capacity input (classify input item)
  metadata : Documentation := {}

/-- One registered negative-budget localization.  Powers
`supportLocalization`. -/
structure LocalizationData (P : Core.Problem.{uAmbient, uBranch}) where
  Cell : Strategy.ProblemInput P -> Type uData
  schedule : (input : Strategy.ProblemInput P) -> Finite.Enumeration (Cell input)
  localBudget : (input : Strategy.ProblemInput P) -> Cell input -> Int
  selected : (input : Strategy.ProblemInput P) -> Cell input
  selected_negative : forall input, localBudget input (selected input) < 0
  metadata : Documentation := {}

/-- One registered rank/budget threshold split.  Powers `rankBudget`. -/
structure RankBudgetData (P : Core.Problem.{uAmbient, uBranch}) where
  rank : Strategy.ProblemInput P -> Nat
  budget : Strategy.ProblemInput P -> Nat
  threshold : Strategy.ProblemInput P -> Nat
  high : Strategy.ProblemInput P -> Prop
  low : Strategy.ProblemInput P -> Prop
  exhaustive : forall input, high input ∨ low input
  metadata : Documentation := {}

/-- One registered closed-code table.  Powers `closedCode`.  Certified
discrete tables enter here and are never recomputed. -/
structure ClosedCodeData (P : Core.Problem.{uAmbient, uBranch}) where
  Code : Strategy.ProblemInput P -> Type uData
  schedule : (input : Strategy.ProblemInput P) -> Finite.Enumeration (Code input)
  targetCode : (input : Strategy.ProblemInput P) -> Code input
  observedCode : (input : Strategy.ProblemInput P) -> Code input -> Code input
  closed : forall input,
    observedCode input (targetCode input) = targetCode input
  metadata : Documentation := {}

/-- One registered exhaustive mathematical dichotomy.  Powers `dichotomy`
branching.  Branch names such as Type A/Type B are application-level names
for these two constructors, not Core states.  `closeLeft`/`closeRight` are
optional registered branch closures: mathematical facts deriving the target
from the branch witness, consumed by the runner to close the corresponding
side mechanically. -/
structure DichotomyData (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P) where
  LeftPayload : Strategy.ProblemInput P -> Type uData
  RightPayload : Strategy.ProblemInput P -> Type uData
  classify : (input : Strategy.ProblemInput P) ->
    Sum (LeftPayload input) (RightPayload input)
  closeLeft : Option (PLift (forall input : Strategy.ProblemInput P,
    LeftPayload input -> T.Predicate input.object)) := none
  closeRight : Option (PLift (forall input : Strategy.ProblemInput P,
    RightPayload input -> T.Predicate input.object)) := none
  metadata : Documentation := {}
  /-- Ordered display metadata for Core-owned CT phases inside a composed
  strategy. Exported to JSON and ignored by execution. -/
  components : List Documentation := []
  leftMetadata : Documentation := {}
  rightMetadata : Documentation := {}

namespace DichotomyData

/--
**One registered alternative of an ordered stratification.**

The alternative is a proposition on the selected residual.  Core classifies it
classically and retains the *exact negation* on the arm that survives; a
closing arm is supplied only where the mathematics already derives the target,
either from the alternative (`closeLeft`) or from its failure (`closeRight`).

This owns no route, no ledger operation, no branch selection and no target
proof --- it is `Classical.propDecidable` and the two optional closures.  An
application that walks a finite list of ordered alternatives, as a stage
stratification does, registers one of these per stage rather than writing the
classifier out each time.

`uData` is pinned to `0` because `PLift` of a `Prop` lands in `Type 0`; that is
what lets a whole `StrategyData` record built from these stay at `.{u, u, 0}`.
-/
noncomputable def ofAlternative {P : Core.Problem.{uAmbient, uBranch}}
    {T : Core.Target P}
    (Alternative : Strategy.ProblemInput P -> Prop)
    (metadata : Documentation := {})
    (leftMetadata : Documentation := {})
    (rightMetadata : Documentation := {})
    (closeLeft : Option (PLift (forall input : Strategy.ProblemInput P,
      PLift (Alternative input) -> T.Predicate input.object)) := none)
    (closeRight : Option (PLift (forall input : Strategy.ProblemInput P,
      PLift (Not (Alternative input)) -> T.Predicate input.object)) := none) :
    DichotomyData.{uAmbient, uBranch, 0} P T where
  LeftPayload := fun input => PLift (Alternative input)
  RightPayload := fun input => PLift (Not (Alternative input))
  classify := fun input =>
    letI := Classical.propDecidable (Alternative input)
    if holds : Alternative input then Sum.inl ⟨holds⟩ else Sum.inr ⟨holds⟩
  closeLeft := closeLeft
  closeRight := closeRight
  metadata := metadata
  leftMetadata := leftMetadata
  rightMetadata := rightMetadata

@[simp] theorem ofAlternative_leftPayload {P : Core.Problem.{uAmbient, uBranch}}
    {T : Core.Target P} (Alternative : Strategy.ProblemInput P -> Prop)
    (metadata leftMetadata rightMetadata : Documentation)
    (closeLeft closeRight) (input : Strategy.ProblemInput P) :
    (ofAlternative (T := T) Alternative metadata leftMetadata rightMetadata
      closeLeft closeRight).LeftPayload input = PLift (Alternative input) :=
  rfl

@[simp] theorem ofAlternative_rightPayload {P : Core.Problem.{uAmbient, uBranch}}
    {T : Core.Target P} (Alternative : Strategy.ProblemInput P -> Prop)
    (metadata leftMetadata rightMetadata : Documentation)
    (closeLeft closeRight) (input : Strategy.ProblemInput P) :
    (ofAlternative (T := T) Alternative metadata leftMetadata rightMetadata
      closeLeft closeRight).RightPayload input =
      PLift (Not (Alternative input)) :=
  rfl

end DichotomyData

/-- Registered residual-indexed atom--context dichotomy.  The registration
contains only the mathematical projection used by the generic Strategy;
branch selection, ledger extension, and routing remain Core-owned. -/
structure AtomContextObstructionDichotomyData
    (P : Core.Problem.{uAmbient, uBranch}) where
  registration :
    Strategy.AtomContextObstructionDichotomy.Registration.{
      uAmbient, uBranch, uData, max uAmbient uBranch}
      P (Strategy.ProblemInput P)
  metadata : Documentation := {}
  components : List Documentation := []
  atomMetadata : Documentation := {}
  contextMetadata : Documentation := {}

/-- One registered exhaustive finite family of typed terminals.  The
terminal index is framework-owned (`Fin arity`), while the payload may depend
on the selected terminal.  A DAG that invokes this family must provide
exactly one continuation per terminal; that arity check is part of sealed DAG
compliance, not an executable application callback. -/
structure FiniteTerminalFamilyData (P : Core.Problem.{uAmbient, uBranch})
    (_T : Core.Target P) where
  arity : Nat
  Payload : Strategy.ProblemInput P -> Fin arity -> Type uData
  classify : (input : Strategy.ProblemInput P) ->
    Sigma (Payload input)
  metadata : Documentation := {}
  components : List Documentation := []
  terminalMetadata : Fin arity -> Documentation := fun _ => {}

/-- Registered domain-neutral well-founded order used by the sealed
minimal-counterexample selector.  Core obtains branch state from the
`ProblemDefinition`; applications cannot provide selection or routing code. -/
structure MinimalCounterexampleSelectionData
    (P : Core.Problem.{uAmbient, uBranch}) where
  Measure : Type uData
  progress : Core.Progress.{uAmbient, uBranch, uData} P
  metadata : Documentation := {}
  components : List Documentation := []
  terminalMetadata : Documentation := {}

namespace MinimalCounterexampleSelectionData

/-- Register an existing progress profile without restating its dependent
measure type.  The measure is inferred from the profile and is never a DAG
parameter or an execution value. -/
def ofProgress
    (progress : Core.Progress.{uAmbient, uBranch, uData} P)
    (metadata : Documentation := {})
    (components : List Documentation := [])
    (terminalMetadata : Documentation := {}) :
    MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P where
  Measure := progress.Measure
  progress
  metadata
  components
  terminalMetadata

end MinimalCounterexampleSelectionData

/-- Registration of Core's existing minimal-counterexample selector as an
ordinary sealed localization strategy.  It contains no output carrier,
callback, classifier, route, or residual constructor: Core derives the exact
selected context itself. -/
structure CounterexampleLocalizationData
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) where
  selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P
  metadata : Documentation := {}
  components : List Documentation := []
  terminalMetadata : Documentation := {}

/-- Framework-owned semantic capabilities for the standard structural
continuation of a selected minimal counterexample.

The record contains only domain semantics.  It cannot execute a strategy,
choose a terminal, mutate a ledger, or route a branch.  Core consumes these
laws to build the three sealed strategies `targetAlgebraReduction`,
`minimalSubobjectExclusion`, and `criticalModificationStructure` on the
literal selected ledger stage. -/
structure CounterexampleReductionData
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) where
  selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P
  Code : P.Ambient → Type uAmbient
  Accepts : (object : P.Ambient) → Code object → Prop
  target_iff_code : ∀ object,
    T.Predicate object ↔ ∃ code, Accepts object code
  acceptsDecidable : ∀ object code, Decidable (Accepts object code)
  Subobject : P.Ambient → Type uAmbient
  subobjectProfile :
    Minimality.SubobjectMinimalityProfile
      (P := P) T.Predicate selection.progress Subobject
  Atomic : P.Ambient → Type uAmbient
  Carrier : P.Ambient → Type uAmbient
  Related : (object : P.Ambient) → Carrier object → Carrier object → Prop
  Critical : (object : P.Ambient) → Atomic object → Prop
  atomicSubobject : ∀ {object}, Atomic object → Subobject object
  baseline_of_not_critical :
    ∀ {object} (_baseline : P.Baseline object) (atomic : Atomic object),
      ¬ Critical object atomic →
        P.Baseline (subobjectProfile.toAmbient (atomicSubobject atomic))
  atomic_of_related :
    ∀ {object} (left right : Carrier object),
      Related object left right → Atomic object
  noncritical_of_related :
    ∀ {object} (left right : Carrier object)
      (related : Related object left right),
        ¬ Critical object (atomic_of_related left right related)
  metadata : Documentation := {}
  targetAlgebraMetadata : Documentation := {}
  minimalSubobjectMetadata : Documentation := {}
  criticalModificationMetadata : Documentation := {}
  interfaceReplacement :
    Strategy.InterfaceReplacement.Profile.{
      uAmbient, uBranch, uData, uAmbient, uAmbient, uAmbient, uAmbient,
      uAmbient}
      (P := P) (T := T) selection.progress
  interfaceReplacementClosureMetadata : Documentation := {}

/-- One support-normalization registration together with the packing producer
whose residual ledger it consumes.  The familiar `fst`/`snd` projections are
kept so existing compiler code continues to use the ordinary dependent-pair
interface. -/
structure SupportNormalizationEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object))) where
  fst : Fin packings.length
  snd : Strategy.SupportComplementNormalization.Registration.{
    max uAmbient uBranch,
    max uAmbient uBranch uData, max uAmbient uBranch uData,
    max uAmbient uBranch uData, max uAmbient uBranch uData}
    (Strategy.ProblemInput P) (fun input => T.Predicate input.object)
    packings[fst]

/-- One boundary-accounting registration indexed by the exact normalized
support ledger it reads. -/
structure BoundaryAccountingEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings)) where
  fst : Fin supports.length
  snd : Strategy.BoundaryDemandAccounting.Registration.{
    max uAmbient uBranch, uData, uData, uData, uData}
    (Strategy.ProblemInput P)

/-- One local-supply registration indexed by its boundary predecessor.  Its
ambient member carrier is definitionally the carrier of that predecessor's
normalized-support ledger. -/
structure LocalSupplyEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports)) where
  fst : Fin boundaries.length
  snd : Strategy.LocalSupplyLowerBound.Registration.{
    max uAmbient uBranch, max uAmbient uBranch uData, uData, uData}
    (Strategy.ProblemInput P) supports[boundaries[fst].fst].snd.AmbientItem

namespace LocalSupplyEntry

/-- The exact normalized-support producer inherited through a local-supply
entry's boundary predecessor. -/
def supportIndex
    (entry : LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries) : Fin supports.length :=
  boundaries[entry.fst].fst

/-- The concrete ambient carrier read by a local-supply entry. -/
abbrev AmbientItem
    (entry : LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries) : Strategy.ProblemInput P →
        Type (max uAmbient uBranch uData) :=
  supports[entry.supportIndex].snd.AmbientItem

end LocalSupplyEntry

/-- One finite-state-capacity registration indexed by its exact local-supply
predecessor.  Its ambient item carrier is definitionally the carrier of that
predecessor's normalized-support ledger, so `def:remainder-entropy`'s vertex
set `V(R)` reaches the registration as the inherited complement instead of as a
`Nat`.  `fst` is the `Fin localSupplyLowerBounds.length` that makes
`CapabilityStore.localSupplyExact` callable at this branch. -/
structure FiniteStateCapacityEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports))
    (supplies : List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries)) where
  fst : Fin supplies.length
  snd : Strategy.FiniteStateCapacity.Registration.{
    max uAmbient uBranch, max uAmbient uBranch uData,
    max uAmbient uBranch uData}
    (Strategy.ProblemInput P) supplies[fst].AmbientItem

/-- One route-8 carrier-closure registration indexed by its exact local-supply
predecessor, in the shape `FiniteStateCapacityEntry` already uses.  Its indexed
entries are definitionally the items of that predecessor's normalized-support
ledger, so `def:typeA-route8-carriers`' support and `def+` reach the
registration as the inherited carrier instead of being recomputed.

`fst` links the two **by type only**.  Unlike `FiniteStateCapacityEntry`, this
Strategy's `Profile` reads nothing but `Query.residual`, so it registers no
capability requirement: declaring one it never consumes would make every sibling
containing this vertex fail `StructuralRouteCandidate.capabilityCompatible` and
silently strip the branch of its routing destinations. -/
structure Route8CarrierClosureEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports))
    (supplies : List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries)) where
  fst : Fin supplies.length
  snd : Strategy.Route8CarrierClosure.Registration.{
    max uAmbient uBranch, max uAmbient uBranch uData, uData}
    (Strategy.ProblemInput P) supplies[fst].AmbientItem

/-- Inner dependent payload for one target-relative rank registration. -/
structure TargetRankPayload
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports))
    (supplies : List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries))
    (Coordinate : Strategy.ProblemInput P → Type uData) where
  fst : Fin supplies.length
  snd : Strategy.TargetRelativeRankDichotomy.Registration.{
    max uAmbient uBranch, max uAmbient uBranch uData, uData, uData,
    uData, uData, uData}
    (Strategy.ProblemInput P) supplies[fst].AmbientItem Coordinate

/-- One target-relative rank registration, retaining its coordinate carrier
and its exact local-supply predecessor. -/
structure TargetRankEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports))
    (supplies : List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries)) where
  fst : Strategy.ProblemInput P → Type uData
  snd : TargetRankPayload.{uAmbient, uBranch, uData}
    P T packings supports boundaries supplies fst

/-- Target-relative rank registration linked by type to one exact
minimal-counterexample/interface-replacement producer.  `SiteRelation` is
inert domain semantics derived from the retained coordinate.  The dependent
predicate is fixed below to the ordinary Core compression-candidate carrier;
there is no application closure callback or equality bridge. -/
structure CompressionLinkedTargetRankPayload
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports))
    (supplies : List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries))
    (reduction : CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    (Coordinate : Strategy.ProblemInput P → Type uData) where
  fst : Fin supplies.length
  SiteRelation : (input : Strategy.ProblemInput P) →
    Coordinate input →
      reduction.interfaceReplacement.assembly.Site input.object → Prop
  base : Strategy.TargetRelativeRankDichotomy.BaseRegistration.{
    max uAmbient uBranch, max uAmbient uBranch uData, uData, uData,
    uData, uData, uData}
    (Strategy.ProblemInput P) supplies[fst].AmbientItem Coordinate
  fixed : Strategy.TargetRelativeRankDichotomy.FixedRegistration.{
    max uAmbient uBranch, max uAmbient uBranch uData, uData, uData,
    uData, uData, uData} base
    (fun input _response coordinate =>
      Nonempty (Σ site : {site :
          reduction.interfaceReplacement.assembly.Site input.object //
            SiteRelation input coordinate site},
        reduction.interfaceReplacement.CompressionCandidate
          input.object site.1))

/-- Existential coordinate carrier and exact reduction producer for a linked
rank registration. -/
structure CompressionLinkedTargetRankEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (supports : List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T packings))
    (boundaries : List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T packings supports))
    (supplies : List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T packings supports boundaries))
    (reductions : List
      (CounterexampleReductionData.{uAmbient, uBranch, uData} P T)) where
  reductionIndex : Fin reductions.length
  fst : Strategy.ProblemInput P → Type uData
  snd : CompressionLinkedTargetRankPayload.{uAmbient, uBranch, uData}
    P T packings supports boundaries supplies reductions[reductionIndex] fst

/-- One finite bottleneck registration indexed by the exact coupled-pressure
producer whose selected overload ledger it consumes. -/
structure FiniteBottleneckEntry
    (P : Core.Problem.{uAmbient, uBranch})
    (pressures : List
      (Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData} (Strategy.ProblemInput P))) where
  fst : Fin pressures.length
  snd : Strategy.FiniteBottleneckClassification.Registration.{
    max uAmbient uBranch, uData, uData, uData, uData, uData, uData, uData,
    uData} (Strategy.ProblemInput P)

/-- One homogeneous-bottleneck registration indexed by the exact finite
bottleneck producer chain it consumes.  The coupled-pressure producer is
recovered through `bottlenecks[fst].fst`; no application repeats that index. -/
structure HomogeneousBottleneckEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (pressures : List
      (Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData} (Strategy.ProblemInput P)))
    (bottlenecks : List
      (FiniteBottleneckEntry.{uAmbient, uBranch, uData} P pressures)) where
  fst : Fin bottlenecks.length
  snd : Strategy.HomogeneousBottleneck.Registration.{
    max uAmbient uBranch, uData}
    (Strategy.ProblemInput P) (fun input => T.Predicate input.object)

namespace HomogeneousBottleneckEntry

def pressureIndex
    (entry : HomogeneousBottleneckEntry.{uAmbient, uBranch, uData}
      P T pressures bottlenecks) : Fin pressures.length :=
  bottlenecks[entry.fst].fst

/-- Exact carrier of the selected same-token family inherited from the
coupled-pressure producer.  It is definitionally the producer's item carrier,
so downstream consumers require no equality cast or application bridge. -/
abbrev HandoffSupport
    (entry : HomogeneousBottleneckEntry.{uAmbient, uBranch, uData}
      P T pressures bottlenecks) : Strategy.ProblemInput P → Type uData :=
  pressures[entry.pressureIndex].Item

end HomogeneousBottleneckEntry

/-- One cold continuation indexed by both its exact packing producer and the
homogeneous handoff whose selected item family it consumes. -/
structure ColdBranchAggregationEntry
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (reductions : List
      (CounterexampleReductionData.{uAmbient, uBranch, uData} P T))
    (packings : List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)))
    (pressures : List
      (Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData} (Strategy.ProblemInput P)))
    (bottlenecks : List
      (FiniteBottleneckEntry.{uAmbient, uBranch, uData} P pressures))
    (homogeneous : List
      (HomogeneousBottleneckEntry.{uAmbient, uBranch, uData} P T
        pressures bottlenecks)) where
  reductionIndex : Fin reductions.length
  fst : Fin packings.length
  handoffIndex : Fin homogeneous.length
  /-- Whether the homogeneous handoff ledger is a *precondition* of this cold
  continuation, or merely an input it consults when live.

  `.homogeneousHandoff` is branch-local: Core publishes it only on the
  structured output of a homogeneous bottleneck.  A cold continuation placed on
  the shared near-cubic spine is reached from three directions -- the
  structured Type B route, the bounded fixed-cap route, and the plain
  at-or-below surplus case -- and only the first carries the handoff.  Leaving
  this `true` pins the continuation to the structured branch; setting it
  `false` lets the continuation sit on the spine and read an empty handoff
  schedule on the routes where no handoff exists. -/
  handoffRequired : Bool := true
  snd : Strategy.ColdBranchAggregation.LedgerRegistration.{
    max uAmbient uBranch uData, max uAmbient uBranch uData,
    uData, uData, uData, uData, uData,
    uAmbient, uBranch, uData, uAmbient, uAmbient, uAmbient, uAmbient,
    uAmbient}
    P T reductions[reductionIndex].selection.progress
    reductions[reductionIndex].interfaceReplacement
    packings[fst] homogeneous[handoffIndex].HandoffSupport

/-- Everything the private strategy compiler may consume.  Each field is a
named finite list of registered families, so a blueprint can reference the
n-th registered scan, dichotomy, ... by index.  `targetDecidable` powers
runner-owned early stopping and the `targetOrAvoid` key. -/
structure StrategyData (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P) where
  targetDecidable : (input : Strategy.ProblemInput P) ->
    Decidable (T.Predicate input.object)
  scans : List (ScanData.{uAmbient, uBranch, uData} P) := []
  responses : List (ResponseData.{uAmbient, uBranch, uData} P) := []
  capacities : List (CapacityData.{uAmbient, uBranch, uData} P) := []
  localizations : List (LocalizationData.{uAmbient, uBranch, uData} P) := []
  rankBudgets : List (RankBudgetData P) := []
  closedCodes : List (ClosedCodeData.{uAmbient, uBranch, uData} P) := []
  dichotomies : List (DichotomyData.{uAmbient, uBranch, uData} P T) := []
  atomContextObstructionDichotomies :
    List (AtomContextObstructionDichotomyData.{
      uAmbient, uBranch, uData} P) := []
  terminalFamilies :
    List (FiniteTerminalFamilyData.{uAmbient, uBranch, uData} P T) := []
  obstructionPackingClosures :
    List (Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, max uAmbient uBranch uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object)) := []
  exactFiniteLocalAlgebras :
    List (Strategy.ExactFiniteLocalAlgebra.Registration.{
      max uAmbient uBranch, uData, uData, uData}
      (Strategy.ProblemInput P)) := []
  finiteBarrierEnumerations :
    List (Strategy.FiniteBarrierEnumeration.Registration.{
      max uAmbient uBranch, uData} (Strategy.ProblemInput P)) := []
  finiteDensityBudgets :
    List (Strategy.FiniteDensityBudget.Registration.{
      max uAmbient uBranch} (Strategy.ProblemInput P)) := []
  /-- `uData` is the dedicated data universe: a registration is residual-owned
  and its carriers are projected off the object, so they are independent of how
  large the ambient happens to be.  Writing the data universe as
  `max uAmbient uBranch uData` re-couples them and forces every registration's
  data to be at least as large as the ambient, which is an artifact of the
  signature rather than of the mathematics.  This family follows
  `homogeneousBottlenecks` and keeps the data carriers at `uData`. -/
  finiteScheduleCapacities :
    List (Strategy.FiniteScheduleCapacity.Registration.{
      max uAmbient uBranch, uData}
      (Strategy.ProblemInput P)) := []
  scaleThresholdDichotomies :
    List (Strategy.ScaleThresholdDichotomy.Registration
      (Strategy.ProblemInput P)) := []
  orderedSurplusActivations :
    List (Strategy.OrderedSurplusActivation.Registration.{
      max uAmbient uBranch, uData, uData, uData, uData, uData}
      (Strategy.ProblemInput P)) := []
  baselineDemandAccountings :
    List (Strategy.BaselineDemandAccounting.Registration.{
      max uAmbient uBranch, uData, uData, uData}
      (Strategy.ProblemInput P)) := []
  canonicalPairResponseAccountings :
    List (Strategy.CanonicalPairResponseAccounting.Registration.{
      max uAmbient uBranch, uData, uData}
      (Strategy.ProblemInput P)) := []
  canonicalCapacityTokenAccountings :
    List (Strategy.CanonicalCapacityTokenAccounting.Registration.{
      max uAmbient uBranch, uData, uData, uData, uData, uData}
      (Strategy.ProblemInput P)) := []
  coupledHomogeneousFibrePressures :
    List (Strategy.CoupledHomogeneousFibrePressure.Registration.{
      max uAmbient uBranch, uData, uData, uData, uData, uData, uData, uData,
      uData, uData}
      (Strategy.ProblemInput P)) := []
  finiteBottleneckClassifications :
    List (FiniteBottleneckEntry.{uAmbient, uBranch, uData} P
      coupledHomogeneousFibrePressures) := []
  homogeneousBottlenecks :
    List (HomogeneousBottleneckEntry.{uAmbient, uBranch, uData} P T
      coupledHomogeneousFibrePressures finiteBottleneckClassifications) := []
  supportComplementNormalizations :
    List (SupportNormalizationEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures) := []
  boundaryDemandAccountings :
    List (BoundaryAccountingEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures supportComplementNormalizations) := []
  localSupplyLowerBounds :
    List (LocalSupplyEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures supportComplementNormalizations
        boundaryDemandAccountings) := []
  /-- Defect closed.  An entry now carries the index of the local-supply
  producer it reads, mirroring `targetRelativeRankDichotomies`' shape, so
  `entry.fst` is the `Fin localSupplyLowerBounds.length` that makes
  `CapabilityStore.localSupplyExact` callable at the finite-state-capacity
  branch.  The exact carriers the local-supply capability bundles -- in
  particular the normalized support complement, i.e. the vertex set
  `def:remainder-entropy`'s `\mathcal G(R)` is indexed by -- therefore reach
  this registration, and the realized-state family is stated on the inherited
  `V(R)` rather than on a `Nat` surrogate. -/
  finiteStateCapacities :
    List (FiniteStateCapacityEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures supportComplementNormalizations
        boundaryDemandAccountings localSupplyLowerBounds) := []
  targetRelativeRankDichotomies :
    List (TargetRankEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures supportComplementNormalizations
        boundaryDemandAccountings localSupplyLowerBounds) := []
  minimalCounterexamples :
    List (MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P) := []
  counterexampleLocalizations :
    List (CounterexampleLocalizationData.{uAmbient, uBranch, uData} P T) := []
  counterexampleReductions :
    List (CounterexampleReductionData.{uAmbient, uBranch, uData} P T) := []
  compressionLinkedTargetRelativeRankDichotomies :
    List (CompressionLinkedTargetRankEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures supportComplementNormalizations
        boundaryDemandAccountings localSupplyLowerBounds
        counterexampleReductions) := []
  coldBranchAggregations :
    List (ColdBranchAggregationEntry.{uAmbient, uBranch, uData} P T
      counterexampleReductions obstructionPackingClosures
      coupledHomogeneousFibrePressures
      finiteBottleneckClassifications homogeneousBottlenecks) := []
  finiteStateNetChargeContinuation :
    Strategy.FiniteStateNetChargeContinuation.Registration
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object) := {}
  /-- Manuscript nodes `[111]`--`[124]`: the route-8 carrier closure, the
  CT5 -> CT14 -> CT12 composition that terminates exit `(8)`.  Appended last so
  that no dependently-indexed family above it is renumbered. -/
  route8CarrierClosures :
    List (Route8CarrierClosureEntry.{uAmbient, uBranch, uData}
      P T obstructionPackingClosures supportComplementNormalizations
        boundaryDemandAccountings localSupplyLowerBounds) := []

/-- Complete theorem registration consumed by the strategy DAG runner.  The
application exposes one value containing its ambient problem, target, and
registered mathematical data; execution concerns are deliberately absent. -/
structure ProblemDefinition where
  problem : Problem.{uAmbient, uBranch}
  target : Target problem
  initialState : forall object, problem.BranchState object
  data : StrategyData.{uAmbient, uBranch, uData} problem target
  metadata : ProblemMetadata := {}

end Hypostructure.Core
