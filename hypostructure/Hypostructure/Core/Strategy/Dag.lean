import Hypostructure.Core.Strategy
import Hypostructure.Core.Strategy.CounterexampleReduction
import Hypostructure.Core.Strategy.InterfaceReplacement
import Hypostructure.Core.Strategy.ObstructionPackingClosure
import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra
import Hypostructure.Core.Strategy.FiniteBarrierEnumeration
import Hypostructure.Core.Strategy.FiniteDensityBudget
import Hypostructure.Core.Strategy.FiniteStateCapacity
import Hypostructure.Core.Strategy.FiniteScheduleCapacity
import Hypostructure.Core.Strategy.Route8CarrierClosure
import Hypostructure.Core.Strategy.ScaleThresholdDichotomy
import Hypostructure.Core.Strategy.AtomContextObstructionDichotomy
import Hypostructure.Core.Strategy.OrderedSurplusActivation
import Hypostructure.Core.Strategy.BaselineDemandAccounting
import Hypostructure.Core.Strategy.CanonicalPairResponseAccounting
import Hypostructure.Core.Strategy.CanonicalCapacityTokenAccounting
import Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure
import Hypostructure.Core.Strategy.FiniteBottleneckClassification
import Hypostructure.Core.Strategy.HomogeneousBottleneck
import Hypostructure.Core.Strategy.SupportComplementNormalization
import Hypostructure.Core.Strategy.BoundaryDemandAccounting
import Hypostructure.Core.Strategy.LocalSupplyLowerBound
import Hypostructure.Core.Strategy.TargetRelativeRankDichotomy
import Hypostructure.Core.Strategy.Validate
import Hypostructure.Core.Residual.ExactLedger
import Hypostructure.Core.Context
import Hypostructure.Core.Residual.Stage

/-!
# Declarative strategy DAGs

The application boundary is exactly two inputs: one `Core.ProblemDefinition`
(problem, target, initial state, registered strategy data) and one key-only
`Blueprint`.  Everything else — capability resolution, contracts, stages,
dependent composition, branch routing, joins, early target closure,
finalization, and work accounting — is derived privately by the compiler in
this file from the registered problem, the literal previous residual, and the
accumulated ledger.

The frontend is strict: the sole entrypoint is the sealed `ofDag%`
elaborator, which validates the declaration before the compiler is ever
invoked.  Banal targets (hardcoded `True`/`False`, object-independent
predicates, `False` baselines), blueprints naming unregistered strategies,
and problems that cannot certify their target are rejected at elaboration
time with an explanation of what is not allowed and how to fix it.  The
compiler is total by proof — every registered-family access is indexed by
the compliance obligation — so no code path exists that could execute an
unregistered vertex or produce a conditional outcome.

`Report.statement` is the kernel-checked registered theorem; kernel trust is
validated externally with `#print axioms` on the exported projections.
-/

namespace Hypostructure.Core.Strategy.Dag

open Hypostructure.Core.Residual

universe uAmbient uBranch uData uStage uTerminal uPayload uResult

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
variable {data : StrategyData.{uAmbient, uBranch, uData} P T}

/-! ## Closed strategy references -/

/-- Official strategy keys.  A numeric index selects the n-th registered
family of the corresponding kind in the problem's `StrategyData`.  Indices
are proof architecture (which registered family runs at this vertex), not
execution values. -/
inductive StrategyKey where
  | orderedWitnessScan (index : Nat := 0)
  | responseClassifier (index : Nat := 0)
  | capacityLedger (index : Nat := 0)
  | supportLocalization (index : Nat := 0)
  | rankBudget (index : Nat := 0)
  | closedCode (index : Nat := 0)
  | dichotomy (index : Nat := 0)
  | obstructionPackingClosure (index : Nat := 0)
  | exactFiniteLocalAlgebra (index : Nat := 0)
  | finiteBarrierEnumeration (index : Nat := 0)
  | finiteDensityBudget (index : Nat := 0)
  | finiteStateCapacity (index : Nat := 0)
  | finiteScheduleCapacity (index : Nat := 0)
  | route8CarrierClosure (index : Nat := 0)
  | scaleThresholdDichotomy (index : Nat := 0)
  | atomContextObstructionDichotomy (index : Nat := 0)
  | orderedSurplusActivation (index : Nat := 0)
  | baselineDemandAccounting (index : Nat := 0)
  | canonicalPairResponseAccounting (index : Nat := 0)
  | canonicalCapacityTokenAccounting (index : Nat := 0)
  | coupledHomogeneousFibrePressure (index : Nat := 0)
  | finiteBottleneckClassification (index : Nat := 0)
  | homogeneousBottleneck (index : Nat := 0)
  | supportComplementNormalization (index : Nat := 0)
  | boundaryDemandAccounting (index : Nat := 0)
  | localSupplyLowerBound (index : Nat := 0)
  | targetRelativeRankDichotomy (index : Nat := 0)
  | compressionLinkedTargetRelativeRankDichotomy (index : Nat := 0)
  | counterexampleLocalization (index : Nat := 0)
  | minimalCounterexampleSelection (index : Nat := 0)
  | targetAlgebraReduction (index : Nat := 0)
  | minimalSubobjectExclusion (index : Nat := 0)
  | criticalModificationStructure (index : Nat := 0)
  | interfaceReplacementClosure (index : Nat := 0)
  | coldBranchAggregation (index : Nat := 0)
  | finiteStateNetChargeContinuation
  | targetOrAvoid
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- The key names an existing executable family in the framework-owned
problem presentation.  This proposition is used only inside the sealed
reference constructor below; proof authors never supply it. -/
def StrategyKey.ResolvedIn
    (data : StrategyData.{uAmbient, uBranch, uData} P T) :
    StrategyKey -> Prop
  | .orderedWitnessScan index => index < data.scans.length
  | .responseClassifier index => index < data.responses.length
  | .capacityLedger index => index < data.capacities.length
  | .supportLocalization index => index < data.localizations.length
  | .rankBudget index => index < data.rankBudgets.length
  | .closedCode index => index < data.closedCodes.length
  | .dichotomy index => index < data.dichotomies.length
  | .obstructionPackingClosure index =>
      index < data.obstructionPackingClosures.length
  | .exactFiniteLocalAlgebra index =>
      index < data.exactFiniteLocalAlgebras.length
  | .finiteBarrierEnumeration index =>
      index < data.finiteBarrierEnumerations.length
  | .finiteDensityBudget index =>
      index < data.finiteDensityBudgets.length
  | .finiteStateCapacity index =>
      index < data.finiteStateCapacities.length
  | .finiteScheduleCapacity index =>
      index < data.finiteScheduleCapacities.length
  | .route8CarrierClosure index =>
      index < data.route8CarrierClosures.length
  | .scaleThresholdDichotomy index =>
      index < data.scaleThresholdDichotomies.length
  | .atomContextObstructionDichotomy index =>
      index < data.atomContextObstructionDichotomies.length
  | .orderedSurplusActivation index =>
      index < data.orderedSurplusActivations.length
  | .baselineDemandAccounting index =>
      index < data.baselineDemandAccountings.length
  | .canonicalPairResponseAccounting index =>
      index < data.canonicalPairResponseAccountings.length
  | .canonicalCapacityTokenAccounting index =>
      index < data.canonicalCapacityTokenAccountings.length
  | .coupledHomogeneousFibrePressure index =>
      index < data.coupledHomogeneousFibrePressures.length
  | .finiteBottleneckClassification index =>
      index < data.finiteBottleneckClassifications.length
  | .homogeneousBottleneck index =>
      index < data.homogeneousBottlenecks.length
  | .supportComplementNormalization index =>
      index < data.supportComplementNormalizations.length
  | .boundaryDemandAccounting index =>
      index < data.boundaryDemandAccountings.length
  | .localSupplyLowerBound index =>
      index < data.localSupplyLowerBounds.length
  | .targetRelativeRankDichotomy index =>
      index < data.targetRelativeRankDichotomies.length
  | .compressionLinkedTargetRelativeRankDichotomy index =>
      index < data.compressionLinkedTargetRelativeRankDichotomies.length
  | .counterexampleLocalization index =>
      index < data.counterexampleLocalizations.length
  | .minimalCounterexampleSelection index =>
      index < data.counterexampleReductions.length
  | .targetAlgebraReduction _index
  | .minimalSubobjectExclusion _index
  | .criticalModificationStructure _index
  | .interfaceReplacementClosure _index => False
  | .coldBranchAggregation index =>
      index < data.coldBranchAggregations.length
  | .finiteStateNetChargeContinuation => True
  | .targetOrAvoid => True

/-- An existing scalar Strategy.  Its constructor and resolution witness are
private, so a proof author cannot manufacture a key, slot, executor, or
availability claim.  Public fluent DAG operations below are the only source
of these references. -/
structure StrategyRef
    (data : StrategyData.{uAmbient, uBranch, uData} P T) where
  private mk ::
  private key : StrategyKey
  private resolved : key.ResolvedIn data

/-- Read-only identity used by reports and artifact renderers.  It exposes no
constructor, resolution witness, callback, or execution authority. -/
def StrategyRef.keyView (strategy : StrategyRef data) : StrategyKey :=
  strategy.key

/-- One sealed two-terminal Strategy reference.  Blueprint branching depends
only on this common arity boundary, never on a Strategy-specific constructor. -/
structure BinaryStrategyRef
    (data : StrategyData.{uAmbient, uBranch, uData} P T) where
  private mk ::
  private terminal :
    Sum (Fin data.dichotomies.length)
      (Sum (Fin data.scaleThresholdDichotomies.length)
        (Sum (Fin data.atomContextObstructionDichotomies.length)
          (Sum (Fin data.targetRelativeRankDichotomies.length)
              (Sum (Fin data.finiteDensityBudgets.length)
                (Sum (Fin data.finiteStateCapacities.length)
                  (Sum (Fin data.finiteScheduleCapacities.length)
                    (Sum
                      (Fin data.compressionLinkedTargetRelativeRankDichotomies.length)
                      (Sum (Fin data.route8CarrierClosures.length) PUnit))))))))

private def BinaryStrategyRef.key (strategy : BinaryStrategyRef data) :
    StrategyKey :=
  match strategy.terminal with
  | .inl index => .dichotomy index
  | .inr (.inl index) => .scaleThresholdDichotomy index
  | .inr (.inr (.inl index)) => .atomContextObstructionDichotomy index
  | .inr (.inr (.inr (.inl index))) => .targetRelativeRankDichotomy index
  | .inr (.inr (.inr (.inr (.inl index)))) => .finiteDensityBudget index
  | .inr (.inr (.inr (.inr (.inr (.inl index))))) =>
      .finiteStateCapacity index
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl index)))))) =>
      .finiteScheduleCapacity index
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index))))))) =>
      .compressionLinkedTargetRelativeRankDichotomy index
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index)))))))) =>
      .route8CarrierClosure index
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))))) =>
      .finiteStateNetChargeContinuation

private def BinaryStrategyRef.resolved
    (strategy : BinaryStrategyRef data) :
    strategy.key.ResolvedIn data := by
  rcases strategy with ⟨terminal⟩
  rcases terminal with index | terminal
  · exact index.isLt
  · rcases terminal with index | terminal
    · exact index.isLt
    · rcases terminal with index | terminal
      · exact index.isLt
      · rcases terminal with index | terminal
        · exact index.isLt
        · rcases terminal with index | terminal
          · exact index.isLt
          · rcases terminal with index | terminal
            · exact index.isLt
            · rcases terminal with index | terminal
              · exact index.isLt
              · rcases terminal with index | terminal
                · exact index.isLt
                · rcases terminal with index | _
                  · exact index.isLt
                  · trivial

def BinaryStrategyRef.keyView (strategy : BinaryStrategyRef data) :
    StrategyKey :=
  strategy.key

private def BinaryStrategyRef.view (strategy : BinaryStrategyRef data) :
  Sum (Fin data.dichotomies.length)
      (Sum (Fin data.scaleThresholdDichotomies.length)
        (Sum (Fin data.atomContextObstructionDichotomies.length)
          (Sum (Fin data.targetRelativeRankDichotomies.length)
            (Sum (Fin data.finiteDensityBudgets.length)
                (Sum (Fin data.finiteStateCapacities.length)
                (Sum (Fin data.finiteScheduleCapacities.length)
                  (Sum
                    (Fin data.compressionLinkedTargetRelativeRankDichotomies.length)
                    (Sum (Fin data.route8CarrierClosures.length) PUnit)))))))) :=
  strategy.terminal

private def BinaryStrategyRef.finiteDensityBudget
    (index : Fin data.finiteDensityBudgets.length) :
    BinaryStrategyRef data :=
  ⟨.inr (.inr (.inr (.inr (.inl index))))⟩

private def BinaryStrategyRef.finiteStateCapacity
    (index : Fin data.finiteStateCapacities.length) :
  BinaryStrategyRef data :=
  ⟨.inr (.inr (.inr (.inr (.inr (.inl index)))))⟩

private def BinaryStrategyRef.finiteScheduleCapacity
    (index : Fin data.finiteScheduleCapacities.length) :
  BinaryStrategyRef data :=
  ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl index))))))⟩

private def BinaryStrategyRef.finiteStateNetChargeContinuation :
    BinaryStrategyRef data :=
  ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .unit))))))))⟩

private def BinaryStrategyRef.route8CarrierClosure
    (index : Fin data.route8CarrierClosures.length) :
    BinaryStrategyRef data :=
  ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index))))))))⟩

private def BinaryStrategyRef.compressionLinkedTargetRelativeRankDichotomy
    (index : Fin
      data.compressionLinkedTargetRelativeRankDichotomies.length) :
    BinaryStrategyRef data :=
  ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index)))))))⟩

/-- The first element of a framework-owned nonempty strategy family. -/
private def firstFamilyIndex (length : Nat) [NeZero length] : Fin length :=
  ⟨0, Nat.pos_of_neZero length⟩

/-- Whether a DAG is still in the public authoring language or has already
been semantically routed by Core.  The compiler accepts only `expanded`.
Applications can place a targetless `route` marker, but only Core can produce
the corresponding `resolvedRoute` carrying a destination and bridge
provenance. -/
inductive RouteMode where
  | authoring
  | expanded
  deriving DecidableEq, Repr, Inhabited

/-- Display-only metadata for one strategy vertex.  Empty strings mean that
the author supplied no custom value; renderers then fall back to the official
strategy-key display name.  These fields never participate in compilation,
compliance, residuals, or work accounting. -/
structure DisplayMetadata where
  name : String := ""
  note : String := ""
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- Display-only metadata for one output edge of an exhaustive dichotomy. -/
structure OutputMetadata where
  name : String := ""
  note : String := ""
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- All authored documentation attached to one blueprint vertex.  `left` and
`right` are consulted only when the vertex is a dichotomy. -/
structure VertexMetadata where
  display : DisplayMetadata := {}
  left : OutputMetadata := {}
  right : OutputMetadata := {}
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- Display-only documentation for a semantic route edge.  None of these
fields participates in destination selection or bridge construction. -/
structure RouteMetadata where
  name : String := ""
  note : String := ""
  tags : List String := []
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- Whether Core selected an ordinary enclosing continuation or the entry of
an enclosing branch family's sibling continuation.  Applications never
construct this value: it is retained only for execution and reporting. -/
inductive RouteScope where
  | enclosing
  | sibling
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Core-owned resolution of one targetless autoroute marker.  The source and
destination are stable structural vertex IDs.  Candidate discovery is
structural; manifest verification subsequently checks that the selected
continuation can be instantiated from the literal source ledger. -/
structure ResolvedRoute where
  private mk ::
  sourceId : Nat
  destinationId : Nat
  sourceDepth : Nat
  destinationDepth : Nat
  scope : RouteScope
  candidateIds : List Nat
  candidateDepths : List Nat
  destinationWork : Nat
  deriving DecidableEq, Repr, Lean.ToExpr

/-- The selection law is framework policy, not route data. -/
def ResolvedRoute.selectedBy (_route : ResolvedRoute) : String :=
  "deepest_most_restrictive"

/-- The current bridge transports the literal residual; applications cannot
replace this with an asserted equivalence. -/
def ResolvedRoute.relation (_route : ResolvedRoute) : String :=
  "literal_residual"

/-- A semantic bridge contributes one framework-owned ledger operation. -/
def ResolvedRoute.work (_route : ResolvedRoute) : Nat :=
  1

def ResolvedRoute.compatibleCandidates (route : ResolvedRoute) : List Nat :=
  route.destinationId :: route.candidateIds

def ResolvedRoute.compatibleCandidateDepths (route : ResolvedRoute) : List Nat :=
  route.destinationDepth :: route.candidateDepths

def ResolvedRoute.scopeName (route : ResolvedRoute) : String :=
  match route.scope with
  | .enclosing => "enclosing"
  | .sibling => "sibling"

def ResolvedRoute.routesToSibling (route : ResolvedRoute) : Bool :=
  match route.scope with
  | .enclosing => false
  | .sibling => true

namespace VertexMetadata

def isEmpty (metadata : VertexMetadata) : Bool :=
  metadata.display.name.isEmpty && metadata.display.note.isEmpty &&
    metadata.left.name.isEmpty && metadata.left.note.isEmpty &&
    metadata.right.name.isEmpty && metadata.right.note.isEmpty

/-- Prefer explicit fields from `primary`, filling only empty fields from
`fallback`. -/
def merge (primary fallback : VertexMetadata) : VertexMetadata where
  display.name :=
    if primary.display.name.isEmpty then fallback.display.name
    else primary.display.name
  display.note :=
    if primary.display.note.isEmpty then fallback.display.note
    else primary.display.note
  left.name := if primary.left.name.isEmpty then fallback.left.name else primary.left.name
  left.note := if primary.left.note.isEmpty then fallback.left.note else primary.left.note
  right.name :=
    if primary.right.name.isEmpty then fallback.right.name else primary.right.name
  right.note :=
    if primary.right.note.isEmpty then fallback.right.note else primary.right.note

end VertexMetadata

/-! ## Framework-owned minimal-counterexample continuation payload -/

/-- Complete metadata for the three sealed dependent Strategies following
minimal-counterexample selection.  Its constructor is private; the public
flat fluent builders below are its only source. -/
structure CounterexampleContinuationMetadata where
  private mk ::
  targetMetadata : VertexMetadata
  minimalMetadata : VertexMetadata
  criticalMetadata : VertexMetadata
  interfaceReplacementClosureMetadata : VertexMetadata

/-- Public declarative DAG over one fixed framework Strategy library.
Every operation stored in the type already carries its intrinsic resolution
witness.  Consequently an unavailable key, raw slot, ad-hoc Strategy, or
post-hoc compliance claim is unrepresentable. -/
inductive Blueprint
    (data : StrategyData.{uAmbient, uBranch, uData} P T) :
    RouteMode -> Type (max uAmbient uBranch uData) where
  | root : Blueprint data mode
  | step (rest : Blueprint data mode)
      (strategy : StrategyRef data) : Blueprint data mode
  /-- Exhaustive dichotomy with branch-local continuations.  Core
  classifies, routes, runs exactly the selected branch, and joins the two
  surviving terminals as a disjoint union. -/
  | binaryBranch (rest : Blueprint data mode)
      (strategy : BinaryStrategyRef data)
      (left right : Blueprint data mode) : Blueprint data mode
  /-- The four existing homogeneous-bottleneck outputs.  Core closes the
  target output and retains independent continuations for the three live
  residual outputs. -/
  | homogeneousBottleneckBranches (rest : Blueprint data mode)
      (index : Fin data.homogeneousBottlenecks.length)
      (exceptional structured bounded : Blueprint data mode) :
      Blueprint data mode
  /-- Target-or-minimal reduction with one open continuation. -/
  | minimalCounterexample (rest : Blueprint data mode)
      (index : Fin data.counterexampleReductions.length)
      (counterexample : CounterexampleContinuationMetadata) :
      Blueprint data mode
  /-- Pure documentation marker: identical compiled semantics to `rest` (no
  work, no key, no compliance obligation of its own) carrying a free-text
  label the renderer surfaces next to the vertex it precedes — e.g. to record
  manuscript correspondence. Shared forward transport is represented only by
  targetless `autoroute`; annotation text is never interpreted as routing. -/
  | annotate (rest : Blueprint data mode) (label : String) :
      Blueprint data mode
  /-- Pure documentation marker: identical compiled semantics to `rest`,
  attaching a short custom display name to the vertex immediately
  following it.  Unlike `annotate`'s free-text note (panels and the CLI
  summary only), a label is a prettification of the node's own title and is
  shown everywhere the node itself is shown — the main diagram, the panels,
  and the CLI. -/
  | labelled (rest : Blueprint data mode) (name : String) :
      Blueprint data mode
  /-- First-class display metadata attached to the vertex immediately
  following it.  Like `annotate` and `labelled`, this wrapper is erased by
  every proof-relevant traversal. -/
  | documented (rest : Blueprint data mode)
      (metadata : VertexMetadata) : Blueprint data mode
  /-- Targetless semantic handoff from a branch-local suffix to the deepest
  compatible enclosing or sibling continuation.  Core derives the
  destination and bridge. -/
  | route (rest : Blueprint data .authoring)
      (metadata : RouteMetadata) : Blueprint data .authoring
  /-- Compiler-owned routed handoff.  It survives normalization, contributes
  one bridge ledger extension, and is recorded in the sealed proof trace. -/
  | resolvedRoute (rest : Blueprint data .expanded)
      (route : ResolvedRoute) (metadata : RouteMetadata) :
      Blueprint data .expanded

noncomputable instance : DecidableEq (Blueprint data mode) := Classical.decEq _
instance : Inhabited (Blueprint data mode) := ⟨Blueprint.root⟩
instance : Repr (Blueprint data mode) where
  reprPrec _ _ := "Blueprint"

/-! ## Flat minimal-counterexample strategy builders

The wrappers below carry only framework-owned syntax under private
constructors.  They provide a flat fluent chain while retaining the dependent
continuation required by early target closure: no application can omit,
reorder, or forge one of the three continuation Strategies. -/

structure AfterMinimalCounterexampleSelection
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (mode : RouteMode) where
  private mk ::
  private dag : Blueprint data mode
  private index : Fin data.counterexampleReductions.length
  private selectionMetadata : VertexMetadata

structure AfterTargetAlgebraReduction
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (mode : RouteMode) where
  private mk ::
  private selected : AfterMinimalCounterexampleSelection data mode
  private targetMetadata : VertexMetadata

structure AfterMinimalSubobjectExclusion
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (mode : RouteMode) where
  private mk ::
  private target : AfterTargetAlgebraReduction data mode
  private minimalMetadata : VertexMetadata

structure AfterCriticalModificationStructure
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (mode : RouteMode) where
  private mk ::
  private minimal : AfterMinimalSubobjectExclusion data mode
  private criticalMetadata : VertexMetadata

/-! Fluent public spellings.  Ordinary operations append one sealed strategy
key.  The flat minimal-counterexample builders select the fixed dependent
continuation whose Strategies Core executes against their literal stages. -/

private def Blueprint.withMetadata (dag : Blueprint data mode)
    (metadata : VertexMetadata) : Blueprint data mode :=
  if metadata.isEmpty then dag else .documented dag metadata

def Blueprint.orderedWitnessScan (dag : Blueprint data mode)
    [NeZero data.scans.length]
    (index : Fin data.scans.length := firstFamilyIndex data.scans.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.orderedWitnessScan index, index.isLt⟩

def Blueprint.responseClassifier (dag : Blueprint data mode)
    [NeZero data.responses.length]
    (index : Fin data.responses.length := firstFamilyIndex data.responses.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.responseClassifier index, index.isLt⟩

def Blueprint.capacityLedger (dag : Blueprint data mode)
    [NeZero data.capacities.length]
    (index : Fin data.capacities.length := firstFamilyIndex data.capacities.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.capacityLedger index, index.isLt⟩

def Blueprint.orderedSurplusActivation (dag : Blueprint data mode)
    [NeZero data.orderedSurplusActivations.length]
    (index : Fin data.orderedSurplusActivations.length :=
      firstFamilyIndex data.orderedSurplusActivations.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.orderedSurplusActivation index, index.isLt⟩

def Blueprint.baselineDemandAccounting (dag : Blueprint data mode)
    [NeZero data.baselineDemandAccountings.length]
    (index : Fin data.baselineDemandAccountings.length :=
      firstFamilyIndex data.baselineDemandAccountings.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.baselineDemandAccounting index, index.isLt⟩

def Blueprint.canonicalPairResponseAccounting (dag : Blueprint data mode)
    [NeZero data.canonicalPairResponseAccountings.length]
    (index : Fin data.canonicalPairResponseAccountings.length :=
      firstFamilyIndex data.canonicalPairResponseAccountings.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.canonicalPairResponseAccounting index, index.isLt⟩

def Blueprint.canonicalCapacityTokenAccounting (dag : Blueprint data mode)
    [NeZero data.canonicalCapacityTokenAccountings.length]
    (index : Fin data.canonicalCapacityTokenAccountings.length :=
      firstFamilyIndex data.canonicalCapacityTokenAccountings.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.canonicalCapacityTokenAccounting index, index.isLt⟩

def Blueprint.coupledHomogeneousFibrePressure (dag : Blueprint data mode)
    [NeZero data.coupledHomogeneousFibrePressures.length]
    (index : Fin data.coupledHomogeneousFibrePressures.length :=
      firstFamilyIndex data.coupledHomogeneousFibrePressures.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.coupledHomogeneousFibrePressure index, index.isLt⟩

def Blueprint.finiteBottleneckClassification (dag : Blueprint data mode)
    [NeZero data.finiteBottleneckClassifications.length]
    (index : Fin data.finiteBottleneckClassifications.length :=
      firstFamilyIndex data.finiteBottleneckClassifications.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.finiteBottleneckClassification index, index.isLt⟩

def Blueprint.homogeneousBottleneck (dag : Blueprint data mode)
    [NeZero data.homogeneousBottlenecks.length]
    (index : Fin data.homogeneousBottlenecks.length :=
      firstFamilyIndex data.homogeneousBottlenecks.length)
    (exceptional : Blueprint data mode → Blueprint data mode := id)
    (structured : Blueprint data mode → Blueprint data mode := id)
    (bounded : Blueprint data mode → Blueprint data mode := id)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .homogeneousBottleneckBranches
    (dag.withMetadata { display := { name, note } }) index
    (exceptional .root) (structured .root) (bounded .root)

def Blueprint.supportComplementNormalization (dag : Blueprint data mode)
    [NeZero data.supportComplementNormalizations.length]
    (index : Fin data.supportComplementNormalizations.length :=
      firstFamilyIndex data.supportComplementNormalizations.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.supportComplementNormalization index, index.isLt⟩

def Blueprint.boundaryDemandAccounting (dag : Blueprint data mode)
    [NeZero data.boundaryDemandAccountings.length]
    (index : Fin data.boundaryDemandAccountings.length :=
      firstFamilyIndex data.boundaryDemandAccountings.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.boundaryDemandAccounting index, index.isLt⟩

def Blueprint.localSupplyLowerBound (dag : Blueprint data mode)
    [NeZero data.localSupplyLowerBounds.length]
    (index : Fin data.localSupplyLowerBounds.length :=
      firstFamilyIndex data.localSupplyLowerBounds.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.localSupplyLowerBound index, index.isLt⟩

def Blueprint.targetRelativeRankDichotomy (dag : Blueprint data mode)
    [NeZero data.targetRelativeRankDichotomies.length]
    (index : Fin data.targetRelativeRankDichotomies.length :=
      firstFamilyIndex data.targetRelativeRankDichotomies.length)
    (rankDrop : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (fullRank : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (rankDropName : String := "") (rankDropNote : String := "")
    (fullRankName : String := "") (fullRankNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := rankDropName, note := rankDropNote }
        right := { name := fullRankName, note := fullRankNote } })
    ⟨.inr (.inr (.inr (.inl index)))⟩
    (rankDrop .root) (fullRank .root)

/-- Target-relative rank whose dependent-coordinate terminal is linked by
type to an exact interface-replacement closure producer. -/
def Blueprint.compressionLinkedTargetRelativeRankDichotomy
    (dag : Blueprint data mode)
    [NeZero data.compressionLinkedTargetRelativeRankDichotomies.length]
    (index : Fin data.compressionLinkedTargetRelativeRankDichotomies.length :=
      firstFamilyIndex
        data.compressionLinkedTargetRelativeRankDichotomies.length)
    (rankDrop : Blueprint data mode → Blueprint data mode := fun branch => branch)
    (fullRank : Blueprint data mode → Blueprint data mode := fun branch => branch)
    (name : String := "") (note : String := "")
    (rankDropName : String := "") (rankDropNote : String := "")
    (fullRankName : String := "") (fullRankNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := rankDropName, note := rankDropNote }
        right := { name := fullRankName, note := fullRankNote } })
    ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index)))))))⟩
    (rankDrop .root) (fullRank .root)

def Blueprint.supportLocalization (dag : Blueprint data mode)
    [NeZero data.localizations.length]
    (index : Fin data.localizations.length :=
      firstFamilyIndex data.localizations.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.supportLocalization index, index.isLt⟩

/-- Select a minimal target-avoiding context with Core's existing selector
and append its registered domain interpretation.  The author supplies only a
family index and documentation; selection and residual production remain
sealed. -/
def Blueprint.counterexampleLocalization (dag : Blueprint data mode)
    [NeZero data.counterexampleLocalizations.length]
    (index : Fin data.counterexampleLocalizations.length :=
      firstFamilyIndex data.counterexampleLocalizations.length)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.counterexampleLocalization index, index.isLt⟩

def Blueprint.rankBudget (dag : Blueprint data mode)
    [NeZero data.rankBudgets.length]
    (index : Fin data.rankBudgets.length := firstFamilyIndex data.rankBudgets.length)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.rankBudget index, index.isLt⟩

def Blueprint.closedCode (dag : Blueprint data mode)
    [NeZero data.closedCodes.length]
    (index : Fin data.closedCodes.length := firstFamilyIndex data.closedCodes.length)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.closedCode index, index.isLt⟩

def Blueprint.obstructionPackingClosure (dag : Blueprint data mode)
    [NeZero data.obstructionPackingClosures.length]
    (index : Fin data.obstructionPackingClosures.length :=
      firstFamilyIndex data.obstructionPackingClosures.length)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.obstructionPackingClosure index, index.isLt⟩

def Blueprint.exactFiniteLocalAlgebra (dag : Blueprint data mode)
    [NeZero data.exactFiniteLocalAlgebras.length]
    (index : Fin data.exactFiniteLocalAlgebras.length :=
      firstFamilyIndex data.exactFiniteLocalAlgebras.length)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.exactFiniteLocalAlgebra index, index.isLt⟩

def Blueprint.finiteBarrierEnumeration (dag : Blueprint data mode)
    [NeZero data.finiteBarrierEnumerations.length]
    (index : Fin data.finiteBarrierEnumerations.length :=
      firstFamilyIndex data.finiteBarrierEnumerations.length)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.finiteBarrierEnumeration index, index.isLt⟩

def Blueprint.finiteDensityBudget (dag : Blueprint data mode)
    [NeZero data.finiteDensityBudgets.length]
    (index : Fin data.finiteDensityBudgets.length :=
      firstFamilyIndex data.finiteDensityBudgets.length)
    (overflow : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (cap : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (overflowName : String := "") (overflowNote : String := "")
    (capName : String := "") (capNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := overflowName, note := overflowNote }
        right := { name := capName, note := capNote } })
    (BinaryStrategyRef.finiteDensityBudget index)
    (overflow .root) (cap .root)

private theorem finiteDensityBudget_public_constructor_is_binary
    (dag : Blueprint data mode)
    [NeZero data.finiteDensityBudgets.length]
    (index : Fin data.finiteDensityBudgets.length)
    (overflow cap : Blueprint data mode → Blueprint data mode)
    (name note overflowName overflowNote capName capNote : String) :
    dag.finiteDensityBudget index overflow cap name note
        overflowName overflowNote capName capNote =
      .binaryBranch (dag.withMetadata
          { display := { name, note }
            left := { name := overflowName, note := overflowNote }
            right := { name := capName, note := capNote } })
        (BinaryStrategyRef.finiteDensityBudget index)
        (overflow .root) (cap .root) := rfl

def Blueprint.finiteStateCapacity (dag : Blueprint data mode)
    [NeZero data.finiteStateCapacities.length]
    (index : Fin data.finiteStateCapacities.length :=
      firstFamilyIndex data.finiteStateCapacities.length)
    (nonCapacity : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (capacity : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (nonCapacityName : String := "") (nonCapacityNote : String := "")
    (capacityName : String := "") (capacityNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := nonCapacityName, note := nonCapacityNote }
        right := { name := capacityName, note := capacityNote } })
    (BinaryStrategyRef.finiteStateCapacity index)
    (nonCapacity .root) (capacity .root)

def Blueprint.finiteScheduleCapacity (dag : Blueprint data mode)
    [NeZero data.finiteScheduleCapacities.length]
    (index : Fin data.finiteScheduleCapacities.length :=
      firstFamilyIndex data.finiteScheduleCapacities.length)
    (nonCapacity : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (capacity : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (nonCapacityName : String := "") (nonCapacityNote : String := "")
    (capacityName : String := "") (capacityNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := nonCapacityName, note := nonCapacityNote }
        right := { name := capacityName, note := capacityNote } })
    (BinaryStrategyRef.finiteScheduleCapacity index)
    (nonCapacity .root) (capacity .root)

/-- **Manuscript nodes `[111]`--`[124]`.**  The route-8 carrier closure: the
CT5 -> CT14 -> CT12 composition that terminates exit `(8)`.  The `closure` arm is
node `[124]`, the terminal two-carrier obstruction; every other terminal of the
three stages lands on the `nonClosure` arm. -/
def Blueprint.route8CarrierClosure (dag : Blueprint data mode)
    [NeZero data.route8CarrierClosures.length]
    (index : Fin data.route8CarrierClosures.length :=
      firstFamilyIndex data.route8CarrierClosures.length)
    (nonClosure : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (closure : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (nonClosureName : String := "") (nonClosureNote : String := "")
    (closureName : String := "") (closureNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := nonClosureName, note := nonClosureNote }
        right := { name := closureName, note := closureNote } })
    (BinaryStrategyRef.route8CarrierClosure index)
    (nonClosure .root) (closure .root)

def Blueprint.targetOrAvoid (dag : Blueprint data mode)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.targetOrAvoid, trivial⟩

def Blueprint.coldBranchAggregation (dag : Blueprint data mode)
    [NeZero data.coldBranchAggregations.length]
    (index : Fin data.coldBranchAggregations.length :=
      firstFamilyIndex data.coldBranchAggregations.length)
    (name : String := "") (note : String := "") : Blueprint data mode :=
  .step (dag.withMetadata { display := { name, note } })
    ⟨.coldBranchAggregation index, index.isLt⟩

def Blueprint.finiteStateNetChargeContinuation (dag : Blueprint data mode)
    (typeA : Blueprint data mode → Blueprint data mode := fun branch => branch)
    (typeB : Blueprint data mode → Blueprint data mode := fun branch => branch)
    (name : String := "") (note : String := "")
    (typeAName : String := "") (typeANote : String := "")
    (typeBName : String := "") (typeBNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := typeAName, note := typeANote }
        right := { name := typeBName, note := typeBNote } })
    BinaryStrategyRef.finiteStateNetChargeContinuation
    (typeA .root) (typeB .root)


def Blueprint.dichotomy (dag : Blueprint data mode)
    [NeZero data.dichotomies.length]
    (index : Fin data.dichotomies.length :=
      firstFamilyIndex data.dichotomies.length)
    (left : Blueprint data mode := .root)
    (right : Blueprint data mode := .root)
    (name : String := "") (note : String := "")
    (leftName : String := "") (leftNote : String := "")
    (rightName : String := "") (rightNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := leftName, note := leftNote }
        right := { name := rightName, note := rightNote } })
    ⟨.inl index⟩ left right

def Blueprint.scaleThresholdDichotomy (dag : Blueprint data mode)
    [NeZero data.scaleThresholdDichotomies.length]
    (index : Fin data.scaleThresholdDichotomies.length :=
      firstFamilyIndex data.scaleThresholdDichotomies.length)
    (above : Blueprint data mode → Blueprint data mode := fun branch => branch)
    (atOrBelow : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (aboveName : String := "") (aboveNote : String := "")
    (atOrBelowName : String := "") (atOrBelowNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := aboveName, note := aboveNote }
        right := { name := atOrBelowName, note := atOrBelowNote } })
    ⟨.inr (.inl index)⟩
    (above .root) (atOrBelow .root)

def Blueprint.atomContextObstructionDichotomy (dag : Blueprint data mode)
    [NeZero data.atomContextObstructionDichotomies.length]
    (index : Fin data.atomContextObstructionDichotomies.length :=
      firstFamilyIndex data.atomContextObstructionDichotomies.length)
    (atom : Blueprint data mode → Blueprint data mode := fun branch => branch)
    (context : Blueprint data mode → Blueprint data mode :=
      fun branch => branch)
    (name : String := "") (note : String := "")
    (atomName : String := "") (atomNote : String := "")
    (contextName : String := "") (contextNote : String := "") :
    Blueprint data mode :=
  .binaryBranch (dag.withMetadata
      { display := { name, note }
        left := { name := atomName, note := atomNote }
        right := { name := contextName, note := contextNote } })
    ⟨.inr (.inr (.inl index))⟩
    (atom .root) (context .root)

/-- Begin the sealed target-or-minimal reduction.  The result exposes only
the next legal Strategy in the dependent continuation. -/
def Blueprint.minimalCounterexampleSelection (dag : Blueprint data mode)
    [NeZero data.counterexampleReductions.length]
    (index : Fin data.counterexampleReductions.length :=
      firstFamilyIndex data.counterexampleReductions.length)
    (name : String := "") (note : String := "") :
    AfterMinimalCounterexampleSelection data mode :=
  ⟨dag, index, { display := { name, note } }⟩

/-- Append target-algebra reduction to the selected avoiding residual. -/
def AfterMinimalCounterexampleSelection.targetAlgebraReduction
    (selected : AfterMinimalCounterexampleSelection data mode)
    (name : String := "") (note : String := "") :
    AfterTargetAlgebraReduction data mode :=
  ⟨selected, { display := { name, note } }⟩

/-- Append strict-subobject exclusion using the selected minimality context. -/
def AfterTargetAlgebraReduction.minimalSubobjectExclusion
    (target : AfterTargetAlgebraReduction data mode)
    (name : String := "") (note : String := "") :
    AfterMinimalSubobjectExclusion data mode :=
  ⟨target, { display := { name, note } }⟩

/-- Append critical-modification structure and return the ordinary Blueprint.
Core lowers the completed flat chain to its sealed dependent continuation. -/
def AfterMinimalSubobjectExclusion.criticalModificationStructure
    (minimal : AfterMinimalSubobjectExclusion data mode)
    (name : String := "") (note : String := "") :
    AfterCriticalModificationStructure data mode :=
  ⟨minimal, { display := { name, note } }⟩

def AfterCriticalModificationStructure.interfaceReplacementClosure
    (critical : AfterCriticalModificationStructure data mode)
    (name : String := "") (note : String := "") :
    Blueprint data mode :=
  let minimal := critical.minimal
  let target := minimal.target
  let selected := target.selected
  .minimalCounterexample
    (selected.dag.withMetadata selected.selectionMetadata)
    selected.index
    ⟨target.targetMetadata, minimal.minimalMetadata,
      critical.criticalMetadata, { display := { name, note } }⟩

def Blueprint.note (dag : Blueprint data mode)
    (label : String) : Blueprint data mode :=
  .annotate dag label

def Blueprint.label (dag : Blueprint data mode)
    (name : String) : Blueprint data mode :=
  .labelled dag name

def Blueprint.autoroute (dag : Blueprint data .authoring)
    (name : String := "") (note : String := "")
    (tags : List String := []) : Blueprint data .authoring :=
  .route dag { name, note, tags }

/-! ### Compiler-owned typed capabilities

The same key-only capability algebra is used both while resolving targetless
routes and while verifying the exact fact manifest. -/

private inductive CapabilityKey where
  /-- Distinguished branch-closure fact required by the canonical fact
  vocabulary.  It is never a strategy production. -/
  | closed
  | obstructionPacking (index : Nat)
  | exactFiniteLocalCode
  | finiteBarrierSummary
  | normalizedSupportLedger (index : Nat)
  | boundaryAccountingLedger
  | localSupplyLedger (index : Nat)
  | targetRankDrop
  | fullRankExactCode
  | fullRankCertificate
  | independentRank
  | finiteStateCapacityContinuation
  | finiteDensityOverflow
  /-- The surviving alternative of the multiplicative density comparison.
  Its complementary key `finiteDensityOverflow` was already routed; without
  this one the *cap* branch published nothing, so the one fact the whole
  near-cubic continuation rests on was discarded at the node where the proof
  continues. -/
  | finiteDensityCap
  | minimalContext
  | minimalClosureAt (index : Nat)
  | canonicalPairDependence (index : Nat)
  | canonicalPairRole (index : Nat)
  | canonicalCapacityAssignment (index : Nat)
  | canonicalCapacityFibre (index : Nat)
  | canonicalCapacityAggregate (index : Nat)
  | homogeneousPressureOverload (index : Nat)
  | homogeneousPressureReconciliation (index : Nat)
  | homogeneousPressureAggregate (index : Nat)
  | bottleneckCollision (index : Nat)
  | bottleneckPressure (index : Nat)
  | bottleneckClassification (index : Nat)
  | bottleneckSeparator (index : Nat)
  | homogeneousHandoff (index : Nat)
  /-- **The near-cubic spine estimate carried by the at-or-below arm of the
  `index`-th scale-threshold split.**

  `def:surviving-cold-branch` (vi) is a branch precondition, not something the
  cold corridor derives: the split already proved `load ≤ table(size)` at the
  active object and retained it in `RightBranchStage`.  Without this key that
  proof was discarded at `rightProductions`, exactly as the surviving density
  cap was before `finiteDensityCap` was routed, and every consumer nested
  inside the near-cubic arm lost the one estimate the whole continuation rests
  on. -/
  | nearCubicSpine (index : Nat)
  deriving DecidableEq

/-- Framework-owned capability requirements of each sealed Strategy. -/
private def StrategyKey.requirements
    (data : StrategyData.{uAmbient, uBranch, uData} P T) :
    (key : StrategyKey) → key.ResolvedIn data → List CapabilityKey
  | .obstructionPackingClosure _, _ => [.minimalContext]
  | .finiteBarrierEnumeration _, _ => [.exactFiniteLocalCode]
  | .finiteDensityBudget _, _ =>
      [.obstructionPacking 0, .finiteBarrierSummary, .nearCubicSpine 0]
  | .supportComplementNormalization index, resolved =>
      [.obstructionPacking
        (data.supportComplementNormalizations[index]'resolved).fst,
        .finiteDensityCap]
  | .boundaryDemandAccounting index, resolved =>
      [.normalizedSupportLedger
        (data.boundaryDemandAccountings[index]'resolved).fst]
  | .localSupplyLowerBound index, resolved =>
      let boundaryIndex := data.localSupplyLowerBounds[index]'resolved |>.fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      [.normalizedSupportLedger supportIndex, .boundaryAccountingLedger]
  | .targetRelativeRankDichotomy index, resolved =>
      let packed := data.targetRelativeRankDichotomies[index]'resolved
      let supplyIndex := packed.snd.fst
      let boundaryIndex := data.localSupplyLowerBounds[supplyIndex].fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      [.normalizedSupportLedger supportIndex,
        .localSupplyLedger supplyIndex]
  | .compressionLinkedTargetRelativeRankDichotomy index, resolved =>
      let packed :=
        data.compressionLinkedTargetRelativeRankDichotomies[index]'resolved
      let supplyIndex := packed.snd.fst
      let boundaryIndex := data.localSupplyLowerBounds[supplyIndex].fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      [.normalizedSupportLedger supportIndex,
        .localSupplyLedger supplyIndex,
        .minimalClosureAt packed.reductionIndex]
  | .finiteStateCapacity index, resolved =>
      let supplyIndex := (data.finiteStateCapacities[index]'resolved).fst
      [.independentRank, .finiteBarrierSummary,
        .fullRankCertificate,
        .localSupplyLedger supplyIndex]
  | .finiteStateNetChargeContinuation, _ =>
      [.finiteStateCapacityContinuation, .finiteDensityCap]
  | .coldBranchAggregation index, resolved =>
      let entry := data.coldBranchAggregations[index]'resolved
      let bottleneckIndex :=
        data.homogeneousBottlenecks[entry.handoffIndex].fst
      if entry.handoffRequired then
        [.obstructionPacking entry.fst,
          .finiteBarrierSummary, .finiteDensityOverflow,
          .minimalClosureAt entry.reductionIndex,
          .homogeneousHandoff entry.handoffIndex,
          .homogeneousPressureOverload
            data.homogeneousBottlenecks[entry.handoffIndex].pressureIndex,
          .bottleneckSeparator bottleneckIndex]
      else
        [.obstructionPacking entry.fst,
          .finiteBarrierSummary, .finiteDensityOverflow,
          .minimalClosureAt entry.reductionIndex]
  | .finiteBottleneckClassification index, resolved =>
      let pressureIndex := data.finiteBottleneckClassifications[index]'resolved |>.fst
      [.homogeneousPressureOverload pressureIndex]
  | .homogeneousBottleneck index, resolved =>
      let entry := data.homogeneousBottlenecks[index]'resolved
      let bottleneckIndex := entry.fst
      let pressureIndex :=
        data.finiteBottleneckClassifications[bottleneckIndex].fst
      [.canonicalPairDependence pressureIndex,
        .canonicalPairRole pressureIndex,
        .canonicalCapacityAssignment pressureIndex,
        .canonicalCapacityFibre pressureIndex,
        .canonicalCapacityAggregate pressureIndex,
        .homogeneousPressureOverload pressureIndex,
        .homogeneousPressureReconciliation pressureIndex,
        .homogeneousPressureAggregate pressureIndex,
        .bottleneckCollision bottleneckIndex,
        .bottleneckPressure bottleneckIndex,
        .bottleneckClassification bottleneckIndex,
        .bottleneckSeparator bottleneckIndex]
  | _, _ => []

/-- Framework-owned capability productions of each sealed Strategy. -/
private def StrategyKey.productions
    (data : StrategyData.{uAmbient, uBranch, uData} P T) :
    (key : StrategyKey) → key.ResolvedIn data → List CapabilityKey
  | .obstructionPackingClosure index, _ => [.obstructionPacking index]
  | .exactFiniteLocalAlgebra _, _ => [.exactFiniteLocalCode]
  | .finiteBarrierEnumeration _, _ => [.finiteBarrierSummary]
  | .supportComplementNormalization index, _ => [.normalizedSupportLedger index]
  | .boundaryDemandAccounting _, _ => [.boundaryAccountingLedger]
  | .localSupplyLowerBound index, _ => [.localSupplyLedger index]
  | .canonicalPairResponseAccounting index, _ =>
      [.canonicalPairDependence index, .canonicalPairRole index]
  | .canonicalCapacityTokenAccounting index, _ =>
      [.canonicalCapacityAssignment index, .canonicalCapacityFibre index,
        .canonicalCapacityAggregate index]
  | .coupledHomogeneousFibrePressure index, _ =>
      [.homogeneousPressureOverload index,
        .homogeneousPressureReconciliation index,
        .homogeneousPressureAggregate index]
  | .finiteBottleneckClassification index, _ =>
      [.bottleneckCollision index, .bottleneckPressure index,
        .bottleneckClassification index, .bottleneckSeparator index]
  | _, _ => []

/-- Capabilities published only on the left terminal of a binary Strategy. -/
private def BinaryStrategyRef.leftProductions
    (strategy : BinaryStrategyRef data) : List CapabilityKey :=
  match strategy.view with
  | .inr (.inr (.inr (.inl _))) => [.targetRankDrop]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) =>
      [.targetRankDrop]
  | .inr (.inr (.inr (.inr (.inl _)))) => [.finiteDensityOverflow]
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) =>
      [.finiteStateCapacityContinuation]
  | _ => []

/-- Capabilities published only on the right terminal of a binary Strategy.

The compression-linked target-relative rank family repeats the ordinary
family's *right* entry only: both right payloads are the same
`FullRankResidual` carrying the same CT15 full-rank ledger output, so the
exact independent rank and the exact-code marker are available on either
branch verbatim.  The linked left arm also publishes the exact dependent
rank-drop payload as `targetRankDrop` for the downstream dependence-routing
row. -/
private def BinaryStrategyRef.rightProductions
    (strategy : BinaryStrategyRef data) : List CapabilityKey :=
  match strategy.view with
  | .inr (.inl index) => [.nearCubicSpine index]
  | .inr (.inr (.inr (.inl _))) =>
      [.fullRankExactCode, .fullRankCertificate, .independentRank]
  | .inr (.inr (.inr (.inr (.inl _)))) => [.finiteDensityCap]
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) =>
      [.finiteStateCapacityContinuation]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) =>
      [.fullRankExactCode, .fullRankCertificate, .independentRank]
  | _ => []

private def StrategyKey.requirementsMet
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (key : StrategyKey) (resolved : key.ResolvedIn data)
    (available : List CapabilityKey) : Bool :=
  (key.requirements data resolved).all fun required =>
    available.contains required

/-- Computable no-duplicate boundary for one atomic publication. -/
private def CapabilityKey.fresh
    (produced available : List CapabilityKey) : Bool :=
  produced.all fun key => !available.contains key

private theorem CapabilityKey.not_mem_of_fresh
    {produced available : List CapabilityKey}
    (fresh : CapabilityKey.fresh produced available = true)
    {key : CapabilityKey} (member : key ∈ produced) : key ∉ available := by
  simp only [CapabilityKey.fresh, List.all_eq_true] at fresh
  intro present
  have rejected := fresh key member
  simp [present] at rejected

/-- One public proof entry.  Shared continuations are expressed structurally;
targetless branch routes are resolved to compatible continuation entries by
Core.  There is no named-block or destination-string API. -/
structure Program
    (data : StrategyData.{uAmbient, uBranch, uData} P T) where
  private mk ::
  private entry : Blueprint data .authoring

namespace Program

def ofBlueprint (entry : Blueprint data .authoring) : Program data :=
  .mk entry

/-! The public frontend normalizes with primitive `Blueprint.rec` folds.
These folds reduce directly in the kernel, keeping `ofDag%` resource usage
proportional to the authored DAG and avoiding application-owned recursion
settings. -/

private def depthOf? (depths : List (Nat × Nat)) (id : Nat) : Option Nat :=
  (depths.find? fun entry => entry.1 == id).map Prod.snd

private noncomputable def spineEndsInRouteFast
    (dag : Blueprint data mode) : Bool :=
  Blueprint.rec
    (motive := fun _ _ => Bool)
    false
    (fun _ _ _ => false)
    (fun _ _ _ _ _ _ _ => false)
    (fun _ _ _ _ _ _ _ _ _ => false)
    (fun _ _ _ _ => false)
    (fun _ _ rest => rest)
    (fun _ _ rest => rest)
    (fun _ _ rest => rest)
    (fun _ _ _ => true)
    (fun _ _ _ _ => false)
    dag

private noncomputable def localSourceFast
    (dag : Blueprint data mode) : Nat -> Option Nat -> Option Nat :=
  Blueprint.rec
    (motive := fun _ _ => Nat -> Option Nat -> Option Nat)
    (fun _ fallback => fallback)
    (fun _ _ _ nextId _ => some nextId)
    (fun _ _ _ _ _ _ _ nextId _ => some nextId)
    (fun _ _ _ _ _ _ _ _ _ nextId _ => some nextId)
    (fun _ _ _ _ nextId _ => some nextId)
    (fun _ _ rest => rest)
    (fun _ _ rest => rest)
    (fun _ _ rest => rest)
    (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ => none)
    dag

/-- Stable structural IDs consumed by an authored subtree.  Documentation
and route markers consume no IDs; the dependent minimal-counterexample block
consumes its five registered Strategy IDs. -/
private noncomputable def structuralIdCountFast :
    Blueprint data .authoring → Nat
  := fun dag =>
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with | .authoring => Nat | .expanded => PUnit)
    (fun {mode} => match mode with | .authoring => 0 | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest + 1 | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ rest left right =>
      match mode with
      | .authoring => rest + 1 + left + right
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ _ rest exceptional structured bounded =>
      match mode with
      | .authoring => rest + 1 + exceptional + structured + bounded
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ rest =>
      match mode with | .authoring => rest + 5 | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun _ _ rest => rest)
    (fun _ _ _ _ => ⟨⟩)
    dag

/-- First Strategy executed by a nonempty authored continuation, expressed in
the global stable-ID allocation beginning at `nextId`. -/
private noncomputable def firstExecutionIdFast :
    Blueprint data .authoring → Nat → Option Nat
  := fun dag =>
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with
      | .authoring => Nat → Option Nat
      | .expanded => PUnit)
    (fun {mode} =>
      match mode with
      | .authoring => fun _ => none
      | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with
      | .authoring => fun nextId =>
          (rest (nextId + 1)).orElse fun _ => some nextId
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ rest _ _ =>
      match mode with
      | .authoring => fun nextId =>
          (rest (nextId + 1)).orElse fun _ => some nextId
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ _ rest _ _ _ =>
      match mode with
      | .authoring => fun nextId =>
          (rest (nextId + 1)).orElse fun _ => some nextId
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ rest =>
      match mode with
      | .authoring => fun nextId =>
          (rest (nextId + 1)).orElse fun _ => some nextId
      | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun _ _ rest => rest)
    (fun _ _ _ _ => ⟨⟩)
    dag

/-- Sibling reuse is deliberately limited to route-free continuations in the
initial implementation.  Enclosing continuations retain their existing
forward-only semantics.  This conservative guard makes a sibling route
acyclic by construction without accepting a second routing decision inside
the reused continuation. -/
private noncomputable def containsRouteFast :
    Blueprint data .authoring → Bool
  := fun dag =>
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with | .authoring => Bool | .expanded => PUnit)
    (fun {mode} =>
      match mode with | .authoring => false | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ rest left right =>
      match mode with
      | .authoring => rest || left || right
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ _ rest exceptional structured bounded =>
      match mode with
      | .authoring => rest || exceptional || structured || bounded
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun _ _ _ => true)
    (fun _ _ _ _ => ⟨⟩)
    dag

/-- Core-derived work of an authored continuation.  It uses exactly the same
sequential-sum and branch-max laws as the sealed expanded DAG. -/
private noncomputable def authoredWorkFast :
    Blueprint data .authoring → Nat
  := fun dag =>
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with | .authoring => Nat | .expanded => PUnit)
    (fun {mode} => match mode with | .authoring => 0 | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest + 1 | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ rest left right =>
      match mode with
      | .authoring => rest + 1 + max left right
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ _ rest exceptional structured bounded =>
      match mode with
      | .authoring => rest + 1 + max exceptional (max structured bounded)
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ rest =>
      match mode with | .authoring => rest + 5 | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun _ _ rest => rest + 1)
    (fun _ _ _ _ => ⟨⟩)
    dag

/-- Capability result of an authored continuation.  This is the exact
key-only counterpart of `VerifiedManifest`: it reads no ledger value and is
used only to discard structurally visible sibling entries whose registered
requirements are unavailable at the route source. -/
private noncomputable def authoredCapabilityOutput?
    (dag : Blueprint data .authoring) :
    List CapabilityKey → Option (List CapabilityKey) :=
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with
      | .authoring => List CapabilityKey → Option (List CapabilityKey)
      | .expanded => PUnit)
    (fun {mode} =>
      match mode with
      | .authoring => fun available => some available
      | .expanded => ⟨⟩)
    (fun {mode} _ strategy rest =>
      match mode with
      | .authoring => fun available => do
          let current ← rest available
          if strategy.key.requirementsMet data strategy.resolved current then
            some (strategy.key.productions data strategy.resolved ++ current)
          else none
      | .expanded => ⟨⟩)
    (fun {mode} _ strategy _ _ rest left right =>
      match mode with
      | .authoring => fun available => do
          let current ← rest available
          if strategy.key.requirementsMet data strategy.resolved current then
            let _ ← left (strategy.leftProductions ++ current)
            let _ ← right (strategy.rightProductions ++ current)
            some current
          else none
      | .expanded => ⟨⟩)
    (fun {mode} _ index _ _ _ rest exceptional structured bounded =>
      match mode with
      | .authoring => fun available => do
          let current ← rest available
          let _ ← exceptional current
          let _ ← structured (.homogeneousHandoff index.val :: current)
          let _ ← bounded current
          some current
      | .expanded => ⟨⟩)
    (fun {mode} _ index _ rest =>
      match mode with
      | .authoring => fun available => do
          let _current ← rest available
          some [.minimalClosureAt index.val, .minimalContext]
      | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun _ _ rest => rest)
    (fun _ _ _ _ => ⟨⟩)
    dag

private structure StructuralRouteCandidate
    (data : StrategyData.{uAmbient, uBranch, uData} P T) where
  id : Nat
  depth : Nat
  scope : RouteScope
  destinationWork : Nat
  continuation : Option (Blueprint data .authoring)

private def StructuralRouteCandidate.preferred
    (left right : StructuralRouteCandidate data) : Bool :=
  left.depth < right.depth ||
    (left.depth = right.depth && left.id < right.id)

private def insertRouteCandidate
    (candidate : StructuralRouteCandidate data) :
    List (StructuralRouteCandidate data) →
      List (StructuralRouteCandidate data)
  | [] => [candidate]
  | head :: tail =>
      if candidate.preferred head then candidate :: head :: tail
      else head :: insertRouteCandidate candidate tail

private def orderRouteCandidates
    (candidates : List (StructuralRouteCandidate data)) :
    List (StructuralRouteCandidate data) :=
  candidates.foldr insertRouteCandidate []

/-- One sibling continuation offered as a routing destination.

`allowRoutedDestination` controls whether a candidate that itself contains a
targetless route may be selected.  Refusing them outright is sound but too
strong: it makes any branch containing a route ineligible as a destination even
when routing into it is acyclic.  A cycle among siblings needs edges in *both*
directions, so admitting routed candidates in one direction only is enough.
Core admits them for the left-to-right edge and keeps the strict guard on the
right-to-left edge; a two-cycle would then need the left branch both to contain
a route (to emit the left-to-right edge) and to contain none (for the
right-to-left edge to be offered at all). -/
private noncomputable def siblingCandidate?
    (dag : Blueprint data .authoring) (startId : Nat)
    (depths : List (Nat × Nat))
    (allowRoutedDestination : Bool := false) :
    Option (StructuralRouteCandidate data) :=
  if !allowRoutedDestination && containsRouteFast dag then none
  else
    match firstExecutionIdFast dag startId with
    | none => none
    | some id =>
        match depthOf? depths id with
        | none => none
        | some depth =>
            some ({
              id := id
              depth := depth
              scope := .sibling
              destinationWork := authoredWorkFast dag
              continuation := some dag
            } : StructuralRouteCandidate data)

private def enclosingCandidate?
    (id : Nat) (depths : List (Nat × Nat)) :
    Option (StructuralRouteCandidate data) :=
  match depthOf? depths id with
  | none => none
  | some depth =>
      some ({
        id := id
        depth := depth
        scope := .enclosing
        destinationWork := 0
        continuation := none
      } : StructuralRouteCandidate data)

private noncomputable def StructuralRouteCandidate.capabilityCompatible
    (candidate : StructuralRouteCandidate data)
    (available : List CapabilityKey) : Bool :=
  match candidate.scope, candidate.continuation with
  | .enclosing, _ => true
  | .sibling, some continuation =>
      (authoredCapabilityOutput? continuation available).isSome
  | .sibling, none => false

private noncomputable def collectDepthsFast
    (dag : Blueprint data .authoring) :
    Nat -> Nat -> List (Nat × Nat) × Nat × Nat :=
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with
      | .authoring => Nat -> Nat -> List (Nat × Nat) × Nat × Nat
      | .expanded => PUnit)
    (fun {mode} =>
      match mode with
      | .authoring => fun nextId baseDepth => ([], nextId, baseDepth)
      | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with
      | .authoring => fun nextId baseDepth =>
          let id := nextId
          let (depths, nextId, currentDepth) :=
            rest (nextId + 1) baseDepth
          (depths ++ [(id, currentDepth)], nextId, currentDepth + 1)
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ rest left right =>
      match mode with
      | .authoring => fun nextId baseDepth =>
          let id := nextId
          let (priorDepths, nextId, branchDepth) :=
            rest (nextId + 1) baseDepth
          let (leftDepths, nextId, leftExit) :=
            left nextId (branchDepth + 1)
          let (rightDepths, nextId, rightExit) :=
            right nextId (branchDepth + 1)
          (priorDepths ++ [(id, branchDepth)] ++ leftDepths ++ rightDepths,
            nextId, max leftExit rightExit)
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ _ _ rest exceptional structured bounded =>
      match mode with
      | .authoring => fun nextId baseDepth =>
          let id := nextId
          let (priorDepths, nextId, branchDepth) :=
            rest (nextId + 1) baseDepth
          let (exceptionalDepths, nextId, exceptionalExit) :=
            exceptional nextId (branchDepth + 1)
          let (structuredDepths, nextId, structuredExit) :=
            structured nextId (branchDepth + 1)
          let (boundedDepths, nextId, boundedExit) :=
            bounded nextId (branchDepth + 1)
          (priorDepths ++ [(id, branchDepth)] ++ exceptionalDepths ++
              structuredDepths ++ boundedDepths,
            nextId, max exceptionalExit (max structuredExit boundedExit))
      | .expanded => ⟨⟩)
    (fun {mode} _ _ _ rest =>
      match mode with
      | .authoring => fun nextId baseDepth =>
          let id := nextId
          let (priorDepths, nextId, branchDepth) :=
            rest (nextId + 1) baseDepth
          (priorDepths ++ [(id, branchDepth)],
            nextId + 4, branchDepth + 5)
      | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun {mode} _ _ rest =>
      match mode with | .authoring => rest | .expanded => ⟨⟩)
    (fun _ _ rest nextId baseDepth =>
      let (depths, nextId, exitDepth) := rest nextId baseDepth
      (depths, nextId, exitDepth + 1))
    (fun _ _ _ _ => ⟨⟩)
    dag

private noncomputable def resolveBlueprintFast
    (dag : Blueprint data .authoring) :
    Nat -> List (Nat × Nat) -> List (StructuralRouteCandidate data) ->
      Option Nat -> List CapabilityKey ->
        Except String (Blueprint data .expanded × Nat) :=
  Blueprint.rec
    (motive := fun mode _ =>
      match mode with
      | .authoring =>
          Nat -> List (Nat × Nat) -> List (StructuralRouteCandidate data) ->
            Option Nat -> List CapabilityKey ->
              Except String (Blueprint data .expanded × Nat)
      | .expanded => PUnit)
    (fun {mode} =>
      match mode with
      | .authoring => fun nextId _ _ _ _ => .ok (.root, nextId)
      | .expanded => ⟨⟩)
    (fun {mode} rest strategy resolveRest =>
      match mode with
      | .authoring => fun nextId depths candidates incoming available =>
          if spineEndsInRouteFast rest then
            .error "autoroute must terminate its branch; a strategy follows it"
          else do
            let id := nextId
            let some candidate := enclosingCandidate? id depths
              | throw
                  "Core failed to recover structural depth for an enclosing continuation"
            let (rest, nextId) ←
              resolveRest (nextId + 1) depths (candidate :: candidates)
                incoming available
            .ok (.step rest strategy, nextId)
      | .expanded => ⟨⟩)
    (fun {mode} rest strategy _left _right resolveRest resolveLeft
        resolveRight =>
      match mode with
      | .authoring => fun nextId depths candidates incoming available =>
          if spineEndsInRouteFast rest then
            .error "autoroute must terminate its branch; a dichotomy follows it"
          else do
            let id := nextId
            let some candidate := enclosingCandidate? id depths
              | throw
                  "Core failed to recover structural depth for an enclosing continuation"
            let some current := authoredCapabilityOutput? rest available
              | throw
                  "a branch prefix requests a ledger capability that its predecessor does not provide"
            unless
                strategy.key.requirementsMet data strategy.resolved current do
              throw
                "a binary Strategy requests a ledger capability that its predecessor does not provide"
            let (rest, nextId) ←
              resolveRest (nextId + 1) depths (candidate :: candidates)
                incoming available
            let leftStart := nextId
            let rightStart := leftStart + structuralIdCountFast _left
            let leftSibling := siblingCandidate? _right rightStart depths
              (allowRoutedDestination := true)
            let rightSibling := siblingCandidate? _left leftStart depths
            let (left, nextId) ←
              resolveLeft nextId depths
                (leftSibling.toList ++ candidates) (some id)
                (strategy.leftProductions ++ current)
            let (right, nextId) ←
              resolveRight nextId depths
                (rightSibling.toList ++ candidates) (some id)
                (strategy.rightProductions ++ current)
            .ok (.binaryBranch rest strategy left right, nextId)
      | .expanded => ⟨⟩)
    (fun {mode} rest index _exceptional _structured _bounded resolveRest
        resolveExceptional resolveStructured resolveBounded =>
      match mode with
      | .authoring => fun nextId depths candidates incoming available =>
          if spineEndsInRouteFast rest then
            .error
              "autoroute must terminate its branch; homogeneous bottleneck follows it"
          else do
            let id := nextId
            let some candidate := enclosingCandidate? id depths
              | throw
                  "Core failed to recover structural depth for an enclosing continuation"
            let some current := authoredCapabilityOutput? rest available
              | throw
                  "a branch prefix requests a ledger capability that its predecessor does not provide"
            let (rest, nextId) ←
              resolveRest (nextId + 1) depths (candidate :: candidates)
                incoming available
            let exceptionalStart := nextId
            let structuredStart :=
              exceptionalStart + structuralIdCountFast _exceptional
            let boundedStart :=
              structuredStart + structuralIdCountFast _structured
            let exceptionalSiblingCandidates :=
              (siblingCandidate? _structured structuredStart depths).toList ++
                (siblingCandidate? _bounded boundedStart depths).toList ++
                candidates
            let structuredSiblingCandidates :=
              (siblingCandidate? _exceptional exceptionalStart depths).toList ++
                (siblingCandidate? _bounded boundedStart depths).toList ++
                candidates
            let boundedSiblingCandidates :=
              (siblingCandidate? _exceptional exceptionalStart depths).toList ++
                (siblingCandidate? _structured structuredStart depths).toList ++
                candidates
            let (exceptional, nextId) ←
              resolveExceptional nextId depths exceptionalSiblingCandidates
                (some id) current
            let (structured, nextId) ←
              resolveStructured nextId depths structuredSiblingCandidates
                (some id) (.homogeneousHandoff index :: current)
            let (bounded, nextId) ←
              resolveBounded nextId depths boundedSiblingCandidates (some id)
                current
            .ok (.homogeneousBottleneckBranches rest index exceptional
              structured bounded, nextId)
      | .expanded => ⟨⟩)
    (fun {mode} rest index continuation resolveRest =>
      match mode with
      | .authoring => fun nextId depths candidates incoming available =>
          if spineEndsInRouteFast rest then
            .error "autoroute must terminate its branch; minimal selection follows it"
          else do
            let id := nextId
            let some candidate := enclosingCandidate? id depths
              | throw
                  "Core failed to recover structural depth for an enclosing continuation"
            let (rest, nextId) ←
              resolveRest (nextId + 1) depths (candidate :: candidates)
                incoming available
            .ok (.minimalCounterexample rest index continuation, nextId + 4)
      | .expanded => ⟨⟩)
    (fun {mode} _ label resolveRest =>
      match mode with
      | .authoring => fun nextId depths next incoming available => do
          let (rest, nextId) ←
            resolveRest nextId depths next incoming available
          .ok (.annotate rest label, nextId)
      | .expanded => ⟨⟩)
    (fun {mode} _ name resolveRest =>
      match mode with
      | .authoring => fun nextId depths next incoming available => do
          let (rest, nextId) ←
            resolveRest nextId depths next incoming available
          .ok (.labelled rest name, nextId)
      | .expanded => ⟨⟩)
    (fun {mode} _ metadata resolveRest =>
      match mode with
      | .authoring => fun nextId depths next incoming available => do
          let (rest, nextId) ←
            resolveRest nextId depths next incoming available
          .ok (.documented rest metadata, nextId)
      | .expanded => ⟨⟩)
    (fun rest metadata resolveRest nextId depths candidates incoming available =>
      let source? := localSourceFast rest nextId incoming
      match source? with
      | none => .error
          "an autoroute source cannot contain an earlier autoroute"
      | some source =>
        let current? := authoredCapabilityOutput? rest available
        match current? with
        | none => .error
            "an autoroute prefix requests a ledger capability that its predecessor does not provide"
        | some current =>
            let ordered :=
              orderRouteCandidates (candidates.filter fun candidate =>
                candidate.id != source &&
                  candidate.capabilityCompatible current)
            match ordered with
            | [] => .error
                "autoroute has no compatible continuation; every targetless route \
                must occur on a branch with a nonempty compatible continuation"
            | destination :: _ =>
                match depthOf? depths source with
                | some sourceDepth => do
                    let (rest, nextId) ←
                      resolveRest nextId depths candidates incoming available
                    .ok (.resolvedRoute rest {
                      sourceId := source
                      destinationId := destination.id
                      sourceDepth
                      destinationDepth := destination.depth
                      scope := destination.scope
                      candidateIds := ordered.tail.map (·.id)
                      candidateDepths := ordered.tail.map (·.depth)
                      destinationWork := destination.destinationWork
                    } metadata, nextId)
                | none => .error
                    "Core failed to recover structural depth for a derived \
                    autoroute source")
    (fun _ _ _ _ => ⟨⟩)
    dag

private noncomputable def expand (program : Program data) :
    Except String (Blueprint data .expanded) :=
  let depths := (collectDepthsFast program.entry 0 0).1
  (resolveBlueprintFast program.entry 0 depths [] none []).map Prod.fst

end Program

/-! ## Private compiler recipes

A recipe is one resolved vertex: a contract at an arbitrary ledger stage
plus a certificate projection that recognizes target certificates inside the
literal produced payload.  All recipes are derived from `StrategyData`
through `residualOf`, so the residual and ledger do all data accounting. -/

private structure Recipe (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P) (Stage : Type uStage)
    [HasResidual Stage (Strategy.ProblemInput P)] where
  contract : Contract.{uStage, 0, uStage} Stage
  certify : (stage : Stage) -> Sigma (contract.Payload stage) ->
    Option (PLift (T.Predicate (residualOf stage : Strategy.ProblemInput P).object))
  /-- Present exactly when this vertex or compiled fragment consumes every
  payload it can produce into a target certificate.  This proof is built by
  the private compiler from registered terminal consumers; applications
  cannot supply it to `ofDag%`. -/
  closes : Option (PLift (
    ∀ stage payload, ∃ proof, certify stage payload = some proof)) := none

/-- Seal a contract's payload into the stage universe without touching its
terminal family or literal product. -/
private def sealPayload {Stage : Type uStage}
    (contract : Contract.{uStage, uTerminal, uPayload} Stage) :
    Contract.{uStage, uTerminal, max uPayload uStage} Stage :=
  Strategy.map contract (NewTerminal := contract.Terminal)
    (NewPayload := fun stage terminal =>
      ULift.{uStage} (contract.Payload stage terminal))
    (fun _ payload => ⟨payload.fst, ULift.up payload.snd⟩)

/-! ### Residual pull-backs of registered data

Each `lift*` re-indexes one registered family from the initial residual to
an arbitrary ledger stage through `residualOf`; the corresponding recipe
reuses the backend `asContract` constructor unchanged. -/

private def liftScan (scan : ScanData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.OrderedWitnessScan Stage where
  Item := fun stage => scan.Item (residualOf stage)
  schedule :=  fun stage => scan.schedule (residualOf stage)
  witness := fun stage item => scan.witness (residualOf stage) item
  witnessDecidable := fun stage item =>
    scan.witnessDecidable (residualOf stage) item
  exhaustive := fun stage item _ =>
    match scan.witnessDecidable (residualOf stage) item with
    | Decidable.isTrue proof => Or.inl proof
    | Decidable.isFalse proof => Or.inr proof

private def scanRecipe (scan : ScanData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage where
  contract := sealPayload (liftScan scan).asContract
  certify := fun _ _ => none

private def liftResponse (response : ResponseData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.ResponseClassifier Stage where
  Item := fun stage => response.Item (residualOf stage)
  Response := fun stage => response.Response (residualOf stage)
  schedule :=  fun stage =>
    response.schedule (residualOf stage)
  observe := fun stage item => response.observe (residualOf stage) item
  Class := fun stage => response.Class (residualOf stage)
  classify := fun stage value => response.classify (residualOf stage) value
  exhaustive := fun _ _ => ⟨_, rfl⟩

private def responseRecipe
    (response : ResponseData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage where
  contract := sealPayload (liftResponse response).asContract
  certify := fun _ _ => none

private def liftCapacity (capacity : CapacityData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.CapacityLedger Stage where
  Item := fun stage => capacity.Item (residualOf stage)
  Class := fun stage => capacity.Class (residualOf stage)
  schedule :=  fun stage =>
    capacity.schedule (residualOf stage)
  classify := fun stage item => capacity.classify (residualOf stage) item
  contribution := fun stage item =>
    capacity.contribution (residualOf stage) item
  capacity := fun stage cls => capacity.capacity (residualOf stage) cls
  totalWithin := fun stage item =>
    capacity.totalWithin (residualOf stage) item

private def capacityRecipe
    (capacity : CapacityData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage where
  contract := sealPayload (liftCapacity capacity).asContract
  certify := fun _ _ => none

private def liftLocalization
    (localization : LocalizationData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.SupportLocalization Stage where
  Cell := fun stage => localization.Cell (residualOf stage)
  schedule :=  fun stage =>
    localization.schedule (residualOf stage)
  localBudget := fun stage cell =>
    localization.localBudget (residualOf stage) cell
  selected := fun stage => localization.selected (residualOf stage)
  selected_negative := fun stage =>
    localization.selected_negative (residualOf stage)

private def localizationRecipe
    (localization : LocalizationData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage where
  contract := sealPayload (liftLocalization localization).asContract
  certify := fun _ _ => none

private def liftRankBudget (rankBudget : RankBudgetData P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.RankBudgetSplit Stage where
  Rank := fun stage => rankBudget.rank (residualOf stage)
  Budget := fun stage => rankBudget.budget (residualOf stage)
  threshold := fun stage => rankBudget.threshold (residualOf stage)
  high := fun stage => rankBudget.high (residualOf stage)
  low := fun stage => rankBudget.low (residualOf stage)
  exhaustive := fun stage => rankBudget.exhaustive (residualOf stage)

private noncomputable def rankBudgetRecipe (rankBudget : RankBudgetData P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage where
  contract := sealPayload (liftRankBudget rankBudget).asContract
  certify := fun _ _ => none

private def liftClosedCode
    (closedCode : ClosedCodeData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.ClosedCodeExhaustion Stage where
  Code := fun stage => closedCode.Code (residualOf stage)
  schedule :=  fun stage =>
    closedCode.schedule (residualOf stage)
  targetCode := fun stage => closedCode.targetCode (residualOf stage)
  observedCode := fun stage code =>
    closedCode.observedCode (residualOf stage) code
  closed := fun stage => closedCode.closed (residualOf stage)

private def closedCodeRecipe
    (closedCode : ClosedCodeData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage where
  contract := sealPayload (liftClosedCode closedCode).asContract
  certify := fun _ _ => none

/-- The early-closure vertex: the registered target decision procedure
pulled back to the current stage.  Its certificate projection recognizes the
`.target` terminal payload, so `HaltingProgram.snoc` closes the run here. -/
private noncomputable def targetRecipe
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage :=
  let continuation : Strategy.TargetAvoidingContinuation Stage :=
    { Target := fun stage =>
        T.Predicate (residualOf stage : Strategy.ProblemInput P).object
      targetDecidable := fun stage => data.targetDecidable (residualOf stage) }
  { contract := sealPayload continuation.asContract
    certify := fun _ payload =>
      match payload with
      | ⟨.target, proof⟩ => some proof.down
      | ⟨.avoiding, _⟩ => none }

structure MinimalSelectionEvidence
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (previous : Stage) where
  context : MinimalCounterexampleContext P T.Predicate selection.progress

structure MinimalSelectionStage
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)] where
  ledger : Ledger.Extension Stage
    (fun previous => MinimalSelectionEvidence (T := T) selection previous)

private instance
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    HasResidual (MinimalSelectionStage (T := T) selection Stage)
      (Strategy.ProblemInput P) where
  residual selected :=
    let context := selected.ledger.added.context
    ⟨context.G, context.baseline, context.state⟩

/-- Exact selected-context query produced by the existing sealed selector.
Domain continuations consume this query; they cannot construct or replace
the selected context. -/
def MinimalSelectionStage.contextQuery
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Query (MinimalSelectionStage (T := T) selection Stage) fun _ =>
      MinimalCounterexampleContext P T.Predicate selection.progress :=
   fun selected => selected.ledger.added.context

/-! The selected ambient object is the active residual exposed by the sealed
minimal-counterexample selector. Consumers use this query instead of
traversing the extension ledger or rebuilding the selection output. -/
def MinimalSelectionStage.activeResidualQuery
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Query (MinimalSelectionStage (T := T) selection Stage) fun _ => P.Ambient :=
  (MinimalSelectionStage.contextQuery (T := T) selection).map
    (fun _ context => context.G)

@[simp] theorem MinimalSelectionStage.contextQuery_read
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (selected : MinimalSelectionStage (T := T) selection Stage) :
    (MinimalSelectionStage.contextQuery (T := T) selection) selected =
      selected.ledger.added.context :=
  rfl

@[simp] theorem MinimalSelectionStage.activeResidualQuery_read
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (selected : MinimalSelectionStage (T := T) selection Stage) :
    (MinimalSelectionStage.activeResidualQuery (T := T) selection) selected =
      selected.ledger.added.context.G :=
  rfl

private noncomputable def selectedMinimalStage
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (stateOf : (G : P.Ambient) -> P.BranchState G)
    (stage : Stage)
    (avoids : ¬ T.Predicate (residualOf stage).object) :
    MinimalSelectionStage (T := T) selection Stage :=
  let input := residualOf stage
  let initial : AvoidingContext P T.Predicate :=
    AvoidingContext.ofBranch
      { G := input.object, baseline := input.baseline,
        state := input.branchState } avoids
  let context := Classical.choice
    (initial.exists_minimalCounterexample selection.progress stateOf)
  let selectionNode :
      Residual.StageNode Stage
        (fun previous =>
          MinimalSelectionEvidence (T := T) selection previous) :=
    Residual.StageNode.create (fun _ => { context })
  ⟨selectionNode.run stage⟩

private theorem MinimalSelectionStage.avoids
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (selected : MinimalSelectionStage (T := T) selection Stage) :
    ¬ T.Predicate (residualOf selected).object := by
  exact selected.ledger.added.context.avoids

/-- Decide the target on the current residual.  The target arm certifies it;
the avoiding arm appends a context that is minimal for the registered
well-founded progress relation and runs the continuation on that context. -/
private noncomputable def minimalCounterexampleRecipe
    (selection : MinimalCounterexampleSelectionData.{uAmbient, uBranch, uData} P)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (targetDecidable : (input : Strategy.ProblemInput P) ->
      Decidable (T.Predicate input.object))
    (stateOf : (G : P.Ambient) -> P.BranchState G)
    (continuation :
      Recipe P T (MinimalSelectionStage (T := T) selection Stage)) :
    Recipe P T Stage :=
  let Selected := MinimalSelectionStage (T := T) selection Stage
  let targetDecision : Strategy.TargetAvoidingContinuation Stage :=
    { Target := fun stage =>
        T.Predicate (residualOf stage : Strategy.ProblemInput P).object
      targetDecidable := fun stage => targetDecidable (residualOf stage) }
  let targetDecisionContract := targetDecision.asContract
  let Payload : Stage -> Strategy.TargetAvoidingTerminal ->
      Type (max uAmbient uBranch uData)
    | stage, _ =>
      Sum
        (ULift.{max uAmbient uBranch uData}
          (PLift (T.Predicate (residualOf stage).object)))
        (Sigma fun selected : Selected =>
          Sigma (continuation.contract.Payload selected))
  let produce : (stage : Stage) -> Sigma (Payload stage) := fun stage =>
    match targetDecisionContract.produce stage with
    | ⟨.target, proof⟩ => ⟨.target, .inl (ULift.up proof)⟩
    | ⟨.avoiding, avoids⟩ =>
        let selected :=
          selectedMinimalStage selection stateOf stage avoids.down
        ⟨.avoiding, .inr ⟨selected, continuation.contract.produce selected⟩⟩
  let contract : Contract Stage :=
    { Terminal := Strategy.TargetAvoidingTerminal
      Payload
      produce
      exhaustive := fun stage => ⟨produce stage⟩ }
  let certify := fun stage (payload : Sigma (contract.Payload stage)) =>
    match payload.2 with
    | .inl proof => some ⟨proof.down.down⟩
    | .inr selected =>
        match continuation.certify selected.fst selected.snd with
        | none => none
        | some proof =>
            some ⟨False.elim (selected.fst.avoids selection proof.down)⟩
  let closes :=
    match continuation.closes with
    | none => none
    | some closed =>
        some ⟨by
          intro stage payload
          rcases payload with ⟨terminal, payload⟩
          cases payload with
          | inl target =>
              exact ⟨⟨target.down.down⟩, by simp [certify]⟩
          | inr selected =>
              obtain ⟨proof, certified⟩ :=
                closed.down selected.fst selected.snd
              exact ⟨⟨False.elim
                (selected.fst.avoids selection proof.down)⟩, by
                  simp [certify, certified]⟩⟩
  { contract, certify, closes }

/-! ## Sequential and routed recipe composition -/

/-- Reify two dependent vertices through Core's certified live-composition
boundary.  The second vertex is pulled back along the canonical
`LiveExtension.toLedger` projection and therefore executes only when the
first vertex did not certify the target. -/
private def composeRecipe {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (first : Recipe P T Stage)
    (second : Recipe P T
      (HaltingProgram.LiveExtension T Stage first.contract first.certify)) :
    Recipe P T Stage :=
  let Live :=
    HaltingProgram.LiveExtension T Stage first.contract first.certify
  let composition :=
    HaltingProgram.composeLiveContracts first.contract first.certify
      second.contract second.certify
  let contract := composition.contract
  let certify := composition.certify
  let closes : Option (PLift (
      ∀ stage payload, ∃ proof, certify stage payload = some proof)) :=
    match first.closes, second.closes with
    | some closesFirst, _ =>
        some ⟨by
          intro stage payload
          rcases payload with ⟨_, closed | continued⟩
          · exact ⟨closed.proof, rfl⟩
          · obtain ⟨proof, certified⟩ :=
              closesFirst.down continued.stage.previous.previous
                continued.stage.previous.added
            have impossible :
                first.certify continued.stage.previous.previous
                  continued.stage.previous.added = none :=
              continued.stage.previous.isLive
            exact False.elim (by simp [certified] at impossible)⟩
    | none, some closesSecond =>
        some ⟨by
          intro stage payload
          rcases payload with ⟨_, closed | continued⟩
          · exact ⟨closed.proof, rfl⟩
          · obtain ⟨_proof, certified⟩ :=
              closesSecond.down continued.stage.previous
                continued.stage.added
            let proof : PLift (T.Predicate (residualOf stage).object) :=
              ⟨by
                have target := _proof.down
                have residual_eq :
                    residualOf continued.stage.previous =
                      residualOf stage := by
                  change residualOf continued.stage.previous.previous =
                    residualOf stage
                  rw [continued.previous_eq]
                rw [residual_eq] at target
                exact target⟩
            refine ⟨proof, ?_⟩
            simp [certify, composition,
              HaltingProgram.composeLiveContracts, certified]⟩
    | none, none => none
  { contract, certify, closes }

/-- The payload of one dichotomy side: the branch witness alone for an empty
continuation, or the witness paired with the continuation's literal product.
No filler value is ever manufactured. -/
private def sideType {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (Witness : Stage -> Type (max uAmbient uBranch uData)) :
    Option (Recipe P T (Ledger.Extension Stage Witness)) ->
      Stage -> Type (max uAmbient uBranch uData)
  | none, stage => Witness stage
  | some recipe, stage =>
      Sigma fun witness : Witness stage =>
        Sigma (recipe.contract.Payload (Ledger.extend stage witness))

private def sideProduce {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (Witness : Stage -> Type (max uAmbient uBranch uData)) :
    (branch : Option (Recipe P T (Ledger.Extension Stage Witness))) ->
      (stage : Stage) ->
      Witness stage -> sideType Witness branch stage
  | none, _, witness => witness
  | some recipe, stage, witness =>
      let branchStage := Ledger.extend stage witness
      ⟨witness, recipe.contract.produce branchStage⟩

private def sideCertify {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (Witness : Stage -> Type (max uAmbient uBranch uData)) :
    (branch : Option (Recipe P T (Ledger.Extension Stage Witness))) ->
      (stage : Stage) ->
      sideType Witness branch stage ->
      Option (PLift (T.Predicate
        (residualOf stage : Strategy.ProblemInput P).object))
  | none, _, _ => none
  | some recipe, stage, payload =>
      recipe.certify (Ledger.extend stage payload.fst) payload.snd

/-- The branch witness retained inside one side's payload. -/
private def sideWitness {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (Witness : Stage -> Type (max uAmbient uBranch uData)) :
    (branch : Option (Recipe P T (Ledger.Extension Stage Witness))) ->
      (stage : Stage) ->
      sideType Witness branch stage -> Witness stage
  | none, _, witness => witness
  | some _, _, payload => payload.fst

private def sideCertificate
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (Witness : Stage -> Type (max uAmbient uBranch uData))
    (direct : Option (∀ stage, Witness stage ->
      PLift (T.Predicate
        (residualOf stage : Strategy.ProblemInput P).object)))
    (branch : Option (Recipe P T (Ledger.Extension Stage Witness)))
    (stage : Stage) (payload : sideType Witness branch stage) :
    Option (PLift (T.Predicate
      (residualOf stage : Strategy.ProblemInput P).object)) :=
  match direct with
  | some close => some (close stage (sideWitness Witness branch stage payload))
  | none => sideCertify Witness branch stage payload

private def sideCloses
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (Witness : Stage -> Type (max uAmbient uBranch uData))
    (direct : Option (∀ stage, Witness stage ->
      PLift (T.Predicate
        (residualOf stage : Strategy.ProblemInput P).object)))
    (branch : Option (Recipe P T (Ledger.Extension Stage Witness))) :
    Option (PLift (∀ stage payload, ∃ proof,
      sideCertificate Witness direct branch stage payload = some proof)) :=
  match direct with
  | some close =>
      some ⟨by
        intro stage payload
        exact ⟨close stage (sideWitness Witness branch stage payload), rfl⟩⟩
  | none =>
      match branch with
      | none => none
      | some recipe =>
          match recipe.closes with
          | none => none
          | some closes =>
              some ⟨by
                intro stage payload
                obtain ⟨proof, certified⟩ :=
                  closes.down (Ledger.extend stage payload.fst) payload.snd
                exact ⟨proof, by
                  simp [sideCertificate, sideCertify, certified]⟩⟩

/-- The selected left witness appended to the literal incoming stage before
the left continuation is instantiated. -/
private abbrev LeftBranchStage
    (split : DichotomyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)] :=
  Ledger.Extension Stage (fun stage =>
    ULift.{max uAmbient uBranch uData}
      (split.LeftPayload (residualOf stage)))

/-- The selected right witness appended to the literal incoming stage before
the right continuation is instantiated. -/
private abbrev RightBranchStage
    (split : DichotomyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)] :=
  Ledger.Extension Stage (fun stage =>
    ULift.{max uAmbient uBranch uData}
      (split.RightPayload (residualOf stage)))

/-- Core's single lowering for a stage-indexed dichotomy.  Specialized
Strategy families provide only the dichotomy and optional direct target
closures; branch execution, joins, and certification are shared here. -/
private def routedDichotomyRecipe
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (split : Strategy.Dichotomy.{
      max uAmbient uBranch uData,
      max uAmbient uBranch uData,
      max uAmbient uBranch uData} Stage)
    (leftDirect : Option (∀ stage, split.LeftPayload stage ->
      PLift (T.Predicate
        (residualOf stage : Strategy.ProblemInput P).object)))
    (rightDirect : Option (∀ stage, split.RightPayload stage ->
      PLift (T.Predicate
        (residualOf stage : Strategy.ProblemInput P).object)))
    (left : Option (Recipe P T
      (Ledger.Extension Stage split.LeftPayload)))
    (right : Option (Recipe P T
      (Ledger.Extension Stage split.RightPayload))) :
    Recipe P T Stage :=
  let LeftWitness := split.LeftPayload
  let RightWitness := split.RightPayload
  let produce :
      (stage : Stage) →
        Sigma fun terminal : Strategy.DichotomyTerminal =>
          Sum (sideType LeftWitness left stage)
            (sideType RightWitness right stage) :=
    fun stage =>
      match split.classify stage with
      | Sum.inl witness =>
          ⟨.left, Sum.inl
            (sideProduce LeftWitness left stage witness)⟩
      | Sum.inr witness =>
          ⟨.right, Sum.inr
            (sideProduce RightWitness right stage witness)⟩
  let contract : Contract Stage :=
    { Terminal := Strategy.DichotomyTerminal
      Payload := fun stage _ =>
        Sum (sideType LeftWitness left stage)
          (sideType RightWitness right stage)
      produce := produce
      exhaustive := fun stage => ⟨produce stage⟩ }
  let certify := fun stage (payload : Sigma (contract.Payload stage)) =>
    match payload.snd with
    | Sum.inl leftPayload =>
        sideCertificate LeftWitness leftDirect left stage leftPayload
    | Sum.inr rightPayload =>
        sideCertificate RightWitness rightDirect right stage rightPayload
  let closes : Option (PLift (
      ∀ stage payload, ∃ proof, certify stage payload = some proof)) :=
    match sideCloses LeftWitness leftDirect left,
        sideCloses RightWitness rightDirect right with
    | some closesLeft, some closesRight =>
        some ⟨by
          intro stage payload
          rcases payload with ⟨terminal, payload⟩
          cases payload with
          | inl leftPayload =>
              obtain ⟨proof, certified⟩ :=
                closesLeft.down stage leftPayload
              exact ⟨proof, by
                simpa [certify] using certified⟩
          | inr rightPayload =>
              obtain ⟨proof, certified⟩ :=
                closesRight.down stage rightPayload
              exact ⟨proof, by
                simpa [certify] using certified⟩⟩
    | _, _ => none
  { contract, certify, closes }

/-- Registered problem-level dichotomies are reindexed through the stable
residual and delegated to Core's stage-indexed router. -/
private def routedRecipe
    (split : DichotomyData.{uAmbient, uBranch, uData} P T)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (left : Option (Recipe P T (LeftBranchStage split Stage)))
    (right : Option (Recipe P T (RightBranchStage split Stage))) :
    Recipe P T Stage :=
  let routed : Strategy.Dichotomy.{
      max uAmbient uBranch uData,
      max uAmbient uBranch uData,
      max uAmbient uBranch uData} Stage :=
    { LeftPayload := fun stage =>
        ULift.{max uAmbient uBranch uData}
          (split.LeftPayload (residualOf stage))
      RightPayload := fun stage =>
        ULift.{max uAmbient uBranch uData}
          (split.RightPayload (residualOf stage))
      classify := fun stage =>
        match split.classify (residualOf stage) with
        | .inl witness => .inl (ULift.up witness)
        | .inr witness => .inr (ULift.up witness) }
  let leftDirect := split.closeLeft.map fun close stage witness =>
    ⟨close.down (residualOf stage) witness.down⟩
  let rightDirect := split.closeRight.map fun close stage witness =>
    ⟨close.down (residualOf stage) witness.down⟩
  routedDichotomyRecipe routed leftDirect rightDirect left right

/-- Lower an exhaustive finite typed terminal family.  Runtime routing is a
total function on `Fin arity`; the selected continuation is therefore
obtained by proof-indexing, never by an option-valued dispatch. -/
private noncomputable def finiteFamilyRecipe
    (family : FiniteTerminalFamilyData.{uAmbient, uBranch, uData} P T)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (branches : (terminal : Fin family.arity) ->
      Recipe P T (Ledger.Extension Stage (fun stage =>
        ULift.{max uAmbient uBranch uData}
          (family.Payload (residualOf stage) terminal)))) :
    Recipe P T Stage :=
  let Witness := fun (stage : Stage) (terminal : Fin family.arity) =>
    ULift.{max uAmbient uBranch uData}
      (family.Payload (residualOf stage) terminal)
  let contract : Contract Stage :=
    { Terminal := Fin family.arity
      Payload := fun stage terminal =>
        sideType (fun stage => Witness stage terminal)
          (some (branches terminal)) stage
      produce := fun stage =>
        let result := family.classify (residualOf stage)
        ⟨result.fst,
          sideProduce (fun stage => Witness stage result.fst)
            (some (branches result.fst)) stage (ULift.up result.snd)⟩
      exhaustive := fun stage =>
        let result := family.classify (residualOf stage)
        ⟨⟨result.fst,
          sideProduce (fun stage => Witness stage result.fst)
            (some (branches result.fst)) stage (ULift.up result.snd)⟩⟩ }
  let certify := fun stage (payload : Sigma (contract.Payload stage)) =>
    sideCertify (fun stage => Witness stage payload.fst)
      (some (branches payload.fst)) stage payload.snd
  letI : Decidable (∀ terminal, ∃ proof,
      (branches terminal).closes = some proof) :=
    Classical.propDecidable _
  let closes : Option (PLift (
      ∀ stage payload, ∃ proof, certify stage payload = some proof)) :=
    if closed : ∀ terminal, ∃ proof,
        (branches terminal).closes = some proof then
      some ⟨by
        intro stage payload
        rcases payload with ⟨terminal, payload⟩
        obtain ⟨closedProof, _recipeClosed⟩ := closed terminal
        obtain ⟨proof, certified⟩ :=
          closedProof.down (Ledger.extend stage payload.fst) payload.snd
        exact ⟨proof, by
          simpa [certify, sideCertify] using certified⟩⟩
    else none
  { contract, certify, closes }

/-! ## Key resolution and blueprint fragments -/

/-- Sealed lowering of the CT1 obstruction-free/canonical-packing strategy.
The payload is the strategy's literal accumulated ledger output. -/
private noncomputable def obstructionPackingRecipe
    (semantics : Core.Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage).object) : Recipe P T Stage :=
  let profile :
      Core.Strategy.ObstructionPackingClosure.Profile.{
        uAmbient, uBranch, uData} (P := P) (T := T) :=
    semantics
  {
    contract := sealPayload (profile.contractAt (Previous := Stage) current)
    certify := fun stage payload =>
      match payload.snd.down with
      | Sum.inl _ => none
      | Sum.inr target => some ⟨(targetToRoot stage) target.down⟩
  }

/-- Sealed lowering of the literal CT9→CT16 composition.  Registration is
lifted to the current stage exclusively through the stable residual query. -/
private noncomputable def exactFiniteLocalAlgebraRecipe
    (registration : Core.Strategy.ExactFiniteLocalAlgebra.Registration.{
      max uAmbient uBranch, uData, uData, uData}
      (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] : Recipe P T Stage :=
  let profile :
      Core.Strategy.ExactFiniteLocalAlgebra.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData, uData, uData}
        Stage (Strategy.ProblemInput P) :=
    Core.Strategy.ExactFiniteLocalAlgebra.Profile.ofRegistration
      (Previous := Stage) registration
  {
    contract := profile.execution.toContract
    certify := fun _ _ => none
  }

private noncomputable def exactFiniteLocalCodeQuery
    (registration : Core.Strategy.ExactFiniteLocalAlgebra.Registration.{
      max uAmbient uBranch, uData, uData, uData}
      (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    let recipe := exactFiniteLocalAlgebraRecipe (T := T) registration
      (Stage := Stage)
    Query (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (fun _ => List Bool) := by
  let profile := Core.Strategy.ExactFiniteLocalAlgebra.Profile.ofRegistration
    (Previous := Stage) registration
  let recipe := exactFiniteLocalAlgebraRecipe (T := T) registration
    (Stage := Stage)
  let Live := HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  let latest : Query Live
      (fun live => Sigma (recipe.contract.Payload live.previous)) :=
    (Query.latest (Previous := Stage)
      (Added := fun stage => Sigma (recipe.contract.Payload stage))).comap
      (fun live : Live => live.toLedger)
  exact latest.map fun _ payload => profile.codeOfExecution payload.snd

/-- Sealed lowering of the residual-owned finite barrier enumeration.
Core filters the complete candidate schedule and runs CT16 on the literal
incoming stage; no stored count or application outcome enters execution. -/
private noncomputable def finiteBarrierEnumerationRecipe
    (registration :
      Core.Strategy.FiniteBarrierEnumeration.Registration.{
        max uAmbient uBranch, uData} (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (sourceCode : Query Stage fun _ => List Bool)
    (current : Query Stage fun _ => Strategy.ProblemInput P) :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.FiniteBarrierEnumeration.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration := registration, sourceCode := sourceCode, current := current }
  {
    contract := profile.execution.toContract
    certify := fun _ _ => none
  }

/-! ### Compiler-owned typed capabilities

The compiler transports only typed `Query` values.  A capability key names
the result type of an existing framework Strategy; it does not name a domain,
a proof, an execution result, or a prescribed Strategy order.  Requirements
and productions are uniform effects of sealed Strategy keys, so the same
inference works for every sequential or branched DAG. -/

private def CapabilityKey.Result
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (data : StrategyData.{uAmbient, uBranch, uData} P T) : CapabilityKey → Type
  | .closed => Core.Residual.ClosureEvidence
  | .obstructionPacking _ => Unit
  | .exactFiniteLocalCode => List Bool
  | .finiteBarrierSummary =>
      Core.Strategy.FiniteBarrierEnumeration.Summary
  | .normalizedSupportLedger _ =>
      Core.Strategy.SupportComplementNormalization.Summary
  | .boundaryAccountingLedger =>
      Core.Strategy.BoundaryDemandAccounting.Summary
  | .localSupplyLedger _ =>
      Core.Strategy.LocalSupplyLowerBound.Summary
  | .targetRankDrop
  | .fullRankExactCode => Unit
  | .fullRankCertificate =>
      Core.Strategy.TargetRelativeRankDichotomy.FullRankCertificate
  | .independentRank => Nat
  | .finiteStateCapacityContinuation => Unit
  | .finiteDensityOverflow => Unit
  | .finiteDensityCap => Unit
  | .minimalContext => Unit
  | .minimalClosureAt _ => Unit
  | .canonicalPairDependence _ => CT15.Terminal
  | .canonicalPairRole _ => CT9.Terminal
  | .canonicalCapacityAssignment _ => CT4.Terminal
  | .canonicalCapacityFibre _ => CT9.Terminal
  | .canonicalCapacityAggregate _ => CT14.Terminal
  | .homogeneousPressureOverload _ => CT9.Terminal
  | .homogeneousPressureReconciliation _ => CT13.Terminal
  | .homogeneousPressureAggregate _ => CT14.Terminal
  | .bottleneckCollision _ => CT9.Terminal
  | .bottleneckPressure _ => CT14.Terminal
  | .bottleneckClassification _ => CT10.Terminal
  | .bottleneckSeparator _ => CT6.Terminal
  | .homogeneousHandoff _ => Unit
  | .nearCubicSpine _ => Unit

/-- Exact dependent rank-drop capability retained on the literal left branch.
The profile owns all CT9/CT10/CT15/CT16 queries used to construct the result;
the result is the private CT payload produced at this same stage. -/
private structure TargetRankDropCapability
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (input : Strategy.ProblemInput P) where
  Source : Type (max uAmbient uBranch uData)
  sourceHasResidual : HasResidual Source (Strategy.ProblemInput P)
  source : Source
  source_residual_eq : @residualOf Source (Strategy.ProblemInput P)
    sourceHasResidual source = input
  profile : Core.Strategy.TargetRelativeRankDichotomy.Profile.{
    max uAmbient uBranch uData, max uAmbient uBranch, uData, uData, uData,
    uData, uData, uData,
    max uAmbient uBranch uData, max uAmbient uBranch uData,
    max uAmbient uBranch uData}
    Source (Strategy.ProblemInput P)
  result : profile.code.RankDropResidual source

/-- Provenance-bearing normalized-support capability.  The input query is
the exact graph query consumed by CT9, retained together with CT9--CT6's
literal structural ledger. -/
private structure NormalizedSupportCapability
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (index : Fin data.supportComplementNormalizations.length)
    (Stage : Type uStage) [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) where
  exact : Core.Strategy.SupportComplementNormalization.ExactLedger.{
    max uAmbient uBranch, uStage, max uAmbient uBranch uData,
    max uAmbient uBranch uData}
    Stage (Strategy.ProblemInput P)
    (fun stage =>
      data.supportComplementNormalizations[index].snd.AmbientItem
        (current stage))
  densityCap : Core.Strategy.FiniteDensityBudget.CapLedger Stage

/-- Provenance-bearing CT14 capability.  It retains the normalized support
consumed by the local-supply execution, so CT15 receives the very same input
query and never has to equate independently reconstructed carriers. -/
private structure LocalSupplyCapability
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (index : Fin data.localSupplyLowerBounds.length)
    (Stage : Type uStage) [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) where
  normalized : Core.Strategy.SupportComplementNormalization.ExactLedger.{
    max uAmbient uBranch, uStage, max uAmbient uBranch uData,
    max uAmbient uBranch uData}
    Stage (Strategy.ProblemInput P)
    (fun stage =>
      data.supportComplementNormalizations[
        data.boundaryDemandAccountings[
          data.localSupplyLowerBounds[index].fst].fst].snd.AmbientItem
        (current stage))
  exact : Core.Strategy.LocalSupplyLowerBound.ExactLedger.{
    uStage, max uAmbient uBranch, uData}
    Stage (Strategy.ProblemInput P)
    (fun stage => data.localSupplyLowerBounds[index].snd.Member
      (current stage))

/-- Producer-owned coupled-pressure ledger together with its exact selected
fibre reindexed by the compiler's one current-input query. -/
private structure HomogeneousPressureOverloadCapability
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (index : Fin data.coupledHomogeneousFibrePressures.length)
    (Stage : Type uStage) [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) where
  ledger : Core.Strategy.CoupledHomogeneousFibrePressure.OverloadLedger
    Stage (Strategy.ProblemInput P)
    data.coupledHomogeneousFibrePressures[index]
  current_eq : ∀ stage, ledger.current stage = current stage

/-- Producer-owned CT6 separator ledger and the exact selected separator
indexed by the same compiler current-input query. -/
private structure BottleneckSeparatorCapability
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (index : Fin data.finiteBottleneckClassifications.length)
    (Stage : Type uStage) [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) where
  ledger : Core.Strategy.FiniteBottleneckClassification.SeparatorLedger
    Stage (Strategy.ProblemInput P)
    data.finiteBottleneckClassifications[index].snd
  current_eq : ∀ stage, ledger.current stage = current stage

/-! ### Canonical compiler ledger domain

The compiler changes dependent execution-stage types while it composes
contracts.  `CapabilityCursor` packages that type and its two residual views
as the residual indexed by the one canonical `Core.Residual.ExactLedger`.
Facts below are one-key payloads; there is no aggregate capability store.
-/

private structure CapabilityCursor
    (data : StrategyData.{uAmbient, uBranch, uData} P T) where
  Stage : Type (max uAmbient uBranch uData)
  stageResidual : HasResidual Stage (Strategy.ProblemInput P)
  activeInput : Query Stage fun _ => Strategy.ProblemInput P
  targetToRoot : Query Stage fun stage =>
    T.Predicate (activeInput stage).object →
      T.Predicate (@residualOf Stage (Strategy.ProblemInput P)
        stageResidual stage).object

/-- Stage-indexed compiler state.  The stage and its canonical residual
instance are parameters, so dependent contract composition never needs to
cast an existential cursor or accept an alternative residual implementation. -/
private structure CapabilityState
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [stageResidual : HasResidual Stage (Strategy.ProblemInput P)] where
  activeInput : Query Stage fun _ => Strategy.ProblemInput P
  targetToRoot : Query Stage fun stage =>
    T.Predicate (activeInput stage).object →
      T.Predicate (residualOf stage).object

private def CapabilityState.toCursor
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [stageResidual : HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage) : CapabilityCursor data where
  Stage := Stage
  stageResidual := stageResidual
  activeInput := state.activeInput
  targetToRoot := state.targetToRoot

private structure CapabilityProjection
    (new old : CapabilityCursor data) where
  project : new.Stage → old.Stage
  residual_eq : ∀ stage,
    @residualOf new.Stage (Strategy.ProblemInput P) new.stageResidual stage =
      @residualOf old.Stage (Strategy.ProblemInput P) old.stageResidual
        (project stage)
  active_eq : ∀ stage,
    new.activeInput stage = old.activeInput (project stage)

private instance capabilityCursorHasResidual
    (cursor : CapabilityCursor data) :
    HasResidual cursor.Stage (Strategy.ProblemInput P) :=
  cursor.stageResidual

private instance capabilityRefinementSystem
    (data : StrategyData.{uAmbient, uBranch, uData} P T) :
    Core.Residual.RefinementSystem (CapabilityCursor data) where
  Subject := Unit
  subject := fun _ => ()
  Refines new old := Nonempty (CapabilityProjection new old)
  refl cursor := ⟨{
    project := id
    residual_eq := fun _ => rfl
    active_eq := fun _ => rfl
  }⟩
  trans newMiddle middleOld := by
    rcases newMiddle with ⟨newMiddle⟩
    rcases middleOld with ⟨middleOld⟩
    exact ⟨{
      project := middleOld.project ∘ newMiddle.project
      residual_eq := fun stage =>
        (newMiddle.residual_eq stage).trans
          (middleOld.residual_eq (newMiddle.project stage))
      active_eq := fun stage =>
        (newMiddle.active_eq stage).trans
          (middleOld.active_eq (newMiddle.project stage))
    }⟩
  subject_eq := fun _ => rfl

private structure ObstructionPackingFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  indexValid : index < data.obstructionPackingClosures.length
  packing : Query cursor.Stage fun stage =>
    Core.Strategy.ObstructionPackingClosure.NonemptyPacking
      ((data.obstructionPackingClosures[index]'indexValid).occurrences
        (cursor.activeInput stage))
      ((data.obstructionPackingClosures[index]'indexValid).conflict
        (cursor.activeInput stage))

private structure NormalizedSupportFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  indexValid : index < data.supportComplementNormalizations.length
  summary : Query cursor.Stage fun _ =>
    Core.Strategy.SupportComplementNormalization.Summary
  exact : @NormalizedSupportCapability P T data ⟨index, indexValid⟩
    cursor.Stage cursor.stageResidual cursor.activeInput

private structure LocalSupplyFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  indexValid : index < data.localSupplyLowerBounds.length
  summary : Query cursor.Stage fun _ =>
    Core.Strategy.LocalSupplyLowerBound.Summary
  exact : @LocalSupplyCapability P T data ⟨index, indexValid⟩
    cursor.Stage cursor.stageResidual cursor.activeInput

private structure HomogeneousPressureOverloadFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  indexValid : index < data.coupledHomogeneousFibrePressures.length
  terminal : Query cursor.Stage fun _ => CT9.Terminal
  exact : @HomogeneousPressureOverloadCapability P T data
    ⟨index, indexValid⟩ cursor.Stage cursor.stageResidual cursor.activeInput

private structure BottleneckSeparatorFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  indexValid : index < data.finiteBottleneckClassifications.length
  terminal : Query cursor.Stage fun _ => CT6.Terminal
  exact : @BottleneckSeparatorCapability P T data ⟨index, indexValid⟩
    cursor.Stage cursor.stageResidual cursor.activeInput

private structure MinimalClosureFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  indexValid : index < data.counterexampleReductions.length
  exact : Core.Strategy.InterfaceReplacement.ExactClosureQueries
    (data.counterexampleReductions[index]'indexValid).interfaceReplacement
      cursor.Stage
  activeObject : ∀ stage,
    (cursor.activeInput stage).object = (exact.context stage).G

private structure NearCubicFact
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) (index : Nat) where
  marker : Unit := ()
  indexValid : index < data.scaleThresholdDichotomies.length
  estimate : Query cursor.Stage fun stage =>
    (data.scaleThresholdDichotomies[index]'indexValid).load
        (cursor.activeInput stage) ≤
      ((data.scaleThresholdDichotomies[index]'indexValid).table
        (cursor.activeInput stage)).threshold
        ((data.scaleThresholdDichotomies[index]'indexValid).size
          (cursor.activeInput stage))

private def CapabilityPayload
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (cursor : CapabilityCursor data) : CapabilityKey →
      Type (max (uAmbient + 1) (uBranch + 1) (uData + 1))
  | .closed => ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
      Core.Residual.ClosureEvidence
  | .obstructionPacking index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (ObstructionPackingFact data cursor index)
  | .exactFiniteLocalCode =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => List Bool)
  | .finiteBarrierSummary =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Core.Strategy.FiniteBarrierEnumeration.RateLedger cursor.Stage)
  | .normalizedSupportLedger index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (NormalizedSupportFact data cursor index)
  | .boundaryAccountingLedger =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ =>
          Core.Strategy.BoundaryDemandAccounting.Summary)
  | .localSupplyLedger index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (LocalSupplyFact data cursor index)
  | .targetRankDrop =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun stage =>
          TargetRankDropCapability data
            (@residualOf cursor.Stage (Strategy.ProblemInput P)
              cursor.stageResidual stage))
  | .fullRankExactCode =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => Unit)
  | .fullRankCertificate =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ =>
          Core.Strategy.TargetRelativeRankDichotomy.FullRankCertificate)
  | .independentRank =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => Nat)
  | .finiteStateCapacityContinuation =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Core.Strategy.FiniteStateNetChargeContinuation.CapacityLedger
          cursor.Stage)
  | .finiteDensityOverflow =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Core.Strategy.ColdBranchAggregation.OverflowLedger cursor.Stage)
  | .finiteDensityCap =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Core.Strategy.FiniteDensityBudget.CapLedger cursor.Stage)
  | .minimalContext =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ =>
          Σ index : Fin data.counterexampleReductions.length,
            Core.MinimalCounterexampleContext P T.Predicate
              data.counterexampleReductions[index].selection.progress)
  | .minimalClosureAt index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (MinimalClosureFact data cursor index)
  | .canonicalPairDependence _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT15.Terminal)
  | .canonicalPairRole _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT9.Terminal)
  | .canonicalCapacityAssignment _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT4.Terminal)
  | .canonicalCapacityFibre _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT9.Terminal)
  | .canonicalCapacityAggregate _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT14.Terminal)
  | .homogeneousPressureOverload index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (HomogeneousPressureOverloadFact data cursor index)
  | .homogeneousPressureReconciliation _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT13.Terminal)
  | .homogeneousPressureAggregate _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT14.Terminal)
  | .bottleneckCollision _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT9.Terminal)
  | .bottleneckPressure _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT14.Terminal)
  | .bottleneckClassification _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => CT10.Terminal)
  | .bottleneckSeparator index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (BottleneckSeparatorFact data cursor index)
  | .homogeneousHandoff _ =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (Query cursor.Stage fun _ => Unit)
  | .nearCubicSpine index =>
      ULift.{max (uAmbient + 1) (uBranch + 1) (uData + 1)}
        (NearCubicFact data cursor index)

/-- One canonical fact value remembers the cursor where the fact was proved
and a refinement lineage from the active cursor to that origin.  Refinement
therefore updates only ancestry; it never copies, rewrites, or drops the
producer-owned payload. -/
private structure StoredCapability
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (key : CapabilityKey) (cursor : CapabilityCursor data) where
  origin : CapabilityCursor data
  payload : CapabilityPayload data origin key
  lineage : Core.Residual.RefinementSystem.Refines cursor origin

private def CapabilityKey.tag : CapabilityKey → Nat
  | .closed => 0
  | .obstructionPacking _ => 1
  | .exactFiniteLocalCode => 2
  | .finiteBarrierSummary => 3
  | .normalizedSupportLedger _ => 4
  | .boundaryAccountingLedger => 5
  | .localSupplyLedger _ => 6
  | .targetRankDrop => 7
  | .fullRankExactCode => 8
  | .fullRankCertificate => 9
  | .independentRank => 10
  | .finiteStateCapacityContinuation => 11
  | .finiteDensityOverflow => 12
  | .finiteDensityCap => 13
  | .minimalContext => 14
  | .minimalClosureAt _ => 15
  | .canonicalPairDependence _ => 16
  | .canonicalPairRole _ => 17
  | .canonicalCapacityAssignment _ => 18
  | .canonicalCapacityFibre _ => 19
  | .canonicalCapacityAggregate _ => 20
  | .homogeneousPressureOverload _ => 21
  | .homogeneousPressureReconciliation _ => 22
  | .homogeneousPressureAggregate _ => 23
  | .bottleneckCollision _ => 24
  | .bottleneckPressure _ => 25
  | .bottleneckClassification _ => 26
  | .bottleneckSeparator _ => 27
  | .homogeneousHandoff _ => 28
  | .nearCubicSpine _ => 29

private def CapabilityKey.index : CapabilityKey → Nat
  | .obstructionPacking index
  | .normalizedSupportLedger index
  | .localSupplyLedger index
  | .minimalClosureAt index
  | .canonicalPairDependence index
  | .canonicalPairRole index
  | .canonicalCapacityAssignment index
  | .canonicalCapacityFibre index
  | .canonicalCapacityAggregate index
  | .homogeneousPressureOverload index
  | .homogeneousPressureReconciliation index
  | .homogeneousPressureAggregate index
  | .bottleneckCollision index
  | .bottleneckPressure index
  | .bottleneckClassification index
  | .bottleneckSeparator index
  | .homogeneousHandoff index
  | .nearCubicSpine index => index
  | _ => 0

private def CapabilityKey.factName : CapabilityKey → Lean.Name
  | .closed => Core.Residual.closureFactName
  | key => .num (.num `Hypostructure.Core.Strategy.capability key.tag) key.index

private theorem CapabilityKey.factName_injective :
    Function.Injective CapabilityKey.factName := by
  intro left right equality
  cases left <;> cases right <;>
    simp_all [CapabilityKey.factName, CapabilityKey.tag, CapabilityKey.index,
      Core.Residual.closureFactName]

private noncomputable instance capabilityFactSystem
    (data : StrategyData.{uAmbient, uBranch, uData} P T) :
    Core.Residual.FactSystem (CapabilityCursor data) where
  Key := CapabilityKey
  keyDecidableEq := inferInstance
  name := CapabilityKey.factName
  name_injective := CapabilityKey.factName_injective
  Value key cursor := StoredCapability data key cursor
  transport refinement stored :=
    { origin := stored.origin
      payload := stored.payload
      lineage := Core.Residual.RefinementSystem.trans refinement stored.lineage }
  transport_refl := by
    intro _ _ stored
    cases stored
    congr
  transport_trans := by
    intro _ _ _ _ _ _ stored
    cases stored
    congr
  closureKey := .closed
  closure_name := rfl
  closureValue cursor evidence :=
    { origin := cursor
      payload := ⟨evidence⟩
      lineage := Core.Residual.RefinementSystem.refl cursor }
  closureEvidence _ stored := stored.payload.down

private noncomputable def CapabilityPayload.comap
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    {new old : CapabilityCursor data}
    (projection : CapabilityProjection new old) :
    (key : CapabilityKey) → CapabilityPayload data old key →
      CapabilityPayload data new key
  | .closed, payload => ⟨payload.down⟩
  | .obstructionPacking index, payload =>
      let fact := payload.down
      ⟨{
        indexValid := fact.indexValid
        packing := fun stage => by
          change Core.Strategy.ObstructionPackingClosure.NonemptyPacking
            ((data.obstructionPackingClosures[index]'fact.indexValid).occurrences
              (new.activeInput stage))
            ((data.obstructionPackingClosures[index]'fact.indexValid).conflict
              (new.activeInput stage))
          rw [projection.active_eq stage]
          exact fact.packing (projection.project stage)
      }⟩
  | .exactFiniteLocalCode, payload =>
      ⟨payload.down.comap projection.project⟩
  | .finiteBarrierSummary, payload =>
      ⟨payload.down.comap projection.project⟩
  | .normalizedSupportLedger _, payload =>
      let fact := payload.down
      let index : Fin data.supportComplementNormalizations.length :=
        ⟨_, fact.indexValid⟩
      let registration := data.supportComplementNormalizations[index].snd
      let exact := fact.exact
      ⟨{
        indexValid := fact.indexValid
        summary := fact.summary.comap projection.project
        exact := {
          exact := exact.exact.comapTo projection.project
            (fun stage => (projection.residual_eq stage).symm)
            (fun stage => registration.AmbientItem (new.activeInput stage))
            (fun stage => congrArg registration.AmbientItem
              (projection.active_eq stage).symm)
          densityCap := exact.densityCap.comap projection.project
        }
      }⟩
  | .boundaryAccountingLedger, payload =>
      ⟨payload.down.comap projection.project⟩
  | .localSupplyLedger _, payload =>
      let fact := payload.down
      let index : Fin data.localSupplyLowerBounds.length :=
        ⟨_, fact.indexValid⟩
      let registration := data.localSupplyLowerBounds[index].snd
      let supportIndex := data.boundaryDemandAccountings[
        data.localSupplyLowerBounds[index].fst].fst
      let supportRegistration :=
        data.supportComplementNormalizations[supportIndex].snd
      let exact := fact.exact
      ⟨{
        indexValid := fact.indexValid
        summary := fact.summary.comap projection.project
        exact := {
          normalized := exact.normalized.comapTo projection.project
            (fun stage => (projection.residual_eq stage).symm)
            (fun stage => supportRegistration.AmbientItem
              (new.activeInput stage))
            (fun stage => congrArg supportRegistration.AmbientItem
              (projection.active_eq stage).symm)
          exact := exact.exact.comapTo projection.project
            (fun stage => (projection.residual_eq stage).symm)
            (fun stage => registration.Member (new.activeInput stage))
            (fun stage => congrArg registration.Member
              (projection.active_eq stage).symm)
        }
      }⟩
  | .targetRankDrop, payload =>
      ⟨fun stage =>
        let capability := payload.down (projection.project stage)
        { Source := capability.Source
          sourceHasResidual := capability.sourceHasResidual
          source := capability.source
          source_residual_eq := capability.source_residual_eq.trans
            (projection.residual_eq stage).symm
          profile := capability.profile
          result := capability.result }⟩
  | .fullRankExactCode, payload =>
      ⟨payload.down.comap projection.project⟩
  | .fullRankCertificate, payload =>
      ⟨payload.down.comap projection.project⟩
  | .independentRank, payload =>
      ⟨payload.down.comap projection.project⟩
  | .finiteStateCapacityContinuation, payload =>
      ⟨payload.down.comap projection.project⟩
  | .finiteDensityOverflow, payload =>
      ⟨payload.down.comap projection.project⟩
  | .finiteDensityCap, payload =>
      ⟨payload.down.comap projection.project⟩
  | .minimalContext, payload =>
      ⟨payload.down.comap projection.project⟩
  | .minimalClosureAt index, payload =>
      let fact := payload.down
      let exact : Core.Strategy.InterfaceReplacement.ExactClosureQueries
          (data.counterexampleReductions[index]'fact.indexValid).interfaceReplacement
          new.Stage :=
        { context := fact.exact.context.comap projection.project
          closure := fact.exact.closure.comap projection.project }
      ⟨{
        indexValid := fact.indexValid
        exact := exact
        activeObject := fun stage => by
          rw [projection.active_eq stage]
          exact fact.activeObject (projection.project stage)
      }⟩
  | .canonicalPairDependence _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .canonicalPairRole _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .canonicalCapacityAssignment _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .canonicalCapacityFibre _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .canonicalCapacityAggregate _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .homogeneousPressureOverload _, payload =>
      let fact := payload.down
      let exact := fact.exact
      ⟨{
        indexValid := fact.indexValid
        terminal := fact.terminal.comap projection.project
        exact := {
          ledger := exact.ledger.comap projection.project new.activeInput
            (fun stage => (exact.current_eq (projection.project stage)).trans
              (projection.active_eq stage).symm)
          current_eq := fun _ => rfl
        }
      }⟩
  | .homogeneousPressureReconciliation _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .homogeneousPressureAggregate _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .bottleneckCollision _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .bottleneckPressure _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .bottleneckClassification _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .bottleneckSeparator _, payload =>
      let fact := payload.down
      let exact := fact.exact
      ⟨{
        indexValid := fact.indexValid
        terminal := fact.terminal.comap projection.project
        exact := {
          ledger := exact.ledger.comap projection.project new.activeInput
            (fun stage => (exact.current_eq (projection.project stage)).trans
              (projection.active_eq stage).symm)
          current_eq := fun _ => rfl
        }
      }⟩
  | .homogeneousHandoff _, payload =>
      ⟨payload.down.comap projection.project⟩
  | .nearCubicSpine _, payload =>
      let fact := payload.down
      ⟨{
        marker := ()
        indexValid := fact.indexValid
        estimate := fun stage => by
          simpa only [projection.active_eq stage] using
            fact.estimate (projection.project stage)
      }⟩

private noncomputable def StoredCapability.atCurrent
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {key : CapabilityKey} {cursor : CapabilityCursor data}
    (stored : StoredCapability data key cursor) :
    CapabilityPayload data cursor key :=
  CapabilityPayload.comap data (Classical.choice stored.lineage)
    key stored.payload

/-- The active object is an index of the canonical compiler ledger, never a
second value travelling beside it. -/
def _root_.Hypostructure.Core.Residual.ExactLedger.activeInput
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (_history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available) :=
  cursor.activeInput

def _root_.Hypostructure.Core.Residual.ExactLedger.targetToRoot
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (_history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available) :=
  cursor.targetToRoot

/-- Retrieve one compiler fact by semantic key.  Producer and execution order
are deliberately absent from this API. -/
noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.capability
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (key : CapabilityKey) (present : key ∈ available) :
    CapabilityPayload data cursor key :=
  (_root_.Hypostructure.Core.Residual.ExactLedger.getPresent history key present).atCurrent

/-- Scalar view of a semantic fact.  Structured producer facts are projected
from the same canonical value, never copied into a summary channel. -/
noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.query
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (key : CapabilityKey) (present : key ∈ available) :
    Query cursor.Stage fun _ => key.Result.{uAmbient, uBranch} data :=
  match key with
  | .closed => fun _ => (history.capability .closed present).down
  | .obstructionPacking _ => fun _ => ()
  | .exactFiniteLocalCode => (history.capability _ present).down
  | .finiteBarrierSummary => (history.capability _ present).down.summary
  | .normalizedSupportLedger _ => (history.capability _ present).down.summary
  | .boundaryAccountingLedger => (history.capability _ present).down
  | .localSupplyLedger _ => (history.capability _ present).down.summary
  | .targetRankDrop => fun _ => ()
  | .fullRankExactCode => (history.capability _ present).down
  | .fullRankCertificate => (history.capability _ present).down
  | .independentRank => (history.capability _ present).down
  | .finiteStateCapacityContinuation => fun _ => ()
  | .finiteDensityOverflow => fun _ => ()
  | .finiteDensityCap => fun _ => ()
  | .minimalContext => fun _ => ()
  | .minimalClosureAt _ => fun _ => ()
  | .canonicalPairDependence _ => (history.capability _ present).down
  | .canonicalPairRole _ => (history.capability _ present).down
  | .canonicalCapacityAssignment _ => (history.capability _ present).down
  | .canonicalCapacityFibre _ => (history.capability _ present).down
  | .canonicalCapacityAggregate _ => (history.capability _ present).down
  | .homogeneousPressureOverload _ =>
      (history.capability _ present).down.terminal
  | .homogeneousPressureReconciliation _ =>
      (history.capability _ present).down
  | .homogeneousPressureAggregate _ => (history.capability _ present).down
  | .bottleneckCollision _ => (history.capability _ present).down
  | .bottleneckPressure _ => (history.capability _ present).down
  | .bottleneckClassification _ => (history.capability _ present).down
  | .bottleneckSeparator _ =>
      (history.capability _ present).down.terminal
  | .homogeneousHandoff _ => (history.capability _ present).down
  | .nearCubicSpine _ => fun _ => ()

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.packingIndexValid
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Nat) (present : CapabilityKey.obstructionPacking index ∈ available) :
    index < data.obstructionPackingClosures.length :=
  (history.capability (.obstructionPacking index) present).down.indexValid

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.packingQuery
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.obstructionPackingClosures.length)
    (present : CapabilityKey.obstructionPacking index ∈ available) :
    Query cursor.Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.NonemptyPacking
        (data.obstructionPackingClosures[index].occurrences
          (cursor.activeInput stage))
        (data.obstructionPackingClosures[index].conflict
          (cursor.activeInput stage)) :=
  (history.capability (.obstructionPacking index) present).down.packing

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.packingCountQuery
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Nat) (present : CapabilityKey.obstructionPacking index ∈ available) :
    Query cursor.Stage fun _ => Nat :=
  let packingIndex : Fin data.obstructionPackingClosures.length :=
    ⟨index, history.packingIndexValid index present⟩
  (history.packingQuery packingIndex present).map fun _ packed =>
    packed.packing.selected.length

noncomputable def
    _root_.Hypostructure.Core.Residual.ExactLedger.homogeneousHandoffQuery
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.homogeneousBottlenecks.length)
    (_handoff : CapabilityKey.homogeneousHandoff index ∈ available)
    (overload : CapabilityKey.homogeneousPressureOverload
      data.homogeneousBottlenecks[index].pressureIndex ∈ available)
    (separator : CapabilityKey.bottleneckSeparator
      data.homogeneousBottlenecks[index].fst ∈ available) :
    Query cursor.Stage fun stage =>
      Core.Finite.Enumeration
        (data.homogeneousBottlenecks[index].HandoffSupport
          (cursor.activeInput stage)) :=
  fun stage =>
    let separatorCapability :=
      (history.capability
        (.bottleneckSeparator data.homogeneousBottlenecks[index].fst)
        separator).down.exact
    let overloadCapability :=
      (history.capability
        (.homogeneousPressureOverload
          data.homogeneousBottlenecks[index].pressureIndex)
        overload).down.exact
    let selected : Option
        (data.finiteBottleneckClassifications[
          data.homogeneousBottlenecks[index].fst].snd.SeparatorIndex
            (cursor.activeInput stage)) :=
      Eq.mp
        (congrArg
          (fun input => Option
            (data.finiteBottleneckClassifications[
              data.homogeneousBottlenecks[index].fst].snd.SeparatorIndex input))
          (separatorCapability.current_eq stage))
        (separatorCapability.ledger.selected stage)
    match selected with
    | some _ =>
        Eq.mp
          (congrArg
            (fun input => Core.Finite.Enumeration
              (data.homogeneousBottlenecks[index].HandoffSupport input))
            (overloadCapability.current_eq stage))
          (overloadCapability.ledger.selectedEnumeration stage)
    | none =>
        let registration := data.coupledHomogeneousFibrePressures[
          data.homogeneousBottlenecks[index].pressureIndex]
        letI : DecidableEq (registration.Item (cursor.activeInput stage)) :=
          (registration.items (cursor.activeInput stage)).decEq
        Core.Finite.Enumeration.empty _

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.capacityLedger
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (present : CapabilityKey.finiteStateCapacityContinuation ∈ available) :=
  (history.capability .finiteStateCapacityContinuation present).down

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.overflowLedger
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (present : CapabilityKey.finiteDensityOverflow ∈ available) :=
  (history.capability .finiteDensityOverflow present).down

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.capLedger
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (present : CapabilityKey.finiteDensityCap ∈ available) :=
  (history.capability .finiteDensityCap present).down

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.barrierRate
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (present : CapabilityKey.finiteBarrierSummary ∈ available) :=
  (history.capability .finiteBarrierSummary present).down

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.normalizedSupportExact
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.supportComplementNormalizations.length)
    (present : CapabilityKey.normalizedSupportLedger index ∈ available) :
    NormalizedSupportCapability data index cursor.Stage cursor.activeInput :=
  (history.capability (.normalizedSupportLedger index) present).down.exact

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.localSupplyExact
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.localSupplyLowerBounds.length)
    (present : CapabilityKey.localSupplyLedger index ∈ available) :
    LocalSupplyCapability data index cursor.Stage cursor.activeInput :=
  (history.capability (.localSupplyLedger index) present).down.exact

private noncomputable def
    _root_.Hypostructure.Core.Residual.ExactLedger.homogeneousPressureOverloadExact
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.coupledHomogeneousFibrePressures.length)
    (present : CapabilityKey.homogeneousPressureOverload index ∈ available) :
    HomogeneousPressureOverloadCapability data index cursor.Stage
      cursor.activeInput :=
  (history.capability (.homogeneousPressureOverload index) present).down.exact

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.bottleneckSeparatorExact
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.finiteBottleneckClassifications.length)
    (present : CapabilityKey.bottleneckSeparator index ∈ available) :
    BottleneckSeparatorCapability data index cursor.Stage cursor.activeInput :=
  (history.capability (.bottleneckSeparator index) present).down.exact

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.minimalContext
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (present : CapabilityKey.minimalContext ∈ available) :=
  (history.capability .minimalContext present).down

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.minimalClosureAt
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.counterexampleReductions.length)
    (present : CapabilityKey.minimalClosureAt index ∈ available) :
    Core.Strategy.InterfaceReplacement.ExactClosureQueries
      data.counterexampleReductions[index].interfaceReplacement cursor.Stage :=
  (history.capability (.minimalClosureAt index) present).down.exact

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.minimalClosureActiveObject
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.counterexampleReductions.length)
    (present : CapabilityKey.minimalClosureAt index ∈ available) :=
  (history.capability (.minimalClosureAt index) present).down.activeObject

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.targetRankDropExact
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (present : CapabilityKey.targetRankDrop ∈ available) :=
  (history.capability .targetRankDrop present).down

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.nearCubicIndexValid
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Nat) (present : CapabilityKey.nearCubicSpine index ∈ available) :=
  (history.capability (.nearCubicSpine index) present).down.indexValid

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.nearCubicSpine
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.scaleThresholdDichotomies.length)
    (present : CapabilityKey.nearCubicSpine index ∈ available) :
    Query cursor.Stage fun stage =>
      data.scaleThresholdDichotomies[index].load (cursor.activeInput stage) ≤
        (data.scaleThresholdDichotomies[index].table
          (cursor.activeInput stage)).threshold
          (data.scaleThresholdDichotomies[index].size
            (cursor.activeInput stage)) :=
  (history.capability (.nearCubicSpine index) present).down.estimate

/-- Append one semantic value to the one canonical history. -/
noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.publishCapability
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (key : CapabilityKey) (payload : CapabilityPayload data cursor key)
    (fresh : key ∉ available)
    (producer : Lean.Name := key.factName) :
    Core.Residual.ExactLedger (CapabilityCursor data) cursor
      (key :: available) :=
  _root_.Hypostructure.Core.Residual.ExactLedger.publishFact exactLedgerInternal% history key
    { origin := cursor
      payload := payload
      lineage := Core.Residual.RefinementSystem.refl cursor }
    fresh producer

/-- Generic scalar publication.  Structured facts have dedicated methods, so
they cannot be published from a summary with their exact witness omitted. -/
noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.cons
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (key : CapabilityKey)
    (query : Query cursor.Stage fun _ => key.Result.{uAmbient, uBranch} data)
    (notPacking : ∀ index : Nat, key ≠ .obstructionPacking index)
    (notCapacity : key ≠ .finiteStateCapacityContinuation)
    (notOverflow : key ≠ .finiteDensityOverflow)
    (notCap : key ≠ .finiteDensityCap := by intro equality; cases equality)
    (notBarrier : key ≠ .finiteBarrierSummary := by
      intro equality; cases equality)
    (notNormalized : ∀ index, key ≠ .normalizedSupportLedger index := by
      intro index equality; cases equality)
    (notLocalSupply : ∀ index, key ≠ .localSupplyLedger index := by
      intro index equality; cases equality)
    (notHomogeneousPressureOverload :
      ∀ index, key ≠ .homogeneousPressureOverload index := by
      intro index equality; cases equality)
    (notBottleneck : ∀ index, key ≠ .bottleneckSeparator index := by
      intro index equality; cases equality)
    (notMinimalContext : key ≠ .minimalContext := by
      intro equality; cases equality)
    (notMinimalClosureAt : ∀ index, key ≠ .minimalClosureAt index := by
      intro index equality; cases equality)
    (notTargetRankDrop : key ≠ .targetRankDrop := by
      intro equality; cases equality)
    (notNearCubic : ∀ index, key ≠ .nearCubicSpine index := by
      intro index equality; cases equality)
    (notClosed : key ≠ .closed := by intro equality; cases equality)
    (fresh : key ∉ available := by decide) :
    Core.Residual.ExactLedger (CapabilityCursor data) cursor
      (key :: available) :=
  history.publishCapability key (by
    cases key with
    | closed => exact (notClosed rfl).elim
    | obstructionPacking index => exact (notPacking index rfl).elim
    | exactFiniteLocalCode => exact ⟨query⟩
    | finiteBarrierSummary => exact (notBarrier rfl).elim
    | normalizedSupportLedger index => exact (notNormalized index rfl).elim
    | boundaryAccountingLedger => exact ⟨query⟩
    | localSupplyLedger index => exact (notLocalSupply index rfl).elim
    | targetRankDrop => exact (notTargetRankDrop rfl).elim
    | fullRankExactCode => exact ⟨query⟩
    | fullRankCertificate => exact ⟨query⟩
    | independentRank => exact ⟨query⟩
    | finiteStateCapacityContinuation => exact (notCapacity rfl).elim
    | finiteDensityOverflow => exact (notOverflow rfl).elim
    | finiteDensityCap => exact (notCap rfl).elim
    | minimalContext => exact (notMinimalContext rfl).elim
    | minimalClosureAt index => exact (notMinimalClosureAt index rfl).elim
    | canonicalPairDependence _ => exact ⟨query⟩
    | canonicalPairRole _ => exact ⟨query⟩
    | canonicalCapacityAssignment _ => exact ⟨query⟩
    | canonicalCapacityFibre _ => exact ⟨query⟩
    | canonicalCapacityAggregate _ => exact ⟨query⟩
    | homogeneousPressureOverload index =>
        exact (notHomogeneousPressureOverload index rfl).elim
    | homogeneousPressureReconciliation _ => exact ⟨query⟩
    | homogeneousPressureAggregate _ => exact ⟨query⟩
    | bottleneckCollision _ => exact ⟨query⟩
    | bottleneckPressure _ => exact ⟨query⟩
    | bottleneckClassification _ => exact ⟨query⟩
    | bottleneckSeparator index => exact (notBottleneck index rfl).elim
    | homogeneousHandoff _ => exact ⟨query⟩
    | nearCubicSpine index => exact (notNearCubic index rfl).elim)
    fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consTargetRankDrop
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (exact : Query cursor.Stage fun stage =>
      TargetRankDropCapability data (residualOf stage))
    (fresh : CapabilityKey.targetRankDrop ∉ available := by decide) :=
  history.publishCapability .targetRankDrop ⟨exact⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consCapacity
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (value : Core.Strategy.FiniteStateNetChargeContinuation.CapacityLedger
      cursor.Stage)
    (fresh : CapabilityKey.finiteStateCapacityContinuation ∉ available := by
      decide) :=
  history.publishCapability .finiteStateCapacityContinuation ⟨value⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consOverflow
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (value : Core.Strategy.ColdBranchAggregation.OverflowLedger cursor.Stage)
    (fresh : CapabilityKey.finiteDensityOverflow ∉ available := by decide) :=
  history.publishCapability .finiteDensityOverflow ⟨value⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consCap
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (value : Core.Strategy.FiniteDensityBudget.CapLedger cursor.Stage)
    (fresh : CapabilityKey.finiteDensityCap ∉ available := by decide) :=
  history.publishCapability .finiteDensityCap ⟨value⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consNearCubicSpine
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.scaleThresholdDichotomies.length)
    (spine : Query cursor.Stage fun stage =>
      data.scaleThresholdDichotomies[index].load (cursor.activeInput stage) ≤
        (data.scaleThresholdDichotomies[index].table
          (cursor.activeInput stage)).threshold
          (data.scaleThresholdDichotomies[index].size
            (cursor.activeInput stage)))
    (fresh : CapabilityKey.nearCubicSpine index ∉ available := by decide) :=
  history.publishCapability (.nearCubicSpine index)
    ⟨{ indexValid := index.isLt, estimate := spine }⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consBarrierRate
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (value : Core.Strategy.FiniteBarrierEnumeration.RateLedger cursor.Stage)
    (fresh : CapabilityKey.finiteBarrierSummary ∉ available := by decide) :=
  history.publishCapability .finiteBarrierSummary ⟨value⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consNormalizedSupport
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.supportComplementNormalizations.length)
    (summary : Query cursor.Stage fun _ =>
      Core.Strategy.SupportComplementNormalization.Summary)
    (exact : NormalizedSupportCapability data index cursor.Stage
      cursor.activeInput)
    (fresh : CapabilityKey.normalizedSupportLedger index ∉ available := by
      decide) :=
  history.publishCapability (.normalizedSupportLedger index)
    ⟨{ indexValid := index.isLt, summary, exact }⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consLocalSupply
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.localSupplyLowerBounds.length)
    (summary : Query cursor.Stage fun _ =>
      Core.Strategy.LocalSupplyLowerBound.Summary)
    (exact : LocalSupplyCapability data index cursor.Stage cursor.activeInput)
    (fresh : CapabilityKey.localSupplyLedger index ∉ available := by decide) :=
  history.publishCapability (.localSupplyLedger index)
    ⟨{ indexValid := index.isLt, summary, exact }⟩ fresh

private noncomputable def
    _root_.Hypostructure.Core.Residual.ExactLedger.consHomogeneousPressureOverload
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.coupledHomogeneousFibrePressures.length)
    (terminal : Query cursor.Stage fun _ => CT9.Terminal)
    (exact : Core.Strategy.CoupledHomogeneousFibrePressure.OverloadLedger
      cursor.Stage (Strategy.ProblemInput P)
      data.coupledHomogeneousFibrePressures[index])
    (current_eq : ∀ stage, exact.current stage = cursor.activeInput stage)
    (fresh : CapabilityKey.homogeneousPressureOverload index ∉ available := by
      decide) :=
  history.publishCapability (.homogeneousPressureOverload index)
    ⟨{ indexValid := index.isLt
       terminal
       exact := { ledger := exact, current_eq } }⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consBottleneckSeparator
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.finiteBottleneckClassifications.length)
    (terminal : Query cursor.Stage fun _ => CT6.Terminal)
    (exact : Core.Strategy.FiniteBottleneckClassification.SeparatorLedger
      cursor.Stage (Strategy.ProblemInput P)
      data.finiteBottleneckClassifications[index].snd)
    (current_eq : ∀ stage, exact.current stage = cursor.activeInput stage)
    (fresh : CapabilityKey.bottleneckSeparator index ∉ available := by
      decide) :=
  history.publishCapability (.bottleneckSeparator index)
    ⟨{ indexValid := index.isLt
       terminal
       exact := { ledger := exact, current_eq } }⟩ fresh

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.consPacking
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {cursor : CapabilityCursor data} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) cursor available)
    (index : Fin data.obstructionPackingClosures.length)
    (packing : Query cursor.Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.NonemptyPacking
        (data.obstructionPackingClosures[index].occurrences
          (cursor.activeInput stage))
        (data.obstructionPackingClosures[index].conflict
          (cursor.activeInput stage)))
    (fresh : CapabilityKey.obstructionPacking index ∉ available := by decide) :=
  history.publishCapability (.obstructionPacking index)
    ⟨{ indexValid := index.isLt, packing }⟩ fresh

private def CapabilityCursor.root
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [stageInstance : HasResidual Stage (Strategy.ProblemInput P)] :
    CapabilityCursor data where
  Stage := Stage
  stageResidual := stageInstance
  activeInput := Query.residual
  targetToRoot := fun _ proof => proof

private def CapabilityState.root
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)] :
    CapabilityState data Stage where
  activeInput := Query.residual
  targetToRoot := fun _ proof => proof

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.emptyCapabilities
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (CapabilityState.toCursor (CapabilityState.root data Stage)) [] :=
  _root_.Hypostructure.Core.Residual.ExactLedger.root exactLedgerInternal%
    (CapabilityState.toCursor (CapabilityState.root data Stage))

private def CapabilityCursor.comap
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    (old : CapabilityCursor data)
    (NewStage : Type (max uAmbient uBranch uData))
    [newResidual : HasResidual NewStage (Strategy.ProblemInput P)]
    (project : NewStage → old.Stage)
    (residual_eq : ∀ stage,
      @residualOf NewStage (Strategy.ProblemInput P) newResidual stage =
        @residualOf old.Stage (Strategy.ProblemInput P) old.stageResidual
          (project stage)) : CapabilityCursor data where
  Stage := NewStage
  stageResidual := newResidual
  activeInput := old.activeInput.comap project
  targetToRoot := fun stage proof => by
    rw [residual_eq stage]
    exact old.targetToRoot (project stage) proof

private def CapabilityState.comap
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage NewStage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    [HasResidual NewStage (Strategy.ProblemInput P)]
    (old : CapabilityState data Stage) (project : NewStage → Stage)
    (residual_eq : ∀ stage : NewStage,
      residualOf stage = residualOf (project stage)) :
    CapabilityState data NewStage where
  activeInput := old.activeInput.comap project
  targetToRoot := fun stage proof => by
    rw [residual_eq stage]
    exact old.targetToRoot (project stage) proof

private def CapabilityState.extension
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage)
    (Added : Stage → Type (max uAmbient uBranch uData)) :
    CapabilityState data (Ledger.Extension Stage Added) :=
  state.comap Ledger.Extension.previous (fun _ => rfl)

private def CapabilityState.live
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage) (recipe : Recipe P T Stage) :
    CapabilityState data
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify) :=
  state.comap (fun live => live.toLedger.previous) (fun _ => rfl)

private def CapabilityCursor.extension
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    (cursor : CapabilityCursor data)
    (Added : cursor.Stage → Type (max uAmbient uBranch uData)) :
    CapabilityCursor data :=
  cursor.comap (Ledger.Extension cursor.Stage Added)
    Ledger.Extension.previous (fun _ => rfl)

private def CapabilityCursor.live
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    (cursor : CapabilityCursor data) (recipe : Recipe P T cursor.Stage) :
    CapabilityCursor data :=
  cursor.comap
    (HaltingProgram.LiveExtension T cursor.Stage recipe.contract recipe.certify)
    (fun live => live.toLedger.previous) (fun _ => rfl)

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.comapState
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage NewStage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    [HasResidual NewStage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor available)
    (project : NewStage → Stage)
    (residual_eq : ∀ stage : NewStage,
      residualOf stage = residualOf (project stage)) :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (state.comap project residual_eq).toCursor available :=
  _root_.Hypostructure.Core.Residual.ExactLedger.refine exactLedgerInternal% history ⟨{
    project := project
    residual_eq := residual_eq
    active_eq := fun _ => rfl
  }⟩

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.preserveLedger
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor available)
    {Added : Stage → Type (max uAmbient uBranch uData)} :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (state.extension Added).toCursor available :=
  history.comapState Ledger.Extension.previous (fun _ => rfl)

noncomputable def _root_.Hypostructure.Core.Residual.ExactLedger.preserveLive
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage} {available : List CapabilityKey}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor available)
    (recipe : Recipe P T Stage) :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (state.live recipe).toCursor available :=
  by
    simpa only [CapabilityState.live] using
      history.comapState
        (fun live : HaltingProgram.LiveExtension T Stage recipe.contract
            recipe.certify => live.toLedger.previous)
        (fun _ => rfl)

private def CapabilityCursor.minimalScope
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    (cursor : CapabilityCursor data) (index : Fin data.counterexampleReductions.length)
    (recipe : Recipe P T cursor.Stage)
    (exact : Core.Strategy.InterfaceReplacement.ExactClosureQueries
      data.counterexampleReductions[index].interfaceReplacement
      (HaltingProgram.LiveExtension T cursor.Stage recipe.contract
        recipe.certify)) : CapabilityCursor data where
  Stage := HaltingProgram.LiveExtension T cursor.Stage recipe.contract
    recipe.certify
  stageResidual := inferInstance
  activeInput := exact.context.map fun _ context =>
    { object := context.G
      baseline := context.baseline
      branchState := context.state }
  targetToRoot := fun stage proof => absurd proof (exact.context stage).avoids

private def CapabilityState.minimalScope
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage)
    (index : Fin data.counterexampleReductions.length)
    (recipe : Recipe P T Stage)
    (exact : Core.Strategy.InterfaceReplacement.ExactClosureQueries
      data.counterexampleReductions[index].interfaceReplacement
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)) :
    CapabilityState data
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify) where
  activeInput := exact.context.map fun _ context =>
    { object := context.G
      baseline := context.baseline
      branchState := context.state }
  targetToRoot := fun stage proof => absurd proof (exact.context stage).avoids

noncomputable def
    _root_.Hypostructure.Core.Residual.ExactLedger.initializeMinimalClosure
    {data : StrategyData.{uAmbient, uBranch, uData} P T}
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage}
    (history : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor [])
    (index : Fin data.counterexampleReductions.length)
    (recipe : Recipe P T Stage)
    (exact : Core.Strategy.InterfaceReplacement.ExactClosureQueries
      data.counterexampleReductions[index].interfaceReplacement
      (HaltingProgram.LiveExtension T Stage recipe.contract
        recipe.certify))
    :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (state.minimalScope index recipe exact).toCursor
      [CapabilityKey.minimalClosureAt index, CapabilityKey.minimalContext] :=
  let next := (state.minimalScope index recipe exact).toCursor
  let closureValue : StoredCapability data
      (CapabilityKey.minimalClosureAt index) next :=
    { origin := next
      payload := ⟨{
        indexValid := index.isLt
        exact := exact
        activeObject := fun _ => rfl
      }⟩
      lineage := Core.Residual.RefinementSystem.refl next }
  let contextValue : StoredCapability data CapabilityKey.minimalContext next :=
    { origin := next
      payload := ⟨fun stage => ⟨index, exact.context stage⟩⟩
      lineage := Core.Residual.RefinementSystem.refl next }
  _root_.Hypostructure.Core.Residual.ExactLedger.initializeScope exactLedgerInternal%
    history next (.cons closureValue (.cons contextValue .nil))
    (by simp) (by simp)
    { producer := `Hypostructure.Core.Strategy.minimalCounterexampleScope }

/-- Generic proof that every Strategy consumer is reached with all its typed
ledger requirements.  The output capability list is computed uniformly as
`productions ++ input`; no constructor encodes a particular Strategy chain.
Branch-local capabilities are checked within that branch and are not leaked
through its enclosing routed join. -/
private inductive VerifiedManifest
    {data : StrategyData.{uAmbient, uBranch, uData} P T} :
    Blueprint data .expanded →
      List CapabilityKey → List CapabilityKey →
      Type (max (uAmbient + 1) (uBranch + 1) (uData + 1)) where
  | root :
      VerifiedManifest (.root : Blueprint data .expanded) available available
  | step
      (strategy : StrategyRef data)
      (restFlow : VerifiedManifest rest input current)
      (valid :
        strategy.key.requirementsMet data strategy.resolved current = true)
      (fresh : CapabilityKey.fresh
        (strategy.key.productions data strategy.resolved) current = true) :
      VerifiedManifest (.step rest strategy) input
        (strategy.key.productions data strategy.resolved ++ current)
  | binaryBranch
      (strategy : BinaryStrategyRef data)
      (restFlow : VerifiedManifest rest input current)
      (valid :
        strategy.key.requirementsMet data strategy.resolved current = true)
      (leftFresh : CapabilityKey.fresh strategy.leftProductions current = true)
      (rightFresh : CapabilityKey.fresh strategy.rightProductions current = true)
      (leftFlow :
        VerifiedManifest left
          (strategy.leftProductions ++ current) leftOutput)
      (rightFlow :
        VerifiedManifest right
          (strategy.rightProductions ++ current) rightOutput) :
      VerifiedManifest (.binaryBranch rest strategy left right)
        input current
  | homogeneousBottleneckBranches
      (index : Fin data.homogeneousBottlenecks.length)
      (restFlow : VerifiedManifest rest input current)
      (valid :
        (StrategyKey.homogeneousBottleneck index).requirementsMet
          data index.isLt current = true)
      (handoffFresh : CapabilityKey.fresh
        [.homogeneousHandoff index] current = true)
      (exceptionalFlow :
        VerifiedManifest exceptional current exceptionalOutput)
      (structuredFlow :
        VerifiedManifest structured
          (.homogeneousHandoff index :: current) structuredOutput)
      (boundedFlow :
        VerifiedManifest bounded current boundedOutput) :
      VerifiedManifest
        (.homogeneousBottleneckBranches rest index exceptional structured
          bounded)
        input current
  | minimalCounterexample
      (rest : Blueprint data .expanded)
      (index : Fin data.counterexampleReductions.length)
      (metadata : CounterexampleContinuationMetadata)
      (restFlow : VerifiedManifest rest input []) :
      VerifiedManifest (.minimalCounterexample rest index metadata) input
        [.minimalClosureAt index, .minimalContext]
  | annotate (restFlow : VerifiedManifest rest input output) :
      VerifiedManifest (.annotate rest label) input output
  | labelled (restFlow : VerifiedManifest rest input output) :
      VerifiedManifest (.labelled rest name) input output
  | documented (restFlow : VerifiedManifest rest input output) :
      VerifiedManifest (.documented rest metadata) input output
  | resolvedRoute (route : ResolvedRoute) (metadata : RouteMetadata)
      (restFlow : VerifiedManifest rest input output) :
      VerifiedManifest (.resolvedRoute rest route metadata) input output
  | siblingRoute (route : ResolvedRoute) (metadata : RouteMetadata)
      (restFlow : VerifiedManifest rest input output)
      {destination : Blueprint data .expanded}
      {destinationOutput : List CapabilityKey}
      (destinationFlow :
        VerifiedManifest destination output destinationOutput) :
      VerifiedManifest (.resolvedRoute rest route metadata) input output

private structure CheckedBlueprint
    (data : StrategyData.{uAmbient, uBranch, uData} P T) where
  output : List CapabilityKey
  dag : Blueprint data .expanded
  verified : VerifiedManifest (data := data) dag [] output

private noncomputable def obstructionPackingQuery
    (semantics : Core.Strategy.ObstructionPackingClosure.Semantics.{
      max uAmbient uBranch, uData}
      (Strategy.ProblemInput P) (fun input => T.Predicate input.object))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage).object) :
    let recipe := obstructionPackingRecipe (T := T) semantics (Stage := Stage)
      current targetToRoot
    Query
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (fun live =>
        Core.Strategy.ObstructionPackingClosure.NonemptyPacking
          (semantics.occurrences
            ((HaltingProgram.LiveExtension.preserveQuery (T := T) current) live))
          (semantics.conflict
            ((HaltingProgram.LiveExtension.preserveQuery (T := T) current) live))) := by
  let recipe := obstructionPackingRecipe (T := T) semantics (Stage := Stage)
    current targetToRoot
  let Live :=
    HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  let latest : Query Live
      (fun live => Sigma (recipe.contract.Payload live.previous)) :=
    (Query.latest (Previous := Stage)
      (Added := fun stage => Sigma (recipe.contract.Payload stage))).comap
      (fun live : Live => live.toLedger)
  exact latest.map fun live _payload =>
    match outcomeEq : live.ledger.added.snd.down with
    | .inl packing => packing
    | .inr target =>
        False.elim (by
          have certified :
              recipe.certify live.ledger.previous live.ledger.added =
                some ⟨(targetToRoot live.ledger.previous) target.down⟩ := by
            dsimp [recipe, obstructionPackingRecipe]
            rw [outcomeEq]
          have rejected := live.isLive
          rw [certified] at rejected
          contradiction)

/-- **The barrier node's rate ledger.**

The retained CT16 result's `Summary`, published together with the two facts
only this node can prove about it:
that the record is Core's own `ofRows` aggregation of the rows it generated
(`summaryOfExecution_derived`), and that the generated flat column -- the
denominator of the flatness ratio `log₂(W/F)` -- is nonvanishing
(`output_flatProduct_pos`, from the sealed proof payload).

Both are read from the identical `latest` query the summary itself is read
from, so a downstream consumer receives facts about the very value it compares,
never about an independently reconstructed table. -/
private noncomputable def finiteBarrierRateLedger
    (registration :
      Core.Strategy.FiniteBarrierEnumeration.Registration.{
        max uAmbient uBranch, uData} (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (sourceCode : Query Stage fun _ => List Bool)
    (current : Query Stage fun _ => Strategy.ProblemInput P) :
    let recipe :=
      finiteBarrierEnumerationRecipe (T := T) registration (Stage := Stage)
        sourceCode current
    Core.Strategy.FiniteBarrierEnumeration.RateLedger
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify) := by
  let profile :
      Core.Strategy.FiniteBarrierEnumeration.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration := registration, sourceCode := sourceCode, current := current }
  let recipe :=
    finiteBarrierEnumerationRecipe (T := T) registration (Stage := Stage)
      sourceCode current
  let Live :=
    HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  let latest : Query Live
      (fun live => Sigma (recipe.contract.Payload live.previous)) :=
    (Query.latest (Previous := Stage)
      (Added := fun stage => Sigma (recipe.contract.Payload stage))).comap
      (fun live : Live => live.toLedger)
  exact
    { summary := latest.map fun _ payload =>
        profile.summaryOfOutput _ payload.snd
      sourceRows := latest.map fun _ payload =>
        profile.rows payload.snd.1.stage.previous
      exact := latest.dependentMap fun _ payload =>
        profile.output_exact _ payload.snd
      derived := latest.dependentMap fun _ payload =>
        profile.output_derived _ payload.snd
      flatPositive := latest.dependentMap fun _ payload =>
        profile.output_flatProduct_pos _ payload.snd }

private noncomputable def finiteDensityBudgetSplit
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage) :
    Strategy.Dichotomy.{uStage, uStage, uStage} Stage :=
  let profile :
      Core.Strategy.FiniteDensityBudget.Profile Stage :=
    Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
      packingCount barrierRate registration
      degreeSurplusLoad degreeSurplusThreshold nearCubic
  profile.dichotomy

private theorem finiteDensityBudgetSplit_leftPayload_eq
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage) :
    (finiteDensityBudgetSplit registration packingCount barrierRate
      degreeSurplusLoad degreeSurplusThreshold nearCubic).LeftPayload =
      (let profile :=
        Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
          packingCount barrierRate registration
          degreeSurplusLoad degreeSurplusThreshold nearCubic;
        profile.OverflowResidual) := rfl

private theorem finiteDensityBudgetSplit_leftBranchStage_eq
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage) :
    Ledger.Extension Stage
        (finiteDensityBudgetSplit registration
          packingCount barrierRate
          degreeSurplusLoad degreeSurplusThreshold nearCubic).LeftPayload =
      Ledger.Extension Stage
        (let profile :=
          Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
            packingCount barrierRate registration
            degreeSurplusLoad degreeSurplusThreshold nearCubic;
          profile.OverflowResidual) := by
  rw [finiteDensityBudgetSplit_leftPayload_eq]

private theorem finiteDensityBudgetSplit_rightPayload_eq
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage) :
    (finiteDensityBudgetSplit registration packingCount barrierRate
      degreeSurplusLoad degreeSurplusThreshold nearCubic).RightPayload =
      (let profile :=
        Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
          packingCount barrierRate registration
          degreeSurplusLoad degreeSurplusThreshold nearCubic;
        profile.CapResidual) := rfl

private theorem finiteDensityBudgetSplit_rightBranchStage_eq
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage) :
    Ledger.Extension Stage
        (finiteDensityBudgetSplit registration
          packingCount barrierRate
          degreeSurplusLoad degreeSurplusThreshold nearCubic).RightPayload =
      Ledger.Extension Stage
        (let profile :=
          Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
            packingCount barrierRate registration
            degreeSurplusLoad degreeSurplusThreshold nearCubic;
          profile.CapResidual) := by
  rw [finiteDensityBudgetSplit_rightPayload_eq]

private noncomputable def finiteDensityBudgetSplit_classifiedTerminalTypeCheck
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage)
    (stage : Stage) :
    (let profile :=
      Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
        packingCount barrierRate registration
        degreeSurplusLoad degreeSurplusThreshold nearCubic;
      Sum (profile.OverflowResidual stage) (profile.CapResidual stage)) :=
  (finiteDensityBudgetSplit registration
    packingCount barrierRate
    degreeSurplusLoad degreeSurplusThreshold nearCubic).classify stage

private noncomputable def finiteDensityBudgetRecipe
    (registration :
      Core.Strategy.FiniteDensityBudget.Registration.{
        max uAmbient uBranch} (Strategy.ProblemInput P))
    {Stage : Type uStage}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (packingCount : Query Stage fun _ => Nat)
    (barrierRate :
      Core.Strategy.FiniteBarrierEnumeration.RateLedger Stage)
    (degreeSurplusLoad degreeSurplusThreshold : Query Stage fun _ => Nat)
    (nearCubic : Query Stage fun stage =>
      degreeSurplusLoad stage ≤ degreeSurplusThreshold stage) :
    Recipe P T Stage :=
  let split :=
    finiteDensityBudgetSplit registration packingCount barrierRate
      degreeSurplusLoad degreeSurplusThreshold nearCubic
  let contract : Contract.{uStage, 0, uStage} Stage :=
    Strategy.dichotomyContract.{uStage, uStage, uStage} split
  { contract
    certify := fun _ _ => none }

private noncomputable def scaleThresholdRecipe
    (registration : Core.Strategy.ScaleThresholdDichotomy.Registration
      (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.ScaleThresholdDichotomy.Profile
        Stage :=
    Core.Strategy.ScaleThresholdDichotomy.Profile.ofRegistration registration
  { contract := profile.execution.toContract
    certify := fun _ _ => none }

/-- Lift the registered residual-owned atom/context classifier to the common
sealed dichotomy interface. -/
private noncomputable def atomContextObstructionSplit
    (registration :
      Core.Strategy.AtomContextObstructionDichotomy.Registration.{
        uAmbient, uBranch, uData, max uAmbient uBranch}
        P (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Strategy.Dichotomy.{
      max uAmbient uBranch uData,
      max uAmbient uBranch uData,
      max uAmbient uBranch uData} Stage :=
  let profile :
      Core.Strategy.AtomContextObstructionDichotomy.Profile.{
        uAmbient, uBranch, max uAmbient uBranch uData, uData}
        P Stage :=
    Core.Strategy.AtomContextObstructionDichotomy.Profile.ofRegistration
      registration
  { LeftPayload := fun stage =>
      ULift.{max uAmbient uBranch uData}
        (profile.AtomResidual stage)
    RightPayload := fun stage =>
      ULift.{max uAmbient uBranch uData}
        (profile.ContextResidual stage)
    classify := fun stage =>
      match profile.dichotomy.classify stage with
      | .inl residual => .inl (ULift.up residual)
      | .inr residual => .inr (ULift.up residual) }

private noncomputable def atomContextObstructionRecipe
    (registration :
      Core.Strategy.AtomContextObstructionDichotomy.Registration.{
        uAmbient, uBranch, uData, max uAmbient uBranch}
        P (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.AtomContextObstructionDichotomy.Profile.{
        uAmbient, uBranch, max uAmbient uBranch uData, uData}
        P Stage :=
    Core.Strategy.AtomContextObstructionDichotomy.Profile.ofRegistration
      registration
  { contract := profile.execution.toContract
    certify := fun _ _ => none }

/-- Deterministic atom closure and promotion of the retained context. -/
private structure BinaryResolution
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (strategy : BinaryStrategyRef data)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage)
    {available : List CapabilityKey}
    (capabilities : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor available) where
  split : Strategy.Dichotomy.{
    max uAmbient uBranch uData,
    max uAmbient uBranch uData,
    max uAmbient uBranch uData} Stage
  leftDirect : Option (∀ stage, split.LeftPayload stage ->
    PLift (T.Predicate
      (residualOf stage : Strategy.ProblemInput P).object))
  rightDirect : Option (∀ stage, split.RightPayload stage ->
    PLift (T.Predicate
      (residualOf stage : Strategy.ProblemInput P).object))
  leftProduced : List CapabilityKey
  rightProduced : List CapabilityKey
  leftProduced_eq : leftProduced = strategy.leftProductions
  rightProduced_eq : rightProduced = strategy.rightProductions
  /-- Each arm refines and appends to the literal incoming canonical ledger. -/
  leftCapabilities :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (state.extension split.LeftPayload).toCursor
      (leftProduced ++ available)
  rightCapabilities :
    Core.Residual.ExactLedger (CapabilityCursor data)
      (state.extension split.RightPayload).toCursor
      (rightProduced ++ available)

universe uPrevious uResidual uResponse uSupply uDatum uClass uPromotion
  uCoordinate uCode uAmbientItem uPiece

/-- The one rank-drop exclusion Core owns at a consuming stage: the registered
target-dependence predicate is refuted at the object the spine is currently
arguing about, pointwise on the coordinate schedule.

This is not a registration statement.  A registration sees only its own
residual, and the fact that refutes the predicate is produced at the
minimal-counterexample node and retained in the closure ledger; it is read
back here through `ExactLedger.minimalClosureAt` and its provenance law.
The two remaining ledger arguments are kept in the signature so that this
statement is pinned to the very composition Core builds. -/
private abbrev TargetRelativeRankCoreExclusions
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbientItem}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Core.Strategy.TargetRelativeRankDichotomy.Registration.{
        uResidual, uAmbientItem, uCoordinate, uPromotion, uClass, uDatum,
        uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (_normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbientItem, uPiece} Previous Residual
        (fun previous => AmbientItem (current previous)))
    (_localSupply : Query Previous fun _ =>
      ULift.{uSupply} Core.Strategy.LocalSupplyLowerBound.Summary) : Prop :=
  ∀ (previous : Previous) (coordinate : Coordinate (current previous)),
    ¬ registration.TargetDependent (current previous)
        (registration.response (current previous)) coordinate

open Core.Strategy.TargetRelativeRankDichotomy in
/-- Every rank-drop alternative of a registration-built target-relative rank
composition is impossible under three facts, one per owner.

`RankDropResidual` has four constructors and Core's direct branch closure is
all-or-nothing, so a rank-drop closure has to account for all four.  Three of
the four are Core's own business:

* the CT16 proper-support alternative needs nothing at all -- every
  registration-built composition hands CT16 the very schedule its own
  `InSupport` recognizes;
* the CT15 capacity alternative needs nothing at all either -- the capacity
  `ofRegistrationAt` installs is the charge total of that same schedule plus
  the registered slack, so CT15's own gate cannot overflow it;
* the CT15 dependence alternative is excluded by `core`, the pointwise
  exclusion of the registered target-dependence predicate at the object the
  spine is currently arguing about, which Core reads back from the retained
  minimal-counterexample closure.

Only the fourth, the CT16 closed-code mismatch, is a statement about the
registration's own observation table, and that is exactly what
`Registration.rankDropImpossible` carries.  Nothing is re-executed and no
terminal is asserted: each branch is discharged by the existing impossibility
theorem for its own alternative. -/
private theorem targetRelativeRankDrop_false
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbientItem}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Core.Strategy.TargetRelativeRankDichotomy.Registration.{
        uResidual, uAmbientItem, uCoordinate, uPromotion, uClass, uDatum,
        uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbientItem, uPiece} Previous Residual
        (fun previous => AmbientItem (current previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} Core.Strategy.LocalSupplyLowerBound.Summary)
    (exhaustive : registration.toBaseRegistration.ClassificationExhaustive)
    (core : TargetRelativeRankCoreExclusions registration current
      normalizedSupport localSupply)
    {previous : Previous}
    (drop :
      (Core.Strategy.TargetRelativeRankDichotomy.Profile.ofRegistrationAt.{
        uPrevious, uResidual, uResponse, uSupply, uDatum, uClass, uPromotion,
        uCoordinate, uCode, uAmbientItem, uPiece}
        registration current normalizedSupport
        localSupply).code.RankDropResidual previous) :
    False := by
  have independent := core
  cases drop with
  | dependent output selected =>
      exact CodeProfile.dependent_impossible _ output selected
        fun coordinate => independent _ coordinate
  | capacity output selected =>
      exact Profile.ofRegistrationAt_capacity_impossible registration current
        normalizedSupport localSupply output selected
  | properSupport output _ codeSelected =>
      exact Profile.ofRegistrationAt_properSupport_impossible registration
        current normalizedSupport localSupply output codeSelected
  | mismatch output _ codeSelected =>
      exact Profile.ofRegistrationAt_mismatch_impossible registration current
        normalizedSupport localSupply exhaustive output codeSelected

/--
Resolve any sealed two-terminal key to the common predecessor-indexed
dichotomy interface.  This is registration lowering, not DAG topology:
`sharedContinuation` never inspects the Strategy family.
-/
private noncomputable def resolveBinary
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (strategy : BinaryStrategyRef data)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage}
    {available : List CapabilityKey}
    (capabilities : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor available)
    (valid :
      strategy.key.requirementsMet data strategy.resolved available = true)
    (leftFresh : CapabilityKey.fresh strategy.leftProductions available = true)
    (rightFresh : CapabilityKey.fresh strategy.rightProductions available = true) :
    BinaryResolution data strategy Stage state capabilities := by
  rcases strategy with ⟨terminal⟩
  exact match view_eq : terminal with
  | .inl index =>
      let registered := data.dichotomies[index]
      let split : Strategy.Dichotomy.{
          max uAmbient uBranch uData,
          max uAmbient uBranch uData,
          max uAmbient uBranch uData} Stage :=
        { LeftPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (registered.LeftPayload (residualOf stage))
          RightPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (registered.RightPayload (residualOf stage))
          classify := fun stage =>
            match registered.classify (residualOf stage) with
            | .inl witness => .inl (ULift.up witness)
            | .inr witness => .inr (ULift.up witness) }
      { split
        leftDirect := registered.closeLeft.map fun close stage witness =>
          ⟨close.down (residualOf stage) witness.down⟩
        rightDirect := registered.closeRight.map fun close stage witness =>
          ⟨close.down (residualOf stage) witness.down⟩
        leftProduced := []
        rightProduced := []
        leftProduced_eq := by
          simp [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view]
        rightProduced_eq := by
          simp [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view]
        leftCapabilities := capabilities.preserveLedger
        rightCapabilities := capabilities.preserveLedger }
  | .inr (.inl index) =>
      let registration := data.scaleThresholdDichotomies[index]
      have rightFresh' : CapabilityKey.fresh
          [.nearCubicSpine index] available = true := by
        simpa [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view,
          view_eq] using rightFresh
      /- The comparison is run at the object the spine is arguing about, the
      same query every other registered family in this file is lowered at.
      Before a minimal-counterexample selection that is the problem input; after
      one it is the selected minimal object, and running the surplus/threshold
      comparison anywhere else would compare the wrong object. -/
      let profile :
          Core.Strategy.ScaleThresholdDichotomy.Profile
            Stage :=
        Core.Strategy.ScaleThresholdDichotomy.Profile.ofRegistrationAt
          registration capabilities.activeInput
      let split : Strategy.Dichotomy.{
          max uAmbient uBranch uData,
          max uAmbient uBranch uData,
          max uAmbient uBranch uData} Stage :=
        { LeftPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.AboveResidual stage)
          RightPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.AtOrBelowResidual stage)
          classify := fun stage =>
            match profile.dichotomy.classify stage with
            | .inl residual => .inl (ULift.up residual)
            | .inr residual => .inr (ULift.up residual) }
      { split
        leftDirect := none
        rightDirect := none
        leftProduced := []
        rightProduced := [.nearCubicSpine index]
        leftProduced_eq := by
          simp [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view]
        rightProduced_eq := by
          simp [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view]
        leftCapabilities := capabilities.preserveLedger
        /- `def:surviving-cold-branch` (vi).  The at-or-below arm's payload is
        the CT14 capacity outcome itself, so the estimate it records is read off
        that payload by `registeredComparisonAt` and published; the strict-above
        arm records the complementary comparison and publishes nothing new. -/
        rightCapabilities :=
          capabilities.preserveLedger.consNearCubicSpine index
            ( fun stage =>
              (Core.Strategy.ScaleThresholdDichotomy.Profile.AtOrBelowResidual.registeredComparisonAt
                registration capabilities.activeInput
                stage.added.down))
            (fresh := CapabilityKey.not_mem_of_fresh rightFresh' (by simp)) }
  | .inr (.inr (.inl index)) => by
      let registered := data.atomContextObstructionDichotomies[index]
      exact
      { split := atomContextObstructionSplit
          registered.registration
        leftDirect := none
        rightDirect := none
        leftProduced := []
        rightProduced := []
        leftProduced_eq := by
          simp [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view]
        rightProduced_eq := by
          simp [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view]
        leftCapabilities := capabilities.preserveLedger
        rightCapabilities := capabilities.preserveLedger }
  | .inr (.inr (.inr (.inl index))) => by
      have leftFresh' : CapabilityKey.fresh [.targetRankDrop] available = true := by
        simpa [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view,
          view_eq] using leftFresh
      have rightFresh' : CapabilityKey.fresh
          [.fullRankExactCode, .fullRankCertificate, .independentRank]
          available = true := by
        simpa [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view,
          view_eq] using rightFresh
      have fullRankExactFresh : CapabilityKey.fullRankExactCode ∉ available :=
        CapabilityKey.not_mem_of_fresh rightFresh' (by simp)
      have fullRankCertificateFresh :
          CapabilityKey.fullRankCertificate ∉ available :=
        CapabilityKey.not_mem_of_fresh rightFresh' (by simp)
      have independentRankFresh : CapabilityKey.independentRank ∉ available :=
        CapabilityKey.not_mem_of_fresh rightFresh' (by simp)
      let packed := data.targetRelativeRankDichotomies[index]
      let supplyIndex := packed.snd.fst
      let boundaryIndex := data.localSupplyLowerBounds[supplyIndex].fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      change StrategyKey.requirementsMet data
        (.targetRelativeRankDichotomy index) index.isLt available = true at valid
      have requiredRaw := valid
      simp [StrategyKey.requirementsMet, StrategyKey.requirements]
        at requiredRaw
      have requiredSupport :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ available := by
        simpa [packed, supplyIndex, boundaryIndex, supportIndex] using requiredRaw.1
      have requiredSupply :
          CapabilityKey.localSupplyLedger supplyIndex ∈ available := by
        simpa [packed, supplyIndex] using requiredRaw.2
      let registration := packed.snd.snd
      let supplyCapability :=
        capabilities.localSupplyExact supplyIndex requiredSupply
      let localSupplyQuery :=
        (capabilities.query (.localSupplyLedger supplyIndex) requiredSupply).map
          fun _ summary => ULift.up.{uData} summary
      let profile :=
        Core.Strategy.TargetRelativeRankDichotomy.Profile.ofRegistrationAt
          (Previous := Stage) (Residual := Strategy.ProblemInput P)
          registration capabilities.activeInput supplyCapability.normalized
          localSupplyQuery
      let split : Strategy.Dichotomy.{
          max uAmbient uBranch uData,
          max uAmbient uBranch uData,
          max uAmbient uBranch uData} Stage :=
        { LeftPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.code.RankDropResidual stage)
          RightPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.code.FullRankResidual stage)
          classify := fun stage =>
            match profile.dichotomy.classify stage with
            | .inl residual => .inl (ULift.up residual)
            | .inr residual => .inr (ULift.up residual) }
      let leftPayload :
          Query (Ledger.Extension Stage split.LeftPayload)
            (fun branch => split.LeftPayload branch.previous) :=
        Query.latest
      let rightPayload :
          Query (Ledger.Extension Stage split.RightPayload)
            (fun branch => split.RightPayload branch.previous) :=
        Query.latest
      let exactRankDrop :
          Query (Ledger.Extension Stage split.LeftPayload) fun branch =>
            TargetRankDropCapability data (residualOf branch) :=
         fun branch =>
          { Source := Stage
            sourceHasResidual := inferInstance
            source := branch.previous
            source_residual_eq := rfl
            profile := profile
            result := branch.added.down }
      let fullRankMarker :=
        rightPayload.map fun _ _ => ()
      let independentRank :=
        rightPayload.map fun _ payload =>
          let fullRank := payload.down
          let routed := fullRank.exact.output.fst.snd.stage.added
          (routed.fullRankLedgerOutput fullRank.rankSelected).rank.value
      let fullRankCertificate :
          Query (Ledger.Extension Stage split.RightPayload) fun _ =>
            Core.Strategy.TargetRelativeRankDichotomy.FullRankCertificate :=
        rightPayload.map fun _ payload =>
          let fullRank := payload.down
          { rank := profile.code.fullRankValue fullRank
            coordinateCard :=
              (profile.rank.rankCapability.coordinatesAt
                fullRank.exact.output.fst.snd.stage.previous).values.length
            rank_eq_coordinateCard :=
              profile.code.fullRankValue_eq_coordinateCard fullRank }
      /- No rank-drop closure is available on the unlinked key.  Its
      `TargetDependent` predicate is an opaque registration field, so the
      minimal-counterexample closure retained in the ledger says nothing about
      it and CT15's dependence alternative stays live.  The linked key below
      is the one whose predicate Core pins to the compression-candidate
      carrier, and that is where the rank-drop output closes. -/
      exact {
        split := split
        leftDirect := none
        rightDirect := none
        leftProduced := [.targetRankDrop]
        rightProduced :=
          [.fullRankExactCode, .fullRankCertificate, .independentRank]
        leftProduced_eq := rfl
        rightProduced_eq := rfl
        leftCapabilities :=
          capabilities.preserveLedger.consTargetRankDrop exactRankDrop
            (fresh := CapabilityKey.not_mem_of_fresh leftFresh' (by simp))
        rightCapabilities :=
          (((capabilities.preserveLedger.cons
              .independentRank independentRank
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (fresh := by simpa using independentRankFresh)).cons
              .fullRankCertificate fullRankCertificate
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (fresh := by simpa using fullRankCertificateFresh)).cons
            .fullRankExactCode fullRankMarker
            (by intro packingIndex equality; cases equality)
            (by intro equality; cases equality)
            (by intro equality; cases equality)
            (fresh := by simpa using fullRankExactFresh))
      }
  | .inr (.inr (.inr (.inr (.inl index)))) => by
      have leftFresh' : CapabilityKey.fresh
          [.finiteDensityOverflow] available = true := by
        simpa [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view,
          view_eq] using leftFresh
      have rightFresh' : CapabilityKey.fresh
          [.finiteDensityCap] available = true := by
        simpa [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view,
          view_eq] using rightFresh
      have required :
          CapabilityKey.obstructionPacking 0 ∈ available ∧
            CapabilityKey.finiteBarrierSummary ∈ available ∧
            CapabilityKey.nearCubicSpine 0 ∈ available := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
          BinaryStrategyRef.key] using valid
      let nearCubicIndex : Fin data.scaleThresholdDichotomies.length :=
        ⟨0, capabilities.nearCubicIndexValid 0 required.2.2⟩
      let degreeSurplusLoad : Query Stage fun _ => Nat :=
         fun stage =>
          data.scaleThresholdDichotomies[nearCubicIndex].load
            (capabilities.activeInput stage)
      let degreeSurplusThreshold : Query Stage fun _ => Nat :=
         fun stage =>
          (data.scaleThresholdDichotomies[nearCubicIndex].table
            (capabilities.activeInput stage)).threshold
            (data.scaleThresholdDichotomies[nearCubicIndex].size
              (capabilities.activeInput stage))
      let profile :=
        Core.Strategy.FiniteDensityBudget.Profile.ofRegistration
          (capabilities.packingCountQuery 0 required.1)
          (capabilities.barrierRate required.2.1)
          (data.finiteDensityBudgets[index])
          degreeSurplusLoad degreeSurplusThreshold
          (capabilities.nearCubicSpine nearCubicIndex required.2.2)
      exact {
        split := profile.dichotomy
        leftDirect := none
        rightDirect := none
        leftProduced := [.finiteDensityOverflow]
        rightProduced := [.finiteDensityCap]
        leftProduced_eq := rfl
        rightProduced_eq := rfl
        leftCapabilities :=
          capabilities.preserveLedger.consOverflow profile.overflowLedger
            (fresh := CapabilityKey.not_mem_of_fresh leftFresh' (by simp))
        rightCapabilities :=
          capabilities.preserveLedger.consCap profile.capLedger
            (fresh := CapabilityKey.not_mem_of_fresh rightFresh' (by simp))
      }
  | .inr (.inr (.inr (.inr (.inr (.inl index))))) => by
      have leftFresh' : CapabilityKey.fresh
          [.finiteStateCapacityContinuation] available = true := by
        simpa [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view,
          view_eq] using leftFresh
      have rightFresh' : CapabilityKey.fresh
          [.finiteStateCapacityContinuation] available = true := by
        simpa [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view,
          view_eq] using rightFresh
      let entry := data.finiteStateCapacities[index]
      let supplyIndex := entry.fst
      change StrategyKey.requirementsMet data
        (.finiteStateCapacity index) index.isLt available = true at valid
      have requiredRaw := valid
      simp [StrategyKey.requirementsMet, StrategyKey.requirements]
        at requiredRaw
      have requiredRank : CapabilityKey.independentRank ∈ available :=
        requiredRaw.1
      have requiredBarrier :
          CapabilityKey.finiteBarrierSummary ∈ available :=
        requiredRaw.2.1
      have requiredFullRank :
          CapabilityKey.fullRankCertificate ∈ available :=
        requiredRaw.2.2.1
      have requiredSupply :
          CapabilityKey.localSupplyLedger supplyIndex ∈ available := by
        simpa [entry, supplyIndex] using requiredRaw.2.2.2
      let supplyCapability :=
        capabilities.localSupplyExact supplyIndex requiredSupply
      let profile :
          Core.Strategy.FiniteStateCapacity.Profile
            Stage (Strategy.ProblemInput P) :=
        { AmbientItem := data.localSupplyLowerBounds[supplyIndex].AmbientItem
          registration := entry.snd
          current := capabilities.activeInput
          complement := supplyCapability.normalized.complement
          fullRankCertificate :=
            capabilities.query .fullRankCertificate requiredFullRank
          independentRank := capabilities.query .independentRank requiredRank
          finiteBarrierSummary :=
            capabilities.query .finiteBarrierSummary requiredBarrier
          localSupply :=
            capabilities.query (.localSupplyLedger supplyIndex) requiredSupply }
      /- The registered non-capacity closure, read as Core's ordinary direct
      branch closure.  This is the same mechanism `DichotomyData.closeLeft`
      already supplies for binary families; registrations that leave the field
      `none` keep a live non-capacity output exactly as before. -/
      let nonCapacityDirect :
          Option (∀ stage, profile.dichotomy.LeftPayload stage →
            PLift (T.Predicate
              (residualOf stage : Strategy.ProblemInput P).object)) :=
        profile.nonCapacityClosureOfRegistration.map
          fun closure stage witness =>
            (profile.nonCapacityResidual_false closure.down stage witness).elim
      let resolution :
          BinaryResolution data ⟨.inr (.inr (.inr (.inr (.inr (.inl index)))))⟩
            Stage state capabilities :=
        { split := profile.dichotomy
          leftDirect := nonCapacityDirect
          rightDirect := none
          leftProduced := [.finiteStateCapacityContinuation]
          rightProduced := [.finiteStateCapacityContinuation]
          leftProduced_eq := rfl
          rightProduced_eq := rfl
          leftCapabilities :=
            capabilities.preserveLedger.consCapacity
              (profile.inheritedContinuationLedger.preserve
                (Added := profile.dichotomy.LeftPayload))
              (fresh := CapabilityKey.not_mem_of_fresh leftFresh' (by simp))
          rightCapabilities :=
            capabilities.preserveLedger.consCapacity profile.continuationLedger
              (fresh := CapabilityKey.not_mem_of_fresh rightFresh' (by simp)) }
      exact resolution
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl index)))))) =>
      let profile :
          Core.Strategy.FiniteScheduleCapacity.Profile
            Stage (Strategy.ProblemInput P) :=
        { registration := data.finiteScheduleCapacities[index] }
      { split := profile.dichotomy
        leftDirect := none
        rightDirect := none
        leftProduced := []
        rightProduced := []
        leftProduced_eq := by
          simp [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view]
        rightProduced_eq := by
          simp [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view]
        leftCapabilities := capabilities.preserveLedger
        rightCapabilities := capabilities.preserveLedger }
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index))))))) => by
      have leftFresh' : CapabilityKey.fresh [.targetRankDrop] available = true := by
        simpa [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view,
          view_eq] using leftFresh
      have rightFresh' : CapabilityKey.fresh
          [.fullRankExactCode, .fullRankCertificate, .independentRank]
          available = true := by
        simpa [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view,
          view_eq] using rightFresh
      have fullRankExactFresh : CapabilityKey.fullRankExactCode ∉ available :=
        CapabilityKey.not_mem_of_fresh rightFresh' (by simp)
      have fullRankCertificateFresh :
          CapabilityKey.fullRankCertificate ∉ available :=
        CapabilityKey.not_mem_of_fresh rightFresh' (by simp)
      have independentRankFresh : CapabilityKey.independentRank ∉ available :=
        CapabilityKey.not_mem_of_fresh rightFresh' (by simp)
      let packed := data.compressionLinkedTargetRelativeRankDichotomies[index]
      let supplyIndex := packed.snd.fst
      let boundaryIndex := data.localSupplyLowerBounds[supplyIndex].fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      have valid' : StrategyKey.requirementsMet data
          (.compressionLinkedTargetRelativeRankDichotomy index)
          index.isLt available = true := by
        simpa only [BinaryStrategyRef.key] using valid
      have requiredRaw :
          let packedRaw :=
            data.compressionLinkedTargetRelativeRankDichotomies[index]'
              index.isLt
          let supplyRaw := packedRaw.snd.fst
          let boundaryRaw := data.localSupplyLowerBounds[supplyRaw].fst
          let supportRaw := data.boundaryDemandAccountings[boundaryRaw].fst
          CapabilityKey.normalizedSupportLedger supportRaw ∈ available ∧
            CapabilityKey.localSupplyLedger supplyRaw ∈ available ∧
              CapabilityKey.minimalClosureAt packedRaw.reductionIndex ∈
                available := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid'
      have requiredRaw' :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ available ∧
            CapabilityKey.localSupplyLedger supplyIndex ∈ available ∧
              CapabilityKey.minimalClosureAt packed.reductionIndex ∈
                available := by
        simpa [packed, supplyIndex, boundaryIndex, supportIndex] using requiredRaw
      have requiredSupport :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ available := by
        exact requiredRaw'.1
      have requiredSupply :
          CapabilityKey.localSupplyLedger supplyIndex ∈ available := by
        exact requiredRaw'.2.1
      have requiredClosure :
          CapabilityKey.minimalClosureAt packed.reductionIndex ∈ available := by
        exact requiredRaw'.2.2
      let supplyCapability :=
        capabilities.localSupplyExact supplyIndex requiredSupply
      let closureQueries :=
        capabilities.minimalClosureAt packed.reductionIndex requiredClosure
      let localSupplyQuery :=
        (capabilities.query (.localSupplyLedger supplyIndex)
          requiredSupply).map fun _ summary => ULift.up.{uData} summary
      let registration :=
        Core.Strategy.TargetRelativeRankDichotomy.FixedRegistration.toRegistration
          packed.snd.base _ packed.snd.fixed
      let profile :=
        Core.Strategy.TargetRelativeRankDichotomy.Profile.ofRegistrationAt
          (Previous := Stage) (Residual := Strategy.ProblemInput P)
          registration capabilities.activeInput supplyCapability.normalized
          localSupplyQuery
      let split : Strategy.Dichotomy.{
          max uAmbient uBranch uData,
          max uAmbient uBranch uData,
          max uAmbient uBranch uData} Stage :=
        { LeftPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.code.RankDropResidual stage)
          RightPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.code.FullRankResidual stage)
          classify := fun stage =>
            match profile.dichotomy.classify stage with
            | .inl residual => .inl (ULift.up residual)
            | .inr residual => .inr (ULift.up residual) }
      let rightPayload :
          Query (Ledger.Extension Stage split.RightPayload)
            (fun branch => split.RightPayload branch.previous) :=
        Query.latest
      let fullRankMarker :=
        rightPayload.map fun _ _ => ()
      let independentRank :=
        rightPayload.map fun _ payload =>
          let fullRank := payload.down
          let routed := fullRank.exact.output.fst.snd.stage.added
          (routed.fullRankLedgerOutput fullRank.rankSelected).rank.value
      let fullRankCertificate :
          Query (Ledger.Extension Stage split.RightPayload) fun _ =>
            Core.Strategy.TargetRelativeRankDichotomy.FullRankCertificate :=
        rightPayload.map fun _ payload =>
          let fullRank := payload.down
          { rank := profile.code.fullRankValue fullRank
            coordinateCard :=
              (profile.rank.rankCapability.coordinatesAt
                fullRank.exact.output.fst.snd.stage.previous).values.length
            rank_eq_coordinateCard :=
              profile.code.fullRankValue_eq_coordinateCard fullRank }
      let exactRankDrop :
          Query (Ledger.Extension Stage split.LeftPayload) fun branch =>
            TargetRankDropCapability data (residualOf branch) :=
         fun branch =>
          { Source := Stage
            sourceHasResidual := inferInstance
            source := branch.previous
            source_residual_eq := rfl
            profile := profile
            result := branch.added.down }
      /- CT15's dependence alternative, refuted from the ledger.  On the linked
      key the registered target-dependence predicate is not an opaque field:
      Core pinned it to the interface-replacement compression-candidate carrier
      when the entry was typed.  So a dependent coordinate would exhibit a
      compression candidate at the object the spine is arguing about, the
      provenance law identifies that object with the selected minimal
      counterexample, and the closure retained at the reduction node rejects
      it.  Nothing is recomputed and no fact is restated: the site and the
      candidate are read out of the predicate the branch already carries. -/
      let dependenceExcluded :
          TargetRelativeRankCoreExclusions registration
            capabilities.activeInput supplyCapability.normalized
            localSupplyQuery :=
        fun stage _coordinate compressible => by
          have objectEq :=
            capabilities.minimalClosureActiveObject packed.reductionIndex
              requiredClosure stage
          rcases compressible with ⟨pair⟩
          obtain ⟨sited, candidate⟩ := pair
          revert candidate
          generalize sited.1 = site
          clear sited
          revert site
          simp only [
            _root_.Hypostructure.Core.Residual.ExactLedger.activeInput] at *
          rw [objectEq]
          intro site candidate
          exact (closureQueries.closure stage).noCompressionCandidate _
            site ⟨candidate⟩
      /- The registered rank-drop closure, read as Core's ordinary direct
      branch closure.  This is the same mechanism `DichotomyData.closeLeft`
      already supplies for binary families; registrations that leave the field
      `none` keep a live rank-drop output exactly as before. -/
      let _rankDropDirect :
          Option (∀ stage, split.LeftPayload stage →
            PLift (T.Predicate
              (residualOf stage : Strategy.ProblemInput P).object)) :=
        packed.snd.base.rankDropClosure.map fun closure stage witness =>
          (targetRelativeRankDrop_false (previous := stage) registration
            capabilities.activeInput supplyCapability.normalized
            localSupplyQuery closure.down dependenceExcluded
            witness.down).elim
      exact
        { split
          leftDirect := none
          rightDirect := none
          leftProduced := [.targetRankDrop]
          rightProduced :=
            [.fullRankExactCode, .fullRankCertificate, .independentRank]
          leftProduced_eq := rfl
          rightProduced_eq := rfl
          leftCapabilities :=
            capabilities.preserveLedger.consTargetRankDrop exactRankDrop
              (fresh := CapabilityKey.not_mem_of_fresh leftFresh' (by simp))
          rightCapabilities :=
            (((capabilities.preserveLedger.cons
                .independentRank independentRank
                (by intro packingIndex equality; cases equality)
                (by intro equality; cases equality)
                (by intro equality; cases equality)
                (fresh := by simpa using independentRankFresh)).cons
                .fullRankCertificate fullRankCertificate
                (by intro packingIndex equality; cases equality)
                (by intro equality; cases equality)
                (by intro equality; cases equality)
                (fresh := by simpa using fullRankCertificateFresh)).cons
              .fullRankExactCode fullRankMarker
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (fresh := by simpa using fullRankExactFresh)) }
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl index)))))))) =>
      let profile :
          Core.Strategy.Route8CarrierClosure.Profile
            Stage (Strategy.ProblemInput P) _ :=
        { registration := (data.route8CarrierClosures[index]).snd }
      { split := profile.dichotomy
        leftDirect := none
        -- Manuscript nodes [122] and [124].  The registration's own two
        -- refutations make the closure arm's payload uninhabited, so the arm
        -- terminates instead of being retained as an open branch endpoint.
        -- A registration leaving either slot `none` keeps the arm live.
        rightDirect :=
          profile.registration.tierImpossible.bind fun tier =>
            profile.registration.capacityImpossible.map fun demand =>
              fun _stage payload =>
                (profile.closureResidual_impossible tier.down demand.down
                  payload).elim
        leftProduced := []
        rightProduced := []
        leftProduced_eq := by
          simp [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view]
        rightProduced_eq := by
          simp [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view]
        leftCapabilities := capabilities.preserveLedger
        rightCapabilities := capabilities.preserveLedger }
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))))) => by
      have required :
          CapabilityKey.finiteStateCapacityContinuation ∈ available ∧
            CapabilityKey.finiteDensityCap ∈ available := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
          BinaryStrategyRef.key] using valid
      let profile :
          Core.Strategy.FiniteStateNetChargeContinuation.Profile
            Stage (Strategy.ProblemInput P) :=
        { Target := fun input => T.Predicate input.object
          registration := data.finiteStateNetChargeContinuation
          capacity := capabilities.capacityLedger required.1
          density := capabilities.capLedger required.2 }
      let split : Strategy.Dichotomy.{
          max uAmbient uBranch uData,
          max uAmbient uBranch uData,
          max uAmbient uBranch uData} Stage :=
        { LeftPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.TypeAResidual stage)
          RightPayload := fun stage =>
            ULift.{max uAmbient uBranch uData}
              (profile.TypeBResidual stage)
          classify := fun stage =>
            match profile.execution.run stage with
            | .inl typeA => .inl (ULift.up typeA)
            | .inr typeB => .inr (ULift.up typeB) }
      let leftDirect : Option (∀ stage, split.LeftPayload stage →
          PLift (T.Predicate
            (residualOf stage : Strategy.ProblemInput P).object)) :=
        none
      let rightDirect : Option (∀ stage, split.RightPayload stage →
          PLift (T.Predicate
            (residualOf stage : Strategy.ProblemInput P).object)) :=
        none
      exact
        { split := split
          leftDirect := leftDirect
          rightDirect := rightDirect
          leftProduced := []
          rightProduced := []
          leftProduced_eq := by
            simp [BinaryStrategyRef.leftProductions, BinaryStrategyRef.view]
          rightProduced_eq := by
            simp [BinaryStrategyRef.rightProductions, BinaryStrategyRef.view]
          leftCapabilities := capabilities.preserveLedger
          rightCapabilities := capabilities.preserveLedger }

private noncomputable def orderedSurplusActivationRecipe
    (registration :
      Core.Strategy.OrderedSurplusActivation.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData}
        (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.OrderedSurplusActivation.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData, uData, uData, uData, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration, current }
  { contract := profile.execution.toContract
    certify := fun _ _ => none }

private noncomputable def baselineDemandAccountingRecipe
    (registration :
      Core.Strategy.BaselineDemandAccounting.Registration.{
        max uAmbient uBranch, uData, uData, uData}
        (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.BaselineDemandAccounting.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData, uData, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration, current }
  { contract := profile.execution.toContract
    certify := fun _ _ => none }

private noncomputable def canonicalPairResponseAccountingRecipe
    (registration :
      Core.Strategy.CanonicalPairResponseAccounting.Registration.{
        max uAmbient uBranch, uData, uData}
        (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.CanonicalPairResponseAccounting.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration }
  let execution : Core.Strategy.CTExecution Stage :=
    profile.execution
  { contract := execution.toContract
    certify := fun _ _ => none }

private noncomputable def canonicalCapacityTokenAccountingRecipe
    (registration :
      Core.Strategy.CanonicalCapacityTokenAccounting.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData}
        (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.CanonicalCapacityTokenAccounting.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData, uData, uData, uData, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration }
  let execution : Core.Strategy.CTExecution Stage :=
    profile.execution
  { contract := execution.toContract
    certify := fun _ _ => none }

private noncomputable def coupledHomogeneousFibrePressureRecipe
    (registration :
      Core.Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData}
        (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P) :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.CoupledHomogeneousFibrePressure.Profile.{
        max (max uAmbient uBranch) uData,
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData}
        Stage (Strategy.ProblemInput P) :=
    { registration, current }
  let execution : Core.Strategy.CTExecution Stage :=
    profile.execution
  { contract := execution.toContract
    certify := fun _ _ => none }

/-! ### Registered dependent CT compositions

Each recipe receives one inert registration, obtains its exact predecessor
capability queries from the compiler-owned store, builds the already
implemented dependent profile, and lowers that profile's own contract or
dichotomy.  No CT is re-executed and no ledger entry is written here. -/

private abbrev HomogeneousBottleneckRegistration
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) :=
  Core.Strategy.HomogeneousBottleneck.Registration.{
    max uAmbient uBranch, uData}
    (Strategy.ProblemInput P) (fun input => T.Predicate input.object)

/-- Exact producer-indexed input to the homogeneous continuation.  The two
ledger fields force the registration to be compiled against the literal
coupled-pressure and finite-bottleneck producers selected by `StrategyData`. -/
private structure HomogeneousBottleneckContinuation
    (pressureRegistration :
      Core.Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData} (Strategy.ProblemInput P))
    (bottleneckRegistration :
      Core.Strategy.FiniteBottleneckClassification.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData} (Strategy.ProblemInput P))
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)] where
  registration :
    HomogeneousBottleneckRegistration.{uAmbient, uBranch, uData} P T
  overload :
    Core.Strategy.CoupledHomogeneousFibrePressure.OverloadLedger
      Stage (Strategy.ProblemInput P) pressureRegistration
  separator :
    Core.Strategy.FiniteBottleneckClassification.SeparatorLedger
      Stage (Strategy.ProblemInput P) bottleneckRegistration

/-- The registered nine-CT homogeneous-bottleneck composition.  Only its
target constructor certifies the problem target; all other routed residuals
remain live in the ordinary contract payload. -/
private noncomputable def homogeneousBottleneckRecipe
    (pressureRegistration :
      Core.Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData} (Strategy.ProblemInput P))
    (bottleneckRegistration :
      Core.Strategy.FiniteBottleneckClassification.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData} (Strategy.ProblemInput P))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage : Strategy.ProblemInput P).object)
    (continuation : HomogeneousBottleneckContinuation
      (T := T) pressureRegistration bottleneckRegistration Stage) :
    Recipe P T Stage :=
  let profile :=
    Core.Strategy.HomogeneousBottleneck.Profile.ofRegistrationAt
      (Previous := Stage) continuation.registration current
  let semantics :=
    Core.Strategy.HomogeneousBottleneck.Profile.semanticsOfProfile profile
  { contract := profile.contract semantics
    certify := fun stage payload =>
      match payload with
      | ⟨_, .target _ proof⟩ =>
          some (PLift.up (targetToRoot stage proof))
      | ⟨_, .exceptional _ _ identified⟩ =>
          match continuation.registration.exceptionalImpossible with
          | some impossible =>
              (profile.exceptionalSelected_false impossible.down
                identified).elim
          | none => none
      | ⟨_, .structured _ _ _⟩ => none
      | ⟨_, .bounded _ _ _ _⟩ => none }

/-- The literal ledger stage of one existing live homogeneous-bottleneck
output. -/
private abbrev HomogeneousBottleneckBranchStage
    (registration :
      HomogeneousBottleneckRegistration.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (terminal :
      Core.Strategy.HomogeneousBottleneck.Profile.Terminal) :=
  Ledger.Extension Stage (fun stage =>
    let profile :=
      Core.Strategy.HomogeneousBottleneck.Profile.ofRegistrationAt
        (Previous := Stage) registration current
    let semantics :=
      Core.Strategy.HomogeneousBottleneck.Profile.semanticsOfProfile profile
    profile.RoutedResidual semantics stage terminal)

/-- Compose the three live output continuations onto the exact payload
selected by the existing homogeneous-bottleneck contract. -/
private noncomputable def homogeneousBottleneckBranchesRecipe
    (pressureRegistration :
      Core.Strategy.CoupledHomogeneousFibrePressure.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData, uData} (Strategy.ProblemInput P))
    (bottleneckRegistration :
      Core.Strategy.FiniteBottleneckClassification.Registration.{
        max uAmbient uBranch, uData, uData, uData, uData, uData, uData,
        uData, uData} (Strategy.ProblemInput P))
    (registration :
      HomogeneousBottleneckRegistration.{uAmbient, uBranch, uData} P T)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (overload :
      Core.Strategy.CoupledHomogeneousFibrePressure.OverloadLedger
        Stage (Strategy.ProblemInput P) pressureRegistration)
    (separator :
      Core.Strategy.FiniteBottleneckClassification.SeparatorLedger
        Stage (Strategy.ProblemInput P) bottleneckRegistration)
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage : Strategy.ProblemInput P).object)
    (exceptional : Option (Recipe P T
      (HomogeneousBottleneckBranchStage registration Stage current
        .exceptional)))
    (structured : Option (Recipe P T
      (HomogeneousBottleneckBranchStage registration Stage current
        .structured)))
    (bounded : Option (Recipe P T
      (HomogeneousBottleneckBranchStage registration Stage current
        .bounded))) :
    Recipe P T Stage :=
  let _selectedOverload := overload.selected
  let _selectedSeparator := separator.selected
  let profile :=
    Core.Strategy.HomogeneousBottleneck.Profile.ofRegistrationAt
      (Previous := Stage) registration current
  let semantics :=
    Core.Strategy.HomogeneousBottleneck.Profile.semanticsOfProfile profile
  let Witness := profile.RoutedResidual semantics
  let ExceptionalWitness := fun stage => Witness stage .exceptional
  let StructuredWitness := fun stage => Witness stage .structured
  let BoundedWitness := fun stage => Witness stage .bounded
  /- The registered exceptional-vacuity fact, read as Core's ordinary direct
  branch closure.  This is the same mechanism `DichotomyData.closeLeft` and
  `closeRight` already supply for binary families; nothing here is specific to
  any application, and registrations that leave the field `none` keep a live
  exceptional output exactly as before. -/
  let exceptionalDirect :
      Option (∀ stage, ExceptionalWitness stage →
        PLift (T.Predicate
          (residualOf stage : Strategy.ProblemInput P).object)) :=
    registration.exceptionalImpossible.map fun impossible stage witness =>
      (Core.Strategy.HomogeneousBottleneck.Profile.exceptional_false
        (profile := profile) (semantics := semantics) (previous := stage)
        impossible.down witness).elim
  let Payload :
      Stage →
        Core.Strategy.HomogeneousBottleneck.Profile.Terminal →
          Type (max uAmbient uBranch uData) :=
    fun stage terminal =>
      match terminal with
      | .target => Witness stage .target
      | .exceptional =>
          sideType ExceptionalWitness exceptional stage
      | .structured =>
          sideType StructuredWitness structured stage
      | .bounded =>
          sideType BoundedWitness bounded stage
  let produce : ∀ stage, Sigma (Payload stage) := fun stage =>
    match (profile.contract semantics).produce stage with
    | ⟨.target, witness⟩ => ⟨.target, witness⟩
    | ⟨.exceptional, witness⟩ =>
        ⟨.exceptional,
          sideProduce ExceptionalWitness exceptional stage witness⟩
    | ⟨.structured, witness⟩ =>
        ⟨.structured,
          sideProduce StructuredWitness structured stage witness⟩
    | ⟨.bounded, witness⟩ =>
        ⟨.bounded,
          sideProduce BoundedWitness bounded stage witness⟩
  let contract : Contract Stage :=
    { Terminal :=
        Core.Strategy.HomogeneousBottleneck.Profile.Terminal
      Payload := Payload
      produce := produce
      exhaustive := fun stage => ⟨produce stage⟩ }
  let certify :
      ∀ stage, Sigma (Payload stage) →
        Option (PLift (T.Predicate
          (residualOf stage : Strategy.ProblemInput P).object)) :=
    fun stage payload =>
      match payload with
      | ⟨.target, .target _ proof⟩ =>
          some (PLift.up (targetToRoot stage proof))
      | ⟨.exceptional, branchPayload⟩ =>
          sideCertificate ExceptionalWitness exceptionalDirect exceptional
            stage branchPayload
      | ⟨.structured, branchPayload⟩ =>
          sideCertify StructuredWitness structured stage branchPayload
      | ⟨.bounded, branchPayload⟩ =>
          sideCertify BoundedWitness bounded stage branchPayload
  let closes : Option (PLift (
      ∀ stage payload, ∃ proof, certify stage payload = some proof)) :=
    match sideCloses ExceptionalWitness exceptionalDirect exceptional,
        sideCloses StructuredWitness none structured,
        sideCloses BoundedWitness none bounded with
    | some closesExceptional, some closesStructured, some closesBounded =>
        some ⟨by
          intro stage payload
          rcases payload with ⟨terminal, payload⟩
          cases terminal with
          | target =>
              cases payload with
              | target _ proof =>
                  exact ⟨PLift.up (targetToRoot stage proof), rfl⟩
          | exceptional =>
              obtain ⟨proof, certified⟩ :=
                closesExceptional.down stage payload
              exact ⟨proof, by
                simpa [certify, sideCertificate] using certified⟩
          | structured =>
              obtain ⟨proof, certified⟩ :=
                closesStructured.down stage payload
              exact ⟨proof, by
                simpa [certify, sideCertificate] using certified⟩
          | bounded =>
              obtain ⟨proof, certified⟩ :=
                closesBounded.down stage payload
              exact ⟨proof, by
                simpa [certify, sideCertificate] using certified⟩⟩
    | _, _, _ => none
  { contract, certify, closes }

private noncomputable def supportComplementProfile
    {packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics.{
        max uAmbient uBranch, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)}
    (registration :
      Core.Strategy.SupportComplementNormalization.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)
        packingSemantics)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (packingQuery : Query Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current stage))
        (packingSemantics.conflict (current stage))) :
    Core.Strategy.SupportComplementNormalization.Profile.{
      max uAmbient uBranch uData, max uAmbient uBranch}
      Stage (Strategy.ProblemInput P) :=
  Core.Strategy.SupportComplementNormalization.Profile.ofRegistrationAt
    (Previous := Stage) registration current packingQuery

private noncomputable def supportComplementSemantics
    {packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics.{
        max uAmbient uBranch, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)}
    (registration :
      Core.Strategy.SupportComplementNormalization.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)
        packingSemantics)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (packingQuery : Query Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current stage))
        (packingSemantics.conflict (current stage))) :
    (supportComplementProfile (T := T) registration Stage current
      packingQuery).Semantics :=
  Core.Strategy.SupportComplementNormalization.Profile.semanticsOfRegistrationAt
    (Previous := Stage) registration current packingQuery

/-- CT9 → CT14 → CT1 → CT6.  The registered target implication is the sole
certifying branch; the normalized branch stays live. -/
private noncomputable def supportComplementNormalizationRecipe
    {packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics.{
        max uAmbient uBranch, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)}
    (registration :
      Core.Strategy.SupportComplementNormalization.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)
        packingSemantics)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (packingQuery : Query Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current stage))
        (packingSemantics.conflict (current stage)))
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage).object) :
    Recipe P T Stage :=
  { contract :=
      (supportComplementProfile (T := T) registration Stage current
        packingQuery).contract
        (supportComplementSemantics (T := T) registration Stage current
          packingQuery)
    certify := fun stage payload =>
      match payload.snd with
      | .target _ proof => some (PLift.up ((targetToRoot stage) proof))
      | .normalized _ _ _ _ _ => none }

private noncomputable def normalizedSupportLedgerQuery
    {packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics.{
        max uAmbient uBranch, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)}
    (registration :
      Core.Strategy.SupportComplementNormalization.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)
        packingSemantics)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (packingQuery : Query Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current stage))
        (packingSemantics.conflict (current stage)))
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage).object) :
    let recipe :=
      supportComplementNormalizationRecipe (T := T) registration
        (Stage := Stage) current packingQuery targetToRoot
    Query
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (fun _ => Core.Strategy.SupportComplementNormalization.Summary) := by
  let recipe :=
    supportComplementNormalizationRecipe (T := T) registration
      (Stage := Stage) current packingQuery targetToRoot
  let Live :=
    HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  let latest : Query Live
      (fun live => Sigma (recipe.contract.Payload live.previous)) :=
    (Query.latest (Previous := Stage)
      (Added := fun stage => Sigma (recipe.contract.Payload stage))).comap
      (fun live : Live => live.toLedger)
  exact latest.map fun _ payload =>
    (supportComplementProfile (T := T) registration Stage current
      packingQuery).summaryOfRouted
      payload.snd

/-- Exact query-only structural ledger published by the same normalization
recipe as `normalizedSupportLedgerQuery`.  The live-stage proof eliminates
the target terminal; all remaining fields are projections of the literal
CT9--CT14--CT1--CT6 output. -/
private noncomputable def normalizedSupportExactLedger
    {packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics.{
        max uAmbient uBranch, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)}
    (registration :
      Core.Strategy.SupportComplementNormalization.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object)
        packingSemantics)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (packingQuery : Query Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current stage))
        (packingSemantics.conflict (current stage)))
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage).object) :
    let recipe :=
      supportComplementNormalizationRecipe (T := T) registration
        (Stage := Stage) current packingQuery targetToRoot
    Core.Strategy.SupportComplementNormalization.ExactLedger
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (Strategy.ProblemInput P)
      (fun live => registration.AmbientItem
        ((HaltingProgram.LiveExtension.preserveQuery (T := T) current) live)) := by
  let profile := supportComplementProfile (T := T) registration Stage current
    packingQuery
  let recipe := supportComplementNormalizationRecipe (T := T) registration
    (Stage := Stage) current packingQuery targetToRoot
  let Live := HaltingProgram.LiveExtension T Stage
    recipe.contract recipe.certify
  let routedAt (live : Live) := live.ledger.added.snd
  let targetImpossible (live : Live)
      {exact : profile.ExactOutput live.previous}
      {proof : T.Predicate (current live.previous).object}
      (selected : routedAt live = .target exact proof) : False := by
    have rejected := live.isLive
    change recipe.certify live.previous live.ledger.added = none at rejected
    change live.ledger.added.snd = .target exact proof at selected
    dsimp [recipe, supportComplementNormalizationRecipe] at rejected
    rw [selected] at rejected
    cases rejected
  let exactActiveAt (live : Live) :
      { exact : profile.ExactOutput live.previous //
        exact.output.snd.terminal = .activeLedger } :=
    match selected : routedAt live with
    | .target exact proof =>
        False.elim (targetImpossible live selected)
    | .normalized exact _ _ _ active => ⟨exact, active⟩
  let exactAt (live : Live) : profile.ExactOutput live.previous :=
    (exactActiveAt live).1
  let activeAt (live : Live) :
      (exactAt live).output.snd.terminal = .activeLedger :=
    (exactActiveAt live).2
  exact {
    Block := fun live =>
      packingSemantics.Occurrence (current live.previous)
    LocalPiece := fun live =>
      profile.core.LocalPiece live.previous (exactAt live).output.fst
    Failure := fun live =>
      profile.core.Failure live.previous (exactAt live).output.fst
    summary :=  fun live =>
      profile.summaryOfExact (exactAt live)
    partitionExact :=  fun live =>
      profile.summaryOfExact_selectedCount_add_complementCount_eq_ambientCount
        (exactAt live)
    selectedUniform :=  fun live =>
      Core.Strategy.SupportComplementNormalization.Profile.selectedCount_eq_coverCard_mul_packingCount
        registration current packingQuery (exactAt live)
    complementExact :=  fun live =>
      Core.Strategy.SupportComplementNormalization.Profile.coverCard_mul_packingCount_add_complementCount_eq_ambientCount
        registration current packingQuery (exactAt live)
    ambient :=  fun live =>
      registration.ambientSupport (current live.previous)
    selected :=  fun live =>
      profile.partition.selectedAtPrevious live.previous
        (exactAt live).output.fst.fst.fst
    blocks :=  fun live => by
      let packing := packingQuery live.previous
      letI := (packingSemantics.occurrences
        (current live.previous)).decEq
      exact Core.Finite.Enumeration.ofNodupList
        packing.selected packing.selected_nodup
    cover := fun live block => registration.cover
      (current live.previous) block
    selectedMembership := fun live item => by
      exact
        Core.Strategy.SupportComplementNormalization.Profile.ofRegistrationAt_mem_selectedAtPrevious_iff
          registration current packingQuery live.previous
          (exactAt live).output.fst.fst.fst item
    coverNodup :=  fun live block =>
      registration.coverNodup (current live.previous) block
    coverCardExact :=  fun live block => by
      change (registration.cover (current live.previous) block).length =
        profile.coverCard
          (exactAt live).output.fst.fst.fst.stage.previous
      rw [(exactAt live).output.fst.fst.fst.previous_eq]
      exact registration.cover_card (current live.previous) block
    coverDisjoint := fun live left leftMem right rightMem different => by
      apply List.disjoint_left.mpr
      intro item itemLeft itemRight
      have conflict := (registration.conflict_iff_shared_item
        (current live.previous) left right).mpr
          ⟨item, itemLeft, itemRight⟩
      exact (packingQuery live.previous).pairwiseCompatible
        leftMem rightMem different conflict
    complement :=  fun live =>
      profile.partition.complementAtPrevious live.previous
        (exactAt live).output.fst.fst.fst
    complementMembership := fun live item => by
      constructor
      · intro complementMem
        have characterized :=
          (Core.Strategy.SupportComplementNormalization.PartitionProfile.mem_complementAtPrevious_iff
            profile.partition live.previous
            (exactAt live).output.fst.fst.fst item).mp complementMem
        refine ⟨characterized.1, ?_⟩
        intro selectedMem
        have selected :=
          (Core.Strategy.SupportComplementNormalization.PartitionProfile.mem_selectedAtPrevious_iff
            profile.partition live.previous
            (exactAt live).output.fst.fst.fst item).mp selectedMem
        exact characterized.2 selected.2
      · rintro ⟨ambientMem, notSelectedMem⟩
        apply
          (Core.Strategy.SupportComplementNormalization.PartitionProfile.mem_complementAtPrevious_iff
            profile.partition live.previous
            (exactAt live).output.fst.fst.fst item).mpr
        refine ⟨ambientMem, ?_⟩
        intro selected
        apply notSelectedMem
        exact
          (Core.Strategy.SupportComplementNormalization.PartitionProfile.mem_selectedAtPrevious_iff
            profile.partition live.previous
            (exactAt live).output.fst.fst.fst item).mpr ⟨ambientMem, selected⟩
    localPieces :=  fun live =>
      profile.core.localPieces live.previous (exactAt live).output.fst
    active :=  fun live piece member =>
      Core.Strategy.SupportComplementNormalization.Profile.ExactOutput.noFailureAt
        (profile := profile) (exactAt live) (activeAt live) piece member }

/-- CT4 → CT14 over the exact normalized-support ledger. -/
private noncomputable def boundaryDemandAccountingRecipe
    {ResidualAmbient : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    {ambient : (input : Strategy.ProblemInput P) →
      Core.Finite.Enumeration (ResidualAmbient input)}
    {Block : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    {cover : (input : Strategy.ProblemInput P) → Block input →
      List (ResidualAmbient input)}
    (registration :
      Core.Strategy.BoundaryDemandAccounting.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData}
        (Strategy.ProblemInput P) ResidualAmbient ambient Block cover)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (normalizedSupportExact :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P)
          (fun stage => ResidualAmbient (current stage))) :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.BoundaryDemandAccounting.Profile.{
        max uAmbient uBranch uData, max uAmbient uBranch,
        max uAmbient uBranch uData, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData,
        max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P) :=
    Core.Strategy.BoundaryDemandAccounting.Profile.ofRegistrationAt
      registration current normalizedSupportExact
  { contract := profile.contract
    certify := fun _ _ => none }

private noncomputable def boundaryAccountingLedgerQuery
    {ResidualAmbient : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    {ambient : (input : Strategy.ProblemInput P) →
      Core.Finite.Enumeration (ResidualAmbient input)}
    {Block : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    {cover : (input : Strategy.ProblemInput P) → Block input →
      List (ResidualAmbient input)}
    (registration :
      Core.Strategy.BoundaryDemandAccounting.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData}
        (Strategy.ProblemInput P) ResidualAmbient ambient Block cover)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (normalizedSupportExact :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P)
          (fun stage => ResidualAmbient (current stage))) :
    let recipe :=
      boundaryDemandAccountingRecipe (T := T) registration current
        normalizedSupportExact
    Query
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (fun _ => Core.Strategy.BoundaryDemandAccounting.Summary) := by
  let profile :
      Core.Strategy.BoundaryDemandAccounting.Profile.{
        max uAmbient uBranch uData, max uAmbient uBranch,
        max uAmbient uBranch uData, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData,
        max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P) :=
    Core.Strategy.BoundaryDemandAccounting.Profile.ofRegistrationAt
      registration current normalizedSupportExact
  let recipe :=
    boundaryDemandAccountingRecipe (T := T) registration current
      normalizedSupportExact
  let Live :=
    HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  let latest : Query Live
      (fun live => Sigma (recipe.contract.Payload live.previous)) :=
    (Query.latest (Previous := Stage)
      (Added := fun stage => Sigma (recipe.contract.Payload stage))).comap
      (fun live : Live => live.toLedger)
  exact latest.map fun _ payload => profile.summaryOfOutput payload.snd

/-- The single CT14 local-supply bound over the exact accounting ledger. -/
private noncomputable def localSupplyLowerBoundRecipe
    {AmbientItem : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    (registration :
      Core.Strategy.LocalSupplyLowerBound.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData, uData, uData}
        (Strategy.ProblemInput P) AmbientItem)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P)
        (fun stage => AmbientItem (current stage)))
    (boundaryAccounting : Query Stage fun _ =>
      Core.Strategy.BoundaryDemandAccounting.Summary) :
    Recipe P T Stage :=
  { contract :=
      (Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
        (Previous := Stage) (Residual := Strategy.ProblemInput P) registration
        current normalizedSupport
        (boundaryAccounting.map fun _ summary =>
          ULift.up.{uData} summary)).contract
    certify := fun _ _ => none }

private noncomputable def localSupplyLedgerQuery
    {AmbientItem : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    (registration :
      Core.Strategy.LocalSupplyLowerBound.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData, uData, uData}
        (Strategy.ProblemInput P) AmbientItem)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P)
        (fun stage => AmbientItem (current stage)))
    (boundaryAccounting : Query Stage fun _ =>
      Core.Strategy.BoundaryDemandAccounting.Summary) :
    let recipe :=
      localSupplyLowerBoundRecipe (T := T) registration current normalizedSupport
        boundaryAccounting
    Query
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (fun _ => Core.Strategy.LocalSupplyLowerBound.Summary) := by
  let profile :=
    Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
      (Previous := Stage) (Residual := Strategy.ProblemInput P) registration
      current normalizedSupport
      (boundaryAccounting.map fun _ summary => ULift.up.{uData} summary)
  let recipe :=
    localSupplyLowerBoundRecipe (T := T) registration current normalizedSupport
      boundaryAccounting
  let Live :=
    HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  let latest : Query Live
      (fun live => Sigma (recipe.contract.Payload live.previous)) :=
    (Query.latest (Previous := Stage)
      (Added := fun stage => Sigma (recipe.contract.Payload stage))).comap
      (fun live : Live => live.toLedger)
  exact latest.map fun _ payload => profile.summaryOfResidual payload.snd

/-- Exact CT14 member carrier on the literal live successor.  The query is
the producer's own `localCells`, transported through Core's live extension;
no member family is rebuilt from the residual. -/
private noncomputable def localSupplyExactLedger
    {AmbientItem : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    (registration :
      Core.Strategy.LocalSupplyLowerBound.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData, uData, uData}
        (Strategy.ProblemInput P) AmbientItem)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P)
        (fun stage => AmbientItem (current stage)))
    (boundaryAccounting : Query Stage fun _ =>
      Core.Strategy.BoundaryDemandAccounting.Summary) :
    let recipe :=
      localSupplyLowerBoundRecipe (T := T) registration current normalizedSupport
        boundaryAccounting
    Core.Strategy.LocalSupplyLowerBound.ExactLedger.{
      max uAmbient uBranch uData, max uAmbient uBranch,
      uData}
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify)
      (Strategy.ProblemInput P)
      (fun live => registration.Member
        ((HaltingProgram.LiveExtension.preserveQuery (T := T) current) live)) := by
  let profile :=
    Core.Strategy.LocalSupplyLowerBound.Profile.ofRegistrationAt
      (Previous := Stage) (Residual := Strategy.ProblemInput P) registration
      current normalizedSupport
      (boundaryAccounting.map fun _ summary => ULift.up.{uData} summary)
  let recipe :=
    localSupplyLowerBoundRecipe (T := T) registration current normalizedSupport
      boundaryAccounting
  let Live :=
    HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify
  exact
    { members :=
        HaltingProgram.LiveExtension.preserveQuery
          (T := T) profile.localCells
      sourceResidual := Query.residual }

/-- CT10 → CT15 → CT16 lowered through Core's stage-indexed dichotomy router.
Both typed rank residuals stay live for the enclosing DAG. -/
private noncomputable def targetRelativeRankDichotomyRecipe
    {AmbientItem : Strategy.ProblemInput P →
      Type (max uAmbient uBranch uData)}
    {Coordinate : Strategy.ProblemInput P → Type uData}
    (registration :
      Core.Strategy.TargetRelativeRankDichotomy.Registration.{
        max uAmbient uBranch, max uAmbient uBranch uData, uData, uData,
        uData, uData, uData}
        (Strategy.ProblemInput P) AmbientItem Coordinate)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (normalizedSupport :
      Core.Strategy.SupportComplementNormalization.ExactLedger.{
        max uAmbient uBranch, max uAmbient uBranch uData,
        max uAmbient uBranch uData, max uAmbient uBranch uData}
        Stage (Strategy.ProblemInput P)
        (fun stage => AmbientItem (current stage)))
    (localSupply : Query Stage fun _ =>
      Core.Strategy.LocalSupplyLowerBound.Summary) :
    Recipe P T Stage :=
  let profile :=
    Core.Strategy.TargetRelativeRankDichotomy.Profile.ofRegistrationAt
      (Previous := Stage) (Residual := Strategy.ProblemInput P) registration
      current normalizedSupport
      (localSupply.map fun _ summary => ULift.up.{uData} summary)
  let split : Strategy.Dichotomy.{
      max uAmbient uBranch uData,
      max uAmbient uBranch uData,
      max uAmbient uBranch uData} Stage :=
    { LeftPayload := fun stage =>
        ULift.{max uAmbient uBranch uData} (profile.code.RankDropResidual stage)
      RightPayload := fun stage =>
        ULift.{max uAmbient uBranch uData} (profile.code.FullRankResidual stage)
      classify := fun stage =>
        match profile.dichotomy.classify stage with
        | .inl residual => .inl (ULift.up residual)
        | .inr residual => .inr (ULift.up residual) }
  routedDichotomyRecipe split none none none none

/-- One compiler-resolved vertex together with every exact typed capability
available on its live output.  Both fields are derived by Core. -/
private structure ResolvedVertex
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage)
    (output : List CapabilityKey) where
  recipe : Recipe P T Stage
  nextState : CapabilityState data
    (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify) :=
      state.live recipe
  capabilities : Core.Residual.ExactLedger (CapabilityCursor data)
    nextState.toCursor output

private noncomputable def preservingVertex
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage}
    {available : List CapabilityKey}
    (capabilities : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor available)
    (recipe : Recipe P T Stage) :
    ResolvedVertex P T data Stage state available :=
  { recipe
    nextState := state.live recipe
    capabilities := capabilities.preserveLive recipe }

private noncomputable def counterexampleLocalizationRecipe
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (registration :
      CounterexampleLocalizationData.{uAmbient, uBranch, uData} P T)
    (stateOf : (object : P.Ambient) → P.BranchState object)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage :=
  let Selected :=
    MinimalSelectionStage (T := T) registration.selection Stage
  let context :=
    MinimalSelectionStage.contextQuery (T := T) registration.selection
  let continuation : Recipe P T Selected :=
    { contract :=
        { Terminal := Strategy.CompletedTerminal
          Payload := fun selected _ =>
            ULift.{uData}
              (MinimalCounterexampleContext P T.Predicate
                registration.selection.progress)
          produce := fun selected =>
            ⟨.completed, ULift.up (context selected)⟩
          exhaustive := fun selected =>
            ⟨⟨.completed, ULift.up (context selected)⟩⟩ }
      certify := fun _ _ => none }
  minimalCounterexampleRecipe registration.selection data.targetDecidable
    stateOf continuation

private noncomputable def coldBranchAggregationRecipe
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (packingIndex : Fin data.obstructionPackingClosures.length)
    (reductionIndex : Fin data.counterexampleReductions.length)
    {HandoffSupport : Strategy.ProblemInput P → Type uData}
    (registration :
      Core.Strategy.ColdBranchAggregation.LedgerRegistration
        P T data.counterexampleReductions[reductionIndex].selection.progress
        data.counterexampleReductions[reductionIndex].interfaceReplacement
        data.obstructionPackingClosures[packingIndex] HandoffSupport)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (current : Query Stage fun _ => Strategy.ProblemInput P)
    (packed : Query Stage fun stage =>
      Core.Strategy.ObstructionPackingClosure.NonemptyPacking
        (data.obstructionPackingClosures[packingIndex].occurrences
          (current stage))
        (data.obstructionPackingClosures[packingIndex].conflict
          (current stage)))
    (barrierSummary : Query Stage fun _ =>
      Core.Strategy.FiniteBarrierEnumeration.Summary)
    (overflow : Core.Strategy.ColdBranchAggregation.OverflowLedger Stage)
    (exactClosure :
      Core.Strategy.InterfaceReplacement.ExactClosureQueries
        data.counterexampleReductions[reductionIndex].interfaceReplacement Stage)
    (handoffSupports : Query Stage fun stage =>
      Core.Finite.Enumeration
        (HandoffSupport (current stage)))
    (handoffAbsent : Option (PLift (∀ stage,
      (handoffSupports stage).values = [])))
    (activeObject : Query Stage fun stage =>
      (current stage).object = (exactClosure.context stage).G)
    (targetToRoot : Query Stage fun stage =>
      T.Predicate (current stage).object →
        T.Predicate (residualOf stage).object) :
    Recipe P T Stage :=
  let packing := packed.map fun _ value => value.packing
  let familyCapability := registration.atStage
    exactClosure current activeObject packing handoffSupports handoffAbsent
  let profile :
      Core.Strategy.ColdBranchAggregation.LedgerProfile.{
        max (max uAmbient uBranch) uData, max uAmbient uBranch,
        max uAmbient uBranch uData, max uAmbient uData,
        uData, uData, uData, uData}
        Stage (Strategy.ProblemInput P)
        (fun input => T.Predicate input.object)
        data.obstructionPackingClosures[packingIndex] :=
    { Owner := familyCapability.Owner
      family := familyCapability.family
      current := current
      packing := packing
      packing_nonempty := packed.dependentMap fun _ value =>
        value.selected_nonempty
      barrierSummary := barrierSummary
      overflow := overflow
      Closure := fun stage =>
        ULift.{uData}
          (Core.Strategy.InterfaceReplacement.ClosurePayload
            data.counterexampleReductions[reductionIndex].interfaceReplacement
            (exactClosure.context stage))
      closure := exactClosure.closure.map fun _ value => ULift.up value
      storedF1ForcesTarget := familyCapability.storedF1ForcesTarget
      classifiedStateForcesTarget := familyCapability.classifiedStateForcesTarget }
  { contract := profile.execution.toContract
    /- Follows `obstructionPackingRecipe` above: the registered cold outcome
    already carries the target in its right branch, so certification is the
    projection of that branch through `targetToRoot`. -/
    certify := fun stage payload =>
      match payload.snd with
      | Sum.inl _ => none
      | Sum.inr target => some ⟨(targetToRoot stage) target.down⟩ }

private noncomputable def finiteStateNetChargeContinuationRecipe
    (registration :
      Core.Strategy.FiniteStateNetChargeContinuation.Registration
        (Strategy.ProblemInput P) (fun input => T.Predicate input.object))
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (capacity :
      Core.Strategy.FiniteStateNetChargeContinuation.CapacityLedger Stage)
    (density : Core.Strategy.FiniteDensityBudget.CapLedger Stage) :
    Recipe P T Stage :=
  let profile :
      Core.Strategy.FiniteStateNetChargeContinuation.Profile.{
        max uAmbient uBranch uData, max uAmbient uBranch}
        Stage (Strategy.ProblemInput P) :=
    { Target := fun input => T.Predicate input.object
      registration, capacity, density }
  { contract := profile.execution.toContract
    certify := fun _ _ => none }

private noncomputable def minimalCounterexampleStep
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (stateOf : (G : P.Ambient) -> P.BranchState G)
    (index : Fin data.counterexampleReductions.length)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage :=
  let reduction := data.counterexampleReductions[index]
  let Selected := MinimalSelectionStage (T := T) reduction.selection Stage
  let context : Query Selected fun _ =>
      MinimalCounterexampleContext P T.Predicate
        reduction.selection.progress :=
     fun selected => selected.ledger.added.context
  let ContextPayload :=
    MinimalCounterexampleContext P T.Predicate reduction.selection.progress
  let ClosurePayload :=
    InterfaceReplacement.UncompressibleStage
      reduction.interfaceReplacement
      (Strategy.CounterexampleReduction.contextAfterCritical
        reduction context)
  let continuation : Recipe P T Selected :=
    { contract :=
        { Terminal := Strategy.CompletedTerminal
          Payload := fun selected _ =>
            ULift.{uData} (ContextPayload × ClosurePayload)
          produce := fun selected =>
            ⟨.completed,
              ULift.up
                ⟨context selected,
                  InterfaceReplacement.closure reduction.interfaceReplacement
                    (Strategy.CounterexampleReduction.contextAfterCritical
                      reduction context)
                    (Strategy.CounterexampleReduction.execute
                      reduction context selected)⟩⟩
          exhaustive := fun selected =>
            ⟨⟨.completed,
              ULift.up
                ⟨context selected,
                  InterfaceReplacement.closure reduction.interfaceReplacement
                    (Strategy.CounterexampleReduction.contextAfterCritical
                      reduction context)
                    (Strategy.CounterexampleReduction.execute
                      reduction context selected)⟩⟩⟩ }
      certify := fun _ _ => none }
  minimalCounterexampleRecipe reduction.selection data.targetDecidable stateOf
    continuation


/-- Resolve one official key against registered data and the literal
predecessor ledger capabilities.  Family access and every required query are
total by sealed proofs produced before executable lowering. -/
private noncomputable def resolveVertex
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (stateOf : (object : P.Ambient) → P.BranchState object)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage}
    {input : List CapabilityKey}
    (capabilities : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor input) :
    (key : StrategyKey) → (resolved : key.ResolvedIn data) →
      key.requirementsMet data resolved input = true →
      CapabilityKey.fresh (key.productions data resolved) input = true →
      ResolvedVertex P T data Stage state
        (key.productions data resolved ++ input)
  | .orderedWitnessScan index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (scanRecipe (data.scans[index]'resolved))
  | .responseClassifier index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (responseRecipe (data.responses[index]'resolved))
  | .capacityLedger index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (capacityRecipe (data.capacities[index]'resolved))
  | .supportLocalization index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (localizationRecipe (data.localizations[index]'resolved))
  | .rankBudget index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (rankBudgetRecipe (data.rankBudgets[index]'resolved))
  | .closedCode index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (closedCodeRecipe (data.closedCodes[index]'resolved))
  | .dichotomy index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (routedRecipe (data.dichotomies[index]'resolved) none none)
  | .obstructionPackingClosure index, resolved =>
      fun valid fresh =>
      let packingIndex : Fin data.obstructionPackingClosures.length :=
        ⟨index, resolved⟩
      let semantics := data.obstructionPackingClosures[packingIndex]
      have required : CapabilityKey.minimalContext ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid
      let current := capabilities.activeInput
      let targetToRoot := capabilities.targetToRoot
      let recipe := obstructionPackingRecipe (T := T) semantics current
        targetToRoot
      have factFresh : CapabilityKey.obstructionPacking index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          (capabilities.preserveLive recipe).consPacking packingIndex
            (obstructionPackingQuery (T := T) semantics current targetToRoot)
            (fresh := by simpa [packingIndex] using factFresh)
      }
  | .exactFiniteLocalAlgebra index, resolved =>
      fun _ fresh =>
      let registration := data.exactFiniteLocalAlgebras[index]'resolved
      let recipe := exactFiniteLocalAlgebraRecipe (T := T) registration
      {
        recipe
        capabilities :=
          (capabilities.preserveLive recipe).cons .exactFiniteLocalCode
            (exactFiniteLocalCodeQuery (T := T) registration)
            (by intro _ equality; cases equality)
            (by intro equality; cases equality)
            (by intro equality; cases equality)
            (fresh := CapabilityKey.not_mem_of_fresh fresh (by
              simp [StrategyKey.productions]))
      }
  | .finiteBarrierEnumeration index, resolved =>
      fun valid fresh =>
      have required : CapabilityKey.exactFiniteLocalCode ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid
      let registration := data.finiteBarrierEnumerations[index]'resolved
      let sourceCode := capabilities.query .exactFiniteLocalCode required
      let recipe := finiteBarrierEnumerationRecipe (T := T) registration
        sourceCode capabilities.activeInput
      have factFresh : CapabilityKey.finiteBarrierSummary ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          (capabilities.preserveLive recipe).consBarrierRate
            (finiteBarrierRateLedger (T := T) registration
              sourceCode capabilities.activeInput)
            (fresh := factFresh)
      }
  | .finiteDensityBudget index, resolved =>
      fun valid fresh =>
      have required :
          CapabilityKey.obstructionPacking 0 ∈ input ∧
            CapabilityKey.finiteBarrierSummary ∈ input ∧
            CapabilityKey.nearCubicSpine 0 ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid
      let nearCubicIndex : Fin data.scaleThresholdDichotomies.length :=
        ⟨0, capabilities.nearCubicIndexValid 0 required.2.2⟩
      let degreeSurplusLoad : Query Stage fun _ => Nat :=
         fun stage =>
          data.scaleThresholdDichotomies[nearCubicIndex].load
            (capabilities.activeInput stage)
      let degreeSurplusThreshold : Query Stage fun _ => Nat :=
         fun stage =>
          (data.scaleThresholdDichotomies[nearCubicIndex].table
            (capabilities.activeInput stage)).threshold
            (data.scaleThresholdDichotomies[nearCubicIndex].size
              (capabilities.activeInput stage))
      let recipe := finiteDensityBudgetRecipe
        (T := T) (data.finiteDensityBudgets[index]'resolved)
        (capabilities.packingCountQuery 0 required.1)
        (capabilities.barrierRate required.2.1)
        degreeSurplusLoad degreeSurplusThreshold
        (capabilities.nearCubicSpine nearCubicIndex required.2.2)
      preservingVertex data capabilities recipe
  | .finiteStateCapacity index, resolved =>
      fun valid fresh =>
        let entry := data.finiteStateCapacities[index]'resolved
        let supplyIndex := entry.fst
        have required :
            CapabilityKey.independentRank ∈ input ∧
              CapabilityKey.finiteBarrierSummary ∈ input ∧
              CapabilityKey.fullRankCertificate ∈ input ∧
              CapabilityKey.localSupplyLedger supplyIndex ∈ input := by
          simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
            entry, supplyIndex] using valid
      let supplyCapability :=
        capabilities.localSupplyExact supplyIndex required.2.2.2
      let profile :
          Core.Strategy.FiniteStateCapacity.Profile
            Stage (Strategy.ProblemInput P) :=
        { AmbientItem := data.localSupplyLowerBounds[supplyIndex].AmbientItem
          registration := entry.snd
          current := capabilities.activeInput
          complement := supplyCapability.normalized.complement
          fullRankCertificate :=
            capabilities.query .fullRankCertificate required.2.2.1
          independentRank := capabilities.query .independentRank required.1
          finiteBarrierSummary :=
            capabilities.query .finiteBarrierSummary required.2.1
          localSupply :=
            capabilities.query (.localSupplyLedger supplyIndex) required.2.2.2 }
      preservingVertex data capabilities
        (routedDichotomyRecipe profile.dichotomy none none none none)
  | .finiteScheduleCapacity index, resolved =>
      fun _ _ =>
      let profile :
          Core.Strategy.FiniteScheduleCapacity.Profile
            Stage (Strategy.ProblemInput P) :=
        { registration := data.finiteScheduleCapacities[index]'resolved
          current := capabilities.activeInput }
      preservingVertex data capabilities
        (routedDichotomyRecipe profile.dichotomy none none none none)
  | .route8CarrierClosure index, resolved =>
      fun _ _ =>
      let profile :
          Core.Strategy.Route8CarrierClosure.Profile
            Stage (Strategy.ProblemInput P) _ :=
        { registration := (data.route8CarrierClosures[index]'resolved).snd }
      -- Manuscript nodes [122] and [124].  Both of Figure 9's terminal
      -- ellipses sit on the closure arm, and a registration that supplies both
      -- refutations makes that payload uninhabited, so the arm is eliminated
      -- rather than retained as an open leaf.  A registration that leaves
      -- either slot `none` keeps the arm live, which is the same discipline
      -- every other closure slot in this file follows.
      preservingVertex data capabilities
        (routedDichotomyRecipe profile.dichotomy none
          (profile.registration.tierImpossible.bind fun tier =>
            profile.registration.capacityImpossible.map fun demand =>
              fun _stage payload =>
                (profile.closureResidual_impossible tier.down demand.down
                  payload).elim)
          none none)
  | .scaleThresholdDichotomy index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (scaleThresholdRecipe
          (data.scaleThresholdDichotomies[index]'resolved))
  | .atomContextObstructionDichotomy index, resolved =>
      fun _ _ =>
      let registered := data.atomContextObstructionDichotomies[index]'resolved
      preservingVertex data capabilities
        (atomContextObstructionRecipe registered.registration)
  | .orderedSurplusActivation index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (orderedSurplusActivationRecipe
          (data.orderedSurplusActivations[index]'resolved)
          capabilities.activeInput)
  | .baselineDemandAccounting index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (baselineDemandAccountingRecipe
          (data.baselineDemandAccountings[index]'resolved)
          capabilities.activeInput)
  | .canonicalPairResponseAccounting index, resolved =>
      fun _ fresh =>
      let registration := data.canonicalPairResponseAccountings[index]'resolved
      let profile :
          Core.Strategy.CanonicalPairResponseAccounting.Profile
        Stage (Strategy.ProblemInput P) :=
        { registration, current := capabilities.activeInput }
      let execution : Core.Strategy.CTExecution Stage := profile.execution
      let recipe : Recipe P T Stage :=
        { contract := execution.toContract
          certify := fun _ _ => none }
      let output := execution.liveOutputQuery recipe.certify
      let dependence := output.map fun _ result => result.fst.terminal
      let role := output.map fun _ result => result.snd.terminal
      let inherited := capabilities.preserveLive recipe
      have dependenceFresh : CapabilityKey.canonicalPairDependence index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have roleFresh : CapabilityKey.canonicalPairRole index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          (inherited.cons (.canonicalPairRole index) role
            (by intro packingIndex equality; cases equality)
            (by intro equality; cases equality)
            (by intro equality; cases equality)
            (notNormalized := by simp)
            (notLocalSupply := by simp)
            (notMinimalContext := by simp)
            (fresh := by simpa using roleFresh)).cons
              (.canonicalPairDependence index) dependence
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (notNormalized := by simp)
              (notLocalSupply := by simp)
              (notMinimalContext := by simp)
              (fresh := by simpa using dependenceFresh)
      }
  | .canonicalCapacityTokenAccounting index, resolved =>
      fun _ fresh =>
      let registration := data.canonicalCapacityTokenAccountings[index]'resolved
      let profile :
          Core.Strategy.CanonicalCapacityTokenAccounting.Profile
            Stage (Strategy.ProblemInput P) :=
        { registration, current := capabilities.activeInput }
      let execution : Core.Strategy.CTExecution Stage := profile.execution
      let recipe : Recipe P T Stage :=
        { contract := execution.toContract
          certify := fun _ _ => none }
      let output := execution.liveOutputQuery recipe.certify
      let assignment := output.map fun _ result => result.fst.terminal
      let fibre := output.map fun _ result => result.snd.fst.terminal
      let aggregate := output.map fun _ result => result.snd.snd.terminal
      let inherited := capabilities.preserveLive recipe
      have assignmentFresh :
          CapabilityKey.canonicalCapacityAssignment index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have fibreFresh : CapabilityKey.canonicalCapacityFibre index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have aggregateFresh :
          CapabilityKey.canonicalCapacityAggregate index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          ((inherited.cons (.canonicalCapacityAggregate index) aggregate
            (by intro packingIndex equality; cases equality)
            (by intro equality; cases equality)
            (by intro equality; cases equality)
            (notNormalized := by simp)
            (notLocalSupply := by simp)
            (notMinimalContext := by simp)
            (fresh := by simpa using aggregateFresh)).cons
              (.canonicalCapacityFibre index) fibre
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (notNormalized := by simp)
              (notLocalSupply := by simp)
              (notMinimalContext := by simp)
              (fresh := by simpa using fibreFresh)).cons
                (.canonicalCapacityAssignment index) assignment
                (by intro packingIndex equality; cases equality)
                (by intro equality; cases equality)
                (by intro equality; cases equality)
                (notNormalized := by simp)
                (notLocalSupply := by simp)
                (notMinimalContext := by simp)
                (fresh := by simpa using assignmentFresh)
      }
  | .coupledHomogeneousFibrePressure index, resolved =>
      fun _ fresh =>
      let producerIndex : Fin data.coupledHomogeneousFibrePressures.length :=
        ⟨index, resolved⟩
      let registration := data.coupledHomogeneousFibrePressures[producerIndex]
      let profile :
          Core.Strategy.CoupledHomogeneousFibrePressure.Profile
            Stage (Strategy.ProblemInput P) :=
        { registration
          current := capabilities.activeInput }
      let execution : Core.Strategy.CTExecution Stage := profile.execution
      let recipe : Recipe P T Stage :=
        { contract := execution.toContract
          certify := fun _ _ => none }
      let output := execution.liveOutputQuery recipe.certify
      let overload := output.map fun _ result => result.fst.terminal
      let overloadExact := profile.overloadLedgerLive recipe.certify
      let reconciliation := output.map fun _ result => result.snd.fst.terminal
      let pressure := output.map fun _ result => result.snd.snd.terminal
      let inherited := capabilities.preserveLive recipe
      have overloadFresh : CapabilityKey.homogeneousPressureOverload index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have reconciliationFresh :
          CapabilityKey.homogeneousPressureReconciliation index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have aggregateFresh :
          CapabilityKey.homogeneousPressureAggregate index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          ((inherited.cons (.homogeneousPressureAggregate index) pressure
            (by intro packingIndex equality; cases equality)
            (by intro equality; cases equality)
            (by intro equality; cases equality)
            (notNormalized := by simp)
            (notLocalSupply := by simp)
            (notMinimalContext := by simp)
            (fresh := by simpa using aggregateFresh)).cons
              (.homogeneousPressureReconciliation index) reconciliation
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (notNormalized := by simp)
            (notLocalSupply := by simp)
            (notMinimalContext := by simp)
            (fresh := by simpa using reconciliationFresh)).consHomogeneousPressureOverload
                producerIndex overload overloadExact (fun _ => rfl)
                (fresh := by simpa [producerIndex] using overloadFresh)
      }
  | .finiteBottleneckClassification index, resolved =>
      fun valid fresh =>
      let producerIndex : Fin data.finiteBottleneckClassifications.length :=
        ⟨index, resolved⟩
      let entry := data.finiteBottleneckClassifications[producerIndex]
      let pressureIndex := entry.fst
      let registration := entry.snd
      have required :
          CapabilityKey.homogeneousPressureOverload pressureIndex ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
          producerIndex, entry, pressureIndex] using valid
      let overloadCapability :=
        capabilities.homogeneousPressureOverloadExact pressureIndex required
      let overloadExact := overloadCapability.ledger
      let continuation :
          Core.Strategy.FiniteBottleneckClassification.ContinuationProfile
            Stage (Strategy.ProblemInput P)
              data.coupledHomogeneousFibrePressures[pressureIndex] :=
        { registration, overload := overloadExact }
      let profile := continuation.base
      let execution : Core.Strategy.CTExecution Stage := continuation.execution
      let recipe : Recipe P T Stage :=
        { contract := execution.toContract
          certify := fun _ _ => none }
      let output := execution.liveOutputQuery recipe.certify
      let collision := output.map fun _ result => result.fst.terminal
      let pressure := output.map fun _ result => result.snd.fst.terminal
      let classification :=
        output.map fun _ result => result.snd.snd.fst.terminal
      let separator := output.map fun _ result => result.snd.snd.snd.terminal
      let separatorExact := profile.separatorLedgerLive recipe.certify
      let inherited := capabilities.preserveLive recipe
      have collisionFresh : CapabilityKey.bottleneckCollision index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have pressureFresh : CapabilityKey.bottleneckPressure index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have classificationFresh :
          CapabilityKey.bottleneckClassification index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      have separatorFresh : CapabilityKey.bottleneckSeparator index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          (((inherited.consBottleneckSeparator producerIndex separator
            separatorExact
              (fun live => overloadCapability.current_eq live.previous)
              (fresh := by simpa [producerIndex] using separatorFresh)).cons
              (.bottleneckClassification index) classification
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (notNormalized := by simp)
              (notLocalSupply := by simp)
              (notMinimalContext := by simp)
              (fresh := by simpa using classificationFresh)).cons
                (.bottleneckPressure index) pressure
                (by intro packingIndex equality; cases equality)
                (by intro equality; cases equality)
                (by intro equality; cases equality)
                (notNormalized := by simp)
                (notLocalSupply := by simp)
                (notMinimalContext := by simp)
                (fresh := by simpa using pressureFresh)).cons
                  (.bottleneckCollision index) collision
                  (by intro packingIndex equality; cases equality)
                  (by intro equality; cases equality)
                  (by intro equality; cases equality)
                  (notNormalized := by simp)
                  (notLocalSupply := by simp)
                  (notMinimalContext := by simp)
                  (fresh := by simpa using collisionFresh)
      }
  | .homogeneousBottleneck index, resolved =>
      fun valid fresh =>
      let producerIndex : Fin data.homogeneousBottlenecks.length :=
        ⟨index, resolved⟩
      let entry := data.homogeneousBottlenecks[producerIndex]
      let bottleneckIndex := entry.fst
      let pressureIndex :=
        data.finiteBottleneckClassifications[bottleneckIndex].fst
      have required :
          CapabilityKey.canonicalPairDependence pressureIndex ∈ input ∧
          CapabilityKey.canonicalPairRole pressureIndex ∈ input ∧
          CapabilityKey.canonicalCapacityAssignment pressureIndex ∈ input ∧
          CapabilityKey.canonicalCapacityFibre pressureIndex ∈ input ∧
          CapabilityKey.canonicalCapacityAggregate pressureIndex ∈ input ∧
          CapabilityKey.homogeneousPressureOverload pressureIndex ∈ input ∧
          CapabilityKey.homogeneousPressureReconciliation pressureIndex ∈ input ∧
          CapabilityKey.homogeneousPressureAggregate pressureIndex ∈ input ∧
          CapabilityKey.bottleneckCollision bottleneckIndex ∈ input ∧
          CapabilityKey.bottleneckPressure bottleneckIndex ∈ input ∧
          CapabilityKey.bottleneckClassification bottleneckIndex ∈ input ∧
          CapabilityKey.bottleneckSeparator bottleneckIndex ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
          producerIndex, entry, bottleneckIndex, pressureIndex] using valid
      let overloadExact :=
        capabilities.homogeneousPressureOverloadExact pressureIndex
          required.2.2.2.2.2.1 |>.ledger
      let separatorExact :=
        capabilities.bottleneckSeparatorExact bottleneckIndex
          required.2.2.2.2.2.2.2.2.2.2.2 |>.ledger
      preservingVertex data capabilities
        (homogeneousBottleneckRecipe
          data.coupledHomogeneousFibrePressures[pressureIndex]
          data.finiteBottleneckClassifications[bottleneckIndex].snd
          capabilities.activeInput capabilities.targetToRoot
          { registration := entry.snd
            overload := overloadExact
            separator := separatorExact })
  | .supportComplementNormalization index, resolved =>
      fun valid fresh =>
      let producerIndex : Fin data.supportComplementNormalizations.length :=
        ⟨index, resolved⟩
      let packed := data.supportComplementNormalizations[index]'producerIndex.isLt
      let packingIndex := packed.fst
      let registration := packed.snd
      have valid' : StrategyKey.requirementsMet data
          (.supportComplementNormalization index) producerIndex.isLt input = true := by
        simpa only using valid
      have required :
          CapabilityKey.obstructionPacking packingIndex ∈ input ∧
            CapabilityKey.finiteDensityCap ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
          packed, packingIndex] using valid'
      let packedQuery := capabilities.packingQuery packingIndex required.1
      let packing := packedQuery.map
        fun _ value => value.packing
      let current := capabilities.activeInput
      let targetToRoot := capabilities.targetToRoot
      let recipe :=
        supportComplementNormalizationRecipe (T := T) registration current
          packing targetToRoot
      have factFresh : CapabilityKey.normalizedSupportLedger index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          (capabilities.preserveLive recipe).consNormalizedSupport
            producerIndex
            (normalizedSupportLedgerQuery (T := T) registration current packing
              targetToRoot)
            { exact := normalizedSupportExactLedger (T := T) registration
                current packing targetToRoot
              densityCap := (capabilities.capLedger required.2).comap
                (fun live : HaltingProgram.LiveExtension T Stage
                  recipe.contract recipe.certify => live.toLedger.previous) }
            (fresh := by simpa [producerIndex] using factFresh)
      }
  | .boundaryDemandAccounting index, resolved =>
      fun valid fresh =>
      let packed := data.boundaryDemandAccountings[index]'resolved
      let supportIndex := packed.fst
      have required :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid
      let registration := packed.snd
      let supportCapability :=
        capabilities.normalizedSupportExact supportIndex required
      let recipe :=
        boundaryDemandAccountingRecipe (T := T) registration
          capabilities.activeInput supportCapability.exact
      have factFresh : CapabilityKey.boundaryAccountingLedger ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      { recipe
        capabilities :=
          (capabilities.preserveLive recipe).cons
            .boundaryAccountingLedger
            (boundaryAccountingLedgerQuery (T := T) registration
              capabilities.activeInput supportCapability.exact)
            (by intro packingIndex equality; cases equality)
            (by intro equality; cases equality)
            (by intro equality; cases equality)
            (fresh := factFresh) }
  | .localSupplyLowerBound index, resolved =>
      fun valid fresh =>
      let producerIndex : Fin data.localSupplyLowerBounds.length :=
        ⟨index, resolved⟩
      let packed := data.localSupplyLowerBounds[index]'producerIndex.isLt
      let boundaryIndex := packed.fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      have valid' : StrategyKey.requirementsMet data
          (.localSupplyLowerBound index) producerIndex.isLt input = true := by
        simpa only using valid
      have requiredRaw :
          CapabilityKey.normalizedSupportLedger
              data.boundaryDemandAccountings[
                data.localSupplyLowerBounds[index]'producerIndex.isLt |>.fst].fst ∈
                input ∧ CapabilityKey.boundaryAccountingLedger ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid'
      have requiredSupport :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ input := by
        simpa [packed, boundaryIndex, supportIndex] using requiredRaw.1
      let registration := packed.snd
      let accounting := capabilities.query .boundaryAccountingLedger requiredRaw.2
      let support :=
        capabilities.normalizedSupportExact supportIndex requiredSupport
      let recipe :=
        localSupplyLowerBoundRecipe (T := T) registration
          capabilities.activeInput support.exact accounting
      have factFresh : CapabilityKey.localSupplyLedger index ∉ input :=
        CapabilityKey.not_mem_of_fresh fresh (by
          simp [StrategyKey.productions])
      {
        recipe
        capabilities :=
          (capabilities.preserveLive recipe).consLocalSupply
            producerIndex
            (localSupplyLedgerQuery (T := T) registration
              capabilities.activeInput support.exact accounting)
            { normalized := support.exact.comap
                (fun live : HaltingProgram.LiveExtension T Stage
                  recipe.contract recipe.certify => live.toLedger.previous)
                (fun _ => rfl)
              exact := localSupplyExactLedger (T := T) registration
                capabilities.activeInput support.exact accounting }
            (fresh := by simpa [producerIndex] using factFresh)
      }
  | .targetRelativeRankDichotomy index, resolved =>
      fun valid fresh =>
      let producerIndex : Fin data.targetRelativeRankDichotomies.length :=
        ⟨index, resolved⟩
      let packed := data.targetRelativeRankDichotomies[index]'producerIndex.isLt
      let supplyIndex := packed.snd.fst
      let boundaryIndex := data.localSupplyLowerBounds[supplyIndex].fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      have valid' : StrategyKey.requirementsMet data
          (.targetRelativeRankDichotomy index) producerIndex.isLt input = true := by
        simpa only using valid
      have requiredRaw :
          let packedRaw :=
            data.targetRelativeRankDichotomies[index]'producerIndex.isLt
          let supplyRaw := packedRaw.snd.fst
          let boundaryRaw := data.localSupplyLowerBounds[supplyRaw].fst
          let supportRaw := data.boundaryDemandAccountings[boundaryRaw].fst
          CapabilityKey.normalizedSupportLedger supportRaw ∈ input ∧
            CapabilityKey.localSupplyLedger supplyRaw ∈ input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using valid'
      have requiredSupport :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ input := by
        simpa [packed, supplyIndex, boundaryIndex, supportIndex] using requiredRaw.1
      have requiredSupply :
          CapabilityKey.localSupplyLedger supplyIndex ∈ input := by
        simpa [packed, supplyIndex] using requiredRaw.2
      let supplyCapability :=
        capabilities.localSupplyExact supplyIndex requiredSupply
      preservingVertex data capabilities
        (targetRelativeRankDichotomyRecipe (T := T)
          packed.snd.snd
          capabilities.activeInput supplyCapability.normalized
          (capabilities.query (.localSupplyLedger supplyIndex) requiredSupply))
  | .compressionLinkedTargetRelativeRankDichotomy index, resolved =>
      fun valid fresh =>
      let producerIndex :
          Fin data.compressionLinkedTargetRelativeRankDichotomies.length :=
        ⟨index, resolved⟩
      let packed :=
        data.compressionLinkedTargetRelativeRankDichotomies[index]'
          producerIndex.isLt
      let supplyIndex := packed.snd.fst
      let boundaryIndex := data.localSupplyLowerBounds[supplyIndex].fst
      let supportIndex := data.boundaryDemandAccountings[boundaryIndex].fst
      have valid' : StrategyKey.requirementsMet data
          (.compressionLinkedTargetRelativeRankDichotomy index)
          producerIndex.isLt input = true := by
        simpa only using valid
      have requiredRaw :
          let packedRaw :=
            data.compressionLinkedTargetRelativeRankDichotomies[index]'
              producerIndex.isLt
          let supplyRaw := packedRaw.snd.fst
          let boundaryRaw := data.localSupplyLowerBounds[supplyRaw].fst
          let supportRaw := data.boundaryDemandAccountings[boundaryRaw].fst
          CapabilityKey.normalizedSupportLedger supportRaw ∈ input ∧
            CapabilityKey.localSupplyLedger supplyRaw ∈ input ∧
              CapabilityKey.minimalClosureAt packedRaw.reductionIndex ∈
                input := by
        simpa [StrategyKey.requirementsMet, StrategyKey.requirements]
          using valid'
      have requiredSupport :
          CapabilityKey.normalizedSupportLedger supportIndex ∈ input := by
        simpa [packed, supplyIndex, boundaryIndex, supportIndex]
          using requiredRaw.1
      have requiredSupply :
          CapabilityKey.localSupplyLedger supplyIndex ∈ input := by
        simpa [packed, supplyIndex] using requiredRaw.2.1
      let supplyCapability :=
        capabilities.localSupplyExact supplyIndex requiredSupply
      preservingVertex data capabilities
        (targetRelativeRankDichotomyRecipe (T := T)
          (Core.Strategy.TargetRelativeRankDichotomy.FixedRegistration.toRegistration
            packed.snd.base _ packed.snd.fixed)
          capabilities.activeInput supplyCapability.normalized
          (capabilities.query (.localSupplyLedger supplyIndex) requiredSupply))
  | .counterexampleLocalization index, resolved =>
      fun _ _ => preservingVertex data capabilities
        (counterexampleLocalizationRecipe data
          (data.counterexampleLocalizations[index]'resolved) stateOf)
  | .coldBranchAggregation index, resolved =>
      fun valid fresh =>
        let packed := data.coldBranchAggregations[index]'resolved
        let reductionIndex := packed.reductionIndex
        let packingIndex := packed.fst
        let handoffIndex := packed.handoffIndex
        let pressureIndex :=
          data.homogeneousBottlenecks[handoffIndex].pressureIndex
        let bottleneckIndex := data.homogeneousBottlenecks[handoffIndex].fst
        let registration := packed.snd
        if handoffLive : packed.handoffRequired then
          have full :
              CapabilityKey.obstructionPacking packingIndex ∈ input ∧
                CapabilityKey.finiteBarrierSummary ∈ input ∧
                CapabilityKey.finiteDensityOverflow ∈ input ∧
                CapabilityKey.minimalClosureAt reductionIndex ∈ input ∧
                CapabilityKey.homogeneousHandoff handoffIndex ∈ input ∧
                CapabilityKey.homogeneousPressureOverload pressureIndex ∈
                  input ∧
                CapabilityKey.bottleneckSeparator bottleneckIndex ∈ input := by
            simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
              packed, packingIndex, handoffIndex, pressureIndex,
              bottleneckIndex, reductionIndex, handoffLive] using valid
          preservingVertex data capabilities
            (coldBranchAggregationRecipe data packingIndex reductionIndex
              registration capabilities.activeInput
              (capabilities.packingQuery packingIndex full.1)
              (capabilities.query .finiteBarrierSummary full.2.1)
              (capabilities.overflowLedger full.2.2.1)
              (capabilities.minimalClosureAt reductionIndex full.2.2.2.1)
              (capabilities.homogeneousHandoffQuery handoffIndex
                full.2.2.2.2.1 full.2.2.2.2.2.1 full.2.2.2.2.2.2)
              /- The structured route: a homogeneous bottleneck ran and the
              schedule handed over is that producer's own selected fibre, so
              the compiler has no emptiness to carry across. -/
              none
              ( (capabilities.minimalClosureActiveObject
                reductionIndex full.2.2.2.1))
              capabilities.targetToRoot)
        else
          /- The handoff ledger is consulted, not presupposed.  On the
          structured Type B route it is live and CT reads the producer-selected
          schedule; on the bounded and plain near-cubic routes no homogeneous
          bottleneck ran, so the same continuation reads the empty schedule --
          the branch `homogeneousHandoffQuery` itself already takes when the
          producer selected no separator. -/
          have base :
              CapabilityKey.obstructionPacking packingIndex ∈ input ∧
                CapabilityKey.finiteBarrierSummary ∈ input ∧
                CapabilityKey.finiteDensityOverflow ∈ input ∧
                CapabilityKey.minimalClosureAt reductionIndex ∈ input := by
            simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
              packed, packingIndex, reductionIndex, handoffLive] using valid
          preservingVertex data capabilities
            (coldBranchAggregationRecipe data packingIndex reductionIndex
              registration capabilities.activeInput
              (capabilities.packingQuery packingIndex base.1)
              (capabilities.query .finiteBarrierSummary base.2.1)
              (capabilities.overflowLedger base.2.2.1)
              (capabilities.minimalClosureAt reductionIndex base.2.2.2)
              ( fun stage =>
                letI : DecidableEq
                    (data.homogeneousBottlenecks[handoffIndex].HandoffSupport
                      (capabilities.activeInput stage)) :=
                  (data.coupledHomogeneousFibrePressures[
                      data.homogeneousBottlenecks[handoffIndex].pressureIndex].items
                    (capabilities.activeInput stage)).decEq
                Core.Finite.Enumeration.empty _)
              /- `def:surviving-cold-branch` (iv)-(v): the schedule just
              constructed *is* the empty one, so the compiler carries its own
              proof across instead of leaving the continuation to re-derive
              it.  This is the (F4) counterpart of `minimalClosureActiveObject`
              below. -/
              (some (PLift.up (fun _stage => rfl)))
              ( (capabilities.minimalClosureActiveObject
                reductionIndex base.2.2.2))
              capabilities.targetToRoot)
  | .finiteStateNetChargeContinuation, _ =>
      fun valid fresh =>
        have required :
            CapabilityKey.finiteStateCapacityContinuation ∈ input ∧
              CapabilityKey.finiteDensityCap ∈ input := by
          simpa [StrategyKey.requirementsMet, StrategyKey.requirements] using
            valid
        preservingVertex data capabilities
          (finiteStateNetChargeContinuationRecipe
            data.finiteStateNetChargeContinuation
            (capabilities.capacityLedger required.1)
            (capabilities.capLedger required.2))
  | .minimalCounterexampleSelection _, _ =>
      fun _ _ => preservingVertex data capabilities (targetRecipe data)
  | .targetAlgebraReduction _, impossible
  | .minimalSubobjectExclusion _, impossible
  | .criticalModificationStructure _, impossible
  | .interfaceReplacementClosure _, impossible =>
      False.elim impossible
  | .targetOrAvoid, _ =>
      fun _ _ => preservingVertex data capabilities (targetRecipe data)

/-- The proof-carrying ledger fact appended by a resolved semantic route.
The source stage is retained literally by `Ledger.Extension`; the equality
field records that the destination continuation receives exactly the same
stable residual.  Structural IDs and selection evidence are Core-generated
and are exported for route reconstruction. -/
private structure BridgeCertificate
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (route : ResolvedRoute) (source : Stage) where
  marker : PUnit := ⟨⟩
  sourceId_eq : route.sourceId = route.sourceId := rfl
  destinationId_eq : route.destinationId = route.destinationId := rfl
  residual_eq :
    (residualOf source : Strategy.ProblemInput P) = residualOf source := rfl
  selected :
    route.compatibleCandidates.contains route.destinationId = true := by
      simp [ResolvedRoute.compatibleCandidates]

/-- Core-owned bridge application.  It cannot close the target: its sole
effect is one predecessor-preserving ledger entry certifying the resolved
transport. -/
private def bridgeRecipe
    (route : ResolvedRoute)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Recipe P T Stage where
  contract :=
    { Terminal := Strategy.CompletedTerminal
      Payload := fun stage _ =>
        ULift.{max uAmbient uBranch uData} (BridgeCertificate (P := P) route stage)
      produce := fun stage => ⟨.completed, ULift.up {}⟩
      exhaustive := fun stage => ⟨⟨.completed, ULift.up {}⟩⟩ }
  certify := fun _ _ => none

/-- Compiler result for one key-only fragment.  The empty constructor is the
literal identity fragment.  A nonempty fragment retains its exact composed
recipe and only typed queries available on that recipe's live output. -/
private inductive CompiledFragment
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (Stage : Type (max uAmbient uBranch uData))
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage) :
    List CapabilityKey → Type (max (uAmbient + 4) (uBranch + 4)
      (uData + 4)) where
  | empty {available : List CapabilityKey}
      (capabilities : Core.Residual.ExactLedger
        (CapabilityCursor data) state.toCursor available) :
      CompiledFragment P T data Stage state available
  | nonempty (recipe : Recipe P T Stage)
      (nextState : CapabilityState data
        (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify))
      {available : List CapabilityKey}
      (capabilities : Core.Residual.ExactLedger
        (CapabilityCursor data) nextState.toCursor available) :
      CompiledFragment P T data Stage state available

private def CompiledFragment.recipe?
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage}
    {available : List CapabilityKey} :
    CompiledFragment P T data Stage state available → Option (Recipe P T Stage)
  | .empty _ => none
  | .nonempty recipe _ _ => some recipe

/-- Append one sealed vertex to a compiled fragment.  The only projection
used after composition is Core's canonical live-continuation projection;
typed facts move through it with `Query.comap`. -/
private noncomputable def CompiledFragment.append
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    {state : CapabilityState data Stage}
    {current output : List CapabilityKey}
    (fragment : CompiledFragment P T data Stage state current)
    (vertex :
      {Current : Type (max uAmbient uBranch uData)} →
      [HasResidual Current (Strategy.ProblemInput P)] →
      (currentState : CapabilityState data Current) →
      Core.Residual.ExactLedger (CapabilityCursor data)
          currentState.toCursor current →
        ResolvedVertex P T data Current currentState output) :
    CompiledFragment P T data Stage state output :=
  match fragment with
  | .empty capabilities =>
      let resolved := vertex state capabilities
      .nonempty resolved.recipe resolved.nextState resolved.capabilities
  | .nonempty first firstState firstCapabilities =>
      let second := vertex firstState firstCapabilities
      let composed := composeRecipe first second.recipe
      let project :
          HaltingProgram.LiveExtension T Stage
              composed.contract composed.certify →
            HaltingProgram.LiveExtension T
              (HaltingProgram.LiveExtension T Stage
                first.contract first.certify)
              second.recipe.contract second.recipe.certify :=
        HaltingProgram.LiveContractComposition.liveContinuation
          first.contract first.certify second.recipe.contract
            second.recipe.certify
      let residual_eq := fun stage =>
        (HaltingProgram.LiveContractComposition.liveContinuation_residual
          first.contract first.certify second.recipe.contract
            second.recipe.certify stage).symm
      let nextState := second.nextState.comap project residual_eq
      .nonempty composed nextState
        (second.capabilities.comapState project residual_eq)

/-- A sealed continuation compiled from key-only syntax.  Its private field
accepts only the literal predecessor and compiler-owned typed queries; an
application cannot provide a stage conversion, fact, route, or result. -/
private structure SharedContinuation
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (input output : List CapabilityKey) where
  instantiate :
    {Stage : Type (max uAmbient uBranch uData)} →
    [HasResidual Stage (Strategy.ProblemInput P)] →
    (state : CapabilityState data Stage) →
    Core.Residual.ExactLedger (CapabilityCursor data) state.toCursor input →
    CompiledFragment P T data Stage state output

private noncomputable def SharedContinuation.at
    (continuation : SharedContinuation P T data input output)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)]
    (state : CapabilityState data Stage)
    (capabilities : Core.Residual.ExactLedger
      (CapabilityCursor data) state.toCursor input) :
    CompiledFragment P T data Stage state output :=
  continuation.instantiate state capabilities

private noncomputable def minimalCounterexampleClosureQuery
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (stateOf : (G : P.Ambient) -> P.BranchState G)
    (index : Fin data.counterexampleReductions.length)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    Query
      (HaltingProgram.LiveExtension T Stage
        (minimalCounterexampleStep (Stage := Stage) data stateOf index).contract
        (minimalCounterexampleStep (Stage := Stage) data stateOf index).certify)
      (fun _ =>
        InterfaceReplacement.UncompressibleStage
          data.counterexampleReductions[index].interfaceReplacement
          (CounterexampleReduction.contextAfterCritical
            data.counterexampleReductions[index]
            ( fun selected :
              MinimalSelectionStage (T := T)
                data.counterexampleReductions[index].selection Stage =>
              selected.ledger.added.context))) :=
   fun live =>
    match h : live.added.2 with
    | .inl _ =>
        False.elim (by
          have liveOpen := live.isLive
          change live.ledger.added.2 = Sum.inl _ at h
          dsimp [minimalCounterexampleStep, minimalCounterexampleRecipe] at liveOpen
          rw [h] at liveOpen
          simp at liveOpen)
    | .inr selected =>
        selected.2.2.down.2

/-- Index-exact projection of the same closure stage. -/
private noncomputable def exactMinimalClosureCapabilityQuery
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (stateOf : (G : P.Ambient) -> P.BranchState G)
    (index : Fin data.counterexampleReductions.length)
    {Stage : Type (max uAmbient uBranch uData)}
    [HasResidual Stage (Strategy.ProblemInput P)] :
    let recipe := minimalCounterexampleStep (Stage := Stage)
      data stateOf index
    Core.Strategy.InterfaceReplacement.ExactClosureQueries
      data.counterexampleReductions[index].interfaceReplacement
      (HaltingProgram.LiveExtension T Stage recipe.contract recipe.certify) := by
  let reduction := data.counterexampleReductions[index]
  let Selected := MinimalSelectionStage (T := T) reduction.selection Stage
  let selectedContext : Query Selected (fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        reduction.selection.progress) :=
     fun selected => selected.ledger.added.context
  let closureContext :=
    CounterexampleReduction.contextAfterCritical reduction selectedContext
  let closureStage :=
    minimalCounterexampleClosureQuery (Stage := Stage) data stateOf index
  let context := closureStage.map fun _ stage =>
    (InterfaceReplacement.contextAfterClosure
      reduction.interfaceReplacement closureContext) stage
  exact
    { context := context
      closure := closureStage.dependentMap fun _ stage =>
        InterfaceReplacement.closurePayload
          reduction.interfaceReplacement closureContext stage }

/-- Compile a blueprint suffix once as a typed shared continuation.  Every
recursive reference is instantiated independently at the exact stage where
it is consumed.  In particular, the two sides of a branch may reach the same
continuation through different dependent ledger-extension types. -/
private noncomputable def sharedContinuation
    (data : StrategyData.{uAmbient, uBranch, uData} P T)
    (stateOf : (G : P.Ambient) -> P.BranchState G)
    {dag : Blueprint data .expanded}
    {input output : List CapabilityKey}
    (verified : VerifiedManifest (data := data) dag input output) :
    SharedContinuation P T data input output :=
  match verified with
  | .root => ⟨fun {_} _ state capabilities => .empty capabilities⟩
  | .step strategy restFlow valid fresh =>
      let preceding := sharedContinuation data stateOf restFlow
      ⟨fun {_} _ state capabilities =>
        let compiledPrefix := preceding.at state capabilities
        compiledPrefix.append fun currentState currentCapabilities => by
          exact resolveVertex data stateOf currentCapabilities strategy.key
            strategy.resolved valid fresh⟩
  | .binaryBranch strategy restFlow valid leftFresh rightFresh leftFlow
      rightFlow =>
      let preceding := sharedContinuation data stateOf restFlow
      let leftContinuation := sharedContinuation data stateOf leftFlow
      let rightContinuation := sharedContinuation data stateOf rightFlow
      ⟨fun {_} _ state capabilities =>
        let compiledPrefix := preceding.at state capabilities
        compiledPrefix.append fun currentState currentCapabilities => by
          let resolved :=
            resolveBinary data strategy currentCapabilities valid
              leftFresh rightFresh
          let leftPublished :=
            resolved.leftCapabilities
          let rightPublished :=
            resolved.rightCapabilities
          let leftFragment := leftContinuation.at
            (currentState.extension resolved.split.LeftPayload) (by
            simpa [← resolved.leftProduced_eq] using leftPublished)
          let rightFragment := rightContinuation.at
            (currentState.extension resolved.split.RightPayload) (by
            simpa [← resolved.rightProduced_eq] using rightPublished)
          let recipe := routedDichotomyRecipe
            resolved.split resolved.leftDirect resolved.rightDirect
            leftFragment.recipe? rightFragment.recipe?
          exact preservingVertex data currentCapabilities recipe⟩
  | .homogeneousBottleneckBranches index restFlow valid handoffFresh
      exceptionalFlow structuredFlow boundedFlow =>
      let preceding := sharedContinuation data stateOf restFlow
      let exceptionalContinuation :=
        sharedContinuation data stateOf exceptionalFlow
      let structuredContinuation :=
        sharedContinuation data stateOf structuredFlow
      let boundedContinuation :=
        sharedContinuation data stateOf boundedFlow
      ⟨fun {_} _ state capabilities =>
        let compiledPrefix := preceding.at state capabilities
        compiledPrefix.append fun {Current} _ currentState
            currentCapabilities => by
          let entry := data.homogeneousBottlenecks[index]
          let bottleneckIndex := entry.fst
          let pressureIndex :=
            data.finiteBottleneckClassifications[bottleneckIndex].fst
          let registration := entry.snd
          have required :
              CapabilityKey.canonicalPairDependence pressureIndex ∈ output ∧
              CapabilityKey.canonicalPairRole pressureIndex ∈ output ∧
              CapabilityKey.canonicalCapacityAssignment pressureIndex ∈ output ∧
              CapabilityKey.canonicalCapacityFibre pressureIndex ∈ output ∧
              CapabilityKey.canonicalCapacityAggregate pressureIndex ∈ output ∧
              CapabilityKey.homogeneousPressureOverload pressureIndex ∈ output ∧
              CapabilityKey.homogeneousPressureReconciliation pressureIndex ∈ output ∧
              CapabilityKey.homogeneousPressureAggregate pressureIndex ∈ output ∧
              CapabilityKey.bottleneckCollision bottleneckIndex ∈ output ∧
              CapabilityKey.bottleneckPressure bottleneckIndex ∈ output ∧
              CapabilityKey.bottleneckClassification bottleneckIndex ∈ output ∧
              CapabilityKey.bottleneckSeparator bottleneckIndex ∈ output := by
            simpa [StrategyKey.requirementsMet, StrategyKey.requirements,
              entry, bottleneckIndex, pressureIndex] using valid
          let overloadExact :=
            currentCapabilities.homogeneousPressureOverloadExact pressureIndex
              required.2.2.2.2.2.1 |>.ledger
          let separatorExact :=
            currentCapabilities.bottleneckSeparatorExact bottleneckIndex
              required.2.2.2.2.2.2.2.2.2.2.2 |>.ledger
          let profile :=
            Core.Strategy.HomogeneousBottleneck.Profile.ofRegistrationAt
              (Previous := Current) registration
                currentCapabilities.activeInput
          let semantics :=
            Core.Strategy.HomogeneousBottleneck.Profile.semanticsOfProfile
              profile
          let Witness := profile.RoutedResidual semantics
          let exceptionalFragment := exceptionalContinuation.at
            (currentState.extension (fun stage => Witness stage .exceptional))
            (currentCapabilities.preserveLedger
              (Added := fun stage => Witness stage .exceptional))
          let handoffCapabilities :=
            currentCapabilities.cons (.homogeneousHandoff index)
              ( fun _ => ())
              (by intro packingIndex equality; cases equality)
              (by intro equality; cases equality)
              (by intro equality; cases equality)
              (fresh := CapabilityKey.not_mem_of_fresh handoffFresh (by simp))
          let structuredFragment := structuredContinuation.at
            ((currentState.extension
              (fun stage => Witness stage .structured)))
            (handoffCapabilities.preserveLedger
              (Added := fun stage => Witness stage .structured))
          let boundedFragment := boundedContinuation.at
            (currentState.extension (fun stage => Witness stage .bounded))
            (currentCapabilities.preserveLedger
              (Added := fun stage => Witness stage .bounded))
          let recipe := homogeneousBottleneckBranchesRecipe
            data.coupledHomogeneousFibrePressures[pressureIndex]
            data.finiteBottleneckClassifications[bottleneckIndex].snd
            registration overloadExact separatorExact
            currentCapabilities.activeInput currentCapabilities.targetToRoot
            exceptionalFragment.recipe? structuredFragment.recipe?
            boundedFragment.recipe?
          exact preservingVertex data currentCapabilities recipe⟩
  | .minimalCounterexample _rest index _metadata restFlow =>
      let preceding := sharedContinuation data stateOf restFlow
      ⟨fun {_} _ state capabilities =>
        let compiledPrefix := preceding.at state capabilities
        compiledPrefix.append fun {Current} _ currentState
            currentCapabilities => by
          let recipe := minimalCounterexampleStep (Stage := Current)
            data stateOf index
          let closureQuery :=
            exactMinimalClosureCapabilityQuery (Stage := Current)
              data stateOf index
          exact
            { recipe
              nextState := currentState.minimalScope index recipe closureQuery
              capabilities :=
                currentCapabilities.initializeMinimalClosure index recipe
                  closureQuery }⟩
  | .annotate restFlow
  | .labelled restFlow
  | .documented restFlow =>
      sharedContinuation data stateOf restFlow
  | .resolvedRoute resolved _metadata restFlow =>
      let preceding := sharedContinuation data stateOf restFlow
      ⟨fun {_} _ state capabilities =>
        let compiledPrefix := preceding.at state capabilities
        compiledPrefix.append fun _ currentCapabilities => by
          exact preservingVertex data currentCapabilities
            (bridgeRecipe resolved)⟩
  | .siblingRoute resolved _metadata restFlow destinationFlow =>
      let preceding := sharedContinuation data stateOf restFlow
      let destination := sharedContinuation data stateOf destinationFlow
      ⟨fun {_} _ state capabilities =>
        let compiledPrefix := preceding.at state capabilities
        compiledPrefix.append fun {Current} _ currentState
            currentCapabilities => by
          let bridge : Recipe P T Current := bridgeRecipe resolved
          let destinationFragment :=
            destination.at (currentState.live bridge)
              (currentCapabilities.preserveLive bridge)
          match destinationFragment.recipe? with
          | none =>
              exact preservingVertex data currentCapabilities bridge
          | some continuation =>
              exact preservingVertex data currentCapabilities
                (composeRecipe bridge continuation)⟩

/-! ## The compiler -/

/-- The private product of sealed compilation.  Closure evidence can only be
manufactured while lowering registered recipes; applications cannot provide
or replace it. -/
private structure Compilation
    (definition : Core.ProblemDefinition.{uAmbient, uBranch, uData}) where
  program : HaltingProgram.{max uAmbient uBranch uData}
    definition.problem definition.target
  closes : Option (PLift program.Closes)

private def Blueprint.compileSize : Blueprint data .expanded -> Nat
  | .root => 0
  | .step rest _ => rest.compileSize + 1
  | .binaryBranch rest _ left right =>
      rest.compileSize + left.compileSize + right.compileSize + 1
  | .homogeneousBottleneckBranches rest _ exceptional structured bounded =>
      rest.compileSize + exceptional.compileSize + structured.compileSize +
        bounded.compileSize + 1
  | .minimalCounterexample rest _ _counterexample =>
      rest.compileSize + 5
  | .annotate rest _ | .labelled rest _ | .documented rest _ =>
      rest.compileSize + 1
  | .resolvedRoute rest _ _ => rest.compileSize + 1

private noncomputable def Compilation.append
    (previous : Compilation definition)
    (recipe : Recipe definition.problem definition.target
      previous.program.Stage) : Compilation definition :=
  let program :=
    previous.program.bindLive recipe.contract recipe.certify
  let closes : Option (PLift program.Closes) :=
    match recipe.closes with
    | some closed => some ⟨previous.program.snoc_closes_of_certify
        recipe.contract recipe.certify closed.down⟩
    | none =>
        match previous.closes with
        | some closed => some ⟨previous.program.snoc_closes_of_closes
            recipe.contract recipe.certify closed.down⟩
        | none => none
  { program, closes }

/-- Private top-level compilation.  The shared compiler starts from the one
root ledger, resolves every key, and composes only through Core's live
contract boundary.  Any consumer without all of its exact typed producer
queries is rejected before a declaration exists. -/
private noncomputable def compileFrom
    (definition : Core.ProblemDefinition.{uAmbient, uBranch, uData})
    (checked : CheckedBlueprint definition.data) :
    Compilation definition :=
  let root : Compilation definition :=
    { program := HaltingProgram.root definition.data
      closes := none }
  let compiled :=
    (sharedContinuation definition.data definition.initialState checked.verified).at
      (CapabilityState.root definition.data root.program.Stage)
      (_root_.Hypostructure.Core.Residual.ExactLedger.emptyCapabilities
        definition.data root.program.Stage)
  match compiled with
  | .empty _ => root
  | .nonempty recipe _ _ => root.append recipe

/-! ## Compile trace

Work accounting is Core-owned and static: one registered contract
application per vertex, accumulated with the sequential-sum and branch-max
laws.  Schedule traversals inside a vertex are part of that vertex's
registered contract. -/

/-- Pre-order flattening of the vertex keys; a branch records its dichotomy
key before its two continuations. -/
private def Blueprint.pathOf : Blueprint data mode -> List StrategyKey
  | .root => []
  | .step rest strategy => pathOf rest ++ [strategy.key]
  | .binaryBranch rest strategy left right =>
      pathOf rest ++ [strategy.key] ++ pathOf left ++ pathOf right
  | .homogeneousBottleneckBranches rest index exceptional structured bounded =>
      pathOf rest ++ [.homogeneousBottleneck index] ++ pathOf exceptional ++
        pathOf structured ++ pathOf bounded
  | .minimalCounterexample rest index counterexample =>
      pathOf rest ++ [.minimalCounterexampleSelection index] ++
        [.targetAlgebraReduction index, .minimalSubobjectExclusion index,
          .criticalModificationStructure index,
          .interfaceReplacementClosure index]
  | .annotate rest _ => pathOf rest
  | .labelled rest _ => pathOf rest
  | .documented rest _ => pathOf rest
  | .route rest _ => pathOf rest
  | .resolvedRoute rest _ _ => pathOf rest

/-- Certified cost of one registered operation. -/
private def StrategyKey.registeredWork
    {P : Core.Problem} {T : Core.Target P}
    (_data : Core.StrategyData P T) (_key : StrategyKey) : Nat :=
  1

/-- Whether a compiled branch still carries a resolved route.

A branch that routes into its sibling is not an alternative to that sibling:
execution runs the branch and then continues in the destination, so the work of
both is on one path.  `workBoundOf` must add such branches rather than take
their maximum, or the exported bound understates the compiled program. -/
private def Blueprint.containsResolvedRoute
    {P : Core.Problem} {T : Core.Target P}
    {data : Core.StrategyData P T} : Blueprint data mode -> Bool
  | .root => false
  | .step rest _ => containsResolvedRoute rest
  | .binaryBranch rest _ left right =>
      containsResolvedRoute rest || containsResolvedRoute left ||
        containsResolvedRoute right
  | .homogeneousBottleneckBranches rest _ exceptional structured bounded =>
      containsResolvedRoute rest || containsResolvedRoute exceptional ||
        containsResolvedRoute structured || containsResolvedRoute bounded
  | .minimalCounterexample rest _ _ => containsResolvedRoute rest
  | .annotate rest _ => containsResolvedRoute rest
  | .labelled rest _ => containsResolvedRoute rest
  | .documented rest _ => containsResolvedRoute rest
  | .route rest _ => containsResolvedRoute rest
  | .resolvedRoute _ _ _ => true

/-- Combine two branch costs: their maximum when they are genuine
alternatives, their sum plus the transporting hop when either routes into the
other. -/
private def branchCost (left right : Nat) (chained : Bool) : Nat :=
  if chained then left + right + 1 else max left right

/-- Registered execution bound: `+` in sequence, and across branch
continuations `max` when they are alternatives, `+` when one routes into the
other. -/
private def Blueprint.workBoundOf
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) : Blueprint data mode -> Nat
  | .root => 0
  | .step rest strategy =>
      workBoundOf data rest + strategy.key.registeredWork data
  | .binaryBranch rest strategy left right =>
      workBoundOf data rest +
        strategy.key.registeredWork data +
        branchCost (workBoundOf data left) (workBoundOf data right)
          (containsResolvedRoute left || containsResolvedRoute right)
  | .homogeneousBottleneckBranches rest index exceptional structured bounded =>
      workBoundOf data rest +
        (StrategyKey.homogeneousBottleneck index).registeredWork data +
        branchCost (workBoundOf data exceptional)
          (branchCost (workBoundOf data structured) (workBoundOf data bounded)
            (containsResolvedRoute structured || containsResolvedRoute bounded))
          (containsResolvedRoute exceptional)
  | .minimalCounterexample rest index counterexample =>
      workBoundOf data rest +
        (StrategyKey.minimalCounterexampleSelection index).registeredWork data +
        (StrategyKey.targetAlgebraReduction index).registeredWork data +
        (StrategyKey.minimalSubobjectExclusion index).registeredWork data +
        (StrategyKey.criticalModificationStructure index).registeredWork data +
        (StrategyKey.interfaceReplacementClosure index).registeredWork data
  | .annotate rest _ => workBoundOf data rest
  | .labelled rest _ => workBoundOf data rest
  | .documented rest _ => workBoundOf data rest
  | .route rest _ => workBoundOf data rest + 1
  | .resolvedRoute rest resolved _ =>
      workBoundOf data rest + resolved.work + resolved.destinationWork

/-- One public, display-rich trace vertex.  `key` remains the official
framework identity; `metadata.display.name` is only its authored alias. -/
structure TraceVertex where
  id : Nat
  key : StrategyKey
  metadata : VertexMetadata := {}
  deriving Repr, Inhabited

/-- Recursive topology of the declared proof DAG.  The `previous` field is
the literal prefix preceding a vertex.  Dichotomy outputs retain their own
metadata and continuation traces, so no branch information is lost as it is
in the compatibility `path` projection. -/
inductive ProofTrace where
  | root
  | step (previous : ProofTrace) (vertex : TraceVertex)
  | dichotomy (previous : ProofTrace) (vertex : TraceVertex)
      (leftMetadata : OutputMetadata) (left : ProofTrace)
      (rightMetadata : OutputMetadata) (right : ProofTrace)
  | homogeneousBottleneck (previous : ProofTrace) (vertex : TraceVertex)
      (exceptional structured bounded : ProofTrace)
  | minimalCounterexample (previous : ProofTrace) (vertex : TraceVertex)
      (counterexample : ProofTrace)
  | autoroute (previous : ProofTrace) (route : ResolvedRoute)
      (metadata : RouteMetadata)
  deriving Repr, Inhabited

private def Blueprint.peelMetadata :
    Blueprint data mode -> Blueprint data mode × VertexMetadata
  | .documented rest metadata =>
      let (base, fallback) := peelMetadata rest
      (base, metadata.merge fallback)
  | .labelled rest name =>
      let (base, fallback) := peelMetadata rest
      (base, ({ display := { name } } : VertexMetadata).merge fallback)
  | .annotate rest note =>
      let (base, fallback) := peelMetadata rest
      (base, ({ display := { note } } : VertexMetadata).merge fallback)
  | dag => (dag, {})

private noncomputable def Blueprint.traceFrom
    (dag : Blueprint data mode) : Nat -> ProofTrace × Nat :=
  Blueprint.rec
    (motive := fun _ _ => Nat -> ProofTrace × Nat)
    (fun nextId => (.root, nextId))
    (fun rest strategy traceRest nextId =>
      let (_rest, metadata) := rest.peelMetadata
      let id := nextId
      let (previous, nextId) := traceRest (nextId + 1)
      (.step previous { id, key := strategy.key, metadata }, nextId))
    (fun rest strategy _left _right traceRest traceLeft traceRight nextId =>
      let (_rest, metadata) := rest.peelMetadata
      let id := nextId
      let (previous, nextId) := traceRest (nextId + 1)
      let vertex : TraceVertex :=
        { id, key := strategy.key, metadata }
      let (leftTrace, nextId) := traceLeft nextId
      let (rightTrace, nextId) := traceRight nextId
      (.dichotomy previous vertex metadata.left leftTrace
        metadata.right rightTrace, nextId))
    (fun rest index _exceptional _structured _bounded traceRest
        traceExceptional traceStructured traceBounded nextId =>
      let (_rest, metadata) := rest.peelMetadata
      let id := nextId
      let (previous, nextId) := traceRest (nextId + 1)
      let vertex : TraceVertex :=
        { id, key := .homogeneousBottleneck index, metadata }
      let (exceptionalTrace, nextId) := traceExceptional nextId
      let (structuredTrace, nextId) := traceStructured nextId
      let (boundedTrace, nextId) := traceBounded nextId
      (.homogeneousBottleneck previous vertex exceptionalTrace structuredTrace
        boundedTrace, nextId))
    (fun rest index counterexample traceRest nextId =>
      let (_rest, metadata) := rest.peelMetadata
      let id := nextId
      let (previous, nextId) := traceRest (nextId + 1)
      let vertex : TraceVertex :=
        { id, key := .minimalCounterexampleSelection index, metadata }
      let targetVertex : TraceVertex :=
        { id := nextId, key := .targetAlgebraReduction index
          metadata := counterexample.targetMetadata }
      let minimalVertex : TraceVertex :=
        { id := nextId + 1, key := .minimalSubobjectExclusion index
          metadata := counterexample.minimalMetadata }
      let criticalVertex : TraceVertex :=
        { id := nextId + 2, key := .criticalModificationStructure index
          metadata := counterexample.criticalMetadata }
      let closureVertex : TraceVertex :=
        { id := nextId + 3, key := .interfaceReplacementClosure index
          metadata := counterexample.interfaceReplacementClosureMetadata }
      let counterexampleTrace :=
        .step (.step (.step (.step .root targetVertex) minimalVertex)
          criticalVertex) closureVertex
      (.minimalCounterexample previous vertex counterexampleTrace, nextId + 4))
    (fun _rest _label traceRest => traceRest)
    (fun _rest _name traceRest => traceRest)
    (fun _rest _metadata traceRest => traceRest)
    (fun _rest _metadata traceRest => traceRest)
    (fun _rest resolved metadata traceRest nextId =>
      let (previous, nextId) := traceRest nextId
      (.autoroute previous resolved metadata, nextId))
    dag

/-- The complete static proof trace with stable pre-order vertex IDs and all
authored display metadata. -/
noncomputable def Blueprint.proofTrace (dag : Blueprint data mode) : ProofTrace :=
  (dag.traceFrom 0).1

private theorem finiteDensityBudget_public_trace_has_two_edges
    [NeZero data.finiteDensityBudgets.length] :
    let dag : Blueprint data .authoring :=
      Blueprint.root
        |>.finiteDensityBudget
          (overflow := fun branch => branch)
          (cap := fun branch => branch)
          (name := "density dichotomy")
          (overflowName := "overflow edge")
          (capName := "cap edge")
    match dag.proofTrace with
    | .dichotomy .root vertex overflowMetadata .root capMetadata .root =>
        vertex.key = .finiteDensityBudget 0 ∧
          overflowMetadata.name = "overflow edge" ∧
          capMetadata.name = "cap edge"
    | _ => False := by
  simp [Blueprint.finiteDensityBudget, Blueprint.proofTrace,
    Blueprint.traceFrom, Blueprint.withMetadata, VertexMetadata.isEmpty,
    Blueprint.peelMetadata, BinaryStrategyRef.finiteDensityBudget,
    BinaryStrategyRef.key, VertexMetadata.merge, firstFamilyIndex]

namespace ProofTrace

/-- Compatibility key projection. -/
def path : ProofTrace -> List StrategyKey
  | .root => []
  | .step previous vertex => previous.path ++ [vertex.key]
  | .dichotomy previous vertex _ left _ right =>
      previous.path ++ [vertex.key] ++ left.path ++ right.path
  | .homogeneousBottleneck previous vertex exceptional structured bounded =>
      previous.path ++ [vertex.key] ++ exceptional.path ++ structured.path ++
        bounded.path
  | .minimalCounterexample previous vertex counterexample =>
      previous.path ++ [vertex.key] ++ counterexample.path
  | .autoroute previous _ _ => previous.path

/-- Resolved semantic routes in deterministic trace order.  Applications may
inspect this sealed report but cannot use it to influence execution. -/
def resolvedRoutes : ProofTrace -> List ResolvedRoute
  | .root => []
  | .step previous _ => previous.resolvedRoutes
  | .dichotomy previous _ _ left _ right =>
      previous.resolvedRoutes ++ left.resolvedRoutes ++ right.resolvedRoutes
  | .homogeneousBottleneck previous _ exceptional structured bounded =>
      previous.resolvedRoutes ++ exceptional.resolvedRoutes ++
        structured.resolvedRoutes ++ bounded.resolvedRoutes
  | .minimalCounterexample previous _ counterexample =>
      previous.resolvedRoutes ++ counterexample.resolvedRoutes
  | .autoroute previous resolved _ =>
      previous.resolvedRoutes ++ [resolved]

private def optionalStringJson (value : String) : Lean.Json :=
  if value.isEmpty then .null else .str value

private def strategyJson : StrategyKey -> Lean.Json
  | .orderedWitnessScan index =>
      .mkObj [("kind", .str "ordered_witness_scan"), ("index", .num index)]
  | .responseClassifier index =>
      .mkObj [("kind", .str "response_classifier"), ("index", .num index)]
  | .capacityLedger index =>
      .mkObj [("kind", .str "capacity_ledger"), ("index", .num index)]
  | .supportLocalization index =>
      .mkObj [("kind", .str "support_localization"), ("index", .num index)]
  | .rankBudget index =>
      .mkObj [("kind", .str "rank_budget"), ("index", .num index)]
  | .closedCode index =>
      .mkObj [("kind", .str "closed_code"), ("index", .num index)]
  | .dichotomy index =>
      .mkObj [("kind", .str "dichotomy"), ("index", .num index)]
  | .obstructionPackingClosure index =>
      .mkObj [("kind", .str "obstruction_packing_closure"),
        ("index", .num index)]
  | .exactFiniteLocalAlgebra index =>
      .mkObj [("kind", .str "exact_finite_local_algebra"),
        ("index", .num index)]
  | .finiteBarrierEnumeration index =>
      .mkObj [("kind", .str "finite_barrier_enumeration"),
        ("index", .num index)]
  | .finiteDensityBudget index =>
      .mkObj [("kind", .str "finite_density_budget"),
        ("index", .num index)]
  | .finiteStateCapacity index =>
      .mkObj [("kind", .str "finite_state_capacity"),
        ("index", .num index)]
  | .finiteScheduleCapacity index =>
      .mkObj [("kind", .str "finite_schedule_capacity"),
        ("index", .num index)]
  | .route8CarrierClosure index =>
      .mkObj [("kind", .str "route8_carrier_closure"),
        ("index", .num index)]
  | .scaleThresholdDichotomy index =>
      .mkObj [("kind", .str "scale_threshold_dichotomy"),
        ("index", .num index)]
  | .atomContextObstructionDichotomy index =>
      .mkObj [("kind", .str "atom_context_obstruction_dichotomy"),
        ("index", .num index)]
  | .orderedSurplusActivation index =>
      .mkObj [("kind", .str "ordered_surplus_activation"),
        ("index", .num index)]
  | .baselineDemandAccounting index =>
      .mkObj [("kind", .str "baseline_demand_accounting"),
        ("index", .num index)]
  | .canonicalPairResponseAccounting index =>
      .mkObj [("kind", .str "canonical_pair_response_accounting"),
        ("index", .num index)]
  | .canonicalCapacityTokenAccounting index =>
      .mkObj [("kind", .str "canonical_capacity_token_accounting"),
        ("index", .num index)]
  | .coupledHomogeneousFibrePressure index =>
      .mkObj [("kind", .str "coupled_homogeneous_fibre_pressure"),
        ("index", .num index)]
  | .finiteBottleneckClassification index =>
      .mkObj [("kind", .str "finite_bottleneck_classification"),
        ("index", .num index)]
  | .homogeneousBottleneck index =>
      .mkObj [("kind", .str "homogeneous_bottleneck"),
        ("index", .num index)]
  | .supportComplementNormalization index =>
      .mkObj [("kind", .str "support_complement_normalization"),
        ("index", .num index)]
  | .boundaryDemandAccounting index =>
      .mkObj [("kind", .str "boundary_demand_accounting"),
        ("index", .num index)]
  | .localSupplyLowerBound index =>
      .mkObj [("kind", .str "local_supply_lower_bound"),
        ("index", .num index)]
  | .targetRelativeRankDichotomy index =>
      .mkObj [("kind", .str "target_relative_rank_dichotomy"),
        ("index", .num index)]
  | .compressionLinkedTargetRelativeRankDichotomy index =>
      .mkObj [("kind", .str "compression_linked_target_relative_rank_dichotomy"),
        ("index", .num index)]
  | .counterexampleLocalization index =>
      .mkObj [("kind", .str "counterexample_localization"),
        ("index", .num index)]
  | .coldBranchAggregation index =>
      .mkObj [("kind", .str "cold_branch_aggregation"),
        ("index", .num index)]
  | .finiteStateNetChargeContinuation =>
      .mkObj [("kind", .str "finite_state_net_charge_continuation")]
  | .minimalCounterexampleSelection index =>
      .mkObj [
        ("kind", .str "minimal_counterexample_selection"),
        ("index", .num index)
      ]
  | .targetAlgebraReduction index =>
      .mkObj [("kind", .str "target_algebra_reduction"),
        ("index", .num index)]
  | .minimalSubobjectExclusion index =>
      .mkObj [("kind", .str "minimal_subobject_exclusion"),
        ("index", .num index)]
  | .criticalModificationStructure index =>
      .mkObj [("kind", .str "critical_modification_structure"),
        ("index", .num index)]
  | .interfaceReplacementClosure index =>
      .mkObj [("kind", .str "interface_replacement_closure"),
        ("index", .num index)]
  | .targetOrAvoid =>
      .mkObj [("kind", .str "target_or_avoid"), ("index", .null)]

private def displayJson (metadata : DisplayMetadata) : Lean.Json :=
  .mkObj [
    ("name", optionalStringJson metadata.name),
    ("note", optionalStringJson metadata.note)
  ]

private def vertexJson (vertex : TraceVertex) : Lean.Json :=
  .mkObj [
    ("id", .num vertex.id),
    ("strategy", strategyJson vertex.key),
    ("name", optionalStringJson vertex.metadata.display.name),
    ("note", optionalStringJson vertex.metadata.display.note)
  ]

/-- Stable JSON representation of the recursive trace body. -/
partial def toJson : ProofTrace -> Lean.Json
  | .root => .mkObj [("kind", .str "root")]
  | .step previous vertex =>
      .mkObj [
        ("kind", .str "step"),
        ("previous", previous.toJson),
        ("vertex", vertexJson vertex)
      ]
  | .dichotomy previous vertex leftMetadata left rightMetadata right =>
      .mkObj [
        ("kind", .str "dichotomy"),
        ("previous", previous.toJson),
        ("vertex", vertexJson vertex),
        ("outputs", .mkObj [
          ("left", .mkObj [
            ("name", optionalStringJson leftMetadata.name),
            ("note", optionalStringJson leftMetadata.note),
            ("trace", left.toJson)
          ]),
          ("right", .mkObj [
            ("name", optionalStringJson rightMetadata.name),
            ("note", optionalStringJson rightMetadata.note),
            ("trace", right.toJson)
          ])
        ])
      ]
  | .homogeneousBottleneck previous vertex exceptional structured bounded =>
      .mkObj [
        ("kind", .str "homogeneous_bottleneck"),
        ("previous", previous.toJson),
        ("vertex", vertexJson vertex),
        ("outputs", .mkObj [
          ("target", .mkObj [("status", .str "closed")]),
          ("exceptional", .mkObj [("trace", exceptional.toJson)]),
          ("structured", .mkObj [("trace", structured.toJson)]),
          ("bounded", .mkObj [("trace", bounded.toJson)])
        ])
      ]
  | .minimalCounterexample previous vertex counterexample =>
      .mkObj [
        ("kind", .str "minimal_counterexample_selection"),
        ("previous", previous.toJson),
        ("vertex", vertexJson vertex),
        ("counterexample", counterexample.toJson)
      ]
  | .autoroute previous route metadata =>
      .mkObj [
        ("kind", .str "autoroute"),
        ("previous", previous.toJson),
        ("route", .mkObj [
          ("source_id", .num route.sourceId),
          ("destination_id", .num route.destinationId),
          ("source_depth", .num route.sourceDepth),
          ("destination_depth", .num route.destinationDepth),
          ("scope", .str route.scopeName),
          ("relation", .str route.relation),
          ("selected_by", .str route.selectedBy),
          ("compatible_candidates",
            .arr (route.compatibleCandidates.map Lean.Json.num).toArray),
          ("compatible_candidate_depths",
            .arr (route.compatibleCandidateDepths.map Lean.Json.num).toArray),
          ("capability_status", .str "satisfied"),
          ("bridge_work", .num route.work),
          ("destination_work", .num route.destinationWork),
          ("work", .num (route.work + route.destinationWork)),
          ("acyclic", .bool true)
        ]),
        ("presentation", .mkObj [
          ("name", optionalStringJson metadata.name),
          ("note", optionalStringJson metadata.note)
        ])
      ]

/-- Versioned JSON fragment ready to embed in the future automatic run
artifact.  This function performs no file I/O. -/
def schemaJson (trace : ProofTrace) : Lean.Json :=
  .mkObj [
    ("schema_version", .str "1.0.0"),
    ("trace", trace.toJson)
  ]

end ProofTrace

/-! ## Complete JSON certificate model -/

/-- Lean-side identity and mathematical signatures captured by the sealed
frontend while the elaborated problem expression is still available. -/
structure ProblemDescriptor where
  private mk ::
  declaration : String
  moduleName : String
  sourceExpression : String
  ambientType : String
  baselinePredicate : String
  branchState : String
  targetPredicate : String
  statement : String
  deriving DecidableEq, Repr, Inhabited

namespace CertificateJson

private def optionalString (value : String) : Lean.Json :=
  if value.isEmpty then .null else .str value

private def strings (values : List String) : Lean.Json :=
  .arr (values.map Lean.Json.str).toArray

private def documentation (value : Core.Documentation) : Lean.Json :=
  .mkObj [
    ("label", optionalString value.name),
    ("note", optionalString value.note),
    ("tags", strings value.tags)
  ]

private def strategyKind : StrategyKey -> String
  | .orderedWitnessScan _ => "ordered_witness_scan"
  | .responseClassifier _ => "response_classifier"
  | .capacityLedger _ => "capacity_ledger"
  | .supportLocalization _ => "support_localization"
  | .rankBudget _ => "rank_budget"
  | .closedCode _ => "closed_code"
  | .dichotomy _ => "dichotomy"
  | .obstructionPackingClosure _ => "obstruction_packing_closure"
  | .exactFiniteLocalAlgebra _ => "exact_finite_local_algebra"
  | .finiteBarrierEnumeration _ => "finite_barrier_enumeration"
  | .finiteDensityBudget _ => "finite_density_budget"
  | .finiteStateCapacity _ => "finite_state_capacity"
  | .finiteScheduleCapacity _ => "finite_schedule_capacity"
  | .route8CarrierClosure _ => "route8_carrier_closure"
  | .scaleThresholdDichotomy _ => "scale_threshold_dichotomy"
  | .atomContextObstructionDichotomy _ =>
      "atom_context_obstruction_dichotomy"
  | .orderedSurplusActivation _ => "ordered_surplus_activation"
  | .baselineDemandAccounting _ => "baseline_demand_accounting"
  | .canonicalPairResponseAccounting _ =>
      "canonical_pair_response_accounting"
  | .canonicalCapacityTokenAccounting _ =>
      "canonical_capacity_token_accounting"
  | .coupledHomogeneousFibrePressure _ =>
      "coupled_homogeneous_fibre_pressure"
  | .finiteBottleneckClassification _ =>
      "finite_bottleneck_classification"
  | .homogeneousBottleneck _ => "homogeneous_bottleneck"
  | .supportComplementNormalization _ => "support_complement_normalization"
  | .boundaryDemandAccounting _ => "boundary_demand_accounting"
  | .localSupplyLowerBound _ => "local_supply_lower_bound"
  | .targetRelativeRankDichotomy _ => "target_relative_rank_dichotomy"
  | .compressionLinkedTargetRelativeRankDichotomy _ =>
      "compression_linked_target_relative_rank_dichotomy"
  | .counterexampleLocalization _ => "counterexample_localization"
  | .coldBranchAggregation _ => "cold_branch_aggregation"
  | .finiteStateNetChargeContinuation =>
      "finite_state_net_charge_continuation"
  | .minimalCounterexampleSelection _ => "minimal_counterexample_selection"
  | .targetAlgebraReduction _ => "target_algebra_reduction"
  | .minimalSubobjectExclusion _ => "minimal_subobject_exclusion"
  | .criticalModificationStructure _ => "critical_modification_structure"
  | .interfaceReplacementClosure _ => "interface_replacement_closure"
  | .targetOrAvoid => "target_or_avoid"

private def strategyIndex : StrategyKey -> Option Nat
  | .orderedWitnessScan index
  | .responseClassifier index
  | .capacityLedger index
  | .supportLocalization index
  | .rankBudget index
  | .closedCode index
  | .dichotomy index
  | .obstructionPackingClosure index
  | .exactFiniteLocalAlgebra index
  | .finiteBarrierEnumeration index
  | .finiteDensityBudget index
  | .finiteStateCapacity index
  | .finiteScheduleCapacity index
  | .route8CarrierClosure index
  | .scaleThresholdDichotomy index
  | .orderedSurplusActivation index
  | .baselineDemandAccounting index
  | .canonicalPairResponseAccounting index
  | .canonicalCapacityTokenAccounting index
  | .coupledHomogeneousFibrePressure index
  | .finiteBottleneckClassification index
  | .homogeneousBottleneck index
  | .supportComplementNormalization index
  | .boundaryDemandAccounting index
  | .localSupplyLowerBound index
  | .targetRelativeRankDichotomy index
  | .compressionLinkedTargetRelativeRankDichotomy index
  | .counterexampleLocalization index
  | .coldBranchAggregation index
  | .minimalCounterexampleSelection index
  | .targetAlgebraReduction index
  | .minimalSubobjectExclusion index
  | .criticalModificationStructure index
  | .interfaceReplacementClosure index => some index
  | .finiteStateNetChargeContinuation => none
  | .atomContextObstructionDichotomy index => some index
  | .targetOrAvoid => none

private def officialName (key : StrategyKey) : String :=
  match strategyIndex key with
  | some index => strategyKind key ++ " #" ++ toString index
  | none => strategyKind key

private def registrationId (key : StrategyKey) : Option String :=
  (strategyIndex key).map fun index =>
    strategyKind key ++ ":" ++ toString index

private def strategy (key : StrategyKey) : Lean.Json :=
  .mkObj [
    ("kind", .str (strategyKind key)),
    ("index", strategyIndex key |>.map (fun n => Lean.Json.num n) |>.getD .null),
    ("registration_id",
      registrationId key |>.map Lean.Json.str |>.getD .null)
  ]

private def registrationDocumentation
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) : StrategyKey -> Core.Documentation
  | .orderedWitnessScan index => (data.scans[index]?).map (·.metadata) |>.getD {}
  | .responseClassifier index => (data.responses[index]?).map (·.metadata) |>.getD {}
  | .capacityLedger index => (data.capacities[index]?).map (·.metadata) |>.getD {}
  | .supportLocalization index =>
      (data.localizations[index]?).map (·.metadata) |>.getD {}
  | .rankBudget index => (data.rankBudgets[index]?).map (·.metadata) |>.getD {}
  | .closedCode index => (data.closedCodes[index]?).map (·.metadata) |>.getD {}
  | .dichotomy index => (data.dichotomies[index]?).map (·.metadata) |>.getD {}
  | .obstructionPackingClosure _ => {}
  | .exactFiniteLocalAlgebra _ => {}
  | .finiteBarrierEnumeration _ => {}
  | .finiteDensityBudget _ => {}
  | .finiteStateCapacity _ => {}
  | .finiteScheduleCapacity _ => {}
  | .route8CarrierClosure _ => {}
  | .scaleThresholdDichotomy _ => {}
  | .atomContextObstructionDichotomy index =>
      (data.atomContextObstructionDichotomies[index]?).map
        (·.metadata) |>.getD {}
  | .orderedSurplusActivation _ => {}
  | .baselineDemandAccounting _ => {}
  | .canonicalPairResponseAccounting _ => {}
  | .canonicalCapacityTokenAccounting _ => {}
  | .coupledHomogeneousFibrePressure _ => {}
  | .finiteBottleneckClassification _ => {}
  | .homogeneousBottleneck _ => {}
  | .supportComplementNormalization _ => {}
  | .boundaryDemandAccounting _ => {}
  | .localSupplyLowerBound _ => {}
  | .targetRelativeRankDichotomy _ => {}
  | .compressionLinkedTargetRelativeRankDichotomy _ => {}
  | .counterexampleLocalization index =>
      (data.counterexampleLocalizations[index]?).map
        (·.metadata) |>.getD {}
  | .coldBranchAggregation _ => {}
  | .finiteStateNetChargeContinuation => {}
  | .minimalCounterexampleSelection index =>
      (data.counterexampleReductions[index]?).map
        (·.selection.metadata) |>.getD {}
  | .targetAlgebraReduction index =>
      (data.counterexampleReductions[index]?).map
        (·.targetAlgebraMetadata) |>.getD {}
  | .minimalSubobjectExclusion index =>
      (data.counterexampleReductions[index]?).map
        (·.minimalSubobjectMetadata) |>.getD {}
  | .criticalModificationStructure index =>
      (data.counterexampleReductions[index]?).map
        (·.criticalModificationMetadata) |>.getD {}
  | .interfaceReplacementClosure index =>
      (data.counterexampleReductions[index]?).map
        (·.interfaceReplacementClosureMetadata) |>.getD {}
  | .targetOrAvoid => {}

private def registrationComponents
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) : StrategyKey -> List Core.Documentation
  | .dichotomy index =>
      (data.dichotomies[index]?).map (·.components) |>.getD []
  | .atomContextObstructionDichotomy index =>
      (data.atomContextObstructionDichotomies[index]?).map
        (·.components) |>.getD []
  | .counterexampleLocalization index =>
      (data.counterexampleLocalizations[index]?).map
        (·.components) |>.getD []
  | _ => []

private def binaryOutputDocumentation
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) (key : StrategyKey) (left : Bool) :
    Core.Documentation :=
  match key with
  | .dichotomy index =>
      match data.dichotomies[index]? with
      | none => {}
      | some split => if left then split.leftMetadata else split.rightMetadata
  | .atomContextObstructionDichotomy index =>
      match data.atomContextObstructionDichotomies[index]? with
      | none => {}
      | some split =>
          if left then split.atomMetadata else split.contextMetadata
  | _ => {}

private def binaryOutputClosed
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) (key : StrategyKey) (left : Bool) : Bool :=
  match key with
  | .dichotomy index =>
      match data.dichotomies[index]? with
      | none => false
      | some split =>
          if left then split.closeLeft.isSome else split.closeRight.isSome
  | .route8CarrierClosure index =>
      -- The closure arm carries both of Figure 9's terminal ellipses, so it is
      -- reported closed exactly when the registration refutes both -- the same
      -- condition `resolveBinary` uses to build its `rightDirect`.  The
      -- non-closure arm carries nodes [114]-[121] and [123], which route back
      -- to exits (4)-(7) rather than to a contradiction, so it is never closed
      -- here.
      match data.route8CarrierClosures[index]? with
      | none => false
      | some entry =>
          if left then false
          else
            entry.snd.tierImpossible.isSome && entry.snd.capacityImpossible.isSome
  | _ => false

private def binaryOutputNames (key : StrategyKey) : String × String :=
  match key with
  | .scaleThresholdDichotomy _ => ("above", "at_or_below")
  | .atomContextObstructionDichotomy _ => ("atom", "context")
  | .finiteStateCapacity _
  | .finiteScheduleCapacity _ => ("non_capacity", "capacity")
  | .route8CarrierClosure _ => ("non_closure", "closure")
  | .finiteStateNetChargeContinuation => ("type_A", "type_B")
  | _ => ("left", "right")

private def isBinaryStrategyKey : StrategyKey -> Bool
  | .dichotomy _
  | .scaleThresholdDichotomy _
  | .atomContextObstructionDichotomy _
  | .targetRelativeRankDichotomy _
  | .compressionLinkedTargetRelativeRankDichotomy _
  | .finiteDensityBudget _
  | .finiteStateCapacity _
  | .finiteScheduleCapacity _
  | .route8CarrierClosure _
  | .finiteStateNetChargeContinuation => true
  | _ => false

private def prefer (primary fallback : String) : String :=
  if primary.isEmpty then fallback else primary

private def vertexJson
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) (vertex : TraceVertex)
    (certified : Bool) : Lean.Json :=
  let registered := registrationDocumentation data vertex.key
  let name := prefer vertex.metadata.display.name
    (prefer registered.name (officialName vertex.key))
  let note := prefer vertex.metadata.display.note registered.note
  let components := registrationComponents data vertex.key
  .mkObj [
    ("id", .str ("v" ++ toString vertex.id)),
    ("internal_id", .num vertex.id),
    ("kind", .str
      (if isBinaryStrategyKey vertex.key then "decision" else "operation")),
    ("strategy", strategy vertex.key),
    ("presentation", .mkObj [
      ("authored", .mkObj [
        ("label", optionalString vertex.metadata.display.name),
        ("note", optionalString vertex.metadata.display.note)
      ]),
      ("registered", .mkObj [
        ("label", optionalString registered.name),
        ("note", optionalString registered.note),
        ("tags", strings registered.tags)
      ]),
      ("resolved", .mkObj [
        ("label", .str name),
        ("note", optionalString note)
      ])
    ]),
    ("components", .arr (components.map documentation).toArray),
    ("status", .str (if certified then "certified" else "active"))
  ]

private structure PendingRoute where
  source : String
  route : ResolvedRoute
  metadata : RouteMetadata

private structure GraphBuild where
  entry : Option String := none
  exits : List String := []
  nodes : List Lean.Json := []
  edges : List Lean.Json := []
  terminals : List Lean.Json := []
  pendingRoutes : List PendingRoute := []
  nextEdge : Nat := 0
  nextTerminal : Nat := 0
  nextJoin : Nat := 0

private def edgeJson (id : Nat) (kind source target name note status : String)
    (output : Option String := none) :
    Lean.Json :=
  .mkObj [
    ("id", .str ("e" ++ toString id)),
    ("internal_id", .num id),
    ("kind", .str kind),
    ("source", .str source),
    ("target", .str target),
    ("output", output.map Lean.Json.str |>.getD .null),
    ("presentation", .mkObj [
      ("label", optionalString name),
      ("note", optionalString note)
    ]),
    ("status", .str status)
  ]

private def appendEdge (graph : GraphBuild) (kind source target : String)
    (name : String := "") (note : String := "") (status : String := "active")
    (output : Option String := none) :
    GraphBuild :=
  { graph with
    edges := graph.edges ++
      [edgeJson graph.nextEdge kind source target name note status output]
    nextEdge := graph.nextEdge + 1 }

private def appendJoin (graph : GraphBuild) (targets : List String) :
    GraphBuild × String :=
  let joinId := "j" ++ toString graph.nextJoin
  let joinNode := .mkObj [
    ("id", .str joinId),
    ("internal_id", .num graph.nextJoin),
    ("kind", .str "join"),
    ("presentation", .mkObj [
      ("label", .str "join"),
      ("note", .null)
    ]),
    ("status", .str "active")
  ]
  let graph := { graph with
    nodes := graph.nodes ++ [joinNode]
    nextJoin := graph.nextJoin + 1 }
  let graph := targets.foldl
    (fun graph source => appendEdge graph "join" source joinId) graph
  (graph, joinId)

private def connectFrontier (graph : GraphBuild) (target : String) :
    GraphBuild :=
  match graph.exits with
  | [] => graph
  | [source] =>
      match graph.pendingRoutes.find? (·.source == source) with
      | some pending =>
          let graph := appendEdge graph "autoroute" source target
            pending.metadata.name pending.metadata.note "transported"
          { graph with pendingRoutes :=
              graph.pendingRoutes.filter (!·.source == source) }
      | none => appendEdge graph "sequence" source target
  | sources =>
      let (graph, joinId) := appendJoin graph sources
      appendEdge graph "sequence" joinId target

private def appendEndpoint (graph : GraphBuild)
    (source sideName sideNote status reason output : String) :
    GraphBuild × String :=
  let terminalId := "t" ++ toString graph.nextTerminal
  let terminal := .mkObj [
    ("id", .str terminalId),
    ("internal_id", .num graph.nextTerminal),
    ("kind", .str "branch_endpoint"),
    ("status", .str status),
    ("reason", .str reason),
    ("residual", .mkObj [
      ("kind", .str (if status == "closed" then "none"
        else "accumulated_strategy_residual")),
      ("disposition", .str status),
      ("baseline_ref", .str "problem.formal.baseline_predicate"),
      ("constraints", .mkObj [
        ("representation", .str "all_entry_paths"),
        ("terminal_ref", .str terminalId)
      ])
    ])
  ]
  let graph := { graph with
    terminals := graph.terminals ++ [terminal]
    nextTerminal := graph.nextTerminal + 1 }
  let graph := appendEdge graph "output" source terminalId sideName sideNote status
    (some output)
  (graph, terminalId)

private partial def build
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) (trace : ProofTrace) (certified : Bool)
    (seed : GraphBuild := {}) : GraphBuild :=
  match trace with
  | .root => seed
  | .step previous vertex =>
      let graph := build data previous certified seed
      let nodeId := "v" ++ toString vertex.id
      let graph := connectFrontier graph nodeId
      { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [vertexJson data vertex certified] }
  | .dichotomy previous vertex leftMetadata left rightMetadata right =>
      let graph := build data previous certified seed
      let nodeId := "v" ++ toString vertex.id
      let graph := connectFrontier graph nodeId
      let graph := { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [vertexJson data vertex certified] }
      let (defaultLeftName, defaultRightName) :=
        binaryOutputNames vertex.key
      let addSide (graph : GraphBuild) (leftSide : Bool)
          (authored : OutputMetadata) (side : ProofTrace) :
          GraphBuild × List String :=
        let registered := binaryOutputDocumentation data vertex.key leftSide
        let defaultName :=
          if leftSide then defaultLeftName else defaultRightName
        let name := prefer authored.name (prefer registered.name defaultName)
        let note := prefer authored.note registered.note
        let closed := binaryOutputClosed data vertex.key leftSide
        match side with
        | .root =>
            let status := if closed || certified then "closed" else "open"
            let reason :=
              if closed then "registered branch closure"
              else if certified then "kernel-certified target"
              else "empty continuation"
            let (graph, endpoint) :=
              appendEndpoint graph nodeId name note status reason
                defaultName
            (graph, [endpoint])
        | _ =>
            let branchSeed : GraphBuild :=
              { graph with
                entry := none
                exits := []
                nodes := graph.nodes
                edges := graph.edges
                terminals := graph.terminals }
            let branch := build data side certified branchSeed
            let graph := { branch with entry := graph.entry }
            let graph := match branch.entry with
              | some target => appendEdge graph "output" nodeId target name note
                  (if closed then "closed" else "conditional")
                  (some (if leftSide then "left" else "right"))
              | none => graph
            (graph, branch.exits)
      let (graph, leftExits) := addSide graph true leftMetadata left
      let (graph, rightExits) := addSide graph false rightMetadata right
      { graph with exits := leftExits ++ rightExits }
  | .homogeneousBottleneck previous vertex exceptional structured bounded =>
      let graph := build data previous certified seed
      let nodeId := "v" ++ toString vertex.id
      let graph := connectFrontier graph nodeId
      let graph := { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [vertexJson data vertex certified] }
      let (graph, _targetEndpoint) :=
        appendEndpoint graph nodeId "target" "" "closed"
          "registered target output" "target"
      let addResidual (graph : GraphBuild) (name : String)
          (side : ProofTrace) : GraphBuild × List String :=
        match side with
        | .root =>
            let status := if certified then "closed" else "open"
            let reason :=
              if certified then "kernel-certified target"
              else "empty continuation"
            let (graph, endpoint) :=
              appendEndpoint graph nodeId name "" status reason name
            (graph, [endpoint])
        | _ =>
            let branchSeed : GraphBuild :=
              { graph with
                entry := none
                exits := []
                nodes := graph.nodes
                edges := graph.edges
                terminals := graph.terminals }
            let branch := build data side certified branchSeed
            let graph := { branch with entry := graph.entry }
            let graph := match branch.entry with
              | some target =>
                  appendEdge graph "output" nodeId target name ""
                    "conditional" (some name)
              | none => graph
            (graph, branch.exits)
      let (graph, exceptionalExits) :=
        addResidual graph "exceptional" exceptional
      let (graph, structuredExits) :=
        addResidual graph "structured" structured
      let (graph, boundedExits) :=
        addResidual graph "bounded" bounded
      { graph with
        exits := exceptionalExits ++ structuredExits ++ boundedExits }
  | .minimalCounterexample previous vertex counterexample =>
      let graph := build data previous certified seed
      let nodeId := "v" ++ toString vertex.id
      let graph := connectFrontier graph nodeId
      let graph := { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [vertexJson data vertex certified] }
      match counterexample with
      | .root => graph
      | _ =>
          let branchSeed : GraphBuild :=
            { graph with
              entry := none
              exits := []
              nodes := graph.nodes
              edges := graph.edges
              terminals := graph.terminals }
          let branch := build data counterexample certified branchSeed
          let graph := { branch with entry := graph.entry }
          let graph := match branch.entry with
            | some target =>
                appendEdge graph "output" nodeId target "counterexample" ""
                  "conditional" (some "counterexample")
            | none => graph
          { graph with exits := branch.exits }
  | .autoroute previous route metadata =>
      let graph := build data previous certified seed
      let source := "v" ++ toString route.sourceId
      { graph with
        exits := [source]
        pendingRoutes := graph.pendingRoutes ++ [{ source, route, metadata }] }

private def finalize (graph : GraphBuild) (certified : Bool) : GraphBuild :=
  if graph.exits.isEmpty then
    let terminalId := "t" ++ toString graph.nextTerminal
    { graph with
      entry := some terminalId
      terminals := graph.terminals ++ [.mkObj [
        ("id", .str terminalId), ("internal_id", .num graph.nextTerminal),
        ("kind", .str "proof_terminal"),
        ("status", .str (if certified then "closed" else "open")),
        ("reason", .str "empty proof DAG"),
        ("residual", .mkObj [
          ("kind", .str (if certified then "none"
            else "accumulated_strategy_residual")),
          ("disposition", .str (if certified then "closed" else "open")),
          ("baseline_ref", .str "problem.formal.baseline_predicate"),
          ("constraints", .mkObj [
            ("representation", .str "all_entry_paths"),
            ("terminal_ref", .str terminalId)
          ])
        ])
      ]]
      nextTerminal := graph.nextTerminal + 1 }
  else
    graph.exits.foldl (fun graph source =>
      if source.startsWith "t" then graph
      else
        let terminalId := "t" ++ toString graph.nextTerminal
        let terminal := .mkObj [
          ("id", .str terminalId), ("internal_id", .num graph.nextTerminal),
          ("kind", .str "proof_terminal"),
          ("status", .str (if certified then "closed" else "open")),
          ("reason", .str (if certified then "kernel-certified target"
            else "target-or-residual terminal")),
          ("residual", .mkObj [
            ("kind", .str (if certified then "none"
              else "accumulated_strategy_residual")),
            ("disposition", .str (if certified then "closed" else "open")),
            ("baseline_ref", .str "problem.formal.baseline_predicate"),
            ("constraints", .mkObj [
              ("representation", .str "all_entry_paths"),
              ("terminal_ref", .str terminalId)
            ])
          ])
        ]
        let graph := { graph with
          terminals := graph.terminals ++ [terminal]
          nextTerminal := graph.nextTerminal + 1 }
        appendEdge graph "terminal" source terminalId "" ""
          (if certified then "closed" else "open")) graph

private def graphJson
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) (trace : ProofTrace)
    (certified : Bool) : Lean.Json :=
  let graph := finalize (build data trace certified) certified
  .mkObj [
    ("entry", graph.entry.map Lean.Json.str |>.getD .null),
    ("nodes", .arr graph.nodes.toArray),
    ("edges", .arr graph.edges.toArray),
    ("terminals", .arr graph.terminals.toArray)
  ]

private def routeJson (ordinal : Nat) (route : ResolvedRoute)
    (metadata : RouteMetadata) : Lean.Json :=
  .mkObj [
    ("id", .str s!"route-{ordinal}"),
    ("kind", .str "autoroute"),
    ("source_id", .str s!"v{route.sourceId}"),
    ("destination_id", .str s!"v{route.destinationId}"),
    ("source_depth", .num route.sourceDepth),
    ("destination_depth", .num route.destinationDepth),
    ("scope", .str route.scopeName),
    ("relation", .str route.relation),
    ("compatible_candidates", .arr <|
      ((route.compatibleCandidates.zip route.compatibleCandidateDepths).map
        fun (id, depth) => Lean.Json.mkObj [
        ("node_id", .str s!"v{id}"),
        ("depth", .num depth),
        ("relation", .str route.relation),
        ("capability_status", .str "satisfied")
      ]).toArray),
    ("selection", .mkObj [
      ("rule", .str route.selectedBy),
      ("selected_candidate_id", .str s!"v{route.destinationId}"),
      ("tie_break", .str "smallest_stable_structural_id")
    ]),
    ("bridge_provenance", .mkObj [
      ("relation_witness", .str "BridgeCertificate.residual_eq"),
      ("target_congruence", .str "literal_residual_identity"),
      ("destination_requirements",
        strings ["typed_continuation_entry", "literal_source_capabilities"]),
      ("ledger_ancestors", strings ["literal_predecessor_stage"]),
      ("framework_lemmas", strings [
        "Hypostructure.Core.Residual.Ledger.extend_previous",
        "Hypostructure.Core.Residual.Ledger.residualOf_extend",
        "Hypostructure.Core.Strategy.HaltingProgram.snoc_previous"
      ]),
      ("ledger_extension",
        .str "Hypostructure.Core.Residual.Ledger.Extension")
    ]),
    ("presentation", .mkObj [
      ("label", optionalString metadata.name),
      ("note", optionalString metadata.note),
      ("tags", strings metadata.tags)
    ]),
    ("bridge_work", .num route.work),
    ("destination_work", .num route.destinationWork),
    ("work", .num (route.work + route.destinationWork)),
    ("acyclic", .bool true)
  ]

private partial def collectRouteJson :
    ProofTrace -> Nat -> List Lean.Json × Nat
  | .root, next => ([], next)
  | .step previous _, next => collectRouteJson previous next
  | .dichotomy previous _ _ left _ right, next =>
      let (priorRoutes, next) := collectRouteJson previous next
      let (leftRoutes, next) := collectRouteJson left next
      let (rightRoutes, next) := collectRouteJson right next
      (priorRoutes ++ leftRoutes ++ rightRoutes, next)
  | .homogeneousBottleneck previous _ exceptional structured bounded, next =>
      let (priorRoutes, next) := collectRouteJson previous next
      let (exceptionalRoutes, next) := collectRouteJson exceptional next
      let (structuredRoutes, next) := collectRouteJson structured next
      let (boundedRoutes, next) := collectRouteJson bounded next
      (priorRoutes ++ exceptionalRoutes ++ structuredRoutes ++ boundedRoutes,
        next)
  | .minimalCounterexample previous _ counterexample, next =>
      let (priorRoutes, next) := collectRouteJson previous next
      let (counterexampleRoutes, next) :=
        collectRouteJson counterexample next
      (priorRoutes ++ counterexampleRoutes, next)
  | .autoroute previous route metadata, next =>
      let (routes, next) := collectRouteJson previous next
      (routes ++ [routeJson next route metadata], next + 1)

private def registrations
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T) : Lean.Json :=
  let family (kind : String) (fields : List String)
      (values : List Core.Documentation) :=
    (List.range values.length |>.zip values).map fun (index, metadata) =>
      Lean.Json.mkObj [
      ("id", .str (kind ++ ":" ++ toString index)),
      ("kind", .str kind), ("index", .num index),
      ("presentation", documentation metadata),
      ("components", .arr #[]),
      ("interface", .arr (fields.map (fun field => Lean.Json.mkObj [
        ("name", .str field),
        ("role", .str "contract_field")
      ])).toArray),
      ("outputs", .arr #[]),
      ("closures", .mkObj [
        ("target", .bool false),
        ("residual", .bool false)
      ])
    ]
  let dichotomies :=
    (List.range data.dichotomies.length |>.zip data.dichotomies).map
      fun (index, split) => Lean.Json.mkObj [
    ("id", .str ("dichotomy:" ++ toString index)),
    ("kind", .str "dichotomy"), ("index", .num index),
    ("presentation", documentation split.metadata),
    ("components", .arr (split.components.map documentation).toArray),
    ("interface", .arr (["LeftPayload", "RightPayload", "classify",
      "closeLeft", "closeRight"].map (fun field => Lean.Json.mkObj [
        ("name", .str field),
        ("role", .str "contract_field")
      ])).toArray),
    ("outputs", .arr #[
      .mkObj [
        ("port", .str "left"),
        ("presentation", documentation split.leftMetadata),
        ("closed", .bool split.closeLeft.isSome)
      ],
      .mkObj [
        ("port", .str "right"),
        ("presentation", documentation split.rightMetadata),
        ("closed", .bool split.closeRight.isSome)
      ]
    ]),
    ("closures", .mkObj [
      ("target", .bool (split.closeLeft.isSome || split.closeRight.isSome)),
      ("residual", .bool (split.closeLeft.isSome && split.closeRight.isSome))
    ])
  ]
  let minimalCounterexamples :=
    ((List.range data.minimalCounterexamples.length).zip
      data.minimalCounterexamples).map fun (index, selection) =>
      Lean.Json.mkObj [
        ("id", .str ("minimal_counterexample_selection:" ++ toString index)),
        ("kind", .str "minimal_counterexample_selection"),
        ("index", .num index),
        ("presentation", documentation selection.metadata),
        ("components", .arr
          (selection.components.map documentation).toArray),
        ("interface", .arr
          (["progress", "targetDecidable", "initialState"].map
            (fun field => Lean.Json.mkObj [
              ("name", .str field),
              ("role", .str "framework_owned_input")
            ])).toArray),
        ("outputs", .arr #[
          .mkObj [
            ("port", .str "counterexample"),
            ("presentation", documentation selection.terminalMetadata),
            ("closed", .bool false)
          ]
        ]),
        ("closures", .mkObj [
          ("target", .bool true),
          ("residual", .bool false)
        ])
      ]
  let counterexampleLocalizations :=
    ((List.range data.counterexampleLocalizations.length).zip
      data.counterexampleLocalizations).map fun (index, localization) =>
      Lean.Json.mkObj [
        ("id", .str ("counterexample_localization:" ++ toString index)),
        ("kind", .str "counterexample_localization"),
        ("index", .num index),
        ("presentation", documentation localization.metadata),
        ("components", .arr
          (localization.components.map documentation).toArray),
        ("interface", .arr
          (["selection"].map
            (fun field => Lean.Json.mkObj [
              ("name", .str field),
              ("role", .str "contract_field")
            ])).toArray),
        ("outputs", .arr #[
          .mkObj [
            ("port", .str "local_residual"),
            ("presentation", documentation localization.terminalMetadata),
            ("closed", .bool false)
          ]
        ]),
        ("closures", .mkObj [
          ("target", .bool true),
          ("residual", .bool false)
        ])
      ]
  let finiteBarrierEnumerations :=
    (List.range data.finiteBarrierEnumerations.length).map fun index =>
      Lean.Json.mkObj [
        ("id", .str ("finite_barrier_enumeration:" ++ toString index)),
        ("kind", .str "finite_barrier_enumeration"),
        ("index", .num index),
        ("presentation", documentation {}),
        ("components", .arr #[
          documentation {
            name := "whole-support barrier enumeration"
            note := "Core filters the complete candidate schedule and computes \
              every safe/flat relation-barrier row through CT16."
          }
        ]),
        ("interface", .arr
          (["Candidate", "candidates", "accepted", "labelCount", "profile",
            "leftLength", "rightLength"].map
            (fun field => Lean.Json.mkObj [
              ("name", .str field),
              ("role", .str "residual_semantics")
            ])).toArray),
        ("outputs", .arr #[
          .mkObj [
            ("port", .str "computed_table"),
            ("presentation", documentation {}),
            ("closed", .bool false)
          ]
        ]),
        ("closures", .mkObj [
          ("target", .bool false),
          ("residual", .bool false)
        ])
      ]
  let homogeneousBottlenecks :=
    (List.range data.homogeneousBottlenecks.length).map fun index =>
      Lean.Json.mkObj [
        ("id", .str ("homogeneous_bottleneck:" ++ toString index)),
        ("kind", .str "homogeneous_bottleneck"),
        ("index", .num index),
        ("presentation", documentation {}),
        ("components", .arr #[]),
        ("interface", .arr
          (["Terminal", "RoutedResidual"].map
            (fun field => Lean.Json.mkObj [
              ("name", .str field),
              ("role", .str "contract_field")
            ])).toArray),
        ("outputs", .arr #[
          .mkObj [
            ("port", .str "target"),
            ("presentation", documentation {}),
            ("closed", .bool true)
          ],
          .mkObj [
            ("port", .str "exceptional"),
            ("presentation", documentation {}),
            ("closed", .bool false)
          ],
          .mkObj [
            ("port", .str "structured"),
            ("presentation", documentation {}),
            ("closed", .bool false)
          ],
          .mkObj [
            ("port", .str "bounded"),
            ("presentation", documentation {}),
            ("closed", .bool false)
          ]
        ]),
        ("closures", .mkObj [
          ("target", .bool true),
          ("residual", .bool false)
        ])
      ]
  .arr ((family "ordered_witness_scan"
      ["Item", "schedule", "witness", "witnessDecidable"]
      (data.scans.map Core.ScanData.metadata) ++
    family "response_classifier"
      ["Item", "Response", "Class", "schedule", "observe", "classify"]
      (data.responses.map Core.ResponseData.metadata) ++
    family "capacity_ledger"
      ["Item", "Class", "schedule", "classify", "contribution", "capacity",
        "totalWithin"]
      (data.capacities.map Core.CapacityData.metadata) ++
    family "support_localization"
      ["Cell", "schedule", "localBudget", "selected", "selected_negative"]
      (data.localizations.map Core.LocalizationData.metadata) ++
    family "rank_budget"
      ["rank", "budget", "threshold", "high", "low", "exhaustive"]
      (data.rankBudgets.map Core.RankBudgetData.metadata) ++
    family "closed_code"
      ["Code", "schedule", "targetCode", "observedCode", "closed"]
      (data.closedCodes.map Core.ClosedCodeData.metadata) ++
    dichotomies ++
    finiteBarrierEnumerations ++
    homogeneousBottlenecks ++
    counterexampleLocalizations ++
    minimalCounterexamples).toArray)

private def certificate
    {P : Core.Problem} {T : Core.Target P}
    (definitionMetadata : Core.ProblemMetadata)
    (data : Core.StrategyData P T)
    (descriptor : ProblemDescriptor) (trace : ProofTrace)
    (checksBound workBound : Nat) (closed : Bool := true) : Lean.Json :=
  let ⟨declaration, moduleName, sourceExpression, ambientType,
    baselinePredicate, branchState, targetPredicate, statement⟩ := descriptor
  let definitionRef :=
    if sourceExpression.isEmpty then moduleName else moduleName ++ "." ++ sourceExpression
  let formal (reference rendering : String) := Lean.Json.mkObj [
    ("declaration_ref", .str reference),
    ("rendering", .str rendering)
  ]
  .mkObj [
    ("$schema", .str "https://json-schema.org/draft/2020-12/schema"),
    ("schema_id", .str
      "https://structural-exhaustion.local/schemas/hypostructure-proof-run.schema.json"),
    ("artifact_type", .str "hypostructure_proof_run"),
    ("schema_version", .str "2.3.0"),
    ("framework", .mkObj [
      ("name", .str "Hypostructure"),
      ("version", .str "0.1.0"),
      ("proof_authority", .str "Lean kernel")
    ]),
    ("run", .mkObj [
      ("name", .str declaration),
      ("kind", .str (if closed then
        "certified_declaration" else "certified_reduction")),
      ("certified", .bool true)
    ]),
    ("problem", .mkObj [
      ("id", .str definitionRef),
      ("identity", .mkObj [
        ("definition_ref", .str definitionRef),
        ("module", .str moduleName),
        ("source_expression", .str sourceExpression)
      ]),
      ("presentation", .mkObj [
        ("label", optionalString definitionMetadata.name),
        ("note", optionalString definitionMetadata.note),
        ("tags", strings definitionMetadata.tags),
        ("authored_signature", optionalString definitionMetadata.signature),
        ("authored_statement", optionalString definitionMetadata.statement)
      ]),
      ("formal", .mkObj [
        ("ambient_type", formal (definitionRef ++ ".problem.Ambient") ambientType),
        ("baseline_predicate",
          formal (definitionRef ++ ".problem.Baseline") baselinePredicate),
        ("branch_state",
          formal (definitionRef ++ ".problem.BranchState") branchState),
        ("target_predicate",
          formal (definitionRef ++ ".target.Predicate") targetPredicate),
        ("statement", formal (definitionRef ++ ".target.Statement") statement)
      ])
    ]),
    ("strategy_registrations", registrations data),
    ("dag", .mkObj [
      ("representation", .str "normalized_directed_graph"),
      ("entry", (graphJson data trace closed).getObjValD "entry"),
      ("nodes", (graphJson data trace closed).getObjValD "nodes"),
      ("edges", (graphJson data trace closed).getObjValD "edges"),
      ("terminals", (graphJson data trace closed).getObjValD "terminals"),
      ("autoroutes", .arr (collectRouteJson trace 0).1.toArray)
    ]),
    ("execution", .mkObj [
      ("result", .str (if closed then "certified" else "reduced")),
      ("statement_ref", .str (if closed then
        "problem.formal.statement" else "execution.target_or_residual")),
      ("checks_bound", .num checksBound),
      ("work_bound", .num workBound),
      ("residual_disposition", .str (if closed then "none" else "retained"))
    ]),
    ("trust", .mkObj [
      ("kernel_checked", .bool true),
      ("proof_term_exported", .bool false),
      ("verification_note", .str
        "JSON is an auditable visualization artifact; Lean remains the proof authority.")
    ])
  ]

end CertificateJson

private structure CompileTrace where
  path : List StrategyKey
  proofTrace : ProofTrace
  checksBound : Nat
  workBound : Nat
  deriving Repr

private noncomputable def traceOf
    {P : Core.Problem} {T : Core.Target P}
    (data : Core.StrategyData P T)
    (dag : Blueprint data .expanded) : CompileTrace where
  path := dag.pathOf
  proofTrace := dag.proofTrace
  checksBound := dag.workBoundOf data
  workBound := dag.workBoundOf data

/-! ## Declaration, finalization, report -/

/-- Public sealed result of compiling any valid official DAG.  Unlike a
`ProblemDeclaration`, a reduction may retain a terminal residual.  Its
constructor and compiled program remain private: applications obtain one only
through `reduceDag%`. -/
structure ReductionDeclaration where
  private mk ::
  private problem : Core.ProblemDefinition.{uAmbient, uBranch, uData}
  private dag : Blueprint problem.data .expanded
  private program : HaltingProgram.{max uAmbient uBranch uData}
    problem.problem problem.target
  private trace : CompileTrace
  private descriptor : ProblemDescriptor

/-- Seal the exact compiler product without requiring target-only closure. -/
private noncomputable def ReductionDeclaration.ofValidated
    (problem : Core.ProblemDefinition.{uAmbient, uBranch, uData})
    (dag : Blueprint problem.data .expanded)
    (compilation : Compilation problem)
    (descriptor : ProblemDescriptor) :
    ReductionDeclaration :=
  .mk problem dag compilation.program (traceOf problem.data dag) descriptor

/-- Public application declaration.  Constructed exclusively by the sealed
`ofDag%` frontend; its compiled program, trace, and closure proof are
inaccessible. -/
structure ProblemDeclaration where
  private mk ::
  private problem : Core.ProblemDefinition.{uAmbient, uBranch, uData}
  private dag : Blueprint problem.data .expanded
  private program : HaltingProgram.{max uAmbient uBranch uData}
    problem.problem problem.target
  private trace : CompileTrace
  private descriptor : ProblemDescriptor
  private closed : program.Closes

/-- Sealed constructor behind the `ofDag%` frontend.  A declaration is only
built from validated inputs — a compliant blueprint and a certifying
problem — so every report certifies the registered statement
unconditionally, and the compiler below never receives anything else. -/
private noncomputable def ProblemDeclaration.ofValidated
    (problem : Core.ProblemDefinition.{uAmbient, uBranch, uData})
    (dag : Blueprint problem.data .expanded)
    (compilation : Compilation problem)
    (descriptor : ProblemDescriptor)
    (closed : compilation.closes.isSome = true) :
    ProblemDeclaration :=
  .mk problem dag compilation.program
    (traceOf problem.data dag) descriptor (compilation.closes.get closed).down

/-- Sole application entrypoint: `ofDag% definition dag`.  The DAG type
already contains only resolved framework Strategies; the frontend performs
no author-supplied registration or compliance step. -/
scoped syntax (name := ofDagFrontend) "ofDag% " term:max term:max : term

/-- Seal any valid official DAG as an unconditional target-or-residual
reduction.  This syntax accepts exactly the same problem and DAG language as
`ofDag%`; it accepts no residual, outcome, or certification argument. -/
scoped syntax (name := reduceDagFrontend) "reduceDag% " term:max term:max : term

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def captureProblemDescriptor (problemE : Expr)
    (sourceExpression declaration : String) : TermElabM Expr := do
  let problem ← mkAppM ``Core.ProblemDefinition.problem #[problemE]
  let target ← mkAppM ``Core.ProblemDefinition.target #[problemE]
  let ambient ← mkAppM ``Core.Problem.Ambient #[problem]
  let baseline ← mkAppM ``Core.Problem.Baseline #[problem]
  let branchState ← mkAppM ``Core.Problem.BranchState #[problem]
  let predicate ← mkAppM ``Core.Target.Predicate #[target]
  let statement ← mkAppM ``Core.Target.Statement #[target]
  let render (e : Expr) : TermElabM String :=
    return (toString (← ppExpr e)).replace "\n" " "
  let moduleName := (← getEnv).mainModule.toString
  mkAppM ``ProblemDescriptor.mk #[
    mkStrLit declaration,
    mkStrLit moduleName,
    mkStrLit sourceExpression,
    mkStrLit (← render ambient),
    mkStrLit (← render baseline),
    mkStrLit (← render branchState),
    mkStrLit (← render predicate),
    mkStrLit (← render statement)
  ]

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def elaborateProgram (dataE : Expr) (stx : Syntax) :
    TermElabM Expr := do
  let programType ← mkAppM ``Program #[dataE]
  let value ← Term.elabTerm stx (some programType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  let valueType ← whnf (← inferType value)
  if ← isDefEq valueType programType then
    let expansion ← withTransparency .all <|
      reduce (← mkAppM ``Program.expand #[value])
    match expansion.getAppFn.constName? with
    | some ``Except.ok =>
        return expansion.getAppArgs.back!
    | some ``Except.error =>
        throwError (Validate.rejection
          "invalid autoroute program: Core could not derive a typed acyclic bridge from a targetless branch terminal to a compatible continuation.")
    | _ =>
        throwError (Validate.rejection
          "the routing program must reduce to a closed literal whose targetless routes are resolved exclusively by Core.")
  else
    throwError (Validate.rejection
      "the second argument must be the canonical `Dag.Program` built from existing framework Strategies.")

private structure SiblingContinuationEntry where
  id : Nat
  dag : Lean.Expr

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private partial def firstExpandedExecutionId
    (dagE : Expr) (nextId : Nat) : MetaM (Option Nat) := do
  let dagE ← withTransparency .all <| whnf dagE
  let args := dagE.getAppArgs
  let fromEnd (offset : Nat) : MetaM Expr := do
    if offset < args.size then
      pure args[args.size - (offset + 1)]!
    else
      throwError (Validate.rejection
        "Core encountered malformed expanded DAG syntax while discovering \
        sibling continuation entries.")
  match dagE.getAppFn.constName? with
  | some ``Blueprint.root => pure none
  | some ``Blueprint.step =>
      let restE ← fromEnd 1
      return (← firstExpandedExecutionId restE (nextId + 1)).orElse
        fun _ => some nextId
  | some ``Blueprint.binaryBranch =>
      let restE ← fromEnd 3
      return (← firstExpandedExecutionId restE (nextId + 1)).orElse
        fun _ => some nextId
  | some ``Blueprint.homogeneousBottleneckBranches =>
      let restE ← fromEnd 4
      return (← firstExpandedExecutionId restE (nextId + 1)).orElse
        fun _ => some nextId
  | some ``Blueprint.minimalCounterexample =>
      let restE ← fromEnd 2
      return (← firstExpandedExecutionId restE (nextId + 1)).orElse
        fun _ => some nextId
  | some ``Blueprint.annotate
  | some ``Blueprint.labelled
  | some ``Blueprint.documented =>
      firstExpandedExecutionId (← fromEnd 1) nextId
  | some ``Blueprint.resolvedRoute =>
      firstExpandedExecutionId (← fromEnd 2) nextId
  | _ =>
      throwError (Validate.rejection
        "Core found a non-expanded constructor while discovering sibling \
        continuation entries.")

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private partial def collectSiblingContinuationEntries
    (dagE : Expr) (nextId : Nat) :
    MetaM (Array SiblingContinuationEntry × Nat) := do
  let dagE ← withTransparency .all <| whnf dagE
  let args := dagE.getAppArgs
  let fromEnd (offset : Nat) : MetaM Expr := do
    if offset < args.size then
      pure args[args.size - (offset + 1)]!
    else
      throwError (Validate.rejection
        "Core encountered malformed expanded DAG syntax while collecting \
        sibling continuations.")
  let addEntry (entries : Array SiblingContinuationEntry)
      (branch : Expr) (startId : Nat) : MetaM (Array SiblingContinuationEntry) := do
    match ← firstExpandedExecutionId branch startId with
    | none => pure entries
    | some id => pure (entries.push { id, dag := branch })
  match dagE.getAppFn.constName? with
  | some ``Blueprint.root => pure (#[], nextId)
  | some ``Blueprint.step =>
      collectSiblingContinuationEntries (← fromEnd 1) (nextId + 1)
  | some ``Blueprint.binaryBranch =>
      let restE ← fromEnd 3
      let leftE ← fromEnd 1
      let rightE ← fromEnd 0
      let (restEntries, leftStart) ←
        collectSiblingContinuationEntries restE (nextId + 1)
      let entries ← addEntry restEntries leftE leftStart
      let (leftEntries, rightStart) ←
        collectSiblingContinuationEntries leftE leftStart
      let entries := entries ++ leftEntries
      let entries ← addEntry entries rightE rightStart
      let (rightEntries, nextId) ←
        collectSiblingContinuationEntries rightE rightStart
      pure (entries ++ rightEntries, nextId)
  | some ``Blueprint.homogeneousBottleneckBranches =>
      let restE ← fromEnd 4
      let exceptionalE ← fromEnd 2
      let structuredE ← fromEnd 1
      let boundedE ← fromEnd 0
      let (restEntries, exceptionalStart) ←
        collectSiblingContinuationEntries restE (nextId + 1)
      let entries ← addEntry restEntries exceptionalE exceptionalStart
      let (exceptionalEntries, structuredStart) ←
        collectSiblingContinuationEntries exceptionalE exceptionalStart
      let entries := entries ++ exceptionalEntries
      let entries ← addEntry entries structuredE structuredStart
      let (structuredEntries, boundedStart) ←
        collectSiblingContinuationEntries structuredE structuredStart
      let entries := entries ++ structuredEntries
      let entries ← addEntry entries boundedE boundedStart
      let (boundedEntries, nextId) ←
        collectSiblingContinuationEntries boundedE boundedStart
      pure (entries ++ boundedEntries, nextId)
  | some ``Blueprint.minimalCounterexample =>
      let (entries, nextId) ←
        collectSiblingContinuationEntries (← fromEnd 2) (nextId + 1)
      pure (entries, nextId + 4)
  | some ``Blueprint.annotate
  | some ``Blueprint.labelled
  | some ``Blueprint.documented =>
      collectSiblingContinuationEntries (← fromEnd 1) nextId
  | some ``Blueprint.resolvedRoute =>
      collectSiblingContinuationEntries (← fromEnd 2) nextId
  | _ =>
      throwError (Validate.rejection
        "Core found a non-expanded constructor while collecting sibling \
        continuations.")

private structure ElaboratedManifest where
  output : Lean.Expr
  proof : Lean.Expr

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def applyConstructorAtType
    (constructor : Name) (explicitArguments : Array Expr)
    (expected : Expr) : TermElabM Expr := do
  let initial ← mkConstWithFreshMVarLevels constructor
  let rec applyArguments (fuel : Nat) (term type : Expr) (index : Nat) :
      TermElabM Expr := do
    match fuel with
    | 0 =>
        throwError (Validate.rejection
          "Core exhausted the constructor arity derived from the sealed \
          manifest-verification constructor.")
    | fuel + 1 =>
        let type ← whnf type
        match type with
        | .forallE binderName domain body binderInfo =>
            let argument ←
              match binderInfo with
              | .default =>
                  if index < explicitArguments.size then
                    let argument := explicitArguments[index]!
                    unless ← isDefEq (← inferType argument) domain do
                      throwError (Validate.rejection
                        "Core found an ill-typed explicit constructor argument \
                        while lowering the expanded DAG.")
                    pure argument
                  else
                    throwError (Validate.rejection
                      "Core found a missing explicit constructor argument while \
                      lowering the expanded DAG.")
              | .instImplicit =>
                  mkFreshExprMVar domain .synthetic binderName
              | _ =>
                  mkFreshExprMVar domain .natural binderName
            let nextIndex :=
              if binderInfo == .default then index + 1 else index
            applyArguments fuel (mkApp term argument)
              (body.instantiate1 argument) nextIndex
        | _ =>
            unless index = explicitArguments.size do
              throwError (Validate.rejection
                "Core found excess explicit constructor arguments while \
                lowering the expanded DAG.")
            unless ← isDefEq expected type do
              throwError (Validate.rejection
                "Core could not construct the typed manifest proof for \
                the expanded DAG.\n"
                ++ s!"actual: {type}\nexpected: {expected}")
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars term
  let initialType ← inferType initial
  applyArguments (initialType.getForallArity + 1) initial initialType 0

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def elaborateVerifiedManifestStep
    (siblings : Array SiblingContinuationEntry)
    (recurse : Expr → Expr → TermElabM ElaboratedManifest)
    (dagE inputE : Expr) : TermElabM ElaboratedManifest := do
  let dagE ← withTransparency .all <| whnf dagE
  let args := dagE.getAppArgs
  let argumentFromEnd (offset : Nat) : TermElabM Expr := do
    if offset < args.size then
      pure args[args.size - (offset + 1)]!
    else
      throwError (Validate.rejection
        "Core encountered malformed expanded DAG syntax during sealed \
        execution lowering.")
  match dagE.getAppFn.constName? with
  | some ``Blueprint.root =>
      let expected ← mkAppM ``VerifiedManifest #[dagE, inputE, inputE]
      let proof ← applyConstructorAtType ``VerifiedManifest.root #[] expected
      pure { output := inputE, proof }
  | some ``Blueprint.step =>
      let strategyE ← argumentFromEnd 0
      let restE ← argumentFromEnd 1
      let preceding ← recurse restE inputE
      let strategyType ← withTransparency .all <| whnf (← inferType strategyE)
      unless strategyType.getAppFn.constName? == some ``StrategyRef do
        throwError (Validate.rejection
          "Core found a malformed scalar Strategy reference while lowering \
          fact manifest.")
      let strategyTypeArgs := strategyType.getAppArgs
      if strategyTypeArgs.isEmpty then
        throwError (Validate.rejection
          "Core could not recover the registered Strategy data while \
          lowering the fact manifest.")
      let dataE := strategyTypeArgs[strategyTypeArgs.size - 1]!
      let keyE ← mkAppM ``StrategyRef.keyView #[strategyE]
      let resolvedE ← mkAppM ``StrategyRef.resolved #[strategyE]
      let requirementTest ←
        mkAppM ``StrategyKey.requirementsMet
          #[dataE, keyE, resolvedE, preceding.output]
      let requirementResult ← withTransparency .all <| reduce requirementTest
      unless requirementResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed Strategy execution queried a ledger capability that no \
          preceding Strategy produced on this branch.")
      let valid ← mkEqRefl (mkConst ``Bool.true)
      let produced ←
        mkAppM ``StrategyKey.productions #[dataE, keyE, resolvedE]
      let freshTest ←
        mkAppM ``CapabilityKey.fresh #[produced, preceding.output]
      let freshResult ← withTransparency .all <| reduce freshTest
      unless freshResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed Strategy execution attempted to publish a semantic fact \
          already present on this branch.")
      let fresh ← mkEqRefl (mkConst ``Bool.true)
      let output ← mkAppM ``List.append #[produced, preceding.output]
      let expected ← mkAppM ``VerifiedManifest #[dagE, inputE, output]
      let proof ← applyConstructorAtType ``VerifiedManifest.step
        #[strategyE, preceding.proof, valid, fresh] expected
      pure { output, proof }
  | some ``Blueprint.binaryBranch =>
      let rightE ← argumentFromEnd 0
      let leftE ← argumentFromEnd 1
      let strategyE ← argumentFromEnd 2
      let restE ← argumentFromEnd 3
      let preceding ← recurse restE inputE
      let strategyType ← withTransparency .all <| whnf (← inferType strategyE)
      unless strategyType.getAppFn.constName? == some ``BinaryStrategyRef do
        throwError (Validate.rejection
          "Core found a malformed binary Strategy reference while lowering \
          fact manifest.")
      let strategyTypeArgs := strategyType.getAppArgs
      if strategyTypeArgs.isEmpty then
        throwError (Validate.rejection
          "Core could not recover the registered Strategy data while \
          lowering the binary fact manifest.")
      let dataE := strategyTypeArgs[strategyTypeArgs.size - 1]!
      let keyE ← mkAppM ``BinaryStrategyRef.keyView #[strategyE]
      let resolvedE ← mkAppM ``BinaryStrategyRef.resolved #[strategyE]
      let requirementTest ←
        mkAppM ``StrategyKey.requirementsMet
          #[dataE, keyE, resolvedE, preceding.output]
      let requirementResult ← withTransparency .all <| reduce requirementTest
      unless requirementResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed binary Strategy execution queried a ledger capability that \
          no preceding Strategy produced on this branch.")
      let valid ← mkEqRefl (mkConst ``Bool.true)
      let leftProduced ←
        mkAppM ``BinaryStrategyRef.leftProductions #[strategyE]
      let rightProduced ←
        mkAppM ``BinaryStrategyRef.rightProductions #[strategyE]
      let leftFreshTest ←
        mkAppM ``CapabilityKey.fresh #[leftProduced, preceding.output]
      let leftFreshResult ← withTransparency .all <| reduce leftFreshTest
      unless leftFreshResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed binary Strategy left arm attempted to republish a semantic \
          fact already present on this branch.")
      let rightFreshTest ←
        mkAppM ``CapabilityKey.fresh #[rightProduced, preceding.output]
      let rightFreshResult ← withTransparency .all <| reduce rightFreshTest
      unless rightFreshResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed binary Strategy right arm attempted to republish a semantic \
          fact already present on this branch.")
      let leftFresh ← mkEqRefl (mkConst ``Bool.true)
      let rightFresh ← mkEqRefl (mkConst ``Bool.true)
      let leftInput ← mkAppM ``List.append #[leftProduced, preceding.output]
      let rightInput ← mkAppM ``List.append #[rightProduced, preceding.output]
      let left ← recurse leftE leftInput
      let right ← recurse rightE rightInput
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, preceding.output]
      let proof ← applyConstructorAtType ``VerifiedManifest.binaryBranch
        #[strategyE, preceding.proof, valid, leftFresh, rightFresh,
          left.proof, right.proof] expected
      pure {
        output := preceding.output
        proof
      }
  | some ``Blueprint.homogeneousBottleneckBranches =>
      let boundedE ← argumentFromEnd 0
      let structuredE ← argumentFromEnd 1
      let exceptionalE ← argumentFromEnd 2
      let indexE ← argumentFromEnd 3
      let restE ← argumentFromEnd 4
      let preceding ← recurse restE inputE
      let restType ← withTransparency .all <| whnf (← inferType restE)
      let restTypeArgs := restType.getAppArgs
      if restTypeArgs.size < 2 then
        throwError (Validate.rejection
          "Core could not recover the registered Strategy data while \
          lowering the homogeneous-bottleneck fact manifest.")
      let dataE := restTypeArgs[restTypeArgs.size - 2]!
      -- Both `StrategyKey.homogeneousBottleneck` and
      -- `CapabilityKey.homogeneousHandoff` below take a `Nat`; `indexE` is the
      -- constructor's `Fin` and `mkAppM` inserts no coercion.  The typed
      -- `VerifiedManifest.homogeneousBottleneckBranches` publishes `↑index`.
      let indexNatE ← mkAppM ``Fin.val #[indexE]
      let keyE ← mkAppM ``StrategyKey.homogeneousBottleneck #[indexNatE]
      let resolvedE ← mkAppM ``Fin.isLt #[indexE]
      let requirementTest ←
        mkAppM ``StrategyKey.requirementsMet
          #[dataE, keyE, resolvedE, preceding.output]
      let requirementResult ← withTransparency .all <| reduce requirementTest
      unless requirementResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed homogeneous-bottleneck execution queried a ledger capability \
          that no preceding Strategy produced on this branch.")
      let valid ← mkEqRefl (mkConst ``Bool.true)
      let exceptional ← recurse exceptionalE preceding.output
      let structuredInput ←
        mkAppM ``List.cons
          #[← mkAppM ``CapabilityKey.homogeneousHandoff #[indexNatE],
            preceding.output]
      let handoffProduced ← mkAppM ``List.cons
        #[← mkAppM ``CapabilityKey.homogeneousHandoff #[indexNatE],
          ← mkAppM ``List.nil #[mkConst ``CapabilityKey]]
      let handoffFreshTest ←
        mkAppM ``CapabilityKey.fresh #[handoffProduced, preceding.output]
      let handoffFreshResult ←
        withTransparency .all <| reduce handoffFreshTest
      unless handoffFreshResult.isConstOf ``Bool.true do
        throwError (Validate.rejection
          "sealed homogeneous handoff attempted to republish a semantic fact \
          already present on this branch.")
      let handoffFresh ← mkEqRefl (mkConst ``Bool.true)
      let structured ← recurse structuredE structuredInput
      let bounded ← recurse boundedE preceding.output
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, preceding.output]
      let proof ← applyConstructorAtType
        ``VerifiedManifest.homogeneousBottleneckBranches
        #[indexE, preceding.proof, valid, handoffFresh, exceptional.proof,
          structured.proof, bounded.proof] expected
      pure {
        output := preceding.output
        proof
      }
  | some ``Blueprint.minimalCounterexample =>
      let metadataE ← argumentFromEnd 0
      let indexE ← argumentFromEnd 1
      let restE ← argumentFromEnd 2
      let preceding ← recurse restE inputE
      -- `CapabilityKey.minimalClosureAt` takes a `Nat`; `indexE` is the
      -- constructor's `Fin`, and `mkAppM` inserts no coercion.  The typed
      -- `VerifiedManifest.minimalCounterexample` publishes `↑index`, so the manifest
      -- key has to be built from `Fin.val` to agree with it.
      let exactKey ← mkAppM ``CapabilityKey.minimalClosureAt
        #[← mkAppM ``Fin.val #[indexE]]
      let withContext ← mkAppM ``List.cons
        #[mkConst ``CapabilityKey.minimalContext,
          ← mkAppM ``List.nil #[mkConst ``CapabilityKey]]
      let output ← mkAppM ``List.cons #[exactKey, withContext]
      let empty ← mkAppM ``List.nil #[mkConst ``CapabilityKey]
      let precedingIsEmpty ← withTransparency .all <| isDefEq preceding.output empty
      unless precedingIsEmpty do
        throwError (Validate.rejection
          "minimal-counterexample scope initialization must precede every \
          fact-producing Strategy; committed facts can never be rebased away.")
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, output]
      let proof ←
        applyConstructorAtType ``VerifiedManifest.minimalCounterexample
          #[restE, indexE, metadataE, preceding.proof] expected
      pure {
        output := output
        proof
      }
  | some ``Blueprint.annotate =>
      let restE ← argumentFromEnd 1
      let preceding ← recurse restE inputE
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, preceding.output]
      let proof ← applyConstructorAtType ``VerifiedManifest.annotate
        #[preceding.proof] expected
      pure {
        output := preceding.output
        proof
      }
  | some ``Blueprint.labelled =>
      let restE ← argumentFromEnd 1
      let preceding ← recurse restE inputE
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, preceding.output]
      let proof ← applyConstructorAtType ``VerifiedManifest.labelled
        #[preceding.proof] expected
      pure {
        output := preceding.output
        proof
      }
  | some ``Blueprint.documented =>
      let restE ← argumentFromEnd 1
      let preceding ← recurse restE inputE
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, preceding.output]
      let proof ← applyConstructorAtType ``VerifiedManifest.documented
        #[preceding.proof] expected
      pure {
        output := preceding.output
        proof
      }
  | some ``Blueprint.resolvedRoute =>
      let metadataE ← argumentFromEnd 0
      let routeE ← argumentFromEnd 1
      let restE ← argumentFromEnd 2
      let preceding ← recurse restE inputE
      let expected ←
        mkAppM ``VerifiedManifest #[dagE, inputE, preceding.output]
      let siblingTest ← mkAppM ``ResolvedRoute.routesToSibling #[routeE]
      let siblingResult ← withTransparency .all <| reduce siblingTest
      let proof ←
        if siblingResult.isConstOf ``Bool.true then
          let destinationIdE ←
            mkAppM ``ResolvedRoute.destinationId #[routeE]
          let destinationIdE ← withTransparency .all <| reduce destinationIdE
          let destinationId ←
            match destinationIdE with
            | .lit (.natVal value) => pure value
            | _ => throwError (Validate.rejection
                "Core could not recover the selected sibling continuation ID.")
          let some destination := siblings.find?
              (fun entry : SiblingContinuationEntry =>
                entry.id == destinationId)
            | throwError (Validate.rejection
                "Core could not recover the selected sibling continuation.")
          let destinationFlow ← recurse destination.dag preceding.output
          applyConstructorAtType ``VerifiedManifest.siblingRoute
            #[routeE, metadataE, preceding.proof, destinationFlow.proof]
            expected
        else
          applyConstructorAtType ``VerifiedManifest.resolvedRoute
            #[routeE, metadataE, preceding.proof] expected
      pure {
        output := preceding.output
        proof
      }
  | _ =>
      throwError (Validate.rejection
        "sealed execution accepts only Core-expanded DAG constructors.")

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def elaborateVerifiedManifestWithFuel :
    Array SiblingContinuationEntry →
      Nat → Expr → Expr → TermElabM ElaboratedManifest
  | _, 0, _, _ =>
      throwError (Validate.rejection
        "Core exhausted the exact expanded-DAG size while lowering sealed \
        Strategy execution.")
  | siblings, fuel + 1, dagE, inputE =>
      elaborateVerifiedManifestStep siblings
        (elaborateVerifiedManifestWithFuel siblings fuel) dagE inputE

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def elaborateVerifiedManifest
    (dagE inputE : Expr) : TermElabM ElaboratedManifest := do
  let (siblings, _) ← collectSiblingContinuationEntries dagE 0
  elaborateVerifiedManifestWithFuel siblings
    (dagE.sizeWithoutSharing + 1) dagE inputE

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def elaborateCheckedBlueprint (dagE : Expr) :
    TermElabM Expr := do
  let empty :=
    mkApp (mkConst ``List.nil [0]) (mkConst ``CapabilityKey)
  let result ← elaborateVerifiedManifest dagE empty
  mkAppM ``CheckedBlueprint.mk #[result.output, dagE, result.proof]

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
private def deriveCompiledClosure
    (runName : String) (problemE dagE prop : Expr) : TermElabM Expr := do
  let proof? ← try
    let refl := ← mkEqRefl (mkConst ``Bool.true)
    let reflType ← inferType refl
    if ← withTransparency .all <| isDefEq reflType prop then
      check refl
      pure (some refl)
    else
      pure none
  catch _ =>
    pure none
  let proof? ← match proof? with
  | some proof => pure (some proof)
  | none => try
    let instance_ ← synthInstance (← mkAppM ``Decidable #[prop])
    let decision ← withTransparency .all <| whnf
      (mkApp2 (mkConst ``Decidable.decide) prop instance_)
    if decision.isConstOf ``Bool.true then
      let proof := mkApp3 (mkConst ``of_decide_eq_true)
        prop instance_ (← mkEqRefl (mkConst ``Bool.true))
      check proof
      pure (some proof)
    else
      pure none
  catch _ =>
    pure none
  match proof? with
  | some proof => pure proof
  | none =>
      -- Render the compiler's branch analysis only as a failed-declaration
      -- diagnostic.  No partial execution value or residual API is exposed.
      Validate.emitRejectedRunSummary runName problemE dagE
      throwError (Validate.rejection
        "the sealed compiler could not derive total execution closure from the registered DAG. The preceding summary lists every closed branch and every surviving residual.")

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
elab_rules : term
  | `(reduceDag% $problemStx $dagStx) => do
    let problemE ← Term.elabTerm problemStx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let problemE ← instantiateMVars problemE
    let problemType ← whnf (← inferType problemE)
    unless problemType.isConstOf ``Core.ProblemDefinition do
      throwError (Validate.rejection
        "the first argument must be a `Core.ProblemDefinition`.")
    let dataE ← mkAppM ``Core.ProblemDefinition.data #[problemE]
    let dagE ← elaborateProgram dataE dagStx
    Validate.checkHonestTarget problemE
    let runName :=
      (toString problemStx.raw.prettyPrint).trimAscii.toString ++ " ⊢ " ++
        (toString dagStx.raw.prettyPrint).trimAscii.toString
    let sourceExpression :=
      (toString problemStx.raw.prettyPrint).trimAscii.toString
    let descriptor ← captureProblemDescriptor problemE sourceExpression runName
    let checked ← elaborateCheckedBlueprint dagE
    let compilation ← mkAppM ``compileFrom #[problemE, checked]
    mkAppM ``ReductionDeclaration.ofValidated
      #[problemE, dagE, compilation, descriptor]
  | `(ofDag% $problemStx $dagStx) => do
    let problemE ← Term.elabTerm problemStx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let problemE ← instantiateMVars problemE
    let problemType ← whnf (← inferType problemE)
    unless problemType.isConstOf ``Core.ProblemDefinition do
      throwError (Validate.rejection
        "the first argument must be a `Core.ProblemDefinition`.")
    let dataE ← mkAppM ``Core.ProblemDefinition.data #[problemE]
    let dagE ← elaborateProgram dataE dagStx
    Validate.checkHonestTarget problemE
    let checked ← elaborateCheckedBlueprint dagE
    let compilation ← mkAppM ``compileFrom #[problemE, checked]
    let closes ← mkAppM ``Compilation.closes #[compilation]
    let isSome ← mkAppM ``Option.isSome #[closes]
    let closedProp ← mkEq isSome (mkConst ``Bool.true)
    let runName :=
      (toString problemStx.raw.prettyPrint).trimAscii.toString ++ " ⊢ " ++
        (toString dagStx.raw.prettyPrint).trimAscii.toString
    let closedProof ←
      deriveCompiledClosure runName problemE dagE closedProp
    let sourceExpression :=
      (toString problemStx.raw.prettyPrint).trimAscii.toString
    let descriptor ← captureProblemDescriptor problemE sourceExpression runName
    let declaration ← mkAppM ``ProblemDeclaration.ofValidated
      #[problemE, dagE, compilation, descriptor, closedProof]
    return declaration

/-- Exact public outcome family of a sealed reduction.  The right side is the
literal terminal payload type of Core's compiled ledger; applications cannot
construct or replace that family. -/
abbrev ReductionDeclaration.Outcome
    (declaration : ReductionDeclaration)
    (input : Strategy.ProblemInput declaration.problem.problem) :=
  Sum (PLift (declaration.problem.target.Predicate input.object))
    (Strategy.HaltingProgram.OpenResult declaration.problem.problem
      declaration.program.Stage declaration.program.TerminalResidual input)

/-- Kernel term for one unconditional target-or-residual execution. -/
noncomputable def ReductionDeclaration.outcome
    (declaration : ReductionDeclaration)
    (input : Strategy.ProblemInput declaration.problem.problem) :
    declaration.Outcome input :=
  declaration.program.execute input

/-- The unconditional reduction theorem produced by the official DAG. -/
abbrev ReductionDeclaration.Statement
    (declaration : ReductionDeclaration) :=
  ∀ input : Strategy.ProblemInput declaration.problem.problem,
    declaration.Outcome input

/-- Sealed report for a target-or-residual reduction. -/
structure ReductionDeclaration.Report
    (declaration : ReductionDeclaration) where
  private mk ::
  private certified : declaration.Statement
  private trace : CompileTrace

noncomputable def ReductionDeclaration.report
    (declaration : ReductionDeclaration) : declaration.Report where
  certified := declaration.outcome
  trace := declaration.trace

namespace ReductionDeclaration

/-- Kernel-certified target-or-exact-residual statement. -/
noncomputable def Report.statement
    {declaration : ReductionDeclaration} (report : declaration.Report) :
    declaration.Statement :=
  report.certified

def Report.path {declaration : ReductionDeclaration}
    (report : declaration.Report) : List StrategyKey :=
  report.trace.path

def Report.proofTrace {declaration : ReductionDeclaration}
    (report : declaration.Report) : ProofTrace :=
  report.trace.proofTrace

def Report.traceJson {declaration : ReductionDeclaration}
    (report : declaration.Report) : Lean.Json :=
  CertificateJson.certificate declaration.problem.metadata
    declaration.problem.data declaration.descriptor report.proofTrace
    report.trace.checksBound report.trace.workBound (closed := false)

def Report.checksBound {declaration : ReductionDeclaration}
    (report : declaration.Report) : Nat :=
  report.trace.checksBound

def Report.workBound {declaration : ReductionDeclaration}
    (report : declaration.Report) : Nat :=
  report.trace.workBound

def Report.describe {declaration : ReductionDeclaration}
    (report : declaration.Report) : String :=
  s!"path={repr report.trace.path}; certified=target-or-residual; " ++
    s!"checks≤{report.trace.checksBound}; work≤{report.trace.workBound}"

end ReductionDeclaration

/-- Core-only lowering of the compiled program to the strategy output
boundary. -/
private noncomputable def ProblemDeclaration.chain
    (declaration : ProblemDeclaration) :
    Chain declaration.problem.problem declaration.problem.target :=
  Strategy.HaltingProgram.toOutputStrategy declaration.problem
    declaration.program

private noncomputable def ProblemDeclaration.compiled
    (declaration : ProblemDeclaration) : Strategy.CompiledDeclaration where
  problem := declaration.problem.problem
  target := declaration.problem.target
  strategy := declaration.chain

private noncomputable def ProblemDeclaration.run
    (declaration : ProblemDeclaration) :=
  declaration.compiled.run

/-- The sealed report of a validated declaration.  Its statement is total:
a declaration only exists when the registered problem certifies its target,
so there is no residual alternative to report. -/
structure ProblemDeclaration.Report
    (declaration : ProblemDeclaration) where
  private mk ::
  private certified : PLift declaration.problem.target.Statement
  private trace : CompileTrace

noncomputable def ProblemDeclaration.report
    (declaration : ProblemDeclaration) : declaration.Report where
  certified :=
    ⟨declaration.problem.target.target_to_statement
      (fun object baseline =>
        declaration.program.target_of_closes declaration.closed
          ⟨object, baseline, declaration.problem.initialState object⟩)⟩
  trace := declaration.trace

namespace ProblemDeclaration

/-- The kernel-checked registered theorem.  Total: every declaration the
frontend accepts certifies its statement unconditionally. -/
noncomputable def Report.statement
    {declaration : ProblemDeclaration} (report : declaration.Report) :
    PLift declaration.problem.target.Statement :=
  report.certified

/-- The compiled vertex order (pre-order; each branch records its dichotomy
key before its two continuations). -/
def Report.path {declaration : ProblemDeclaration}
    (report : declaration.Report) : List StrategyKey :=
  report.trace.path

/-- The complete metadata-rich static proof topology. -/
def Report.proofTrace {declaration : ProblemDeclaration}
    (report : declaration.Report) : ProofTrace :=
  report.trace.proofTrace

/-- Complete UI-facing certified-proof artifact: problem registration,
normalized DAG, execution result, and trust boundary. -/
def Report.traceJson {declaration : ProblemDeclaration}
    (report : declaration.Report) : Lean.Json :=
  CertificateJson.certificate declaration.problem.metadata
    declaration.problem.data declaration.descriptor report.proofTrace
    report.trace.checksBound report.trace.workBound

/-- Registered decision bound: one contract application per vertex,
sequential sum and branch max. -/
def Report.checksBound {declaration : ProblemDeclaration}
    (report : declaration.Report) : Nat :=
  report.trace.checksBound

/-- Registered work bound: one contract application per vertex, sequential
sum and branch max. -/
def Report.workBound {declaration : ProblemDeclaration}
    (report : declaration.Report) : Nat :=
  report.trace.workBound

/-- Human-readable run summary.  A diagnostic string, not a proof object. -/
def Report.describe {declaration : ProblemDeclaration}
    (report : declaration.Report) : String :=
  s!"path={repr report.trace.path}; certified=unconditional; " ++
    s!"checks≤{report.trace.checksBound}; work≤{report.trace.workBound}"

end ProblemDeclaration

/-! ## Certified artifact commands

Proof authors cannot construct or alter an execution object.  The commands
accept only a sealed `ReductionDeclaration` or `ProblemDeclaration` produced
by the corresponding frontend and render its kernel-certified report. -/

private def certifyLatexPayload (payload : String) (closed : Bool := true) :
    String :=
  payload.replace
    "\\textbf{Certification status omitted.} This is an internal structural payload, not a proof artifact."
    (if closed then
      "\\textbf{Target verified: TRUE} --- the sealed declaration contains a kernel-checked proof of the registered statement."
    else
      "\\textbf{Reduction verified: TRUE} --- the sealed declaration contains a kernel-checked target-or-residual theorem.")

private def certifiedArtifact (payload : Lean.Json) (closed : Bool := true) :
    Lean.Json :=
  .mkObj [
    ("$schema", .str "https://json-schema.org/draft/2020-12/schema"),
    ("schema_id", .str
      "https://structural-exhaustion.local/schemas/hypostructure-proof-run.schema.json"),
    ("artifact_type", .str "hypostructure_proof_run"),
    ("schema_version", .str "2.3.0"),
    ("framework", .mkObj [
      ("name", .str "Hypostructure"),
      ("version", .str "0.1.0"),
      ("proof_authority", .str "Lean kernel")
    ]),
    ("run", .mkObj [
      ("name", payload.getObjValD "run_name"),
      ("kind", .str (if closed then
        "certified_declaration" else "certified_reduction")),
      ("certified", .bool true)
    ]),
    ("problem", payload.getObjValD "problem"),
    ("strategy_registrations", payload.getObjValD "strategy_registrations"),
    ("dag", payload.getObjValD "dag"),
    ("execution", .mkObj [
      ("result", .str (if closed then "certified" else "reduced")),
      ("statement_ref", .str (if closed then
        "problem.formal.statement" else "execution.target_or_residual")),
      ("checks_bound", payload.getObjValD "checks_bound"),
      ("work_bound", payload.getObjValD "work_bound"),
      ("residual_disposition", .str (if closed then "none" else "retained"))
    ]),
    ("trust", .mkObj [
      ("kernel_checked", .bool true),
      ("proof_term_exported", .bool false),
      ("verification_note", .str
        "JSON is an auditable semantic projection; Lean remains the proof authority.")
    ])
  ]

/-- Human-readable executive summary of one certified declaration. -/
scoped syntax (name := hypostructureSummary) "#hypostructure_summary " term : command

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta in
elab_rules : command
  | `(#hypostructure_summary $stx) =>
    Command.runTermElabM fun _ => do
      let runE ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let runE ← instantiateMVars runE
      let runType ← whnf (← inferType runE)
      let description ←
        if runType.isConstOf ``ProblemDeclaration then
          let report ← mkAppM ``ProblemDeclaration.report #[runE]
          mkAppM ``ProblemDeclaration.Report.describe #[report]
        else if runType.isConstOf ``ReductionDeclaration then
          let report ← mkAppM ``ReductionDeclaration.report #[runE]
          mkAppM ``ReductionDeclaration.Report.describe #[report]
        else
          throwError "#hypostructure_summary expects a sealed declaration produced by `reduceDag%` or `ofDag%`."
      logInfo (← Validate.evalStrLiteral description)

/-- Render one run's sealed summary as a standalone LaTeX document — the
compiled strategy tree as a `forest`/TikZ diagram and its certified terminal
evidence — and write it to the given path.  The command also
writes the complete machine-readable companion beside it, replacing a
trailing `.tex` by `.json` (or appending `.json` otherwise).  Both files are
derived from the same Core-owned run summary.  Usage:
`#hypostructure_pdf "path/to/file.tex" run`. -/
scoped syntax (name := hypostructurePdf) "#hypostructure_pdf " str ppSpace term : command

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta in
elab_rules : command
  | `(#hypostructure_pdf $pathStx $stx) => do
    let path := pathStx.getString
    let rendered? ← Command.runTermElabM fun _ => do
      let runE ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let runE ← instantiateMVars runE
      let runType ← whnf (← inferType runE)
      if runType.isConstOf ``ProblemDeclaration then
        let dagE ← mkAppM ``ProblemDeclaration.dag #[runE]
        let problemE ← mkAppM ``ProblemDeclaration.problem #[runE]
        let descriptorE ← mkAppM ``ProblemDeclaration.descriptor #[runE]
        let runName := toString stx.raw.prettyPrint |>.trimAscii |>.toString
        let tex? ←
          Validate.buildRunSummaryLatexPayload runName problemE dagE true
        let payload? ←
          Validate.buildRunSummaryPayload runName problemE dagE
            (some descriptorE) true
        return tex?.bind fun tex => payload?.map fun payload =>
          (certifyLatexPayload tex true,
            (certifiedArtifact payload true).pretty 100 ++ "\n")
      else
        throwError "#hypostructure_pdf expects a sealed declaration produced by `reduceDag%` or `ofDag%`."
    match rendered? with
    | some (tex, json) =>
        let jsonPath :=
          if path.endsWith ".tex" then
            (path.dropEnd 4).toString ++ ".json"
          else path ++ ".json"
        IO.FS.writeFile path tex
        IO.FS.writeFile jsonPath json
        logInfo s!"hypostructure_pdf: wrote LaTeX source to {path}"
        logInfo s!"hypostructure_pdf: wrote JSON certificate to {jsonPath}"
    | none =>
        throwError "#hypostructure_pdf could not compute the run's summary data (the blueprint or its registered data is not a closed literal)."

/-- Write the structured v2 proof-run artifact for one run as JSON.  The DAG,
problem, registrations, strategy metadata, resolved autoroutes, and terminal
residual disposition are emitted as machine-readable objects; display
renderings are explicitly non-authoritative.  Lean remains the proof
authority.  Usage:
`#hypostructure_json "path/to/file.json" run`. -/
scoped syntax (name := hypostructureJson) "#hypostructure_json " str ppSpace term : command

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta in
elab_rules : command
  | `(#hypostructure_json $pathStx (reduceDag% $problemStx $dagStx)) => do
    let path := pathStx.getString
    let json? ← Command.runTermElabM fun _ => do
      let sealed ← Term.elabTerm
        (← `(reduceDag% $problemStx $dagStx)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let sealedType ← whnf (← inferType (← instantiateMVars sealed))
      unless sealedType.isConstOf ``ReductionDeclaration do
        throwError "#hypostructure_json expected a sealed reduction."
      let problemE ← Term.elabTerm problemStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let problemE ← instantiateMVars problemE
      let dataE ← mkAppM ``Core.ProblemDefinition.data #[problemE]
      let dagE ← elaborateProgram dataE dagStx
      let runName := s!"{problemStx.raw.prettyPrint} ⊢ {dagStx.raw.prettyPrint}"
      let payload? ← withTransparency .all <|
        Validate.buildRunSummaryPayload runName problemE dagE none false
      return payload?.map fun payload =>
        (certifiedArtifact payload false).pretty 100 ++ "\n"
    match json? with
    | some json =>
        IO.FS.writeFile path json
        logInfo s!"hypostructure_json: wrote JSON certificate to {path}"
    | none =>
        throwError "#hypostructure_json could not compute the sealed reduction certificate."
  | `(#hypostructure_json $pathStx $stx) => do
    let path := pathStx.getString
    let json? ← Command.runTermElabM fun _ => do
      let runE ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let runE ← instantiateMVars runE
      let runType ← whnf (← inferType runE)
      if runType.isConstOf ``ProblemDeclaration then
        let dagE ← mkAppM ``ProblemDeclaration.dag #[runE]
        let problemE ← mkAppM ``ProblemDeclaration.problem #[runE]
        let descriptorE ← mkAppM ``ProblemDeclaration.descriptor #[runE]
        let runName := toString stx.raw.prettyPrint |>.trimAscii |>.toString
        let payload? ← Validate.buildRunSummaryPayload runName problemE dagE
          (some descriptorE) true
        return payload?.map fun payload =>
          (certifiedArtifact payload true).pretty 100 ++ "\n"
      else
        throwError "#hypostructure_json expects a sealed declaration produced by `reduceDag%` or `ofDag%`."
    match json? with
    | some json =>
        IO.FS.writeFile path json
        logInfo s!"hypostructure_json: wrote JSON certificate to {path}"
    | none =>
        throwError "#hypostructure_json could not compute the run's certificate."

end Hypostructure.Core.Strategy.Dag
