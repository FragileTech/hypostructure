import Hypostructure.Core.Strategy.Data
import Lean

/-!
# Strategy frontend validation

Core-internal elaboration checks behind the sealed `ofDag%` frontend in
`Core/Strategy/Dag.lean`.  Every public declaration is validated here before
the private compiler is ever invoked:

- **banalization lint** — targets hardcoded to `True`/`False`, predicates
  that ignore the ambient object, and uninhabitable (`False`) baselines are
  rejected outright: a certified run must prove real registered content;
- **blueprint compliance** — every strategy key must name a registered
  family; out-of-range vertices are rejected with a message naming each
  offending key, its index, and the registered count;
- **certification** — the private compiler must derive closure of every
  terminal produced by the registered Strategy DAG; the application cannot
  supply or replace closure evidence.

Semantic triviality (e.g. registering `1 = 1`) is undecidable and out of
scope: the kernel already guarantees that no false statement is certified,
and the report exposes the registered statement verbatim for human audit.

These helpers produce proofs or throw curated errors; they cannot
manufacture stages, contracts, outcomes, or reports, so exposing them grants
no execution capability.
-/

namespace Hypostructure.Core.Strategy.Validate

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

/-- Uniform first line of every frontend rejection. -/
def rejection (reason : String) : String :=
  s!"ofDag% rejected this declaration: {reason}"

/-! ## Small evaluation helpers -/

/-- Evaluate a closed `Nat` expression to a literal, unfolding `OfNat`
spellings. -/
partial def evalNatLiteral (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => return some n
  | _ =>
      if e.isAppOfArity ``OfNat.ofNat 3 then
        evalNatLiteral (e.getAppArgs[1]!)
      else if e.isAppOfArity ``Nat.succ 1 then
        match ← evalNatLiteral (e.getAppArgs[0]!) with
        | some n => return some (n + 1)
        | none => return none
      else
        return none

/-- Evaluate the value of a closed `Fin` expression without reading or
reconstructing its bound proof. -/
private def evalFinLiteral (e : Expr) : MetaM (Option Nat) := do
  evalNatLiteral (← mkAppM ``Fin.val #[e])

/-- Evaluate a closed `String` literal expression to its actual value (not a
`toString`-of-syntax approximation), so embedded quotes/backslashes never
leak through as stray characters. -/
def evalStrLiteral (e : Expr) : MetaM String := do
  let e ← whnf e
  match e with
  | .lit (.strVal s) => return s
  | _ => return (toString e)

private partial def evalStringList (value : Expr) : MetaM (List String) := do
  let value ← whnf value
  match value.getAppFn.constName? with
  | some ``List.nil => return []
  | some ``List.cons =>
      let args := value.getAppArgs
      return (← evalStrLiteral args[1]!) :: (← evalStringList args[2]!)
  | _ => return []

private partial def evalNatList (value : Expr) : MetaM (Option (List Nat)) := do
  let value ← whnf value
  match value.getAppFn.constName? with
  | some ``List.nil => return some []
  | some ``List.cons => do
      let args := value.getAppArgs
      let some head ← evalNatLiteral args[1]! | return none
      let some tail ← evalNatList args[2]! | return none
      return some (head :: tail)
  | _ => return none

private def strategyKeyOfRef (strategy : Expr) : MetaM Expr := do
  whnf (← mkAppM
    `Hypostructure.Core.Strategy.Dag.StrategyRef.keyView #[strategy])

private def binaryStrategyKeyOfRef (strategy : Expr) : MetaM Expr := do
  whnf (← mkAppM
    `Hypostructure.Core.Strategy.Dag.BinaryStrategyRef.keyView #[strategy])

private def binaryKeyParts (strategy : Expr) :
    MetaM (Option (Name × Nat)) := do
  let key ← binaryStrategyKeyOfRef strategy
  let some ctor := key.getAppFn.constName? | return none
  if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.atomContextObstructionDichotomy then
    return some (ctor, 0)
  if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateNetChargeContinuation then
    return some (ctor, 0)
  let some index ← evalNatLiteral key.getAppArgs[0]! | return none
  return some (ctor, index)

private def binaryDefaultNames (ctor : Name) : String × String :=
  if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.scaleThresholdDichotomy then
    ("above", "at_or_below")
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.atomContextObstructionDichotomy then
    ("atom", "context")
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateNetChargeContinuation then
    ("type_A", "type_B")
  else
    ("left", "right")

/-- Constructor fields are always the trailing arguments; universe and
problem parameters precede them.  Renderers request the framework-declared
field count instead of assuming how many problem parameters Lean retained. -/
private def blueprintCtorArgs (dag : Expr) (fieldCount : Nat) : Array Expr :=
  let args := dag.getAppArgs
  args.extract (args.size - fieldCount) args.size

/-- Read-only projection of a route record created by Core while expanding
the typed DAG.  This validator never constructs a route and never accepts
an application-authored destination, relation, priority, bridge, or work
claim. -/
private structure ResolvedRouteView where
  sourceId : Nat
  destinationId : Nat
  sourceDepth : Nat
  destinationDepth : Nat
  scope : String
  selectedBy : String
  relation : String
  compatibleCandidates : List Nat
  compatibleCandidateDepths : List Nat
  work : Nat
  destinationWork : Nat
  name : String
  note : String
  tags : List String

private def evalResolvedRoute (route metadata : Expr) :
    MetaM (Option ResolvedRouteView) := do
  let some sourceId ← evalNatLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.sourceId #[route])
    | return none
  let some destinationId ← evalNatLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.destinationId #[route])
    | return none
  let some sourceDepth ← evalNatLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.sourceDepth #[route])
    | return none
  let some destinationDepth ← evalNatLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.destinationDepth #[route])
    | return none
  let scope ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.scopeName #[route])
  let selectedBy ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.selectedBy #[route])
  let relation ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.relation #[route])
  let some compatibleCandidates ← evalNatList (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.compatibleCandidates #[route])
    | return none
  let some compatibleCandidateDepths ← evalNatList (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.compatibleCandidateDepths
      #[route])
    | return none
  let some work ← evalNatLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.work #[route])
    | return none
  let some destinationWork ← evalNatLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.ResolvedRoute.destinationWork #[route])
    | return none
  let name ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.RouteMetadata.name #[metadata])
  let note ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.RouteMetadata.note #[metadata])
  let tags ← evalStringList (← mkAppM
    `Hypostructure.Core.Strategy.Dag.RouteMetadata.tags #[metadata])
  return some {
    sourceId
    destinationId
    sourceDepth
    destinationDepth
    scope
    selectedBy
    relation
    compatibleCandidates
    compatibleCandidateDepths
    work
    destinationWork
    name
    note
    tags
  }

/-- Renderer-facing evaluation of the public display-only metadata. -/
structure RenderMetadata where
  name : Option String := none
  note : Option String := none
  leftName : Option String := none
  leftNote : Option String := none
  rightName : Option String := none
  rightNote : Option String := none

def prefer {α : Type} (primary fallback : Option α) : Option α :=
  primary <|> fallback

def RenderMetadata.merge (primary fallback : RenderMetadata) : RenderMetadata where
  name := prefer primary.name fallback.name
  note := prefer primary.note fallback.note
  leftName := prefer primary.leftName fallback.leftName
  leftNote := prefer primary.leftNote fallback.leftNote
  rightName := prefer primary.rightName fallback.rightName
  rightNote := prefer primary.rightNote fallback.rightNote

def nonemptyString (value : String) : Option String :=
  if value.isEmpty then none else some value

def evalDocumentedMetadata (metadata : Expr) : MetaM RenderMetadata := do
  let display ← mkAppM
    `Hypostructure.Core.Strategy.Dag.VertexMetadata.display #[metadata]
  let left ← mkAppM
    `Hypostructure.Core.Strategy.Dag.VertexMetadata.left #[metadata]
  let right ← mkAppM
    `Hypostructure.Core.Strategy.Dag.VertexMetadata.right #[metadata]
  let name ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.DisplayMetadata.name #[display])
  let note ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.DisplayMetadata.note #[display])
  let leftName ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.OutputMetadata.name #[left])
  let leftNote ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.OutputMetadata.note #[left])
  let rightName ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.OutputMetadata.name #[right])
  let rightNote ← evalStrLiteral (← mkAppM
    `Hypostructure.Core.Strategy.Dag.OutputMetadata.note #[right])
  return {
    name := nonemptyString name
    note := nonemptyString note
    leftName := nonemptyString leftName
    leftNote := nonemptyString leftNote
    rightName := nonemptyString rightName
    rightNote := nonemptyString rightNote
  }

/-- Peel all consecutive metadata wrappers immediately preceding a vertex.
Explicit first-class metadata wins; compatibility decorators fill only fields
that the explicit fluent arguments leave empty. -/
partial def peelMetadata (e : Expr) : MetaM (Expr × RenderMetadata) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented => do
      let args := blueprintCtorArgs e 2
      let metadata ← evalDocumentedMetadata args[1]!
      let (rest, fallback) ← peelMetadata args[0]!
      return (rest, metadata.merge fallback)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled => do
      let args := blueprintCtorArgs e 2
      let name ← evalStrLiteral args[1]!
      let (rest, fallback) ← peelMetadata args[0]!
      return (rest, ({ name := nonemptyString name } : RenderMetadata).merge fallback)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate => do
      let args := blueprintCtorArgs e 2
      let note ← evalStrLiteral args[1]!
      let (rest, fallback) ← peelMetadata args[0]!
      return (rest, ({ note := nonemptyString note } : RenderMetadata).merge fallback)
  | _ => return (e, {})

/-- Count the rendered vertices in a `Blueprint`'s straight-line run, from
its own `root` up to (not including) the next nested dichotomy, or up to
its end (a closure/residual leaf) if there is none — i.e. exactly the run
the main diagram would stack as one vertical column for this side of a
split.  `annotate`/`labelled` markers contribute no separate node (a note
renders nowhere in the main diagram; a label merges into the vertex it
names), so they don't add to the count.  The second component is `true`
when the run ends at a genuine closure/residual leaf (`root`), `false` when
it stops early because it hit another nested dichotomy — a branch only
counts as "short" for the main diagram's horizontal-layout treatment when it
actually finishes (reaches its own red or green leaf) within the short
count, not when it merely forks again. -/
partial def branchRun (e : Expr) : MetaM (Nat × Bool) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root => return (0, true)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let (n, endsAtLeaf) ← branchRun (blueprintCtorArgs e 2)[0]!
      return (n + 1, endsAtLeaf)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate =>
      branchRun (blueprintCtorArgs e 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled =>
      branchRun (blueprintCtorArgs e 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      branchRun (blueprintCtorArgs e 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.route =>
      branchRun (blueprintCtorArgs e 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute =>
      branchRun (blueprintCtorArgs e 3)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      -- The next dichotomy: count only the steps leading up to it, and
      -- report that this run did NOT end at a leaf.
      let (n, _) ← branchRun (blueprintCtorArgs e 4)[0]!
      return (n, false)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let (n, _) ← branchRun (blueprintCtorArgs e 5)[0]!
      return (n, false)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let (n, _) ← branchRun (blueprintCtorArgs e 3)[0]!
      return (n + 1, false)
  | _ => return (0, true)

/-- Evaluate the length of a literal list without normalizing its
elements. -/
partial def evalListLength (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some ``List.nil => return some 0
  | some ``List.cons =>
      match ← evalListLength (e.getAppArgs[2]!) with
      | some n => return some (n + 1)
      | none => return none
  | _ => return none

/-! ## Banalization lint -/

/-- Reject problem registrations whose target or baseline is hardcoded:
`Statement`/`Predicate` reducing to `True` or `False`, predicates ignoring
the ambient object, and baselines reducing to `False`. -/
def checkHonestTarget (problemDefn : Expr) : TermElabM Unit := do
  let problemE ← mkAppM ``Hypostructure.Core.ProblemDefinition.problem #[problemDefn]
  let targetE ← mkAppM ``Hypostructure.Core.ProblemDefinition.target #[problemDefn]
  let statementE ← whnf (← mkAppM ``Hypostructure.Core.Target.Statement #[targetE])
  if statementE.isConstOf ``True || statementE.isConstOf ``False then
    throwError (rejection s!"the registered target is banal: `Statement` reduces to `{statementE.constName!.toString}`.\n\
      The strict frontend refuses hardcoded targets — a certified run must prove real registered content, not a constant.\n\
      Register the actual mathematical statement this problem is meant to certify.")
  let ambientE ← mkAppM ``Hypostructure.Core.Problem.Ambient #[problemE]
  withLocalDeclD `object ambientE fun object => do
    let predicateE ← whnf (mkApp
      (← mkAppM ``Hypostructure.Core.Target.Predicate #[targetE]) object)
    if predicateE.isConstOf ``True || predicateE.isConstOf ``False then
      throwError (rejection s!"the registered target is banal: `Predicate` reduces to `{predicateE.constName!.toString}` for every ambient object.\n\
        The strict frontend refuses hardcoded targets — a certified run must prove real registered content, not a constant.\n\
        Register the actual per-object target the strategies are meant to establish.")
    unless predicateE.containsFVar object.fvarId! do
      throwError (rejection "the registered target is banal: `Predicate` does not depend on the ambient object.\n\
        Every certified run proves the target for each problem input; an object-independent predicate would banalize the theorem.\n\
        Index the target predicate by the ambient object it constrains.")
    let baselineE ← whnf (mkApp
      (← mkAppM ``Hypostructure.Core.Problem.Baseline #[problemE]) object)
    if baselineE.isConstOf ``False then
      throwError (rejection "the registered problem is vacuous: `Baseline` reduces to `False`, so no problem input exists.\n\
        Certification over an empty input space is meaningless; the strict frontend refuses it.\n\
        Register a satisfiable baseline (use `fun _ => True` when there is no precondition).")

/-! ## Blueprint compliance -/

/-- One out-of-range vertex: the key's display name, its requested index,
the `StrategyData` field it selects from, and the registered family count. -/
structure KeyViolation where
  keyName : String
  index : Nat
  fieldName : String
  registered : Nat

/-- Indexed strategy keys and the registered-data field each one selects
from.  `targetOrAvoid` carries no index and always resolves. -/
def indexedKeys : List (Name × String × Name) :=
  [ (`Hypostructure.Core.Strategy.Dag.StrategyKey.orderedWitnessScan,
      "orderedWitnessScan", ``Hypostructure.Core.StrategyData.scans),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.responseClassifier,
      "responseClassifier", ``Hypostructure.Core.StrategyData.responses),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.capacityLedger,
      "capacityLedger", ``Hypostructure.Core.StrategyData.capacities),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.orderedSurplusActivation,
      "orderedSurplusActivation",
      ``Hypostructure.Core.StrategyData.orderedSurplusActivations),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.baselineDemandAccounting,
      "baselineDemandAccounting",
      ``Hypostructure.Core.StrategyData.baselineDemandAccountings),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.canonicalPairResponseAccounting,
      "canonicalPairResponseAccounting",
      ``Hypostructure.Core.StrategyData.canonicalPairResponseAccountings),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.canonicalCapacityTokenAccounting,
      "canonicalCapacityTokenAccounting",
      ``Hypostructure.Core.StrategyData.canonicalCapacityTokenAccountings),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.coupledHomogeneousFibrePressure,
      "coupledHomogeneousFibrePressure",
      ``Hypostructure.Core.StrategyData.coupledHomogeneousFibrePressures),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteBottleneckClassification,
      "finiteBottleneckClassification",
      ``Hypostructure.Core.StrategyData.finiteBottleneckClassifications),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.homogeneousBottleneck,
      "homogeneousBottleneck",
      ``Hypostructure.Core.StrategyData.homogeneousBottlenecks),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.supportComplementNormalization,
      "supportComplementNormalization",
      ``Hypostructure.Core.StrategyData.supportComplementNormalizations),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.boundaryDemandAccounting,
      "boundaryDemandAccounting",
      ``Hypostructure.Core.StrategyData.boundaryDemandAccountings),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.localSupplyLowerBound,
      "localSupplyLowerBound",
      ``Hypostructure.Core.StrategyData.localSupplyLowerBounds),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.targetRelativeRankDichotomy,
      "targetRelativeRankDichotomy",
      ``Hypostructure.Core.StrategyData.targetRelativeRankDichotomies),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.compressionLinkedTargetRelativeRankDichotomy,
      "compressionLinkedTargetRelativeRankDichotomy",
      ``Hypostructure.Core.StrategyData.compressionLinkedTargetRelativeRankDichotomies),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateCapacity,
      "finiteStateCapacity",
      ``Hypostructure.Core.StrategyData.finiteStateCapacities),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteScheduleCapacity,
      "finiteScheduleCapacity",
      ``Hypostructure.Core.StrategyData.finiteScheduleCapacities),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.route8CarrierClosure,
      "route8CarrierClosure",
      ``Hypostructure.Core.StrategyData.route8CarrierClosures),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.supportLocalization,
      "supportLocalization", ``Hypostructure.Core.StrategyData.localizations),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.rankBudget,
      "rankBudget", ``Hypostructure.Core.StrategyData.rankBudgets),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.closedCode,
      "closedCode", ``Hypostructure.Core.StrategyData.closedCodes),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy,
      "dichotomy", ``Hypostructure.Core.StrategyData.dichotomies),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.obstructionPackingClosure,
      "obstructionPackingClosure",
      ``Hypostructure.Core.StrategyData.obstructionPackingClosures),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.exactFiniteLocalAlgebra,
      "exactFiniteLocalAlgebra",
      ``Hypostructure.Core.StrategyData.exactFiniteLocalAlgebras),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteBarrierEnumeration,
      "finiteBarrierEnumeration",
      ``Hypostructure.Core.StrategyData.finiteBarrierEnumerations),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteDensityBudget,
      "finiteDensityBudget",
      ``Hypostructure.Core.StrategyData.finiteDensityBudgets),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.scaleThresholdDichotomy,
      "scaleThresholdDichotomy",
      ``Hypostructure.Core.StrategyData.scaleThresholdDichotomies),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.counterexampleLocalization,
      "counterexampleLocalization",
      ``Hypostructure.Core.StrategyData.counterexampleLocalizations),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.minimalCounterexampleSelection,
      "minimalCounterexampleSelection",
      ``Hypostructure.Core.StrategyData.counterexampleReductions),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.targetAlgebraReduction,
      "targetAlgebraReduction",
      ``Hypostructure.Core.StrategyData.counterexampleReductions),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.minimalSubobjectExclusion,
      "minimalSubobjectExclusion",
      ``Hypostructure.Core.StrategyData.counterexampleReductions),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.criticalModificationStructure,
      "criticalModificationStructure",
      ``Hypostructure.Core.StrategyData.counterexampleReductions),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.interfaceReplacementClosure,
      "interfaceReplacementClosure",
      ``Hypostructure.Core.StrategyData.counterexampleReductions) ]

/-- Check one indexed key occurrence against its registered family list. -/
def keyViolation (data : Expr) (ctor : Name) (indexE : Expr) :
    MetaM (Option KeyViolation) := do
  let some (_, keyName, fieldName) :=
      indexedKeys.find? (fun entry => entry.1 == ctor) | return none
  let some index ← evalNatLiteral indexE | return none
  let some registered ← evalListLength (← mkAppM fieldName #[data])
    | return none
  if index < registered then
    return none
  return some
    { keyName := keyName, index := index
      fieldName := (fieldName.componentsRev.headD .anonymous).toString
      registered := registered }

/-- Walk a literal `Blueprint`, collecting every vertex whose key index is
out of range for the registered data.  Returns `none` when the blueprint or
its indices are not closed literals. -/
partial def collectViolations (data dag : Expr) :
    MetaM (Option (List KeyViolation)) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root => return some []
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let some rest ← collectViolations data args[0]! | return none
      let key ← strategyKeyOfRef args[1]!
      match key.getAppFn.constName? with
      | some `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid =>
          return some rest
      | some ctor =>
          match ← keyViolation data ctor (key.getAppArgs[0]!) with
          | some violation => return some (rest ++ [violation])
          | none =>
              if indexedKeys.any (fun entry => entry.1 == ctor) then
                return some rest
              else
                return none
      | none => return none
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let some rest ← collectViolations data args[0]! | return none
      let some (ctor, index) ← binaryKeyParts args[1]! | return none
      let branchViolation ← keyViolation data ctor (mkNatLit index)
      let some left ← collectViolations data args[2]! | return none
      let some right ← collectViolations data args[3]! | return none
      return some (rest ++ branchViolation.toList ++ left ++ right)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let some rest ← collectViolations data args[0]! | return none
      let some index ← evalFinLiteral args[1]! | return none
      let violation ← keyViolation data
        `Hypostructure.Core.Strategy.Dag.StrategyKey.homogeneousBottleneck
        (mkNatLit index)
      let some exceptional ← collectViolations data args[2]! | return none
      let some structured ← collectViolations data args[3]! | return none
      let some bounded ← collectViolations data args[4]! | return none
      return some
        (rest ++ violation.toList ++ exceptional ++ structured ++ bounded)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      let some rest ← collectViolations data args[0]! | return none
      let some index ← evalFinLiteral args[1]! | return none
      let violation ← keyViolation data
        `Hypostructure.Core.Strategy.Dag.StrategyKey.minimalCounterexampleSelection
        (mkNatLit index)
      -- `args[2]` is `CounterexampleContinuationMetadata`, not a blueprint: the
      -- four spine vertices it names carry no continuation of their own, which
      -- is why `Blueprint.pathOf` emits their keys without recursing.  Treating
      -- it as a blueprint made this function return `none` for *every* DAG that
      -- opens with `minimalCounterexampleSelection`, which surfaced as the
      -- spurious "not a closed literal" rejection.
      return some (rest ++ violation.toList)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate => do
      collectViolations data (blueprintCtorArgs dag 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled => do
      collectViolations data (blueprintCtorArgs dag 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented => do
      collectViolations data (blueprintCtorArgs dag 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.route =>
      collectViolations data (blueprintCtorArgs dag 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute =>
      collectViolations data (blueprintCtorArgs dag 3)[0]!
  | _ => return none

/-- Prove blueprint compliance by evaluating its `Decidable` instance, or
throw a curated error naming every out-of-range vertex. -/
def checkCompliance (data dag compliantProp : Expr) : TermElabM Expr := do
  let complianceProof? ← do
    try
      let instance_ ← synthInstance (← mkAppM ``Decidable #[compliantProp])
      let decision ← withTransparency .all <| whnf
        (mkApp2 (mkConst ``Decidable.decide) compliantProp instance_)
      if decision.isConstOf ``Bool.true then
        let proof := mkApp3 (mkConst ``of_decide_eq_true)
          compliantProp instance_ (← mkEqRefl (mkConst ``Bool.true))
        check proof
        pure (some proof)
      else
        pure none
    catch _ =>
      pure none
  match complianceProof? with
  | some proof => return proof
  | none =>
    match ← collectViolations data dag with
    | some violations =>
        if violations.isEmpty then
          throwError "internal error: closed executable Strategy constructors did not elaborate to their intrinsic compliance proof"
        let lines := violations.map fun violation =>
          s!"  • {violation.keyName} {violation.index} — only {violation.registered} registered families (StrategyData field `{violation.fieldName}`)"
        throwError (rejection ("the blueprint references strategies the problem does not register:\n" ++
          String.intercalate "\n" lines ++ "\n\
          Only official strategy keys backed by registered data may appear in a DAG.\n\
          Remove the offending vertices or register the corresponding families."))
    | none =>
        throwError (rejection "the blueprint or its registered data is not a closed literal, so compliance cannot be decided at elaboration time.\n\
          Declare the blueprint and problem definition as concrete top-level definitions.")

/-! ## Executive summary rendering

Residuals live only at terminal leaves: the last vertex of the spine and,
inside a terminal dichotomy, the last vertex of each branch continuation.
Intermediate vertices retain their payloads in the accumulated ledger but
contribute no pending residual of their own.  A closed run skips every
vertex after root closure; an open run's terminal leaves carry the residual
union.

Every accumulated constraint is carried as a pair: the LaTeX display text,
and — where the constraint is a single faithfully-representable
proposition (target avoidances, dichotomy branch witnesses and their
negation once a side is registered-closed, rank/budget sides) — the actual
`Expr` of that proposition, built against one shared generic input so a
real contradiction search is possible.  Constraints whose content is not a
single clean proposition (schedule/table facts) carry `none` and are
display-only; they can never falsely trigger a contradiction. -/

abbrev Constraint := String × Option Expr

/-- Display name and registered-family reference for one key. -/
def keyInfo (ctor : Name) (index? : Option Nat) :
    Option (String × Option String) :=
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid then
    some ("targetOrAvoid", none)
  else
    match indexedKeys.find? (fun entry => entry.1 == ctor), index? with
    | some (_, keyName, fieldName), some index =>
        some (s!"{keyName} #{index}",
          some s!"{(fieldName.componentsRev.headD .anonymous).toString}[{index}]")
    | _, _ => none

/-- The n-th element of a literal list expression. -/
partial def listNth (xs : Expr) (n : Nat) : MetaM (Option Expr) := do
  let xs ← whnf xs
  match xs.getAppFn.constName? with
  | some ``List.cons =>
      let args := xs.getAppArgs
      match n with
      | 0 => return some args[1]!
      | n + 1 => listNth args[2]! n
  | _ => return none

private def registeredDichotomy? (data : Expr) (ctor : Name) (index : Nat) :
    MetaM (Option Expr) := do
  if ctor != `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
    return none
  listNth (← mkAppM
    `Hypostructure.Core.StrategyData.dichotomies #[data]) index

/-- Whether an `Option`-valued expression reduces to `some`. -/
def optionIsSome (e : Expr) : MetaM Bool := do
  let e ← whnf e
  return e.getAppFn.constName? == some ``Option.some

/-- Whether the registered homogeneous-bottleneck family at `index` carries the
exceptional-vacuity fact.  When it does, the exceptional output is not a live
branch endpoint: Core discharges it, and the reports record a closed terminal
exactly as they already do for a registered dichotomy closure. -/
def homogeneousExceptionalClosed (data : Expr) (index : Nat) :
    MetaM Bool := do
  let some registered ← listNth (← mkAppM
    ``Hypostructure.Core.StrategyData.homogeneousBottlenecks #[data]) index
    | return false
  let registration ←
    mkAppM ``Hypostructure.Core.HomogeneousBottleneckEntry.snd #[registered]
  optionIsSome (← mkAppM
    ``Hypostructure.Core.Strategy.HomogeneousBottleneck.Registration.exceptionalImpossible
    #[registration])

/-- Whether the registered compression-linked target-relative rank family at
`index` carries the rank-drop closure.  When it does, the rank-drop output is
not a live branch endpoint: the compiler reads that registered closure through
`BaseRegistration.rankDropClosure` and installs it as this family's direct
left closure, which is the very mechanism `DichotomyData.closeLeft` supplies
for a registered dichotomy. -/
private def compressionLinkedRankDropClosed (data : Expr) (index : Nat) :
    MetaM Bool := do
  let some registered ← listNth (← mkAppM
    ``Hypostructure.Core.StrategyData.compressionLinkedTargetRelativeRankDichotomies
    #[data]) index
    | return false
  let payload ← mkAppM
    ``Hypostructure.Core.CompressionLinkedTargetRankEntry.snd #[registered]
  let base ← mkAppM
    ``Hypostructure.Core.CompressionLinkedTargetRankPayload.base #[payload]
  optionIsSome (← mkAppM
    ``Hypostructure.Core.Strategy.TargetRelativeRankDichotomy.BaseRegistration.rankDropClosure
    #[base])

/-- Whether the registered finite-state-capacity family at `index` carries the
non-capacity closure.  When it does, the non-capacity output is not a live
branch endpoint: the compiler reads that registered closure through
`Profile.nonCapacityClosureOfRegistration`, whose whole content is the
registration field read here, and installs it as this family's direct left
closure exactly as `DichotomyData.closeLeft` supplies one for a registered
dichotomy. -/
private def finiteStateNonCapacityClosed (data : Expr) (index : Nat) :
    MetaM Bool := do
  let some registered ← listNth (← mkAppM
    ``Hypostructure.Core.StrategyData.finiteStateCapacities #[data]) index
    | return false
  let registration ← mkAppM
    ``Hypostructure.Core.FiniteStateCapacityEntry.snd #[registered]
  optionIsSome (← mkAppM
    ``Hypostructure.Core.Strategy.FiniteStateCapacity.Registration.nonCapacityImpossible
    #[registration])

/-- The route-8 carrier closure's **closure** arm carries both of Figure 9's
terminal ellipses -- node `[122]`, the large-budget carrier obstruction, and
node `[124]`, the terminal two-carrier obstruction -- so it is a closed branch
endpoint exactly when the registration refutes both.  Those two refutations are
the fields read here, and they are the same two the compiler feeds to
`Profile.closureResidual_impossible` when it installs this family's direct
right closure. -/
private def route8ClosureClosed (data : Expr) (index : Nat) :
    MetaM Bool := do
  let some registered ← listNth (← mkAppM
    ``Hypostructure.Core.StrategyData.route8CarrierClosures #[data]) index
    | return false
  let registration ← mkAppM
    ``Hypostructure.Core.Route8CarrierClosureEntry.snd #[registered]
  let tier ← optionIsSome (← mkAppM
    ``Hypostructure.Core.Strategy.Route8CarrierClosure.Registration.tierImpossible
    #[registration])
  let demand ← optionIsSome (← mkAppM
    ``Hypostructure.Core.Strategy.Route8CarrierClosure.Registration.capacityImpossible
    #[registration])
  return tier && demand

/-- The registered left/right branch closures of one binary strategy family,
read from the same registration field the compiler reads.  A registered
dichotomy publishes them as `closeLeft`/`closeRight`; the compression-linked
target-relative rank family publishes its rank-drop closure and the
finite-state-capacity family its non-capacity closure, each of which the
compiler installs as that family's left direct closure; the route-8 carrier
closure publishes both terminal refutations, which the compiler installs as its
right direct closure.  Every other binary family leaves both outputs live. -/
private def binaryRegisteredClosures (data : Expr) (ctor : Name) (index : Nat) :
    MetaM (Bool × Bool) := do
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
    let some split ← registeredDichotomy? data ctor index | return (false, false)
    return (← optionIsSome (← mkAppM
        `Hypostructure.Core.DichotomyData.closeLeft #[split]),
      ← optionIsSome (← mkAppM
        `Hypostructure.Core.DichotomyData.closeRight #[split]))
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.compressionLinkedTargetRelativeRankDichotomy then
    return (← compressionLinkedRankDropClosed data index, false)
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateCapacity then
    return (← finiteStateNonCapacityClosed data index, false)
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.route8CarrierClosure then
    return (false, ← route8ClosureClosed data index)
  else
    return (false, false)

/-- Pretty-print one field of a registered family applied to a generic
input, collapsed to one line. -/
def ppFamilyField (field : Name) (family input : Expr) : MetaM String := do
  let e ← whnf (mkApp (← mkAppM field #[family]) input)
  return ((toString (← ppExpr e)).replace "\n" " ").trimAscii.toString

/-- Core-owned prose description of the residual carried by one open leaf.
The structural template is fixed by the backend contract semantics of the
key kind; every specific component is pretty-printed from the registered
family at a generic input.  Nothing problem-dependent is hardcoded. -/
def residualProse (data : Expr) (ctor : Name) (index? : Option Nat)
    (indent : String) (input : Expr) : MetaM (List String) := do
  let dataType ← whnf (← inferType data)
  let args := dataType.getAppArgs
  if args.size < 2 then return []
  let targetE := args[1]!
  do
    let pad := indent ++ "      "
    if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid then
      let objectE ← mkAppM ``Hypostructure.Core.Strategy.ProblemInput.object #[input]
      let predicateE ← whnf (mkApp
        (← mkAppM ``Hypostructure.Core.Target.Predicate #[targetE]) objectE)
      let predicate :=
        ((toString (← ppExpr predicateE)).replace "\n" " ").trimAscii.toString
      return [pad ++ "residual: a certified avoidance of the registered target at this leaf's input —",
         pad ++ s!"  ¬({predicate})"]
    else
      let some (_, _, fieldName) :=
        indexedKeys.find? (fun entry => entry.1 == ctor) | return []
      let some index := index? | return []
      let some family ← listNth (← mkAppM fieldName #[data]) index | return []
      if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.orderedWitnessScan then
        let item ← ppFamilyField ``Hypostructure.Core.ScanData.Item family input
        let witness ← ppFamilyField ``Hypostructure.Core.ScanData.witness family input
        return [pad ++ "residual: the complete ordered scan record over the registered schedule —",
           pad ++ s!"  one entry per scheduled item of {item},",
           pad ++ s!"  each carrying a certified decision of the witness {witness}"]
      else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.responseClassifier then
        let item ← ppFamilyField ``Hypostructure.Core.ResponseData.Item family input
        let cls ← ppFamilyField ``Hypostructure.Core.ResponseData.Class family input
        return [pad ++ "residual: the complete classified response table —",
           pad ++ s!"  one entry per scheduled item of {item},",
           pad ++ s!"  each with its certified class in {cls}"]
      else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.capacityLedger then
        let item ← ppFamilyField ``Hypostructure.Core.CapacityData.Item family input
        let contribution ← ppFamilyField ``Hypostructure.Core.CapacityData.contribution family input
        let capacity ← ppFamilyField ``Hypostructure.Core.CapacityData.capacity family input
        return [pad ++ "residual: the complete capacity account —",
           pad ++ s!"  one entry per scheduled item of {item},",
           pad ++ s!"  each certifying its contribution {contribution}",
           pad ++ s!"  within the capacity {capacity} of its class"]
      else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.supportLocalization then
        let cell ← ppFamilyField ``Hypostructure.Core.LocalizationData.Cell family input
        let budget ← ppFamilyField ``Hypostructure.Core.LocalizationData.localBudget family input
        return [pad ++ s!"residual: one selected cell of {cell}",
           pad ++ s!"  with a certified strictly negative local budget {budget}"]
      else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.rankBudget then
        let high ← ppFamilyField ``Hypostructure.Core.RankBudgetData.high family input
        let low ← ppFamilyField ``Hypostructure.Core.RankBudgetData.low family input
        return [pad ++ "residual: one certified side of the exhaustive threshold split —",
           pad ++ s!"  high: {high}",
           pad ++ s!"  low: {low}"]
      else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.closedCode then
        let code ← ppFamilyField ``Hypostructure.Core.ClosedCodeData.Code family input
        return [pad ++ s!"residual: the certified closure equation on the code table {code} —",
           pad ++ "  the registered observation fixes the target code"]
      else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
        let left ← ppFamilyField ``Hypostructure.Core.DichotomyData.LeftPayload family input
        let right ← ppFamilyField ``Hypostructure.Core.DichotomyData.RightPayload family input
        return [pad ++ "residual: the routed branch join —",
           pad ++ s!"  left witness: {left}",
           pad ++ s!"  right witness: {right}"]
      else
        return []

/-- Prose for the retained branch witness of one dichotomy side. -/
def dichotomyWitnessProse (split : Expr) (field : Name) (indent : String)
    (input : Expr) : MetaM (List String) := do
  let payload ← ppFamilyField field split input
  return [indent ++ "      residual: the retained branch witness — " ++ payload]

/-! ### Contradiction search

Every accumulated constraint that carries a real proposition (not just
display text) participates in an honest, mechanical search: if any single
constraint is `False`, or any two constraints are a direct complementary
pair `P` and `¬P` (checked with `isDefEq`, not string matching), the leaf's
residual is empty — a genuine, kernel-checkable finding, not an assertion.
The search never claims more than it verifies: when it finds nothing, it
says so explicitly rather than staying silent. -/

/-- If `e` is `Not p` (in either its constant-application or unfolded
non-dependent-arrow-to-`False` form), return `p`. -/
def asNegation? (e : Expr) : MetaM (Option Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``Not 1 then
    return some (e.getAppArgs[0]!)
  else
    match e with
    | .forallE _ dom body _ =>
        if body.hasLooseBVars then
          return none
        else if (← whnf body).isConstOf ``False then
          return some dom
        else
          return none
    | _ => return none

/-- Pairwise search for a direct contradiction among constraints that carry
a real proposition.  Returns the display names of the two conflicting
constraints (or the same name twice, for a lone `False`). -/
partial def findContradiction (constraints : List Constraint) :
    MetaM (Option (String × String)) := do
  match constraints.find? (fun c => c.2.isSome) with
  | none => return none
  | some _ =>
    let named := constraints.filterMap fun (name, e?) =>
      e?.map fun e => (name, e)
    -- a lone `False` constraint is already a contradiction on its own
    for (name, e) in named do
      if ← isDefEq e (mkConst ``False) then
        return some (name, name)
    -- pairwise complementary search
    for (nameI, propI) in named do
      for (nameJ, propJ) in named do
        if nameI != nameJ then
          match ← asNegation? propI with
          | some negated =>
              if ← isDefEq negated propJ then
                return some (nameI, nameJ)
          | none => pure ()
    return none

/-- Format the outcome of the contradiction search. -/
def contradictionLines (found : Option (String × String)) (indent : String) :
    List String :=
  let pad := indent ++ "      "
  match found with
  | some (a, b) =>
      if a == b then
        [pad ++ s!"contradiction check: UNCONDITIONAL CLOSURE — the constraint '{a}' is mechanically `False`; this residual is empty."]
      else
        [pad ++ "contradiction check: UNCONDITIONAL CLOSURE — a direct contradiction was mechanically found",
         pad ++ s!"  between the constraints '{a}' and '{b}'; this residual is empty."]
  | none =>
      [pad ++ "contradiction check: no direct (P and its negation) contradiction found among the",
       pad ++ "  accumulated constraints above; the residual stands as printed."]

/-! ### Accumulated-constraint rendering

Each executed vertex narrows the residual deterministically: its certified
payload is retained in the ledger, so the residual at any open leaf exists
only conjoined with every constraint accumulated along its path.  The
renderer below emits that accumulation as one LaTeX statement, with every
component pretty-printed from the registered data at a generic input. -/

/-- Wrap a pretty-printed Lean fragment for LaTeX embedding. -/
def tex (s : String) : String :=
  -- `_`/`^`/`#`/`%`/`&` keep math-active catcodes even inside `\text{...}`
  -- when it appears within a math environment (e.g. `align*`), so they
  -- must be escaped here — the single choke-point every pretty-printed
  -- fragment passes through before being wrapped for LaTeX.
  let s := s.replace "_" "\\_"
  let s := s.replace "^" "\\textasciicircum{}"
  let s := s.replace "#" "\\#"
  let s := s.replace "%" "\\%"
  let s := s.replace "&" "\\&"
  s!"\\text\{{s}}"

/-- The certified constraint one executed vertex contributes: a LaTeX
fragment over the shared generic input, paired with its proposition when it
is a single faithfully-representable fact.  `none` for unrenderable kinds. -/
def vertexConstraintLatex (data : Expr) (ctor : Name) (index? : Option Nat)
    (input : Expr) : MetaM (Option Constraint) := do
  let dataType ← whnf (← inferType data)
  let args := dataType.getAppArgs
  if args.size < 2 then return none
  let targetE := args[1]!
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid then
    let objectE ← mkAppM ``Hypostructure.Core.Strategy.ProblemInput.object #[input]
    let predicateE ← whnf (mkApp
      (← mkAppM ``Hypostructure.Core.Target.Predicate #[targetE]) objectE)
    let predicate :=
      ((toString (← ppExpr predicateE)).replace "\n" " ").trimAscii.toString
    let negProp ← mkAppM ``Not #[predicateE]
    return some (s!"\\neg\\big({tex predicate}\\big)", some negProp)
  else
    let some (_, _, fieldName) :=
      indexedKeys.find? (fun entry => entry.1 == ctor) | return none
    let some index := index? | return none
    let some family ← listNth (← mkAppM fieldName #[data]) index
      | return none
    if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.orderedWitnessScan then
      let item ← ppFamilyField ``Hypostructure.Core.ScanData.Item family input
      let witness ← ppFamilyField ``Hypostructure.Core.ScanData.witness family input
      return some
        (s!"\\forall i \\in \\mathrm\{sched}(x) \\subseteq {tex item},\\ W(i) \\lor \\neg W(i),\\ W = {tex witness}",
         none)
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.responseClassifier then
      let item ← ppFamilyField ``Hypostructure.Core.ResponseData.Item family input
      let cls ← ppFamilyField ``Hypostructure.Core.ResponseData.Class family input
      return some
        (s!"\\forall i \\in \\mathrm\{sched}(x) \\subseteq {tex item},\\ \\mathrm\{classify}(\\mathrm\{observe}(i)) \\in {tex cls}",
         none)
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.capacityLedger then
      let contribution ← ppFamilyField ``Hypostructure.Core.CapacityData.contribution family input
      let capacity ← ppFamilyField ``Hypostructure.Core.CapacityData.capacity family input
      return some
        (s!"\\forall i \\in \\mathrm\{sched}(x),\\ {tex contribution}(i) \\le {tex capacity}(\\mathrm\{class}(i))",
         none)
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.supportLocalization then
      let cell ← ppFamilyField ``Hypostructure.Core.LocalizationData.Cell family input
      let budget ← ppFamilyField ``Hypostructure.Core.LocalizationData.localBudget family input
      return some (s!"\\exists c \\in {tex cell},\\ {tex budget}(c) < 0", none)
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.rankBudget then
      let highE ← whnf (mkApp
        (← mkAppM ``Hypostructure.Core.RankBudgetData.high #[family]) input)
      let lowE ← whnf (mkApp
        (← mkAppM ``Hypostructure.Core.RankBudgetData.low #[family]) input)
      let high := ((toString (← ppExpr highE)).replace "\n" " ").trimAscii.toString
      let low := ((toString (← ppExpr lowE)).replace "\n" " ").trimAscii.toString
      let disjProp ← mkAppM ``Or #[highE, lowE]
      return some (s!"{tex high} \\lor {tex low}", some disjProp)
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.closedCode then
      let code ← ppFamilyField ``Hypostructure.Core.ClosedCodeData.Code family input
      return some
        (s!"\\mathrm\{observed}(\\mathrm\{target}) = \\mathrm\{target} \\ \\text\{on the code table } {tex code}",
         none)
    else
      return none

/-- The retained side witness of one dichotomy, as a LaTeX fragment paired
with the proposition `Nonempty (side payload)`. -/
def sideWitnessLatex (split : Expr) (field : Name) (input : Expr) :
    MetaM Constraint := do
  let payloadType ← whnf (mkApp (← mkAppM field #[split]) input)
  let payload ← ppFamilyField field split input
  let prop ← mkAppM ``Nonempty #[payloadType]
  return (tex payload, some prop)

/-- The constraint the OUTER continuation of a dichotomy may soundly assume.
When a side is registered-closed, any residual reaching later code
necessarily did NOT take that side — a real strengthening, not the
tautological "left or right".  When both sides are closed, later code is
unreachable altogether (`False`).  When neither side is closed, the
honest (non-restrictive) disjunction is kept, display-only. -/
def dichotomyJoinConstraint (split : Expr) (leftClosed rightClosed : Bool)
    (input : Expr) : MetaM Constraint := do
  if leftClosed && rightClosed then
    return ("\\bot\\ \\text{(both branches closed here --- unreachable)}",
      some (mkConst ``False))
  else if leftClosed then
    let (leftText, leftProp?) ← sideWitnessLatex split
      ``Hypostructure.Core.DichotomyData.LeftPayload input
    let negProp ← match leftProp? with
      | some p => some <$> mkAppM ``Not #[p]
      | none => pure none
    return (s!"\\neg {leftText}", negProp)
  else if rightClosed then
    let (rightText, rightProp?) ← sideWitnessLatex split
      ``Hypostructure.Core.DichotomyData.RightPayload input
    let negProp ← match rightProp? with
      | some p => some <$> mkAppM ``Not #[p]
      | none => pure none
    return (s!"\\neg {rightText}", negProp)
  else
    let leftText ← ppFamilyField
      ``Hypostructure.Core.DichotomyData.LeftPayload split input
    let rightText ← ppFamilyField
      ``Hypostructure.Core.DichotomyData.RightPayload split input
    return (s!"{tex leftText} \\lor {tex rightText}", none)

/-- Format the accumulated constraints of one open leaf as a LaTeX
statement — a generic input satisfying the registered baseline conjoined
with every constraint along the leaf's path — followed by the mechanical
contradiction check over the same accumulation (baseline included). -/
def accumulatedLatex (data : Expr) (constraints : List Constraint)
    (indent : String) (input : Expr) : MetaM (List String) := do
  let dataType ← whnf (← inferType data)
  let args := dataType.getAppArgs
  if args.size < 2 then return []
  let problemE := args[0]!
  let objectE ← mkAppM ``Hypostructure.Core.Strategy.ProblemInput.object #[input]
  let baselineE ← whnf (mkApp
    (← mkAppM ``Hypostructure.Core.Problem.Baseline #[problemE]) objectE)
  let baseline :=
    ((toString (← ppExpr baselineE)).replace "\n" " ").trimAscii.toString
  let pad := indent ++ "      "
  let header := pad ++ "accumulated residual constraints (LaTeX):"
  let opening := pad ++ s!"  \\exists\\, x\\ \\text\{(problem input)\\!}:\\quad {tex baseline}"
  let conjuncts := constraints.map fun (c, _) => pad ++ s!"  \\;\\land\\; {c}"
  let searchPool : List Constraint := ("baseline", some baselineE) :: constraints
  let found ← findContradiction searchPool
  return (header :: opening :: conjuncts) ++ contradictionLines found indent

/-- Status suffix for one vertex line.  `closure?` carries the reason this
position is closed (root closure or a registered branch closure); `none`
means the position is open. -/
def vertexStatus (closure? : Option String) (isClosure : Bool)
    (terminal : Bool) (_family? : Option String) : String :=
  match closure? with
  | some _ => " — closed"
  | none =>
    if terminal then " — open"
    else if isClosure then " — closed"
    else ""

/-- Render a literal `Blueprint` as indented executive-summary lines with
per-vertex status computed from the registered data: `closure?` is the
enclosing closure reason (root closure or a registered branch closure), and
each dichotomy's sides are annotated from its registered `closeLeft`/
`closeRight` facts.  `terminal` marks terminal-leaf position.  `input` is
the one generic input shared by the entire walk, so every accumulated
constraint is a real proposition over the same variable.  Returns `none`
when the blueprint or its data is not a closed literal. -/
partial def blueprintLines (data dag : Expr) (indent : String)
    (closure? : Option String) (terminal : Bool)
    (accumulated : List Constraint) (input : Expr) (nextId : Nat) :
    MetaM (Option (List String × List Constraint × Nat)) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root =>
      return some ([], accumulated, nextId)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate => do
      let args := blueprintCtorArgs dag 2
      let some (rest, accRest, nextId) ←
        blueprintLines data args[0]! indent closure? terminal accumulated input nextId
        | return none
      let label ← evalStrLiteral args[1]!
      return some (rest ++ [indent ++ "  ↳ note: " ++ label], accRest, nextId)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled => do
      -- Not immediately followed by a `step`/`branch` (the peeled cases
      -- below consume it there); pass through silently — there is no
      -- vertex here to attach the name to.
      blueprintLines data (blueprintCtorArgs dag 2)[0]!
        indent closure? terminal accumulated input nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      blueprintLines data (blueprintCtorArgs dag 2)[0]!
        indent closure? terminal accumulated input nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute => do
      let args := blueprintCtorArgs dag 3
      let some route ← evalResolvedRoute args[1]! args[2]! | return none
      let some (rest, accRest, nextId) ←
        blueprintLines data args[0]! indent closure? false accumulated input nextId
        | return none
      let label :=
        if route.name.isEmpty then ""
        else " \"" ++ route.name ++ "\""
      let note :=
        if route.note.isEmpty then []
        else [indent ++ "  ↳ note: " ++ route.note]
      let line := indent ++ s!"  ↳ autoroute{label}: v{route.sourceId} → " ++
        s!"v{route.destinationId}; relation={route.relation}; " ++
        s!"scope={route.scope}; " ++
        s!"depth {route.sourceDepth}→{route.destinationDepth}; " ++
        s!"selection={route.selectedBy}; bridge_work={route.work}; " ++
        s!"destination_work={route.destinationWork}"
      return some (rest ++ [line] ++ note, accRest, nextId)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let (restExpr, metadata) ← peelMetadata args[0]!
      let some (rest, accRest, nextId) ←
        blueprintLines data restExpr indent closure? false accumulated input nextId
        | return none
      let id := nextId
      let key ← strategyKeyOfRef args[1]!
      let some ctor := key.getAppFn.constName? | return none
      let index? ← if key.getAppArgs.isEmpty then pure none
        else evalNatLiteral key.getAppArgs[0]!
      let some (display, family?) := keyInfo ctor index? | return none
      let isClosure :=
        ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid
      let effectiveClosure? := closure?
      let nameSuffix := match metadata.name with
        | some n => s!" \"{n}\""
        | none => ""
      let line := indent ++ s!"[#{id}] " ++ display ++ nameSuffix ++
        vertexStatus effectiveClosure? isClosure terminal family?
      let ownConstraint? ← vertexConstraintLatex data ctor index? input
      let accOut := accRest ++ ownConstraint?.toList
      let prose ←
        if effectiveClosure?.isNone && terminal then do
          pure ((← residualProse data ctor index? indent input) ++
            (← accumulatedLatex data accOut indent input))
        else
          pure []
      let noteLines := (metadata.note.map fun note =>
        [indent ++ "  ↳ note: " ++ note]).getD []
      return some (rest ++ [line] ++ noteLines ++ prose, accOut, id + 1)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let (restExpr, metadata) ← peelMetadata args[0]!
      let some (rest, accRest, nextId) ←
        blueprintLines data restExpr indent closure? false accumulated input nextId
        | return none
      let id := nextId
      let some (ctor, index) ← binaryKeyParts args[1]! | return none
      let split? ← registeredDichotomy? data ctor index
      let (leftClosed, rightClosed) ← binaryRegisteredClosures data ctor index
      let branchReason := "closed by registered branch closure"
      let leftClosure? := closure? <|> (if leftClosed then some branchReason else none)
      let rightClosure? := closure? <|> (if rightClosed then some branchReason else none)
      let sideWitness? (field : Name) : MetaM (Option Constraint) :=
        match split? with
        | some split => some <$> sideWitnessLatex split field input
        | none => pure none
      let leftWitness? ← sideWitness? ``Hypostructure.Core.DichotomyData.LeftPayload
      let rightWitness? ← sideWitness? ``Hypostructure.Core.DichotomyData.RightPayload
      let some (left, accLeft, nextId) ← blueprintLines data args[2]! (indent ++ "    ")
        leftClosure? terminal (accRest ++ leftWitness?.toList) input (id + 1) | return none
      let some (right, accRight, nextId) ← blueprintLines data args[3]! (indent ++ "    ")
        rightClosure? terminal (accRest ++ rightWitness?.toList) input nextId | return none
      let emptyContinuation (side? : Option String) :=
        match side? with
        | some _ => "(empty continuation — closed)"
        | none =>
          if terminal then "(empty continuation — open)"
          else "(empty continuation)"
      let sideProse (side? : Option String) (field : Name)
          (accSide : List Constraint) : MetaM (List String) :=
        match side?, split? with
        | none, some split =>
            if terminal then do
              pure ((← dichotomyWitnessProse split field (indent ++ "  ") input) ++
                (← accumulatedLatex data accSide (indent ++ "  ") input))
            else pure []
        | _, _ => pure []
      let leftBlock ←
        if left.isEmpty then do
          pure ([indent ++ "    " ++ emptyContinuation leftClosure?] ++
            (← sideProse leftClosure?
              ``Hypostructure.Core.DichotomyData.LeftPayload accLeft))
        else pure left
      let rightBlock ←
        if right.isEmpty then do
          pure ([indent ++ "    " ++ emptyContinuation rightClosure?] ++
            (← sideProse rightClosure?
              ``Hypostructure.Core.DichotomyData.RightPayload accRight))
        else pure right
      let headerStatus :=
        match closure? with
        | some _ => " — closed"
        | none => ""
      let sideLabel (name : String) (_side? : Option String) :=
        indent ++ s!"  {name}:"
      let joinConstraint? ← match split? with
        | some split =>
            some <$> dichotomyJoinConstraint split leftClosed rightClosed input
        | none => pure none
      let accOut := accRest ++ joinConstraint?.toList
      let nameSuffix := match metadata.name with
        | some n => s!" \"{n}\""
        | none => ""
      let noteLines := (metadata.note.map fun note =>
        [indent ++ "  ↳ note: " ++ note]).getD []
      let (defaultLeftName, defaultRightName) := binaryDefaultNames ctor
      let leftName := metadata.leftName.getD defaultLeftName
      let rightName := metadata.rightName.getD defaultRightName
      let leftNotes := (metadata.leftNote.map fun note =>
        [indent ++ "    ↳ note: " ++ note]).getD []
      let rightNotes := (metadata.rightNote.map fun note =>
        [indent ++ "    ↳ note: " ++ note]).getD []
      let display := (keyInfo ctor (some index)).map (·.1)
        |>.getD s!"binary strategy #{index}"
      return some (((rest ++ [indent ++ s!"[#{id}] {display}" ++ nameSuffix ++ headerStatus])
        ++ noteLines
        ++ [sideLabel leftName leftClosure?] ++ leftNotes ++ leftBlock
        ++ [sideLabel rightName rightClosure?] ++ rightNotes ++ rightBlock), accOut, nextId)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let (restExpr, metadata) ← peelMetadata args[0]!
      let some (rest, accRest, nextId) ←
        blueprintLines data restExpr indent closure? false accumulated input nextId
        | return none
      let id := nextId
      let some index ← evalFinLiteral args[1]! | return none
      let some (exceptional, _, nextId) ←
        blueprintLines data args[2]! (indent ++ "    ") closure? terminal
          accRest input (id + 1) | return none
      let some (structured, _, nextId) ←
        blueprintLines data args[3]! (indent ++ "    ") closure? terminal
          accRest input nextId | return none
      let some (bounded, _, nextId) ←
        blueprintLines data args[4]! (indent ++ "    ") closure? terminal
          accRest input nextId | return none
      let empty :=
        if terminal then "(empty continuation — open)"
        else "(empty continuation)"
      let branchBlock (lines : List String) :=
        if lines.isEmpty then [indent ++ "    " ++ empty] else lines
      let nameSuffix := metadata.name.map
        (fun name => s!" \"{name}\"") |>.getD ""
      let noteLines := metadata.note.map
        (fun note => [indent ++ "  ↳ note: " ++ note]) |>.getD []
      return some
        (rest ++
          [indent ++ s!"[#{id}] homogeneousBottleneck #{index}" ++ nameSuffix,
           indent ++ "  target: closed internally by Core"] ++
          noteLines ++
          [indent ++ "  exceptional:"] ++ branchBlock exceptional ++
          [indent ++ "  structured:"] ++ branchBlock structured ++
          [indent ++ "  bounded:"] ++ branchBlock bounded,
         accRest, nextId)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      let (restExpr, metadata) ← peelMetadata args[0]!
      let some (rest, accRest, nextId) ←
        blueprintLines data restExpr indent closure? false accumulated input nextId
        | return none
      let id := nextId
      let some index ← evalFinLiteral args[1]! | return none
      -- `args[2]` is `CounterexampleContinuationMetadata`, not a blueprint.  The
      -- four sealed vertices it names have no continuation of their own, so
      -- they are rendered from their own metadata rather than recursed into;
      -- `Blueprint.pathOf` and `blueprintWorkBound` treat them the same way.
      let continuation :=
        [ indent ++ "    targetAlgebraReduction — sealed",
          indent ++ "    minimalSubobjectExclusion — sealed",
          indent ++ "    criticalModificationStructure — sealed",
          indent ++ "    interfaceReplacementClosure — sealed" ]
      let nameSuffix := metadata.name.map
        (fun name => s!" \"{name}\"") |>.getD ""
      let noteLines := metadata.note.map
        (fun note => [indent ++ "  ↳ note: " ++ note]) |>.getD []
      return some
        (rest ++
          [indent ++ s!"[#{id}] minimalCounterexampleSelection #{index}" ++
            nameSuffix,
           indent ++ "  target: closed internally by Core",
           indent ++ "  counterexample:"] ++
          noteLines ++ continuation,
         accRest, id + 1)
  | _ => return none

/-! ### PDF rendering: tree diagram and residual math blocks

These renderers reuse the exact same closure/terminal propagation as
`blueprintLines` (dichotomy branch closures negate outward, terminal
leaves carry the residual) so the generated PDF is never out of step with
the terminal report — both are projections of the same sealed run. -/

/-- Escape the one LaTeX-special character that can appear in a Core-owned
key label (`#`, from an index like `orderedWitnessScan #0`). -/
def escapeLatex (s : String) : String :=
  let s := s.replace "\\" ""
  let s := s.replace "_" "\\_"
  let s := s.replace "%" "\\%"
  let s := s.replace "&" "\\&"
  let s := s.replace "^" "\\textasciicircum{}"
  s.replace "#" "\\#"

/-- Insert a `forest` `edge label` option naming the incoming arrow (`left`/
`right`) into the OUTERMOST bracket of an already-built tree fragment.  Every
bracket this module builds has the fixed shape `[header\n children]` (or,
for a childless leaf, the one-line `[header]`), so the edge-label option is
always inserted right after `header` — before the first newline if there is
one, otherwise before the closing `]`.  `tree` is never touched beyond its
own outermost bracket: the option applies only to the vertex the edge points
at, not to anything nested inside it. -/
def insertNodeOption (tree opt : String) : String :=
  if tree.isEmpty then tree
  else
    match tree.splitOn "\n" with
    | first :: rest =>
        if rest.isEmpty then
          if first.endsWith "]" then (first.dropEnd 1).toString ++ opt ++ "]"
          else first ++ opt
        else String.intercalate "\n" ((first ++ opt) :: rest)
    | [] => tree

def attachEdgeLabel (tree side : String) : String :=
  insertNodeOption tree
    (", edge label={node[midway, fill=white, font=\\tiny]{" ++ side ++ "}}")

/-- Flatten a straight-line `Blueprint` run (guaranteed by `branchRun`'s
`endsAtLeaf = true` to contain no nested dichotomy) into its rendered
vertices in order, each as `(id, title, style)` — the same title/style a
normal `blueprintForestCont` vertex would get, just collected as a list
instead of composed into nested brackets, so it can be drawn as a
horizontal side-chain of plain TikZ nodes alongside the dichotomy that
starts it rather than another full-height forest column. -/
partial def blueprintForestFlat (data dag : Expr) (closure? : Option String)
    (terminal : Bool) (nextId : Nat) :
    MetaM (Nat × List (Nat × String × String)) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root => return (nextId, [])
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate =>
      blueprintForestFlat data (blueprintCtorArgs dag 2)[0]!
        closure? terminal nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled =>
      blueprintForestFlat data (blueprintCtorArgs dag 2)[0]!
        closure? terminal nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      blueprintForestFlat data (blueprintCtorArgs dag 2)[0]!
        closure? terminal nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute =>
      blueprintForestFlat data (blueprintCtorArgs dag 3)[0]!
        closure? false nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let (restExpr, metadata) ← peelMetadata args[0]!
      let (nextId, restList) ←
        blueprintForestFlat data restExpr closure? false nextId
      let id := nextId
      let key ← strategyKeyOfRef args[1]!
      let some ctor := key.getAppFn.constName? | return (id, restList)
      let index? ← if key.getAppArgs.isEmpty then pure none
        else evalNatLiteral key.getAppArgs[0]!
      let some (display, _) := keyInfo ctor index? | return (id, restList)
      let isClosure :=
        ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid
      let style :=
        match closure? with
        | some _ =>
            if isClosure then "target, fill=green!15"
            else "terminal, fill=green!15"
        | none =>
          if terminal && isClosure then "target, fill=red!25, thick"
          else if terminal then "terminal, fill=red!25, thick"
          else if isClosure then "target, fill=yellow!20"
          else "archnode, fill=white"
      let title := "\\#" ++ toString id ++ " " ++ escapeLatex display
      let label := match metadata.name with
        | some n => title ++ " \"" ++ escapeLatex n ++ "\""
        | none => title
      return (id + 1, restList ++ [(id, label, style)])
  | _ => return (nextId, [])

/-- Render a flattened side-run as a chain of plain TikZ nodes extending
right from `parentName`, each connected to the previous by a plain arrow;
the first arrow (from the dichotomy itself) carries the `left`/`right` edge
label, exactly like a normal forest child would. -/
partial def chainNodes (parentName pfx : String) :
    List (Nat × String × String) → Nat → String
  | [], _ => ""
  | (_, label, style) :: rest, i =>
      let name := pfx ++ "c" ++ toString i
      let node := "\\node[" ++ style ++ ", right=6mm of " ++ parentName ++
        "] (" ++ name ++ ") {" ++ label ++ "};\n"
      let edge := "\\draw[-Latex] (" ++ parentName ++ ") -- (" ++ name ++ ");\n"
      node ++ edge ++ chainNodes name pfx rest (i + 1)

def renderSideChain (parentName sideLabel pfx : String)
    (flat : List (Nat × String × String)) : String :=
  match flat with
  | [] => ""
  | (_, label0, style0) :: rest =>
      let name0 := pfx ++ "c0"
      let node0 := "\\node[" ++ style0 ++ ", right=6mm of " ++ parentName ++
        "] (" ++ name0 ++ ") {" ++ label0 ++ "};\n"
      let edge0 := "\\draw[-Latex] (" ++ parentName ++ ") -- (" ++ name0 ++
        ") node[midway, above, font=\\tiny]{" ++ sideLabel ++ "};\n"
      node0 ++ edge0 ++ chainNodes name0 pfx rest 1

/-- Continuation-passing bracket builder for one blueprint piece: given the
`forest` bracket content to nest as the child of THIS piece's last vertex,
produce the complete bracket string from `Blueprint.root` down, plus the
next free node id.  Node ids are assigned in the exact same pre-order as
`blueprintLines`, so the two views cross-reference by `#id`.  Node coloring
mirrors `vertexStatus` exactly (closed = green, open leaf = red, dichotomy =
blue, ordinary executed vertex = white).  The main diagram shows titles only:
a `Blueprint.annotate` note contributes no node here (it is surfaced in the
CLI summary and the detailed panels instead), while a `Blueprint.labelled`
custom name IS part of the title, since it prettifies the very node it
attaches to. -/
partial def blueprintForestCont (data dag : Expr) (closure? : Option String)
    (terminal : Bool) (input : Expr) (nextId : Nat) :
    MetaM (Nat × (String → MetaM String)) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root =>
      return (nextId, fun children => pure children)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate => do
      -- The main diagram shows titles only; the note itself is surfaced in
      -- the CLI summary and the detailed panels (`blueprintLines`), not
      -- here — so this is a pure pass-through with no node of its own.
      blueprintForestCont data (blueprintCtorArgs dag 2)[0]!
        closure? terminal input nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled => do
      -- Not immediately followed by a `step`/`branch` (the peeled cases
      -- below consume it there); pass through silently.
      blueprintForestCont data (blueprintCtorArgs dag 2)[0]!
        closure? terminal input nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      blueprintForestCont data (blueprintCtorArgs dag 2)[0]!
        closure? terminal input nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute =>
      blueprintForestCont data (blueprintCtorArgs dag 3)[0]!
        closure? false input nextId
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let (restExpr, metadata) ← peelMetadata args[0]!
      let (nextId, restCont) ←
        blueprintForestCont data restExpr closure? false input nextId
      let id := nextId
      let key ← strategyKeyOfRef args[1]!
      let some ctor := key.getAppFn.constName?
        | return (id, fun children => pure children)
      let index? ← if key.getAppArgs.isEmpty then pure none
        else evalNatLiteral key.getAppArgs[0]!
      let some (display, _) := keyInfo ctor index?
        | return (id, fun children => pure children)
      let isClosure :=
        ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid
      let style :=
        match closure? with
        | some _ =>
            if isClosure then "target, fill=green!15"
            else "terminal, fill=green!15"
        | none =>
          if terminal && isClosure then "target, fill=red!25, thick"
          else if terminal then "terminal, fill=red!25, thick"
          else if isClosure then "target, fill=yellow!20"
          else "archnode, fill=white"
      let title := s!"\\#{id} " ++ escapeLatex display
      let label := match metadata.name with
        | some n => "{" ++ title ++ " \"" ++ escapeLatex n ++ "\"}"
        | none => title
      return (id + 1, fun children => do
        restCont s!"[{label}, {style}\n{children}]")
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let (restExpr, metadata) ← peelMetadata args[0]!
      let (nextId, restCont) ←
        blueprintForestCont data restExpr closure? false input nextId
      let id := nextId
      let some (ctor, index) ← binaryKeyParts args[1]!
        | return (id, fun children => pure children)
      let (leftClosed, rightClosed) ← binaryRegisteredClosures data ctor index
      let leftClosure? := closure? <|> (if leftClosed then some "closed" else none)
      let rightClosure? := closure? <|> (if rightClosed then some "closed" else none)
      let (defaultLeftName, defaultRightName) := binaryDefaultNames ctor
      let leftName := metadata.leftName.getD defaultLeftName
      let rightName := metadata.rightName.getD defaultRightName
      -- Decide which side (if either) is short enough to hang off this
      -- dichotomy as a horizontal side-chain instead of stacking as
      -- another full-height forest column — like the paper's own
      -- flow diagrams, where a quick exit branches sideways from the
      -- decision point and the main proof flow keeps going straight down.
      -- A side only qualifies if it actually finishes (reaches its own
      -- closure/residual leaf) within 3 rendered vertices, not when it
      -- merely forks again; when both qualify, only the strictly shorter
      -- one gets the side-chain treatment, and on a tie the right side
      -- does (the left stays on the main vertical spine).
      let (leftLen, leftEndsAtLeaf) ← branchRun args[2]!
      let (rightLen, rightEndsAtLeaf) ← branchRun args[3]!
      let leftShort := leftLen ≤ 3 && leftEndsAtLeaf
      let rightShort := rightLen ≤ 3 && rightEndsAtLeaf
      let shortSide : Option Bool :=  -- some true = left is the short side
        if leftShort then
          if rightShort then some (leftLen < rightLen) else some true
        else if rightShort then some false
        else none
      let nodeName := "nd" ++ toString id
      let (nextId, leftPart) ←
        if shortSide == some true then do
          let (nid, flat) ←
            blueprintForestFlat data args[2]! leftClosure? terminal (id + 1)
          pure (nid, Sum.inr flat)
        else do
          let (nid, cont) ←
            blueprintForestCont data args[2]! leftClosure? terminal input (id + 1)
          pure (nid, Sum.inl (← cont ""))
      let (nextId, rightPart) ←
        if shortSide == some false then do
          let (nid, flat) ←
            blueprintForestFlat data args[3]! rightClosure? terminal nextId
          pure (nid, Sum.inr flat)
        else do
          let (nid, cont) ←
            blueprintForestCont data args[3]! rightClosure? terminal input nextId
          pure (nid, Sum.inl (← cont ""))
      -- A real (non-short) side becomes a normal forest child, with its
      -- side named on the connecting arrow via `edge label`, exactly as
      -- before.  A short side becomes NO forest child at all — it is drawn
      -- as a small chain of plain TikZ nodes extending right from this
      -- dichotomy's own node (`nodeName`), using the identical node styles
      -- (archnode/target/terminal colors) so it reads as the same kind of
      -- node, just positioned beside the decision point instead of below
      -- it — this is what keeps the main flow vertical instead of
      -- drifting wider at every level.
      let mkChild (tree side : String) : String :=
        attachEdgeLabel
          (if tree.isEmpty then "[(empty), archnode, fill=gray!10]" else tree) side
      let (childBrackets, sideTikz) :=
        match leftPart, rightPart with
        | Sum.inl leftTree, Sum.inl rightTree =>
            ([mkChild leftTree leftName,
              mkChild rightTree rightName], "")
        | Sum.inr leftFlat, Sum.inl rightTree =>
            ([mkChild rightTree rightName],
              renderSideChain nodeName leftName
                ("l" ++ toString id) leftFlat)
        | Sum.inl leftTree, Sum.inr rightFlat =>
            ([mkChild leftTree leftName],
              renderSideChain nodeName rightName
                ("r" ++ toString id) rightFlat)
        | Sum.inr leftFlat, Sum.inr rightFlat =>
            ([], renderSideChain nodeName leftName
                   ("l" ++ toString id) leftFlat ++
                 renderSideChain nodeName rightName
                   ("r" ++ toString id) rightFlat)
      let style :=
        match closure? with
        | some _ => "terminal, fill=green!15"
        | none => "decision, fill=blue!15, thick"
      let styleWithName := style ++ ", name=" ++ nodeName ++
        (if sideTikz.isEmpty then "" else ", tikz={" ++ sideTikz ++ "}")
      let display := (keyInfo ctor (some index)).map (·.1)
        |>.getD ("binary strategy #" ++ toString index)
      let title := "\\#" ++ toString id ++ " " ++ escapeLatex display
      let label := match metadata.name with
        | some n => "{" ++ title ++ " \"" ++ escapeLatex n ++ "\"}"
        | none => title
      -- The dichotomy is strictly binary (its output is one `Sum Left
      -- Right` value); `children` is the vertex sequence that runs AFTER
      -- the join, on EITHER side — never a third alternative outcome.  It
      -- is nested under its own explicit node, visually and textually
      -- distinct from the two case branches above, so the diagram cannot
      -- be misread as a three-way split.
      return (nextId, fun children => do
        let continuationNode :=
          if children.isEmpty then []
          else ["[then (either case), archnode, fill=gray!20, dashed\n" ++ children ++ "]"]
        let body := String.intercalate "\n" (childBrackets ++ continuationNode)
        restCont ("[" ++ label ++ ", " ++ styleWithName ++ "\n" ++ body ++ "]"))
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let (restExpr, metadata) ← peelMetadata args[0]!
      let (nextId, restCont) ←
        blueprintForestCont data restExpr closure? false input nextId
      let id := nextId
      let some index ← evalFinLiteral args[1]!
        | return (id, fun children => pure children)
      let (nextId, exceptionalCont) ←
        blueprintForestCont data args[2]! closure? terminal input (id + 1)
      let exceptionalTree ← exceptionalCont ""
      let (nextId, structuredCont) ←
        blueprintForestCont data args[3]! closure? terminal input nextId
      let structuredTree ← structuredCont ""
      let (nextId, boundedCont) ←
        blueprintForestCont data args[4]! closure? terminal input nextId
      let boundedTree ← boundedCont ""
      let openStyle :=
        if closure?.isSome then "terminal, fill=green!15"
        else "terminal, fill=red!25, thick"
      let branchChild (tree output : String) : String :=
        attachEdgeLabel
          (if tree.isEmpty then
            "[" ++ escapeLatex output ++ " residual, " ++ openStyle ++ "]"
          else tree)
          output
      let targetChild :=
        attachEdgeLabel
          "[target, target, fill=green!15]"
          "target"
      let title :=
        "\\#" ++ toString id ++ " homogeneousBottleneck \\#" ++
          toString index
      let label := match metadata.name with
        | some name =>
            "{" ++ title ++ " \"" ++ escapeLatex name ++ "\"}"
        | none => title
      let style :=
        if closure?.isSome then "terminal, fill=green!15"
        else "decision, fill=blue!15, thick"
      return (nextId, fun children => do
        let continuationNode :=
          if children.isEmpty then []
          else ["[then (any live output), archnode, fill=gray!20, dashed\n" ++
            children ++ "]"]
        let body := String.intercalate "\n"
          ([targetChild,
            branchChild exceptionalTree "exceptional",
            branchChild structuredTree "structured",
            branchChild boundedTree "bounded"] ++ continuationNode)
        restCont ("[" ++ label ++ ", " ++ style ++ "\n" ++ body ++ "]"))
  | _ => return (nextId, fun children => pure children)

/-- The complete `forest`-package tree fragment for the whole blueprint. -/
def blueprintForest (data dag input : Expr) : MetaM String := do
  let (_, cont) ← blueprintForestCont data dag none true input 0
  cont ""

/-! ### Paginated proof-flow panels

`forest` treats the complete tree as one TeX box and therefore cannot break
an oversized proof across pages.  The panel view is a deliberately ordered
projection of the same `blueprintLines` traversal: it keeps every compiled
vertex visible, bounds the amount of material on each page, and labels the
boundary between consecutive panels explicitly.  The complete forest remains
the overview; panels are the readable continuation view. -/

def escapePanelLatex (s : String) : String :=
  let s := s.replace "\\" ""
  let s := s.replace "_" "\\_"
  let s := s.replace "^" "\\textasciicircum{}"
  let s := s.replace "%" "\\%"
  let s := s.replace "&" "\\&"
  let s := s.replace "$" "\\$"
  let s := s.replace "#" "\\#"
  let s := s.replace "~" "\\textasciitilde{}"
  s.replace "" "\\textbackslash{}"

/-- Break `words` into lines of at most `width` characters, greedily
packing whole words per line. -/
partial def packWords (words : List String) (current : String)
    (acc : List String) (width : Nat) : List String :=
  match words with
  | [] => acc ++ (if current.isEmpty then [] else [current])
  | w :: rest =>
      let candidate := if current.isEmpty then w else current ++ " " ++ w
      if candidate.length > width && !current.isEmpty then
        packWords rest w (acc ++ [current]) width
      else
        packWords rest candidate acc width

/-- Word-wrap long panel-node text by inserting forced TikZ line breaks
(`\\`, honored under the tree's `align=center`) every `width` characters at
a word boundary.  `forest`'s `text width` node style does not reliably wrap
long free-text content (e.g. a note's prose, or a long residual predicate),
so panel labels are wrapped explicitly here rather than left to overflow the
page. -/
def wrapPanelText (s : String) (width : Nat := 42) : String :=
  if s.length ≤ width then s
  else String.intercalate " \\\\ " (packWords (s.splitOn " ") "" [] width)

def panelNodeStyle (line : String) : String :=
  if line.contains "dichotomy" then "decision, fill=blue!15, thick"
  else if line.contains "targetOrAvoid" && line.contains "closed" then
    "target, fill=green!15"
  else if line.contains "targetOrAvoid" then "target, fill=red!25, thick"
  else if line.contains "closed" then "terminal, fill=green!15"
  else if line.contains "left:" || line.contains "right:" then "archnode, fill=gray!5"
  else if line.contains "continues to panel" then "archnode, fill=gray!20, dashed"
  else "archnode, fill=white"

partial def panelForestRoot (edgeLabel? : Option String) : List String → String
  | line :: leftLabel :: leftNode :: rightLabel :: rest =>
      if line.contains "dichotomy" && leftLabel.contains "left:" &&
          rightLabel.contains "right:" then
        -- `forest` splits node content on the first top-level comma unless
        -- brace-wrapped; prose labels (e.g. a note's free text) routinely
        -- contain commas, so every label here is brace-wrapped.
        let dichotomy :=
          "{" ++ wrapPanelText (escapePanelLatex line.trimAscii.toString) ++ "}"
        let leftBranch := panelForestRoot (some "left") [leftNode]
        let rightBranch := panelForestRoot (some "right") rest
        s!"[{dichotomy}, {panelNodeStyle line}\n{leftBranch}\n{rightBranch}]"
      else
        let label :=
          "{" ++ wrapPanelText (escapePanelLatex line.trimAscii.toString) ++ "}"
        let style := panelNodeStyle line
        let child := panelForestRoot none (leftLabel :: leftNode :: rightLabel :: rest)
        let edge := match edgeLabel? with
          | some edgeLabel =>
              (if edgeLabel == "left" then "grow'=west, " else "") ++
                "edge label={node[fill=white, inner sep=1.5pt]{" ++ edgeLabel ++ "}}, "
          | none => ""
        if child.isEmpty then s!"[{label}, {edge}{style}]"
        else s!"[{label}, {edge}{style}\n{child}]"
  | line :: rest =>
      let cleanLine := (line.replace " — closed" "").replace " — open" ""
      let label :=
        "{" ++ wrapPanelText (escapePanelLatex cleanLine.trimAscii.toString) ++ "}"
      let style := panelNodeStyle line
      let child := panelForestRoot none rest
      let edge := match edgeLabel? with
        | some edgeLabel =>
            (if edgeLabel == "left" then "grow'=west, " else "") ++
              "edge label={node[fill=white, inner sep=1.5pt]{" ++ edgeLabel ++ "}}, "
        | none => ""
      if child.isEmpty then s!"[{label}, {edge}{style}]"
      else s!"[{label}, {edge}{style}\n{child}]"
  | [] => ""

def panelForest (lines : List String) : String :=
  panelForestRoot none lines

partial def partitionDiagramLines (panelSize : Nat) : List String → List (List String)
  | [] => []
  | lines =>
      let size := max 1 panelSize
      let panel := lines.take size
      panel :: partitionDiagramLines size (lines.drop size)

def blueprintForestPanels (dagLines : List String) : List String :=
  let diagramLines := dagLines.filter fun line =>
    !line.contains "\\" &&
    !line.contains "residual:" &&
    !line.contains "accumulated" &&
    !line.contains "contradiction check"
  let panels := partitionDiagramLines 4 diagramLines
  panels.mapIdx fun index lines =>
    let panelHeader :=
      if index == 0 then "[proof flow overview, fill=gray!8\n"
      else s!"[continued proof flow, fill=gray!8\n"
    let handoff :=
      if index + 1 < panels.length then
        [s!"continues to panel {index + 2}"]
      else []
    panelHeader ++ panelForest (lines ++ handoff) ++ "]"

/-- Ready-to-embed `align*` block for one open leaf's accumulated
constraints: the registered baseline followed by every constraint along
its path, each ending in a line break for direct use inside `align*`. -/
def accumulatedAlignBlock (data : Expr) (constraints : List Constraint)
    (input : Expr) : MetaM String := do
  let dataType ← whnf (← inferType data)
  let args := dataType.getAppArgs
  if args.size < 2 then return ""
  let problemE := args[0]!
  let objectE ← mkAppM ``Hypostructure.Core.Strategy.ProblemInput.object #[input]
  let baselineE ← whnf (mkApp
    (← mkAppM ``Hypostructure.Core.Problem.Baseline #[problemE]) objectE)
  let baseline :=
    ((toString (← ppExpr baselineE)).replace "\n" " ").trimAscii.toString
  -- Each conjunct is its own `dmath*` (auto-wrapping display equation, from
  -- the `breqn` package) rather than an `align*` row: individual accumulated
  -- constraints can be far too long for one page width, and `align*` never
  -- wraps a single row, whereas `dmath*` breaks long expressions across
  -- lines automatically.
  let opening := s!"\\begin\{dmath*}\\exists\\, x\\ \\text\{(problem input)\\!}:\\quad {tex baseline}\\end\{dmath*}\n"
  let conjuncts := constraints.map fun (c, _) =>
    s!"\\begin\{dmath*}\\land\\; {c}\\end\{dmath*}\n"
  return opening ++ String.intercalate "" conjuncts

/-- Mirror of `blueprintLines`'s closure/terminal propagation, collecting
one ready-to-embed residual `align*` block per open leaf (empty when the
run is fully certified).  Kept as an independent traversal from
`blueprintLines` so the PDF renderer can never perturb the tested terminal
report. -/
partial def collectResidualBlocks (data dag : Expr) (closure? : Option String)
    (terminal : Bool) (accumulated : List Constraint) (input : Expr) :
    MetaM (List Constraint × List String) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root =>
      return (accumulated, [])
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let (accRest, blocksRest) ←
        collectResidualBlocks data args[0]! closure? false accumulated input
      let key ← strategyKeyOfRef args[1]!
      let some ctor := key.getAppFn.constName? | return (accRest, blocksRest)
      let index? ← if key.getAppArgs.isEmpty then pure none
        else evalNatLiteral key.getAppArgs[0]!
      let effectiveClosure? := closure?
      let ownConstraint? ← vertexConstraintLatex data ctor index? input
      let accOut := accRest ++ ownConstraint?.toList
      let blocks ←
        if effectiveClosure?.isNone && terminal then do
          pure (blocksRest ++ [← accumulatedAlignBlock data accOut input])
        else pure blocksRest
      return (accOut, blocks)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let (accRest, blocksRest) ←
        collectResidualBlocks data args[0]! closure? false accumulated input
      let some (ctor, index) ← binaryKeyParts args[1]!
        | return (accRest, blocksRest)
      let split? ← registeredDichotomy? data ctor index
      let (leftClosed, rightClosed) ← binaryRegisteredClosures data ctor index
      let leftClosure? := closure? <|> (if leftClosed then some "closed" else none)
      let rightClosure? := closure? <|> (if rightClosed then some "closed" else none)
      let sideWitness? (field : Name) : MetaM (Option Constraint) :=
        match split? with
        | some split => some <$> sideWitnessLatex split field input
        | none => pure none
      let leftWitness? ← sideWitness? ``Hypostructure.Core.DichotomyData.LeftPayload
      let rightWitness? ← sideWitness? ``Hypostructure.Core.DichotomyData.RightPayload
      let (_, blocksLeft) ← collectResidualBlocks data args[2]!
        leftClosure? terminal (accRest ++ leftWitness?.toList) input
      let (_, blocksRight) ← collectResidualBlocks data args[3]!
        rightClosure? terminal (accRest ++ rightWitness?.toList) input
      let joinConstraint? ← match split? with
        | some split =>
            some <$> dichotomyJoinConstraint split leftClosed rightClosed input
        | none => pure none
      let accOut := accRest ++ joinConstraint?.toList
      return (accOut, blocksRest ++ blocksLeft ++ blocksRight)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let (accRest, blocksRest) ←
        collectResidualBlocks data args[0]! closure? false accumulated input
      let (_, blocksExceptional) ←
        collectResidualBlocks data args[2]! closure? terminal accRest input
      let (_, blocksStructured) ←
        collectResidualBlocks data args[3]! closure? terminal accRest input
      let (_, blocksBounded) ←
        collectResidualBlocks data args[4]! closure? terminal accRest input
      pure (accRest, blocksRest ++ blocksExceptional ++ blocksStructured ++
        blocksBounded)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      -- `args[2]` is `CounterexampleContinuationMetadata`, not a blueprint, and
      -- the sealed vertices it names retain no residual of their own.
      let (accRest, blocksRest) ←
        collectResidualBlocks data args[0]! closure? terminal accumulated input
      return (accRest, blocksRest)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate => do
      collectResidualBlocks data (blueprintCtorArgs dag 2)[0]!
        closure? terminal accumulated input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled => do
      collectResidualBlocks data (blueprintCtorArgs dag 2)[0]!
        closure? terminal accumulated input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented => do
      collectResidualBlocks data (blueprintCtorArgs dag 2)[0]!
        closure? terminal accumulated input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute =>
      collectResidualBlocks data (blueprintCtorArgs dag 3)[0]!
        closure? false accumulated input
  | _ => return (accumulated, [])

/-- Assemble a certification-neutral LaTeX payload: registered statement,
evidence, closed branches, the reflected strategy tree, and residual text.
Only `Dag.lean`, after receiving a sealed `ProblemDeclaration`, may add the
kernel-certification banner and publish the resulting artifact. -/
private def runSummaryLatexDocument (runName statement evidence : String)
    (closedBranches : List String) (forest : String)
    (forestPanels : List String) (residualBlocks : List String) : String :=
  let esc (s : String) : String :=
    let s := s.replace "\\" ""
    let s := s.replace "_" "\\_"
    let s := s.replace "^" "\\textasciicircum{}"
    let s := s.replace "%" "\\%"
    let s := s.replace "&" "\\&"
    let s := s.replace "$" "\\$"
    let s := s.replace "#" "\\#"
    let s := s.replace "~" "\\textasciitilde{}"
    s.replace "" "\\textbackslash{}"
  let closedSection :=
    if closedBranches.isEmpty then
      "None registered."
    else
      "\\begin{itemize}\n" ++
        String.intercalate "\n"
          (closedBranches.map fun l => s!"\\item \\texttt\{{esc l}}") ++
        "\n\\end{itemize}"
  let verdictLine :=
    "\\textbf{Certification status omitted.} This is an internal structural payload, not a proof artifact."
  let residualSection :=
    if residualBlocks.isEmpty then
      ""
    else
      "\\section*{Pending residuals}\n" ++
        String.intercalate "\n\n" residualBlocks
  "\\documentclass[11pt]{article}\n" ++
  "\\usepackage[a4paper,margin=2cm]{geometry}\n" ++
  "\\usepackage{amsmath,amssymb}\n" ++
  "\\usepackage{breqn}\n" ++
  "\\usepackage{graphicx}\n" ++
  "\\usepackage{forest}\n" ++
  "\\usetikzlibrary{arrows.meta,positioning}\n" ++
  "\\tikzset{archnode/.style={draw, rounded corners, align=center, text width=3cm, minimum height=7mm}, decision/.style={draw, diamond, aspect=2.05, align=center, text width=3cm, inner sep=1pt}, terminal/.style={draw, rounded corners, align=center, text width=3cm, minimum height=7mm}, target/.style={draw, circle, align=center, text width=2.4cm, inner sep=2pt}}\n" ++
  "\\usepackage{fontspec}\n" ++
  "\\setmainfont{DejaVu Serif}\n" ++
  "\\setmonofont{DejaVu Sans Mono}[Scale=0.75]\n" ++
  "\\title{Hypostructure Run Summary}\n" ++
  s!"\\author\{{esc runName}}\n" ++
  "\\date{\\today}\n" ++
  "\\begin{document}\n" ++
  "\\maketitle\n" ++
  "\\section*{Registered statement}\n" ++
  s!"\\texttt\{{esc statement}}\n\n" ++
  verdictLine ++ "\n\n" ++
  s!"Evidence: {esc evidence}\n" ++
  "\\section*{Closed branches}\n" ++
  closedSection ++ "\n" ++
  "\\section*{Compiled strategy tree}\n" ++
  "\\begin{center}\n" ++
  "\\resizebox{\\linewidth}{0.68\\textheight}{%\n" ++
  "\\begin{forest}\n" ++
  "for tree={draw, rounded corners, align=center, edge={-Latex}, l sep=8mm, s sep=18mm, font=\\scriptsize, text width=3cm}\n" ++
  forest ++ "\n" ++
  "\\end{forest}}\n" ++
  "\\end{center}\n" ++
  (if forestPanels.length ≤ 1 then ""
   else String.intercalate "\n"
     (forestPanels.mapIdx fun index panel =>
       (if index % 2 == 0 then "\\clearpage\n"
        else "\\vspace{8mm}\n") ++
       "\\section*{Proof flow continuation --- panel " ++
       toString (index + 1) ++ " of " ++ toString forestPanels.length ++ "}\n" ++
       "\\begin{forest}\n" ++
       "for tree={draw, rounded corners, align=center, edge={-Latex}, l sep=8mm, s sep=18mm, font=\\scriptsize, text width=3cm}\n" ++
       panel ++ "\n\\end{forest}\n")) ++
  "\\clearpage\n" ++
  residualSection ++
  "\\end{document}\n"

/-- Whether the registered decision procedure of a `ProblemDefinition`
reduces to `isTrue` for an arbitrary input. -/
def deciderReduces (problemDefn : Expr) : TermElabM Bool := do
  let problemE ← mkAppM ``Hypostructure.Core.ProblemDefinition.problem #[problemDefn]
  let dataE ← mkAppM ``Hypostructure.Core.ProblemDefinition.data #[problemDefn]
  let inputType ← mkAppM ``Hypostructure.Core.Strategy.ProblemInput #[problemE]
  withLocalDeclD `input inputType fun input => do
    let decision ← whnf (mkApp
      (← mkAppM ``Hypostructure.Core.StrategyData.targetDecidable #[dataE]) input)
    return decision.getAppFn.constName? == some ``Decidable.isTrue

/-- Walk the whole blueprint once collecting every registered branch
closure, so the fact each closed branch certifies is displayed alongside
the pending residual — not just implied by its downstream propagation. -/
partial def collectClosedBranches (data dag : Expr) (input : Expr) :
    MetaM (List String) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      collectClosedBranches data args[0]! input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate => do
      collectClosedBranches data (blueprintCtorArgs dag 2)[0]! input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled => do
      collectClosedBranches data (blueprintCtorArgs dag 2)[0]! input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented => do
      collectClosedBranches data (blueprintCtorArgs dag 2)[0]! input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute =>
      collectClosedBranches data (blueprintCtorArgs dag 3)[0]! input
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let rest ← collectClosedBranches data args[0]! input
      let some (ctor, index) ← binaryKeyParts args[1]! | pure rest
      let split? ← registeredDichotomy? data ctor index
      let (leftClosed, rightClosed) ← binaryRegisteredClosures data ctor index
      let (leftLine, rightLine) ← match split? with
        | some split =>
            let leftLine ←
              if leftClosed then do
                let payload ← ppFamilyField
                  ``Hypostructure.Core.DichotomyData.LeftPayload split input
                pure [s!"  dichotomy #{index}, left branch: closed — the registered closure certifies the target whenever {payload}"]
              else pure []
            let rightLine ←
              if rightClosed then do
                let payload ← ppFamilyField
                  ``Hypostructure.Core.DichotomyData.RightPayload split input
                pure [s!"  dichotomy #{index}, right branch: closed — the registered closure certifies the target whenever {payload}"]
              else pure []
            pure (leftLine, rightLine)
        | none =>
            let label := ((keyInfo ctor (some index)).map Prod.fst).getD
              s!"binary strategy #{index}"
            pure (
              (if leftClosed then
                [s!"  {label}, left branch: closed — the registered branch closure is the direct closure Core installs on this family"]
              else []),
              (if rightClosed then
                [s!"  {label}, right branch: closed — the registered branch closure is the direct closure Core installs on this family"]
              else []))
      let leftInner ← collectClosedBranches data args[2]! input
      let rightInner ← collectClosedBranches data args[3]! input
      pure (rest ++ leftLine ++ rightLine ++ leftInner ++ rightInner)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let rest ← collectClosedBranches data args[0]! input
      let some index ← evalFinLiteral args[1]! | pure rest
      let exceptional ← collectClosedBranches data args[2]! input
      let structured ← collectClosedBranches data args[3]! input
      let bounded ← collectClosedBranches data args[4]! input
      let exceptionalLine ←
        if ← homogeneousExceptionalClosed data index then
          pure [s!"  homogeneous bottleneck #{index}, exceptional branch: \
            closed — the registered exceptional schedule is uninhabited, so \
            CT1 can never select this output"]
        else pure []
      pure (rest ++
        [s!"  homogeneous bottleneck #{index}, target branch: \
          closed by the retained target proof"] ++
        exceptionalLine ++ exceptional ++ structured ++ bounded)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      let rest ← collectClosedBranches data args[0]! input
      let some index ← evalFinLiteral args[1]! | pure rest
      -- `args[2]` is `CounterexampleContinuationMetadata`, not a blueprint.
      pure (rest ++
        [s!"  minimal-counterexample selection #{index}, target branch: \
          closed by the framework target decision"])
  | _ => pure []

/-- Assemble the internal executive summary used by the rejecting frontend. -/
private def executiveSummary (runName statement evidence : String)
    (closedBranches dagLines : List String) : String :=
  let header := s!"════════ Hypostructure run summary: {runName} ════════"
  let registered := s!"Registered statement:\n  {statement}"
  let closedSection :=
    if closedBranches.isEmpty then
      "Closed branches: none registered.\n"
    else
      "Closed branches (constraints imposed alongside the pending residuals):\n" ++
        String.intercalate "\n" closedBranches ++ "\n"
  let verdict :=
    s!"Target verified: FALSE\n\
      Evidence: {evidence}\n\
      Pending residuals — the open leaves below carry the residual union:"
  header ++ "\n" ++ registered ++ "\n" ++ closedSection ++ verdict ++ "\n" ++
  String.intercalate "\n" dagLines

/-- Everything a run's report is derived from — computed once, against one
shared generic input, and consumed identically by the terminal summary and
the PDF renderer, so the two views can never diverge. -/
structure RunSummaryData where
  statement : String
  evidence : String
  closedBranches : List String
  dagLines : List String
  forest : String
  forestPanels : List String
  residualBlocks : List String

/-- Compute every projection of one run's report.  `none` when the
blueprint or its registered data is not a closed literal. -/
private def computeRunSummaryData (verified : Bool) (problemE dagE : Expr) :
    TermElabM (Option RunSummaryData) := do
  let targetE ← mkAppM ``Hypostructure.Core.ProblemDefinition.target #[problemE]
  let statementE ← whnf (← mkAppM ``Hypostructure.Core.Target.Statement #[targetE])
  let statement := toString (← ppExpr statementE)
  let dataE ← mkAppM ``Hypostructure.Core.ProblemDefinition.data #[problemE]
  let reduces ← deciderReduces problemE
  let evidence :=
    if reduces then
      "the registered decision procedure reduces to `isTrue` for an arbitrary input."
    else
      "the registered decision procedure does not reduce to `isTrue` for an arbitrary input."
  let rootClosure? := if verified then some "certified closure" else none
  let inputType ← mkAppM ``Hypostructure.Core.Strategy.ProblemInput
    #[← mkAppM ``Hypostructure.Core.ProblemDefinition.problem #[problemE]]
  withLocalDeclD `x inputType fun input => do
    let closedBranches ← collectClosedBranches dataE dagE input
    match ← blueprintLines dataE dagE "  " rootClosure? true [] input 0 with
    | some (dagLines, _, _) =>
        let forest ← blueprintForest dataE dagE input
        let (_, residualBlocks) ←
          collectResidualBlocks dataE dagE rootClosure? true [] input
        return some
          { statement, evidence, closedBranches, dagLines, forest,
            forestPanels := blueprintForestPanels dagLines,
            residualBlocks }
    | none => return none

/-- Emit only a failed-declaration diagnostic.  This function has no
certified mode and cannot construct or serialize a proof artifact. -/
def emitRejectedRunSummary (runName : String)
    (problemE dagE : Expr) : TermElabM Unit := do
  match ← computeRunSummaryData false problemE dagE with
  | some data =>
      logInfo (executiveSummary runName data.statement data.evidence
        data.closedBranches data.dagLines)
  | none =>
      logInfo s!"hypostructure summary for {runName}: unavailable (the blueprint or its registered data is not a closed literal)."

/-- Reflect a certification-neutral LaTeX payload.  The public result never
claims target closure; the sealed artifact command in `Dag.lean` adds that
claim only after it has type-checked a `ProblemDeclaration`. -/
def buildRunSummaryLatexPayload (runName : String)
    (problemE dagE : Expr) (certified : Bool := true) :
    TermElabM (Option String) := do
  match ← computeRunSummaryData certified problemE dagE with
  | some data =>
      return some (runSummaryLatexDocument runName data.statement
        data.evidence data.closedBranches data.forest
        data.forestPanels data.residualBlocks)
    | none => return none

private def optionalJson (value : Option String) : Json :=
  value.map Json.str |>.getD .null

private def stringArray (values : List String) : Json :=
  .arr (values.map Json.str).toArray

private structure ExportDocumentation where
  label : Option String := none
  note : Option String := none
  tags : List String := []

private def exportDocumentation (value : Expr) :
    MetaM ExportDocumentation := do
  let label ← evalStrLiteral
    (← mkAppM ``Hypostructure.Core.Documentation.name #[value])
  let note ← evalStrLiteral
    (← mkAppM ``Hypostructure.Core.Documentation.note #[value])
  let tags ← evalStringList
    (← mkAppM ``Hypostructure.Core.Documentation.tags #[value])
  return {
    label := nonemptyString label
    note := nonemptyString note
    tags
  }

private def ExportDocumentation.toJson (value : ExportDocumentation) : Json :=
  .mkObj [
    ("label", optionalJson value.label),
    ("note", optionalJson value.note),
    ("tags", stringArray value.tags)
  ]

private partial def exportDocumentationList (values : Expr) :
    MetaM (List ExportDocumentation) := do
  let values ← whnf values
  match values.getAppFn.constName? with
  | some ``List.nil => return []
  | some ``List.cons =>
      let args := values.getAppArgs
      return (← exportDocumentation args[1]!) ::
        (← exportDocumentationList args[2]!)
  | _ => return []

private def renderMetadataJson (value : RenderMetadata) : Json :=
  .mkObj [
    ("label", optionalJson value.name),
    ("note", optionalJson value.note)
  ]

private def strategyKind (ctor : Name) : Option String :=
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.orderedWitnessScan then
    some "ordered_witness_scan"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.responseClassifier then
    some "response_classifier"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.capacityLedger then
    some "capacity_ledger"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.orderedSurplusActivation then
    some "ordered_surplus_activation"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.baselineDemandAccounting then
    some "baseline_demand_accounting"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.canonicalPairResponseAccounting then
    some "canonical_pair_response_accounting"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.canonicalCapacityTokenAccounting then
    some "canonical_capacity_token_accounting"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.coupledHomogeneousFibrePressure then
    some "coupled_homogeneous_fibre_pressure"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteBottleneckClassification then
    some "finite_bottleneck_classification"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.homogeneousBottleneck then
    some "homogeneous_bottleneck"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.supportComplementNormalization then
    some "support_complement_normalization"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.boundaryDemandAccounting then
    some "boundary_demand_accounting"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.localSupplyLowerBound then
    some "local_supply_lower_bound"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.targetRelativeRankDichotomy then
    some "target_relative_rank_dichotomy"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.compressionLinkedTargetRelativeRankDichotomy then
    some "compression_linked_target_relative_rank_dichotomy"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateCapacity then
    some "finite_state_capacity"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteScheduleCapacity then
    some "finite_schedule_capacity"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.route8CarrierClosure then
    some "route8_carrier_closure"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateNetChargeContinuation then
    some "finite_state_net_charge_continuation"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.supportLocalization then
    some "support_localization"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.rankBudget then
    some "rank_budget"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.closedCode then
    some "closed_code"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
    some "dichotomy"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.obstructionPackingClosure then
    some "obstruction_packing_closure"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.exactFiniteLocalAlgebra then
    some "exact_finite_local_algebra"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteBarrierEnumeration then
    some "finite_barrier_enumeration"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteDensityBudget then
    some "finite_density_budget"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.scaleThresholdDichotomy then
    some "scale_threshold_dichotomy"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.atomContextObstructionDichotomy then
    some "atom_context_obstruction_dichotomy"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.counterexampleLocalization then
    some "counterexample_localization"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.coldBranchAggregation then
    some "cold_branch_aggregation"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.minimalCounterexampleSelection then
    some "minimal_counterexample_selection"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.targetAlgebraReduction then
    some "target_algebra_reduction"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.minimalSubobjectExclusion then
    some "minimal_subobject_exclusion"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.criticalModificationStructure then
    some "critical_modification_structure"
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.interfaceReplacementClosure then
    some "interface_replacement_closure"
  else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid then
    some "target_or_avoid"
  else
    none

private def familyExpression (data : Expr) (ctor : Name) (index : Nat) :
    MetaM (Option Expr) := do
  let some (_, _, fieldName) :=
      indexedKeys.find? (fun entry => entry.1 == ctor) | return none
  listNth (← mkAppM fieldName #[data]) index

private def registrationDocumentation (data : Expr) (ctor : Name)
    (index? : Option Nat) : MetaM ExportDocumentation := do
  let some index := index? | return {}
  let some family ← familyExpression data ctor index | return {}
  let metadataField? :=
    if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.orderedWitnessScan then
      some ``Hypostructure.Core.ScanData.metadata
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.responseClassifier then
      some ``Hypostructure.Core.ResponseData.metadata
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.capacityLedger then
      some ``Hypostructure.Core.CapacityData.metadata
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.supportLocalization then
      some ``Hypostructure.Core.LocalizationData.metadata
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.rankBudget then
      some ``Hypostructure.Core.RankBudgetData.metadata
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.closedCode then
      some ``Hypostructure.Core.ClosedCodeData.metadata
    else if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
      some ``Hypostructure.Core.DichotomyData.metadata
    else none
  let some metadataField := metadataField? | return {}
  exportDocumentation (← mkAppM metadataField #[family])

private def registrationComponents (data : Expr) (ctor : Name)
    (index? : Option Nat) : MetaM (List ExportDocumentation) := do
  let some index := index? | return []
  let some family ← familyExpression data ctor index | return []
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
    exportDocumentationList
      (← mkAppM ``Hypostructure.Core.DichotomyData.components #[family])
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateCapacity then
    return [
      { label := some "CT17"
        note := some "Exact finite-state realization over the residual-owned schedules."
        tags := ["state-realization", "ledger-extension"] },
      { label := some "CT14"
        note := some "Exact labelled capacity aggregation over CT17's survivor enumeration."
        tags := ["capacity-aggregation", "dependent-composition"] }
    ]
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.route8CarrierClosure then
    return [
      { label := some "CT5"
        note := some "Exact carrier-supply aggregation over the route-8 entries."
        tags := ["resource-aggregation", "ledger-extension"] },
      { label := some "CT14"
        note := some "Exact private-carrier census over the CT5 outcome."
        tags := ["capacity-aggregation", "dependent-composition"] },
      { label := some "CT12"
        note := some "Well-founded exit-(4) pressure descent over the census."
        tags := ["peeling", "well-founded-descent"] }
    ]
  else if ctor ==
      `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteScheduleCapacity then
    return [
      { label := some "CT6"
        note := some "Exact residual-owned ordered failure scan."
        tags := ["ordered-scan", "ledger-extension"] },
      { label := some "CT5"
        note := some "Exact contribution aggregation over the CT6 outcome."
        tags := ["resource-aggregation", "dependent-composition"] },
      { label := some "CT14"
        note := some "Exact finite capacity comparison over the derived schedule."
        tags := ["capacity-aggregation", "dependent-composition"] }
    ]
  else
    return []

private def strategyJson (ctor : Name) (index? : Option Nat) : Json :=
  let kind := (strategyKind ctor).getD "unknown"
  .mkObj [
    ("kind", .str kind),
    ("index", index?.map Json.num |>.getD .null),
    ("registration_id", index?.map (fun index =>
      .str (kind ++ ":" ++ toString index)) |>.getD .null)
  ]

private structure ExportGraph where
  entry : Option String := none
  exits : List String := []
  nodes : List Json := []
  edges : List Json := []
  terminals : List Json := []
  nextNode : Nat := 0
  nextEdge : Nat := 0
  nextTerminal : Nat := 0

private def appendExportEdge (graph : ExportGraph) (kind source target : String)
    (output : Option String := none) (label : Option String := none)
    (note : Option String := none) (status : String := "active") : ExportGraph :=
  let edge := Json.mkObj [
    ("id", .str ("e" ++ toString graph.nextEdge)),
    ("internal_id", .num graph.nextEdge),
    ("kind", .str kind),
    ("source", .str source),
    ("target", .str target),
    ("output", optionalJson output),
    ("presentation", .mkObj [
      ("label", optionalJson label),
      ("note", optionalJson note)
    ]),
    ("status", .str status)
  ]
  { graph with
    edges := graph.edges ++ [edge]
    nextEdge := graph.nextEdge + 1 }

private def appendResolvedRouteEdge (graph : ExportGraph)
    (route : ResolvedRouteView) : ExportGraph :=
  let graph := appendExportEdge graph "autoroute"
    ("v" ++ toString route.sourceId)
    ("v" ++ toString route.destinationId)
    (label := nonemptyString route.name)
    (note := nonemptyString route.note)
  { graph with exits := [] }

private def connectExportFrontier (graph : ExportGraph) (target : String) :
    ExportGraph :=
  graph.exits.foldl
    (fun graph source => appendExportEdge graph "sequence" source target) graph

private def appendExportTerminal (graph : ExportGraph) (source kind reason : String)
    (certified : Bool) (output : Option String := none)
    (label : Option String := none) (note : Option String := none)
    (registeredClosed : Bool := false) : ExportGraph × String :=
  let terminalId := "t" ++ toString graph.nextTerminal
  let closed := certified || registeredClosed
  let status := if closed then "closed" else "open"
  let terminal := Json.mkObj [
    ("id", .str terminalId),
    ("internal_id", .num graph.nextTerminal),
    ("kind", .str kind),
    ("status", .str status),
    ("reason", .str reason),
    ("residual", .mkObj [
      ("kind", .str (if closed then "none" else "accumulated_strategy_residual")),
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
  let graph :=
    if source.isEmpty then graph
    else appendExportEdge graph (if output.isSome then "output" else "terminal")
      source terminalId output label note status
  (graph, terminalId)

private def keyParts (key : Expr) : MetaM (Option (Name × Option Nat)) := do
  let key ← strategyKeyOfRef key
  let some ctor := key.getAppFn.constName? | return none
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.targetOrAvoid then
    return some (ctor, none)
  let some index ← evalNatLiteral key.getAppArgs[0]! | return none
  return some (ctor, some index)

private def resolvedLabel (authored : RenderMetadata)
    (registered : ExportDocumentation) (kind : String) (index? : Option Nat) :
    String :=
  authored.name.getD <| registered.label.getD <|
    match index? with
    | some index => kind ++ " #" ++ toString index
    | none => kind

private def nodeJson (data : Expr) (id : Nat) (ctor : Name)
    (index? : Option Nat) (authored : RenderMetadata) : MetaM Json := do
  let registered ← registrationDocumentation data ctor index?
  let components ← registrationComponents data ctor index?
  let kind := (strategyKind ctor).getD "unknown"
  let resolvedNote := authored.note <|> registered.note
  return .mkObj [
    ("id", .str ("v" ++ toString id)),
    ("internal_id", .num id),
    ("kind", .str
      (if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy ||
          ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.scaleThresholdDichotomy ||
          ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.atomContextObstructionDichotomy ||
          ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.targetRelativeRankDichotomy ||
          ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.compressionLinkedTargetRelativeRankDichotomy ||
          ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteDensityBudget
          || ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateCapacity
          || ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.route8CarrierClosure
          || ctor ==
            `Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateNetChargeContinuation
        then "decision" else "operation")),
    ("strategy", strategyJson ctor index?),
    ("presentation", .mkObj [
      ("authored", renderMetadataJson authored),
      ("registered", registered.toJson),
      ("resolved", .mkObj [
        ("label", .str (resolvedLabel authored registered kind index?)),
        ("note", optionalJson resolvedNote)
      ])
    ]),
    ("components", .arr (components.map (·.toJson)).toArray),
    ("status", .str "active")
  ]

private def binaryOutputDocumentation (data : Expr) (ctor : Name)
    (index : Nat) (left : Bool) : MetaM (ExportDocumentation × Bool) := do
  let some registered ← familyExpression data ctor index
    | return ({}, false)
  if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy then
    let metadataField :=
      if left then ``Hypostructure.Core.DichotomyData.leftMetadata
      else ``Hypostructure.Core.DichotomyData.rightMetadata
    let closeField :=
      if left then ``Hypostructure.Core.DichotomyData.closeLeft
      else ``Hypostructure.Core.DichotomyData.closeRight
    return (← exportDocumentation (← mkAppM metadataField #[registered]),
      ← optionIsSome (← mkAppM closeField #[registered]))
  else
    let (leftClosed, rightClosed) ← binaryRegisteredClosures data ctor index
    return ({}, if left then leftClosed else rightClosed)

private partial def buildExportGraph (data dag : Expr) (certified : Bool)
    (seed : ExportGraph := {}) : MetaM (Option ExportGraph) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root => return some seed
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let (rest, authored) ← peelMetadata args[0]!
      let id := seed.nextNode
      let seed := { seed with nextNode := id + 1 }
      let some graph ← buildExportGraph data rest certified seed | return none
      let some (ctor, index?) ← keyParts args[1]! | return none
      let nodeId := "v" ++ toString id
      let graph := connectExportFrontier graph nodeId
      let node ← nodeJson data id ctor index? authored
      return some { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [node] }
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let (rest, authored) ← peelMetadata args[0]!
      let some (ctor, index) ← binaryKeyParts args[1]! | return none
      let id := seed.nextNode
      let seed := { seed with nextNode := id + 1 }
      let some graph ← buildExportGraph data rest certified seed | return none
      let nodeId := "v" ++ toString id
      let graph := connectExportFrontier graph nodeId
      let node ← nodeJson data id ctor (some index) authored
      let graph := { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [node] }
      let (defaultLeftName, defaultRightName) := binaryDefaultNames ctor
      let addSide (graph : ExportGraph) (side : Expr) (left : Bool) :
          MetaM (Option (ExportGraph × List String)) := do
        let (registered, registeredClosed) ←
          binaryOutputDocumentation data ctor index left
        let authoredLabel := if left then authored.leftName else authored.rightName
        let authoredNote := if left then authored.leftNote else authored.rightNote
        let defaultLabel := if left then defaultLeftName else defaultRightName
        let label := authoredLabel <|> registered.label <|> some defaultLabel
        let note := authoredNote <|> registered.note
        let output := defaultLabel
        let side ← whnf side
        if side.getAppFn.constName? ==
            some `Hypostructure.Core.Strategy.Dag.Blueprint.root then
          let reason :=
            if registeredClosed then "registered branch closure"
            else if certified then "kernel-certified target"
            else "empty continuation"
          let (graph, terminalId) := appendExportTerminal graph nodeId
            "branch_endpoint" reason certified (some output) label note registeredClosed
          return some (graph, [terminalId])
        let branchSeed : ExportGraph :=
          { graph with entry := none, exits := [] }
        let some branch ← buildExportGraph data side certified branchSeed | return none
        let graph := { branch with entry := graph.entry }
        let graph := match branch.entry with
          | some target => appendExportEdge graph "output" nodeId target
              (some output) label note
              (if registeredClosed then "closed" else "conditional")
          | none => graph
        return some (graph, branch.exits)
      let some (graph, leftExits) ← addSide graph args[2]! true | return none
      let some (graph, rightExits) ← addSide graph args[3]! false | return none
      return some { graph with exits := leftExits ++ rightExits }
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let (rest, authored) ← peelMetadata args[0]!
      let some index ← evalFinLiteral args[1]! | return none
      let id := seed.nextNode
      let seed := { seed with nextNode := id + 1 }
      let some graph ← buildExportGraph data rest certified seed | return none
      let nodeId := "v" ++ toString id
      let graph := connectExportFrontier graph nodeId
      let node ← nodeJson data id
        `Hypostructure.Core.Strategy.Dag.StrategyKey.homogeneousBottleneck
        (some index) authored
      let graph := { graph with
        entry := graph.entry <|> some nodeId
        exits := [nodeId]
        nodes := graph.nodes ++ [node] }
      let (graph, _) := appendExportTerminal graph nodeId
        "target" "homogeneous-bottleneck target output" true
        (output := some "target") (label := some "target")
        (registeredClosed := true)
      let exceptionalClosed ← homogeneousExceptionalClosed data index
      let addLiveOutput (graph : ExportGraph) (side : Expr)
          (output : String) :
          MetaM (Option (ExportGraph × List String)) := do
        let registeredClosed := exceptionalClosed && output == "exceptional"
        let side ← whnf side
        if side.getAppFn.constName? ==
            some `Hypostructure.Core.Strategy.Dag.Blueprint.root then
          let reason :=
            if registeredClosed then "registered branch closure"
            else "retained homogeneous-bottleneck residual"
          let (graph, terminalId) := appendExportTerminal graph nodeId
            "branch_endpoint" reason certified (some output) (some output)
            none registeredClosed
          return some (graph, [terminalId])
        let branchSeed : ExportGraph :=
          { graph with entry := none, exits := [] }
        let some branch ←
          buildExportGraph data side certified branchSeed | return none
        let graph := { branch with entry := graph.entry }
        let graph := match branch.entry with
          | some target =>
              appendExportEdge graph "output" nodeId target
                (some output) (some output) none
                (if registeredClosed then "closed" else "conditional")
          | none => graph
        return some (graph, branch.exits)
      let some (graph, exceptionalExits) ←
        addLiveOutput graph args[2]! "exceptional" | return none
      let some (graph, structuredExits) ←
        addLiveOutput graph args[3]! "structured" | return none
      let some (graph, boundedExits) ←
        addLiveOutput graph args[4]! "bounded" | return none
      return some { graph with
        exits := exceptionalExits ++ structuredExits ++ boundedExits }
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      let (rest, authored) ← peelMetadata args[0]!
      let some index ← evalFinLiteral args[1]! | return none
      let id := seed.nextNode
      let seed := { seed with nextNode := id + 5 }
      let some graph ← buildExportGraph data rest certified seed | return none
      let selectionId := "v" ++ toString id
      let graph := connectExportFrontier graph selectionId
      let selection ← nodeJson data id
        `Hypostructure.Core.Strategy.Dag.StrategyKey.minimalCounterexampleSelection
        (some index) authored
      let graph := { graph with
        entry := graph.entry <|> some selectionId
        exits := [selectionId]
        nodes := graph.nodes ++ [selection] }
      let (graph, _) := appendExportTerminal graph selectionId
        "target" "minimal-counterexample target arm" certified
        (output := some "target") (registeredClosed := true)
      let metadata := args[2]!
      let stages : List (Name × Name) := [
        (`Hypostructure.Core.Strategy.Dag.StrategyKey.targetAlgebraReduction,
          `Hypostructure.Core.Strategy.Dag.CounterexampleContinuationMetadata.targetMetadata),
        (`Hypostructure.Core.Strategy.Dag.StrategyKey.minimalSubobjectExclusion,
          `Hypostructure.Core.Strategy.Dag.CounterexampleContinuationMetadata.minimalMetadata),
        (`Hypostructure.Core.Strategy.Dag.StrategyKey.criticalModificationStructure,
          `Hypostructure.Core.Strategy.Dag.CounterexampleContinuationMetadata.criticalMetadata),
        (`Hypostructure.Core.Strategy.Dag.StrategyKey.interfaceReplacementClosure,
          `Hypostructure.Core.Strategy.Dag.CounterexampleContinuationMetadata.interfaceReplacementClosureMetadata)
      ]
      let mut graph := graph
      for ((ctor, metadataField), offset) in stages.zip (List.range 4) do
        let stageId := id + offset + 1
        let authored ← evalDocumentedMetadata (← mkAppM metadataField #[metadata])
        let node ← nodeJson data stageId ctor (some index) authored
        let nodeId := "v" ++ toString stageId
        graph := connectExportFrontier graph nodeId
        graph := { graph with
          exits := [nodeId]
          nodes := graph.nodes ++ [node] }
      return some graph
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate =>
      buildExportGraph data (blueprintCtorArgs dag 2)[0]! certified seed
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled =>
      buildExportGraph data (blueprintCtorArgs dag 2)[0]! certified seed
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      buildExportGraph data (blueprintCtorArgs dag 2)[0]! certified seed
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute => do
      let args := blueprintCtorArgs dag 3
      let some graph ← buildExportGraph data args[0]! certified seed | return none
      let some route ← evalResolvedRoute args[1]! args[2]! | return none
      return some (appendResolvedRouteEdge graph route)
  | _ => return none

private def finalizeExportGraph (graph : ExportGraph) (certified : Bool) :
    ExportGraph :=
  if graph.exits.isEmpty then
    let (graph, terminalId) := appendExportTerminal graph "" "proof_terminal"
      "empty proof DAG" certified
    { graph with entry := graph.entry <|> some terminalId, exits := [terminalId] }
  else
    graph.exits.foldl (fun graph source =>
      if source.startsWith "t" then graph
      else
        (appendExportTerminal graph source "proof_terminal"
          (if certified then "kernel-certified target"
          else "target-or-residual terminal") certified).1) graph

private def interfaceJson (fields : List String) : Json :=
  .arr (fields.map (fun field => .mkObj [
    ("name", .str field),
    ("role", .str "contract_field")
  ])).toArray

private def registrationJson (data : Expr) (ctor : Name) (kind : String)
    (index : Nat) (fields : List String) : MetaM (Option Json) := do
  let some family ← familyExpression data ctor index | return none
  let presentation ← registrationDocumentation data ctor (some index)
  let components ← registrationComponents data ctor (some index)
  let outputs ←
    if ctor == `Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy ||
        ctor ==
          `Hypostructure.Core.Strategy.Dag.StrategyKey.scaleThresholdDichotomy ||
        ctor ==
          `Hypostructure.Core.Strategy.Dag.StrategyKey.atomContextObstructionDichotomy ||
        ctor ==
          `Hypostructure.Core.Strategy.Dag.StrategyKey.compressionLinkedTargetRelativeRankDichotomy
    then do
      let (left, leftClosed) ←
        binaryOutputDocumentation data ctor index true
      let (right, rightClosed) ←
        binaryOutputDocumentation data ctor index false
      let (leftPort, rightPort) := binaryDefaultNames ctor
      pure <| Json.arr #[
        .mkObj [("port", .str leftPort), ("presentation", left.toJson),
          ("closed", .bool leftClosed)],
        .mkObj [("port", .str rightPort), ("presentation", right.toJson),
          ("closed", .bool rightClosed)]
      ]
    else pure <| Json.arr #[]
  return some <| .mkObj [
    ("id", .str (kind ++ ":" ++ toString index)),
    ("kind", .str kind),
    ("index", .num index),
    ("presentation", presentation.toJson),
    ("components", .arr (components.map (·.toJson)).toArray),
    ("interface", interfaceJson fields),
    ("outputs", outputs)
  ]

/-- Singleton strategy fields are registered directly rather than through a
list family.  They still receive the same stable `kind:0` identity used by
the normalized DAG, and binary singleton outputs report the closure carried
by the literal registration. -/
private def singletonRegistrationJson (kind : String) (fields : List String)
    (outputs : List (String × Bool) := []) : Json :=
  .mkObj [
    ("id", .str (kind ++ ":0")),
    ("kind", .str kind),
    ("index", .num 0),
    ("presentation", ExportDocumentation.toJson {}),
    ("components", .arr #[]),
    ("interface", interfaceJson fields),
    ("outputs", .arr <| (outputs.map fun (port, closed) => .mkObj [
      ("port", .str port),
      ("presentation", ExportDocumentation.toJson {}),
      ("closed", .bool closed)
    ]).toArray)
  ]

private def registrationsJson (data : Expr) : MetaM Json := do
  let specs : List (Name × String × Name × List String) := [
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.orderedWitnessScan,
      "ordered_witness_scan", ``Hypostructure.Core.StrategyData.scans,
      ["Item", "schedule", "witness", "witnessDecidable"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.responseClassifier,
      "response_classifier", ``Hypostructure.Core.StrategyData.responses,
      ["Item", "Response", "Class", "schedule", "observe", "classify"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.capacityLedger,
      "capacity_ledger", ``Hypostructure.Core.StrategyData.capacities,
      ["Item", "Class", "schedule", "classify", "contribution", "capacity",
        "totalWithin"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.supportLocalization,
      "support_localization", ``Hypostructure.Core.StrategyData.localizations,
      ["Cell", "schedule", "localBudget", "selected", "selected_negative"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.rankBudget,
      "rank_budget", ``Hypostructure.Core.StrategyData.rankBudgets,
      ["rank", "budget", "threshold", "high", "low", "exhaustive"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.closedCode,
      "closed_code", ``Hypostructure.Core.StrategyData.closedCodes,
      ["Code", "schedule", "targetCode", "observedCode", "closed"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.dichotomy,
      "dichotomy", ``Hypostructure.Core.StrategyData.dichotomies,
      ["LeftPayload", "RightPayload", "classify", "closeLeft", "closeRight"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.counterexampleLocalization,
      "counterexample_localization",
      ``Hypostructure.Core.StrategyData.counterexampleLocalizations,
      ["selection"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.minimalCounterexampleSelection,
      "minimal_counterexample_selection",
      ``Hypostructure.Core.StrategyData.counterexampleReductions,
      ["progress", "targetDecidable", "initialState"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.targetAlgebraReduction,
      "target_algebra_reduction",
      ``Hypostructure.Core.StrategyData.counterexampleReductions,
      ["targetAlgebra"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.minimalSubobjectExclusion,
      "minimal_subobject_exclusion",
      ``Hypostructure.Core.StrategyData.counterexampleReductions,
      ["minimality"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.criticalModificationStructure,
      "critical_modification_structure",
      ``Hypostructure.Core.StrategyData.counterexampleReductions,
      ["criticalModification"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.interfaceReplacementClosure,
      "interface_replacement_closure",
      ``Hypostructure.Core.StrategyData.counterexampleReductions,
      ["interfaceReplacement"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.obstructionPackingClosure,
      "obstruction_packing_closure",
      ``Hypostructure.Core.StrategyData.obstructionPackingClosures,
      ["obstruction", "conflict", "maximalSelection"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.exactFiniteLocalAlgebra,
      "exact_finite_local_algebra",
      ``Hypostructure.Core.StrategyData.exactFiniteLocalAlgebras,
      ["carrier", "relation", "finiteExhaustion"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteBarrierEnumeration,
      "finite_barrier_enumeration",
      ``Hypostructure.Core.StrategyData.finiteBarrierEnumerations,
      ["Candidate", "candidates", "accepted", "labelCount", "profile",
        "leftLength", "rightLength"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteDensityBudget,
      "finite_density_budget",
      ``Hypostructure.Core.StrategyData.finiteDensityBudgets,
      ["ambientCapacity"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.orderedSurplusActivation,
      "ordered_surplus_activation",
      ``Hypostructure.Core.StrategyData.orderedSurplusActivations,
      ["Index", "FailureData", "order", "Failure", "failureData",
        "failureDecidable", "contribution", "accounting"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.baselineDemandAccounting,
      "baseline_demand_accounting",
      ``Hypostructure.Core.StrategyData.baselineDemandAccountings,
      ["budget", "Site", "Witness", "family", "Active", "Supports",
        "contribution", "required", "capacity", "activeDecidable",
        "supportsDecidable", "resourceLEDecidable"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.canonicalPairResponseAccounting,
      "canonical_pair_response_accounting",
      ``Hypostructure.Core.StrategyData.canonicalPairResponseAccountings,
      ["Pair", "pairSchedule", "Dependent", "dependentDecidable",
        "pairCharge", "pairCapacity", "BlockerKind",
        "completeBlockerKinds", "roleOf", "roleCapacity"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.canonicalCapacityTokenAccounting,
      "canonical_capacity_token_accounting",
      ``Hypostructure.Core.StrategyData.canonicalCapacityTokenAccountings,
      ["Demand", "Token", "Role", "Label", "demands", "tokens",
        "completeLabels", "Eligible", "eligibleDecidable", "demandWeight",
        "tokenCapacity", "required", "roleOf", "labelOf", "labelCapacity",
        "aggregateLabel", "aggregateLabelDecidableEq",
        "memberAggregateLabel"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.coupledHomogeneousFibrePressure,
      "coupled_homogeneous_fibre_pressure",
      ``Hypostructure.Core.StrategyData.coupledHomogeneousFibrePressures,
      ["Item", "Token", "Role", "Label", "items", "completeLabels",
        "labelOf", "fibreCapacity", "Payer", "Obstruction", "Resource",
        "payers", "obstructions", "tierTwo", "Eligible",
        "obstructionCost", "payerResource", "charge", "demand",
        "eligibleDecidable", "resourceDecidableEq", "Member",
        "AggregateLabel", "members", "memberLowerMass", "memberCapacity",
        "memberLabel", "aggregateLabelDecidableEq"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteBottleneckClassification,
      "finite_bottleneck_classification",
      ``Hypostructure.Core.StrategyData.finiteBottleneckClassifications,
      ["PatternItem", "CoarseCode", "patternItems", "completeCoarseCodes",
        "coarseCodeOf", "PressureLabel", "pressureCapacity",
        "pressureLabel", "pressureLabelDecidableEq", "Datum",
        "SemanticTag", "Promotion", "data", "completeSemanticTags",
        "classOf", "Direct", "promote", "directDecidable",
        "SeparatorIndex", "SeparatorData", "separatorOrder",
        "SeparatorFailure", "separatorFailureData",
        "separatorFailureDecidable", "separatorContribution"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.homogeneousBottleneck,
      "homogeneous_bottleneck",
      ``Hypostructure.Core.StrategyData.homogeneousBottlenecks,
      ["Item", "HomogeneityCode", "items", "completeHomogeneityCodes",
        "homogeneityCodeOf", "homogeneityCapacity", "CapacityLabel",
        "codeCapacity", "codeLabel", "codeLabelDecidableEq", "Datum",
        "LocalClass", "Promotion", "data", "completeLocalClasses", "classOf",
        "Direct", "promote", "directDecidable", "LocalIndex",
        "LocalFailureData", "localOrder", "LocalFailure", "localFailureData",
        "localFailureDecidable", "localContribution", "Representative",
        "responseSystem", "targetSemantics", "ResponseCandidate",
        "ResponseRow", "candidatePiece", "rowPiece", "rowResponse",
        "responseSource", "responseCoordinates", "responseCandidates",
        "responseRows", "ResponseAdmissible", "ResponseStrictlySmaller",
        "responseValueDecEq", "responseAdmissibleDecidable",
        "responseSmallerDecidable", "responseCandidateCoverage",
        "responseRowCoverage", "AdmissibilityField",
        "AdmissibilityFailureData", "admissibilityOrder",
        "AdmissibilityFailure", "admissibilityFailureData",
        "admissibilityFailureDecidable", "admissibilityContribution",
        "TargetCandidate", "ExceptionalCandidate", "outcomeCandidates",
        "RealizesTarget", "RealizesException", "targetRealizationDecidable",
        "exceptionRealizationDecidable", "targetOfRealization",
        "supportBudget", "SupportSite", "SupportWitness", "supportFamily",
        "SupportActive", "SupportRelation", "supportContribution",
        "supportRequired", "supportCapacity", "supportActiveDecidable",
        "supportRelationDecidable", "supportResourceLEDecidable",
        "BoundedMember", "BoundedLabel", "boundedMembers",
        "boundedLowerMass", "boundedCapacity", "boundedLabel",
        "boundedLabelDecidableEq", "localFailureScheduled",
        "responseDefectScheduled", "admissibilityFailureScheduled",
        "supportDeficitScheduled", "supportCapacityFailureScheduled",
        "boundedCapacityTotal", "boundedLabelTotal"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.scaleThresholdDichotomy,
      "scale_threshold_dichotomy",
      ``Hypostructure.Core.StrategyData.scaleThresholdDichotomies,
      ["table", "size", "load"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.supportComplementNormalization,
      "support_complement_normalization",
      ``Hypostructure.Core.StrategyData.supportComplementNormalizations,
      ["AmbientItem", "ambientSupport", "SelectedPacking", "selectedPacking",
        "Selected", "selectedDecidable", "DensityCap", "densityCap",
        "lowerMass", "Obstruction", "obstructions",
        "SupportedByComplement", "supportedDecidable", "Realizes",
        "realizesDecidable", "LocalPiece", "localPieces", "FailureData",
        "Failure", "failureData", "failureDecidable", "contribution"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.boundaryDemandAccounting,
      "boundary_demand_accounting",
      ``Hypostructure.Core.StrategyData.boundaryDemandAccountings,
      ["Demand", "Payer", "demands", "payers", "Eligible",
        "eligibleDecidable", "demandWeight", "payerCapacity", "Member",
        "Label", "members", "memberLowerMass", "memberCapacity",
        "memberLabel", "labelDecidableEq"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.localSupplyLowerBound,
      "local_supply_lower_bound",
      ``Hypostructure.Core.StrategyData.localSupplyLowerBounds,
      ["Member", "Label", "members", "requiredMass", "observedSupply",
        "defectCorrection", "label", "labelDecidableEq"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.targetRelativeRankDichotomy,
      "target_relative_rank_dichotomy",
      ``Hypostructure.Core.StrategyData.targetRelativeRankDichotomies,
      ["Response", "response", "Datum", "Class", "Promotion",
        "observationData", "completeClasses", "classOf", "Direct",
        "promote", "directDecidable", "Coordinate", "coordinates",
        "TargetDependent", "targetDependentDecidable", "charge",
        "capacitySlack"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.compressionLinkedTargetRelativeRankDichotomy,
      "compression_linked_target_relative_rank_dichotomy",
      ``Hypostructure.Core.StrategyData.compressionLinkedTargetRelativeRankDichotomies,
      ["reductionIndex", "Coordinate", "SiteRelation", "Response", "response",
        "Datum", "Class", "Promotion", "observationData", "completeClasses",
        "classOf", "Direct", "promote", "directDecidable", "coordinates",
        "charge", "charge_pos", "capacitySlack", "rankDropImpossible",
        "targetDependentDecidable"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteStateCapacity,
      "finite_state_capacity",
      ``Hypostructure.Core.StrategyData.finiteStateCapacities,
      ["Target", "Offset", "Position", "Value", "targets", "offsets",
        "scales", "selectedScale", "selectedScale_mem", "positions",
        "finiteScaleLimit", "targetValue", "blockValue", "orbitValue",
        "Compatible", "compatibleDecidable", "valueDecidableEq", "Label",
        "memberLowerMass", "memberCapacity", "memberLabel",
        "labelDecidableEq", "RealizedState", "realizedStateFinite",
        "realizedStateNonempty", "ambientOrder", "remainderCard",
        "statePowerExponent", "statePowerExponent_pos",
        "forcedBase", "flatBase",
        "flatBase_pos", "jointProfile", "jointBaseCard", "jointExponent",
        "jointWeight", "jointLocalLower", "jointPaidExponent",
        "jointPaidExponent_exact", "jointDesiredExponent",
        "jointErrorExponent", "jointCapacity", "jointCapacity_pos",
        "jointCodeCapacity", "jointDesiredExponent_exact"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.route8CarrierClosure,
      "route8_carrier_closure",
      ``Hypostructure.Core.StrategyData.route8CarrierClosures,
      ["budget", "Site", "Witness", "family", "Active", "Supports",
        "witnessContribution", "required", "capacity", "activeDecidable",
        "supportsDecidable", "resourceLEDecidable", "Member", "Label",
        "members", "memberLowerMass", "memberCapacity", "memberLabel",
        "labelDecidableEq", "State", "Peeled", "DemandResidual",
        "TierResidual", "peel", "restorations", "initialLoad",
        "initialState"]),
    (`Hypostructure.Core.Strategy.Dag.StrategyKey.finiteScheduleCapacity,
      "finite_schedule_capacity",
      ``Hypostructure.Core.StrategyData.finiteScheduleCapacities,
      ["Index", "FailureData", "failureOrder", "Failure", "failureData",
        "failureDecidable", "rowContribution", "budget", "Site", "Witness",
        "family", "Active", "Supports", "witnessContribution", "required",
        "capacity", "activeDecidable", "supportsDecidable",
        "resourceLEDecidable", "Member", "Label", "members",
        "memberLowerMass", "memberCapacity", "memberLabel",
        "labelDecidableEq"])
  ]
  let mut registrations : List Json := []
  for (ctor, kind, field, fields) in specs do
    let some count ← evalListLength (← mkAppM field #[data]) | continue
    for index in List.range count do
      match ← registrationJson data ctor kind index fields with
      | some registration => registrations := registrations ++ [registration]
      | none => pure ()
  registrations := registrations ++ [
    singletonRegistrationJson "cold_branch_aggregation" [],
    singletonRegistrationJson "finite_state_net_charge_continuation"
      [] [("type_A", false), ("type_B", false)]
  ]
  return .arr registrations.toArray

private def registeredKeyWork (data key : Expr) : MetaM (Option Nat) := do
  let _ := data
  let _ ← strategyKeyOfRef key
  return some 1

private partial def blueprintWorkBound (data dag : Expr) : MetaM (Option Nat) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root => return some 0
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step => do
      let args := blueprintCtorArgs dag 2
      let some rest ← blueprintWorkBound data args[0]! | return none
      let some own ← registeredKeyWork data args[1]! | return none
      return some (rest + own)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let some rest ← blueprintWorkBound data args[0]! | return none
      let _ ← binaryStrategyKeyOfRef args[1]!
      let some left ← blueprintWorkBound data args[2]! | return none
      let some right ← blueprintWorkBound data args[3]! | return none
      return some (rest + 1 + max left right)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let some rest ← blueprintWorkBound data args[0]! | return none
      let some exceptional ← blueprintWorkBound data args[2]! | return none
      let some structured ← blueprintWorkBound data args[3]! | return none
      let some bounded ← blueprintWorkBound data args[4]! | return none
      return some
        (rest + 1 + max exceptional (max structured bounded))
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      let some rest ← blueprintWorkBound data args[0]! | return none
      -- Selection plus the four sealed continuation strategies represented
      -- by `CounterexampleContinuationMetadata`.
      return some (rest + 5)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      blueprintWorkBound data (blueprintCtorArgs dag 2)[0]!
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute => do
      let args := blueprintCtorArgs dag 3
      let some rest ← blueprintWorkBound data args[0]! | return none
      let some route ← evalResolvedRoute args[1]! args[2]! | return none
      return some (rest + route.work + route.destinationWork)
  | _ => return none

private def resolvedRouteJson (_ordinal : Nat)
    (route : ResolvedRouteView) : Json :=
  .mkObj [
    ("source_id", .str ("v" ++ toString route.sourceId)),
    ("destination_id", .str ("v" ++ toString route.destinationId)),
    ("source_depth", .num route.sourceDepth),
    ("destination_depth", .num route.destinationDepth),
    ("scope", .str route.scope),
    ("relation", .str route.relation),
    ("compatible_candidates", .arr
      ((route.compatibleCandidates.zip route.compatibleCandidateDepths).map
        (fun (id, depth) =>
        Json.mkObj [
          ("node_id", .str ("v" ++ toString id)),
          ("depth", .num depth),
          ("relation", .str route.relation),
          ("capability_status", .str "satisfied")
        ])).toArray),
    ("selection", .mkObj [
      ("rule", .str route.selectedBy),
      ("selected_candidate_id",
        .str ("v" ++ toString route.destinationId)),
      ("tie_break", .str "smallest_stable_structural_id")
    ]),
    ("bridge_provenance", .mkObj [
      ("relation_witness", .str "BridgeCertificate.residual_eq"),
      ("target_congruence", .str "literal_residual_identity"),
      ("destination_requirements",
        stringArray ["typed_continuation_entry",
          "literal_source_capabilities"]),
      ("ledger_ancestors", stringArray ["literal_predecessor_stage"]),
      ("framework_lemmas", stringArray [
        "Hypostructure.Core.Residual.Ledger.extend_previous",
        "Hypostructure.Core.Residual.Ledger.residualOf_extend",
        "Hypostructure.Core.Strategy.HaltingProgram.snoc_previous"
      ]),
      ("ledger_extension",
        .str "Hypostructure.Core.Residual.Ledger.Extension")
    ]),
    ("presentation", .mkObj [
      ("label", optionalJson (nonemptyString route.name)),
      ("note", optionalJson (nonemptyString route.note)),
      ("tags", stringArray route.tags)
    ]),
    ("bridge_work", .num route.work),
    ("destination_work", .num route.destinationWork),
    ("work", .num (route.work + route.destinationWork)),
    ("acyclic", .bool true)
  ]

private partial def collectResolvedRoutes (dag : Expr) (next : Nat) :
    MetaM (Option (List Json × Nat × Nat)) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.root =>
      return some ([], next, 0)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.step
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.annotate
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.labelled
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.documented =>
      collectResolvedRoutes (blueprintCtorArgs dag 2)[0]! next
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.resolvedRoute => do
      let args := blueprintCtorArgs dag 3
      let some (prior, next, priorWork) ←
        collectResolvedRoutes args[0]! next | return none
      let some route ← evalResolvedRoute args[1]! args[2]! | return none
      return some
        (prior ++ [resolvedRouteJson next route], next + 1,
          priorWork + route.work + route.destinationWork)
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.binaryBranch => do
      let args := blueprintCtorArgs dag 4
      let _ ← binaryStrategyKeyOfRef args[1]!
      let some (prior, next, priorWork) ←
        collectResolvedRoutes args[0]! next | return none
      let some (left, next, leftWork) ←
        collectResolvedRoutes args[2]! next | return none
      let some (right, next, rightWork) ←
        collectResolvedRoutes args[3]! next | return none
      return some
        (prior ++ left ++ right, next, priorWork + max leftWork rightWork)
  | some
      `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneckBranches => do
      let args := blueprintCtorArgs dag 5
      let some (prior, next, priorWork) ←
        collectResolvedRoutes args[0]! next | return none
      let some (exceptional, next, exceptionalWork) ←
        collectResolvedRoutes args[2]! next | return none
      let some (structured, next, structuredWork) ←
        collectResolvedRoutes args[3]! next | return none
      let some (bounded, next, boundedWork) ←
        collectResolvedRoutes args[4]! next | return none
      return some
        (prior ++ exceptional ++ structured ++ bounded, next,
          priorWork + max exceptionalWork (max structuredWork boundedWork))
  | some `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexample => do
      let args := blueprintCtorArgs dag 3
      let some (prior, next, priorWork) ←
        collectResolvedRoutes args[0]! next | return none
      return some (prior, next, priorWork)
  | _ => return none

private def descriptorString (descriptor? : Option Expr) (field : Name)
    (fallback : String) : MetaM String := do
  let some descriptor := descriptor? | return fallback
  evalStrLiteral (← mkAppM field #[descriptor])

/-- Longest execution-vertex path of the exported graph.

This is the single derivation of the sealed check/work bound: it reads the very
`ExportGraph` that `buildRunSummaryPayload` serializes, so the number in the
certificate is a function of the artifact rather than a parallel re-derivation
over the blueprint.  Execution vertices are the `v`-prefixed ids and cost one
check each; edge traversal costs nothing, because a route transports a residual
and is not a registered check. -/
private def exportGraphEdgePairs (graph : ExportGraph) :
    List (String × String) :=
  graph.edges.map fun edge =>
    let field (key : String) : String :=
      ((edge.getObjValD key).getStr?).toOption.getD ""
    (field "source", field "target")

private def exportLongestPath (edges : List (String × String)) :
    Nat -> String -> Nat
  | 0, _ => 0
  | Nat.succ fuel, source =>
      let weight := if source.startsWith "v" then 1 else 0
      let tail := (edges.filter fun edge => edge.1 == source).foldl
        (fun acc edge => max acc (exportLongestPath edges fuel edge.2)) 0
      weight + tail

private def exportGraphBound (graph : ExportGraph) : Nat :=
  match graph.entry with
  | none => 0
  | some entry =>
      exportLongestPath (exportGraphEdgePairs graph)
        (graph.nodes.length + graph.terminals.length + graph.edges.length + 1)
        entry

/-- Reflect the neutral machine-readable payload consumed by the private
certificate finalizer in `Dag.lean`.  This value deliberately omits the
artifact type, run status, execution result, and trust fields, so arbitrary
raw expressions cannot be published as certified declarations through this
API. -/
def buildRunSummaryPayload (runName : String)
    (problemE dagE : Expr) (descriptorE : Option Expr := none)
    (certified : Bool := true) :
    TermElabM (Option Json) := do
  let summary? ← (if certified then
      computeRunSummaryData true problemE dagE
    else do
      let targetE ← mkAppM
        ``Hypostructure.Core.ProblemDefinition.target #[problemE]
      let statementE ← whnf
        (← mkAppM ``Hypostructure.Core.Target.Statement #[targetE])
      return some ({
        statement := toString (← ppExpr statementE)
        evidence := "kernel-certified target-or-exact-residual reduction"
        closedBranches := []
        dagLines := []
        forest := ""
        forestPanels := []
        residualBlocks := []
      } : RunSummaryData) : TermElabM (Option RunSummaryData))
  match summary? with
  | some data =>
      let dataE ← mkAppM ``Hypostructure.Core.ProblemDefinition.data #[problemE]
      let some graph ← buildExportGraph dataE dagE certified | return none
      let graph := finalizeExportGraph graph certified
      let problem ← mkAppM ``Hypostructure.Core.ProblemDefinition.problem #[problemE]
      let target ← mkAppM ``Hypostructure.Core.ProblemDefinition.target #[problemE]
      let metadata ← mkAppM ``Hypostructure.Core.ProblemDefinition.metadata #[problemE]
      let authored ← exportDocumentation
        (← mkAppM ``Hypostructure.Core.ProblemMetadata.toDocumentation #[metadata])
      let authoredSignature ← evalStrLiteral
        (← mkAppM ``Hypostructure.Core.ProblemMetadata.signature #[metadata])
      let authoredStatement ← evalStrLiteral
        (← mkAppM ``Hypostructure.Core.ProblemMetadata.statement #[metadata])
      let render (e : Expr) : TermElabM String :=
        return (toString (← ppExpr e)).replace "\n" " "
      let moduleName ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.moduleName
        (← getEnv).mainModule.toString
      let sourceExpression ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.sourceExpression runName
      let definitionRef := moduleName ++ "." ++ sourceExpression
      let ambientRendering ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.ambientType
        (← render (← mkAppM ``Hypostructure.Core.Problem.Ambient #[problem]))
      let baselineRendering ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.baselinePredicate
        (← render (← mkAppM ``Hypostructure.Core.Problem.Baseline #[problem]))
      let branchRendering ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.branchState
        (← render (← mkAppM ``Hypostructure.Core.Problem.BranchState #[problem]))
      let targetRendering ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.targetPredicate
        (← render (← mkAppM ``Hypostructure.Core.Target.Predicate #[target]))
      let statementRendering ← descriptorString descriptorE
        `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.statement data.statement
      let formal (reference rendering : String) := Json.mkObj [
        ("declaration_ref", .str reference),
        ("rendering", .str rendering)
      ]
      let registrations ← registrationsJson dataE
      let some (autoroutes, _, _) ← collectResolvedRoutes dagE 0 | return none
      let payload : Json := .mkObj [
        ("run_name", .str runName),
        ("problem", .mkObj [
          ("id", .str definitionRef),
          ("identity", .mkObj [
            ("definition_ref", .str definitionRef),
            ("module", .str moduleName),
            ("source_expression", .str sourceExpression)
          ]),
          ("presentation", .mkObj [
            ("label", optionalJson authored.label),
            ("note", optionalJson authored.note),
            ("tags", stringArray authored.tags),
            ("authored_signature", optionalJson (nonemptyString authoredSignature)),
            ("authored_statement", optionalJson (nonemptyString authoredStatement))
          ]),
          ("formal", .mkObj [
            ("ambient_type", formal (definitionRef ++ ".problem.Ambient")
              ambientRendering),
            ("baseline_predicate", formal (definitionRef ++ ".problem.Baseline")
              baselineRendering),
            ("branch_state", formal (definitionRef ++ ".problem.BranchState")
              branchRendering),
            ("target_predicate", formal (definitionRef ++ ".target.Predicate")
              targetRendering),
            ("statement", formal (definitionRef ++ ".target.Statement")
              statementRendering)
          ])
        ]),
        ("strategy_registrations", registrations),
        ("dag", .mkObj [
          ("representation", .str "normalized_directed_graph"),
          ("entry", graph.entry.map Json.str |>.getD .null),
          ("nodes", .arr graph.nodes.toArray),
          ("edges", .arr graph.edges.toArray),
          ("terminals", .arr graph.terminals.toArray),
          ("autoroutes", .arr autoroutes.toArray)
        ]),
        ("checks_bound", .num (exportGraphBound graph)),
        ("work_bound", .num (exportGraphBound graph))
      ]
      return some payload
  | none => return none

end Hypostructure.Core.Strategy.Validate
