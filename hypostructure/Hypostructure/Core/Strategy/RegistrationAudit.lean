import Hypostructure.Core.Strategy.Dag

/-!
# Adversarial audit of registered strategy data

This module is deliberately execution-free.  It inspects a closed
`ProblemDefinition` and `Dag.Blueprint` at elaboration time and rejects
registration patterns which let an application disguise an asserted result
as strategy input:

* `targetOrAvoid` in a certified declaration;
* repeated references to the same generic registration;
* definitionally duplicate registrations in one family;
* registered tables which the blueprint never references.

The checks are structural.  They neither execute application callbacks nor
attempt to decide semantic equality of arbitrary functions.
-/

namespace Hypostructure.Core.Strategy.RegistrationAudit

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

structure Family where
  key : Name
  projection : Name
  label : String

private def families : List Family := [
  { key := ``Dag.StrategyKey.orderedWitnessScan,
    projection := ``Core.StrategyData.scans, label := "scan" },
  { key := ``Dag.StrategyKey.responseClassifier,
    projection := ``Core.StrategyData.responses, label := "response" },
  { key := ``Dag.StrategyKey.capacityLedger,
    projection := ``Core.StrategyData.capacities, label := "capacity" },
  { key := ``Dag.StrategyKey.orderedSurplusActivation,
    projection := ``Core.StrategyData.orderedSurplusActivations,
    label := "ordered-surplus-activation" },
  { key := ``Dag.StrategyKey.baselineDemandAccounting,
    projection := ``Core.StrategyData.baselineDemandAccountings,
    label := "baseline-demand-accounting" },
  { key := ``Dag.StrategyKey.canonicalPairResponseAccounting,
    projection := ``Core.StrategyData.canonicalPairResponseAccountings,
    label := "canonical-pair-response-accounting" },
  { key := ``Dag.StrategyKey.canonicalCapacityTokenAccounting,
    projection := ``Core.StrategyData.canonicalCapacityTokenAccountings,
    label := "canonical-capacity-token-accounting" },
  { key := ``Dag.StrategyKey.coupledHomogeneousFibrePressure,
    projection := ``Core.StrategyData.coupledHomogeneousFibrePressures,
    label := "coupled-homogeneous-fibre-pressure" },
  { key := ``Dag.StrategyKey.finiteBottleneckClassification,
    projection := ``Core.StrategyData.finiteBottleneckClassifications,
    label := "finite-bottleneck-classification" },
  { key := ``Dag.StrategyKey.homogeneousBottleneck,
    projection := ``Core.StrategyData.homogeneousBottlenecks,
    label := "homogeneous-bottleneck" },
  { key := ``Dag.StrategyKey.supportComplementNormalization,
    projection := ``Core.StrategyData.supportComplementNormalizations,
    label := "support-complement-normalization" },
  { key := ``Dag.StrategyKey.boundaryDemandAccounting,
    projection := ``Core.StrategyData.boundaryDemandAccountings,
    label := "boundary-demand-accounting" },
  { key := ``Dag.StrategyKey.localSupplyLowerBound,
    projection := ``Core.StrategyData.localSupplyLowerBounds,
    label := "local-supply-lower-bound" },
  { key := ``Dag.StrategyKey.targetRelativeRankDichotomy,
    projection := ``Core.StrategyData.targetRelativeRankDichotomies,
    label := "target-relative-rank-dichotomy" },
  { key := ``Dag.StrategyKey.finiteStateCapacity,
    projection := ``Core.StrategyData.finiteStateCapacities,
    label := "finite-state-capacity" },
  { key := ``Dag.StrategyKey.finiteScheduleCapacity,
    projection := ``Core.StrategyData.finiteScheduleCapacities,
    label := "finite-schedule-capacity" },
  { key := ``Dag.StrategyKey.supportLocalization,
    projection := ``Core.StrategyData.localizations, label := "localization" },
  { key := ``Dag.StrategyKey.rankBudget,
    projection := ``Core.StrategyData.rankBudgets, label := "rank" },
  { key := ``Dag.StrategyKey.closedCode,
    projection := ``Core.StrategyData.closedCodes, label := "closed-code" },
  { key := ``Dag.StrategyKey.dichotomy,
    projection := ``Core.StrategyData.dichotomies, label := "dichotomy" },
  { key := ``Dag.StrategyKey.scaleThresholdDichotomy,
    projection := ``Core.StrategyData.scaleThresholdDichotomies,
    label := "scale-threshold-dichotomy" },
  { key := ``Dag.StrategyKey.coldBranchAggregation,
    projection := ``Core.StrategyData.coldBranchAggregations,
    label := "cold-branch-aggregation" }
]

private partial def natLiteral? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => pure (some n)
  | _ => pure none

private def finLiteral? (e : Expr) : MetaM (Option Nat) := do
  natLiteral? (← mkAppM ``Fin.val #[e])

private partial def listEntries (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some ``List.nil => pure []
  | some ``List.cons =>
      let args := e.getAppArgs
      return args[1]! :: (← listEntries args[2]!)
  | _ =>
      throwError "strategy registrations must reduce to closed literal lists"

private def blueprintCtorArgs (dag : Expr) (fieldCount : Nat) : Array Expr :=
  let args := dag.getAppArgs
  args.extract (args.size - fieldCount) args.size

private def binaryKey (strategy : Expr) : MetaM Expr := do
  whnf (← mkAppM ``Dag.BinaryStrategyRef.keyView #[strategy])

private def scalarKey (strategy : Expr) : MetaM Expr := do
  whnf (← mkAppM ``Dag.StrategyRef.keyView #[strategy])

private partial def collectKeys (dag : Expr) : MetaM (List (Name × Nat)) := do
  let dag ← whnf dag
  match dag.getAppFn.constName? with
  | some ``Dag.Blueprint.root => pure []
  | some ``Dag.Blueprint.step =>
      let args := blueprintCtorArgs dag 2
      let prior ← collectKeys args[0]!
      let key ← scalarKey args[1]!
      let some ctor := key.getAppFn.constName?
        | throwError "strategy key does not reduce to a registered constructor"
      if ctor == ``Dag.StrategyKey.targetOrAvoid then
        throwError "certified declarations may not use `targetOrAvoid`; register a framework-owned exhaustive strategy"
      match families.find? (·.key == ctor) with
      | none => pure prior
      | some _ =>
          let some index ← natLiteral? key.getAppArgs.back!
            | throwError "strategy registration index must reduce to a natural-number literal"
          pure (prior ++ [(ctor, index)])
  | some ``Dag.Blueprint.binaryBranch =>
      let args := blueprintCtorArgs dag 4
      let prior ← collectKeys args[0]!
      let key ← binaryKey args[1]!
      let some ctor := key.getAppFn.constName?
        | throwError "binary strategy key does not reduce to a registered constructor"
      let some index ← natLiteral? key.getAppArgs.back!
        | throwError "binary strategy registration index must reduce to a natural-number literal"
      let own :=
        if families.any (·.key == ctor) then [(ctor, index)] else []
      return prior ++ own ++ (← collectKeys args[2]!) ++
        (← collectKeys args[3]!)
  | some ``Dag.Blueprint.homogeneousBottleneckBranches =>
      let args := blueprintCtorArgs dag 5
      let prior ← collectKeys args[0]!
      let some index ← finLiteral? args[1]!
        | throwError
            "homogeneous-bottleneck registration index must reduce to a \
            natural-number literal"
      return prior ++
        [(``Dag.StrategyKey.homogeneousBottleneck, index)] ++
        (← collectKeys args[2]!) ++ (← collectKeys args[3]!) ++
        (← collectKeys args[4]!)
  | some ``Dag.Blueprint.minimalCounterexample =>
      collectKeys (blueprintCtorArgs dag 3)[0]!
  | some ``Dag.Blueprint.annotate
  | some ``Dag.Blueprint.labelled
  | some ``Dag.Blueprint.documented
  | some ``Dag.Blueprint.route =>
      collectKeys (blueprintCtorArgs dag 2)[0]!
  | some ``Dag.Blueprint.resolvedRoute =>
      collectKeys (blueprintCtorArgs dag 3)[0]!
  | some ctor =>
      if ctor.toString.endsWith ".Program.mk" then
        collectKeys (blueprintCtorArgs dag 1)[0]!
      else
        throwError
          "blueprint must reduce to a closed framework-owned DAG; unsupported \
          constructor: {some ctor}"
  | none =>
      throwError
        "blueprint must reduce to a closed framework-owned DAG; unsupported \
        constructor: none"

private def duplicateIndex? (keys : List (Name × Nat)) : Option (Name × Nat) :=
  keys.find? fun key => (keys.filter (· == key)).length > 1

private def duplicateExpr? (entries : List Expr) : MetaM (Option (Nat × Nat)) := do
  for i in List.range entries.length do
    for j in List.range entries.length do
      if i < j then
        if ← isDefEq entries[i]! entries[j]! then return some (i, j)
  pure none

/-- Reject structurally detectable result-smuggling in a closed registration.
This is the validator intended to be called by the sealed frontend immediately
after ordinary blueprint compliance. -/
def check (problem dag : Expr) : TermElabM Unit := do
  let data ← mkAppM ``Core.ProblemDefinition.data #[problem]
  let keys ← collectKeys dag
  if let some (ctor, index) := duplicateIndex? keys then
    let label := (families.find? (·.key == ctor)).map (·.label) |>.getD "strategy"
    throwError s!"duplicate {label} registration reference #{index}; repeated generic stand-ins are forbidden"
  for family in families do
    let entries ← listEntries (← mkAppM family.projection #[data])
    if let some (i, j) ← duplicateExpr? entries then
      throwError s!"definitionally duplicate {family.label} registrations #{i} and #{j}"
    let used := keys.filterMap fun (ctor, index) =>
      if ctor == family.key then some index else none
    for index in List.range entries.length do
      unless used.contains index do
        throwError s!"unreferenced {family.label} registration #{index}"

scoped syntax (name := strictRegistrationAudit)
  "#hypostructure_strict_audit " term:max term:max : command

open Lean Elab Command in
elab_rules : command
  | `(#hypostructure_strict_audit $problemStx $dagStx) => liftTermElabM do
      let problem ← Term.elabTerm problemStx none
      let dag ← Term.elabTerm dagStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      check (← instantiateMVars problem) (← instantiateMVars dag)

end Hypostructure.Core.Strategy.RegistrationAudit
