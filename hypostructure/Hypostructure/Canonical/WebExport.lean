import Hypostructure
import Lean

/-!
# Hypostructure web declaration export

This build-time exporter is the compiled-environment boundary for the
documentation application.  It deliberately exports facts about Lean
declarations only.  Editorial copy, examples, and navigation are assembled by
the deterministic Python web-data build, while declaration names, types,
documentation strings, source locations, and dependency edges come from Lean.
-/

open Lean Meta Elab Command

namespace Hypostructure.Canonical.WebExport

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationType (info : ConstantInfo) : CommandElabM String :=
  liftTermElabM do pure (toString (← ppExpr info.type))

private def sourcePath (moduleName : Name) : String :=
  String.intercalate "/" (moduleName.toString.splitOn ".") ++ ".lean"

private def distinctNames (names : List Name) : List Name :=
  names.foldl (fun result name =>
    if result.contains name then result else result ++ [name]) []

private def sortedNames (names : List Name) : List Name :=
  distinctNames names |>.mergeSort fun first second =>
    first.toString < second.toString

private def typeDependencies (info : ConstantInfo) : List Name :=
  sortedNames info.type.getUsedConstants.toList

private def valueDependencies : ConstantInfo → List Name
  | .defnInfo info => sortedNames info.value.getUsedConstants.toList
  | .thmInfo info => sortedNames info.value.getUsedConstants.toList
  | .opaqueInfo info => sortedNames info.value.getUsedConstants.toList
  | .inductInfo info => sortedNames info.ctors
  | _ => []

private def hasBody : ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

private def projectName (name : Name) : Bool :=
  (`Hypostructure).isPrefixOf name

private def declarationModule?
    (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  pure env.header.moduleNames[moduleIdx.toNat]!

private def exportedModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text.startsWith "Hypostructure" &&
    !text.startsWith "Hypostructure.Fixtures" &&
    !text.startsWith "Hypostructure.Canonical"

private def layer (moduleName : Name) : String :=
  let text := moduleName.toString
  if text.startsWith "Hypostructure.Core" then "core"
  else if text.startsWith "Hypostructure.Routes" then "routes"
  else if text.startsWith "Hypostructure.Graph" then "graph"
  else if text.startsWith "Hypostructure.PDE" then "pde"
  else if text.startsWith "Hypostructure.CT" then "ct"
  else "framework"

private def routeOwner : Routes.Registry.Owner → String
  | .sourceRegistry => "framework"
  | .erdosGyarf64 => "erdos"
  | .pdeArchitecture => "pde"

private def routeKind : Routes.Registry.Kind → String
  | .specializedDiscovery => "specialized_discovery"
  | .genericAccumulated => "generic_accumulated"
  | .profileRequirement => "profile_requirement"
  | .familyRequirement => "family_requirement"

private def routeStatus : Routes.Registry.Status → String
  | .baseline => "baseline"
  | .planned => "planned"

private def routeJson (entry : Routes.Registry.Entry) : Json :=
  Json.mkObj [
    ("route_id", toJson entry.edgeKey),
    ("source_ct", toJson entry.source.key),
    ("target_ct", toJson entry.target.key),
    ("family_id", toJson entry.familyKey),
    ("profile_id", toJson entry.profileId),
    ("owner", toJson (routeOwner entry.owner)),
    ("kind", toJson (routeKind entry.kind)),
    ("catalog_status", toJson (routeStatus entry.status)),
    ("executable_evidence", Json.null)
  ]

private def strategyJson
    (id tier title blueprintKey registration declaration : String) : Json :=
  Json.mkObj [
    ("id", toJson id),
    ("tier", toJson tier),
    ("title", toJson title),
    ("blueprint_key", if blueprintKey.isEmpty then Json.null else toJson blueprintKey),
    ("registration", toJson registration),
    ("declaration", toJson declaration)
  ]

/-- The application-facing strategy surface.  This explicit registry keeps
the web catalog tied to the compiled API without exposing compiler recipes or
the older CT execution layer as application authoring concepts. -/
private def strategyCatalog : List Json :=
  [
    strategyJson "ordered-witness-scan" "vertex" "Ordered witness scan"
      "orderedWitnessScan" "Core.ScanData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.orderedWitnessScan",
    strategyJson "response-classifier" "vertex" "Response classifier"
      "responseClassifier" "Core.ResponseData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.responseClassifier",
    strategyJson "capacity-ledger" "vertex" "Capacity ledger"
      "capacityLedger" "Core.CapacityData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.capacityLedger",
    strategyJson "support-localization" "vertex" "Support localization"
      "supportLocalization" "Core.LocalizationData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.supportLocalization",
    strategyJson "rank-budget" "vertex" "Rank and budget split"
      "rankBudget" "Core.RankBudgetData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.rankBudget",
    strategyJson "closed-code" "vertex" "Closed-code exhaustion"
      "closedCode" "Core.ClosedCodeData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.closedCode",
    strategyJson "obstruction-packing-closure" "vertex"
      "Obstruction packing closure" "obstructionPackingClosure"
      "Core.Strategy.ObstructionPackingClosure.Semantics"
      "Hypostructure.Core.Strategy.Dag.Blueprint.obstructionPackingClosure",
    strategyJson "exact-finite-local-algebra" "vertex"
      "Exact finite local algebra" "exactFiniteLocalAlgebra"
      "Core.Strategy.ExactFiniteLocalAlgebra.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.exactFiniteLocalAlgebra",
    strategyJson "finite-barrier-enumeration" "vertex"
      "Finite barrier enumeration" "finiteBarrierEnumeration"
      "Core.Strategy.FiniteBarrierEnumeration.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.finiteBarrierEnumeration",
    strategyJson "finite-density-budget" "vertex"
      "Finite density budget" "finiteDensityBudget"
      "Core.Strategy.FiniteDensityBudget.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.finiteDensityBudget",
    strategyJson "finite-state-capacity" "vertex"
      "Finite state capacity" "finiteStateCapacity"
      "Core.Strategy.FiniteStateCapacity.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.finiteStateCapacity",
    strategyJson "finite-schedule-capacity" "vertex"
      "Finite schedule capacity" "finiteScheduleCapacity"
      "Core.Strategy.FiniteScheduleCapacity.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.finiteScheduleCapacity",
    strategyJson "dichotomy" "vertex" "Exhaustive dichotomy"
      "dichotomy" "Core.DichotomyData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.dichotomy",
    strategyJson "scale-threshold-dichotomy" "vertex"
      "Scale threshold dichotomy" "scaleThresholdDichotomy"
      "Core.Strategy.ScaleThresholdDichotomy.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.scaleThresholdDichotomy",
    strategyJson "atom-context-obstruction-dichotomy" "vertex"
      "Atom-context obstruction dichotomy" "atomContextObstructionDichotomy"
      "Core.AtomContextObstructionDichotomyData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.atomContextObstructionDichotomy",
    strategyJson "ordered-surplus-activation" "vertex"
      "Ordered surplus activation" "orderedSurplusActivation"
      "Core.Strategy.OrderedSurplusActivation.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.orderedSurplusActivation",
    strategyJson "baseline-demand-accounting" "vertex"
      "Baseline demand accounting" "baselineDemandAccounting"
      "Core.Strategy.BaselineDemandAccounting.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.baselineDemandAccounting",
    strategyJson "canonical-pair-response-accounting" "vertex"
      "Canonical pair-response accounting" "canonicalPairResponseAccounting"
      "Core.Strategy.CanonicalPairResponseAccounting.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.canonicalPairResponseAccounting",
    strategyJson "canonical-capacity-token-accounting" "vertex"
      "Canonical capacity-token accounting" "canonicalCapacityTokenAccounting"
      "Core.Strategy.CanonicalCapacityTokenAccounting.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.canonicalCapacityTokenAccounting",
    strategyJson "coupled-homogeneous-fibre-pressure" "vertex"
      "Coupled homogeneous-fibre pressure" "coupledHomogeneousFibrePressure"
      "Core.Strategy.CoupledHomogeneousFibrePressure.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.coupledHomogeneousFibrePressure",
    strategyJson "finite-bottleneck-classification" "vertex"
      "Finite bottleneck classification" "finiteBottleneckClassification"
      "Core.Strategy.FiniteBottleneckClassification.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.finiteBottleneckClassification",
    strategyJson "homogeneous-bottleneck" "vertex"
      "Homogeneous bottleneck" "homogeneousBottleneck"
      "Core.Strategy.HomogeneousBottleneck.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneck",
    strategyJson "support-complement-normalization" "vertex"
      "Support-complement normalization" "supportComplementNormalization"
      "Core.Strategy.SupportComplementNormalization.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.supportComplementNormalization",
    strategyJson "boundary-demand-accounting" "vertex"
      "Boundary-demand accounting" "boundaryDemandAccounting"
      "Core.Strategy.BoundaryDemandAccounting.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.boundaryDemandAccounting",
    strategyJson "local-supply-lower-bound" "vertex"
      "Local-supply lower bound" "localSupplyLowerBound"
      "Core.Strategy.LocalSupplyLowerBound.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.localSupplyLowerBound",
    strategyJson "target-relative-rank-dichotomy" "vertex"
      "Target-relative rank dichotomy" "targetRelativeRankDichotomy"
      "Core.Strategy.TargetRelativeRankDichotomy.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.targetRelativeRankDichotomy",
    strategyJson "counterexample-localization" "vertex"
      "Counterexample localization" "counterexampleLocalization"
      "Core.CounterexampleLocalizationData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.counterexampleLocalization",
    strategyJson "finite-state-net-charge-continuation" "vertex"
      "Finite-state net-charge continuation" "finiteStateNetChargeContinuation"
      "Core.Strategy.FiniteStateNetChargeContinuation.Registration"
      "Hypostructure.Core.Strategy.Dag.Blueprint.finiteStateNetChargeContinuation",
    strategyJson "minimal-counterexample-selection" "dependent"
      "Minimal counterexample selection" "minimalCounterexampleSelection"
      "Core.CounterexampleReductionData"
      "Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexampleSelection",
    strategyJson "target-algebra-reduction" "dependent"
      "Target algebra reduction" "targetAlgebraReduction"
      "Core.CounterexampleReductionData"
      "Hypostructure.Core.Strategy.Dag.AfterMinimalCounterexampleSelection.targetAlgebraReduction",
    strategyJson "minimal-subobject-exclusion" "dependent"
      "Minimal subobject exclusion" "minimalSubobjectExclusion"
      "Core.CounterexampleReductionData"
      "Hypostructure.Core.Strategy.Dag.AfterTargetAlgebraReduction.minimalSubobjectExclusion",
    strategyJson "critical-modification-structure" "dependent"
      "Critical modification structure" "criticalModificationStructure"
      "Core.CounterexampleReductionData"
      "Hypostructure.Core.Strategy.Dag.AfterMinimalSubobjectExclusion.criticalModificationStructure",
    strategyJson "interface-replacement-closure" "dependent"
      "Interface replacement closure" "interfaceReplacementClosure"
      "Core.CounterexampleReductionData"
      "Hypostructure.Core.Strategy.Dag.AfterCriticalModificationStructure.interfaceReplacementClosure",
    strategyJson "target-or-avoid" "vertex" "Target or avoidance"
      "targetOrAvoid" "Core.StrategyData.targetDecidable"
      "Hypostructure.Core.Strategy.Dag.Blueprint.targetOrAvoid"
  ]

private def positionJson (position : Position) : Json :=
  Json.mkObj [
    ("line", toJson position.line),
    ("column", toJson position.column)
  ]

private def rangeJson (range : DeclarationRange) : Json :=
  Json.mkObj [
    ("start", positionJson range.pos),
    ("end", positionJson range.endPos)
  ]

private def declarationJson
    (env : Environment) (name moduleName : Name) : CommandElabM Json := do
  let some info := env.find? name
    | throwError "Hypostructure web export: missing declaration {name}"
  let typeDeps := typeDependencies info |>.filter fun dependency =>
    projectName dependency && dependency != name
  let bodyDeps := valueDependencies info |>.filter fun dependency =>
    projectName dependency && dependency != name && !typeDeps.contains dependency
  let ranges? ← findDeclarationRanges? name
  let rangeValue := match ranges? with
    | none => Json.null
    | some ranges => rangeJson ranges.range
  let selectionRangeValue := match ranges? with
    | none => Json.null
    | some ranges => rangeJson ranges.selectionRange
  let docValue := match ← findDocString? env name with
    | none => Json.null
    | some doc => toJson doc
  pure <| Json.mkObj [
    ("declaration_id", toJson name.toString),
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("type", toJson (← declarationType info)),
    ("doc_string", docValue),
    ("module", toJson moduleName.toString),
    ("source_file", toJson (sourcePath moduleName)),
    ("range", rangeValue),
    ("selection_range", selectionRangeValue),
    ("body_available", toJson (hasBody info)),
    ("type_dependencies", toJson (typeDeps.map (·.toString))),
    ("body_dependencies", toJson (bodyDeps.map (·.toString))),
    ("layer", toJson (layer moduleName))
  ]

private def exportCatalog : CommandElabM Unit := do
  let env ← getEnv
  let declarationsUnsorted : List (Name × Name) := env.constants.toList.filterMap fun (name, _) => do
      guard (projectName name)
      let moduleName ← declarationModule? env name
      guard (exportedModule moduleName)
      pure (name, moduleName)
  let declarations := declarationsUnsorted.mergeSort fun first second =>
    first.1.toString < second.1.toString
  let declarationValues ← declarations.mapM fun (name, moduleName) =>
    declarationJson env name moduleName
  let catalog := Json.mkObj [
    ("artifact_type", toJson "hypostructure_declaration_catalog"),
    ("schema_version", toJson "1.0.0"),
    ("framework", Json.mkObj [
      ("name", toJson "Hypostructure"),
      ("namespace", toJson "Hypostructure"),
      ("source_of_truth", toJson "compiled_lean_environment")
    ]),
    ("ct_catalog", Json.arr
      (Routes.Registry.ctIds.map fun id => toJson id.key).toArray),
    ("route_registry", Json.arr
      (Routes.Registry.all.map routeJson).toArray),
    ("strategy_catalog", Json.arr strategyCatalog.toArray),
    ("declarations", Json.arr declarationValues.toArray)
  ]
  let output := (← IO.getEnv "HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT").getD
    "../generated/hypostructure/web/declarations.raw.json"
  let outputPath := System.FilePath.mk output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (catalog.pretty 100 ++ "\n")
  logInfo m!"Exported {declarationValues.length} Hypostructure declarations to {output}"

run_cmd exportCatalog

end Hypostructure.Canonical.WebExport
