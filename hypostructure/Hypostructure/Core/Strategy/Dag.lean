import Hypostructure.Core.Strategy.StrategyProgram
import Lean.Elab.Tactic

/-!
# Fluent strategy DAG frontend

The public language contains only sealed scopes, atomic strategies, exhaustive
decisions, topology, and display metadata.  The elaborators at the bottom of
this file lower that syntax to the dependent `StrategyProgram` backend.
-/

namespace Hypostructure.Core.Strategy.Dag

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe uAmbient uBranch uKey uValue

structure DisplayMetadata where
  name : String := ""
  note : String := ""
  deriving Inhabited, Repr

structure BranchMetadata where
  leftName : String := ""
  leftNote : String := ""
  rightName : String := ""
  rightNote : String := ""
  deriving Inhabited, Repr

private inductive BlueprintBody
    {P : Core.Problem.{uAmbient, uBranch}} (T : Core.Target P)
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)] where
  | root : BlueprintBody T
  | scoped (rest : BlueprintBody T) (scope : CounterexampleScope T) : BlueprintBody T
  | atomic (rest : BlueprintBody T) (ct : AtomicCT (ProblemInput P))
      (metadata : DisplayMetadata) : BlueprintBody T
  | decision (rest : BlueprintBody T) (split : AtomicDecision (ProblemInput P))
      (left right : BlueprintBody T) (metadata : DisplayMetadata)
      (branches : BranchMetadata) : BlueprintBody T
  | route (rest : BlueprintBody T) (metadata : DisplayMetadata) : BlueprintBody T

/-- Proof-irrelevant authored topology.  Its representation is private, so
the fluent operations below are the complete application authoring surface. -/
structure Blueprint
    {P : Core.Problem.{uAmbient, uBranch}} (T : Core.Target P)
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)] where
  private mk ::
  private body : BlueprintBody T

namespace Blueprint

def root
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)] : Blueprint T :=
  .mk .root

def scope
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)]
    (dag : Blueprint T) (entry : CounterexampleScope T) : Blueprint T :=
  .mk (.scoped dag.body entry)

def step
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)]
    (dag : Blueprint T) (ct : AtomicCT (ProblemInput P))
    (name : String := "") (note : String := "") : Blueprint T :=
  .mk (.atomic dag.body ct { name, note })

def branch
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)]
    (dag : Blueprint T) (split : AtomicDecision (ProblemInput P))
    (left : Blueprint T -> Blueprint T := id)
    (right : Blueprint T -> Blueprint T := id)
    (name : String := "") (note : String := "")
    (leftName : String := "") (leftNote : String := "")
    (rightName : String := "") (rightNote : String := "") : Blueprint T :=
  .mk (.decision dag.body split (left root).body (right root).body { name, note }
    { leftName, leftNote, rightName, rightNote })

/-- A targetless handoff marker.  Route resolution is deliberately rejected
until the exact-key structural resolver installs a destination. -/
def autoroute
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)]
    (dag : Blueprint T) (name : String := "") (note : String := "") : Blueprint T :=
  .mk (.route dag.body { name, note })

end Blueprint

/-- A diagnostic compilation whose exact frontier is existentially sealed. -/
structure CompiledDag
    {P : Core.Problem.{uAmbient, uBranch}} (T : Core.Target P)
    [FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (ProblemInput P)] where
  private mk ::
  private frontier : List (FactKeys (ProblemInput P))
  private dag : StrategyDag T frontier

scoped syntax (name := reduceDagFrontend) "reduceDag% " term:max term:max : term
scoped syntax (name := ofDagFrontend) "ofDag% " term:max term:max : term

section Frontend

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

private inductive AuthoredTree where
  | hole
  | atomic (ct : Expr) (next : AuthoredTree)
  | branch (decision : Expr) (left right : AuthoredTree)
  | route

private structure ParsedBlueprint where
  tree : AuthoredTree
  scope? : Option Expr := none

private def mapHoles (tree suffix : AuthoredTree) : AuthoredTree :=
  match tree with
  | .hole => suffix
  | .atomic ct next => .atomic ct (mapHoles next suffix)
  | .branch decision left right =>
      .branch decision (mapHoles left suffix) (mapHoles right suffix)
  | .route => .route

private def constructorName (value : Expr) : MetaM Name := do
  let reduced <- whnf value
  match reduced.getAppFn.constName? with
  | some name => pure name
  | none => throwError "strategy DAG frontend expected a reducible Blueprint term"

private partial def parseBody (value : Expr) : MetaM ParsedBlueprint := do
  let reduced <- whnf value
  let name <- constructorName reduced
  let args := reduced.getAppArgs
  if name == ``BlueprintBody.root then
    pure { tree := .hole }
  else if name == ``BlueprintBody.scoped then
    let previous <- parseBody args[args.size - 2]!
    if previous.scope?.isSome then
      throwError "strategy DAG contains more than one counterexample scope"
    pure { previous with scope? := some args[args.size - 1]! }
  else if name == ``BlueprintBody.atomic then
    let previous <- parseBody args[args.size - 3]!
    pure { previous with
      tree := mapHoles previous.tree (.atomic args[args.size - 2]! .hole) }
  else if name == ``BlueprintBody.decision then
    let previous <- parseBody args[args.size - 6]!
    let left <- parseBody args[args.size - 4]!
    let right <- parseBody args[args.size - 3]!
    if left.scope?.isSome || right.scope?.isSome then
      throwError "a branch continuation cannot open a new counterexample scope"
    let tree := mapHoles previous.tree
      (.branch args[args.size - 5]! left.tree right.tree)
    pure { previous with tree := tree }
  else if name == ``BlueprintBody.route then
    let previous <- parseBody args[args.size - 2]!
    pure { previous with tree := mapHoles previous.tree .route }
  else
    throwError "unsupported strategy DAG constructor {name}"

private partial def listElementsAux (cursor : Expr) (result : Array Expr) :
    MetaM (Array Expr) := do
  let cursor <- whnf cursor
  match cursor.getAppFn.constName? with
  | some ``List.nil => pure result
  | some ``List.cons =>
      let args := cursor.getAppArgs
      listElementsAux args[args.size - 1]! (result.push args[args.size - 2]!)
  | _ => throwError "strategy manifest did not reduce to an exact fact-key list"

private def listElements (value : Expr) : MetaM (Array Expr) :=
  listElementsAux value #[]

private def normalizeKeyList (value : Expr) : MetaM Expr := do
  let keys <- withTransparency .all <| listElements value
  let elementType <- match keys[0]? with
    | some key => inferType key
    | none => do
        let type <- whnf (← inferType value)
        pure type.getAppArgs.back!
  mkListLit elementType keys.toList

private def notMember (key keys : Expr) : MetaM Expr := do
  mkAppM ``Not #[← mkAppM ``List.Mem #[key, keys]]

private def normalizeSafetyList (keys : Expr) : MetaM Expr := do
  let elements <- listElements keys
  let elements <- elements.mapM fun key => withTransparency .all <| whnf key
  let elementType <- match elements[0]? with
    | some key => inferType key
    | none => do
        let type <- whnf (← inferType keys)
        pure type.getAppArgs.back!
  mkListLit elementType elements.toList

private def closureKey (residual : Expr) : MetaM Expr := do
  withTransparency .all <|
    whnf (← mkAppOptM ``FactSystem.closureKey #[some residual, none, none])

private def decideWithKeyEquality (residual keyType proposition : Expr) : MetaM Expr := do
  let instanceType <- mkAppM ``DecidableEq #[keyType]
  let instanceValue <- mkAppOptM ``FactSystem.keyDecidableEq
    #[some residual, none, none]
  withLocalDecl `_dagKeyDecidableEq .instImplicit instanceType fun localInstance => do
    let declaration := (← getLCtx).get! localInstance.fvarId!
    let proof <- withLocalInstances [declaration] <|
      withTransparency .all <| mkDecideProof proposition
    pure (mkApp (← mkLambdaFVars #[localInstance] proof) instanceValue)

private def proveNotMember (residual key keys : Expr) : MetaM Expr := do
  let key <- withTransparency .all <| whnf key
  let keys <- normalizeSafetyList keys
  decideWithKeyEquality residual (← inferType key) (← notMember key keys)

private def proveDisjoint (residual left right : Expr) : MetaM Expr := do
  let left <- normalizeSafetyList left
  let right <- normalizeSafetyList right
  let keyType <- match (← listElements left)[0]? with
    | some key => inferType key
    | none => do
        let type <- whnf (← inferType left)
        pure type.getAppArgs.back!
  decideWithKeyEquality residual keyType
    (← mkAppM ``List.Disjoint #[left, right])

private def programType (residual known frontier : Expr) : MetaM Expr :=
  mkAppM ``StrategyProgram #[residual, known, frontier]

private def singleton (element : Expr) : MetaM Expr := do
  mkListLit (← inferType element) [element]

private def emptyFactFrontier (known : Expr) : MetaM Expr := do
  mkListLit (← inferType known) []

private def tryClosing (residual known : Expr) : MetaM (Option Expr) := do
  let empty <- emptyFactFrontier known
  let expected <- programType residual known empty
  try
    let value <- mkAppOptM ``StrategyProgram.closed
      #[some residual, none, none, some known]
    return some (← Lean.Meta.ensureHasType value expected)
  catch _ => pure ()
  let keys <- listElements known
  for key in keys do
    try
      let value <- mkAppOptM ``StrategyProgram.closeImpossibleExplicit
        #[some residual, none, none, some known, some key, none, none,
          some (← proveNotMember residual (← closureKey residual) known)]
      return some (← Lean.Meta.ensureHasType
        value expected)
    catch _ => pure ()
  for leftIndex in [:keys.size] do
    for rightIndex in [leftIndex + 1:keys.size] do
      try
        let value <- mkAppOptM ``StrategyProgram.closeIncompatibleExplicit
          #[some residual, none, none, some known, some keys[leftIndex]!,
            some keys[rightIndex]!, none, none, none,
            some (← proveNotMember residual (← closureKey residual) known)]
        return some (← Lean.Meta.ensureHasType
          value expected)
      catch _ => pure ()
  pure none

private partial def compileTree (residual known : Expr) : AuthoredTree ->
    MetaM (Expr × Expr)
  | .hole => do
      if let some closed <- tryClosing residual known then
        pure (closed, ← emptyFactFrontier known)
      else
        let frontier <- singleton known
        let expected <- programType residual known frontier
        let value <- mkAppOptM ``StrategyProgram.defer
          #[some residual, none, none, some known]
        pure (← Lean.Meta.ensureHasType value expected, frontier)
  | .route =>
      throwError "unresolved `autoroute`: exact-key route expansion is not installed for this topology"
  | .atomic ct next => do
      let ct <- withTransparency .all <| whnf ct
      let manifest <- mkAppM ``AtomicCT.manifest #[ct]
      let produced <- normalizeKeyList
        (← mkAppM ``FactManifest.Produces #[manifest])
      let nextKnown <- normalizeKeyList
        (← mkAppM ``List.append #[produced, known])
      let (continuation, frontier) <- compileTree residual nextKnown next
      let expected <- programType residual known frontier
      let requirements <- mkAppM ``FactManifest.toFactRequirements #[manifest]
      let requires <- normalizeKeyList
        (← mkAppM ``FactRequirements.Requires #[requirements])
      let availableType <- mkAppOptM ``FactKeys.Available
        #[some residual, none, none, some requires, some known]
      let available <- withTransparency .all <| synthInstance availableType
      let closedKey <- closureKey residual
      let value <- withTransparency .all <| mkAppOptM ``StrategyProgram.atomicExplicit
        #[some residual, none, none, some known, some frontier, some ct, some available,
          some continuation, some (← proveNotMember residual closedKey known),
          some (← proveNotMember residual closedKey produced),
          some (← proveDisjoint residual produced known)]
      pure (← Lean.Meta.ensureHasType
        value expected, frontier)
  | .branch decision left right => do
      let decision <- withTransparency .all <| whnf decision
      let manifest <- mkAppM ``AtomicDecision.manifest #[decision]
      let leftKey <- withTransparency .all <|
        whnf (← mkAppM ``DecisionManifest.left #[manifest])
      let rightKey <- withTransparency .all <|
        whnf (← mkAppM ``DecisionManifest.right #[manifest])
      let leftKnown <- normalizeKeyList
        (← mkAppM ``List.cons #[leftKey, known])
      let rightKnown <- normalizeKeyList
        (← mkAppM ``List.cons #[rightKey, known])
      let (leftProgram, leftFrontier) <- compileTree residual leftKnown left
      let (rightProgram, rightFrontier) <- compileTree residual rightKnown right
      let frontier <- mkAppM ``List.append #[leftFrontier, rightFrontier]
      let expected <- programType residual known frontier
      let requirements <- mkAppM ``DecisionManifest.toFactRequirements #[manifest]
      let requires <- normalizeKeyList
        (← mkAppM ``FactRequirements.Requires #[requirements])
      let availableType <- mkAppOptM ``FactKeys.Available
        #[some residual, none, none, some requires, some known]
      let available <- withTransparency .all <| synthInstance availableType
      let closedKey <- closureKey residual
      let value <- withTransparency .all <| mkAppOptM ``StrategyProgram.branchExplicit
        #[some residual, none, none, some known, some leftFrontier,
          some rightFrontier, some decision, some available, some leftProgram,
          some rightProgram, some (← proveNotMember residual closedKey known),
          some (← proveNotMember residual leftKey known),
          some (← proveNotMember residual rightKey known)]
      pure (← Lean.Meta.ensureHasType
        value expected, frontier)

private def compileBlueprint (target blueprint : Expr) : TermElabM (Expr × Expr × Expr) := do
  let blueprint <- whnf blueprint
  unless blueprint.getAppFn.constName? == some ``Blueprint.mk do
    throwError "strategy DAG frontend expected a reducible Blueprint term"
  let parsed <- parseBody blueprint.getAppArgs.back!
  let scope <- match parsed.scope? with
    | some scope => withTransparency .all <| whnf scope
    | none => throwError "strategy DAG must open exactly one counterexample scope"
  let targetType <- whnf (← inferType target)
  let targetArgs := targetType.getAppArgs
  let problem := targetArgs[targetArgs.size - 1]!
  let residual <- mkAppM ``ProblemInput #[problem]
  let selection <- mkAppM ``CounterexampleScope.selection #[scope]
  let known <- mkListLit (← inferType selection) [selection]
  let (program, frontier) <- compileTree residual known parsed.tree
  pure (scope, program, frontier)

elab_rules : term
  | `(reduceDag% $targetSyntax $blueprintSyntax) => do
      let target <- elabTerm targetSyntax none
      let blueprint <- elabTerm blueprintSyntax none
      let (scope, program, frontier) <- compileBlueprint target blueprint
      let dag <- mkAppM ``StrategyDag.ofCounterexampleScope #[target, scope, program]
      mkAppOptM ``CompiledDag.mk #[none, some target, none, some frontier, some dag]
  | `(ofDag% $targetSyntax $blueprintSyntax) => do
      let target <- elabTerm targetSyntax none
      let blueprint <- elabTerm blueprintSyntax none
      let (scope, program, frontier) <- compileBlueprint target blueprint
      let frontier <- whnf frontier
      unless frontier.getAppFn.constName? == some ``List.nil do
        throwError "strategy DAG did not close every local branch; use `reduceDag%` to inspect the derived frontier"
      let dag <- mkAppM ``StrategyDag.ofCounterexampleScope #[target, scope, program]
      mkAppM ``StrategyDag.complete #[dag]

end Frontend

end Hypostructure.Core.Strategy.Dag
