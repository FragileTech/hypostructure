import Lean.Elab.Command
import Hypostructure.Core.Problem
import Hypostructure.Core.Provision

/-!
# Presentation purity

`#check_presentation_pure root` is a compile-time ownership check for the
public problem boundary.  It accepts raw data, operators, predicates, and
proof-free records, and rejects proof or certificate payloads that a backend
must construct.  It creates no runtime registry or audit state.
-/

open Lean Meta Elab Command

namespace Hypostructure.Core.PresentationPurity

private inductive FindingKind
  | propositionField
  | forbiddenProofPackage
  | unsupportedOpaqueType

private structure Finding where
  path : List Name
  fieldType : String
  kind : FindingKind

private structure VisitState where
  visited : Std.HashSet Expr := {}
  depth : Nat := 0

private abbrev VisitM := StateRefT VisitState MetaM

private def scalarHeads : List Name :=
  [``PUnit, ``Unit, ``Empty, ``Bool, ``Nat, ``Int, ``String, ``Char, ``UInt8,
   ``UInt16, ``UInt32, ``UInt64, ``USize]

private def containerHeads : List Name :=
  [``Fin, ``List, ``Array, ``Option, ``Prod, ``Sum]

private def forbiddenHeads : List Name :=
  [``Subtype, ``Exists, ``Nonempty, ``Equiv,
   ``Hypostructure.Core.AuthorPrimitiveRef, ``Hypostructure.Core.Provision.Entry]

private def headName? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const name _ => some name
  | _ => none

private def replacement : FindingKind → String
  | .propositionField =>
      "keep the raw operands in the presentation and prove this proposition in Core or the domain backend"
  | .forbiddenProofPackage =>
      "present the raw data or operators and construct the certificate in Core or the domain backend"
  | .unsupportedOpaqueType =>
      "expose a proof-free data view whose fields can be inspected at the public boundary"

private def reason : FindingKind → String
  | .propositionField =>
      "proposition-valued field supplies a proof owned by the backend"
  | .forbiddenProofPackage =>
      "proof or audit package belongs behind the presentation boundary"
  | .unsupportedOpaqueType =>
      "opaque type cannot be verified as proof-free"

private def mkFinding (path : List Name) (type : Expr)
    (kind : FindingKind) : MetaM Finding := do
  return { path, fieldType := toString (← ppExpr type), kind }

private def isPropositionValue (type : Expr) : MetaM Bool := do
  let sort ← whnf (← inferType type)
  return sort == .sort .zero

private partial def inspect (type : Expr) (path : List Name) : VisitM (Option Finding) := do
  let type ← whnf type
  if ← isPropositionValue type then
    return some (← mkFinding path type .propositionField)
  if type.isSort || type.isFVar || type.isMVar then return none
  if (← get).depth > 128 then
    return some (← mkFinding path type .unsupportedOpaqueType)
  if (← get).visited.contains type then return none
  modify fun state => { state with visited := state.visited.insert type, depth := state.depth + 1 }
  let result ← match type with
    | .forallE _ domain body _ =>
        match ← inspect domain path with
        | some finding => pure (some finding)
        | none => withLocalDeclD `input domain fun argument => do
            let result := body.instantiate1 argument
            if result == .sort .zero then
              pure none
            else if ← isPropositionValue result then
              pure (some (← mkFinding path result .propositionField))
            else
              inspect result path
    | _ => do
        let some head := headName? type
          | return some (← mkFinding path type .unsupportedOpaqueType)
        let args := type.getAppArgs
        if forbiddenHeads.contains head then
          return some (← mkFinding path type .forbiddenProofPackage)
        if scalarHeads.contains head then return none
        if containerHeads.contains head then
          for arg in args do
            let argType ← whnf (← inferType arg)
            if argType.isSort then
              if let some finding ← inspect arg path then return some finding
          return none
        let env ← getEnv
        let some info := env.find? head
          | return some (← mkFinding path type .unsupportedOpaqueType)
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
            return some (← mkFinding path type .unsupportedOpaqueType)
        | .defnInfo _ =>
            let unfolded ← unfoldDefinition? type
            match unfolded with
            | some reduced => inspect reduced path
            | none => return some (← mkFinding path type .unsupportedOpaqueType)
        | .thmInfo _ =>
            return some (← mkFinding path type .propositionField)
        | .inductInfo induct =>
            if induct.isRec then
              -- Recursive occurrences are stopped by `visited`; constructor
              -- fields are still inspected on the first visit.
              pure ()
            if isStructure env head then
              withLocalDeclD `self type fun self => do
                for shortFieldName in getStructureFields env head do
                  let fieldName := Name.str head shortFieldName.getString!
                  let projection ← mkAppM fieldName #[self]
                  let fieldType ← inferType projection
                  if let some finding ← inspect fieldType (path ++ [shortFieldName]) then
                    return some finding
                return none
            else
              for constructor in induct.ctors do
                let constructorType ← inferType (← mkConstWithFreshMVarLevels constructor)
                let finding? ← forallTelescopeReducing constructorType fun locals _ => do
                  let fieldLocals := locals.extract induct.numParams (locals.size - induct.numParams)
                  for index in [:fieldLocals.size] do
                    let fieldName := Name.mkSimple s!"field{index + 1}"
                    let fieldType ← inferType fieldLocals[index]!
                    if let some finding ← inspect fieldType (path ++ [fieldName]) then
                      return some finding
                  return none
                if finding?.isSome then return finding?
              return none
        | .ctorInfo _ | .recInfo _ | .quotInfo _ =>
            return some (← mkFinding path type .unsupportedOpaqueType)
  modify fun state => { state with depth := state.depth - 1 }
  return result

private def rootName (type : Expr) : Name :=
  (headName? type).getD `presentation

private def formatPath (root : Name) (segments : List Name) : String :=
  String.intercalate "." ((root :: segments).map (fun name => name.getString!))

private def report (root : Name) (finding : Finding) : MetaM MessageData := do
  return m!"public presentation is not proof-free\nroot: {root.getString!}\npath: {formatPath root finding.path}\nfield type: {finding.fieldType}\nreason: {reason finding.kind}\nreplacement: {replacement finding.kind}"

syntax (name := checkPresentationPure) "#check_presentation_pure " term : command

elab_rules : command
  | `(#check_presentation_pure $rootTerm) => liftTermElabM do
      let term ← Term.elabTerm rootTerm none
      Term.synthesizeSyntheticMVarsNoPostponing
      let term ← instantiateMVars term
      let inferred ← inferType term >>= instantiateMVars
      let inferredWhnf ← whnf inferred
      let inspected ←
        if inferredWhnf.getAppFn.isConstOf ``Hypostructure.Core.Problem then
          let projected ← liftMetaM <| mkAppM ``Hypostructure.Core.Problem.Presentation #[term]
          liftMetaM <| whnf projected
        else if inferredWhnf.isSort then
          pure term
        else do
          let (parameters, _, body) ← liftMetaM <| forallMetaTelescopeReducing inferred
          let body ← liftMetaM <| whnf body
          if body.isSort then pure (mkAppN term parameters) else pure inferred
      let inspected ← whnf inspected
      let root := rootName inspected
      let finding? ← (inspect inspected []).run' {}
      if let some finding := finding? then
        throwError (← report root finding)

end Hypostructure.Core.PresentationPurity
