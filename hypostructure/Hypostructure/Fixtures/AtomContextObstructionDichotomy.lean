import Hypostructure.Core.Strategy.AtomContextObstructionDichotomy
import Hypostructure.Core.Strategy.Dag

/-!
# Neutral sealed atom--context dichotomy fixture

The two registrations differ only in the truth of the atom obstruction.  No
domain interpretation is attached to the atom or context.
-/

namespace Hypostructure.Fixtures.AtomContextObstructionDichotomy

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Core.Strategy.AtomContextObstructionDichotomy
open Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def semantics : Core.SemanticEquivalence problem :=
  Core.SemanticEquivalence.equality problem

def assembly : Core.AtomContextAssembly problem semantics where
  Interface := Unit
  Site := fun _ => Unit
  interface := fun _ _ => ()
  Atom := fun _ => Nat
  Context := fun _ => Nat
  compatible := fun _ _ => True
  atom := fun object _ => object
  context := fun _ _ => 0
  assemble := fun atom context => atom + context
  extractedCompatible := fun _ _ => trivial
  reconstruct := fun object _ => Nat.add_zero object

abbrev Input := Core.Strategy.ProblemInput problem
abbrev Root := Core.Residual.Ledger Input

def input : Input where
  object := (7 : Nat)
  baseline := trivial
  branchState := ()

def atomRegistration :
    Core.Strategy.AtomContextObstructionDichotomy.Registration
      problem Input where
  semantics := semantics
  assembly := assembly
  object := fun residual => residual.object
  site := fun _ => ()
  AtomLocal := fun _ => Unit
  atomRepresented := fun _ => ()
  ContextLocal := fun _ => Unit
  contextRepresented := fun _ => ()
  AtomObstruction := fun _ _ => True
  ContextObstruction := fun _ _ => False
  atomDecidable := fun _ => .isTrue trivial
  contextOfAtomFailure := fun _ absent => absent trivial

def contextRegistration :
    Core.Strategy.AtomContextObstructionDichotomy.Registration
      problem Input where
  semantics := semantics
  assembly := assembly
  object := fun residual => residual.object
  site := fun _ => ()
  AtomLocal := fun _ => Unit
  atomRepresented := fun _ => ()
  ContextLocal := fun _ => Unit
  contextRepresented := fun _ => ()
  AtomObstruction := fun _ _ => False
  ContextObstruction := fun _ _ => True
  atomDecidable := fun _ => .isFalse id
  contextOfAtomFailure := fun _ _ => trivial

def atomProfile : Profile problem Root Input where
  registration := atomRegistration

def contextProfile : Profile problem Root Input where
  registration := contextRegistration

def atomProfileAt (Previous : Type)
    [Core.Residual.HasResidual Previous Input] :
    Profile problem Previous Input where
  registration := atomRegistration

def contextProfileAt (Previous : Type)
    [Core.Residual.HasResidual Previous Input] :
    Profile problem Previous Input where
  registration := contextRegistration

def atomRoot : Root := Core.Residual.Ledger.initial input
def contextRoot : Root := Core.Residual.Ledger.initial input

def atomBranch :=
  Core.Strategy.runDichotomy atomProfile.dichotomy atomRoot

def contextBranch :=
  Core.Strategy.runDichotomy contextProfile.dichotomy contextRoot

def atomStage : atomProfile.dichotomy.LeftStage :=
  match atomBranch with
  | .inl stage => stage
  | .inr stage => False.elim stage.added.obstruction

def contextStage : contextProfile.dichotomy.RightStage :=
  match contextBranch with
  | .inl stage => False.elim stage.added.obstruction
  | .inr stage => stage

theorem atom_selected : atomBranch = .inl atomStage :=
  rfl

theorem context_selected : contextBranch = .inr contextStage :=
  rfl

theorem atom_latest_is_selected :
    (Core.Residual.Query.latest.read atomStage) = atomStage.added :=
  rfl

theorem context_latest_is_selected :
    (Core.Residual.Query.latest.read contextStage) = contextStage.added :=
  rfl

theorem atom_literal_predecessor : atomStage.previous = atomRoot :=
  rfl

theorem context_literal_predecessor : contextStage.previous = contextRoot :=
  rfl

theorem atom_exact_decomposition :
    atomStage.added.decomposition =
      atomProfile.exactDecomposition atomRoot :=
  rfl

theorem context_exact_decomposition :
    contextStage.added.decomposition =
      contextProfile.exactDecomposition contextRoot :=
  rfl

def target : Core.Target problem where
  Predicate := fun n : Nat => n = n + 1
  Statement := ∀ n : Nat, n = n + 1
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def atomDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun residual => .isFalse (by
      intro equality
      simp only [target, problem] at equality
      omega)
    atomContextObstructionDichotomies := [{
      registration := atomRegistration
      metadata := { name := "neutral atom--context dichotomy" }
      atomMetadata := { name := "atom obstruction" }
      contextMetadata := { name := "context obstruction" }
    }]
  }

def contextDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun residual => .isFalse (by
      intro equality
      simp only [target, problem] at equality
      omega)
    atomContextObstructionDichotomies := [{
      registration := contextRegistration
      metadata := { name := "neutral atom--context dichotomy" }
      atomMetadata := { name := "atom obstruction" }
      contextMetadata := { name := "context obstruction" }
    }]
  }

instance : NeZero atomDefinition.data.atomContextObstructionDichotomies.length :=
  ⟨by simp [atomDefinition]⟩

instance :
    NeZero contextDefinition.data.atomContextObstructionDichotomies.length :=
  ⟨by simp [contextDefinition]⟩

noncomputable def atomProgram : Program atomDefinition.data :=
  Program.ofBlueprint (
    (Blueprint.root : Blueprint atomDefinition.data .authoring)
      |>.atomContextObstructionDichotomy)

noncomputable def contextProgram : Program contextDefinition.data :=
  Program.ofBlueprint (
    (Blueprint.root : Blueprint contextDefinition.data .authoring)
      |>.atomContextObstructionDichotomy)

noncomputable def atomReduction : ReductionDeclaration.{0, 0, 0} :=
  reduceDag% atomDefinition atomProgram

noncomputable def contextReduction : ReductionDeclaration.{0, 0, 0} :=
  reduceDag% contextDefinition contextProgram

example :
    atomReduction.report.path =
      [.atomContextObstructionDichotomy 0] :=
  rfl

example :
    contextReduction.report.path =
      [.atomContextObstructionDichotomy 0] :=
  rfl

example : atomReduction.report.checksBound = 1 :=
  rfl

example : atomReduction.report.workBound = 1 :=
  rfl

example : contextReduction.report.checksBound = 1 :=
  rfl

example : contextReduction.report.workBound = 1 :=
  rfl

example : (atomReduction.outcome input).isRight = true :=
  rfl

example : (contextReduction.outcome input).isRight = true :=
  rfl

theorem atom_compiled_selects_atom :
    match atomReduction.outcome input with
    | .inl _ => False
    | .inr live =>
        match live.stage.added.snd with
        | .inl payload =>
            payload.down.decomposition =
              (atomProfileAt _).exactDecomposition live.stage.previous
        | .inr _ => False := by
  rfl

theorem context_compiled_selects_context :
    match contextReduction.outcome input with
    | .inl _ => False
    | .inr live =>
        match live.stage.added.snd with
        | .inl _ => False
        | .inr payload =>
            payload.down.decomposition =
              (contextProfileAt _).exactDecomposition live.stage.previous := by
  rfl

theorem atom_compiled_latest :
    match atomReduction.outcome input with
    | .inl _ => True
    | .inr live =>
        Core.Residual.Query.latest.read live.stage.toLedger =
          live.stage.added := by
  rfl

theorem context_compiled_latest :
    match contextReduction.outcome input with
    | .inl _ => True
    | .inr live =>
        Core.Residual.Query.latest.read live.stage.toLedger =
          live.stage.added := by
  rfl

noncomputable def atomJson : Lean.Json :=
  atomReduction.report.traceJson

noncomputable def contextJson : Lean.Json :=
  contextReduction.report.traceJson

example : atomJson.getObjValAs? String "schema_version" = .ok "2.3.0" := by
  decide

example : contextJson.getObjValAs? String "schema_version" = .ok "2.3.0" := by
  decide

#check atomReduction.report.statement
#check contextReduction.report.statement
#check atomReduction.report.checksBound
#check contextReduction.report.workBound

#print axioms atom_selected
#print axioms context_selected
#print axioms atom_latest_is_selected
#print axioms context_latest_is_selected
#print axioms atom_exact_decomposition
#print axioms context_exact_decomposition
#print axioms atom_compiled_selects_atom
#print axioms context_compiled_selects_context
#print axioms atom_compiled_latest
#print axioms context_compiled_latest

end Hypostructure.Fixtures.AtomContextObstructionDichotomy
