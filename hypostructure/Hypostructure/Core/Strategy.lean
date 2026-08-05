import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Problem
import Hypostructure.Core.Strategy.Data
import Hypostructure.Core.Strategy.WellFoundedCompression
import Hypostructure.Core.Strategy.RankForcing
import Hypostructure.Core.Residual.Ledger
import Hypostructure.Core.Budget.Dynamic
import Hypostructure.Core.Strategy.Execution

/-!
# Reusable strategy contracts

A strategy is a typed composition boundary above individual CTs.  Core owns
the terminal family, predecessor preservation, and composition shape.  The
domain supplies only schedules, observations, budgets, and semantic transfer
facts through the contract fields.
-/

namespace Hypostructure.Core.Strategy

universe uPrevious uTerminal uPayload uLeft uRight uItem uValue uCode

open Hypostructure.Core.Residual

/-! ## Problem initialization

The application boundary supplies only a Core problem and one theorem input.
`ProblemInput` lives in the dependency-light
`Hypostructure.Core.Strategy.ProblemInput` module; `InitStage` and
`InitStrategy` live in `Hypostructure.Core.Strategy.Data` with the registered
strategy data. All later strategies receive the initial stage through the
ordinary composition API.
-/

/-! ## Target-closed strategy programs

This is the generic endpoint for a composed strategy.  The program owns its
execution stage and proves target realization from the literal residual carried
by that stage.  Core does not inspect or manufacture the stage payload; it
only exposes the target theorem bridge. -/

structure TargetProgram (P : Core.Problem) (T : Core.Target P) where
  Stage : Type uPrevious
  [stageResidual : HasResidual Stage (ProblemInput P)]
  branchState : forall object, P.BranchState object
  run : ProblemInput P -> Stage
  object_preserved : forall input,
    (residualOf (run input)).object = input.object
  target : forall input,
    T.Predicate (residualOf (run input)).object

theorem TargetProgram.statement
    (program : TargetProgram P T) : T.Statement := by
  apply T.target_to_statement
  intro object baseline
  let input : ProblemInput P :=
    { object := object
      baseline := baseline
      branchState := program.branchState object }
  simpa [program.object_preserved input] using program.target input

/-! ## Unconditional target-or-terminal-residual results

Every strategy run is an unconditional theorem: it returns either a certified
target or the exact typed terminal residual emitted by the strategy DAG. The
residual depends on the literal final stage and cannot be detached, replaced,
or supplied by application code. -/

structure TargetReduction (P : Core.Problem) (T : Core.Target P) where
  private mk ::
  Stage : Type uPrevious
  [stageResidual : HasResidual Stage (ProblemInput P)]
  TerminalResidual : Stage -> Type uPayload
  branchState : forall object, P.BranchState object
  run : (input : ProblemInput P) -> Ledger.Extension Stage (fun stage =>
    Sum (PLift (T.Predicate (residualOf stage).object))
      (TerminalResidual stage))
  object_preserved : forall input,
    (residualOf (run input).previous).object = input.object

/-- Public output-side name for a strategy reduction.  Every execution exposes
either a certified target or the exact residual that still needs a consumer. -/
abbrev OutputStrategy (P : Core.Problem) (T : Core.Target P) :=
  TargetReduction P T

/-- A framework-owned executable strategy chain.  Its representation has a
private constructor, so application modules can only obtain a value through
Core strategy composition and terminal constructors. -/
abbrev Chain (P : Core.Problem) (T : Core.Target P) :=
  OutputStrategy P T

/-- Lift a target-closed program into the output protocol.  A closed program
has no remaining residual, so its output is always the target side and no
later continuation is evaluated. -/
def TargetProgram.toOutputStrategy
    (program : TargetProgram P T) : OutputStrategy P T where
  Stage := program.Stage
  stageResidual := program.stageResidual
  TerminalResidual := fun _ => Empty
  branchState := program.branchState
  run input := Ledger.extend (program.run input) (Sum.inl ⟨program.target input⟩)
  object_preserved := program.object_preserved

def OutputStrategy.output
    (strategy : OutputStrategy P T) (input : ProblemInput P) :=
  (strategy.run input).added

theorem OutputStrategy.unconditional
    (strategy : OutputStrategy P T)
    (target_case : forall input,
      ∃ proof : PLift (T.Predicate
        (@residualOf strategy.Stage (ProblemInput P)
          strategy.stageResidual (strategy.run input).previous).object),
        strategy.output input = Sum.inl proof) :
    T.Statement := by
  apply T.target_to_statement
  intro object baseline
  let input : ProblemInput P :=
    { object := object
      baseline := baseline
      branchState := strategy.branchState object }
  rcases target_case input with ⟨proof, _equality⟩
  have certified := proof.down
  rw [strategy.object_preserved input] at certified
  simpa using certified

/-- Empty residual families close automatically.  The application supplies no
outcome classifier; Core eliminates the impossible residual alternative from
the final ledger entry. -/
theorem OutputStrategy.unconditional_of_isEmpty
    (strategy : OutputStrategy P T)
    [empty : forall stage, IsEmpty (strategy.TerminalResidual stage)] :
    T.Statement := by
  apply strategy.unconditional
  intro input
  cases output : strategy.output input with
  | inl proof => exact ⟨proof, rfl⟩
  | inr residual => exact isEmptyElim residual

/-- Run a reduction to its earliest unconditional boundary.  If every input
reaches the target side, the result is the target theorem and no continuation
is needed.  Otherwise the result contains an input and the exact residual
produced by that run. -/
noncomputable def OutputStrategy.closeOrResidual
    (strategy : OutputStrategy P T) :
    Sum (PLift T.Statement)
      (Sigma fun input =>
        Sigma fun residual : strategy.TerminalResidual
            (strategy.run input).previous =>
          PLift (strategy.output input = Sum.inr residual)) := by
  classical
  by_cases h : forall input,
      ∃ proof : PLift (T.Predicate
        (@residualOf strategy.Stage (ProblemInput P)
          strategy.stageResidual (strategy.run input).previous).object),
        strategy.output input = Sum.inl proof
  · exact Sum.inl ⟨OutputStrategy.unconditional strategy h⟩
  · push Not at h
    let input := Classical.choose h
    have notTarget := Classical.choose_spec h
    cases output : strategy.output input with
    | inl proof =>
        exact False.elim (notTarget proof (by simpa [output]))
    | inr residual =>
        exact Sum.inr ⟨input, residual, ⟨output⟩⟩

/-- Runner-facing diagnostic projection. This does not execute or transform
the strategy; it only inspects the Core-defined output boundary to report the
earliest unconditional target theorem or exact terminal residual. -/
abbrev OutputDiagnostics (strategy : OutputStrategy P T) :=
  Sum (PLift T.Statement)
    (Sigma fun input =>
      Sigma fun residual : strategy.TerminalResidual
          (strategy.run input).previous =>
        PLift (strategy.output input = Sum.inr residual))

noncomputable def OutputStrategy.diagnose
    (strategy : OutputStrategy P T) : OutputDiagnostics strategy :=
  strategy.closeOrResidual

/-! ## Hypostructure runner

The runner is the application-independent end-to-end boundary.  An
instantiation supplies one problem, its target contract, and one composed
strategy.  Execution remains the strategy's ordinary output; diagnostics are
an additional runner-side projection and never alter the strategy chain. -/

structure Hypostructure.{uAmbient, uBranch, uRunnerStage, uRunnerPayload} where
  Problem : Core.Problem.{uAmbient, uBranch}
  Target : Core.Target Problem
  strategy : Chain.{uAmbient, uBranch, uRunnerStage, uRunnerPayload}
    Problem Target

/-- Internal compiled declaration consumed by the low-level runner.  Public
applications use `Strategy.Dag.ProblemDeclaration`, whose DAG is lowered to
this representation exclusively by Core. -/
structure CompiledDeclaration.{uAmbient, uBranch, uRunnerStage, uRunnerPayload} where
  problem : Core.Problem.{uAmbient, uBranch}
  target : Core.Target problem
  strategy : Chain.{uAmbient, uBranch, uRunnerStage, uRunnerPayload}
    problem target

def Hypostructure.ofDeclaration
    (declaration : CompiledDeclaration) :
    Hypostructure where
  Problem := declaration.problem
  Target := declaration.target
  strategy := declaration.strategy

def CompiledDeclaration.hypostructure
    (declaration : CompiledDeclaration) :
    Hypostructure :=
  Hypostructure.ofDeclaration declaration

def CompiledDeclaration.run
    (declaration : CompiledDeclaration)
    (input : ProblemInput declaration.problem) :=
  declaration.strategy.output input

noncomputable def CompiledDeclaration.diagnose
    (declaration : CompiledDeclaration) :=
  declaration.strategy.diagnose

theorem CompiledDeclaration.unconditional
    (declaration : CompiledDeclaration)
    (target_case : forall input,
      ∃ proof : PLift (declaration.target.Predicate
        (@residualOf declaration.strategy.Stage
          (ProblemInput declaration.problem)
          declaration.strategy.stageResidual
          (declaration.strategy.run input).previous).object),
        declaration.strategy.output input = Sum.inl proof) :
    declaration.target.Statement :=
  OutputStrategy.unconditional declaration.strategy target_case

def Hypostructure.run (program : Hypostructure) :=
  program.strategy.output

noncomputable def Hypostructure.diagnose (program : Hypostructure) :=
  program.strategy.diagnose

theorem Hypostructure.unconditional
    (program : Hypostructure)
    (target_case : forall input,
      ∃ proof : PLift (program.Target.Predicate
        (@residualOf program.strategy.Stage
          (ProblemInput program.Problem)
          program.strategy.stageResidual
          (program.strategy.run input).previous).object),
        program.strategy.output input = Sum.inl proof) :
    program.Target.Statement :=
  OutputStrategy.unconditional program.strategy target_case

/-- A strategy output indexed by its terminal.  The payload is dependent on
the literal predecessor and terminal, so branches cannot exchange data. -/
structure Contract (Previous : Type uPrevious) where
  Terminal : Type uTerminal
  Payload : Previous -> Terminal -> Type uPayload
  produce : (previous : Previous) -> Sigma (Payload previous)
  /-- Every predecessor receives an actual terminal payload. -/
  exhaustive : (previous : Previous) -> Nonempty (Sigma (Payload previous))

/-! ## Domain-neutral dichotomy

The two outcomes are deliberately unnamed.  An application may give them
domain-specific labels, but Core only sees two predecessor-indexed payloads.
This keeps classification and ledger routing in the framework while leaving
mathematical meaning to the application contract.
-/

inductive DichotomyTerminal where
  | left
  | right
  deriving DecidableEq, Repr

structure Dichotomy (Previous : Type uPrevious) where
  LeftPayload : Previous -> Type uLeft
  RightPayload : Previous -> Type uRight
  classify : (previous : Previous) ->
    Sum (LeftPayload previous) (RightPayload previous)

structure ClosedDichotomy (Previous : Type uPrevious) where
  LeftPayload : Previous -> Type uLeft
  RightPayload : Previous -> Type uRight
  classify : (previous : Previous) ->
    Sum (LeftPayload previous) (RightPayload previous)
  leftClosed : (previous : Previous) -> LeftPayload previous -> Prop
  rightClosed : (previous : Previous) -> RightPayload previous -> Prop
  leftProof : (previous : Previous) ->
    match classify previous with
    | Sum.inl payload => leftClosed previous payload
    | Sum.inr _ => True
  rightProof : (previous : Previous) ->
    match classify previous with
    | Sum.inl _ => True
    | Sum.inr payload => rightClosed previous payload

/-- A proposition carried as ordinary strategy data for finite routing. -/
abbrev ProofPayload (proposition : Prop) : Type := PLift proposition

def proofPayload (proof : proposition) : ProofPayload proposition :=
  ⟨proof⟩

def ClosedDichotomy.toDichotomy (strategy : ClosedDichotomy Previous) :
    Dichotomy Previous where
  LeftPayload := strategy.LeftPayload
  RightPayload := strategy.RightPayload
  classify := strategy.classify

theorem ClosedDichotomy.closed (strategy : ClosedDichotomy Previous)
    (previous : Previous) :
    match strategy.classify previous with
    | Sum.inl payload => strategy.leftClosed previous payload
    | Sum.inr payload => strategy.rightClosed previous payload := by
  cases h : strategy.classify previous with
  | inl payload =>
      simpa [h] using strategy.leftProof previous
  | inr payload =>
      simpa [h] using strategy.rightProof previous

/-! ## Routed continuation strategies

One dichotomy has one literal predecessor ledger and two possible typed
extensions of it.  The selected branch witness is appended before its
continuation is instantiated, so left-only and right-only facts cannot be
mixed. -/

/-- The exact ledger stage entering the left continuation. -/
abbrev Dichotomy.LeftStage (split : Dichotomy Previous) :=
  Ledger.Extension Previous split.LeftPayload

/-- The exact ledger stage entering the right continuation. -/
abbrev Dichotomy.RightStage (split : Dichotomy Previous) :=
  Ledger.Extension Previous split.RightPayload

abbrev RoutedLeft (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (previous : Previous) : Type _ :=
  Sigma (fun witness : split.LeftPayload previous =>
    Sigma ((left (Ledger.extend previous witness)).Payload
      (Ledger.extend previous witness)))

abbrev RoutedRight (split : Dichotomy Previous)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (previous : Previous) : Type _ :=
  Sigma (fun witness : split.RightPayload previous =>
    Sigma ((right (Ledger.extend previous witness)).Payload
      (Ledger.extend previous witness)))

/-/ The canonical dependent join produced by a routed dichotomy.  Keeping this
type alias public prevents applications from reconstructing branch sums or
copying branch witnesses by hand. -/
abbrev RoutedJoin (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (previous : Previous) : Type _ :=
  Sum (RoutedLeft split left previous) (RoutedRight split right previous)

def runRouted
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (previous : Previous) :
    Ledger.Extension Previous (RoutedJoin split left right) :=
  Ledger.extend previous (match split.classify previous with
    | Sum.inl witness =>
        let stage := Ledger.extend previous witness
        Sum.inl ⟨witness, (left stage).produce stage⟩
    | Sum.inr witness =>
        let stage := Ledger.extend previous witness
        Sum.inr ⟨witness, (right stage).produce stage⟩)

/-- Execute a bare dichotomy into exactly one of its two branch-aware ledger
stages.  Both alternatives retain the same literal predecessor; only the
selected witness is appended. -/
def runDichotomy (strategy : Dichotomy Previous) (previous : Previous) :
    Sum strategy.LeftStage strategy.RightStage :=
  match strategy.classify previous with
  | .inl witness => .inl (Ledger.extend previous witness)
  | .inr witness => .inr (Ledger.extend previous witness)

@[simp] theorem runDichotomy_previous
    (strategy : Dichotomy Previous) (previous : Previous) :
    (runDichotomy strategy previous).elim
      (fun stage => stage.previous) (fun stage => stage.previous) = previous := by
  cases h : strategy.classify previous <;> simp [runDichotomy, h]

/-- The predecessor-preserving stage type produced by a dichotomy. -/
abbrev DichotomyStage (strategy : Dichotomy Previous) :=
  Sum strategy.LeftStage strategy.RightStage

abbrev DichotomyPayload (strategy : Dichotomy Previous)
    (previous : Previous) : DichotomyTerminal -> Type (max uLeft uRight)
  | .left => strategy.LeftPayload previous
  | .right => strategy.RightPayload previous

noncomputable def dichotomyContract (strategy : Dichotomy Previous) :
    Contract Previous where
  Terminal := DichotomyTerminal
  Payload := DichotomyPayload strategy
  produce previous := match strategy.classify previous with
    | Sum.inl payload => ⟨.left, payload⟩
    | Sum.inr payload => ⟨.right, payload⟩
  exhaustive previous := ⟨match strategy.classify previous with
    | Sum.inl payload => ⟨.left, payload⟩
    | Sum.inr payload => ⟨.right, payload⟩⟩

/-- The one-extension execution owned by every strategy contract. -/
def run {Previous : Type uPrevious} (contract : Contract Previous)
    (previous : Previous) :
    Ledger.Extension Previous (fun stage => Sigma (contract.Payload stage)) :=
  Ledger.extend previous (contract.produce previous)

/-! ## Compiled halting programs

A halting program is the runner-owned execution object produced by the
private strategy compiler.  `output` is decided vertex by vertex: once the
run is on the target side, later vertices are skipped (their contracts are
never evaluated) and the target certificate is carried forward unchanged.
The constructor is private, so a program can only be obtained from
`HaltingProgram.root` (which consults the registered target decision
procedure once, before vertex 0) and `HaltingProgram.snoc` (which applies
one resolved contract to the literal current stage and re-derives the
output from the contract's literal product). -/

universe uRunnerStage uAmbient uBranch uData

/-- A literal ledger extension that is live precisely because the appended
payload did not certify the target.  Its constructor is private; only Core's
halting execution may produce one. -/
structure HaltingProgram.LiveExtension
    {P : Core.Problem.{uAmbient, uBranch}} (T : Core.Target P)
    (Previous : Type uRunnerStage)
    [HasResidual Previous (ProblemInput P)]
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))) where
  private mk ::
  ledger : Ledger.Extension Previous
    (fun stage => Sigma (contract.Payload stage))
  isLive : certify ledger.previous ledger.added = none
  produced : ledger.added = contract.produce ledger.previous

def HaltingProgram.LiveExtension.previous
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    (live : HaltingProgram.LiveExtension T Previous contract certify) :
    Previous :=
  live.ledger.previous

def HaltingProgram.LiveExtension.added
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    (live : HaltingProgram.LiveExtension T Previous contract certify) :
    Sigma (contract.Payload live.previous) :=
  live.ledger.added

def HaltingProgram.LiveExtension.toLedger
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    (live : HaltingProgram.LiveExtension T Previous contract certify) :
    Ledger.Extension Previous (fun stage => Sigma (contract.Payload stage)) :=
  live.ledger

/-- Read the exact payload appended by the contract at this live stage.  The
query is the ordinary newest-entry query pulled back along `toLedger`; the
`produced` law below identifies it with the contract's unique producer. -/
def HaltingProgram.LiveExtension.producedQuery
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))} :
    Query (HaltingProgram.LiveExtension T Previous contract certify)
      (fun live => Sigma (contract.Payload live.previous)) :=
  (Query.latest (Previous := Previous)
    (Added := fun stage => Sigma (contract.Payload stage))).comap
      HaltingProgram.LiveExtension.toLedger

@[simp] theorem HaltingProgram.LiveExtension.read_producedQuery
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    (live : HaltingProgram.LiveExtension T Previous contract certify) :
    (HaltingProgram.LiveExtension.producedQuery
      (T := T) (contract := contract) (certify := certify)) live =
      contract.produce live.previous :=
  live.produced

instance {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))} :
    HasResidual (HaltingProgram.LiveExtension T Previous contract certify)
      (ProblemInput P) where
  residual live := residualOf live.previous

/-- Canonical transport of an inherited query through a live compiled step:
first preserve it through the literal ledger extension, then pull it back
through the framework-owned live-stage projection. -/
def HaltingProgram.LiveExtension.preserveQuery
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {certify : (stage : Previous) → Sigma (contract.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    {Result : Previous → Sort uData}
    (query : Query Previous Result) :
    Query (HaltingProgram.LiveExtension T Previous contract certify)
      (fun live => Result live.previous) :=
  (query.preserve
    (Added := fun stage => Sigma (contract.Payload stage))).comap
      HaltingProgram.LiveExtension.toLedger

/-- Exact live execution state.  The stage and its terminal payload are
dependent, and residual preservation travels with that same stage. -/
structure HaltingProgram.OpenResult
    (P : Core.Problem.{uAmbient, uBranch})
    (Stage : Type uRunnerStage) [HasResidual Stage (ProblemInput P)]
    (TerminalResidual : Stage → Type uRunnerStage)
    (input : ProblemInput P) where
  stage : Stage
  residual_eq : residualOf stage = input
  terminal : TerminalResidual stage

structure HaltingProgram (P : Core.Problem.{uAmbient, uBranch})
    (T : Core.Target P) where
  private mk ::
  /-- The exact family of stages on which another contract may run.  Closed
  executions have no inhabitant of this family. -/
  Stage : Type uRunnerStage
  [stageResidual : HasResidual Stage (ProblemInput P)]
  TerminalResidual : Stage -> Type uRunnerStage
  execute : (input : ProblemInput P) ->
    Sum (PLift (T.Predicate input.object))
      (HaltingProgram.OpenResult P Stage TerminalResidual input)

instance (program : HaltingProgram P T) :
    HasResidual program.Stage (ProblemInput P) :=
  program.stageResidual

/-- The empty compiled program.  No strategy has run, so it returns the
untouched initial residual.  In particular, the root does not consult a
problem-owned target decision procedure and can never close a proof before
the first registered DAG vertex executes. -/
def HaltingProgram.root {P : Core.Problem.{uAmbient, uBranch}}
    {T : Core.Target P}
    (_data : Core.StrategyData.{uAmbient, uBranch, uData} P T) :
    HaltingProgram.{max uAmbient uBranch uData} P T where
  Stage := ULift.{max uAmbient uBranch uData} (Ledger (ProblemInput P))
  stageResidual := { residual := fun stage => residualOf stage.down }
  TerminalResidual := fun _ =>
    ULift.{max uAmbient uBranch uData} (ProblemInput P)
  execute input := by
    letI : HasResidual
        (ULift.{max uAmbient uBranch uData} (Ledger (ProblemInput P)))
        (ProblemInput P) :=
      { residual := fun stage => residualOf stage.down }
    exact Sum.inr
      { stage := ULift.up (Ledger.initial input)
        residual_eq := rfl
        terminal := ULift.up input }

/-- A compiled program is closed exactly when its own execution reaches the
target side for every theorem input.  This is an execution property, not an
application-supplied theorem about the target. -/
def HaltingProgram.Closes
    (program : HaltingProgram.{uRunnerStage} P T) : Prop :=
  ∀ input : ProblemInput P, (program.execute input).isLeft = true

/-- The one-step execution derivation for an extended program.  A closed
execution carries no stage.  A live execution contains the exact ledger
extension produced by the contract, with no optional or sum wrapper around
its payload. -/
private def HaltingProgram.snocStep {P : Core.Problem} {T : Core.Target P}
    (program : HaltingProgram.{uRunnerStage} P T)
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) -> Sigma (contract.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object)))
    (input : ProblemInput P) :
    Sum (PLift (T.Predicate input.object))
      (HaltingProgram.OpenResult P
        (HaltingProgram.LiveExtension T program.Stage contract certify)
        (fun stage => Sigma (contract.Payload stage.previous)) input) :=
  match program.execute input with
  | Sum.inl proof => Sum.inl proof
  | Sum.inr live =>
      let stage := live.stage
      let payload := contract.produce stage
      match rejected : certify stage payload with
      | some proof =>
          Sum.inl ⟨by
            have target := proof.down
            rw [live.residual_eq] at target
            exact target⟩
      | none =>
          Sum.inr
            { stage :=
                HaltingProgram.LiveExtension.mk
                  (Ledger.extend stage payload) rejected rfl
              residual_eq := live.residual_eq
              terminal := payload }

/-- Append one resolved vertex.  On the target side the existing target
certificate is retained and the contract is never evaluated.  On the live
side the ledger is extended with the exact closed-or-live result of the
contract: if `certify` extracts a target certificate the run closes here,
otherwise the literal added payload is the new terminal residual. -/
def HaltingProgram.snoc {P : Core.Problem} {T : Core.Target P}
    (program : HaltingProgram.{uRunnerStage} P T)
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) -> Sigma (contract.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object))) :
    HaltingProgram.{uRunnerStage} P T where
  Stage := HaltingProgram.LiveExtension T program.Stage contract certify
  TerminalResidual := fun stage => Sigma (contract.Payload stage.previous)
  execute input := HaltingProgram.snocStep program contract certify input

/-- Append one dependent continuation only to the live arm of a compiled
program.  This is the reusable DAG-composition boundary: the continuation is
typed over the predecessor program's exact open stage, target executions are
retained unchanged by `snocStep`, and a surviving result is the canonical
`LiveExtension` carrying the literal ledger addition and its non-certification
proof.  Inherited facts must be transported with
`LiveExtension.preserveQuery`. -/
def HaltingProgram.bindLive {P : Core.Problem} {T : Core.Target P}
    (program : HaltingProgram.{uRunnerStage} P T)
    (continuation :
      Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) ->
      Sigma (continuation.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object))) :
    HaltingProgram.{uRunnerStage} P T :=
  program.snoc continuation certify

/-- `bindLive` uses the existing halting execution verbatim; it introduces no
alternate executor or fallback path. -/
@[simp] theorem HaltingProgram.bindLive_execute
    {P : Core.Problem} {T : Core.Target P}
    (program : HaltingProgram.{uRunnerStage} P T)
    (continuation :
      Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) ->
      Sigma (continuation.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object)))
    (input : ProblemInput P) :
    (program.bindLive continuation certify).execute input =
      (program.snoc continuation certify).execute input :=
  rfl

/-- Exact target-closing result of the first contract in a live composition. -/
structure HaltingProgram.FirstClosedPayload
    {P : Core.Problem} (T : Core.Target P)
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (previous : Previous) where
  payload : Sigma (first.Payload previous)
  proof : PLift (T.Predicate (residualOf previous).object)
  certified : firstCertify previous payload = some proof

/-- Exact two-step live result.  The first payload is retained by the
`LiveExtension`; the second is appended through the ordinary ledger API. -/
structure HaltingProgram.LiveContinuationPayload
    {P : Core.Problem} (T : Core.Target P)
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (previous : Previous) where
  stage : Ledger.Extension
    (HaltingProgram.LiveExtension T Previous first firstCertify)
    (fun live => Sigma (second.Payload live))
  previous_eq : stage.previous.previous = previous
  produced : stage.added = second.produce stage.previous

/-- A sealed Core composition of two contracts across an exact live boundary.
Its private constructor prevents callers from replacing execution or
certification while exposing the ordinary composed contract and projection
needed by the DAG compiler. -/
structure HaltingProgram.LiveContractComposition
    {P : Core.Problem} (T : Core.Target P)
    (Previous : Type uRunnerStage)
    [HasResidual Previous (ProblemInput P)] where
  private mk ::
  contract : Contract.{uRunnerStage, 0, uRunnerStage} Previous
  certify : (stage : Previous) → Sigma (contract.Payload stage) →
    Option (PLift (T.Predicate (residualOf stage).object))

/-- Compose two contracts without evaluating the continuation on a
target-closing first result.  In the live arm Core constructs the certified
`LiveExtension`, executes the second contract there, and retains both literal
payloads in the resulting ledger chain. -/
def HaltingProgram.composeLiveContracts
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (secondCertify :
      (stage : HaltingProgram.LiveExtension T Previous first firstCertify) →
      Sigma (second.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))) :
    HaltingProgram.LiveContractComposition T Previous where
  contract := {
    Terminal := PUnit
    Payload := fun previous _ =>
      Sum
        (HaltingProgram.FirstClosedPayload T first firstCertify previous)
        (HaltingProgram.LiveContinuationPayload T first firstCertify
          second previous)
    produce := fun previous =>
      let firstPayload := first.produce previous
      match rejected : firstCertify previous firstPayload with
      | some proof =>
          ⟨PUnit.unit, Sum.inl
            { payload := firstPayload
              proof
              certified := rejected }⟩
      | none =>
          let live :=
            HaltingProgram.LiveExtension.mk
              (Ledger.extend previous firstPayload) rejected rfl
          let secondPayload := second.produce live
          ⟨PUnit.unit, Sum.inr
            { stage := Ledger.extend live secondPayload
              previous_eq := rfl
              produced := rfl }⟩
    exhaustive := fun previous => ⟨
      let firstPayload := first.produce previous
      match rejected : firstCertify previous firstPayload with
      | some proof =>
          ⟨PUnit.unit, Sum.inl
            { payload := firstPayload
              proof
              certified := rejected }⟩
      | none =>
          let live :=
            HaltingProgram.LiveExtension.mk
              (Ledger.extend previous firstPayload) rejected rfl
          let secondPayload := second.produce live
          ⟨PUnit.unit, Sum.inr
            { stage := Ledger.extend live secondPayload
              previous_eq := rfl
              produced := rfl }⟩⟩
  }
  certify := fun previous payload =>
    match payload.snd with
    | Sum.inl closed => some closed.proof
    | Sum.inr continued =>
        match secondCertify continued.stage.previous continued.stage.added with
        | none => none
        | some proof =>
            some ⟨by
              have target := proof.down
              have residual_eq :
                  residualOf continued.stage.previous =
                    residualOf previous := by
                change residualOf continued.stage.previous.previous =
                  residualOf previous
                rw [continued.previous_eq]
              rw [residual_eq] at target
              exact target⟩

/-- Early-stop projection law: every exact first-step closure is retained as
the composed target certificate.  The producer can construct this payload
only from the `some` arm of the first certifier. -/
theorem HaltingProgram.composeLiveContracts_earlyStop
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (secondCertify :
      (stage : HaltingProgram.LiveExtension T Previous first firstCertify) →
      Sigma (second.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (previous : Previous)
    (closed : HaltingProgram.FirstClosedPayload T first firstCertify previous) :
    let composition :=
      HaltingProgram.composeLiveContracts first firstCertify second secondCertify
    composition.certify previous ⟨PUnit.unit, Sum.inl closed⟩ =
      some closed.proof :=
  rfl

/-- Literal predecessor law for every surviving composed payload. -/
theorem HaltingProgram.LiveContinuationPayload.previous_preserved
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {first : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    {second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify)}
    {previous : Previous}
    (continued : HaltingProgram.LiveContinuationPayload T first firstCertify
      second previous) :
    continued.stage.previous.previous = previous :=
  continued.previous_eq

/-- A second-step payload can exist only on the exact `none` arm of the first
certifier. -/
theorem HaltingProgram.LiveContinuationPayload.first_isLive
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {first : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    {second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify)}
    {previous : Previous}
    (continued : HaltingProgram.LiveContinuationPayload T first firstCertify
      second previous) :
    firstCertify continued.stage.previous.previous
        continued.stage.previous.added = none :=
  continued.stage.previous.isLive

/-- Residual preservation follows from the literal predecessor retained by
the two ordinary ledger extensions. -/
theorem HaltingProgram.LiveContinuationPayload.residual_preserved
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    {first : Contract.{uRunnerStage, 0, uRunnerStage} Previous}
    {firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object))}
    {second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify)}
    {previous : Previous}
    (continued : HaltingProgram.LiveContinuationPayload T first firstCertify
      second previous) :
    residualOf continued.stage = residualOf previous := by
  change residualOf continued.stage.previous.previous = residualOf previous
  rw [continued.previous_eq]

/-- Construct the literal live second-stage extension together with its
residual-preservation law.  Keeping the projection and its dependent law in
one sealed result prevents downstream code from reconstructing provenance by
unfolding the composition. -/
private def
    HaltingProgram.LiveContractComposition.liveContinuationWithResidual
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (secondCertify :
      (stage : HaltingProgram.LiveExtension T Previous first firstCertify) →
      Sigma (second.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (live :
      let composition :=
        HaltingProgram.composeLiveContracts first firstCertify
          second secondCertify
      HaltingProgram.LiveExtension T Previous
        composition.contract composition.certify) :
    { continuation :
        HaltingProgram.LiveExtension T
          (HaltingProgram.LiveExtension T Previous first firstCertify)
          second secondCertify //
      continuation.toLedger.previous.toLedger.previous =
          live.toLedger.previous ∧
        residualOf continuation = residualOf live } := by
  let composition :=
    HaltingProgram.composeLiveContracts first firstCertify second secondCertify
  rcases live with ⟨ledger, isLive, _produced⟩
  rcases ledger with ⟨previous, ⟨terminal, closed | continued⟩⟩
  · cases terminal
    simp [HaltingProgram.composeLiveContracts] at isLive
  · cases terminal
    have rejected :
        secondCertify continued.stage.previous continued.stage.added = none := by
      cases outcome :
          secondCertify continued.stage.previous continued.stage.added with
      | none => rfl
      | some proof =>
          simp [HaltingProgram.composeLiveContracts, outcome] at isLive
    exact
      ⟨HaltingProgram.LiveExtension.mk continued.stage rejected
          continued.produced,
        continued.previous_eq,
        continued.residual_preserved⟩

/-- Recover the literal live second-stage extension from a surviving
composition.  The outer `LiveExtension` proves that the composed certifier
returned `none`; hence the first contract did not close and the second
contract's exact ledger extension is live as well.  This is the canonical
projection used by the sealed DAG compiler to transport typed ledger queries
through dependent contract composition. -/
def HaltingProgram.LiveContractComposition.liveContinuation
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (secondCertify :
      (stage : HaltingProgram.LiveExtension T Previous first firstCertify) →
      Sigma (second.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (live :
      let composition :=
        HaltingProgram.composeLiveContracts first firstCertify
          second secondCertify
      HaltingProgram.LiveExtension T Previous
        composition.contract composition.certify) :
    HaltingProgram.LiveExtension T
      (HaltingProgram.LiveExtension T Previous first firstCertify)
      second secondCertify :=
  (HaltingProgram.LiveContractComposition.liveContinuationWithResidual
    first firstCertify second secondCertify live).val

/-- Core's live-continuation projection preserves the literal residual.
This is the dependent query transport law used by sealed DAG composition. -/
@[simp] theorem HaltingProgram.LiveContractComposition.liveContinuation_residual
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (secondCertify :
      (stage : HaltingProgram.LiveExtension T Previous first firstCertify) →
      Sigma (second.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (live :
      let composition :=
        HaltingProgram.composeLiveContracts first firstCertify
          second secondCertify
      HaltingProgram.LiveExtension T Previous
        composition.contract composition.certify) :
    residualOf
        (HaltingProgram.LiveContractComposition.liveContinuation
          first firstCertify second secondCertify live) =
      residualOf live :=
  (HaltingProgram.LiveContractComposition.liveContinuationWithResidual
    first firstCertify second secondCertify live).property.2

/-- Core's live-continuation projection retains the literal predecessor of
the composed live stage.  This is stronger than residual equality and permits
arbitrary predecessor-indexed facts to be transported without rebuilding
their queries. -/
@[simp] theorem HaltingProgram.LiveContractComposition.liveContinuation_previous
    {P : Core.Problem} {T : Core.Target P}
    {Previous : Type uRunnerStage}
    [HasResidual Previous (ProblemInput P)]
    (first : Contract.{uRunnerStage, 0, uRunnerStage} Previous)
    (firstCertify : (stage : Previous) → Sigma (first.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (second : Contract.{uRunnerStage, 0, uRunnerStage}
      (HaltingProgram.LiveExtension T Previous first firstCertify))
    (secondCertify :
      (stage : HaltingProgram.LiveExtension T Previous first firstCertify) →
      Sigma (second.Payload stage) →
      Option (PLift (T.Predicate (residualOf stage).object)))
    (live :
      let composition :=
        HaltingProgram.composeLiveContracts first firstCertify
          second secondCertify
      HaltingProgram.LiveExtension T Previous
        composition.contract composition.certify) :
    (HaltingProgram.LiveContractComposition.liveContinuation
      first firstCertify second secondCertify live).toLedger.previous.toLedger.previous =
        live.toLedger.previous :=
  (HaltingProgram.LiveContractComposition.liveContinuationWithResidual
    first firstCertify second secondCertify live).property.1

/-- Literal-predecessor law: every appended vertex extends the exact stage
produced by the previous program. -/
@[simp] theorem HaltingProgram.snoc_previous {P : Core.Problem}
    {T : Core.Target P}
    (program : HaltingProgram.{uRunnerStage} P T)
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) -> Sigma (contract.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object)))
    (input : ProblemInput P)
    (live : HaltingProgram.OpenResult P
      (HaltingProgram.LiveExtension T program.Stage contract certify)
      (fun stage => Sigma (contract.Payload stage.previous)) input)
    (output :
      (program.snoc contract certify).execute input = Sum.inr live) :
    ∃ previousOpen : HaltingProgram.OpenResult P program.Stage
        program.TerminalResidual input,
      program.execute input = Sum.inr previousOpen ∧
      ∃ payload : Sigma (contract.Payload previousOpen.stage),
        live.stage.toLedger = Ledger.extend previousOpen.stage payload := by
  change HaltingProgram.snocStep program contract certify input =
    Sum.inr live at output
  cases previousOutput : program.execute input with
  | inl proof =>
      simp [HaltingProgram.snocStep, previousOutput] at output
  | inr previousLive =>
      simp only [HaltingProgram.snocStep, previousOutput] at output
      split at output
      · cases output
      · simp only [Sum.inr.injEq] at output
        subst live
        exact ⟨previousLive, rfl,
          contract.produce previousLive.stage, rfl⟩

/-- Residual preservation for an appended vertex, stated at the exact
compiled stage boundary. -/
@[simp] theorem HaltingProgram.snoc_residual {P : Core.Problem}
    {T : Core.Target P}
    (program : HaltingProgram.{uRunnerStage} P T)
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) -> Sigma (contract.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object)))
    (input : ProblemInput P)
    (live : HaltingProgram.OpenResult P
      (HaltingProgram.LiveExtension T program.Stage contract certify)
      (fun stage => Sigma (contract.Payload stage.previous)) input)
    (_output :
      (program.snoc contract certify).execute input = Sum.inr live) :
    residualOf live.stage = input :=
  live.residual_eq

/-- Appending a vertex cannot reopen a program that has already reached the
target side: later contracts are skipped by `snocStep`. -/
theorem HaltingProgram.snoc_closes_of_closes
    (program : HaltingProgram.{uRunnerStage} P T)
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) -> Sigma (contract.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object)))
    (closed : program.Closes) :
    (program.snoc contract certify).Closes := by
  unfold HaltingProgram.Closes at closed ⊢
  intro input
  rcases output : program.execute input with proof | residual
  · change (HaltingProgram.snocStep program contract certify input).isLeft =
      true
    unfold HaltingProgram.snocStep
    rw [output]
    rfl
  · exact False.elim (by simpa [output] using closed input)

/-- A vertex whose certificate projection is total closes every residual
produced by its predecessor.  The proof is indexed by the literal stage and
payload computed by the framework-owned contract. -/
theorem HaltingProgram.snoc_closes_of_certify
    (program : HaltingProgram.{uRunnerStage} P T)
    (contract : Contract.{uRunnerStage, 0, uRunnerStage} program.Stage)
    (certify : (stage : program.Stage) -> Sigma (contract.Payload stage) ->
      Option (PLift (T.Predicate (residualOf stage).object)))
    (closes :
      ∀ stage payload, ∃ proof, certify stage payload = some proof) :
    (program.snoc contract certify).Closes := by
  unfold HaltingProgram.Closes
  intro input
  rcases output : program.execute input with previousProof | previousOpen
  · change (HaltingProgram.snocStep program contract certify input).isLeft =
      true
    unfold HaltingProgram.snocStep
    rw [output]
    rfl
  · let stage := previousOpen.stage
    let payload := contract.produce stage
    obtain ⟨proof, certified⟩ := closes stage payload
    change (HaltingProgram.snocStep program contract certify input).isLeft =
      true
    unfold HaltingProgram.snocStep
    rw [output]
    dsimp only
    split
    · rfl
    · rename_i rejected
      exfalso
      have impossible : (none : Option
        (PLift (T.Predicate (residualOf stage).object))) = some proof := by
        calc
          none = certify stage payload := rejected.symm
          _ = some proof := certified
      contradiction

/-- A closed compiled execution proves the target on the original problem
input, using only the certificate returned by that execution and residual
preservation. -/
theorem HaltingProgram.target_of_closes
    (program : HaltingProgram.{uRunnerStage} P T)
    (closed : program.Closes)
    (input : ProblemInput P) : T.Predicate input.object := by
  have outputIsLeft := closed input
  exact (program.execute input).getLeft outputIsLeft |>.down

/-- Final lowering stage.  This sum exists only at the output boundary, after
all contracts have been compiled: its left arm is the untouched initial
ledger for a closed run and its right arm is the exact final live stage. -/
private abbrev HaltingProgram.FinalStage
    {P : Core.Problem} {T : Core.Target P}
    (program : HaltingProgram P T) :=
  Sum (Ledger (ProblemInput P)) program.Stage

private instance {P : Core.Problem} {T : Core.Target P}
    (program : HaltingProgram P T) :
    HasResidual (HaltingProgram.FinalStage program) (ProblemInput P) where
  residual
    | Sum.inl initial => residualOf initial
    | Sum.inr live => residualOf live

/-- Core-only lowering of a compiled halting program to the strategy output
boundary.  The output side is decided by the program itself; there is no
argument allowing a caller to choose or replace it. -/
def HaltingProgram.toOutputStrategy
    (definition : Core.ProblemDefinition.{uAmbient, uBranch, uData})
    (program : HaltingProgram.{uRunnerStage}
      definition.problem definition.target) :
    Chain definition.problem definition.target where
  Stage := HaltingProgram.FinalStage program
  TerminalResidual
    | Sum.inl _ => ULift.{uRunnerStage} Empty
    | Sum.inr live => program.TerminalResidual live
  branchState := definition.initialState
  run input :=
    match output : program.execute input with
    | Sum.inl proof =>
        Ledger.extend (Sum.inl (Ledger.initial input)) (Sum.inl proof)
    | Sum.inr live =>
        Ledger.extend (Sum.inr live.stage) (Sum.inr live.terminal)
  object_preserved := fun input => by
    split
    · rfl
    · rename_i live output
      exact congrArg ProblemInput.object live.residual_eq

/-! ## Sequential composition

The next strategy receives the complete literal stage produced by the first
one.  This is the only composition primitive needed by applications: Core
owns predecessor retention and ledger growth, while the next contract may
inspect its predecessor-owned residual through the normal query API.
-/

def chain {Previous : Type uPrevious}
    (first : Contract Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage))) ->
      Contract (Ledger.Extension Previous
        (fun stage => Sigma (first.Payload stage))))
    (previous : Previous) :
    Ledger.Extension (Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage)))
      (fun stage => Sigma ((next stage).Payload stage)) := by
  let middle := run first previous
  exact Ledger.extend middle ((next middle).produce middle)

/-- Public name for dependent strategy composition.  The second strategy is
indexed by the complete first result, so its queries cannot accidentally read
a detached predecessor or a copied payload. -/
def dependentChain {Previous : Type uPrevious}
    (first : Contract Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage))) ->
      Contract (Ledger.Extension Previous
        (fun stage => Sigma (first.Payload stage))))
    (previous : Previous) :=
  chain first next previous

/-! ## CT and pipeline facades

These structures carry no domain data.  They package already executable CT
contracts so Core can compose them, preserve their predecessor stages, and
aggregate their evidence uniformly for Graph and PDE applications.
-/

structure CTAdapter (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  checks : Previous -> Nat
  work : Previous -> Nat

/-- Adapt an already executable CT contract without changing its predecessor
or payload. -/
def CTAdapter.ofContract {Previous : Type uPrevious}
    (execution : Contract.{uPrevious, 0, uPrevious} Previous)
    (checks work : Previous -> Nat) : CTAdapter Previous where
  execution := execution
  checks := checks
  work := work

structure Pipeline (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  checks : Previous -> Nat
  work : Previous -> Nat
  closed : Previous -> Prop
  closed_proof : forall previous, closed previous

def CTAdapter.toPipeline (adapter : CTAdapter Previous)
    (closed : Previous -> Prop) (closed_proof : forall previous, closed previous) :
    Pipeline Previous where
  execution := adapter.execution
  checks := adapter.checks
  work := adapter.work
  closed := closed
  closed_proof := closed_proof

structure BranchPipelines (Previous : Type uPrevious) where
  split : Dichotomy Previous
  left : (stage : split.LeftStage) -> Pipeline split.LeftStage
  right : (stage : split.RightStage) -> Pipeline split.RightStage

def BranchPipelines.run (pipelines : BranchPipelines Previous)
    (previous : Previous) :
    Ledger.Extension Previous
      (fun previous => Sum
        (RoutedLeft pipelines.split
          (fun stage => (pipelines.left stage).execution)
          previous)
        (RoutedRight pipelines.split
          (fun stage => (pipelines.right stage).execution)
          previous)) :=
  runRouted pipelines.split
    (fun stage => (pipelines.left stage).execution)
    (fun stage => (pipelines.right stage).execution)
    previous

@[simp] theorem runRouted_previous
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (previous : Previous) :
    (runRouted split left right previous).previous = previous := rfl

@[simp] theorem runRouted_added
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (previous : Previous) :
    (runRouted split left right previous).added =
      match split.classify previous with
      | Sum.inl witness =>
          let stage := Ledger.extend previous witness
          Sum.inl ⟨witness, (left stage).produce stage⟩
      | Sum.inr witness =>
          let stage := Ledger.extend previous witness
          Sum.inr ⟨witness, (right stage).produce stage⟩ := rfl

def pipelineChain {Previous : Type uPrevious}
    (first : Pipeline Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.execution.Payload stage))) -> Pipeline
        (Ledger.Extension Previous
          (fun stage => Sigma (first.execution.Payload stage))))
    (previous : Previous) :=
  chain first.execution
    (fun stage => (next stage).execution) previous

/-- Execute a branch continuation selected by Core.  The continuation may be
the first member of an arbitrarily long dependent sequence; subsequent steps
use `dependentChain` on the returned ledger stage. -/
def branchContinuation
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (previous : Previous) :=
  runRouted split left right previous

/-- Continue a routed branch sequence from the complete joined stage.  The
next strategy is indexed by that stage, so it may inspect the selected branch
and all retained ledger entries through the normal residual queries. -/
def routedChain
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (next : (stage : Ledger.Extension Previous (RoutedJoin split left right)) ->
      Contract (Ledger.Extension Previous (RoutedJoin split left right)))
    (previous : Previous) :
    Ledger.Extension (Ledger.Extension Previous (RoutedJoin split left right))
      (fun stage => Sigma ((next stage).Payload stage)) := by
  let joined := runRouted split left right previous
  exact Ledger.extend joined ((next joined).produce joined)

@[simp] theorem routedChain_previous
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (next : (stage : Ledger.Extension Previous (RoutedJoin split left right)) ->
      Contract (Ledger.Extension Previous (RoutedJoin split left right)))
    (previous : Previous) :
    (routedChain split left right next previous).previous.previous = previous := rfl

@[simp] theorem routedChain_residual
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (next : (stage : Ledger.Extension Previous (RoutedJoin split left right)) ->
      Contract (Ledger.Extension Previous (RoutedJoin split left right)))
    (previous : Previous) :
    residualOf (routedChain split left right next previous) =
      residualOf previous := rfl


@[simp] theorem pipelineChain_previous {Previous : Type uPrevious}
    (first : Pipeline Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.execution.Payload stage))) -> Pipeline
        (Ledger.Extension Previous
          (fun stage => Sigma (first.execution.Payload stage))))
    (previous : Previous) :
    (pipelineChain first next previous).previous =
      run first.execution previous := rfl

structure WorkEvidence (Previous : Type uPrevious) where
  checks : Previous -> Nat
  work : Previous -> Nat
  checks_nonnegative : forall previous, 0 <= checks previous
  work_nonnegative : forall previous, 0 <= work previous

/-! ## Public framework interfaces for composed CT programs -/

structure StrategyProjection (Root : Type uPrevious) (Value : Type uPayload) where
  read : Root -> Value

structure WorkProfile (Previous : Type uPrevious) where
  checks : Previous -> Nat
  work : Previous -> Nat

def WorkProfile.sequential (left right : WorkProfile Previous) :
    WorkProfile Previous where
  checks previous := left.checks previous + right.checks previous
  work previous := left.work previous + right.work previous

def WorkProfile.branch (left right : WorkProfile Previous) :
    WorkProfile Previous where
  checks previous := max (left.checks previous) (right.checks previous)
  work previous := max (left.work previous) (right.work previous)

inductive TerminalKind where
  | target
  | avoiding
  deriving DecidableEq, Repr

structure TerminalCertificate (Previous : Type uPrevious) where
  kind : TerminalKind
  target : Previous -> Prop
  avoiding : Previous -> Prop
  target_or_avoiding : forall previous,
    kind = .target ∧ target previous ∨ kind = .avoiding ∧ avoiding previous

theorem TerminalCertificate.closed (certificate : TerminalCertificate Previous)
    (previous : Previous) :
    match certificate.kind with
    | .target => certificate.target previous
    | .avoiding => certificate.avoiding previous := by
  rcases certificate.target_or_avoiding previous with h | h
  · simpa [h.1] using h.2
  · simpa [h.1] using h.2

structure ClosedPipeline (Previous : Type uPrevious) where
  pipeline : Pipeline Previous
  terminal : Previous -> TerminalCertificate Previous
  terminal_closed : forall previous,
    (terminal previous).kind = .target ∨ (terminal previous).kind = .avoiding

theorem ClosedPipeline.closed (closed : ClosedPipeline Previous)
    (previous : Previous) :
    match (closed.terminal previous).kind with
    | .target => (closed.terminal previous).target previous
    | .avoiding => (closed.terminal previous).avoiding previous :=
  (closed.terminal previous).closed previous

def normalizeStage {Previous : Type uPrevious} {Added : Previous -> Type uPayload}
    (stage : Ledger.Extension Previous Added) :
    Ledger.Extension Previous Added :=
  stage

/-- Public normalization boundary for an accumulated strategy stage. -/
abbrev NormalizedStage (Previous : Type uPrevious)
    (Added : Previous -> Type uPayload) := Ledger.Extension Previous Added

def normalizeContract {Previous : Type uPrevious}
    (contract : Contract Previous) := contract

def normalizeDichotomy {Previous : Type uPrevious}
    (dichotomy : Dichotomy Previous) := dichotomy

@[simp] theorem normalizeStage_eq {Previous : Type uPrevious}
    {Added : Previous -> Type uPayload}
    (stage : Ledger.Extension Previous Added) :
    normalizeStage stage = stage := rfl

def projectPrevious {Previous : Type uPrevious} {Value : Type uValue}
    {Added : Previous -> Type uPayload}
    (projection : Previous -> Value) :
    Ledger.Extension Previous Added -> Value :=
  fun stage => projection stage.previous

def projectChain {Previous : Type uPrevious} {Value : Type uValue}
    {First : Previous -> Type uPayload}
    {Second : Ledger.Extension Previous First -> Type uPayload}
    (projection : Previous -> Value) :
    Ledger.Extension (Ledger.Extension Previous First) Second -> Value :=
  fun stage => projection stage.previous.previous

@[simp] theorem projectChain_eq_previous {Previous : Type uPrevious}
    {Value : Type uValue} {First : Previous -> Type uPayload}
    {Second : Ledger.Extension Previous First -> Type uPayload}
    (projection : Previous -> Value)
    (stage : Ledger.Extension (Ledger.Extension Previous First) Second) :
    projectChain projection stage = projection stage.previous.previous := rfl

/-/ A branch join is represented by the routed ledger extension itself.  The
framework owns the join; applications only provide the two continuation
contracts to `runRouted`. -/
abbrev BranchJoin (Previous : Type uPrevious) (split : Dichotomy Previous)
    (left : (stage : split.LeftStage) -> Contract split.LeftStage)
    (right : (stage : split.RightStage) -> Contract split.RightStage)
    (_previous : Previous) : Type _ :=
  Ledger.Extension Previous (RoutedJoin split left right)

/-- A routed execution together with its final terminal certificate.  The
certificate is indexed by the exact joined ledger stage, so closure cannot be
proved for a detached or reconstructed branch payload. -/
structure RoutedClosure (Previous : Type uPrevious) where
  split : Dichotomy.{uPrevious, uPrevious, uPrevious} Previous
  left : (stage : split.LeftStage) ->
    Contract.{uPrevious, 0, uPrevious} split.LeftStage
  right : (stage : split.RightStage) ->
    Contract.{uPrevious, 0, uPrevious} split.RightStage
  terminal : TerminalCertificate (Ledger.Extension Previous
      (RoutedJoin split left right))

def RoutedClosure.run {Previous : Type uPrevious}
    (closure : RoutedClosure Previous)
    (previous : Previous) :=
  runRouted closure.split closure.left closure.right previous

theorem RoutedClosure.closed (closure : RoutedClosure Previous)
    (previous : Previous) :
    match closure.terminal.kind with
    | .target => closure.terminal.target
        (closure.run previous)
    | .avoiding => closure.terminal.avoiding
        (closure.run previous) :=
  closure.terminal.closed (closure.run previous)

structure BranchWork (Previous : Type uPrevious) where
  left : Previous -> Nat
  right : Previous -> Nat

def BranchWork.total (profile : BranchWork Previous) (previous : Previous) : Nat :=
  profile.left previous + profile.right previous

structure DomainStrategy (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  projection : StrategyProjection Previous Previous
  work : WorkProfile Previous

/-! An individual executable CT and a composed CT fragment share one lowering
boundary.  Keeping this conversion in Core prevents backends from rebuilding
ledger stages or inventing a second strategy representation. -/

def CTAdapter.toDomainStrategy (adapter : CTAdapter Previous) :
    DomainStrategy Previous where
  execution := adapter.execution
  projection := { read := id }
  work := {
    checks := adapter.checks
    work := adapter.work
  }

/-! ## Generic success-or-residual strategy

Many domain rows have the same shape: a predecessor-owned predicate either
closes the row or leaves a typed residual for the next strategy.  The domain
supplies only the predicate, its decider, and residual construction. -/

inductive BinaryTerminal where
  | success
  | residual
  deriving DecidableEq, Repr

def binaryContract {Previous : Type uPrevious} {Residual : Previous -> Type uPayload}
    (Success : Previous -> Prop)
    (decideSuccess : (previous : Previous) -> Decidable (Success previous))
    (residual : (previous : Previous) -> Residual previous) :
    Contract.{uPrevious, 0, uPayload} Previous where
  Terminal := BinaryTerminal
  Payload := fun previous terminal => match terminal with
    | .success => ULift.{uPayload} (PLift (Success previous))
    | .residual => Residual previous
  produce previous :=
    @dite _ (Success previous) (decideSuccess previous)
      (fun proof => ⟨.success, ⟨⟨proof⟩⟩⟩)
      (fun _ => ⟨.residual, residual previous⟩)
  exhaustive previous := by
    exact @dite _ (Success previous) (decideSuccess previous)
      (fun proof => ⟨⟨.success, ⟨⟨proof⟩⟩⟩⟩)
      (fun _ => ⟨⟨.residual, residual previous⟩⟩)

def WorkEvidence.ofAdapter (adapter : CTAdapter Previous) :
    WorkEvidence Previous where
  checks := adapter.checks
  work := adapter.work
  checks_nonnegative := by intro; omega
  work_nonnegative := by intro; omega

@[simp] theorem chain_previous {Previous : Type uPrevious}
    (first : Contract Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage))) ->
      Contract (Ledger.Extension Previous
        (fun stage => Sigma (first.Payload stage))))
    (previous : Previous) :
    (chain first next previous).previous = run first previous :=
  rfl

@[simp] theorem run_previous {Previous : Type uPrevious}
    (contract : Contract Previous) (previous : Previous) :
    (run contract previous).previous = previous := rfl

@[simp] theorem run_added {Previous : Type uPrevious}
    (contract : Contract Previous) (previous : Previous) :
    (run contract previous).added = contract.produce previous := rfl

/-- A strategy which only transports a previous terminal payload. -/
def map {Previous : Type uPrevious} (contract : Contract Previous)
    {NewTerminal : Type uTerminal} {NewPayload : Previous -> NewTerminal -> Type uPayload}
    (mapPayload : (previous : Previous) ->
      Sigma (contract.Payload previous) -> Sigma (NewPayload previous)) :
    Contract Previous where
  Terminal := NewTerminal
  Payload := NewPayload
  produce previous := mapPayload previous (contract.produce previous)
  exhaustive := fun previous =>
    ⟨mapPayload previous (contract.produce previous)⟩

/-! ## Common strategy pattern contracts -/

/-- An ordered finite witness scan.  The witness and its decision procedure
are domain inputs; first-hit semantics remain a Core contract. -/
structure OrderedWitnessScan (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  schedule : Query Previous (fun previous => Finite.Enumeration (Item previous))
  witness : (previous : Previous) -> Item previous -> Prop
  witnessDecidable : (previous : Previous) -> (item : Item previous) ->
    Decidable (witness previous item)
  exhaustive : (previous : Previous) -> (item : Item previous) ->
    item ∈ (schedule previous).values ->
      witness previous item ∨ ¬ witness previous item

/-- A finite response classifier over a predecessor-owned schedule. -/
structure ResponseClassifier (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  Response : Previous -> Type uValue
  schedule : Query Previous (fun previous => Finite.Enumeration (Item previous))
  observe : (previous : Previous) -> Item previous -> Response previous
  Class : Previous -> Type uTerminal
  classify : (previous : Previous) -> Response previous -> Class previous
  exhaustive : (previous : Previous) -> (item : Item previous) ->
    ∃ cls : Class previous,
      classify previous (observe previous item) = cls

/-- A capacity ledger: every item has a class, a contribution, and a
residual-indexed capacity comparison.  The quantity can be graph charge or
PDE energy. -/
structure CapacityLedger (Previous : Type uPrevious) [Preorder Nat] where
  Item : Previous -> Type uItem
  Class : Previous -> Type uTerminal
  schedule : Query Previous (fun previous => Finite.Enumeration (Item previous))
  classify : (previous : Previous) -> Item previous -> Class previous
  contribution : (previous : Previous) -> Item previous -> Nat
  capacity : (previous : Previous) -> Class previous -> Nat
  totalWithin : (previous : Previous) -> (item : Item previous) ->
    contribution previous item <= capacity previous (classify previous item)

/-- A negative-budget localization contract. -/
structure SupportLocalization (Previous : Type uPrevious) where
  Cell : Previous -> Type uItem
  schedule : Query Previous (fun previous => Finite.Enumeration (Cell previous))
  localBudget : (previous : Previous) -> Cell previous -> Int
  selected : (previous : Previous) -> Cell previous
  selected_negative : (previous : Previous) ->
    localBudget previous (selected previous) < 0

/-- A target-avoiding continuation contract. -/
structure TargetAvoidingContinuation (Previous : Type uPrevious) where
  Target : Previous -> Prop
  targetDecidable : (previous : Previous) -> Decidable (Target previous)

/-- A finite rank/budget split contract. -/
structure RankBudgetSplit (Previous : Type uPrevious) where
  Rank : Previous -> Nat
  Budget : Previous -> Nat
  threshold : Previous -> Nat
  high : (previous : Previous) -> Prop
  low : (previous : Previous) -> Prop
  exhaustive : (previous : Previous) -> high previous ∨ low previous

/-- A closed-code exhaustion contract. -/
structure ClosedCodeExhaustion (Previous : Type uPrevious) where
  Code : Previous -> Type uCode
  schedule : Query Previous (fun previous => Finite.Enumeration (Code previous))
  targetCode : (previous : Previous) -> Code previous
  observedCode : (previous : Previous) -> Code previous -> Code previous
  closed : (previous : Previous) ->
    observedCode previous (targetCode previous) = targetCode previous

/-! ## Executable strategy-pattern boundaries -/

/-! ## Single CT execution bridge

Concrete CT modules expose a sealed result and a terminal projection.  This
adapter converts that common shape into the Core strategy contract without
allowing a caller to choose the terminal or replace the result. -/

def Contract.toCTExecution
    (contract : Contract.{uPrevious, uTerminal, uPayload} Previous)
    (checks work : Previous -> Nat) : CTExecution Previous where
  Terminal := contract.Terminal
  Output := fun previous => Sigma (contract.Payload previous)
  run previous := (Strategy.run contract previous).added
  terminal _ output := output.fst
  checks := checks
  work := work

noncomputable def Dichotomy.toCTExecution
    (strategy : Dichotomy Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  (dichotomyContract strategy).toCTExecution checks work

/-! Dependent execution-level composition.  Unlike the compatibility
`CTAdapter`, this form keeps each CT output typed by the exact ledger stage
that follows it. -/

def CTExecution.compose
    (first : CTExecution Previous)
    (next : CTExecution
      (Ledger.Extension Previous
        first.Output)) : CTExecution Previous where
  Terminal := CompletedTerminal
  Output := fun previous =>
    Sigma fun firstOutput : first.Output previous =>
      next.Output (Ledger.extend previous firstOutput)
  run previous :=
    let firstOutput := first.run previous
    let middle := Ledger.extend previous firstOutput
    ⟨firstOutput, next.run middle⟩
  terminal _ _ := .completed
  checks previous :=
    let firstOutput := first.run previous
    first.checks previous +
      next.checks (Ledger.extend previous firstOutput)
  work previous :=
    let firstOutput := first.run previous
    first.work previous +
      next.work (Ledger.extend previous firstOutput)

/-! ## Framework-owned theorem publication

A sealed Strategy may derive additional propositions from the literal output
of an atomic CT.  The proposition and its proof are not registration data and
cannot influence the CT's schedules, terminal, trace, checks, or work.  Core
appends the proof as one ordinary dependent ledger entry after the exact CT
output. -/

/-- Append facts proved from an atomic CT's literal output.

The returned execution first runs `execution` unchanged and then appends one
zero-work `ProofPayload`.  The proof is indexed by the actual intermediate
ledger stage, so it cannot describe a reconstructed output or a different
predecessor. -/
def CTExecution.appendDerivedFacts
    (execution : CTExecution Previous)
    (Facts : Ledger.Extension Previous execution.Output → Prop)
    (verified : ∀ stage, Facts stage) : CTExecution Previous :=
  execution.compose
    { Terminal := CompletedTerminal
      Output := fun stage => ProofPayload (Facts stage)
      run := fun stage => proofPayload (verified stage)
      terminal := fun _ _ => .completed
      checks := fun _ => 0
      work := fun _ => 0 }

/-- The atomic output retained by `appendDerivedFacts`. -/
def CTExecution.appendDerivedFactsOutput
    (execution : CTExecution Previous)
    (Facts : Ledger.Extension Previous execution.Output → Prop)
    (verified : ∀ stage, Facts stage)
    (previous : Previous)
    (output : (execution.appendDerivedFacts Facts verified).Output previous) :
    execution.Output previous :=
  output.fst

/-- The appended proof is exactly a theorem about the retained atomic output
and its literal predecessor. -/
theorem CTExecution.appendDerivedFacts_verified
    (execution : CTExecution Previous)
    (Facts : Ledger.Extension Previous execution.Output → Prop)
    (verified : ∀ stage, Facts stage)
    (previous : Previous)
    (output : (execution.appendDerivedFacts Facts verified).Output previous) :
    Facts (Ledger.extend previous output.fst) :=
  output.snd.down

/-! Public preservation API for dependent CT composition.  These lemmas are
deliberately stated against the literal `run` value: a composed strategy may
add output, but it cannot replace or silently re-create the predecessor. -/

@[simp] theorem CTExecution.compose_run_first
    (first : CTExecution Previous)
    (next : CTExecution
      (Ledger.Extension Previous first.Output))
    (previous : Previous) :
    ((first.compose next).run previous).fst = first.run previous := rfl

@[simp] theorem CTExecution.compose_run_next
    (first : CTExecution Previous)
    (next : CTExecution
      (Ledger.Extension Previous first.Output))
    (previous : Previous) :
    ((first.compose next).run previous).snd =
      next.run (Ledger.extend previous (first.run previous)) := rfl

@[simp] theorem CTExecution.compose_middle_previous
    (first : CTExecution Previous)
    (_next : CTExecution
      (Ledger.Extension Previous first.Output))
    (previous : Previous) :
    (Ledger.extend previous (first.run previous)).previous = previous := rfl

@[simp] theorem CTExecution.compose_middle_residual
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (first : CTExecution Previous)
    (_next : CTExecution
      (Ledger.Extension Previous first.Output))
    (previous : Previous) :
    residualOf (Ledger.extend previous (first.run previous)) =
      residualOf previous := rfl

def CTExecution.toContract (execution : CTExecution Previous) :
    Contract.{uPrevious, uTerminal, uPayload} Previous where
  Terminal := execution.Terminal
  Payload := fun previous _ => execution.Output previous
  produce previous :=
    let output := execution.run previous
    ⟨execution.terminal previous output, output⟩
  exhaustive previous := by
    let output := execution.run previous
    exact ⟨⟨execution.terminal previous output, output⟩⟩

/-- Direct live-ledger query for the exact output of a CT execution lowered
through `toContract`.  No output is repackaged: this is the second projection
of `LiveExtension.producedQuery`. -/
def CTExecution.liveOutputQuery
    {P : Core.Problem} {T : Core.Target P}
    [HasResidual Previous (ProblemInput P)]
    (execution : CTExecution Previous)
    (certify : (stage : Previous) →
      Sigma (execution.toContract.Payload stage) →
        Option (PLift (T.Predicate (residualOf stage).object))) :
    Query
      (HaltingProgram.LiveExtension T Previous execution.toContract certify)
      (fun live => execution.Output live.previous) :=
  (HaltingProgram.LiveExtension.producedQuery
    (T := T) (contract := execution.toContract) (certify := certify)).map
      fun _ payload => payload.snd

@[simp] theorem CTExecution.read_liveOutputQuery
    {P : Core.Problem} {T : Core.Target P}
    [HasResidual Previous (ProblemInput P)]
    (execution : CTExecution Previous)
    (certify : (stage : Previous) →
      Sigma (execution.toContract.Payload stage) →
        Option (PLift (T.Predicate (residualOf stage).object)))
    (live :
      HaltingProgram.LiveExtension T Previous execution.toContract certify) :
    (execution.liveOutputQuery certify) live =
      execution.run live.previous := by
  change (live.ledger.added).snd = execution.run live.previous
  have produced := live.produced
  exact congrArg Sigma.snd produced

def CTExecution.toAdapter (execution : CTExecution Previous) :
    CTAdapter Previous where
  execution := execution.toContract
  checks := execution.checks
  work := execution.work

def CTAdapter.toExecution (adapter : CTAdapter Previous) :
    CTExecution Previous where
  Terminal := adapter.execution.Terminal
  Output := fun previous => Sigma (adapter.execution.Payload previous)
  run previous := (Strategy.run adapter.execution previous).added
  terminal _ output := output.fst
  checks := adapter.checks
  work := adapter.work

/-! ## CT-composed strategy fragments

An official strategy is assembled from executable CT contracts.  Core keeps
the dependent second CT indexed by the complete first ledger stage, so the
composition cannot copy a residual or route a detached payload.  The public
DAG layer never exposes this type; the private backend resolves strategy
names to these fragments.
-/

structure CTComposition (Previous : Type uPrevious) where
  first : CTAdapter Previous
  next : CTAdapter (Ledger.Extension Previous
    (fun previous => Sigma (first.execution.Payload previous)))

def CTComposition.run (composition : CTComposition Previous)
    (previous : Previous) :=
  dependentChain composition.first.execution
    (fun _stage => composition.next.execution) previous

def CTComposition.execution (composition : CTComposition Previous) :
    Contract Previous where
  Terminal := CompletedTerminal
  Payload := fun previous _ =>
    Sigma fun firstResult : Sigma (composition.first.execution.Payload previous) =>
      Sigma (composition.next.execution.Payload
        (Ledger.extend previous firstResult))
  produce previous :=
    let firstStage := Strategy.run composition.first.execution previous
    let secondStage := Strategy.run
      composition.next.execution firstStage
    ⟨.completed, ⟨firstStage.added, secondStage.added⟩⟩
  exhaustive previous := by
    let firstStage := Strategy.run composition.first.execution previous
    let secondStage := Strategy.run
      composition.next.execution firstStage
    exact ⟨⟨.completed, ⟨firstStage.added, secondStage.added⟩⟩⟩

def CTComposition.work (composition : CTComposition Previous) :
    WorkEvidence Previous where
  checks previous :=
    let firstStage := Strategy.run composition.first.execution previous
    composition.first.checks previous +
      composition.next.checks firstStage
  work previous :=
    let firstStage := Strategy.run composition.first.execution previous
    composition.first.work previous +
      composition.next.work firstStage
  checks_nonnegative := by intro; omega
  work_nonnegative := by intro; omega

def CTComposition.toAdapter (composition : CTComposition Previous) :
    CTAdapter Previous where
  execution := composition.execution
  checks := (composition.work).checks
  work := (composition.work).work

def CTComposition.toDomainStrategy (composition : CTComposition Previous) :
    DomainStrategy Previous where
  execution := composition.execution
  projection := { read := id }
  work := {
    checks := (composition.work).checks
    work := (composition.work).work
  }

/-! A nested composition is itself an adapter, so this constructor is the
Core-owned variadic composition primitive for strategy recipes. -/

def CTComposition.then
    (composition : CTComposition Previous)
    (next : CTAdapter (Ledger.Extension Previous
      (fun previous => Sigma (composition.execution.Payload previous)))) :
    CTComposition Previous where
  first := composition.toAdapter
  next := next

/-! ## Rank-capacity exhaustion

A recurring proof block runs several dependent CTs and has exactly three
semantic outcomes: the target is already certified, or one of two surviving
continuations remains.  `RankCapacityExhaustion` keeps the complete composed CT output
as the evidence interpreted by the domain contract.  Core performs the
execution and binary routing; applications cannot replace the CT run with a
detached branch label.

The target case is retained inside either routed payload.  The halting DAG
runner immediately consumes it through the registered target decision on the
same literal residual, while the non-target payload remains available to the
corresponding continuation.
-/

structure RankCapacityExhaustion
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (pipeline : CTExecution (ProblemInput P)) where
  Left : ProblemInput P -> Type uLeft
  Right : ProblemInput P -> Type uRight
  interpret : (input : ProblemInput P) ->
    pipeline.Output input ->
      Sum (PLift (T.Predicate input.object))
        (Sum (Left input) (Right input))
  targetSide : (input : ProblemInput P) ->
    pipeline.Output input -> Bool := fun _ _ => false
  metadata : Core.Documentation := {}
  components : List Core.Documentation := []
  leftMetadata : Core.Documentation := {}
  rightMetadata : Core.Documentation := {}

abbrev RankCapacityExhaustion.LeftPayload
    (strategy : RankCapacityExhaustion P T pipeline) (input : ProblemInput P) :=
  Sum (PLift (T.Predicate input.object)) (strategy.Left input)

abbrev RankCapacityExhaustion.RightPayload
    (strategy : RankCapacityExhaustion P T pipeline) (input : ProblemInput P) :=
  Sum (PLift (T.Predicate input.object)) (strategy.Right input)

/-- Execute a dependent CT composition and expose only its certified target,
left-continuation, or right-continuation frontier. -/
noncomputable def RankCapacityExhaustion.toDichotomy
    (strategy : RankCapacityExhaustion P T pipeline) : Core.DichotomyData P T where
  LeftPayload := strategy.LeftPayload
  RightPayload := strategy.RightPayload
  classify := fun input =>
    let output := pipeline.run input
    match strategy.interpret input output with
    | .inl targetProof =>
        if strategy.targetSide input output then
          .inr (.inl targetProof)
        else
          .inl (.inl targetProof)
    | .inr (.inl left) => .inl (.inr left)
    | .inr (.inr right) => .inr (.inr right)
  metadata := strategy.metadata
  components := strategy.components
  leftMetadata := strategy.leftMetadata
  rightMetadata := strategy.rightMetadata

namespace OrderedWitnessScan

abbrev Entry (strategy : OrderedWitnessScan Previous) (previous : Previous) :=
  Sigma fun item : strategy.Item previous =>
    PLift (strategy.witness previous item ∨
      ¬ strategy.witness previous item)

def entry (strategy : OrderedWitnessScan Previous) (previous : Previous)
    (item : strategy.Item previous) : strategy.Entry previous :=
  ⟨item, ⟨by
    letI := strategy.witnessDecidable previous item
    by_cases proof : strategy.witness previous item
    · exact Or.inl proof
    · exact Or.inr proof⟩⟩

def entries (strategy : OrderedWitnessScan Previous) (previous : Previous) :
    List (strategy.Entry previous) :=
  (strategy.schedule previous).values.map (strategy.entry previous)

def asContract (strategy : OrderedWitnessScan Previous) : Contract Previous where
  Terminal := CompletedTerminal
  Payload := fun previous _ => List (strategy.Entry previous)
  produce previous := ⟨.completed, strategy.entries previous⟩
  exhaustive previous := ⟨⟨.completed, strategy.entries previous⟩⟩

def toCTExecution
    (strategy : OrderedWitnessScan Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

end OrderedWitnessScan

namespace ResponseClassifier

abbrev Entry (strategy : ResponseClassifier Previous) (previous : Previous) :=
  Sigma fun item : strategy.Item previous =>
    Sigma fun cls : strategy.Class previous =>
      PLift (strategy.classify previous (strategy.observe previous item) = cls)

def entry (strategy : ResponseClassifier Previous) (previous : Previous)
    (item : strategy.Item previous) : strategy.Entry previous :=
  ⟨item, strategy.classify previous (strategy.observe previous item), ⟨rfl⟩⟩

def entries (strategy : ResponseClassifier Previous) (previous : Previous) :
    List (strategy.Entry previous) :=
  (strategy.schedule previous).values.map (strategy.entry previous)

def asContract (strategy : ResponseClassifier Previous) : Contract Previous where
  Terminal := CompletedTerminal
  Payload := fun previous _ => List (strategy.Entry previous)
  produce previous := ⟨.completed, strategy.entries previous⟩
  exhaustive previous := ⟨⟨.completed, strategy.entries previous⟩⟩

def toCTExecution
    (strategy : ResponseClassifier Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

end ResponseClassifier

namespace CapacityLedger

abbrev Entry (strategy : CapacityLedger Previous) (previous : Previous) :=
  Sigma fun item : strategy.Item previous =>
    PLift (strategy.contribution previous item <=
      strategy.capacity previous (strategy.classify previous item))

def entry (strategy : CapacityLedger Previous) (previous : Previous)
    (item : strategy.Item previous) : strategy.Entry previous :=
  ⟨item, ⟨strategy.totalWithin previous item⟩⟩

def entries (strategy : CapacityLedger Previous) (previous : Previous) :
    List (strategy.Entry previous) :=
  (strategy.schedule previous).values.map (strategy.entry previous)

def asContract (strategy : CapacityLedger Previous) : Contract Previous where
  Terminal := CompletedTerminal
  Payload := fun previous _ => List (strategy.Entry previous)
  produce previous := ⟨.completed, strategy.entries previous⟩
  exhaustive previous := ⟨⟨.completed, strategy.entries previous⟩⟩

def toCTExecution
    (strategy : CapacityLedger Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

end CapacityLedger

def SupportLocalization.asContract
    (strategy : SupportLocalization Previous) : Contract Previous where
  Terminal := CompletedTerminal
  Payload := fun previous _ =>
    Sigma fun cell : strategy.Cell previous =>
      PLift (strategy.localBudget previous cell < 0)
  produce previous :=
    ⟨.completed, strategy.selected previous,
      ⟨strategy.selected_negative previous⟩⟩
  exhaustive previous :=
    ⟨⟨.completed, strategy.selected previous,
      ⟨strategy.selected_negative previous⟩⟩⟩

def SupportLocalization.toCTExecution
    (strategy : SupportLocalization Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

inductive TargetAvoidingTerminal where
  | target
  | avoiding

def TargetAvoidingContinuation.Payload
    (strategy : TargetAvoidingContinuation Previous)
    (previous : Previous) : TargetAvoidingTerminal -> Type _
  | .target => PLift (strategy.Target previous)
  | .avoiding => PLift (¬ strategy.Target previous)

theorem TargetAvoidingContinuation.nonemptyPayload
    (strategy : TargetAvoidingContinuation Previous) (previous : Previous) :
    Nonempty (Sigma (strategy.Payload previous)) := by
  letI := strategy.targetDecidable previous
  by_cases proof : strategy.Target previous
  · exact ⟨⟨.target, ⟨proof⟩⟩⟩
  · exact ⟨⟨.avoiding, ⟨proof⟩⟩⟩

noncomputable def TargetAvoidingContinuation.asContract
    (strategy : TargetAvoidingContinuation Previous) : Contract Previous where
  Terminal := TargetAvoidingTerminal
  Payload := strategy.Payload
  produce previous := Classical.choice (strategy.nonemptyPayload previous)
  exhaustive previous := strategy.nonemptyPayload previous

noncomputable def TargetAvoidingContinuation.toCTExecution
    (strategy : TargetAvoidingContinuation Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

inductive RankBudgetTerminal where
  | high
  | low

def RankBudgetSplit.Payload (strategy : RankBudgetSplit Previous)
    (previous : Previous) : RankBudgetTerminal -> Type
  | .high => PLift (strategy.high previous)
  | .low => PLift (strategy.low previous)

theorem RankBudgetSplit.nonemptyPayload
    (strategy : RankBudgetSplit Previous) (previous : Previous) :
    Nonempty (Sigma (strategy.Payload previous)) := by
  rcases strategy.exhaustive previous with high | low
  · exact ⟨⟨.high, ⟨high⟩⟩⟩
  · exact ⟨⟨.low, ⟨low⟩⟩⟩

noncomputable def RankBudgetSplit.asContract
    (strategy : RankBudgetSplit Previous) : Contract Previous where
  Terminal := RankBudgetTerminal
  Payload := strategy.Payload
  produce previous := Classical.choice (strategy.nonemptyPayload previous)
  exhaustive previous := strategy.nonemptyPayload previous

noncomputable def RankBudgetSplit.toCTExecution
    (strategy : RankBudgetSplit Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

def ClosedCodeExhaustion.asContract
    (strategy : ClosedCodeExhaustion Previous) : Contract Previous where
  Terminal := CompletedTerminal
  Payload := fun previous _ =>
    PLift (strategy.observedCode previous (strategy.targetCode previous) =
      strategy.targetCode previous)
  produce previous := ⟨.completed, ⟨strategy.closed previous⟩⟩
  exhaustive previous := ⟨⟨.completed, ⟨strategy.closed previous⟩⟩⟩

def ClosedCodeExhaustion.toCTExecution
    (strategy : ClosedCodeExhaustion Previous)
    (checks work : Previous -> Nat) : CTExecution Previous :=
  strategy.asContract.toCTExecution checks work

end Hypostructure.Core.Strategy
