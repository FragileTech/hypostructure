import Hypostructure.Core.Strategy.AtomicDecision
import Hypostructure.Core.Strategy.MinimalCounterexampleScope

/-!
# Sealed total strategy closure

`ClosingProgram known` is a structurally finite proof program over one exact
branch-local fact index.  It has no open terminal: every leaf either already
contains Core's reserved closure key or constructs that key through one of
Core's registered local closure mechanisms.

The interpreter is private.  Applications author topology only by composing
trusted atomic CTs, trusted atomic decisions, and the public closing
combinators below.  They cannot supply a ledger transformer, executor result,
route callback, or proof of `False`.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uAmbient uBranch uMeasure uResidual uSubject uKey uValue

/-- Private recursive representation of a total branch-local program. -/
private inductive ClosingProgramBody
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    FactKeys Residual →
      Type (max (max (uResidual + 1) (uKey + 1)) (uValue + 3)) where
  | alreadyClosed {known : FactKeys Residual}
      (present : FactKeys.Has system.closureKey known) :
      ClosingProgramBody Residual known
  | atomic {known : FactKeys Residual}
      (ct : AtomicCT Residual)
      [available : FactKeys.Available ct.manifest.Requires known]
      (knownOpen : system.closureKey ∉ known)
      (outputsOpen : system.closureKey ∉ ct.manifest.Produces)
      (fresh : List.Disjoint ct.manifest.Produces known)
      (next : ClosingProgramBody Residual (ct.manifest.Produces ++ known)) :
      ClosingProgramBody Residual known
  | branch {known : FactKeys Residual}
      (decision : AtomicDecision Residual)
      [available : FactKeys.Available decision.manifest.Requires known]
      (knownOpen : system.closureKey ∉ known)
      (leftFresh : decision.manifest.left ∉ known)
      (rightFresh : decision.manifest.right ∉ known)
      (left : ClosingProgramBody Residual (decision.manifest.left :: known))
      (right : ClosingProgramBody Residual (decision.manifest.right :: known)) :
      ClosingProgramBody Residual known
  | incompatible {known : FactKeys Residual}
      (left right : FactKey Residual)
      [leftPresent : FactKeys.Has left known]
      [rightPresent : FactKeys.Has right known]
      [conflict : Incompatible Residual left right]
      (closureFresh : system.closureKey ∉ known) :
      ClosingProgramBody Residual known
  | impossible {known : FactKeys Residual}
      (key : FactKey Residual)
      [present : FactKeys.Has key known]
      [contradiction : Impossible Residual key]
      (closureFresh : system.closureKey ∉ known) :
      ClosingProgramBody Residual known
  | emptiness {known : FactKeys Residual}
      [oracle : EmptinessOracle Residual]
      (closureFresh : system.closureKey ∉ known)
      (openBranch : ClosingProgramBody Residual known) :
      ClosingProgramBody Residual known

/-- A total, branch-local strategy program.  Its representation is private, so
the safe combinators below are the complete authoring surface. -/
structure ClosingProgram
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (known : FactKeys Residual) where
  private mk ::
  private body : ClosingProgramBody Residual known

namespace ClosingProgram

/-- Terminate a branch whose exact index already contains Core's closure key. -/
def closed
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    [present : FactKeys.Has system.closureKey known] :
    ClosingProgram Residual known :=
  .mk (.alreadyClosed present)

/-- Prepend one trusted atomic CT to a closing continuation. -/
def atomic
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    (ct : AtomicCT Residual)
    [FactKeys.Available ct.manifest.Requires known]
    (next : ClosingProgram Residual (ct.manifest.Produces ++ known))
    (knownOpen : system.closureKey ∉ known := by decide)
    (outputsOpen : system.closureKey ∉ ct.manifest.Produces := by decide)
    (fresh : List.Disjoint ct.manifest.Produces known := by decide) :
    ClosingProgram Residual known :=
  .mk (.atomic ct knownOpen outputsOpen fresh next.body)

/-- Prepend one trusted exhaustive decision.  Both continuations are required,
and their different exact indices prevent sibling-only fact reads. -/
def branch
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    (decision : AtomicDecision Residual)
    [FactKeys.Available decision.manifest.Requires known]
    (left : ClosingProgram Residual (decision.manifest.left :: known))
    (right : ClosingProgram Residual (decision.manifest.right :: known))
    (knownOpen : system.closureKey ∉ known := by decide)
    (leftFresh : decision.manifest.left ∉ known := by decide)
    (rightFresh : decision.manifest.right ∉ known := by decide) :
    ClosingProgram Residual known :=
  .mk (.branch decision knownOpen leftFresh rightFresh left.body right.body)

/-- Close a branch from two visible incompatible facts. -/
def closeIncompatible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    (left right : FactKey Residual)
    [FactKeys.Has left known] [FactKeys.Has right known]
    [Incompatible Residual left right]
    (closureFresh : system.closureKey ∉ known := by decide) :
    ClosingProgram Residual known :=
  .mk (.incompatible left right closureFresh)

/-- Close a branch from one visible impossible fact. -/
def closeImpossible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    (key : FactKey Residual)
    [FactKeys.Has key known] [Impossible Residual key]
    (closureFresh : system.closureKey ∉ known := by decide) :
    ClosingProgram Residual known :=
  .mk (.impossible key closureFresh)

/-- Apply the residual domain's emptiness oracle.  Core closes the empty case;
the author supplies only the continuation for the open case. -/
def closeIfEmpty
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    [EmptinessOracle Residual]
    (openBranch : ClosingProgram Residual known)
    (closureFresh : system.closureKey ∉ known := by decide) :
    ClosingProgram Residual known :=
  .mk (.emptiness closureFresh openBranch.body)

private noncomputable def execute
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    {known : FactKeys Residual} → ClosingProgramBody Residual known →
      {current : Residual} → ExactLedger Residual current known → False
  | _, .alreadyClosed present, _, history =>
      history.elimClosed present
  | _, .atomic ct (available := _) _knownOpen _outputsOpen fresh next, _, history =>
      execute next (ct.run history fresh)
  | _, .branch decision (available := _) _knownOpen leftFresh rightFresh left right,
      _, history =>
      match AtomicDecision.run exactLedgerInternal% decision history
          leftFresh rightFresh with
      | .left leftHistory => execute left leftHistory
      | .right rightHistory => execute right rightHistory
  | _, .incompatible left right (leftPresent := _) (rightPresent := _)
      (conflict := _) closureFresh, _, history =>
      let closedHistory :=
        Core.Strategy.closeIncompatible history left right closureFresh
      closedHistory.elimClosed (by infer_instance)
  | _, .impossible key (present := _) (contradiction := _) closureFresh, _, history =>
      let closedHistory :=
        Core.Strategy.closeImpossible history key closureFresh
      closedHistory.elimClosed (by infer_instance)
  | _, .emptiness (oracle := _) closureFresh openBranch, _, history =>
      match Core.Strategy.closeIfEmpty history closureFresh with
      | .open => execute openBranch history
      | .closed closedHistory =>
          closedHistory.elimClosed (by infer_instance)

private noncomputable def executeProgram
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} (program : ClosingProgram Residual known)
    {current : Residual} (history : ExactLedger Residual current known) : False :=
  execute program.body history

end ClosingProgram

/-! ## Sealed counterexample opening and global target closure -/

/-- A framework-owned first-scope strategy.  It packages the canonical
minimal progress, branch-state initialization, and selection encoding without
exposing any of them to an application. -/
structure CounterexampleScope
    {P : Core.Problem.{uAmbient, uBranch}}
    (T : Core.Target P)
    [FactSystem (ProblemInput P)] where
  private mk ::
  selection : FactKey (ProblemInput P)
  private openScope :
    (object : P.Ambient) → (baseline : P.Baseline object) →
      (avoids : ¬ T.Predicate object) → OpenedScope selection

namespace CounterexampleScope

/-- Framework construction boundary for the canonical minimal-counterexample
scope of a domain strategy. -/
noncomputable def createMinimal
    {P : Core.Problem.{uAmbient, uBranch}}
    (T : Core.Target P)
    [FactSystem (ProblemInput P)]
    (_authority : FrameworkToken)
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P)
    (stateOf : (object : P.Ambient) → P.BranchState object)
    (selection : FactKey (ProblemInput P))
    (encode : (context :
        Core.MinimalCounterexampleContext P T.Predicate progress) →
      selection.At (selectedInput context)) :
    CounterexampleScope T where
  selection := selection
  openScope := fun object baseline avoids =>
    openMinimalCounterexampleScope T progress stateOf selection encode
      { object := object
        baseline := baseline
        branchState := stateOf object }
      avoids

end CounterexampleScope

/-- A sealed, total strategy DAG for one registered target.  It contains no
runtime result or proof callback; its private root is a trusted scope followed
by a closing exact-ledger program. -/
structure ClosingDag
    {P : Core.Problem.{uAmbient, uBranch}}
    (T : Core.Target P)
    [FactSystem (ProblemInput P)] where
  private mk ::
  private scope : CounterexampleScope T
  private program : ClosingProgram (ProblemInput P) [scope.selection]

namespace ClosingDag

/-- Safe authoring boundary: join one framework-owned scope to a total closing
program over the scope's exact selection index. -/
def ofCounterexampleScope
    {P : Core.Problem.{uAmbient, uBranch}}
    (T : Core.Target P)
    [FactSystem (ProblemInput P)]
    (scope : CounterexampleScope T)
    (program : ClosingProgram (ProblemInput P) [scope.selection]) :
    ClosingDag T :=
  .mk scope program

/-- The kernel-checked public theorem certified by a sealed closing DAG. -/
theorem statement
    {P : Core.Problem.{uAmbient, uBranch}}
    {T : Core.Target P}
    [FactSystem (ProblemInput P)]
    (dag : ClosingDag T) : T.Statement := by
  apply T.target_to_statement
  intro object baseline
  by_contra avoids
  let opened := dag.scope.openScope object baseline avoids
  exact ClosingProgram.executeProgram dag.program opened.history

end ClosingDag

end Hypostructure.Core.Strategy
