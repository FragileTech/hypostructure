import Hypostructure.Core.Strategy.ClosingProgram

/-!
# Typed partial strategy programs

`StrategyProgram known frontier` is the authoring form of a finite strategy
whose unresolved leaves are recorded by their exact branch-local fact indices.
It has no interpreter.  Execution is available only after the frontier is
definitionally empty, when Core can lower it to a sealed `ClosingProgram`.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uAmbient uBranch uResidual uSubject uKey uValue

private inductive StrategyProgramBody
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    (known : FactKeys Residual) ->
      (frontier : List (FactKeys Residual)) ->
      Type (max (max (uResidual + 1) (uKey + 1)) (uValue + 3)) where
  | defer {known : FactKeys Residual} :
      StrategyProgramBody Residual known [known]
  | terminal {known : FactKeys Residual}
      (program : ClosingProgram Residual known) :
      StrategyProgramBody Residual known []
  | atomic {known : FactKeys Residual} {frontier : List (FactKeys Residual)}
      (ct : AtomicCT Residual)
      [available : FactKeys.Available ct.manifest.Requires known]
      (knownOpen : system.closureKey ∉ known)
      (outputsOpen : system.closureKey ∉ ct.manifest.Produces)
      (fresh : List.Disjoint ct.manifest.Produces known)
      (next : StrategyProgramBody Residual
        (ct.manifest.Produces ++ known) frontier) :
      StrategyProgramBody Residual known frontier
  | branch {known : FactKeys Residual}
      {leftFrontier rightFrontier : List (FactKeys Residual)}
      (decision : AtomicDecision Residual)
      [available : FactKeys.Available decision.manifest.Requires known]
      (knownOpen : system.closureKey ∉ known)
      (leftFresh : decision.manifest.left ∉ known)
      (rightFresh : decision.manifest.right ∉ known)
      (left : StrategyProgramBody Residual
        (decision.manifest.left :: known) leftFrontier)
      (right : StrategyProgramBody Residual
        (decision.manifest.right :: known) rightFrontier) :
      StrategyProgramBody Residual known (leftFrontier ++ rightFrontier)

/-- A finite strategy with a statically visible list of unresolved leaves. -/
structure StrategyProgram
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (known : FactKeys Residual) (frontier : List (FactKeys Residual)) where
  private mk ::
  private body : StrategyProgramBody Residual known frontier

namespace StrategyProgram

/-- Leave the current exact branch index as an explicit unresolved leaf. -/
def defer
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} : StrategyProgram Residual known [known] :=
  .mk .defer

/-- Embed a locally total branch.  A closed branch adds no frontier entry. -/
def ofClosing
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} (program : ClosingProgram Residual known) :
    StrategyProgram Residual known [] :=
  .mk (.terminal program)

def closed
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} [FactKeys.Has system.closureKey known] :
    StrategyProgram Residual known [] :=
  ofClosing ClosingProgram.closed

def closeIncompatible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} (left right : FactKey Residual)
    [FactKeys.Has left known] [FactKeys.Has right known]
    [Incompatible Residual left right]
    (closureFresh : system.closureKey ∉ known := by decide) :
    StrategyProgram Residual known [] :=
  ofClosing (ClosingProgram.closeIncompatible left right closureFresh)

def closeImpossible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} (key : FactKey Residual)
    [FactKeys.Has key known] [Impossible Residual key]
    (closureFresh : system.closureKey ∉ known := by decide) :
    StrategyProgram Residual known [] :=
  ofClosing (ClosingProgram.closeImpossible key closureFresh)

/-- Prepend a trusted atomic CT without changing the unresolved leaves. -/
def atomic
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} {frontier : List (FactKeys Residual)}
    (ct : AtomicCT Residual)
    [FactKeys.Available ct.manifest.Requires known]
    (next : StrategyProgram Residual (ct.manifest.Produces ++ known) frontier)
    (knownOpen : system.closureKey ∉ known := by decide)
    (outputsOpen : system.closureKey ∉ ct.manifest.Produces := by decide)
    (fresh : List.Disjoint ct.manifest.Produces known := by decide) :
    StrategyProgram Residual known frontier :=
  .mk (.atomic ct knownOpen outputsOpen fresh next.body)

/-- Prepend an exhaustive decision.  Its unresolved frontier is the ordered
concatenation of the two branch-local frontiers. -/
def branch
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual}
    {leftFrontier rightFrontier : List (FactKeys Residual)}
    (decision : AtomicDecision Residual)
    [FactKeys.Available decision.manifest.Requires known]
    (left : StrategyProgram Residual
      (decision.manifest.left :: known) leftFrontier)
    (right : StrategyProgram Residual
      (decision.manifest.right :: known) rightFrontier)
    (knownOpen : system.closureKey ∉ known := by decide)
    (leftFresh : decision.manifest.left ∉ known := by decide)
    (rightFresh : decision.manifest.right ∉ known := by decide) :
    StrategyProgram Residual known (leftFrontier ++ rightFrontier) :=
  .mk (.branch decision knownOpen leftFresh rightFresh left.body right.body)

private noncomputable def lower
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    {known : FactKeys Residual} -> {frontier : List (FactKeys Residual)} ->
      StrategyProgramBody Residual known frontier -> frontier = [] ->
      ClosingProgram Residual known
  | _, _, .defer, impossible => by cases impossible
  | _, _, .terminal program, _ => program
  | _, _, .atomic ct (available := _) knownOpen outputsOpen fresh next, empty =>
      ClosingProgram.atomic ct (lower next empty) knownOpen outputsOpen fresh
  | _, _, .branch decision (available := _) knownOpen leftFresh rightFresh left right, empty =>
      have arms := List.append_eq_nil_iff.mp empty
      ClosingProgram.branch decision
        (lower left arms.1) (lower right arms.2)
        knownOpen leftFresh rightFresh

/-- Seal a strategy only when its type proves that no unresolved leaf remains. -/
noncomputable def complete
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} (program : StrategyProgram Residual known []) :
    ClosingProgram Residual known :=
  lower program.body rfl

end StrategyProgram

structure StrategyDag
    {P : Core.Problem.{uAmbient, uBranch}}
    (T : Core.Target P) [FactSystem (ProblemInput P)]
    (frontier : List (FactKeys (ProblemInput P))) where
  private mk ::
  private scope : CounterexampleScope T
  private program : StrategyProgram (ProblemInput P) [scope.selection] frontier

namespace StrategyDag

def ofCounterexampleScope
    {P : Core.Problem.{uAmbient, uBranch}} (T : Core.Target P)
    [FactSystem (ProblemInput P)] {frontier : List (FactKeys (ProblemInput P))}
    (scope : CounterexampleScope T)
    (program : StrategyProgram (ProblemInput P) [scope.selection] frontier) :
    StrategyDag T frontier :=
  .mk scope program

/-- Empty frontier is the sole bridge from partial topology to execution. -/
noncomputable def complete
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    [FactSystem (ProblemInput P)] (dag : StrategyDag T []) : ClosingDag T :=
  ClosingDag.ofCounterexampleScope T dag.scope
    (StrategyProgram.complete dag.program)

end StrategyDag

end Hypostructure.Core.Strategy
