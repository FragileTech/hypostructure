import Hypostructure.Core.Residual.ExactLedger

/-!
# Typed fact manifests, sealed inputs, and deterministic autorouting

Requirements and productions are exact keys from the residual domain's one
`FactSystem`.  Values live only in `ExactLedger`; a manifest carries schemas,
never payloads or a parallel store.  Executors receive `FactInputs`, so they
can inspect only the current residual and their declared prerequisites.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uResidual uSubject uKey uValue

/-- Closed input/output contract for one CT or Strategy.  Every execution must
append at least one fact, and neither side may name a key twice. -/
structure FactManifest
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] where
  Requires : FactKeys Residual
  Produces : FactKeys Residual
  requiresUnique : Requires.Nodup
  producesUnique : Produces.Nodup
  producesNonempty : Produces ≠ []

namespace FactManifest

def requiredNames
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual) : List Lean.Name :=
  manifest.Requires.names

def producedNames
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual) : List Lean.Name :=
  manifest.Produces.names

/-- Exact missing-key set.  Names are used only when rendering diagnostics. -/
def missingKeys
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual)
    (available : FactKeys Residual) : FactKeys Residual :=
  manifest.Requires.filter fun key => !available.contains key

def missing
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual)
    (available : FactKeys Residual) : List Lean.Name :=
  (manifest.missingKeys available).names

def ready
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual)
    (available : FactKeys Residual) : Bool :=
  (manifest.missingKeys available).isEmpty

end FactManifest

/-! ## Sealed manifest inputs -/

namespace FactKeys

/-- Internal extraction of exactly the required values from the current
ledger snapshot.  The constructor is private, and exact structural keys—not
names—control every extraction. -/
class Available
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (required known : FactKeys Residual) where
  private mk ::
  private values : {current : Residual} ->
    ExactLedger Residual current known ->
      Core.Residual.FactKeys.Values current required

instance
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {known : FactKeys Residual} : Available ([] : FactKeys Residual) known where
  values _ := .nil

noncomputable instance
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} {tail known : FactKeys Residual}
    [found : Core.Residual.FactKeys.Has key known]
    [rest : Available tail known] :
    Available (key :: tail) known where
  values history :=
    .cons (ExactLedger.get history key) (rest.values history)

end FactKeys

/-- The complete view supplied to an atomic executor.  It contains no ledger
cursor and exposes no predecessor path. -/
structure FactInputs
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual) where
  private mk ::
  current : Residual
  private facts : Core.Residual.FactKeys.Values current manifest.Requires

namespace FactInputs

/-- Build the sealed view from the sole canonical ledger. -/
noncomputable def ofLedger
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (_authority : FrameworkToken)
    (manifest : FactManifest Residual)
    [available : FactKeys.Available manifest.Requires known]
    (history : ExactLedger Residual current known) : FactInputs manifest :=
  .mk current (available.values history)

/-- Read one declared prerequisite.  Undeclared keys are rejected during
elaboration. -/
noncomputable def get
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {manifest : FactManifest Residual} (inputs : FactInputs manifest)
    (key : FactKey Residual)
    [Core.Residual.FactKeys.Has key manifest.Requires] :
    key.At inputs.current :=
  Core.Residual.FactKeys.Values.get key inputs.facts

end FactInputs

/-! ## Deterministic readiness and autorouting -/

/-- One scheduler candidate.  `order` is its stable authored order. -/
structure RoutedTask
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] where
  id : Lean.Name
  order : Nat
  manifest : FactManifest Residual

namespace RoutedTask

def preferred
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (left right : RoutedTask Residual) : Bool :=
  left.order < right.order ||
    (left.order = right.order && left.id.toString < right.id.toString)

private def insert
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (task : RoutedTask Residual) :
    List (RoutedTask Residual) -> List (RoutedTask Residual)
  | [] => [task]
  | head :: tail =>
      if task.preferred head then task :: head :: tail
      else head :: insert task tail

def authoredOrder
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (tasks : List (RoutedTask Residual)) : List (RoutedTask Residual) :=
  tasks.foldr insert []

private def selectReady
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (available : FactKeys Residual) (tasks : List (RoutedTask Residual)) :
    Option (RoutedTask Residual) :=
  (authoredOrder tasks).find? fun task => task.manifest.ready available

structure Deadlock where
  available : List Lean.Name
  missing : List (Lean.Name × List Lean.Name)
  deriving Repr

private def deadlock
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (available : FactKeys Residual) (tasks : List (RoutedTask Residual)) :
    Deadlock :=
  { available := available.names
    missing := (authoredOrder tasks).map fun task =>
      (task.id, task.manifest.missing available) }

inductive RouteDecision
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] where
  | closed
  | run (task : RoutedTask Residual)
  | deadlock (diagnostic : Deadlock)

private def dispatch
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (available : FactKeys Residual) (tasks : List (RoutedTask Residual)) :
    RouteDecision Residual :=
  if available.contains system.closureKey then .closed
  else
    match selectReady available tasks with
    | some task => .run task
    | none => .deadlock (deadlock available tasks)

/-- Select from the exact branch-local key index of the canonical ledger.
A closed branch has no runnable task. -/
def selectFor
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (_history : ExactLedger Residual current known)
    (tasks : List (RoutedTask Residual)) : Option (RoutedTask Residual) :=
  if known.contains system.closureKey then none else selectReady known tasks

def dispatchFor
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (_history : ExactLedger Residual current known)
    (tasks : List (RoutedTask Residual)) : RouteDecision Residual :=
  dispatch known tasks

end RoutedTask
end Hypostructure.Core.Strategy
