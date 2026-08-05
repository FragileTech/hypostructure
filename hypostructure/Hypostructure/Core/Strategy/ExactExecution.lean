import Hypostructure.Core.Strategy.FactManifest

/-!
# Canonical CT, Strategy, and closure execution

Atomic executors consume a sealed `FactInputs` view, refine its residual, and
commit exactly their declared output facts to the same `ExactLedger`.  CTs and
Strategies share this one input type, executor, and output type.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uResidual uSubject uKey uValue

/-- Complete indivisible output of one atomic executor. -/
structure AtomicResult
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (manifest : FactManifest Residual) (next : Residual) where
  facts : Core.Residual.FactKeys.Values next manifest.Produces
  checks : Nat := 0
  work : Nat := 0

/-- A sealed atomic CT.  Its implementation sees only the current residual
and the facts listed in `Requires`. -/
structure AtomicCT
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] where
  private mk ::
  id : Lean.Name
  manifest : FactManifest Residual
  private next : FactInputs manifest -> Residual
  private refines : (inputs : FactInputs manifest) ->
    RefinementSystem.Refines (next inputs) inputs.current
  private execute : (inputs : FactInputs manifest) ->
    AtomicResult manifest (next inputs)

namespace AtomicCT

/-- Framework construction boundary.  Proof DAG modules are restricted to
registered combinators by the API guard. -/
abbrev create
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (_authority : FrameworkToken)
    (id : Lean.Name) (manifest : FactManifest Residual)
    (next : FactInputs manifest -> Residual)
    (refines : (inputs : FactInputs manifest) ->
      RefinementSystem.Refines (next inputs) inputs.current)
    (execute : (inputs : FactInputs manifest) ->
      AtomicResult manifest (next inputs)) : AtomicCT Residual :=
  .mk id manifest next refines execute

/-- The residual selected by an atomic executor from the canonical ledger.
This projection exposes no input constructor or executor implementation; it is
the residual index used by `run`. -/
noncomputable def outputResidual
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (ct : AtomicCT Residual)
    [FactKeys.Available ct.manifest.Requires known]
    (previous : ExactLedger Residual current known) : Residual :=
  ct.next (FactInputs.ofLedger exactLedgerInternal% ct.manifest previous)

/-- Run and atomically append a CT.  Missing requirements fail during
elaboration.  The result index contains every produced fact followed by every
inherited fact, making history loss unrepresentable. -/
noncomputable def run
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (ct : AtomicCT Residual)
    [FactKeys.Available ct.manifest.Requires known]
    (previous : ExactLedger Residual current known)
    (fresh : List.Disjoint ct.manifest.Produces known := by decide) :
    ExactLedger Residual (ct.outputResidual previous)
      (ct.manifest.Produces ++ known) := by
  let inputs := FactInputs.ofLedger exactLedgerInternal% ct.manifest previous
  let result := ct.execute inputs
  change ExactLedger Residual (ct.next inputs) (ct.manifest.Produces ++ known)
  exact ExactLedger.append exactLedgerInternal% previous
    (ct.next inputs) (ct.refines inputs)
    result.facts ct.manifest.producesNonempty ct.manifest.producesUnique fresh
    { producer := ct.id
      checks := result.checks
      work := result.work }

end AtomicCT

/-- Strategies and CTs deliberately share one sealed executor and one exact
ledger output. -/
abbrev AtomicStrategy
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :=
  AtomicCT Residual

/-! ## Computable closure rules -/

/-- Registered semantic incompatibility. -/
class Incompatible
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (left right : FactKey Residual) where
  contradiction : (residual : Residual) ->
    left.At residual -> right.At residual -> False

/-- Registered semantic impossibility of a single fact.

A branch test must offer every alternative its domain admits, and some of those
alternatives are realized by no object at all.  A branch that commits such a
fact is uninhabited, and that is exactly what a closed terminal is.  Unlike
`Incompatible`, the contradiction is carried by one fact, so no second fact has
to be manufactured to record it. -/
class Impossible
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (key : FactKey Residual) where
  contradiction : (residual : Residual) -> key.At residual -> False

/-- Close from one impossible fact visible on this branch. -/
noncomputable def closeImpossible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (previous : ExactLedger Residual current known)
    (key : FactKey Residual)
    [Core.Residual.FactKeys.Has key known]
    [Impossible Residual key]
    (fresh : system.closureKey ∉ known := by decide) :
    ExactLedger Residual current (system.closureKey :: known) :=
  ExactLedger.publishFact exactLedgerInternal% previous system.closureKey
    (system.closureValue current {
    reason := .impossibleFact key.name
    contradiction := Impossible.contradiction current (ExactLedger.get previous key)
    }) fresh `Hypostructure.Core.Strategy.autoclose.impossible

/-- Optional exact emptiness decision for residual domains where emptiness is
computable. -/
class EmptinessOracle
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual] where
  Empty : Residual -> Prop
  decideEmpty : (residual : Residual) -> Decidable (Empty residual)
  impossible : (residual : Residual) -> Empty residual -> False

abbrev AutomaticClosureReason :=
  Hypostructure.Core.Residual.AutomaticClosureReason

abbrev ContradictionEvidence :=
  Hypostructure.Core.Residual.ClosureEvidence

/-- Close from two incompatible facts visible on this branch. -/
noncomputable def closeIncompatible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (previous : ExactLedger Residual current known)
    (left right : FactKey Residual)
    [Core.Residual.FactKeys.Has left known]
    [Core.Residual.FactKeys.Has right known]
    [Incompatible Residual left right]
    (fresh : system.closureKey ∉ known := by decide) :
    ExactLedger Residual current (system.closureKey :: known) :=
  ExactLedger.publishFact exactLedgerInternal% previous system.closureKey
    (system.closureValue current {
    reason := .incompatibleFacts left.name right.name
    contradiction := Incompatible.contradiction current
      (ExactLedger.get previous left) (ExactLedger.get previous right)
    }) fresh `Hypostructure.Core.Strategy.autoclose.incompatible

/-- Close a CT output when one declared output is incompatible with a visible
upstream fact. -/
noncomputable def AtomicCT.runAndCloseIncompatible
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (ct : AtomicCT Residual)
    [FactKeys.Available ct.manifest.Requires known]
    (previous : ExactLedger Residual current known)
    (left right : FactKey Residual)
    [Core.Residual.FactKeys.Has left known]
    [Core.Residual.FactKeys.Has right ct.manifest.Produces]
    [Incompatible Residual left right]
    (commitFresh : List.Disjoint ct.manifest.Produces known := by decide)
    (closureFresh : system.closureKey ∉
      ct.manifest.Produces ++ known := by decide) :=
  let output := ct.run previous commitFresh
  closeIncompatible output left right closureFresh

/-- Decidable automatic-emptiness result. -/
inductive EmptinessResult
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    [oracle : EmptinessOracle Residual]
    {current : Residual} {known : FactKeys Residual}
    (previous : ExactLedger Residual current known) where
  | open
  | closed (ledger :
      ExactLedger Residual current (system.closureKey :: known))

noncomputable def closeIfEmpty
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    [oracle : EmptinessOracle Residual]
    {current : Residual} {known : FactKeys Residual}
    (previous : ExactLedger Residual current known)
    (fresh : system.closureKey ∉ known := by decide) :
    EmptinessResult previous :=
  match oracle.decideEmpty current with
  | .isFalse _ => .open
  | .isTrue empty => .closed (ExactLedger.publishFact exactLedgerInternal% previous
      system.closureKey (system.closureValue current {
        reason := .emptyResidual
        contradiction := oracle.impossible current empty
      }) fresh `Hypostructure.Core.Strategy.autoclose.empty)

/-- Run a CT and immediately apply the residual domain's emptiness oracle. -/
noncomputable def AtomicCT.runAndCloseIfEmpty
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    [EmptinessOracle Residual]
    {current : Residual} {known : FactKeys Residual}
    (ct : AtomicCT Residual)
    [FactKeys.Available ct.manifest.Requires known]
    (previous : ExactLedger Residual current known)
    (commitFresh : List.Disjoint ct.manifest.Produces known := by decide)
    (closureFresh : system.closureKey ∉
      ct.manifest.Produces ++ known := by decide) :
    EmptinessResult (ct.run previous commitFresh) :=
  closeIfEmpty (ct.run previous commitFresh) closureFresh

/-- Decode a visible domain target fact at the stable refinement subject. -/
noncomputable def closeTarget
    {Residual : Type uResidual}
    [system : RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (previous : ExactLedger Residual current known)
    (key : FactKey Residual) [Core.Residual.FactKeys.Has key known]
    (Target : system.Subject -> Prop)
    (decode : (residual : Residual) -> key.At residual ->
      Target (system.subject residual)) :
    Target (system.subject current) :=
  decode current (ExactLedger.get previous key)

end Hypostructure.Core.Strategy
