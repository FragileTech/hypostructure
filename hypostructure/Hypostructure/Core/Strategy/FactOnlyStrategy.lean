import Hypostructure.Core.Strategy.ExactExecution

/-!
# Fact-only strategies and exact branch decisions

Two execution shapes recur in every structural spine.

*Fact-only steps.*  Most rows of a spine prove new theorems about the object
they were handed and change nothing else.  `factOnly` is that step: its
`refines` obligation is discharged by `RefinementSystem.refl`, which is the
ordinary choice when a step only adds facts.

*Branch decisions.*  A dichotomy is not a payload, a terminal, or a routing
token: each arm is a distinct semantic fact, and the arm a branch did **not**
take is absent from that branch's type-level key index.  `Decision` is the
result type that makes this so, and `decide` is the framework-owned runner
that produces it.  Because both arms commit against the same immutable prefix,
every fact proved before the decision remains visible on both.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uResidual uSubject uKey uValue

variable {Residual : Type uResidual}
variable [RefinementSystem.{uResidual, uSubject} Residual]
variable [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]

/-- A Strategy that preserves the residual and commits exactly the facts it
derives from its declared prerequisites. -/
@[reducible] noncomputable def factOnly
    (id : Lean.Name) (manifest : FactManifest Residual)
    (derive : (inputs : FactInputs manifest) →
      Core.Residual.FactKeys.Values inputs.current manifest.Produces)
    (checks : Nat := 0) (work : Nat := 0) :
    AtomicStrategy Residual :=
  AtomicCT.create exactLedgerInternal% id manifest
    FactInputs.current
    (fun inputs => RefinementSystem.refl inputs.current)
    (fun inputs => { facts := derive inputs, checks := checks, work := work })

/-! ## Exact branch decisions -/

/-- The outcome of a two-way decision.  The two constructors carry *different*
key indices, so a consumer of one arm cannot read the other arm's fact: it is
not in its type. -/
inductive Decision
    {current : Residual} {known : FactKeys Residual}
    (left right : FactKey Residual)
    (_previous : ExactLedger Residual current known) where
  | left (history : ExactLedger Residual current (left :: known))
  | right (history : ExactLedger Residual current (right :: known))

namespace Decision

/-- Run a decision against the canonical ledger.  The caller supplies the
exhaustive alternative as a `Sum` of the two arms' values at the current
residual; whichever arm it returns is the fact that gets committed, and the
other arm's key never enters this branch's index.

This is the only way a spine may record a dichotomy: there is no terminal,
payload, or route channel through which the other alternative could travel. -/
noncomputable def run
    {current : Residual} {known : FactKeys Residual}
    (previous : ExactLedger Residual current known)
    (left right : FactKey Residual)
    (id : Lean.Name)
    (alternatives : Sum (left.At current) (right.At current))
    (leftFresh : left ∉ known := by decide)
    (rightFresh : right ∉ known := by decide) :
    Decision left right previous :=
  match alternatives with
  | .inl value =>
      .left (ExactLedger.publishFact exactLedgerInternal% previous left value
        leftFresh id)
  | .inr value =>
      .right (ExactLedger.publishFact exactLedgerInternal% previous right value
        rightFresh id)

end Decision

end Hypostructure.Core.Strategy
