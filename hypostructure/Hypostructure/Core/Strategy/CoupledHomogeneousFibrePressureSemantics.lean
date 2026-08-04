import Hypostructure.CT13.Capability
import Hypostructure.Core.Finite.Enumeration

/-!
# Coupled homogeneous fibre pressure semantics

The registration contains only residual-indexed mathematical carriers,
complete schedules, primitive observations, and decision procedures.  The
strategy implementation delegates every partition, payer and fallback
selection, reconciliation, aggregate comparison, ledger extension, terminal,
and work bound to CT9, CT13, and CT14.
-/

namespace Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure

universe uResidual uItem uToken uRole uLabel uPayer uObstruction uResource
  uMember uAggregateLabel

structure Registration (Residual : Type uResidual) where
  Item : Residual → Type uItem
  Token : Residual → Type uToken
  Role : Residual → Type uRole
  Label : Residual → Type uLabel
  items : (residual : Residual) →
    Core.Finite.Enumeration (Item residual)
  completeLabels : (residual : Residual) →
    Core.Finite.CompleteEnumeration (Label residual)
  labelOf : (residual : Residual) →
    Item residual → Label residual
  fibreCapacity : (residual : Residual) →
    Label residual → Nat
  Payer : Residual → Type uPayer
  Obstruction : Residual → Type uObstruction
  Resource : Residual → Type uResource
  payers : (residual : Residual) →
    Core.Finite.Enumeration (Payer residual)
  obstructions : (residual : Residual) →
    CT13.ObstructionSchedule (Obstruction residual)
  tierTwo : (residual : Residual) →
    Obstruction residual → Core.Finite.Enumeration (Payer residual)
  Eligible : (residual : Residual) → Payer residual → Prop
  obstructionCost : (residual : Residual) →
    Obstruction residual → Nat
  payerResource : (residual : Residual) →
    Payer residual → Resource residual
  charge : (residual : Residual) → Payer residual → Nat
  demand : Residual → Nat
  eligibleDecidable : (residual : Residual) →
    (payer : Payer residual) → Decidable (Eligible residual payer)
  resourceDecidableEq : (residual : Residual) →
    DecidableEq (Resource residual)
  Member : Residual → Type uMember
  AggregateLabel : Residual → Type uAggregateLabel
  members : (residual : Residual) →
    Core.Finite.Enumeration (Member residual)
  memberLowerMass : (residual : Residual) →
    Member residual → Nat
  memberCapacity : (residual : Residual) →
    Member residual → Option Nat
  memberLabel : (residual : Residual) →
    Member residual → Option (AggregateLabel residual)
  aggregateLabelDecidableEq : (residual : Residual) →
    DecidableEq (AggregateLabel residual)

end Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure
