import Hypostructure.Core.Finite.Enumeration

/-!
# Canonical capacity-token accounting semantics

This registration contains only residual-indexed mathematical data.  Core
constructs the canonical assignment, exact label fibres, and aggregate
accounting ledger from these primitives.
-/

namespace Hypostructure.Core.Strategy.CanonicalCapacityTokenAccounting

universe uResidual uDemand uToken uRole uLabel uAggregateLabel

/-- Domain-neutral input semantics for canonical capacity-token accounting.

The finite schedules and primitive functions are properties of the stable
residual.  No selected token, assignment, partition, aggregate total,
terminal, or execution result is accepted from a proof application. -/
structure Registration (Residual : Type uResidual) where
  Demand : Residual → Type uDemand
  Token : Residual → Type uToken
  Role : Residual → Type uRole
  Label : Residual → Type uLabel
  demands :
    (residual : Residual) → Core.Finite.Enumeration (Demand residual)
  tokens :
    (residual : Residual) → Core.Finite.Enumeration (Token residual)
  completeLabels :
    (residual : Residual) →
      Core.Finite.CompleteEnumeration (Label residual)
  Eligible :
    (residual : Residual) → Demand residual → Token residual → Prop
  eligibleDecidable :
    (residual : Residual) → (demand : Demand residual) →
      (token : Token residual) →
        Decidable (Eligible residual demand token)
  demandWeight :
    (residual : Residual) → Demand residual → Nat
  tokenCapacity :
    (residual : Residual) → Token residual → Nat
  required : Residual → Nat
  roleOf :
    (residual : Residual) → Demand residual → Role residual
  labelOf :
    (residual : Residual) →
      Option (Token residual) → Role residual → Label residual
  labelCapacity :
    (residual : Residual) → Label residual → Nat
  aggregateLabel : Residual → Type uAggregateLabel
  aggregateLabelDecidableEq :
    (residual : Residual) → DecidableEq (aggregateLabel residual)
  memberAggregateLabel :
    (residual : Residual) → Label residual → aggregateLabel residual

end Hypostructure.Core.Strategy.CanonicalCapacityTokenAccounting
