import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.DependentOwnerGlueCapacity
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics

/-!
# Finite-state capacity semantics

Residual-indexed primitive data for the reusable CT17 → CT14 Strategy.
The registration contains no query, ledger, execution result, terminal,
route, or selected outcome.

Every schedule- and value-returning field additionally accepts the exact
independent-rank value, the exact finite-barrier summary, and the exact
local-supply summary Core reads from the accumulated ledger, so a domain
presentation may vary its carriers, values, or laws with those inherited
facts.  The registration itself never stores a `Query`, a `Previous` stage,
or any of these three values: they arrive only as plain arguments supplied
by `Profile` at the literal predecessor.  `FiniteBarrierEnumeration.Summary`
and `LocalSupplyLowerBound.Summary` are plain records of `Nat`/`List` fields
with no dependence on `Previous`/`Residual`/CT machinery, so naming them here
introduces no capability, ledger, or execution dependence.
-/

namespace Hypostructure.Core.Strategy.FiniteStateCapacity

universe uResidual uAmbient uData

/-- Universe-pinned joint profile used by the registration fields below. -/
abbrev JointProfile :=
  Core.DependentOwnerGlueCapacity.BaseProfile.{
    uData, uData, uData, uData, uData}

/-- Inert residual presentation consumed by CT17 and CT14.

`AmbientItem` is the inherited ambient carrier of the local-supply
predecessor, i.e. the carrier of the normalized support complement that
predecessor already reads.  The realized-state family is indexed by the exact
`Core.Finite.Enumeration` of that carrier, in the same argument position
`LocalSupplyLowerBound.Registration.members` uses: `def:remainder-entropy`'s
`𝒢(R)` lives on the inherited vertex set `V(R)`, so the complement reaches the
registration rather than being reconstructed from a `Nat`. -/
structure Registration (Residual : Type uResidual)
    (AmbientItem : Residual → Type uAmbient) where
  Target : Residual → Type uData
  Offset : Residual → Type uData
  Position : (residual : Residual) → Nat → Type uData
  Value : Residual → Type uData
  targets : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → Core.Finite.Enumeration (Target residual)
  offsets : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → Core.Finite.Enumeration (Offset residual)
  scales : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → Core.Finite.Enumeration Nat
  selectedScale : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  selectedScale_mem : ∀ residual rank barrier supply,
    selectedScale residual rank barrier supply ∈
      (scales residual rank barrier supply).values
  positions : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → (scale : Nat) →
      Core.Finite.Enumeration (Position residual scale)
  finiteScaleLimit : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  targetValue : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → Target residual → Value residual
  blockValue : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → (scale : Nat) →
      Position residual scale → Offset residual → Value residual
  orbitValue : (residual : Residual) → Nat → FiniteBarrierEnumeration.Summary →
    LocalSupplyLowerBound.Summary → (scale : Nat) →
      Offset residual → Value residual
  Compatible : (residual : Residual) →
    Target residual → Offset residual → Prop
  compatibleDecidable : (residual : Residual) →
    (target : Target residual) → (offset : Offset residual) →
      Decidable (Compatible residual target offset)
  valueDecidableEq : (residual : Residual) → DecidableEq (Value residual)
  Label : Residual → Type uData
  memberLowerMass : (residual : Residual) → (rank : Nat) →
    (barrier : FiniteBarrierEnumeration.Summary) →
    (supply : LocalSupplyLowerBound.Summary) →
      Position residual (selectedScale residual rank barrier supply) → Nat
  memberCapacity : (residual : Residual) → (rank : Nat) →
    (barrier : FiniteBarrierEnumeration.Summary) →
    (supply : LocalSupplyLowerBound.Summary) →
      Position residual (selectedScale residual rank barrier supply) →
        Option Nat
  memberLabel : (residual : Residual) → (rank : Nat) →
    (barrier : FiniteBarrierEnumeration.Summary) →
    (supply : LocalSupplyLowerBound.Summary) →
      Position residual (selectedScale residual rank barrier supply) →
        Option (Label residual)
  labelDecidableEq : (residual : Residual) → DecidableEq (Label residual)
  /-- Literal realized-state carrier on the inherited support complement.
  Core computes its cardinality and owns the ensuing natural-power
  dichotomy. -/
  RealizedState : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Type uData
  realizedStateFinite : ∀ residual complement rank barrier supply,
    Finite (RealizedState residual complement rank barrier supply)
  realizedStateNonempty : ∀ residual complement rank barrier supply,
    Nonempty (RealizedState residual complement rank barrier supply)
  /-- Ambient order and exact remainder cardinality for the state-power
  comparison. They remain residual observations; neither is a stage, ledger
  entry, selected branch, or computed result.  `remainderCard` is read off the
  inherited complement, so the entropy exponent and the realized-state
  carrier's vertex set are the same `|R|`. -/
  ambientOrder : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  remainderCard : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  statePowerExponent : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  statePowerExponent_pos : ∀ residual rank barrier supply,
    0 < statePowerExponent residual rank barrier supply
  /-- Two residual-owned power bases. Core raises both to the exact
  independent rank read from the predecessor ledger and owns the exhaustive
  comparison. -/
  forcedBase : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  flatBase : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  flatBase_pos : ∀ residual rank barrier supply,
    0 < flatBase residual rank barrier supply
  /-- Recoverable joint state/owner glue. Core, rather than the registration,
  proves the joint finite-capacity inequality from this symbolic profile. -/
  jointProfile : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary →
      JointProfile.{uData}
  jointBaseCard : ∀ residual complement rank barrier supply,
    Nat.card
        (jointProfile residual complement rank barrier supply).Base =
      Nat.card (RealizedState residual complement rank barrier supply)
  jointExponent : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  jointWeight : ∀ residual complement rank barrier supply,
    (jointProfile residual complement rank barrier supply).Owner → Nat
  jointLocalLower : ∀ residual complement rank barrier supply owner,
    2 ^ jointWeight residual complement rank barrier supply owner ≤
      Nat.card
          ((jointProfile residual complement rank barrier supply).Local owner) ^
        jointExponent residual rank barrier supply
  jointPaidExponent : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  jointPaidExponent_exact : ∀ residual complement rank barrier supply,
    (jointProfile residual complement rank barrier supply).weightSum
        (jointWeight residual complement rank barrier supply) =
      jointPaidExponent residual rank barrier supply
  jointDesiredExponent : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  jointErrorExponent : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  jointCapacity : (residual : Residual) → Nat →
    FiniteBarrierEnumeration.Summary → LocalSupplyLowerBound.Summary → Nat
  jointCapacity_pos : ∀ residual rank barrier supply,
    0 < jointCapacity residual rank barrier supply
  jointCodeCapacity : ∀ residual complement rank barrier supply,
    Nat.card (jointProfile residual complement rank barrier supply).Code ≤
      jointCapacity residual rank barrier supply
  jointDesiredExponent_exact : ∀ residual rank barrier supply,
    jointDesiredExponent residual rank barrier supply =
      jointPaidExponent residual rank barrier supply +
        jointErrorExponent residual rank barrier supply
  /-- Optional registered closure of the non-capacity output: the
  residual-owned facts under which the CT17/CT14 composition has no
  non-capacity alternative at all.

  This is not a routing decision and not an asserted terminal.  Every
  conjunct is a statement about data the registration already carries, read
  in the contrapositive:

  * the first four conjuncts say the registered compatibility relation, the
    selected scale, the position schedule, and the block values leave CT17
    with no incompatibility, orbit, target-hit, or exhaustion alternative;
  * the next three say the registered member capacity, member label, and
    member lower mass leave CT14 with no unbounded-member, missing-label, or
    aggregate alternative.

  There is no entropy conjunct, and none is owed.  `prop:two-budget` closes
  this branch by *routing*: "in every case the surviving residual is
  subsequently passed to the large-budget net-charge analysis", and
  `rem:closure-robust` records that "the curvature-rank and forced-cost
  machinery is not required for the net-charge closure outside the explicit
  residuals".  So neither the state-power comparison nor the forced/flat
  realization is an obligation here: all three of `prop:two-budget`'s
  branches -- high entropy, repetitive low entropy, nonrepetitive low
  entropy -- ride the capacity side into
  `FiniteStateNetChargeContinuation`, and the registration is asked only for
  the schedule facts that keep the two CT executions off their degenerate
  terminals.

  Supplying this field lets Core eliminate the non-capacity output as vacuous
  instead of retaining it as an open branch endpoint.  Registrations whose
  non-capacity alternative is genuinely inhabited leave this `none`, and that
  output stays live exactly as before. -/
  nonCapacityImpossible :
    Option (PLift
      ((∀ (residual : Residual) (target : Target residual)
            (offset : Offset residual),
          Compatible residual target offset) ∧
        (∀ residual rank barrier supply,
          selectedScale residual rank barrier supply ≤
            finiteScaleLimit residual rank barrier supply) ∧
        (∀ residual rank barrier supply,
          0 < (positions residual rank barrier supply
            (selectedScale residual rank barrier supply)).card) ∧
        (∀ residual rank barrier supply (scale : Nat)
            (position : Position residual scale) (offset : Offset residual)
            (target : Target residual),
          blockValue residual rank barrier supply scale position offset ≠
            targetValue residual rank barrier supply target) ∧
        (∀ residual rank barrier supply position,
          memberCapacity residual rank barrier supply position ≠ none) ∧
        (∀ residual rank barrier supply position,
          memberLabel residual rank barrier supply position ≠ none) ∧
        (∀ residual rank barrier supply position,
          memberLowerMass residual rank barrier supply position ≤
            (memberCapacity residual rank barrier supply position).getD 0))) :=
      none

end Hypostructure.Core.Strategy.FiniteStateCapacity
