import Hypostructure.Core.Strategy.FiniteStateCapacitySemantics
import Hypostructure.PDE.Model

/-!
# PDE finite-state capacity specialization

This module specializes the residual-indexed primitive observations consumed
by Core's sealed `FiniteStateCapacity` Strategy to an exact represented PDE
state.  It owns no query, ledger, execution, branch, route, or computed
outcome.
-/

namespace Hypostructure.PDE.Strategy.FiniteStateCapacity

open Hypostructure

universe uModel uResidual uAmbient uData

/-- Represented-state presentation of the primitive CT17 and CT14
observations.  Core supplies the inherited rank, barrier, and local-supply
values and performs all finite computation. -/
structure Registration (M : PDE.LocalModel.{uModel})
    (Residual : Type uResidual)
    (AmbientItem : Residual → Type uAmbient) where
  state : Residual → M.problem.Ambient
  Target : (residual : Residual) → M.problem.Ambient → Type uData
  Offset : (residual : Residual) → M.problem.Ambient → Type uData
  Position : (residual : Residual) →
    M.problem.Ambient → Nat → Type uData
  Value : (residual : Residual) → M.problem.Ambient → Type uData
  targets : (residual : Residual) → (state : M.problem.Ambient) →
    Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
    Core.Strategy.LocalSupplyLowerBound.Summary →
      Core.Finite.Enumeration (Target residual state)
  offsets : (residual : Residual) → (state : M.problem.Ambient) →
    Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
    Core.Strategy.LocalSupplyLowerBound.Summary →
      Core.Finite.Enumeration (Offset residual state)
  scales : (residual : Residual) → (state : M.problem.Ambient) →
    Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
    Core.Strategy.LocalSupplyLowerBound.Summary →
      Core.Finite.Enumeration Nat
  selectedScale :
    (residual : Residual) → (state : M.problem.Ambient) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  selectedScale_mem : ∀ residual state rank barrier supply,
    selectedScale residual state rank barrier supply ∈
      (scales residual state rank barrier supply).values
  positions :
    (residual : Residual) → (state : M.problem.Ambient) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → (scale : Nat) →
        Core.Finite.Enumeration (Position residual state scale)
  finiteScaleLimit :
    (residual : Residual) → (state : M.problem.Ambient) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  targetValue :
    (residual : Residual) → (state : M.problem.Ambient) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary →
        Target residual state → Value residual state
  blockValue :
    (residual : Residual) → (state : M.problem.Ambient) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → (scale : Nat) →
        Position residual state scale → Offset residual state →
          Value residual state
  orbitValue :
    (residual : Residual) → (state : M.problem.Ambient) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → (scale : Nat) →
        Offset residual state → Value residual state
  Compatible :
    (residual : Residual) → (state : M.problem.Ambient) →
      Target residual state → Offset residual state → Prop
  compatibleDecidable :
    (residual : Residual) → (state : M.problem.Ambient) →
      (target : Target residual state) → (offset : Offset residual state) →
        Decidable (Compatible residual state target offset)
  valueDecidableEq :
    (residual : Residual) → (state : M.problem.Ambient) →
      DecidableEq (Value residual state)
  Label : (residual : Residual) → M.problem.Ambient → Type uData
  memberLowerMass :
    (residual : Residual) → (state : M.problem.Ambient) →
      (rank : Nat) → (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary) →
      (supply : Core.Strategy.LocalSupplyLowerBound.Summary) →
        Position residual state
          (selectedScale residual state rank barrier supply) → Nat
  memberCapacity :
    (residual : Residual) → (state : M.problem.Ambient) →
      (rank : Nat) → (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary) →
      (supply : Core.Strategy.LocalSupplyLowerBound.Summary) →
        Position residual state
          (selectedScale residual state rank barrier supply) → Option Nat
  memberLabel :
    (residual : Residual) → (state : M.problem.Ambient) →
      (rank : Nat) → (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary) →
      (supply : Core.Strategy.LocalSupplyLowerBound.Summary) →
        Position residual state
          (selectedScale residual state rank barrier supply) →
            Option (Label residual state)
  labelDecidableEq :
    (residual : Residual) → (state : M.problem.Ambient) →
      DecidableEq (Label residual state)
  RealizedState : (residual : Residual) →
    (state : M.problem.Ambient) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Type uData
  realizedStateFinite : (residual : Residual) →
    (state : M.problem.Ambient) → ∀ complement rank barrier supply,
      Finite (RealizedState residual state complement rank barrier supply)
  realizedStateNonempty : (residual : Residual) →
    (state : M.problem.Ambient) → ∀ complement rank barrier supply,
      Nonempty (RealizedState residual state complement rank barrier supply)
  ambientOrder : (residual : Residual) →
    (state : M.problem.Ambient) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  remainderCard : (residual : Residual) →
    (state : M.problem.Ambient) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  statePowerExponent : (residual : Residual) →
    (state : M.problem.Ambient) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  statePowerExponent_pos : ∀ residual state rank barrier supply,
    0 < statePowerExponent residual state rank barrier supply
  forcedBase : (residual : Residual) → (state : M.problem.Ambient) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  flatBase : (residual : Residual) → (state : M.problem.Ambient) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  flatBase_pos : ∀ residual state rank barrier supply,
    0 < flatBase residual state rank barrier supply
  jointProfile : (residual : Residual) → (state : M.problem.Ambient) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary →
        Core.DependentOwnerGlueCapacity.BaseProfile.{
          uData, uData, uData, uData, uData}
  jointBaseCard : ∀ residual state complement rank barrier supply,
    Nat.card
        (jointProfile residual state complement rank barrier supply).Base =
      Nat.card
        (RealizedState residual state complement rank barrier supply)
  jointExponent : (residual : Residual) → (state : M.problem.Ambient) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointWeight : ∀ residual state complement rank barrier supply,
    (jointProfile residual state complement rank barrier supply).Owner → Nat
  jointLocalLower : ∀ residual state complement rank barrier supply owner,
    2 ^ jointWeight residual state complement rank barrier supply owner ≤
      Nat.card
          ((jointProfile residual state complement rank barrier
            supply).Local owner) ^
        jointExponent residual state rank barrier supply
  jointPaidExponent : (residual : Residual) →
    (state : M.problem.Ambient) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointPaidExponent_exact : ∀ residual state complement rank barrier supply,
    (jointProfile residual state complement rank barrier supply).weightSum
        (jointWeight residual state complement rank barrier supply) =
      jointPaidExponent residual state rank barrier supply
  jointDesiredExponent : (residual : Residual) → (state : M.problem.Ambient) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointErrorExponent : (residual : Residual) → (state : M.problem.Ambient) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointCapacity : (residual : Residual) → (state : M.problem.Ambient) → Nat →
    Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointCapacity_pos : ∀ residual state rank barrier supply,
    0 < jointCapacity residual state rank barrier supply
  jointCodeCapacity : ∀ residual state complement rank barrier supply,
    Nat.card
        (jointProfile residual state complement rank barrier supply).Code ≤
      jointCapacity residual state rank barrier supply
  jointDesiredExponent_exact : ∀ residual state rank barrier supply,
    jointDesiredExponent residual state rank barrier supply =
      jointPaidExponent residual state rank barrier supply +
        jointErrorExponent residual state rank barrier supply

namespace Registration

/-- Substitute the exact represented state into Core's existing
registration.  No finite scan, comparison, or branch is recomputed here. -/
def toCore
    (registration :
      Registration.{uModel, uResidual, uAmbient, uData} M Residual
        AmbientItem) :
    Core.Strategy.FiniteStateCapacity.Registration.{
      uResidual, uAmbient, uData}
      Residual AmbientItem where
  Target := fun residual =>
    registration.Target residual (registration.state residual)
  Offset := fun residual =>
    registration.Offset residual (registration.state residual)
  Position := fun residual =>
    registration.Position residual (registration.state residual)
  Value := fun residual =>
    registration.Value residual (registration.state residual)
  targets := fun residual =>
    registration.targets residual (registration.state residual)
  offsets := fun residual =>
    registration.offsets residual (registration.state residual)
  scales := fun residual =>
    registration.scales residual (registration.state residual)
  selectedScale := fun residual =>
    registration.selectedScale residual (registration.state residual)
  selectedScale_mem := fun residual =>
    registration.selectedScale_mem residual (registration.state residual)
  positions := fun residual =>
    registration.positions residual (registration.state residual)
  finiteScaleLimit := fun residual =>
    registration.finiteScaleLimit residual (registration.state residual)
  targetValue := fun residual =>
    registration.targetValue residual (registration.state residual)
  blockValue := fun residual =>
    registration.blockValue residual (registration.state residual)
  orbitValue := fun residual =>
    registration.orbitValue residual (registration.state residual)
  Compatible := fun residual =>
    registration.Compatible residual (registration.state residual)
  compatibleDecidable := fun residual =>
    registration.compatibleDecidable residual (registration.state residual)
  valueDecidableEq := fun residual =>
    registration.valueDecidableEq residual (registration.state residual)
  Label := fun residual =>
    registration.Label residual (registration.state residual)
  memberLowerMass := fun residual =>
    registration.memberLowerMass residual (registration.state residual)
  memberCapacity := fun residual =>
    registration.memberCapacity residual (registration.state residual)
  memberLabel := fun residual =>
    registration.memberLabel residual (registration.state residual)
  labelDecidableEq := fun residual =>
    registration.labelDecidableEq residual (registration.state residual)
  RealizedState := fun residual =>
    registration.RealizedState residual (registration.state residual)
  realizedStateFinite := fun residual =>
    registration.realizedStateFinite residual (registration.state residual)
  realizedStateNonempty := fun residual =>
    registration.realizedStateNonempty residual (registration.state residual)
  ambientOrder := fun residual =>
    registration.ambientOrder residual (registration.state residual)
  remainderCard := fun residual =>
    registration.remainderCard residual (registration.state residual)
  statePowerExponent := fun residual =>
    registration.statePowerExponent residual (registration.state residual)
  statePowerExponent_pos := fun residual =>
    registration.statePowerExponent_pos residual (registration.state residual)
  forcedBase := fun residual =>
    registration.forcedBase residual (registration.state residual)
  flatBase := fun residual =>
    registration.flatBase residual (registration.state residual)
  flatBase_pos := fun residual =>
    registration.flatBase_pos residual (registration.state residual)
  jointProfile := fun residual =>
    registration.jointProfile residual (registration.state residual)
  jointBaseCard := fun residual =>
    registration.jointBaseCard residual (registration.state residual)
  jointExponent := fun residual =>
    registration.jointExponent residual (registration.state residual)
  jointWeight := fun residual =>
    registration.jointWeight residual (registration.state residual)
  jointLocalLower := fun residual =>
    registration.jointLocalLower residual (registration.state residual)
  jointPaidExponent := fun residual =>
    registration.jointPaidExponent residual (registration.state residual)
  jointPaidExponent_exact := fun residual =>
    registration.jointPaidExponent_exact residual (registration.state residual)
  jointDesiredExponent := fun residual =>
    registration.jointDesiredExponent residual (registration.state residual)
  jointErrorExponent := fun residual =>
    registration.jointErrorExponent residual (registration.state residual)
  jointCapacity := fun residual =>
    registration.jointCapacity residual (registration.state residual)
  jointCapacity_pos := fun residual =>
    registration.jointCapacity_pos residual (registration.state residual)
  jointCodeCapacity := fun residual =>
    registration.jointCodeCapacity residual (registration.state residual)
  jointDesiredExponent_exact := fun residual =>
    registration.jointDesiredExponent_exact residual (registration.state residual)

end Registration

end Hypostructure.PDE.Strategy.FiniteStateCapacity
