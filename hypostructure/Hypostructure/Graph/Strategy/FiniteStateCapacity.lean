import Hypostructure.Core.Strategy.FiniteStateCapacitySemantics
import Hypostructure.Graph.Finite
import Hypostructure.Graph.PackedWindowRealization

/-!
# Graph finite-state capacity specialization

This module specializes the residual-indexed primitive observations consumed
by Core's sealed `FiniteStateCapacity` Strategy to an exact finite graph.
It owns no query, ledger, execution, branch, route, or computed outcome.
-/

namespace Hypostructure.Graph.Strategy.FiniteStateCapacity

open Hypostructure

universe uGraph uResidual uAmbient uData uState

/-- Finite-graph presentation of the primitive CT17 and CT14 observations.

Every field receives the exact graph selected by `object residual`.
`Registration.toCore` only substitutes that graph and forgets the Graph
terminology; Core still obtains rank, barrier, and supply from its accumulated
ledger and owns both CT executions and their dichotomy. -/
structure Registration (Residual : Type uResidual)
    (AmbientItem : Residual → Type uAmbient) where
  object : Residual → Graph.FiniteObject.{uGraph}
  Target : (residual : Residual) → Graph.FiniteObject.{uGraph} → Type uData
  Offset : (residual : Residual) → Graph.FiniteObject.{uGraph} → Type uData
  Position : (residual : Residual) →
    Graph.FiniteObject.{uGraph} → Nat → Type uData
  Value : (residual : Residual) → Graph.FiniteObject.{uGraph} → Type uData
  targets : (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
    Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
    Core.Strategy.LocalSupplyLowerBound.Summary →
      Core.Finite.Enumeration (Target residual object)
  offsets : (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
    Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
    Core.Strategy.LocalSupplyLowerBound.Summary →
      Core.Finite.Enumeration (Offset residual object)
  scales : (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
    Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
    Core.Strategy.LocalSupplyLowerBound.Summary →
      Core.Finite.Enumeration Nat
  selectedScale :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  selectedScale_mem : ∀ residual object rank barrier supply,
    selectedScale residual object rank barrier supply ∈
      (scales residual object rank barrier supply).values
  positions :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → (scale : Nat) →
        Core.Finite.Enumeration (Position residual object scale)
  finiteScaleLimit :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  targetValue :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary →
        Target residual object → Value residual object
  blockValue :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → (scale : Nat) →
        Position residual object scale → Offset residual object →
          Value residual object
  orbitValue :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Nat → Core.Strategy.FiniteBarrierEnumeration.Summary →
      Core.Strategy.LocalSupplyLowerBound.Summary → (scale : Nat) →
        Offset residual object → Value residual object
  Compatible :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      Target residual object → Offset residual object → Prop
  compatibleDecidable :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      (target : Target residual object) → (offset : Offset residual object) →
        Decidable (Compatible residual object target offset)
  valueDecidableEq :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      DecidableEq (Value residual object)
  Label : (residual : Residual) → Graph.FiniteObject.{uGraph} → Type uData
  memberLowerMass :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      (rank : Nat) → (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary) →
      (supply : Core.Strategy.LocalSupplyLowerBound.Summary) →
        Position residual object
          (selectedScale residual object rank barrier supply) → Nat
  memberCapacity :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      (rank : Nat) → (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary) →
      (supply : Core.Strategy.LocalSupplyLowerBound.Summary) →
        Position residual object
          (selectedScale residual object rank barrier supply) → Option Nat
  memberLabel :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      (rank : Nat) → (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary) →
      (supply : Core.Strategy.LocalSupplyLowerBound.Summary) →
        Position residual object
          (selectedScale residual object rank barrier supply) →
            Option (Label residual object)
  labelDecidableEq :
    (residual : Residual) → (object : Graph.FiniteObject.{uGraph}) →
      DecidableEq (Label residual object)
  RealizedState : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Type uData
  realizedStateFinite : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) →
    ∀ complement rank barrier supply,
      Finite (RealizedState residual object complement rank barrier supply)
  realizedStateNonempty : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) →
    ∀ complement rank barrier supply,
      Nonempty (RealizedState residual object complement rank barrier supply)
  ambientOrder : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  remainderCard : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  statePowerExponent : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  statePowerExponent_pos : ∀ residual object rank barrier supply,
    0 < statePowerExponent residual object rank barrier supply
  forcedBase : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  flatBase : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  flatBase_pos : ∀ residual object rank barrier supply,
    0 < flatBase residual object rank barrier supply
  jointProfile : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) →
    Core.Finite.Enumeration (AmbientItem residual) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary →
          Core.DependentOwnerGlueCapacity.BaseProfile.{
            uData, uData, uData, uData, uData}
  jointBaseCard : ∀ residual object complement rank barrier supply,
    Nat.card
        (jointProfile residual object complement rank barrier supply).Base =
      Nat.card
        (RealizedState residual object complement rank barrier supply)
  jointExponent : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointWeight : ∀ residual object complement rank barrier supply,
    (jointProfile residual object complement rank barrier supply).Owner → Nat
  jointLocalLower : ∀ residual object complement rank barrier supply owner,
    2 ^ jointWeight residual object complement rank barrier supply owner ≤
      Nat.card
          ((jointProfile residual object complement rank barrier
            supply).Local owner) ^
        jointExponent residual object rank barrier supply
  jointPaidExponent : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointPaidExponent_exact : ∀ residual object complement rank barrier supply,
    (jointProfile residual object complement rank barrier supply).weightSum
        (jointWeight residual object complement rank barrier supply) =
      jointPaidExponent residual object rank barrier supply
  jointDesiredExponent : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointErrorExponent : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointCapacity : (residual : Residual) →
    (object : Graph.FiniteObject.{uGraph}) → Nat →
      Core.Strategy.FiniteBarrierEnumeration.Summary →
        Core.Strategy.LocalSupplyLowerBound.Summary → Nat
  jointCapacity_pos : ∀ residual object rank barrier supply,
    0 < jointCapacity residual object rank barrier supply
  jointCodeCapacity : ∀ residual object complement rank barrier supply,
    Nat.card
        (jointProfile residual object complement rank barrier supply).Code ≤
      jointCapacity residual object rank barrier supply
  jointDesiredExponent_exact : ∀ residual object rank barrier supply,
    jointDesiredExponent residual object rank barrier supply =
      jointPaidExponent residual object rank barrier supply +
        jointErrorExponent residual object rank barrier supply
  /-- Graph-side carrier of Core's optional non-capacity closure.

  Every conjunct is the Core conjunct of
  `Core.Strategy.FiniteStateCapacity.Registration.nonCapacityImpossible` with
  the exact object of this presentation substituted, in the same way every
  other field above substitutes it.  `toCore` forwards the value verbatim, so
  no statement is restated and no obligation is added: a presentation that
  leaves this `none` keeps its non-capacity output live exactly as before.

  The finite-state presentation does not itself close the non-capacity arm.
  That arm is a live residual and must be routed by the surrounding strategy;
  in particular, singleton schedules do not establish the paper's entropy or
  net-charge conclusions. -/
  nonCapacityImpossible :
    Option (PLift
      ((∀ (residual : Residual) (target : Target residual (object residual))
            (offset : Offset residual (object residual)),
          Compatible residual (object residual) target offset) ∧
        (∀ residual rank barrier supply,
          selectedScale residual (object residual) rank barrier supply ≤
            finiteScaleLimit residual (object residual) rank barrier supply) ∧
        (∀ residual rank barrier supply,
          0 < (positions residual (object residual) rank barrier supply
            (selectedScale residual (object residual) rank barrier
              supply)).card) ∧
        (∀ residual rank barrier supply (scale : Nat)
            (position : Position residual (object residual) scale)
            (offset : Offset residual (object residual))
            (target : Target residual (object residual)),
          blockValue residual (object residual) rank barrier supply scale
              position offset ≠
            targetValue residual (object residual) rank barrier supply
              target) ∧
        (∀ residual rank barrier supply position,
          memberCapacity residual (object residual) rank barrier supply
            position ≠ none) ∧
        (∀ residual rank barrier supply position,
          memberLabel residual (object residual) rank barrier supply
            position ≠ none) ∧
        (∀ residual rank barrier supply position,
          memberLowerMass residual (object residual) rank barrier supply
              position ≤
            (memberCapacity residual (object residual) rank barrier supply
              position).getD 0))) :=
      none

namespace Registration

/-- Substitute the exact residual graph into Core's existing registration.
No finite scan, comparison, or branch is recomputed here. -/
def toCore
    (registration :
      Registration.{uGraph, uResidual, uAmbient, uData} Residual AmbientItem) :
    Core.Strategy.FiniteStateCapacity.Registration.{
      uResidual, uAmbient, uData}
      Residual AmbientItem where
  Target := fun residual =>
    registration.Target residual (registration.object residual)
  Offset := fun residual =>
    registration.Offset residual (registration.object residual)
  Position := fun residual =>
    registration.Position residual (registration.object residual)
  Value := fun residual =>
    registration.Value residual (registration.object residual)
  targets := fun residual =>
    registration.targets residual (registration.object residual)
  offsets := fun residual =>
    registration.offsets residual (registration.object residual)
  scales := fun residual =>
    registration.scales residual (registration.object residual)
  selectedScale := fun residual =>
    registration.selectedScale residual (registration.object residual)
  selectedScale_mem := fun residual =>
    registration.selectedScale_mem residual (registration.object residual)
  positions := fun residual =>
    registration.positions residual (registration.object residual)
  finiteScaleLimit := fun residual =>
    registration.finiteScaleLimit residual (registration.object residual)
  targetValue := fun residual =>
    registration.targetValue residual (registration.object residual)
  blockValue := fun residual =>
    registration.blockValue residual (registration.object residual)
  orbitValue := fun residual =>
    registration.orbitValue residual (registration.object residual)
  Compatible := fun residual =>
    registration.Compatible residual (registration.object residual)
  compatibleDecidable := fun residual =>
    registration.compatibleDecidable residual (registration.object residual)
  valueDecidableEq := fun residual =>
    registration.valueDecidableEq residual (registration.object residual)
  Label := fun residual =>
    registration.Label residual (registration.object residual)
  memberLowerMass := fun residual =>
    registration.memberLowerMass residual (registration.object residual)
  memberCapacity := fun residual =>
    registration.memberCapacity residual (registration.object residual)
  memberLabel := fun residual =>
    registration.memberLabel residual (registration.object residual)
  labelDecidableEq := fun residual =>
    registration.labelDecidableEq residual (registration.object residual)
  RealizedState := fun residual =>
    registration.RealizedState residual (registration.object residual)
  realizedStateFinite := fun residual =>
    registration.realizedStateFinite residual (registration.object residual)
  realizedStateNonempty := fun residual =>
    registration.realizedStateNonempty residual (registration.object residual)
  ambientOrder := fun residual =>
    registration.ambientOrder residual (registration.object residual)
  remainderCard := fun residual =>
    registration.remainderCard residual (registration.object residual)
  statePowerExponent := fun residual =>
    registration.statePowerExponent residual (registration.object residual)
  statePowerExponent_pos := fun residual =>
    registration.statePowerExponent_pos residual (registration.object residual)
  forcedBase := fun residual =>
    registration.forcedBase residual (registration.object residual)
  flatBase := fun residual =>
    registration.flatBase residual (registration.object residual)
  flatBase_pos := fun residual =>
    registration.flatBase_pos residual (registration.object residual)
  jointProfile := fun residual =>
    registration.jointProfile residual (registration.object residual)
  jointBaseCard := fun residual =>
    registration.jointBaseCard residual (registration.object residual)
  jointExponent := fun residual =>
    registration.jointExponent residual (registration.object residual)
  jointWeight := fun residual =>
    registration.jointWeight residual (registration.object residual)
  jointLocalLower := fun residual =>
    registration.jointLocalLower residual (registration.object residual)
  jointPaidExponent := fun residual =>
    registration.jointPaidExponent residual (registration.object residual)
  jointPaidExponent_exact := fun residual =>
    registration.jointPaidExponent_exact residual (registration.object residual)
  jointDesiredExponent := fun residual =>
    registration.jointDesiredExponent residual (registration.object residual)
  jointErrorExponent := fun residual =>
    registration.jointErrorExponent residual (registration.object residual)
  jointCapacity := fun residual =>
    registration.jointCapacity residual (registration.object residual)
  jointCapacity_pos := fun residual =>
    registration.jointCapacity_pos residual (registration.object residual)
  jointCodeCapacity := fun residual =>
    registration.jointCodeCapacity residual (registration.object residual)
  jointDesiredExponent_exact := fun residual =>
    registration.jointDesiredExponent_exact residual (registration.object residual)
  nonCapacityImpossible := registration.nonCapacityImpossible

end Registration

/-! ### The labelled-skeleton presentation

`def:remainder-entropy` reads the realized-state count `|𝒢(R)|` of a remainder
against the ambient order `n` and the remainder size `|R|`, and it is explicit
about where that class lives:

> Relative to that residual, let `𝒢(R)` be the set of labelled simple graphs
> on `V(R)` satisfying the remainder constraints already imposed on the
> branch.

`V(R)` is the inherited normalized-support complement, so the realized-state
carrier of this presentation is `Graph.LabelledOn complement.card` — the
labelled simple graphs on the remainder's own vertex set, read off the very
binder Core already hands the registration.  `lem:skeleton-dominates` is not
that carrier; it is the *ambient* class `𝒢_n` those states are paid out of,
and it appears below exactly there, as the joint code capacity.

With that carrier Core's CT17/CT14 composition has a single scheduled target,
offset, scale and position, and its whole content is the entropy comparison of
manuscript node [50].  The constructor below owns the entire presentation,
including its non-capacity closure; a registry supplies only its own object
query, its own entropy-threshold denominator, and the barrier schedule
position the flatness cost is read from.

The closure carries no entropy conjunct.  `prop:two-budget` routes rather than
closes — "in every case the surviving residual is subsequently passed to the
large-budget net-charge analysis" — and `rem:closure-robust` confirms "the
curvature-rank and forced-cost machinery is not required for the net-charge
closure outside the explicit residuals".  So this presentation owes only the
seven schedule facts, and all three of `prop:two-budget`'s branches leave the
Strategy on its capacity arm. -/

/-- `|R| ≤ n` for the inherited complement of this very object.

The complement Core hands the registration is the normalized-support
producer's own duplicate-free schedule of vertices of `object`, so its
cardinality never exceeds the object's vertex count.  This is the containment
`V(R) ⊆ [n]` that `def:remainder-entropy` inherits with the residual, read off
the schedule rather than assumed. -/
theorem complementCard_le_vertexCount
    (object : Graph.FiniteObject.{uGraph})
    (complement : Core.Finite.Enumeration (ULift.{uAmbient} object.Vertex)) :
    complement.card ≤ object.vertexCount := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have vertexCard : Fintype.card object.Vertex = object.vertexCount := by
    simp [Graph.FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard]
  have bound := Finset.card_le_univ complement.toFinset
  rw [Core.Finite.Enumeration.card_toFinset] at bound
  simpa [Fintype.card_ulift, vertexCard] using bound

/-- One scheduled member of the trivial data carrier. -/
private def singletonUnit :
    Core.Finite.Enumeration (ULift.{uState} Unit) :=
  Core.Finite.Enumeration.singleton (ULift.up ())

/-- One scheduled scale. -/
private def singletonScale : Core.Finite.Enumeration Nat :=
  Core.Finite.Enumeration.singleton 0

/-- The labelled simple graphs on a vertex set of a given size, lifted to the
registration's data universe.

At `order = complement.card` this is `def:remainder-entropy`'s own class
`𝒢(R)`: "the set of labelled simple graphs on `V(R)`", with `V(R)` the
inherited normalized-support complement.  At `order = object.vertexCount` it is
`lem:skeleton-dominates`'s ambient class `𝒢_n`.  `Graph.LabelledOn` is that
class as a genuine finite type, not a numerical surrogate. -/
abbrev LabelledSkeleton (order : Nat) : Type uData :=
  ULift.{uData} (Graph.LabelledOn order)

/-- Recoverable joint state/owner glue for the labelled-skeleton carrier.  The
owner and local families are the trivial ones, so the glue is the identity
pairing and Core's joint finite-capacity inequality is discharged from the
carrier alone. -/
noncomputable def labelledSkeletonJointProfile (order : Nat) :
    Core.DependentOwnerGlueCapacity.BaseProfile.{
      uData, uData, uData, uData, uData} where
  Base := LabelledSkeleton.{uData} order
  Owner := ULift.{uData} Unit
  Local := fun _ => ULift.{uData} Unit
  Global :=
    LabelledSkeleton.{uData} order ×
      (ULift.{uData} Unit → ULift.{uData} Unit)
  Code :=
    LabelledSkeleton.{uData} order ×
      (ULift.{uData} Unit → ULift.{uData} Unit)
  finiteBase := inferInstance
  finiteOwner := inferInstance
  finiteLocal := fun _ => inferInstance
  finiteCode := inferInstance
  glue := fun base choice => (base, choice)
  recoverBase := Prod.fst
  recoverLocal := Prod.snd
  recoverBase_glue := by simp
  recoverLocal_glue := by simp
  code := id
  codeInjectiveOnGlue := by
    intro _ _ _ _ equal
    exact equal

/-- The complete finite-state-capacity presentation on the endomorphism
carrier, closure included.

`object` is the registry's own object query; `entropyDenominator` is the
denominator `d` of its own remainder-entropy threshold
`η(R) ≥ (1/d)·log₂ n` (manuscript node [50]), which clearing denominators
turns into Core's `statePowerExponent`; `curvatureRow` is the barrier schedule
position whose safe and flat counts carry the flatness cost `c_Ω` of one
two-step curvature test (`lem:curv-enum`).

The ambient item carrier is the lifted vertex type, which is exactly the
carrier the normalized-support producer publishes and the local-supply ledger
inherits, so the complement Core hands to `RealizedState`, `ambientOrder` and
`remainderCard` is that producer's own schedule of this object's vertices.
That pinning is what puts `def:remainder-entropy`'s class on the right vertex
set: `RealizedState` is the labelled simple graphs on `V(R)`, whose size is
`complement.card`, and `remainderCard` is that same `|R|`, so the entropy
comparison Core computes is `|𝒢(R)| ^ d` against `n ^ |R|` rather than a
comparison between two unrelated readings.  The ambient class `𝒢_n` of
`lem:skeleton-dominates` enters once, as the joint code capacity the remainder
states are paid out of (`Graph.PackedWindowRealization.card_labelled_mono`). -/
noncomputable def labelledSkeletonRegistration
    {Residual : Type uResidual}
    (object : Residual → Graph.FiniteObject.{uGraph})
    (entropyDenominator : Residual → Nat)
    (entropyDenominator_two_le : ∀ residual, 2 ≤ entropyDenominator residual)
    (curvatureRow : Nat) :
    Registration.{uGraph, uResidual, max uGraph uAmbient, max uGraph uData}
        Residual
      (fun residual => ULift.{uAmbient} (object residual).Vertex) where
  object := object
  Target := fun _ _ => ULift.{max uGraph uData} Unit
  Offset := fun _ _ => ULift.{max uGraph uData} Unit
  Position := fun _ _ _ => ULift.{max uGraph uData} Unit
  Value := fun _ _ => ULift.{max uGraph uData} Nat
  targets := fun _ _ _ _ _ => singletonUnit
  offsets := fun _ _ _ _ _ => singletonUnit
  scales := fun _ _ _ _ _ => singletonScale
  selectedScale := fun _ _ _ _ _ => 0
  selectedScale_mem := by
    intro
    simp [singletonScale, Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]
  positions := fun _ _ _ _ _ _ => singletonUnit
  finiteScaleLimit := fun _ object rank barrier supply =>
    object.vertexCount + rank + barrier.rows.length + supply.observedSupply + 1
  targetValue := fun _ object rank barrier supply _ =>
    ULift.up (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply + 1)
  blockValue := fun _ object rank barrier supply _ _ _ =>
    ULift.up (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply)
  orbitValue := fun _ object rank barrier supply _ _ =>
    ULift.up (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply)
  Compatible := fun _ _ _ _ => True
  compatibleDecidable := fun _ _ _ _ => isTrue trivial
  valueDecidableEq := fun _ _ => inferInstance
  Label := fun _ _ => ULift.{max uGraph uData} Unit
  memberLowerMass := fun _ object rank barrier supply _ =>
    object.vertexCount + rank + barrier.rows.length + supply.observedSupply
  memberCapacity := fun _ object rank barrier supply _ =>
    some (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply)
  memberLabel := fun _ _ _ _ _ _ => some (ULift.up ())
  labelDecidableEq := fun _ _ => inferInstance
  RealizedState := fun _ _ complement _ _ _ =>
    LabelledSkeleton.{max uGraph uData} complement.card
  realizedStateFinite := by
    intro _ _ complement _ _ _
    infer_instance
  realizedStateNonempty := fun _ _ _ _ _ _ => ⟨ULift.up ⟨⊥⟩⟩
  ambientOrder := fun _ object _ _ _ _ => object.vertexCount
  remainderCard := fun _ _ complement _ _ _ => complement.card
  statePowerExponent := fun residual _ _ _ _ => entropyDenominator residual
  statePowerExponent_pos := fun residual _ _ _ _ =>
    lt_of_lt_of_le (by norm_num) (entropyDenominator_two_le residual)
  forcedBase := fun _ _ _ barrier _ => barrier.safeAt curvatureRow
  flatBase := fun _ _ _ barrier _ => max 1 (barrier.flatAt curvatureRow)
  flatBase_pos := by
    intro
    omega
  jointProfile := fun _ _ complement _ _ _ =>
    labelledSkeletonJointProfile.{max uGraph uData} complement.card
  jointBaseCard := by
    intro _ _ complement _ _ _
    simp [labelledSkeletonJointProfile]
  jointExponent := fun _ _ _ _ _ => 1
  jointWeight := fun _ _ _ _ _ _ _ => 0
  jointLocalLower := by
    intro _ _ _ _ _ _ owner
    simp [labelledSkeletonJointProfile]
  jointPaidExponent := fun _ _ _ _ _ => 0
  jointPaidExponent_exact := by
    intro
    simp [labelledSkeletonJointProfile,
      Core.DependentOwnerGlueCapacity.BaseProfile.weightSum]
  jointDesiredExponent := fun _ _ _ _ _ => 0
  jointErrorExponent := fun _ _ _ _ _ => 0
  -- `lem:skeleton-dominates`: the remainder's realized states are paid out of
  -- the ambient labelled-skeleton budget on `[n]`.
  -- The complement is a schedule of vertices of `object residual`, so the
  -- ambient budget is read at that same object; every other field receives it
  -- through the `object` binder `toCore` substitutes it into.
  jointCapacity := fun residual _ _ _ _ =>
    Nat.card (LabelledSkeleton.{max uGraph uData} (object residual).vertexCount)
  jointCapacity_pos := by
    intro residual _ _ _ _
    letI : Nonempty
        (LabelledSkeleton.{max uGraph uData} (object residual).vertexCount) :=
      ⟨ULift.up ⟨⊥⟩⟩
    exact Nat.card_pos
  jointCodeCapacity := by
    intro residual _ complement _ _ _
    have mono :=
      Graph.PackedWindowRealization.card_labelled_mono
        (complementCard_le_vertexCount.{uGraph, uAmbient} (object residual)
          complement)
    simpa [labelledSkeletonJointProfile, LabelledSkeleton, Nat.card_ulift]
      using mono
  jointDesiredExponent_exact := by intro; simp
  nonCapacityImpossible := none

/-- The former spelling of `labelledSkeletonRegistration`, retained verbatim
because the registered presentation that consumes it lives outside this
module.  It is the same registration: the realized-state carrier is
`def:remainder-entropy`'s class `𝒢(R)` of labelled simple graphs on the
inherited complement `V(R)`, never an endomorphism family. -/
noncomputable abbrev endomorphismRegistration
    {Residual : Type uResidual}
    (object : Residual → Graph.FiniteObject.{uGraph})
    (entropyDenominator : Residual → Nat)
    (entropyDenominator_two_le : ∀ residual, 2 ≤ entropyDenominator residual)
    (curvatureRow : Nat) :
    Registration.{uGraph, uResidual, max uGraph uAmbient, max uGraph uData}
        Residual
      (fun residual => ULift.{uAmbient} (object residual).Vertex) :=
  labelledSkeletonRegistration.{uGraph, uResidual, uAmbient, uData}
    object entropyDenominator entropyDenominator_two_le curvatureRow

end Hypostructure.Graph.Strategy.FiniteStateCapacity
