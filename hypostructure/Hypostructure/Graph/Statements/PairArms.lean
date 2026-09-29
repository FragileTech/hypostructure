import Hypostructure.Graph.Statements.HubLinks
import Hypostructure.Graph.PairArms.Pattern
import Hypostructure.Graph.PairArms.Generic4
import Hypostructure.Graph.Contracts.Spine.SparseExitReadings

/-!
# Statements: the two arms of G's pair-code configuration

Each statement is one of G's facts at its canonical objects, stated as an implication from the
arm (or outcome) of `PairCodeConfigurationStatement` it concerns (library:
`Graph/PairArms/*`):

* arm A (`[137]`→`[143]`): the exact kind structure of the canonical homogeneous pattern, and
  its role in a ten-letter alphabet;
* arm B (the first failure): its outcomes (B1), (B3) with their exact configurations,
  the demand ends and the connector routes ((B2), the target defect of the obstruction
  coordinates, is exit (b) stated about G, empty at G; its former pinned-witness fact is
  removed with the `[20a]` exit);
* every selected port endpoint has degree `δ`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.FiniteObject
open Hypostructure.Graph.CapacityFreeSide
open Hypostructure.Graph.PairArms
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- **Every selected port endpoint of G has degree `δ`.** -/
noncomputable def PortEndDegreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ d ∈ object.excessPorts data.threshold, object.degree d.2 = data.threshold

open Classical in
/-- **Arm A: the kind structure of the canonical homogeneous pattern.** -/
noncomputable def PairArmAPatternStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (DependentPairFamilyStatement data object ∧
      BlockedPairEntropySandwichStatement data object ∧
      HomogeneousBottleneckPatternSchema data object ∧
      SparsePressureOverloadSchema data object ∧
      ¬ HomogeneousCapsHoldStatement data object) →
    ∃ (active : Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
      (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) (conn : object.graph.Connected),
      canonicalCapacity data object = some (explicitCapacity active avoids conn) ∧
      ∃ (cert : SurplusCertified data object (explicitCapacity active avoids conn))
        (token : CapacityToken object) (role : SameTokenBlockerRoles.Role)
        (pattern : Finset (Finset (object.Vertex × object.Vertex))),
        canonicalCertifiedCapacityData data object = some ⟨_, cert⟩ ∧
        canonicalOverload data object = some ⟨⟨_, cert⟩, (token, role)⟩ ∧
        HomogeneousPatternSpec data object cert token role pattern ∧
        pattern.card + 1 ≤ (PatternFamily.support pattern).card ∧
        role.token = token.subtype ∧
        (∀ π ∈ pattern, π ∈ object.portPairSchedule data.threshold ∧
          capacityCharge (explicitCapacity active avoids conn).activation
            (explicitCapacity active avoids conn).carrier data.threshold
            (explicitCapacity active avoids conn).packing π = some token ∧
          ∃ b, canonicalBlocker (explicitCapacity active avoids conn).activation π = some b ∧
            b.kind = role.blocker) ∧
        ((role.blocker = .sharedDeclaredSupport ∧ ∃ w,
            (token = .primitive (.inl w) ∨ ∃ j, token = .remainder (w, j)) ∧
            ∀ π ∈ pattern, canonicalBlocker (explicitCapacity active avoids conn).activation π =
                some (.sharedDeclaredSupport (.vertex w)) ∧
              ∀ d ∈ π, w ∈ (explicitCapacity active avoids conn).activation.declaredSupport d) ∨
          (role.blocker = .sharedReturnSupport ∧ ∃ w,
            (token = .primitive (.inl w) ∨ ∃ j, token = .remainder (w, j)) ∧
            ∀ π ∈ pattern, canonicalBlocker (explicitCapacity active avoids conn).activation π =
                some (.sharedReturnSupport (.vertex w)) ∧
              ∀ d ∈ π, w ∈ (explicitCapacity active avoids conn).activation.returnSupport d) ∨
          (role.blocker = .targetResponse ∧
            ((∃ e, token = .boundaryWindow e) ∨ (∃ e, token = .crossWindow e) ∨
              (∃ v, token = .remainder v) ∨ (∃ v, token = .primitive (.inl v))) ∧
            ∀ π ∈ pattern, ∃ c, canonicalBlocker (explicitCapacity active avoids conn).activation π =
              some (.targetResponse c)) ∨
          (role.blocker = .arithmeticChordSet ∧
            (∀ π ∈ pattern, FKind active (explicitCapacity active avoids conn) π token) ∧
            ((∃ p₀, token = .primitive (.inr (.inr p₀)) ∧ PatternFamily.IsStar pattern p₀ ∧
                ∀ π ∈ pattern, canonicalBlocker (explicitCapacity active avoids conn).activation π =
                  some (.arithmeticChordSet {p₀})) ∨
              (∃ v k, token = .remainder (v, k) ∧ ∀ π ∈ pattern, ∃ p ∈ π,
                canonicalBlocker (explicitCapacity active avoids conn).activation π =
                  some (.arithmeticChordSet {p}) ∧
                (v = (pairResponseChordEnds active p).1 ∨
                  v = (pairResponseChordEnds active p).2)))))

/-- **Arm A: the canonical overload role is one of ten** (`liveRoles`). -/
noncomputable def PairArmARoleAlphabetStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (DependentPairFamilyStatement data object ∧
      BlockedPairEntropySandwichStatement data object ∧
      HomogeneousBottleneckPatternSchema data object ∧
      SparsePressureOverloadSchema data object ∧
      ¬ HomogeneousCapsHoldStatement data object) →
    ∃ (c : SurplusCapacity data object) (cert : SurplusCertified data object c)
      (token : CapacityToken object) (role : Role),
      canonicalOverload data object = some ⟨⟨c, cert⟩, (token, role)⟩ ∧
      role.token = CapacityToken.subtype token ∧
      (role.blocker, role.token) ∈ liveRoles

/-- **Arm B: its outcomes, exactly** — on arm B of the pair-code configuration, G's
canonical overlap system exists and G is in (B1) or (B3) ((B2), the target defect of the
obstruction coordinates, is exit (b) stated about G and is empty at G); the `[182]` residual (B1)
is one of three exact configurations; the obstruction handoff (B3) has its canonical
separator, envelope and escape; on the realizability failure every forward connector route in
`U` meets every backward one and the demand ends split; at the canonical serial system the
ends lie in `U` with the switch at the left port. -/
noncomputable def PairArmBStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (PairOverlapFirstFailureStatement data object ∧
      (PairConditionalFactorizationResidualStatement data
          object ∨
        ((∃ returns, canonicalPairDemandReturns data
            object = some returns ∧
            PairObstructionHandoff data object returns) ∧
          TypeBFanEntryStatement data object)) →
    PairOverlapSystemStatement data object ∧
    ((∃ system, canonicalPairOverlapSystem data object =
        some system ∧ ¬ system.ConditionalFactorization) ∨
      (∃ returns, canonicalPairDemandReturns data object =
          some returns ∧
        (¬ Graph.ResidualTargetDefect
            (Graph.HasCycleWithLength data.LengthOK)
            object returns.obstructionCoordinates pairCoordinateSupport ∨
        (PairObstructionHandoff data object returns ∧
          TypeBFanEntryStatement data object))))) ∧
  (PairConditionalFactorizationResidualStatement data object →
    (∃ system, canonicalPairOverlapSystem data object = some system ∧
      ¬ system.ConditionalFactorization) ∨
    (∃ returns, canonicalPairDemandReturns data object = some returns ∧
      ¬ Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
        returns.obstructionCoordinates pairCoordinateSupport ∧
      ¬ PairObstructionHandoff data object returns ∧
      (∀ serial : PairSerialDemandSystem data object, serial.returns ≠ returns) ∧
      (∀ routes : PairDemandReturns.ConnectorRoutes returns,
        (∀ v ∈ routes.forward.support,
          v ∈ returns.overlap.system.overlapSupport returns.overlap.family) →
        (∀ v ∈ routes.forward.support, v ∉ routes.backward.support) →
        routes.forward.length = 0 ∧ routes.backward.length = 0)) ∨
    (∃ serial, canonicalPairSerialSystem data object = some serial ∧
      canonicalPairDemandReturns data object = some serial.returns ∧
      ¬ Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
        serial.returns.obstructionCoordinates pairCoordinateSupport ∧
      ¬ PairObstructionHandoff data object serial.returns ∧
      (∀ choice : Fin serial.cells → Nat, (∀ i, choice i ∈ serial.lengths i) →
        ∀ offset ∈ serial.offsets,
          ¬ data.LengthOK (serial.closing + (∑ i, choice i) + offset)))) ∧
  (∀ {returns : PairDemandReturns data object},
    canonicalPairDemandReturns data object = some returns →
    PairObstructionHandoff data object returns →
    TypeBFanEntryStatement data object ∧ SurplusAboveStatement data object ∧
    ∃ routes split envelope,
      canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
      canonicalPairObstructionEnvelope data object returns = some envelope ∧
      3 < object.degree split.separator ∧
      ¬ Graph.WindowLabelCollision.LabelCollision object data.windowOrder
          data.LengthOK (canonicalWindowPacking data object) ∧
      split.nextFirst ≠ split.nextSecond ∧
      object.graph.Adj split.separator split.nextFirst ∧
      object.graph.Adj split.separator split.nextSecond ∧
      split.separator ∈ returns.overlap.system.overlapSupport returns.overlap.family ∧
      split.nextFirst ∈ returns.overlap.system.overlapSupport returns.overlap.family ∧
      split.nextSecond ∈ returns.overlap.system.overlapSupport returns.overlap.family ∧
      SameTokenEscape data object split envelope) ∧
  (∀ {returns : PairDemandReturns data object},
    ¬ Nonempty (PairSystemRealizabilityOutcome returns) →
    ∀ routes : PairDemandReturns.ConnectorRoutes returns,
    (∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family) →
    ∃ v ∈ routes.forward.support, v ∈ routes.backward.support) ∧
  (∀ {returns : PairDemandReturns data object},
    ¬ Nonempty (PairSystemRealizabilityOutcome returns) →
    let U := returns.overlap.system.overlapSupport returns.overlap.family
    ((returns.leftDemand.2 ∉ U ∨ returns.rightDemand.1 ∉ U) ∧
      ∀ serial : PairSerialDemandSystem data object,
        serial.returns ≠ returns) ∨
    (returns.leftDemand.2 ∈ U ∧ returns.rightDemand.1 ∈ U ∧
      (∃ P : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1,
        P.IsPath ∧ ∀ v ∈ P.support, v ∈ U) ∧
      ∀ routes : PairDemandReturns.ConnectorRoutes returns,
        ∀ P : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1,
          P.IsPath → (∀ v ∈ P.support, v ∈ U) →
          ∃ v ∈ P.support, v ∈ routes.backward.support)) ∧
  (∀ {serial : PairSerialDemandSystem data object},
    canonicalPairSerialSystem data object = some serial →
    let R := serial.returns
    let U := R.overlap.system.overlapSupport R.overlap.family
    R.leftDemand.2 ∈ U ∧ R.rightDemand.1 ∈ U ∧
    3 < object.degree R.leftDemand.1 ∧ 3 < object.degree R.rightDemand.1 ∧
    object.degree R.leftDemand.2 = 3 ∧ object.degree R.rightDemand.2 = 3 ∧
    (∀ choice : Fin serial.cells → Nat, (∀ i, choice i ∈ serial.lengths i) →
      ∀ offset ∈ serial.offsets,
        ¬ data.LengthOK (serial.closing + (∑ i, choice i) + offset)) ∧
    ((data.threshold + 2 ≤ object.degree R.leftDemand.1 ∧ ∃ u, object.graph.Adj R.leftDemand.1 u ∧
        u ≠ R.leftDemand.2 ∧ ¬ object.graph.Adj R.leftDemand.2 u ∧
        ∃ p : (object.graph.deleteEdges {s(R.leftDemand.1, R.leftDemand.2),
            s(R.leftDemand.1, u)}).Walk R.leftDemand.2 u,
          p.IsPath ∧ data.LengthOK (p.length + 1)) ∨
      ∃ h₂ u₂, h₂ ≠ R.leftDemand.1 ∧ data.threshold + 1 ≤ object.degree h₂ ∧
        object.graph.Adj u₂ h₂ ∧ u₂ ≠ R.leftDemand.2 ∧ ¬ object.graph.Adj R.leftDemand.2 u₂ ∧
        ∃ p : (object.graph.deleteEdges {s(R.leftDemand.2, R.leftDemand.1),
            s(u₂, h₂)}).Walk R.leftDemand.2 u₂,
          p.IsPath ∧ data.LengthOK (p.length + 1)))

end Hypostructure.Graph.Strategy.Spine
