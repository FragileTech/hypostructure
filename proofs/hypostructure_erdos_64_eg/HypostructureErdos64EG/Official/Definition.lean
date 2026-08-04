import Hypostructure.Graph.Strategy.ScaleThresholdDichotomy
import Hypostructure.Graph.Strategy.FiniteDensityBudget
import Hypostructure.Graph.Strategy.SurplusAccounting
import Hypostructure.Graph.Strategy.NormalizationRank
import Hypostructure.Graph.Strategy.FiniteStateCapacity
import Hypostructure.Graph.Strategy.ColdBranchAggregation
import Hypostructure.Graph.Strategy.TypeBFanClosure
import Hypostructure.Graph.Strategy.TypeAReceiverExhaustion
import Hypostructure.Graph.Strategy.TypeARoute8Closure
import HypostructureErdos64EG.Presentation
import HypostructureErdos64EG.Official.Problem

/-!
# Official Erdős executable definition

This module assembles independently registered framework capabilities around
the mathematical problem.  It contains no DAG topology, node implementation,
branch selection, executor, or ledger operation.
-/

namespace HypostructureErdos64EG.Official

open Hypostructure

/-- The fixed surplus constant used at node `[19]`.  It is derived from the
same uniform homogeneous-token cap used by the non-near-cubic routing, rather
than from an unrelated finite table.  The successor absorbs the additive one
in the routed bound `1 + √(M₀ n)`. -/
def surplusScaleCoefficient : Nat :=
  Graph.Strategy.SurplusAccounting.homogeneousTokenCap
      erdosReceiverLoadProfile.baselineDegree + 1

/-- The exact node-`[19]` threshold table: `C_sp · ⌈√n⌉`. -/
def surplusScaleTable :
    Core.Strategy.Official.Features.ScaleDependentThreshold.Table where
  fixedRows := []
  scaleRows := [{
    basis := .squareRoot
    coefficient := {
      numerator := surplusScaleCoefficient
      denominator := 1
      denominator_pos := Nat.zero_lt_succ Nat.zero
    }
  }]

@[simp] theorem surplusScaleTable_threshold (size : Nat) :
    surplusScaleTable.threshold size =
      surplusScaleCoefficient *
        Core.Strategy.Official.Features.ScaleDependentThreshold.ScaleBasis.ceilSqrt
          size := by
  norm_num [surplusScaleTable, surplusScaleCoefficient,
    Core.Strategy.Official.Features.ScaleDependentThreshold.Table.threshold,
    Core.Strategy.Official.Features.ScaleDependentThreshold.Table.scaleContributions,
    Core.Strategy.Official.Features.ScaleDependentThreshold.ScaleRow.contribution,
    Core.Strategy.Official.Features.ScaleDependentThreshold.RationalCoefficient.contribution]
  exact Nat.mod_one _

/-- The node-`[19]` coefficient absorbs the additive constant in the
homogeneous-cap estimate used by the later non-near-cubic accounting. -/
theorem routedSurplusBound_le_scaleThreshold (size : Nat) (size_pos : 0 < size) :
    1 + Nat.sqrt
          (Graph.Strategy.SurplusAccounting.homogeneousTokenCap
              erdosReceiverLoadProfile.baselineDegree * size) ≤
      surplusScaleTable.threshold size := by
  let cap := Graph.Strategy.SurplusAccounting.homogeneousTokenCap
    erdosReceiverLoadProfile.baselineDegree
  let root :=
    Core.Strategy.Official.Features.ScaleDependentThreshold.ScaleBasis.ceilSqrt size
  have cap_pos : 0 < cap := by decide
  have size_le : size ≤ root ^ 2 :=
    Core.Strategy.Official.Features.ScaleDependentThreshold.ScaleBasis.le_ceilSqrt_sq
      size
  have cap_le_sq : cap ≤ cap ^ 2 := by nlinarith
  have radicand_le : cap * size ≤ (cap * root) ^ 2 := by nlinarith
  have sqrt_le := Nat.sqrt_le_sqrt radicand_le
  have root_pos : 0 < root := by nlinarith
  rw [surplusScaleTable_threshold]
  change 1 + Nat.sqrt (cap * size) ≤ (cap + 1) * root
  simp at sqrt_le
  nlinarith

noncomputable def degreeSurplusScaleThreshold :
    Core.Strategy.ScaleThresholdDichotomy.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.ScaleThresholdDichotomy.degreeSurplusRegistration
    Baseline BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    erdosReceiverLoadProfile.baselineDegree surplusScaleTable

noncomputable def typeBDegreeSplit : Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeBFanClosure.degreeSplitDichotomy problem target
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def typeBCertificateSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeBFanClosure.certificateLabellingSplit problem target
    fun input => input.object

noncomputable def typeBHeavyLocalResponse : Core.ResponseData.{1, 0, 0} problem :=
  Graph.Strategy.TypeBFanClosure.heavyCentreLocalResponse problem
    fun input => input.object

noncomputable def typeBFanSafeCapScan : Core.ScanData.{1, 0, 0} problem :=
  Graph.Strategy.TypeBFanClosure.fanSafeCapScan problem
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

/-- The three lengths the direct Type B cycle constructions produce are
accepted by the official dyadic target: `4 = 2 ^ 2`, `8 = 2 ^ 3`,
`16 = 2 ^ 4`.  A fact about the registered target predicate, not about the
graph. -/
theorem acceptedCycleLengths :
    Graph.TypeBClosure.AcceptedLengths PowerOfTwoLength where
  four := by decide
  eight := by decide
  sixteen := by decide

noncomputable def typeBDirectCycleSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeBFanClosure.directCycleRemovalSplit problem target
    (fun input => input.object) PowerOfTwoLength acceptedCycleLengths
    (fun _ cycle => cycle)

noncomputable def typeBB2LedgerSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeBFanClosure.b2LedgerSplit problem target
    fun input => input.object

noncomputable def typeBFanMassAccounting :
    Core.Strategy.BaselineDemandAccounting.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.TypeBFanClosure.fanMassAccounting
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def typeBDegreeFourProfileScan : Core.ScanData.{1, 0, 0} problem :=
  Graph.Strategy.TypeBFanClosure.degreeFourProfileScan problem
    fun input => input.object

noncomputable def typeBHybridEntryScan : Core.ScanData.{1, 0, 0} problem :=
  Graph.Strategy.TypeBFanClosure.hybridEntryScan problem
    fun input => input.object

noncomputable def typeBBridgeDeficitScan : Core.ScanData.{1, 0, 0} problem :=
  Graph.Strategy.TypeBFanClosure.bridgeDeficitScan problem
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def typeAReceiverLoadLedger :
    Core.Strategy.LocalSupplyLowerBound.Registration
      (Core.Strategy.ProblemInput problem)
      (fun input => ULift input.object.Vertex) :=
  Graph.Strategy.TypeAReceiverExhaustion.receiverLoadLedger
    (fun input : Core.Strategy.ProblemInput problem => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)


/-- The registered return algebra for the Type A return exits: the derived
shifted predicate of the official accepted cycle lengths. -/
noncomputable def typeARootedReturn :
    Graph.RootedReturnTargetAlgebra PowerOfTwoLength :=
  Graph.RootedReturnTargetAlgebra.shifted PowerOfTwoLength

noncomputable def typeASaturatedSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.saturatedReceiverSplit
    presentation (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile) (fun _ => rfl) (fun _ => rfl)

noncomputable def typeAVisibleReturnSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.visibleReturnSplit
    presentation (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile)
    (fun _ => erdosReceiverLoadProfile.loadMultiplier)

noncomputable def typeAExitOneSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitOneSplit
    (fun input => input.object) typeARootedReturn (fun _ cycle => cycle)

noncomputable def typeAExitTwoSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitTwoSplit
    (fun input => input.object) (fun _ cycle => cycle)

noncomputable def typeAExitThreeSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitThreeSplit
    (fun input => input.object)
    (fun input =>
      Graph.InducedPathMaximalPacking.maximalProfile input.object 13)
    acceptedCycleLengths (fun _ cycle => cycle)

noncomputable def typeAExitFourSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitFourSplit presentation
    (fun input => input.object) (fun _ => erdosReceiverLoadProfile)
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl) (fun _ cycle => cycle)

noncomputable def typeAExitFiveSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitFiveSplit presentation
    (fun input => input.object) (fun _ realized => realized)

noncomputable def typeAExitSixSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitSixSplit presentation
    (fun input => input.object) (fun _ => Iff.rfl) (fun _ cycle => cycle)

noncomputable def typeAExitSevenSplit :
    Core.DichotomyData.{1, 0, 0} problem target :=
  Graph.Strategy.TypeAReceiverExhaustion.exitSevenSplit presentation
    (fun input => input.object)

/-- The object the route-8 carrier closure reads: the residual's own, exactly as
every other Type A registration reads it. -/
noncomputable abbrev route8Object
    (input : Core.Strategy.ProblemInput problem) : Graph.FiniteObject.{0} :=
  input.object

noncomputable def typeARoute8Closure :
    Core.Strategy.Route8CarrierClosure.Registration
      (Core.Strategy.ProblemInput problem)
      (fun input => ULift input.object.Vertex) :=
  Graph.Strategy.TypeARoute8Closure.registration
    route8Object
    (fun _ => erdosReceiverLoadProfile.baselineDegree)
    (fun _ => requiredPrivateCount)
    (fun _ => dischargeScale)
    (fun _ => by decide)
    (fun _ => by decide)
    (fun input =>
      Graph.Strategy.TypeAReceiverExhaustion.TargetDefectiveQuotient
        presentation input.object erdosReceiverLoadProfile)
    (fun input =>
      Graph.Strategy.TypeAReceiverExhaustion.TargetCompleteCompression
        presentation input.object)
    (fun input =>
      Graph.Strategy.TypeAReceiverExhaustion.ResponseDelocalization
        presentation input.object)
    (fun input =>
      Graph.Strategy.TypeAReceiverExhaustion.DecoratedHandoffEnvelope
        presentation input.object)
    presentation.Target
    (Graph.Strategy.TypeARoute8Closure.carrierRestriction route8Object
      (fun _ => erdosReceiverLoadProfile.baselineDegree))
    none

noncomputable def labelledGraphDensityBudget :
    Core.Strategy.FiniteDensityBudget.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.FiniteDensityBudget.labelledSkeletonRegistration
    fun input => input.object

noncomputable def orderedSurplusActivation :
    Core.Strategy.OrderedSurplusActivation.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.SurplusAccounting.orderedSurplusActivation
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def baselineDemandAccounting :
    Core.Strategy.BaselineDemandAccounting.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.SurplusAccounting.baselineDemand
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def canonicalPairResponseAccounting :
    Core.Strategy.CanonicalPairResponseAccounting.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.SurplusAccounting.CanonicalAccounting.pairResponse
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def canonicalCapacityTokenAccounting :
    Core.Strategy.CanonicalCapacityTokenAccounting.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.SurplusAccounting.CanonicalAccounting.capacityToken
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def coupledHomogeneousFibrePressure :
    Core.Strategy.CoupledHomogeneousFibrePressure.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def finiteBottleneckClassification :
    Core.Strategy.FiniteBottleneckClassification.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.SurplusAccounting.CanonicalAccounting.bottleneck
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

private noncomputable def homogeneousBottleneck :
    Core.Strategy.HomogeneousBottleneck.Registration
      (Core.Strategy.ProblemInput problem)
      (fun input => target.Predicate input.object) :=
  Graph.Strategy.SurplusAccounting.homogeneousBottleneck
    PowerOfTwoLength (fun _ => inferInstance)

private def firstPackingIndex :
    Fin baseDefinition.data.obstructionPackingClosures.length :=
  ⟨0, Nat.pos_of_ne_zero
    (NeZero.ne baseDefinition.data.obstructionPackingClosures.length)⟩

private noncomputable def finiteBottleneckEntry :
    Core.FiniteBottleneckEntry problem
      [coupledHomogeneousFibrePressure] :=
  { fst := ⟨0, by simp⟩
    snd := finiteBottleneckClassification }

private noncomputable def homogeneousBottleneckEntry :
    Core.HomogeneousBottleneckEntry problem target
      [coupledHomogeneousFibrePressure] [finiteBottleneckEntry] :=
  { fst := ⟨0, by simp⟩
    snd := homogeneousBottleneck }

private noncomputable def coldBranchAggregation :
    Core.ColdBranchAggregationEntry problem target
      baseDefinition.data.counterexampleReductions
      baseDefinition.data.obstructionPackingClosures
      [coupledHomogeneousFibrePressure] [finiteBottleneckEntry]
      [homogeneousBottleneckEntry] :=
  { reductionIndex := ⟨0, by simp [baseDefinition,
      Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition,
      Graph.Strategy.Official.SealedDag.minimalCounterexampleDefinition]⟩
    fst := firstPackingIndex
    handoffIndex := ⟨0, by simp⟩
    handoffRequired := false
    snd :=
      Graph.Strategy.ColdBranchAggregation.inducedPathPressureLedgerRegistration
        inducedPathPresentation
        (fun _ => erdosReceiverLoadProfile.baselineDegree)
        PowerOfTwoLength (fun _ => inferInstance)
        -- The registered target *is* the dyadic cycle predicate at this
        -- problem's object: `target` is `Graph.minimumDegreeCycleTarget …
        -- PowerOfTwoLength` and `inducedPathPresentation.object` is
        -- `input.object`, which is why the same presentation is already built
        -- with `fun _object => Iff.rfl`.  This is that identity, not a proof.
        (fun _input cycle => cycle) }

private noncomputable def supportComplementNormalization :
    Core.SupportNormalizationEntry.{1, 0, 0}
      problem target baseDefinition.data.obstructionPackingClosures :=
  { fst := firstPackingIndex
    snd :=
      Graph.Strategy.NormalizationRank.inducedPathSupportComplementRegistration
        inducedPathPresentation }

noncomputable def boundaryDemandAccounting :
    Core.Strategy.BoundaryDemandAccounting.Registration
      (Core.Strategy.ProblemInput problem) :=
  Graph.Strategy.NormalizationRank.boundaryDemand
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def localSupplyLowerBound :
    Core.Strategy.LocalSupplyLowerBound.Registration
      (Core.Strategy.ProblemInput problem)
      (fun input => ULift input.object.Vertex) :=
  Graph.Strategy.NormalizationRank.localSupply
    (fun input : Core.Strategy.ProblemInput problem => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

/-- The standing minimum-degree hypothesis of the registered problem, read off
the residual it is carried on.  `ProblemInput.baseline` is `problem.Baseline`,
which is `Graph.MinimumDegreeAtLeast erdosReceiverLoadProfile.baselineDegree`,
so this is the residual's own field and not a further assumption. -/
private theorem baselineDegree_le_minDegree :
    ∀ input : Core.Strategy.ProblemInput problem,
      erdosReceiverLoadProfile.baselineDegree ≤ input.object.minDegree :=
  fun input => input.baseline

/-- The rank presentation is isomorphism invariant at the registered baseline,
and the registered target is invariant under the same semantic equivalence.
Both are the framework's own proofs, read at this problem's presentation; they
are `Prop`s, so they are the very values the registered reduction carries. -/
private theorem erdosBaselineInvariant :
    Graph.FiniteObject.IsomorphismInvariant Baseline where
  iff_of_iso := by
    intro left right equivalent
    show Graph.MinimumDegreeAtLeast _ left ↔ Graph.MinimumDegreeAtLeast _ right
    simp only [Graph.MinimumDegreeAtLeast,
      Graph.FiniteObject.minDegree_eq_of_isomorphic equivalent]

private theorem erdosTargetInvariant :
    Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation Baseline BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        erdosBaselineInvariant)
      target.Predicate where
  target_iff := by
    intro left right equivalent
    rcases equivalent with ⟨iso⟩
    exact Graph.hasCycleWithLength_iff_of_iso iso PowerOfTwoLength

private noncomputable def compressionLinkedTargetRelativeRankDichotomy :
    Core.CompressionLinkedTargetRankEntry problem target
      baseDefinition.data.obstructionPackingClosures
      [supportComplementNormalization]
      [(⟨0, boundaryDemandAccounting⟩ :
        Core.BoundaryAccountingEntry problem target
          baseDefinition.data.obstructionPackingClosures
          [supportComplementNormalization])]
      -- The exact `localSupplyLowerBounds` list of `definition` below.  This
      -- family is dependently indexed by it, so appending the Type A
      -- receiver-load ledger there means restating it here; leaving the
      -- one-element list would silently elaborate the whole definition to
      -- `sorry`.
      [(⟨0, localSupplyLowerBound⟩ :
        Core.LocalSupplyEntry problem target
          baseDefinition.data.obstructionPackingClosures
          [supportComplementNormalization]
          [(⟨0, boundaryDemandAccounting⟩ :
            Core.BoundaryAccountingEntry problem target
              baseDefinition.data.obstructionPackingClosures
              [supportComplementNormalization])]),
        (⟨0, typeAReceiverLoadLedger⟩ :
        Core.LocalSupplyEntry problem target
          baseDefinition.data.obstructionPackingClosures
          [supportComplementNormalization]
          [(⟨0, boundaryDemandAccounting⟩ :
            Core.BoundaryAccountingEntry problem target
              baseDefinition.data.obstructionPackingClosures
              [supportComplementNormalization])])]
      baseDefinition.data.counterexampleReductions :=
  { reductionIndex := ⟨0, by simp [baseDefinition,
      Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition,
      Graph.Strategy.Official.SealedDag.minimalCounterexampleDefinition]⟩
    fst := fun input =>
      Graph.Strategy.NormalizationRank.SupportedWedge input.object
    snd :=
      { fst := ⟨0, by simp⟩
        SiteRelation := fun input coordinate site =>
          Graph.Strategy.NormalizationRank.supportedWedgeSiteRelation
            input.object coordinate site
        base :=
          Graph.Strategy.NormalizationRank.targetRelativeRankBase
            (fun input : Core.Strategy.ProblemInput problem => input.object)
            (fun _ => erdosReceiverLoadProfile.baselineDegree)
            (fun _ => 0)
            (some ⟨baselineDegree_le_minDegree⟩)
        fixed :=
          Graph.Strategy.NormalizationRank.compressionLinkedTargetRelativeRankWithPresentation
            Baseline BranchState erdosBaselineInvariant
            Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
            target erdosTargetInvariant
            (fun input : Core.Strategy.ProblemInput problem => input.object)
            (fun _ => erdosReceiverLoadProfile.baselineDegree)
            (fun _ => 0)
            (some ⟨baselineDegree_le_minDegree⟩) } }

/-- Residual-owned finite-state presentation for the full-rank continuation.

The presentation itself, its realized-state carrier, its joint glue and its
non-capacity closure all belong to
`Graph.Strategy.FiniteStateCapacity.endomorphismRegistration`; this registry
supplies only its own object query, its own remainder-entropy threshold
denominator, and the barrier schedule position the flatness cost is read from.

The ambient item carrier is the one the local-supply predecessor's
normalized-support ledger already publishes -- `ULift input.object.Vertex`, the
vertex set `def:remainder-entropy`'s `𝒢(R)` is indexed by -- and
`Core.FiniteStateCapacityEntry` pins the registration to exactly that carrier.
Leaving it polymorphic threw the pinning away: the inherited complement then
had no relation to the object, and the realization conjunct of
`nonCapacityImpossible` could not be read at the values the ledger actually
delivers. -/
noncomputable def finiteStateCapacity :
    Core.Strategy.FiniteStateCapacity.Registration
      (Core.Strategy.ProblemInput problem)
      (fun input => ULift input.object.Vertex) :=
  (Graph.Strategy.FiniteStateCapacity.endomorphismRegistration
      (fun input : Core.Strategy.ProblemInput problem => input.object)
      (fun _ => erdosReceiverLoadProfile.remainderEntropyThresholdDenominator)
      (fun _ => by norm_num [erdosReceiverLoadProfile])
      0).toCore

/-- Canonical executable capability set for the official problem. -/

noncomputable def definition : Core.ProblemDefinition.{1, 0, 0} :=
  { baseDefinition with
    data := {
      baseDefinition.data with
      scaleThresholdDichotomies := [degreeSurplusScaleThreshold]
      finiteDensityBudgets := [labelledGraphDensityBudget]
      orderedSurplusActivations := [orderedSurplusActivation]
      baselineDemandAccountings := [baselineDemandAccounting, typeBFanMassAccounting]
      canonicalPairResponseAccountings :=
        [canonicalPairResponseAccounting]
      canonicalCapacityTokenAccountings :=
        [canonicalCapacityTokenAccounting]
      coupledHomogeneousFibrePressures :=
        [coupledHomogeneousFibrePressure]
      finiteBottleneckClassifications :=
        [finiteBottleneckEntry]
      homogeneousBottlenecks :=
        [homogeneousBottleneckEntry]
      coldBranchAggregations := [coldBranchAggregation]
      supportComplementNormalizations :=
        [supportComplementNormalization]
      boundaryDemandAccountings := [⟨0, boundaryDemandAccounting⟩]
      -- Position 0 is the spine's own local-supply entry; the Type A
      -- receiver-load ledger is appended so the finiteStateCapacities and
      -- targetRelativeRankDichotomies indices below keep pointing at 0.
      localSupplyLowerBounds :=
        [⟨0, localSupplyLowerBound⟩, ⟨0, typeAReceiverLoadLedger⟩]
      targetRelativeRankDichotomies := []
      compressionLinkedTargetRelativeRankDichotomies :=
        [compressionLinkedTargetRelativeRankDichotomy]
      scans := [typeBFanSafeCapScan, typeBDegreeFourProfileScan,
        typeBHybridEntryScan, typeBBridgeDeficitScan]
      responses := [typeBHeavyLocalResponse]
      dichotomies := [typeBDegreeSplit, typeBCertificateSplit, typeBB2LedgerSplit,
        typeBDirectCycleSplit,
        typeASaturatedSplit, typeAVisibleReturnSplit,
        typeAExitOneSplit, typeAExitTwoSplit, typeAExitThreeSplit,
        typeAExitFourSplit, typeAExitFiveSplit, typeAExitSixSplit,
        typeAExitSevenSplit]
      finiteStateCapacities := [⟨0, finiteStateCapacity⟩]
      route8CarrierClosures := [⟨1, typeARoute8Closure⟩]
    } }

instance definition_hasDichotomy :
    NeZero definition.data.dichotomies.length :=
  ⟨by simp [definition]⟩

instance definition_hasResponse :
    NeZero definition.data.responses.length :=
  ⟨by simp [definition]⟩

instance definition_hasScan :
    NeZero definition.data.scans.length :=
  ⟨by simp [definition]⟩

instance definition_hasCounterexampleReduction :
    NeZero definition.data.counterexampleReductions.length :=
  ⟨by simp [definition, baseDefinition,
    Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition,
    Graph.Strategy.Official.SealedDag.minimalCounterexampleDefinition]⟩

instance definition_hasObstructionPackingClosure :
    NeZero definition.data.obstructionPackingClosures.length :=
  ⟨by simp [definition, baseDefinition]⟩

instance definition_hasExactFiniteLocalAlgebra :
    NeZero definition.data.exactFiniteLocalAlgebras.length :=
  ⟨by simp [definition, baseDefinition]⟩

instance definition_hasFiniteBarrierEnumeration :
    NeZero definition.data.finiteBarrierEnumerations.length :=
  ⟨by simp [definition, baseDefinition]⟩

instance definition_hasScaleThresholdDichotomy :
    NeZero definition.data.scaleThresholdDichotomies.length :=
  ⟨by simp [definition]⟩

instance definition_hasFiniteDensityBudget :
    NeZero definition.data.finiteDensityBudgets.length :=
  ⟨by simp [definition]⟩

instance definition_hasOrderedSurplusActivation :
    NeZero definition.data.orderedSurplusActivations.length :=
  ⟨by simp [definition]⟩

instance definition_hasBaselineDemandAccounting :
    NeZero definition.data.baselineDemandAccountings.length :=
  ⟨by simp [definition]⟩

instance definition_hasCanonicalPairResponseAccounting :
    NeZero definition.data.canonicalPairResponseAccountings.length :=
  ⟨by simp [definition]⟩

instance definition_hasCanonicalCapacityTokenAccounting :
    NeZero definition.data.canonicalCapacityTokenAccountings.length :=
  ⟨by simp [definition]⟩

instance definition_hasCoupledHomogeneousFibrePressure :
    NeZero definition.data.coupledHomogeneousFibrePressures.length :=
  ⟨by simp [definition]⟩

instance definition_hasSupportComplementNormalization :
    NeZero definition.data.supportComplementNormalizations.length :=
  ⟨by simp [definition]⟩

instance definition_hasBoundaryDemandAccounting :
    NeZero definition.data.boundaryDemandAccountings.length :=
  ⟨by simp [definition]⟩

instance definition_hasLocalSupplyLowerBound :
    NeZero definition.data.localSupplyLowerBounds.length :=
  ⟨by simp [definition]⟩

instance definition_hasCompressionLinkedTargetRelativeRankDichotomy :
    NeZero
      definition.data.compressionLinkedTargetRelativeRankDichotomies.length :=
  ⟨by simp [definition]⟩

instance definition_hasFiniteStateCapacity :
    NeZero definition.data.finiteStateCapacities.length :=
  ⟨by simp [definition]⟩

instance definition_hasRoute8CarrierClosure :
    NeZero definition.data.route8CarrierClosures.length :=
  ⟨by simp [definition]⟩


instance definition_hasFiniteBottleneckClassification :
    NeZero definition.data.finiteBottleneckClassifications.length :=
  ⟨by simp [definition]⟩

instance definition_hasHomogeneousBottleneck :
    NeZero definition.data.homogeneousBottlenecks.length :=
  ⟨by simp [definition]⟩

instance definition_hasColdBranchAggregation :
    NeZero definition.data.coldBranchAggregations.length :=
  ⟨by simp [definition]⟩


end HypostructureErdos64EG.Official
