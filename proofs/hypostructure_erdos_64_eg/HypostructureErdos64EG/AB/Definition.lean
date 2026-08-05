import HypostructureErdos64EG.AB.Problem
import HypostructureErdos64EG.Official.Definition
import Hypostructure.Graph.Strategy.CounterexampleReduction
import Hypostructure.Graph.Strategy.ColdBranchAggregation

/-!
# Single-target EG Type-A / Type-B definition

This declaration uses the unchanged official EG problem and registers every
strategy against the one target

`OfficialTarget object ∨ GlobalTypeA object ∨ GlobalTypeB object`.

The minimal-counterexample semantics below are the application specialization
of the existing Graph API.  Official cycles enter the target through
`Or.inl`; Type-A/B certificates are transported only by their literal
subgraph embeddings.
-/

namespace HypostructureErdos64EG.AB

open Hypostructure

private abbrev ShiftedTarget :=
  Graph.ShiftedCycleLength PowerOfTwoLength

private abbrev TargetCode (object : Graph.FiniteObject.{0}) :=
  ULift.{1} (Graph.EdgeRootedReturn object ShiftedTarget) ⊕
    (PLift (GlobalTypeA object) ⊕ PLift (GlobalTypeB object))

theorem abPredicate_mono
    {source : Graph.FiniteObject.{0}}
    (subgraph : Graph.ProperSubgraph source) :
    abPredicate subgraph.value → abPredicate source := by
  rintro (cycle | typeA | typeB)
  · exact Or.inl
      ((Graph.cycleProperSubgraphTargetMonotone PowerOfTwoLength).map
        subgraph cycle)
  · exact Or.inr (Or.inl (GlobalTypeA.mapProper subgraph typeA))
  · exact Or.inr (Or.inr (GlobalTypeB.mapProper subgraph typeB))

theorem abPredicate_iff_of_iso
    {left right : Graph.FiniteObject.{u}} (iso : left.Iso right) :
    abPredicate left ↔ abPredicate right := by
  constructor
  · rintro (cycle | typeA | typeB)
    · exact Or.inl
        ((Graph.hasCycleWithLength_iff_of_iso iso PowerOfTwoLength).mp cycle)
    · exact Or.inr (Or.inl ((GlobalTypeA.iff_of_iso iso).mp typeA))
    · exact Or.inr (Or.inr ((GlobalTypeB.iff_of_iso iso).mp typeB))
  · rintro (cycle | typeA | typeB)
    · exact Or.inl
        ((Graph.hasCycleWithLength_iff_of_iso iso PowerOfTwoLength).mpr cycle)
    · exact Or.inr (Or.inl ((GlobalTypeA.iff_of_iso iso).mpr typeA))
    · exact Or.inr (Or.inr ((GlobalTypeB.iff_of_iso iso).mpr typeB))

/-- The official minimal-counterexample registration specialized to the
single disjunctive target.  Its code contains exactly the three target
certificate families and no decision result. -/
noncomputable def counterexampleReduction :
    Core.CounterexampleReductionData.{1, 0, 0} problem abTarget where
  selection :=
    Core.MinimalCounterexampleSelectionData.ofProgress
      (Graph.CanonicalProgress.progress (P := problem))
  Code := TargetCode
  Accepts := fun _ _ => True
  target_iff_code := by
    intro object
    change Graph.FiniteObject at object
    change abPredicate object ↔ ∃ _code : TargetCode object, True
    constructor
    · rintro (cycle | typeA | typeB)
      · change Graph.HasCycleWithLength PowerOfTwoLength object at cycle
        rcases (Graph.hasCycleWithLength_iff_hasEdgeRootedReturn
          PowerOfTwoLength object).mp cycle with ⟨certificate⟩
        exact ⟨Sum.inl (ULift.up certificate), trivial⟩
      · exact ⟨Sum.inr (Sum.inl ⟨typeA⟩), trivial⟩
      · exact ⟨Sum.inr (Sum.inr ⟨typeB⟩), trivial⟩
    · rintro ⟨code, _⟩
      rcases code with cycle | typeAOrB
      · exact Or.inl
          ((Graph.hasCycleWithLength_iff_hasEdgeRootedReturn
            PowerOfTwoLength object).mpr
            ⟨cycle.down⟩)
      · rcases typeAOrB with typeA | typeB
        · exact Or.inr (Or.inl typeA.down)
        · exact Or.inr (Or.inr typeB.down)
  acceptsDecidable := fun _ _ => .isTrue trivial
  Subobject := Graph.ProperSubgraph
  subobjectProfile := {
    toAmbient := fun subgraph => subgraph.value
    smaller := fun subgraph => subgraph.decreases
    targetMonotone := fun subgraph target =>
      abPredicate_mono subgraph target
    stateOf := fun _ => ()
  }
  Atomic := fun object => ULift.{1} object.graph.Dart
  Carrier := fun object =>
    ULift.{1} { vertex : object.Vertex //
      erdosReceiverLoadProfile.baselineDegree + 1 ≤ object.degree vertex }
  Related := fun object left right =>
    object.graph.Adj left.down.1 right.down.1
  Critical := fun object dart =>
    let dart := dart.down
    object.degree dart.fst = erdosReceiverLoadProfile.baselineDegree ∨
      object.degree dart.snd = erdosReceiverLoadProfile.baselineDegree
  atomicSubobject := fun {object} dart =>
    Graph.ProperSubgraph.deleteEdge object (object.edgeOfDart dart.down)
  baseline_of_not_critical := by
    intro object baseline liftedDart notCritical
    let dart := liftedDart.down
    change ¬ (object.degree dart.fst =
        erdosReceiverLoadProfile.baselineDegree ∨
      object.degree dart.snd =
        erdosReceiverLoadProfile.baselineDegree) at notCritical
    have firstLower :=
      baseline.trans (object.minDegree_le_degree dart.fst)
    have secondLower :=
      baseline.trans (object.minDegree_le_degree dart.snd)
    have firstSlack :
        erdosReceiverLoadProfile.baselineDegree + 1 ≤
          object.degree dart.fst := by
      omega
    have secondSlack :
        erdosReceiverLoadProfile.baselineDegree + 1 ≤
          object.degree dart.snd := by
      omega
    exact object.deleteEdge_preserves_minDegree dart
      erdosReceiverLoadProfile.baselineDegree baseline firstSlack secondSlack
  atomic_of_related := fun left right adjacent =>
    ULift.up ⟨(left.down.1, right.down.1), adjacent⟩
  noncritical_of_related := by
    intro object left right adjacent
    simp only
    intro critical
    rcases critical with leftTight | rightTight
    · exact (Nat.not_succ_le_self erdosReceiverLoadProfile.baselineDegree)
        (left.down.2.trans_eq leftTight)
    · exact (Nat.not_succ_le_self erdosReceiverLoadProfile.baselineDegree)
        (right.down.2.trans_eq rightTight)
  interfaceReplacement := by
    let baselineInvariant :
        Graph.FiniteObject.IsomorphismInvariant Baseline := {
      iff_of_iso := by
        intro left right equivalent
        change erdosReceiverLoadProfile.baselineDegree ≤ left.minDegree ↔
          erdosReceiverLoadProfile.baselineDegree ≤ right.minDegree
        rw [Graph.FiniteObject.minDegree_eq_of_isomorphic equivalent]
    }
    let semantics :=
      Graph.isomorphismEquivalenceWithPresentation
        Baseline BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        baselineInvariant
    let targetInvariant : Core.TargetInvariant semantics abPredicate := {
      target_iff := by
        intro left right equivalent
        rcases equivalent with ⟨iso⟩
        exact abPredicate_iff_of_iso iso
    }
    exact Graph.Strategy.InterfaceReplacement.profileWithPresentation
      Baseline BranchState baselineInvariant
      Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
      targetInvariant

noncomputable def inducedPathPresentation :
    Graph.Strategy.InducedPathPresentation.{1, 0}
      (Core.Strategy.ProblemInput problem)
      (fun input => abPredicate input.object) where
  object := fun input => input.object
  order := fun _ =>
    Graph.External.HegdeSandeepShashank.inducedPathOrder
  order_pos := by
    intro _
    norm_num [Graph.External.HegdeSandeepShashank.inducedPathOrder]
  baselineDegree := Official.baselineDegreeQuery
  freeForcesTarget := by
    intro input free
    exact Or.inl (Official.hssHasPowerOfTwoCycle input input.object
      (Graph.Strategy.minimumDegreeAtLeast_of_problemInput input) free)
  componentFreeForcesTarget := by
    intro input support minimumDegree free
    let induced := input.object.induce support
    have componentCycle :=
      Official.hssHasPowerOfTwoCycle input induced minimumDegree free
    rcases componentCycle with ⟨certificate⟩
    exact Or.inl ⟨certificate.mapHom
      (input.object.induceEmbedding support).toHom
      (input.object.induceEmbedding support).injective⟩

noncomputable def obstructionPacking :
    Core.Strategy.ObstructionPackingClosure.Semantics.{1, 1}
      (Core.Strategy.ProblemInput problem)
      (fun input => abPredicate input.object) :=
  Graph.Strategy.NormalizationRank.inducedPathPackingSemantics
    inducedPathPresentation

noncomputable def baseDefinition : Core.ProblemDefinition.{1, 0, 0} :=
  let base :=
    Graph.Strategy.Official.SealedDag.minimalCounterexampleDefinition
      problem abTarget (fun _ => ()) counterexampleReduction
  { base with
    data := {
      base.data with
      coldBranchAggregations := []
      obstructionPackingClosures := [obstructionPacking]
      supportComplementNormalizations := []
      boundaryDemandAccountings := []
      localSupplyLowerBounds := []
      -- Indexed by the four families above: a `with`-update reassigning any of
      -- them must reassign this too, or the inherited value keeps the stale
      -- index and the whole definition elaborates to `sorry`.
      finiteStateCapacities := []
      route8CarrierClosures := []
      targetRelativeRankDichotomies := []
      compressionLinkedTargetRelativeRankDichotomies := []
      exactFiniteLocalAlgebras := [Official.finiteLocalAlgebra]
      finiteBarrierEnumerations :=
        [Graph.Strategy.FiniteDensityBudget.multiScaleWindowPackage
          (fun input => input.object)
          (FiniteChecks.P13Barrier.enumerationRegistration
            (Core.Strategy.ProblemInput problem))]
    } }

private noncomputable def homogeneousBottleneck :
    Core.Strategy.HomogeneousBottleneck.Registration
      (Core.Strategy.ProblemInput problem)
      (fun input => abPredicate input.object) :=
  Graph.Strategy.SurplusAccounting.homogeneousBottleneckOr
    PowerOfTwoLength (fun _ => inferInstance)
    (fun input => GlobalTypeA input.object ∨ GlobalTypeB input.object)

private def firstPackingIndex :
    Fin baseDefinition.data.obstructionPackingClosures.length :=
  ⟨0, by simp [baseDefinition]⟩

private noncomputable def finiteBottleneckEntry :
    Core.FiniteBottleneckEntry problem
      [Official.coupledHomogeneousFibrePressure] :=
  { fst := ⟨0, by simp⟩
    snd := Official.finiteBottleneckClassification }

private noncomputable def homogeneousBottleneckEntry :
    Core.HomogeneousBottleneckEntry problem abTarget
      [Official.coupledHomogeneousFibrePressure] [finiteBottleneckEntry] :=
  { fst := ⟨0, by simp⟩
    snd := homogeneousBottleneck }

private noncomputable def coldBranchAggregation :
    Core.ColdBranchAggregationEntry problem abTarget
      baseDefinition.data.counterexampleReductions
      baseDefinition.data.obstructionPackingClosures
      [Official.coupledHomogeneousFibrePressure] [finiteBottleneckEntry]
      [homogeneousBottleneckEntry] :=
  { reductionIndex := ⟨0, by simp [baseDefinition,
      Graph.Strategy.Official.SealedDag.minimalCounterexampleDefinition]⟩
    fst := firstPackingIndex
    handoffIndex := ⟨0, by simp⟩
    handoffRequired := false
    snd :=
      Graph.Strategy.ColdBranchAggregation.inducedPathDisjunctiveMinimalPressureLedgerRegistration
        (T := abTarget)
        -- The subobject family this registry's own counterexample reduction
        -- registered, read back rather than rebuilt: its `toAmbient` is the
        -- proper subgraph's own `value`, which is what `fun _ => rfl` says.
        counterexampleReduction.subobjectProfile
        (fun _ => rfl)
        -- The registered baseline is `MinimumDegreeAtLeast`, so a graph whose
        -- minimum degree is at least the source's inherits it.  This is that
        -- identity, not a proof.
        (fun baseline degreeBound => Nat.le_trans baseline degreeBound)
        inducedPathPresentation
        -- `inducedPathPresentation.object` is `fun input => input.object`.
        (fun _ => rfl)
        (fun _ => erdosReceiverLoadProfile.baselineDegree)
        PowerOfTwoLength (fun _ => inferInstance)
        (fun object => GlobalTypeA object ∨ GlobalTypeB object)
        -- `abPredicate` *is* `HypostructureErdos64EG.Target ∨ GlobalTypeA ∨
        -- GlobalTypeB` and `inducedPathPresentation.object` is `input.object`,
        -- so the registered A/B target and the disjunctive graph target are the
        -- same proposition.  This is that identity, not a proof.
        (fun _input evidence => evidence) }

private noncomputable def supportComplementNormalization :
    Core.SupportNormalizationEntry.{1, 0, 0}
      problem abTarget baseDefinition.data.obstructionPackingClosures :=
  { fst := firstPackingIndex
    snd :=
      Graph.Strategy.NormalizationRank.inducedPathSupportComplementRegistration
        inducedPathPresentation }

/-- The two invariants of this registry's own reduction, named so the linked
rank entry below can be typed against the very profile that reduction
publishes.  Both are `Prop`s, so they are that reduction's values. -/
private theorem abBaselineInvariant :
    Graph.FiniteObject.IsomorphismInvariant Baseline where
  iff_of_iso := by
    intro left right equivalent
    change erdosReceiverLoadProfile.baselineDegree ≤ left.minDegree ↔
      erdosReceiverLoadProfile.baselineDegree ≤ right.minDegree
    rw [Graph.FiniteObject.minDegree_eq_of_isomorphic equivalent]

private theorem abTargetInvariant :
    Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation Baseline BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        abBaselineInvariant)
      abTarget.Predicate where
  target_iff := by
    intro left right equivalent
    rcases equivalent with ⟨iso⟩
    exact abPredicate_iff_of_iso iso

private noncomputable def compressionLinkedTargetRelativeRankDichotomy :
    Core.CompressionLinkedTargetRankEntry problem abTarget
      baseDefinition.data.obstructionPackingClosures
      [supportComplementNormalization]
      [(⟨0, Official.boundaryDemandAccounting⟩ :
        Core.BoundaryAccountingEntry problem abTarget
          baseDefinition.data.obstructionPackingClosures
          [supportComplementNormalization])]
      -- The exact `localSupplyLowerBounds` list of `definition` below, which
      -- this family is dependently indexed by.  The Type A receiver-load
      -- ledger is appended there for the route-8 closure of nodes
      -- [111]--[124], so leaving the one-element list here would silently
      -- elaborate the whole definition to `sorry`.
      [(⟨0, Official.localSupplyLowerBound⟩ :
        Core.LocalSupplyEntry problem abTarget
          baseDefinition.data.obstructionPackingClosures
          [supportComplementNormalization]
          [(⟨0, Official.boundaryDemandAccounting⟩ :
            Core.BoundaryAccountingEntry problem abTarget
              baseDefinition.data.obstructionPackingClosures
              [supportComplementNormalization])]),
        (⟨0, Official.typeAReceiverLoadLedger⟩ :
        Core.LocalSupplyEntry problem abTarget
          baseDefinition.data.obstructionPackingClosures
          [supportComplementNormalization]
          [(⟨0, Official.boundaryDemandAccounting⟩ :
            Core.BoundaryAccountingEntry problem abTarget
              baseDefinition.data.obstructionPackingClosures
              [supportComplementNormalization])])]
      baseDefinition.data.counterexampleReductions :=
  { reductionIndex := ⟨0, by simp [baseDefinition,
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
            (some ⟨fun input => input.baseline⟩)
        fixed :=
          Graph.Strategy.NormalizationRank.compressionLinkedTargetRelativeRankWithPresentation
            Baseline BranchState abBaselineInvariant
            Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
            abTarget abTargetInvariant
            (fun input : Core.Strategy.ProblemInput problem => input.object)
            (fun _ => erdosReceiverLoadProfile.baselineDegree)
            (fun _ => 0)
            (some ⟨fun input => input.baseline⟩) } }

/-- The complete capability registry for the one-target A/B problem.  Every
target-independent registration is the literal official registration; the
three target-dependent registrations above differ only by replacing a cycle
conclusion with its left injection into `abPredicate`. -/
noncomputable def typeBDegreeSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeBFanClosure.degreeSplitDichotomy problem abTarget
    (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile.baselineDegree)

noncomputable def typeBCertificateSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeBFanClosure.certificateLabellingSplit problem abTarget
    fun input => input.object

noncomputable def typeBB2LedgerSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeBFanClosure.b2LedgerSplit problem abTarget
    fun input => input.object

noncomputable def typeBDirectCycleSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeBFanClosure.directCycleRemovalSplit problem abTarget
    (fun input => input.object) PowerOfTwoLength Official.acceptedCycleLengths
    (fun _ cycle => Or.inl cycle)


noncomputable def typeASaturatedSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.saturatedReceiverSplit
    presentation (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile) (fun _ => rfl) (fun _ => rfl)

noncomputable def typeAVisibleReturnSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.visibleReturnSplit
    presentation (fun input => input.object)
    (fun _ => erdosReceiverLoadProfile)
    (fun _ => erdosReceiverLoadProfile.loadMultiplier)

noncomputable def typeAExitOneSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitOneSplit
    (fun input => input.object) Official.typeARootedReturn
    (fun _ cycle => Or.inl cycle)

noncomputable def typeAExitTwoSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitTwoSplit
    (fun input => input.object) (fun _ cycle => Or.inl cycle)

noncomputable def typeAExitThreeSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitThreeSplit
    (fun input => input.object)
    (fun input =>
      Graph.InducedPathMaximalPacking.maximalProfile input.object 13)
    Official.acceptedCycleLengths (fun _ cycle => Or.inl cycle)

noncomputable def typeAExitFourSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitFourSplit presentation
    (fun input => input.object) (fun _ => erdosReceiverLoadProfile)
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ cycle => Or.inl cycle)

noncomputable def typeAExitFiveSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitFiveSplit presentation
    (fun input => input.object) (fun _ realized => Or.inl realized)

noncomputable def typeAExitSixSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitSixSplit presentation
    (fun input => input.object) (fun _ => Iff.rfl) (fun _ cycle => Or.inl cycle)

noncomputable def typeAExitSevenSplit :
    Core.DichotomyData.{1, 0, 0} problem abTarget :=
  Graph.Strategy.TypeAReceiverExhaustion.exitSevenSplit presentation
    (fun input => input.object)

noncomputable def definition : Core.ProblemDefinition.{1, 0, 0} :=
  { baseDefinition with
    data := {
      baseDefinition.data with
      scaleThresholdDichotomies := [Official.degreeSurplusScaleThreshold]
      finiteDensityBudgets := [Official.labelledGraphDensityBudget]
      orderedSurplusActivations := [Official.orderedSurplusActivation]
      baselineDemandAccountings := [Official.baselineDemandAccounting, Official.typeBFanMassAccounting]
      canonicalPairResponseAccountings :=
        [Official.canonicalPairResponseAccounting]
      canonicalCapacityTokenAccountings :=
        [Official.canonicalCapacityTokenAccounting]
      coupledHomogeneousFibrePressures :=
        [Official.coupledHomogeneousFibrePressure]
      finiteBottleneckClassifications :=
        [finiteBottleneckEntry]
      homogeneousBottlenecks :=
        [homogeneousBottleneckEntry]
      coldBranchAggregations := [coldBranchAggregation]
      supportComplementNormalizations := [supportComplementNormalization]
      boundaryDemandAccountings := [⟨0, Official.boundaryDemandAccounting⟩]
      -- Position 0 is the spine's own local-supply entry; the Type A
      -- receiver-load ledger is appended in the same order as the official
      -- registry, so both call sites share one index vector.
      localSupplyLowerBounds :=
        [⟨0, Official.localSupplyLowerBound⟩, ⟨0, Official.typeAReceiverLoadLedger⟩]
      targetRelativeRankDichotomies := []
      compressionLinkedTargetRelativeRankDichotomies :=
        [compressionLinkedTargetRelativeRankDichotomy]
      scans := [Official.typeBFanSafeCapScan,
        Official.typeBDegreeFourProfileScan, Official.typeBHybridEntryScan,
        Official.typeBBridgeDeficitScan]
      responses := [Official.typeBHeavyLocalResponse]
      dichotomies := [typeBDegreeSplit, typeBCertificateSplit, typeBB2LedgerSplit,
        typeBDirectCycleSplit,
        typeASaturatedSplit, typeAVisibleReturnSplit,
        typeAExitOneSplit, typeAExitTwoSplit, typeAExitThreeSplit,
        typeAExitFourSplit, typeAExitFiveSplit, typeAExitSixSplit,
        typeAExitSevenSplit]
      finiteStateCapacities := [⟨0, Official.finiteStateCapacity⟩]
      route8CarrierClosures := [⟨1, Official.typeARoute8Closure⟩]
    }
    metadata := {
      name := "Official Erdős–Gyárfás reduction to Type A/B"
      statement := "Every baseline graph has a power-of-two cycle or \
        contains the complete paper Type-A or Type-B certificate."
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

instance definition_hasFiniteBottleneckClassification :
    NeZero definition.data.finiteBottleneckClassifications.length :=
  ⟨by simp [definition]⟩

instance definition_hasHomogeneousBottleneck :
    NeZero definition.data.homogeneousBottlenecks.length :=
  ⟨by simp [definition]⟩

instance definition_hasColdBranchAggregation :
    NeZero definition.data.coldBranchAggregations.length :=
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

end HypostructureErdos64EG.AB
