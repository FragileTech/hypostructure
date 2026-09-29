import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

/-!
# Contract lemmas: the pair-overlap chain `[178]`--`[180]`

`def:pair-overlap-system`, `lem:pair-failure-overlap`, the canonical demand
returns of `lem:pair-system-realizability`, and the power-of-two cycle of
`lem:pair-system-increment-arithmetic`, each over a finite object with the
paper's assumptions as explicit hypotheses.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[178]` on the full pair schedule of `[131]`: the canonical pair set is
the schedule (G's canonical activation is blocker-free there), and the
canonical realization of G's spine family's code fails on it, so the canonical
first failure of G's pair code exists. -/
theorem pairOverlapFirstFailure_of_freeCodeUnrealized
    (unrealized : FreePairCodeUnrealizedStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    PairOverlapFirstFailureStatement data object := by
  obtain ⟨activation, spine, realization, activationSelected, spineSelected,
      realizationSelected, blockerFree, _scheduleCard, countFailure,
      pairSetNonempty⟩ := unrealized
  obtain ⟨active, rfl⟩ :=
    exists_active_of_canonicalPairActivation_eq_some activationSelected
  refine canonicalPairFirstFailure_isSome data object spineSelected
    realizationSelected
    (canonicalCodePairSet_eq_schedule data object activationSelected blockerFree)
    ⟨active, pairSetNonempty, fun _ member => member, ?_, countFailure,
      noProperBaseline.2⟩
  intro pair pairMem blocked
  exact blockerFree ⟨pair, pairMem, blocked⟩

/-- Node `[178]` on the capacity-free side of `[137]`: on the dependent arm of
`[130]` the canonical pair set is the free side of G's canonical capacity
charge, every free pair is blocker-free at the recorded activation, and the
canonical realization of G's spine family's code fails on it, so the canonical
first failure of G's pair code exists. -/
theorem pairOverlapFirstFailure_of_blockedCodeUnrealized
    (unrealized : BlockedPairCodeUnrealizedStatement data object)
    (dependent : DependentPairFamilyStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    PairOverlapFirstFailureStatement data object := by
  obtain ⟨capacity, spine, realization, capacitySelected, spineSelected,
      realizationSelected, _scheduleCard, countFailure, pairSetNonempty⟩ :=
    unrealized
  obtain ⟨dependentActivation, activationSelected, blocked⟩ := dependent
  obtain ⟨⟨active, activationEq⟩, -⟩ :=
    canonicalCapacity_spec_of_eq_some data object capacitySelected
  let pairSet := codeFreeSide data object capacity
  let activation := Graph.pairResponseActivation active
  let recorded := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) activation
    (object.portPairSchedule data.threshold)
  have pairSetBlockerFree : ∀ pair, pair ∈ pairSet →
      ¬ (recorded.blockers pair).Nonempty := by
    intro pair pairMem
    have freeRecorded : pair ∈ capacity.activation.freePairs
        data.threshold :=
      capacity.freeSide_subset_activationFree pairMem
    have freeParts :
        pair ∈ object.portPairSchedule data.threshold ∧
          ¬ (Graph.CanonicalFibreLedger.canonicalLabel
            Graph.SameTokenBlockerRoles.canonicalBlockerOrder
            capacity.activation.Blocks pair).isSome := by
      simpa [Graph.FiniteObject.DemandActivation.freePairs,
        Graph.FiniteObject.freePairs,
        Graph.CanonicalFibreLedger.unassigned] using freeRecorded
    have noCapacityBlocker :
        ¬ (capacity.activation.blockers pair).Nonempty := by
      intro blocked
      obtain ⟨kind, blocks⟩ :=
        (capacity.activation.exists_blocks_iff_blockers_nonempty
          pair).mpr blocked
      apply freeParts.2
      exact (Graph.CanonicalFibreLedger.isSome_canonicalLabel_iff
        Graph.SameTokenBlockerRoles.canonicalBlockerOrder
        capacity.activation.Blocks pair).mpr
          ⟨kind, capacity.activation.blocks_mem_canonicalBlockerOrder
            blocks, blocks⟩
    simpa [recorded, activation, activationEq] using
      (show ¬ (capacity.activation.blockers pair).Nonempty from
        noCapacityBlocker)
  refine canonicalPairFirstFailure_isSome data object spineSelected
    realizationSelected
    (canonicalCodePairSet_eq_freeSide data object activationSelected blocked
      capacitySelected)
    ⟨active, pairSetNonempty, ?_, pairSetBlockerFree, countFailure,
      noProperBaseline.2⟩
  intro pair member
  have membership :
      pair ∈ object.portPairSchedule data.threshold ∧
        Graph.CanonicalFibreLedger.canonicalLabel
          capacity.tokenOrder capacity.Eligible pair = none := by
    simpa [pairSet, codeFreeSide, Graph.freeSide,
      Graph.CanonicalFibreLedger.unassigned] using member
  exact membership.1

/-- `def:pair-overlap-system` at a first failure of a connected object: every
canonical pair support `X_π`, the canonical encoding order of `Π`, and the
literal conditional-fibre overlap system whose failed family (the prefix
through the first failed extension) is an obstruction. -/
theorem exists_pairOverlapSystem (first : PairOverlapFirstFailure data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    ∃ system, PairOverlapSystemSpec data object first system := by
  classical
  let activation := Graph.pairResponseActivation first.active
  let connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn object
        object.vertexFinset :=
    Graph.SupportComponents.Connected.connectedOn_vertexFinset
      object noProperBaseline.2
  let Pair := {pair // pair ∈ first.pairSet}
  have supportExists : ∀ pair : Pair,
      (activation.pairSupport pair.1).isSome := by
    intro pair
    exact activation.pairSupport_isSome_of_connected pair.1 connectedOn
  let responseSupport : Pair → Finset object.Vertex := fun pair =>
    Classical.choose (Option.isSome_iff_exists.mp (supportExists pair))
  have responseSupportSelected : ∀ pair : Pair,
      activation.pairSupport pair.1 = some (responseSupport pair) := by
    intro pair
    exact Classical.choose_spec (Option.isSome_iff_exists.mp
      (supportExists pair))
  have responseSupportConnected : ∀ pair : Pair,
      Graph.SupportComponents.Connected.ConnectedOn object
        (responseSupport pair) := by
    intro pair
    exact (Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
      (responseSupportSelected pair)).2
  let rank : Pair → Nat := fun pair => first.pairSet.toList.idxOf pair.1
  have rankInjective : Function.Injective rank := by
    intro left right equalRank
    apply Subtype.ext
    exact (List.idxOf_inj (Finset.mem_toList.mpr left.2)).mp equalRank
  let model : Graph.SparsePairSkeletonModel activation
      (object.portPairSchedule data.threshold) :=
    { BaseCoordinate := first.Coordinate
      baselineFamily := first.baselineFamily
      baseline := first.baselineRealization
      pairSet := first.pairSet
      pairSet_nonempty := first.pairSet_nonempty
      pairSet_subset_schedule := first.pairSet_subset_schedule
      responseSupport := responseSupport
      responseSupport_selected := responseSupportSelected
      responseSupport_connected := responseSupportConnected }
  let horizon := first.firstFailure.index + 1
  have horizonLe : horizon ≤ first.pairSet.card := by
    simpa [horizon] using first.firstFailure.index_lt
  let pairAt : Fin horizon → Pair := fun index =>
    ⟨first.pairSet.toList.get
        ⟨index.1, by
          simpa [Finset.length_toList] using
            lt_of_lt_of_le index.2 horizonLe⟩,
      Finset.mem_toList.mp (List.get_mem _ _)⟩
  have pairAtRank : ∀ index : Fin horizon,
      rank (pairAt index) = index.1 := by
    intro index
    dsimp [rank, pairAt]
    exact (Finset.nodup_toList first.pairSet).idxOf_getElem index.1
      (by simpa [Finset.length_toList] using
        lt_of_lt_of_le index.2 horizonLe)
  let failedFamily : Finset Pair :=
    Finset.univ.filter fun pair => rank pair < horizon
  have pairAtMem : ∀ index : Fin horizon, pairAt index ∈ failedFamily := by
    intro index
    simp only [failedFamily, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pairAtRank index]
    exact index.2
  have rankLt_of_mem_failedFamily : ∀ pair : Pair,
      pair ∈ failedFamily → rank pair < horizon := by
    intro pair member
    change pair ∈ Finset.univ.filter
      (fun candidate => rank candidate < horizon) at member
    exact (Finset.mem_filter.mp member).2
  let prefixEquiv : Fin horizon ≃ {pair // pair ∈ failedFamily} :=
    { toFun := fun index => ⟨pairAt index, pairAtMem index⟩
      invFun := fun pair => ⟨rank pair.1, by
        exact rankLt_of_mem_failedFamily pair.1 pair.2⟩
      left_inv := fun index => by
        apply Fin.ext
        exact pairAtRank index
      right_inv := fun pair => by
        apply Subtype.ext
        apply rankInjective
        exact pairAtRank ⟨rank pair.1, by
          exact rankLt_of_mem_failedFamily pair.1 pair.2⟩ }
  have failedFamilyCard : failedFamily.card = horizon := by
    rw [← Fintype.card_coe]
    calc
      Fintype.card {pair // pair ∈ failedFamily} =
          Fintype.card (Fin horizon) :=
        Fintype.card_congr prefixEquiv.symm
      _ = horizon := Fintype.card_fin horizon
  have failedFamilyNonempty : failedFamily.Nonempty := by
    have horizonPositive : 0 < horizon := by simp [horizon]
    exact Finset.card_pos.mp (by simpa [failedFamilyCard])
  have skeletonCard : Nat.card model.Skeleton = Graph.skeletonBudget object := by
    dsimp [Graph.SparsePairSkeletonModel.Skeleton]
    simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
      Graph.PackedWindowRealization.card_skeleton
        object.vertexCount object.edgeCount
  have failedFamilyObstruction : failedFamily.Nonempty ∧
      ¬ model.CountRealizing data.LengthOK failedFamily := by
    refine ⟨failedFamilyNonempty, ?_⟩
    apply Graph.SparsePairSkeletonModel.not_countRealizing_of_class_lt
    rw [skeletonCard, failedFamilyCard]
    exact Nat.lt_of_not_ge first.firstFailure.failedNext
  let system : PairOverlapSystem data object :=
    { first := first
      responseSupport := responseSupport
      responseSupport_selected := responseSupportSelected
      responseSupport_connected := responseSupportConnected
      rank := rank
      rank_injective := rankInjective
      failedFamily := failedFamily
      failedFamily_eq := rfl
      failedFamily_nonempty := failedFamilyNonempty
      failedFamily_card := failedFamilyCard
      failedFamily_obstruction := by
        simpa [model] using failedFamilyObstruction }
  exact ⟨system, rfl, fun _ => rfl⟩

/-- Node `[178]`, `def:pair-overlap-system` at G: the canonical overlap system of
the canonical first failure exists. -/
theorem pairOverlapSystem_of_firstFailure
    (firstFailure : PairOverlapFirstFailureStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    PairOverlapSystemStatement data object := by
  obtain ⟨first, firstSelected⟩ := firstFailure
  obtain ⟨system, selected, -⟩ :=
    canonicalChoice_spec (exists_pairOverlapSystem first noProperBaseline)
  exact ⟨system, by
    rw [canonicalPairOverlapSystem, firstSelected, Option.bind_some]
    exact selected⟩

/-- `lem:pair-failure-overlap`: on a conditionally factorizing pair overlap
system, an inclusion-minimal obstruction inside the failed family has two
overlapping members and a connected union of response supports. -/
theorem exists_pairFailureOverlap (system : PairOverlapSystem data object)
    (factorization : system.ConditionalFactorization) :
    ∃ overlap : PairFailureOverlap data object, overlap.system = system := by
  classical
  let family := system.obstructionFamily
  have minimal : system.minimalObstruction family :=
    system.obstructionFamily_minimal
  have overlapWitness : ∃ left ∈ family, ∃ right ∈ family,
      left ≠ right ∧ system.toSkeletonModel.Overlaps left right := by
    by_contra absent
    push Not at absent
    have separated : system.toSkeletonModel.PairwiseSeparated family := by
      intro left leftMem right rightMem different overlap
      exact absent left leftMem right rightMem different overlap
    exact minimal.1.2 (factorization.separated separated)
  have connected :
      Graph.SupportComponents.Connected.ConnectedOn object
        (system.overlapSupport family) := by
    let model := system.toSkeletonModel
    have familyNonempty : family.Nonempty := minimal.1.1
    have notRealizing :
        ¬ model.CountRealizing data.LengthOK family := by
      simpa [model, PairOverlapSystem.realizingOrder] using minimal.1.2
    have properRealizing : ∀ proper, proper ⊂ family → proper.Nonempty →
        model.CountRealizing data.LengthOK proper := by
      intro proper properSubset properNonempty
      simpa [model, PairOverlapSystem.realizingOrder] using
        minimal.2 proper properSubset properNonempty
    let support := model.responseSupportUnion family
    have supportNonempty : support.Nonempty := by
      obtain ⟨pair, pairMem⟩ := familyNonempty
      obtain ⟨vertex, vertexMem⟩ :=
        (model.responseSupport_connected pair).1
      refine ⟨vertex, ?_⟩
      change vertex ∈ model.responseSupportUnion family
      exact Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩
    change Graph.SupportComponents.Connected.ConnectedOn object support
    by_contra disconnected
    have componentEqOfPath
        {left right : object.Vertex}
        (leftMem : left ∈ support) (rightMem : right ∈ support)
        (path : object.graph.Walk left right)
        (inside : ∀ vertex ∈ path.support, vertex ∈ support) :
        Graph.SupportComponents.Connected.componentOf object support
            ⟨left, leftMem⟩ =
          Graph.SupportComponents.Connected.componentOf object support
            ⟨right, rightMem⟩ := by
      apply SimpleGraph.ConnectedComponent.sound
      let induced := path.induce (↑support) inside
      exact ⟨by
        simpa [Graph.SupportComponents.Connected.InducedObject,
          Graph.FiniteObject.induce] using induced⟩
    let anchor (pair : {pair // pair ∈ system.first.pairSet}) :
        object.Vertex :=
      Classical.choose (model.responseSupport_connected pair).1
    have anchorMem (pair : {pair // pair ∈ system.first.pairSet}) :
        anchor pair ∈ model.responseSupport pair :=
      Classical.choose_spec (model.responseSupport_connected pair).1
    have responseSubsetOwnComponent
        (pair : {pair // pair ∈ system.first.pairSet})
        (pairMem : pair ∈ family) :
        model.responseSupport pair ⊆
          Graph.SupportComponents.Connected.members object support
            (Graph.SupportComponents.Connected.componentOf object support
              ⟨anchor pair, by
                simpa [support, model, PairOverlapSystem.toSkeletonModel,
                  Graph.SparsePairSkeletonModel.responseSupportUnion] using
                    (Finset.mem_biUnion.mpr
                      ⟨pair, pairMem, anchorMem pair⟩)⟩) := by
      intro vertex vertexMem
      have anchorSupport : anchor pair ∈ support := by
        simpa [support, model, PairOverlapSystem.toSkeletonModel,
          Graph.SparsePairSkeletonModel.responseSupportUnion] using
            (Finset.mem_biUnion.mpr
              ⟨pair, pairMem, anchorMem pair⟩)
      have vertexSupport : vertex ∈ support := by
        simpa [support, model, PairOverlapSystem.toSkeletonModel,
          Graph.SparsePairSkeletonModel.responseSupportUnion] using
            (Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩)
      obtain ⟨path, _path, insidePair⟩ :=
        (model.responseSupport_connected pair).2
          (anchorMem pair) vertexMem
      apply (Graph.SupportComponents.Connected.mem_members_iff
        object support _ vertex).mpr
      refine ⟨vertexSupport, ?_⟩
      exact (componentEqOfPath anchorSupport vertexSupport path
        (fun current currentMem => by
          simpa [support, model, PairOverlapSystem.toSkeletonModel,
            Graph.SparsePairSkeletonModel.responseSupportUnion] using
              (Finset.mem_biUnion.mpr
                ⟨pair, pairMem, insidePair current currentMem⟩))).symm
    let rootPair := Classical.choose familyNonempty
    have rootPairMem : rootPair ∈ family :=
      Classical.choose_spec familyNonempty
    have rootAnchorSupport : anchor rootPair ∈ support := by
      simpa [support, model, PairOverlapSystem.toSkeletonModel,
        Graph.SparsePairSkeletonModel.responseSupportUnion] using
          (Finset.mem_biUnion.mpr
            ⟨rootPair, rootPairMem, anchorMem rootPair⟩)
    let rootComponent :=
      Graph.SupportComponents.Connected.componentOf object support
        ⟨anchor rootPair, rootAnchorSupport⟩
    let rootMembers :=
      Graph.SupportComponents.Connected.members object support rootComponent
    have rootComponentMem : rootComponent ∈
        Graph.SupportComponents.Connected.order object support := by
      obtain ⟨component, componentMem, anchorInComponent⟩ :=
        (Graph.SupportComponents.Connected.mem_support_iff_mem_component
          object support (anchor rootPair)).mp rootAnchorSupport
      have equal : rootComponent = component := by
        exact (Graph.SupportComponents.Connected.mem_members_iff
          object support component (anchor rootPair)).mp
            anchorInComponent |>.2
      simpa [equal] using componentMem
    have rootConnected :
        Graph.SupportComponents.Connected.ConnectedOn object rootMembers :=
      Graph.SupportComponents.Connected.connectedOn_of_mem_order
        object support rootComponentMem
    have rootMembersSubset : rootMembers ⊆ support := by
      intro vertex vertexMem
      exact (Graph.SupportComponents.Connected.mem_members_iff
        object support rootComponent vertex).mp vertexMem |>.1
    have rootResponseSubset :
        model.responseSupport rootPair ⊆ rootMembers := by
      simpa [rootComponent, rootMembers] using
        responseSubsetOwnComponent rootPair rootPairMem
    have responseSubsetRootOfCommon
        (pair : {pair // pair ∈ system.first.pairSet})
        (pairMem : pair ∈ family)
        {common : object.Vertex}
        (commonPair : common ∈ model.responseSupport pair)
        (commonRoot : common ∈ rootMembers) :
        model.responseSupport pair ⊆ rootMembers := by
      intro vertex vertexMem
      have commonSupport : common ∈ support :=
        rootMembersSubset commonRoot
      have vertexSupport : vertex ∈ support := by
        simpa [support, model, PairOverlapSystem.toSkeletonModel,
          Graph.SparsePairSkeletonModel.responseSupportUnion] using
            (Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩)
      obtain ⟨path, _path, insidePair⟩ :=
        (model.responseSupport_connected pair).2 commonPair vertexMem
      have commonComponent :
          Graph.SupportComponents.Connected.componentOf object support
              ⟨common, commonSupport⟩ = rootComponent :=
        (Graph.SupportComponents.Connected.mem_members_iff
          object support rootComponent common).mp commonRoot |>.2
      have pathComponents :=
        componentEqOfPath commonSupport vertexSupport path
          (fun current currentMem => by
            simpa [support, model, PairOverlapSystem.toSkeletonModel,
              Graph.SparsePairSkeletonModel.responseSupportUnion] using
                (Finset.mem_biUnion.mpr
                  ⟨pair, pairMem, insidePair current currentMem⟩))
      apply (Graph.SupportComponents.Connected.mem_members_iff
        object support rootComponent vertex).mpr
      exact ⟨vertexSupport,
        pathComponents.symm.trans commonComponent⟩
    have outsideRoot : ∃ pair ∈ family,
        ¬ model.responseSupport pair ⊆ rootMembers := by
      by_contra absent
      push Not at absent
      have supportSubset : support ⊆ rootMembers := by
        intro vertex vertexMem
        have inUnion :
            vertex ∈ family.biUnion model.responseSupport := by
          simpa [support, model, PairOverlapSystem.toSkeletonModel,
            Graph.SparsePairSkeletonModel.responseSupportUnion] using
              vertexMem
        obtain ⟨pair, pairMem, inResponse⟩ :=
          Finset.mem_biUnion.mp inUnion
        exact absent pair pairMem inResponse
      have supportEq : support = rootMembers :=
        Finset.Subset.antisymm supportSubset rootMembersSubset
      apply disconnected
      simpa [supportEq] using rootConnected
    let left : Finset {pair // pair ∈ system.first.pairSet} :=
      family.filter fun pair => model.responseSupport pair ⊆ rootMembers
    let right : Finset {pair // pair ∈ system.first.pairSet} :=
      family \ left
    have leftSubset : left ⊆ family := Finset.filter_subset _ _
    have rightSubset : right ⊆ family := Finset.sdiff_subset
    have leftNonempty : left.Nonempty := by
      exact ⟨rootPair, by
        simp [left, rootPairMem, rootResponseSubset]⟩
    have rightNonempty : right.Nonempty := by
      obtain ⟨pair, pairMem, notSubset⟩ := outsideRoot
      exact ⟨pair, by simp [right, left, pairMem, notSubset]⟩
    have disjoint : Disjoint left right := by
      apply Finset.disjoint_left.mpr
      intro pair pairLeft pairRight
      exact (Finset.mem_sdiff.mp pairRight).2 pairLeft
    have noCross : ∀ leftPair, leftPair ∈ left →
        ∀ rightPair, rightPair ∈ right →
          ¬ model.Overlaps leftPair rightPair := by
      intro leftPair leftMem rightPair rightMem overlap
      have leftFacts := Finset.mem_filter.mp leftMem
      have rightFacts := Finset.mem_sdiff.mp rightMem
      obtain ⟨vertex, vertexLeft, vertexRight,
          _leftPort, _rightPort⟩ := overlap
      have rightSubsetRoot := responseSubsetRootOfCommon rightPair
        (rightSubset rightMem) vertexRight (leftFacts.2 vertexLeft)
      exact rightFacts.2 (Finset.mem_filter.mpr
        ⟨rightSubset rightMem, rightSubsetRoot⟩)
    have leftProper : left ⊂ family := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨leftSubset, ?_⟩
      intro equal
      obtain ⟨pair, pairRight⟩ := rightNonempty
      exact (Finset.mem_sdiff.mp pairRight).2
        (equal ▸ rightSubset pairRight)
    have rightProper : right ⊂ family := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨rightSubset, ?_⟩
      intro equal
      obtain ⟨pair, pairLeft⟩ := leftNonempty
      exact (Finset.mem_sdiff.mp
        (equal ▸ leftSubset pairLeft)).2 pairLeft
    have unionEq : left ∪ right = family := by
      change left ∪ (family \ left) = family
      rw [Finset.union_comm]
      exact Finset.sdiff_union_of_subset leftSubset
    apply notRealizing
    have familyUnionEq : system.familyUnion left right = family := by
      unfold PairOverlapSystem.familyUnion
        Graph.SparsePairSkeletonModel.familyUnion
      exact unionEq
    have joined := factorization.concatenate left right
      leftNonempty rightNonempty disjoint familyUnionEq noCross
      (properRealizing left leftProper leftNonempty)
      (properRealizing right rightProper rightNonempty)
    exact joined
  exact ⟨
    { system := system
      family := family
      factorization := factorization
      minimal := minimal
      overlapWitness := overlapWitness
      connected := connected }, rfl⟩

/-- `lem:pair-failure-overlap`, node `[178]`, at G: the canonical overlap system
factorizes, so its canonical minimal overlap obstruction exists. -/
theorem pairFailureOverlap_of_factorization
    (factorizationHolds : PairConditionalFactorizationStatement data object) :
    PairFailureOverlapStatement data object := by
  obtain ⟨system, systemSelected, factorization⟩ := factorizationHolds
  obtain ⟨overlap, selected, -⟩ :=
    canonicalChoice_spec (exists_pairFailureOverlap system factorization)
  exact ⟨overlap, by
    rw [canonicalPairFailureOverlap, systemSelected, Option.bind_some]
    exact selected⟩

/-- Node `[179]`: the two demands of the minimal overlap obstruction with their
canonical port returns and the graph-derived return bound. -/
theorem pairDemandReturns_of_failureOverlap
    (overlap : PairFailureOverlapStatement data object) :
    PairDemandReturnsStatement data object := by
  obtain ⟨overlap, selected⟩ := overlap
  exact ⟨PairDemandReturns.of overlap, by
    rw [canonicalPairDemandReturns, selected, Option.map_some]⟩

/-- Node `[180]`, direct arithmetic arm (`lem:pair-system-increment-arithmetic`
with `SerialSystem.Spectrum.exists_pow_realized`): the corrected full-modulus
arithmetic realizes an actual simple cycle of length `2^k`, `k ≥ 2`, which is
accepted when the accepted lengths are exactly the powers of two. -/
theorem pairPowerOfTwoCycle_of_arithmetic
    (arithmeticFact : PairSerialArithmeticStatement data object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    PairPowerOfTwoCycleStatement data object := by
  classical
  obtain ⟨_serial, -, ⟨arithmetic⟩⟩ := arithmeticFact
  let spectrum := arithmetic.spectrum
  letI : NeZero arithmetic.modulus := arithmetic.modulus_neZero
  letI : NeZero spectrum.modulus :=
    { out := by
        change arithmetic.modulus ≠ 0
        exact NeZero.ne arithmetic.modulus }
  have spanning : spectrum.ScaleSpanning := by
    simpa [spectrum, PairSerialArithmetic.spectrum] using
      arithmetic.spanning
  let hit := spectrum.exists_pow_realized
    arithmetic.wide arithmetic.criterion spanning
  let exponent := Classical.choose hit
  have realized := Classical.choose_spec hit
  let cycle := Classical.choice realized
  have threeLe : 3 ≤ 2 ^ exponent := by
    rw [← cycle.length_eq]
    exact cycle.isCycle.three_le_length
  have exponentLower : 2 ≤ exponent := by
    by_contra lower
    have cases : exponent = 0 ∨ exponent = 1 := by omega
    rcases cases with zero | one
    · have powerEq : 2 ^ exponent = 1 := by simp [zero]
      omega
    · have powerEq : 2 ^ exponent = 2 := by simp [one]
      omega
  have accepted : data.LengthOK (2 ^ exponent) :=
    (lengthOK_iff (2 ^ exponent)).2
      (Core.DyadicLength.powerOfTwoLength_of_exists
        ⟨exponent, exponentLower, rfl⟩)
  let certificate : Graph.CycleCertificate object
      data.LengthOK :=
    { vertex := cycle.vertex
      walk := cycle.walk
      isCycle := cycle.isCycle
      length_ok := by simpa [cycle.length_eq] using accepted }
  exact ⟨certificate⟩

end Hypostructure.Graph.Contracts.SurplusPair
