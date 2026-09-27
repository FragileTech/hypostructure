import Hypostructure.Graph.Statements.TypeB
import Hypostructure.Graph.Statements.CanonicalSurplus
import Hypostructure.Graph.Statements.CanonicalSurplusCapacity

/-!
# Statements: SurplusPair

Proof-agnostic statement definitions of the minimum-degree cycle spine:
sparse-surplus, capacity-token, canonical-pair, homogeneous-bottleneck and pair-system statements.
Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- G's canonical activation, when it exists, is the pair-response activation
of the node-`[125]` port data (a proposition, so the activation is unique). -/
theorem exists_active_of_canonicalPairActivation_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    {activation : object.DemandActivation object.PairCoordinate
      (object.Vertex × object.Vertex)}
    (selected : canonicalPairActivation data object = some activation) :
    ∃ active : Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold,
      activation = Graph.pairResponseActivation active := by
  by_cases active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold
  · refine ⟨active, ?_⟩
    rw [canonicalPairActivation_eq data object active] at selected
    exact (Option.some.inj selected).symm
  · rw [(canonicalPairActivation_eq_none_iff data object).2 active] at selected
    cases selected

/-- A target-defective identification of the two demands of a scheduled pair,
read on G's own piece at their canonical support (blocker (e) of
`def:surplus-blockers`), is a clause-(b) exit of G's declared sparse family:
the demands are declared coordinates of that family with the same supports. -/
theorem declaredSparseSurplusExit_of_demandDefect {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairSubset : pair ⊆ object.excessPorts data.threshold)
    (defect : Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK)
      object pair (Graph.pairResponseActivation active).declaredSupport) :
    DeclaredSparseSurplusExit data object := by
  classical
  refine .targetDefect ?_
  refine Graph.ResidualTargetDefect.map
    (fun demand => (Sum.inl demand : SparseDeclaredCoordinate data object))
    ?_ ?_ ?_ defect
  · intro first _ second _ equal
    simpa using equal
  · intro demand member
    unfold sparseDeclaredFamily
    rw [canonicalPairActivation_eq data object active]
    simp only [Finset.mem_union, Finset.mem_image]
    exact Or.inl ⟨demand, pairSubset member, rfl⟩
  · intro demand _
    unfold sparseDeclaredSupport
    rw [canonicalPairActivation_eq data object active]
    rfl

/-- The actual seven-coordinate routing label on a pair of the certified
source pattern. The cubic baseline and the same active shoulder witnesses bound
its true internal degrees; no profile values or label map are supplied by a caller.
The pair order is `Finset.toList`, exactly as in the routing owner. -/
noncomputable def sameTokenActualRoutingLabel (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (cubic : data.threshold = 3)
    (capacity : Graph.CapacityPresentation object data.threshold data.windowOrder)
    (certified : Graph.CertifiedObjectCapacityLedger object data.threshold
      data.windowOrder data.surplusScale capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role)
    (pattern : Finset (Finset (object.Vertex × object.Vertex)))
    (patternSubset : pattern ⊆ certified.ledger.presented.roleFibre token role)
    (pair : Finset (object.Vertex × object.Vertex)) (pairMem : pair ∈ pattern)
    (demand : object.Vertex × object.Vertex) (_demandMem : demand ∈ pair) :
    Graph.SameTokenRoutingGerms.RoutingLabel (Fin data.threshold → Fin data.threshold)
      (Graph.WindowCurvature.Label data.windowOrder) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have fibreMem := patternSubset pairMem
  have scheduleMem : pair ∈ object.portPairSchedule data.threshold :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp fibreMem).1).1
  have pairFacts : pair ⊆ object.excessPorts data.threshold ∧ pair.card = 2 :=
    Finset.mem_powersetCard.mp scheduleMem
  have pairCard : pair.card = 2 := pairFacts.2
  let first := pair.toList.get
    ⟨0, by simp [pairCard]⟩
  let second := pair.toList.get
    ⟨1, by simp [pairCard]⟩
  have firstMem : first ∈ object.excessPorts data.threshold := by
    apply pairFacts.1
    exact Finset.mem_toList.mp (pair.toList.get_mem _)
  have secondMem : second ∈ object.excessPorts data.threshold := by
    apply pairFacts.1
    exact Finset.mem_toList.mp (pair.toList.get_mem _)
  let portStatus (u : object.Vertex × object.Vertex) :
      Graph.SameTokenRoutingGerms.PortStatus :=
    if _ : ∃ member : u ∈ object.excessPorts data.threshold,
        ∃ left ∈ (object.surplusPortOfMem member).shoulders,
          ∃ right ∈ (object.surplusPortOfMem member).shoulders,
            left ≠ right ∧ object.graph.Adj left right then
      .triangular
    else .openPort
  have supportCard (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold) :
      (object.surplusPortOfMem hu).support.card = data.threshold := by
    let port := object.surplusPortOfMem hu
    have endpointNotShoulder : port.endpoint ∉ port.shoulders := by
      intro endpointShoulder
      exact object.graph.loopless.irrefl _
        ((port.mem_shoulders_iff port.endpoint).1 endpointShoulder).2
    obtain ⟨left, right, shoulderPair, shouldersDifferent⟩ := active.shoulderPair u hu
    have shouldersEq : port.shoulders = {left, right} := by
      ext vertex
      rw [shoulderPair vertex]
      simp
    have shoulderCard : port.shoulders.card = data.threshold - 1 := by
      rw [shouldersEq, Finset.card_pair shouldersDifferent, cubic]
    change port.support.card = data.threshold
    unfold Graph.FiniteObject.SurplusPort.support
    rw [Finset.card_insert_of_notMem endpointNotShoulder, shoulderCard, cubic]
  have degreeBound (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold)
      (v : object.Vertex) (hv : v ∈ (object.surplusPortOfMem hu).support) :
      (object.induce (object.surplusPortOfMem hu).support).degree ⟨v, hv⟩ <
        data.threshold := by
    have finiteBound :=
      (object.induce (object.surplusPortOfMem hu).support).degree_lt_vertexCount ⟨v, hv⟩
    rw [Graph.FiniteObject.vertexCount_induce, supportCard u hu] at finiteBound
    exact finiteBound
  let boundaryProfile (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold) :
      Fin data.threshold → Fin data.threshold := fun index => by
    let support := (object.surplusPortOfMem hu).support
    let ordered := object.orderedVertices.filter fun vertex => vertex ∈ support
    have orderedSet : ordered.toFinset = support := by
      ext vertex
      simp [ordered, Graph.FiniteObject.orderedVertices, FinEnum.mem_toList]
    have orderedNodup : ordered.Nodup :=
      List.Nodup.filter _ FinEnum.nodup_toList
    have orderedLength : ordered.length = data.threshold := by
      rw [← List.toFinset_card_of_nodup orderedNodup, orderedSet]
      exact supportCard u hu
    let vertex := ordered.get ⟨index.1, by rw [orderedLength]; exact index.2⟩
    have vertexMem : vertex ∈ support := by
      have inside : vertex ∈ ordered := ordered.get_mem _
      simp only [ordered, List.mem_filter, decide_eq_true_eq] at inside
      exact inside.2
    exact ⟨(object.induce support).degree ⟨vertex, vertexMem⟩,
      degreeBound u hu vertex vertexMem⟩
  let windowLabel : Graph.WindowCurvature.Label data.windowOrder :=
    Finset.univ.filter fun index =>
      ∃ window ∈ capacity.packing,
        ∃ presentation : Graph.TypeBDirectCycle.Presentation object data.windowOrder,
          presentation.support = window ∧
            presentation.coordinate index.1 ∈ capacity.sameTokenRoutingSupport token pair
  let chordFlag : Bool :=
    match Graph.FiniteObject.canonicalBlocker capacity.activation pair with
    | some (.arithmeticChordSet _) => true
    | _ => false
  let endpoint : Fin 2 := if demand = first then 0 else 1
  exact (capacity.role pair, Graph.FiniteObject.CapacityToken.subtype token,
    endpoint, (portStatus first, portStatus second),
    (boundaryProfile first firstMem, boundaryProfile second secondMem),
    windowLabel, chordFlag)

/-- The canonical first failed pair extension of a realized baseline code.
Every prefix through `index` still fits the current skeleton stratum, while
adjoining the pair at that index is the first failed extension. -/
structure FirstFailedPairExtension (object : Graph.FiniteObject.{u})
    {Coordinate : Type u} (family : Finset Coordinate)
    (free : Finset (Finset (object.Vertex × object.Vertex))) where
  index : Nat
  index_lt : index < free.card
  pair : Finset (object.Vertex × object.Vertex)
  pair_eq : pair = free.toList.get
    ⟨index, by simpa [Finset.length_toList] using index_lt⟩
  pair_mem : pair ∈ free
  realizedThrough : ∀ length, length ≤ index →
    2 ^ (family.card + length) ≤ Graph.skeletonBudget object
  failedNext :
    ¬ 2 ^ (family.card + (index + 1)) ≤ Graph.skeletonBudget object

/-- Select the least failed extension and retain the canonical pair at that
position in the free-side order. -/
noncomputable def firstFailedPairExtensionOf
    {object : Graph.FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {free : Finset (Finset (object.Vertex × object.Vertex))}
    (realization : Graph.BaselineCodeRealization object family)
    (failure : ¬ 2 ^ (family.card + free.card) ≤
      Graph.skeletonBudget object) :
    FirstFailedPairExtension object family free := by
  have baselineCount : 2 ^ family.card ≤ Graph.skeletonBudget object :=
    realization.two_pow_le_skeletonBudget
  have existsFailure : ∃ extension : Nat,
      extension ≤ free.card ∧
        ¬ 2 ^ (family.card + extension) ≤ Graph.skeletonBudget object :=
    ⟨free.card, le_rfl, failure⟩
  let firstFailure := Nat.find existsFailure
  have firstFailureSpec : firstFailure ≤ free.card ∧
      ¬ 2 ^ (family.card + firstFailure) ≤ Graph.skeletonBudget object :=
    Nat.find_spec existsFailure
  have firstFailurePositive : 0 < firstFailure := by
    by_contra notPositive
    have firstFailureZero : firstFailure = 0 :=
      Nat.eq_zero_of_not_pos notPositive
    exact firstFailureSpec.2 (by
      simpa [firstFailureZero] using baselineCount)
  let index := firstFailure - 1
  have indexLt : index < free.card := by
    dsimp [index]
    omega
  have realizedAtIndex :
      2 ^ (family.card + index) ≤ Graph.skeletonBudget object := by
    by_contra failedAtIndex
    have indexBefore : index < firstFailure := by
      dsimp [index]
      omega
    exact (Nat.find_min existsFailure indexBefore)
      ⟨by omega, failedAtIndex⟩
  have realizedThrough : ∀ length, length ≤ index →
      2 ^ (family.card + length) ≤ Graph.skeletonBudget object := by
    intro length lengthLe
    exact (Nat.pow_le_pow_right (by norm_num)
      (Nat.add_le_add_left lengthLe family.card)).trans realizedAtIndex
  have failedNext :
      ¬ 2 ^ (family.card + (index + 1)) ≤ Graph.skeletonBudget object := by
    have nextEq : index + 1 = firstFailure := by
      dsimp [index]
      omega
    simpa [nextEq] using firstFailureSpec.2
  let pair := free.toList.get
    ⟨index, by simpa [Finset.length_toList] using indexLt⟩
  have pairMem : pair ∈ free := by
    exact Finset.mem_toList.mp (List.get_mem free.toList
      ⟨index, by simpa [Finset.length_toList] using indexLt⟩)
  exact
    { index := index
      index_lt := indexLt
      pair := pair
      pair_eq := rfl
      pair_mem := pairMem
      realizedThrough := realizedThrough
      failedNext := failedNext }

/-- The route-independent first pair-code failure consumed at node `[178]`.
The pair set is the literal schedule selected by `[131]` or `[137]`; the
baseline realization and least failed extension are those retained by that
route.  The failed pair is equipped with its canonical response support
`X_π`, selected through the framework's support API. -/
structure PairOverlapFirstFailure (data : Parameters)
    (object : Graph.FiniteObject.{u}) where
  active : Graph.ActiveSurplusDemands
    (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
    data.threshold
  Coordinate : Type u
  baselineFamily : Finset Coordinate
  coordinateSupport : Coordinate → Finset object.Vertex
  baselineRealization : Graph.BaselineCodeRealization object baselineFamily
  pairSet : Finset (Finset (object.Vertex × object.Vertex))
  pairSet_nonempty : pairSet.Nonempty
  pairSet_subset_schedule :
    pairSet ⊆ object.portPairSchedule data.threshold
  pairSet_blockerFree : ∀ pair, pair ∈ pairSet →
    ¬ Graph.SparsePairDEProfileObstructionAt
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
          pair ∧
      ¬ Graph.SparsePairDEResponseObstructionAt
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
          pair
  firstFailure : FirstFailedPairExtension object baselineFamily pairSet
  responseSupport : Finset object.Vertex
  responseSupport_selected :
    (Graph.pairResponseActivation active).pairSupport firstFailure.pair =
      some responseSupport
  pairSeed_subset_responseSupport :
    (Graph.pairResponseActivation active).pairSeed firstFailure.pair ⊆
      responseSupport
  responseSupport_connected :
    Graph.SupportComponents.Connected.ConnectedOn object responseSupport

namespace PairOverlapFirstFailure

/-- The literal two-element demand finset formed with the active object's own
decidable equality. -/
noncomputable def demandPair (object : Graph.FiniteObject.{u})
    (left right : object.Vertex × object.Vertex) :
    Finset (object.Vertex × object.Vertex) := by
  letI := object.vertexPairDecidableEq
  exact {left, right}

/-- Package a retained first failed extension with the canonical connected
response support of its failed pair. -/
noncomputable def of
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (Coordinate : Type u) (baselineFamily : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (baselineRealization : Graph.BaselineCodeRealization object baselineFamily)
    (pairSet : Finset (Finset (object.Vertex × object.Vertex)))
    (pairSet_nonempty : pairSet.Nonempty)
    (pairSet_subset_schedule :
      pairSet ⊆ object.portPairSchedule data.threshold)
    (pairSet_blockerFree : ∀ pair, pair ∈ pairSet →
      ¬ Graph.SparsePairDEProfileObstructionAt
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
            pair ∧
        ¬ Graph.SparsePairDEResponseObstructionAt
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
            pair)
    (firstFailure : FirstFailedPairExtension object baselineFamily pairSet)
    (connected : object.graph.Connected) :
    PairOverlapFirstFailure data object := by
  let connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn object object.vertexFinset :=
    Graph.SupportComponents.Connected.connectedOn_vertexFinset object connected
  have supportExists :
      ((Graph.pairResponseActivation active).pairSupport
        firstFailure.pair).isSome :=
    (Graph.pairResponseActivation active).pairSupport_isSome_of_connected
      firstFailure.pair connectedOn
  let responseSupport :=
    Classical.choose (Option.isSome_iff_exists.mp supportExists)
  have selected :
      (Graph.pairResponseActivation active).pairSupport firstFailure.pair =
        some responseSupport :=
    Classical.choose_spec (Option.isSome_iff_exists.mp supportExists)
  have supportProperties :=
    (Graph.pairResponseActivation active).pairSupport_mem_candidates selected
  exact
    { active := active
      Coordinate := Coordinate
      baselineFamily := baselineFamily
      coordinateSupport := coordinateSupport
      baselineRealization := baselineRealization
      pairSet := pairSet
      pairSet_nonempty := pairSet_nonempty
      pairSet_subset_schedule := pairSet_subset_schedule
      pairSet_blockerFree := pairSet_blockerFree
      firstFailure := firstFailure
      responseSupport := responseSupport
      responseSupport_selected := selected
      pairSeed_subset_responseSupport := supportProperties.1
      responseSupport_connected := supportProperties.2 }

end PairOverlapFirstFailure

namespace PairOverlapFirstFailure

/-- The failed coordinate retained at `[178]` is still a member of the active
object's literal pair schedule.  This is the provenance node `[179]` uses; it
does not reconstruct a pair from cardinal data. -/
theorem failedPair_mem_portPairSchedule
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (first : PairOverlapFirstFailure data object) :
    first.firstFailure.pair ∈ object.portPairSchedule data.threshold :=
  first.pairSet_subset_schedule first.firstFailure.pair_mem

/-- Hence the failed coordinate consists of exactly two active demands. -/
theorem failedPair_card
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (first : PairOverlapFirstFailure data object) :
    first.firstFailure.pair.card = 2 :=
  Graph.card_of_mem_portPairSchedule object data.threshold
    first.failedPair_mem_portPairSchedule

/-- The two literal active demands named by the failed pair coordinate. -/
theorem exists_failedPair_demands
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (first : PairOverlapFirstFailure data object) :
    ∃ left right : object.Vertex × object.Vertex,
      left ≠ right ∧
        first.firstFailure.pair = demandPair object left right := by
  letI := object.vertexPairDecidableEq
  obtain ⟨left, right, different, pairEq⟩ :=
    Finset.card_eq_two.mp first.failedPair_card
  exact ⟨left, right, different, by simpa [demandPair] using pairEq⟩

/-- The exact connector used by `[179]`: the selected response support of the
failed pair together with the two canonical return supports already carried by
the active-family activation. -/
noncomputable def failedPairConnector
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (first : PairOverlapFirstFailure data object) : Finset object.Vertex := by
  classical
  exact first.responseSupport ∪ first.firstFailure.pair.biUnion
    (Graph.pairResponseActivation first.active).returnSupport

/-- That connector is connected in the active object.  This is the declared
`X_π ∪ R_p ∪ R_q` connector theorem, specialized to the literal failed
coordinate rather than postulated as a new carrier. -/
theorem failedPairConnector_connectedOn
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (first : PairOverlapFirstFailure data object) :
    Graph.SupportComponents.Connected.ConnectedOn object
      first.failedPairConnector := by
  classical
  let activation := Graph.pairResponseActivation first.active
  let recorded := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) activation
    (object.portPairSchedule data.threshold)
  have pairSubset : first.firstFailure.pair ⊆
      object.excessPorts data.threshold :=
    object.subset_excessPorts_of_mem_portPairSchedule data.threshold
      first.failedPair_mem_portPairSchedule
  have selected : recorded.pairSupport first.firstFailure.pair =
      some first.responseSupport := by
    change activation.pairSupport first.firstFailure.pair =
      some first.responseSupport
    exact first.responseSupport_selected
  have connected := Graph.recordedPairConnector_connectedOn first.active
    pairSubset selected
  simpa [failedPairConnector, recorded, Graph.recordSparsePairDEBlockers,
    activation] using connected

end PairOverlapFirstFailure

/-- The union of the literal port-return supports of all pairs in the current
first-failure package.  Decidable equality is an execution detail of the
finite union and is deliberately kept behind this mathematical definition. -/
noncomputable def PairOverlapFirstFailure.portReturns
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (first : PairOverlapFirstFailure data object) : Finset object.Vertex := by
  classical
  exact first.pairSet.biUnion
    (Graph.pairResponseActivation first.active).pairSeed

/-- **`def:pair-overlap-system`.**

The current fixed-`(n,m)` skeleton class is encoded by the edges outside all
port-return supports, the already-realized baseline word, and the pair
coordinates exposed before the first failed extension.  `response` is the
literal all-context target response of `X_π` in each labelled skeleton.
`jointStates U` is the set `𝒮(U)` realized in that conditional fibre.

The final fields identify the entire canonical prefix through the first failed
extension and certify that this prefix is a genuine obstruction in the exact
skeleton-response model.  They are data of the current residual rather than a
second history or transport channel; the only owner of a value of this
structure is the sealed node-`[178]` fact row. -/
structure PairOverlapSystem (data : Parameters)
    (object : Graph.FiniteObject.{u}) where
  first : PairOverlapFirstFailure data object
  responseSupport :
    {pair // pair ∈ first.pairSet} → Finset object.Vertex
  responseSupport_selected : ∀ pair,
    (Graph.pairResponseActivation first.active).pairSupport pair.1 =
      some (responseSupport pair)
  responseSupport_connected : ∀ pair,
    Graph.SupportComponents.Connected.ConnectedOn object (responseSupport pair)
  rank : {pair // pair ∈ first.pairSet} → Nat
  rank_injective : Function.Injective rank
  failedFamily : Finset {pair // pair ∈ first.pairSet}
  failedFamily_eq :
    failedFamily = Finset.univ.filter fun pair =>
      rank pair < first.firstFailure.index + 1
  failedFamily_nonempty : failedFamily.Nonempty
  failedFamily_obstruction :
    let model : Graph.SparsePairSkeletonModel
        (Graph.pairResponseActivation first.active)
        (object.portPairSchedule data.threshold) :=
      { BaseCoordinate := first.Coordinate
        baselineFamily := first.baselineFamily
        baseline := first.baselineRealization
        pairSet := first.pairSet
        pairSet_nonempty := first.pairSet_nonempty
        pairSet_subset_schedule := first.pairSet_subset_schedule
        responseSupport := responseSupport
        responseSupport_selected := responseSupport_selected
        responseSupport_connected := responseSupport_connected }
    failedFamily.Nonempty ∧
      ¬ model.RealizingOrder (LengthOK := data.LengthOK) failedFamily

namespace PairOverlapSystem

/-- Forget only the first-failure bookkeeping and expose the graph layer's
single exact skeleton-response model.  The baseline realization, pair set and
canonical supports are the same data, not copied witnesses. -/
def toSkeletonModel {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) :
    Graph.SparsePairSkeletonModel
      (Graph.pairResponseActivation system.first.active)
      (object.portPairSchedule data.threshold) where
  BaseCoordinate := system.first.Coordinate
  baselineFamily := system.first.baselineFamily
  baseline := system.first.baselineRealization
  pairSet := system.first.pairSet
  pairSet_nonempty := system.first.pairSet_nonempty
  pairSet_subset_schedule := system.first.pairSet_subset_schedule
  responseSupport := system.responseSupport
  responseSupport_selected := system.responseSupport_selected
  responseSupport_connected := system.responseSupport_connected

end PairOverlapSystem

namespace PairOverlapSystem

/-- The fixed-edge labelled skeleton carrier on which the pair-response code is
actually read.  Keeping this abbreviation attached to the overlap system makes
the distinction between an abstract quotient realization and a graph in the
current `(n,m)` slice explicit. -/
abbrev Skeleton {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) :=
  system.toSkeletonModel.Skeleton

noncomputable def response {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) (member : system.Skeleton)
    (pair : {pair // pair ∈ system.first.pairSet}) : PairResponseState data :=
  system.toSkeletonModel.response (LengthOK := data.LengthOK) member pair

noncomputable def outsideCode {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) (member : system.Skeleton) :=
  system.toSkeletonModel.outsideCode member

def conditionalFibre {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) (reference : system.Skeleton) :
    Set system.Skeleton :=
  system.toSkeletonModel.conditionalFibre reference

def conditionalValues {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (family : Finset {pair // pair ∈ system.first.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (reference : system.Skeleton) (index : Fin family.card) :
    Set (PairResponseState data) :=
  system.toSkeletonModel.conditionalValues (LengthOK := data.LengthOK)
    family order reference index

def realizingOrder {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (family : Finset {pair // pair ∈ system.first.pairSet}) : Prop :=
  system.toSkeletonModel.RealizingOrder (LengthOK := data.LengthOK) family

def obstruction {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (family : Finset {pair // pair ∈ system.first.pairSet}) : Prop :=
  family.Nonempty ∧ ¬ system.realizingOrder family

def minimalObstruction {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (family : Finset {pair // pair ∈ system.first.pairSet}) : Prop :=
  system.obstruction family ∧
    ∀ proper, proper ⊂ family → proper.Nonempty →
      system.realizingOrder proper

def overlaps {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (left right : {pair // pair ∈ system.first.pairSet}) : Prop :=
  system.toSkeletonModel.Overlaps left right

noncomputable def overlapSupport {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (family : Finset {pair // pair ∈ system.first.pairSet}) :
    Finset object.Vertex :=
  system.toSkeletonModel.responseSupportUnion family

/-- A relevant conditional skeleton fibre after a finite set of pair
coordinates has already been exposed.  The candidate must remain in the
system's literal baseline/outside fibre and must agree with the reference
skeleton on every exposed exact response. -/
def refinedFibre {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (exposed : Finset {pair // pair ∈ system.first.pairSet})
    (reference : system.Skeleton) : Set system.Skeleton :=
  {candidate | candidate ∈ system.conditionalFibre reference ∧
    ∀ pair, pair ∈ exposed →
      system.response candidate pair = system.response reference pair}

/-- The exact response values of one pair coordinate that are graph-realized
in a relevant conditional fibre.  This is a range of actual fixed-`(n,m)`
skeletons, not the label set of a rank quotient. -/
def fibreValues {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (exposed : Finset {pair // pair ∈ system.first.pairSet})
    (reference : system.Skeleton)
    (pair : {pair // pair ∈ system.first.pairSet}) :
    Set (PairResponseState data) :=
  {state | ∃ candidate, candidate ∈ system.refinedFibre exposed reference ∧
    system.response candidate pair = state}

/-- The manuscript's geometric separation condition for a family of pair
coordinates: no two distinct members meet outside the port-return supports of
their own demands. -/
def PairwiseSeparated {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (family : Finset {pair // pair ∈ system.first.pairSet}) : Prop :=
  system.toSkeletonModel.PairwiseSeparated family

noncomputable def familyUnion {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object)
    (left right : Finset {pair // pair ∈ system.first.pairSet}) :
    Finset {pair // pair ∈ system.first.pairSet} :=
  system.toSkeletonModel.familyUnion left right

/-- The skeleton-response realization statement used by
`lem:pair-failure-overlap`.

The first clause is the paper's product-code assertion for a family whose
response supports are pairwise separated.  The second is its componentwise
form: if a family is split into two nonempty blocks with no cross-overlap, an
admissible exposure order in each block concatenates to one for their union.
Both clauses speak through `realizingOrder`, hence through existential witnesses
in the literal fixed-`(n,m)` skeleton fibre.  They do not replace graph
realization by rank-label injectivity. -/
abbrev ConditionalFactorization {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) : Prop :=
  system.toSkeletonModel.ConditionalFactorization
    (LengthOK := data.LengthOK)

end PairOverlapSystem

/-- **`lem:pair-failure-overlap`, node `[178]`.**

The retained numerical first failure is converted into a deficient exact
response family, minimized by inclusion.  Conditional factorization rules out
disjoint components, so the union of the selected canonical response supports
is connected. -/
structure PairFailureOverlap (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type (u + 1) where
  system : PairOverlapSystem data object
  family : Finset {pair // pair ∈ system.first.pairSet}
  factorization : system.ConditionalFactorization
  minimal : system.minimalObstruction family
  overlapWitness : ∃ left ∈ family, ∃ right ∈ family,
    left ≠ right ∧ system.toSkeletonModel.Overlaps left right
  connected : Graph.SupportComponents.Connected.ConnectedOn object
    (system.overlapSupport family)

/-! ## Node `[179]`: the two canonical closing returns -/
/-- The two active demands of the selected pair obstruction, together with the
literal canonical return paths already determined by the node-`[129]` active
family.  `returnBound` is the paper's local `ℓ_ret`: the maximum of those two
derived lengths, not a numerical parameter supplied by Assembly. -/
structure PairDemandReturns (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type (u + 1) where
  overlap : PairFailureOverlap data object
  leftDemand : object.Vertex × object.Vertex
  rightDemand : object.Vertex × object.Vertex
  demands_ne : leftDemand ≠ rightDemand
  pair_eq : overlap.system.first.firstFailure.pair =
    PairOverlapFirstFailure.demandPair object leftDemand rightDemand
  left_active : leftDemand ∈ object.excessPorts data.threshold
  right_active : rightDemand ∈ object.excessPorts data.threshold
  returnBound : Nat
  returnBound_eq : returnBound = max
    (overlap.system.first.active.canonicalPairReturnPath
      leftDemand left_active).length
    (overlap.system.first.active.canonicalPairReturnPath
      rightDemand right_active).length

namespace PairDemandReturns

/-- Construct the two closing returns only from the selected `[178]` fact.
Every ingredient is recovered from the failed pair's schedule membership. -/
noncomputable def of
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (overlap : PairFailureOverlap data object) :
    PairDemandReturns data object := by
  classical
  letI := object.vertexPairDecidableEq
  let first := overlap.system.first
  let demandWitness := first.exists_failedPair_demands
  let left := Classical.choose demandWitness
  let rightWitness := Classical.choose_spec demandWitness
  let right := Classical.choose rightWitness
  let demandFacts := Classical.choose_spec rightWitness
  have different : left ≠ right := demandFacts.1
  have pairEq : first.firstFailure.pair =
      PairOverlapFirstFailure.demandPair object left right := demandFacts.2
  have pairMem := first.failedPair_mem_portPairSchedule
  have pairActive :=
    object.subset_excessPorts_of_mem_portPairSchedule data.threshold pairMem
  have leftMem : left ∈ object.excessPorts data.threshold := by
    apply pairActive
    rw [pairEq]
    simp [PairOverlapFirstFailure.demandPair]
  have rightMem : right ∈ object.excessPorts data.threshold := by
    apply pairActive
    rw [pairEq]
    simp [PairOverlapFirstFailure.demandPair]
  exact
    { overlap := overlap
      leftDemand := left
      rightDemand := right
      demands_ne := different
      pair_eq := pairEq
      left_active := leftMem
      right_active := rightMem
      returnBound := max
        (first.active.canonicalPairReturnPath left leftMem).length
        (first.active.canonicalPairReturnPath right rightMem).length
      returnBound_eq := rfl }

/-- The first canonical closing return is bounded by the registered local
`ℓ_ret`. -/
theorem leftReturn_length_le
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    (returns.overlap.system.first.active.canonicalPairReturnPath
      returns.leftDemand returns.left_active).length ≤ returns.returnBound := by
  rw [returns.returnBound_eq]
  exact Nat.le_max_left _ _

/-- The second canonical closing return is bounded by the same `ℓ_ret`. -/
theorem rightReturn_length_le
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    (returns.overlap.system.first.active.canonicalPairReturnPath
      returns.rightDemand returns.right_active).length ≤ returns.returnBound := by
  rw [returns.returnBound_eq]
  exact Nat.le_max_right _ _

/-- The local return bound itself is graph-derived and remains below the order
of the active finite object. -/
theorem returnBound_lt_vertexCount
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    returns.returnBound < object.vertexCount := by
  rw [returns.returnBound_eq, max_lt_iff]
  exact ⟨
    returns.overlap.system.first.active.canonicalPairReturnPath_length_lt
      returns.leftDemand returns.left_active,
    returns.overlap.system.first.active.canonicalPairReturnPath_length_lt
      returns.rightDemand returns.right_active⟩

/-- The first selected demand is its literal port edge in the active object. -/
theorem leftDemand_adj
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    object.graph.Adj returns.leftDemand.1 returns.leftDemand.2 :=
  object.adj_of_mem_excessPorts returns.left_active

/-- The second selected demand is likewise its literal port edge. -/
theorem rightDemand_adj
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    object.graph.Adj returns.rightDemand.1 returns.rightDemand.2 :=
  object.adj_of_mem_excessPorts returns.right_active

/-- Both endpoints of both selected demands lie on the connected
`X_π ∪ R_p ∪ R_q` support from which `[179]` performs its uncrossing. -/
theorem demandEnds_mem_connector
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) :
    returns.leftDemand.1 ∈
        returns.overlap.system.first.failedPairConnector ∧
      returns.leftDemand.2 ∈
        returns.overlap.system.first.failedPairConnector ∧
      returns.rightDemand.1 ∈
        returns.overlap.system.first.failedPairConnector ∧
      returns.rightDemand.2 ∈
        returns.overlap.system.first.failedPairConnector := by
  classical
  let first := returns.overlap.system.first
  have leftPair : returns.leftDemand ∈ first.firstFailure.pair := by
    rw [returns.pair_eq]
    simp [PairOverlapFirstFailure.demandPair]
  have rightPair : returns.rightDemand ∈ first.firstFailure.pair := by
    rw [returns.pair_eq]
    simp [PairOverlapFirstFailure.demandPair]
  have putReturn (demand : object.Vertex × object.Vertex)
      (pairMember : demand ∈ first.firstFailure.pair)
      {vertex : object.Vertex}
      (returnMember : vertex ∈
        (Graph.pairResponseActivation first.active).returnSupport demand) :
      vertex ∈ first.failedPairConnector := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨demand, pairMember, returnMember⟩
  exact ⟨
    putReturn returns.leftDemand leftPair
      (Graph.pairResponseActivation_centre_mem_returnSupport_of_mem
        first.active returns.left_active),
    putReturn returns.leftDemand leftPair
      (Graph.pairResponseActivation_endpoint_mem_returnSupport_of_mem
        first.active returns.left_active),
    putReturn returns.rightDemand rightPair
      (Graph.pairResponseActivation_centre_mem_returnSupport_of_mem
        first.active returns.right_active),
    putReturn returns.rightDemand rightPair
      (Graph.pairResponseActivation_endpoint_mem_returnSupport_of_mem
        first.active returns.right_active)⟩

/-- The two oppositely oriented connector routes used by the manuscript's
first/last-common-vertex uncrossing.  They are selected from the already proved
connected connector; no path is supplied by a caller. -/
structure ConnectorRoutes
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) where
  forward : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1
  backward : object.graph.Walk returns.rightDemand.2 returns.leftDemand.1
  forward_isPath : forward.IsPath
  backward_isPath : backward.IsPath
  forward_inside : ∀ vertex ∈ forward.support,
    vertex ∈ returns.overlap.system.first.failedPairConnector
  backward_inside : ∀ vertex ∈ backward.support,
    vertex ∈ returns.overlap.system.first.failedPairConnector

/-- Select the two literal paths from connector connectedness. -/
noncomputable def connectorRoutes
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) : ConnectorRoutes returns := by
  let connected :=
    returns.overlap.system.first.failedPairConnector_connectedOn
  let ends := returns.demandEnds_mem_connector
  let forwardWitness := connected.2 ends.2.1 ends.2.2.1
  let forward := Classical.choose forwardWitness
  let forwardFacts := Classical.choose_spec forwardWitness
  let backwardWitness := connected.2 ends.2.2.2 ends.1
  let backward := Classical.choose backwardWitness
  let backwardFacts := Classical.choose_spec backwardWitness
  exact
    { forward := forward
      backward := backward
      forward_isPath := forwardFacts.1
      backward_isPath := backwardFacts.1
      forward_inside := forwardFacts.2
      backward_inside := backwardFacts.2 }

/-- The paper's derived pair-system increment cap
`D_sp = 2 M_cold + 2 ℓ_ret`. -/
noncomputable def systemBound
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    (returns : PairDemandReturns data object) : Nat :=
  2 * Graph.ColdCorridor.exchangeBound data.coldSignature +
    2 * returns.returnBound

end PairDemandReturns

/-! ## Nodes `[179]`--`[180]`: exact serial realization and arithmetic -/
/-- An actual simple cycle of the retained object with an exact numerical
length.  This is the realization predicate used by the serial-system API; it
does not identify an abstract sumset element with a graph cycle. -/
structure PairSerialCycle (object : Graph.FiniteObject.{u})
    (length : Nat) : Type u where
  vertex : object.Vertex
  walk : object.graph.Walk vertex vertex
  isCycle : walk.IsCycle
  length_eq : walk.length = length

def PairSerialRealized (object : Graph.FiniteObject.{u})
    (length : Nat) : Prop :=
  Nonempty (PairSerialCycle object length)

/-- Alternative (v) of `lem:pair-system-realizability` on the literal
node-`[178]` obstruction.  The interfaces, corridor paths, disjoint-interior
conditions, two canonical closing returns, bounded increments, and the actual
cycle produced by every choice are all recorded.  The numerical `System`
consumed at `[180]` is derived from these graph objects below. -/
structure PairSerialDemandSystem (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type (u + 1) where
  returns : PairDemandReturns data object
  cells : Nat
  cells_pos : 0 < cells
  interfaces : Fin (cells + 1) → object.Vertex
  lengths : Fin cells → Finset Nat
  lengths_nonempty : ∀ index, (lengths index).Nonempty
  piece : ∀ index length, length ∈ lengths index →
    object.graph.Walk (interfaces index.castSucc) (interfaces index.succ)
  piece_isPath : ∀ index length member, (piece index length member).IsPath
  piece_length : ∀ index length member,
    (piece index length member).length = length
  piece_inside : ∀ index length member vertex,
    vertex ∈ (piece index length member).support →
      vertex ∈ returns.overlap.system.overlapSupport returns.overlap.family
  cell_internal_disjoint : ∀ index left leftMem right rightMem,
    left ≠ right → ∀ vertex,
      vertex ∈ (piece index left leftMem).support →
      vertex ∈ (piece index right rightMem).support →
      vertex = interfaces index.castSucc ∨ vertex = interfaces index.succ
  cells_internal_disjoint : ∀ leftIndex rightIndex,
    leftIndex ≠ rightIndex → ∀ left leftMem right rightMem vertex,
      vertex ∈ (piece leftIndex left leftMem).support →
      vertex ∈ (piece rightIndex right rightMem).support →
      (vertex = interfaces leftIndex.castSucc ∨
        vertex = interfaces leftIndex.succ) ∧
      (vertex = interfaces rightIndex.castSucc ∨
        vertex = interfaces rightIndex.succ)
  routes : PairDemandReturns.ConnectorRoutes returns
  start_eq : interfaces ⟨0, Nat.succ_pos cells⟩ = returns.leftDemand.2
  end_eq : interfaces (Fin.last cells) = returns.rightDemand.1
  closing : Nat
  closing_eq : closing = routes.backward.length + 2
  closing_internal_disjoint : ∀ index length member vertex,
    vertex ∈ routes.backward.support →
      vertex ∈ (piece index length member).support → False
  offsets : Finset Nat
  offsets_nonempty : offsets.Nonempty
  increments_bounded : ∀ index left, left ∈ lengths index →
    ∀ right, right ∈ lengths index →
      Nat.dist left right ≤ PairDemandReturns.systemBound returns
  realized_route : ∀ choice : Fin cells → Nat,
    (∀ index, choice index ∈ lengths index) →
      ∀ offset ∈ offsets,
        PairSerialRealized object
          (closing + (∑ index, choice index) + offset)

namespace PairSerialDemandSystem

/-- Forget only the graph-path presentation after it has proved the exact
`realized_route` contract.  This is the canonical input expected by
`Graph.SerialSystem.System.spectrum`; no parallel length carrier is built. -/
noncomputable def toSystem {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (serial : PairSerialDemandSystem data object) :
    Graph.SerialSystem.System serial.cells where
  lengths := serial.lengths
  closing := serial.closing
  offsets := serial.offsets
  Realized := PairSerialRealized object
  realized_route := serial.realized_route

end PairSerialDemandSystem

/-! ## Key statements

The statement each vocabulary key of this family publishes, stated over the
registered parameters and the selected object. -/

/-- Node `[126]`, `lem:sparse-slack-surplus`: the sparse slack identity
`m = (3/2)n + (1/2)σ(G)`, cleared of division at the registered baseline. -/
noncomputable abbrev SparseSlackSurplusStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:sparse-slack-surplus`: `2m = δn + σ(G)`, the manuscript's
  -- `m = (3/2)n + (1/2)σ(G)` cleared of division.
  (2 * object.edgeCount =
    data.threshold * object.vertexCount +
      object.degreeSurplus data.threshold)

/-- Node `[127]`, `lem:sparse-excess-port-extraction`, with the family half of
`lem:surviving-active-family`: the excess selector `𝒫_exc` has exactly `σ(G)`
members, every selected port has a centre strictly above the baseline and an
endpoint exactly at it, and therefore carries exactly `δ − 1` shoulders. -/
noncomputable abbrev ActiveSurplusFamilyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:sparse-excess-port-extraction`, and the family statement of
  -- `lem:surviving-active-family`.
  ((object.excessPorts data.threshold).card =
      object.degreeSurplus data.threshold ∧
    ∀ pair : object.Vertex × object.Vertex,
      ∀ member : pair ∈ object.excessPorts data.threshold,
        data.threshold < object.degree pair.1 ∧
          object.degree pair.2 = data.threshold ∧
          (object.surplusPortOfMem member).shoulders.card =
            data.threshold - 1)

/-- Node `[128]`, `lem:sparse-port-activation`, clauses (a)--(d): at a
selected port carrying a shoulder pair, the port carries the return path
`R_p ⊆ G − c(p)x(p)` whose first edge after `x(p)` is a shoulder, an open port
carries the suppression witness `Q_p ⊆ G − x(p)` whose restored length is
accepted, and a triangular port carries the triangle `x a_p b_p x`. -/
noncomputable abbrev SparsePortActivationStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:sparse-port-activation`, clauses (a)--(d).
  (∀ pair : object.Vertex × object.Vertex,
    ∀ member : pair ∈ object.excessPorts data.threshold,
      ∀ left right : object.Vertex,
        (∀ vertex : object.Vertex,
          vertex ∈ (object.surplusPortOfMem member).shoulders ↔
            (vertex = left ∨ vertex = right)) →
        left ≠ right →
        Nonempty (Graph.FiniteObject.SurplusPort.PortReturn
            object pair.1 pair.2 left right) ∧
          (¬ object.graph.Adj left right →
            Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness
              object data.LengthOK pair.2 left right)) ∧
          (object.graph.Adj left right →
            object.graph.Adj pair.2 left ∧
              object.graph.Adj left right ∧
              object.graph.Adj right pair.2))

/-- Node `[129]`, `def:baseline-spine-demand` with
`lem:exact-cubic-baseline-budget`, `lem:incremental-skeleton-room` and
`def:spine-lower-bound-deficits`: the common cubic baseline `B₀(n)` the later
surplus accounting is measured against, evaluated in both directions; the room
an edge count above the cubic one buys over it; the definition itself, at
every declared target coordinate family the branch may present, with the
deficit `E_spine(n)` as this node's own output; and the ordering of the three
lower-bound packages that supply it.  Every display is committed with the
logarithms cleared. -/
noncomputable abbrev BaselineSpineDemandStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[129]`, exactly `def:baseline-spine-demand`, at G's canonical
  -- spine family: the `Classical.choose` of this node's own `∃`-body, so
  -- every later key speaks about the family this node exhibits.
  ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
    BaselineSpineFamilySpec data object spine.Coordinate spine.family
      spine.coordinateSupport

/-- Nodes `[130]`--`[134]`, `def:sparse-pair-response`'s pair schedule with
`def:canonical-blocker-ledger` and
`lem:canonical-blocker-ledger-no-overcount`: `Π(𝒜₀)` has `C(σ(G),2)` members,
and at every reading of the closed clause list of `def:surplus-blockers` the
canonical charge is single-valued, so `Π_blk` and `Π_free` exhaust the
schedule and `|Π_blk| = Σ_B μ(B)`. -/
noncomputable abbrev CanonicalPairLedgerStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ activation, canonicalPairActivation data object = some activation ∧
    Graph.HasSparsePairDEBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation
        (object.portPairSchedule data.threshold) ∧
    let pairs := object.portPairSchedule data.threshold
    pairs.card = (object.degreeSurplus data.threshold).choose 2 ∧
      let recorded := Graph.recordSparsePairDEBlockers
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) activation pairs
      (recorded.blockedPairs data.threshold).card +
            (recorded.unblockedPairs data.threshold).card = pairs.card ∧
        (recorded.canonicalIncidenceLedger data.threshold).card =
          (recorded.blockedPairs data.threshold).card ∧
        (recorded.blockedPairs data.threshold).card =
          (recorded.canonicalBlockerSet data.threshold).sum
            (recorded.blockerMultiplicity data.threshold) ∧
        ∃ pair ∈ pairs, (recorded.blockers pair).Nonempty

/-- Node `[132]`, exit arm of `lem:sparse-pair-dependence-exit`: the
dependence of a blocked pair's response coordinates is settled by a sparse
surplus exit of `def:named-surplus-exits` rather than by a canonical blocker.
It closes the branch against node `[125]`'s survivor entry at `[133]`. -/
noncomputable abbrev SparsePairExitStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  DeclaredSparseSurplusExit data object

/-- Node `[125]`, the sole nonterminal named-exit payload: clause (b) of
`def:named-surplus-exits` at G's declared sparse family
(`lem:context-universality`, tex 6106-6112) -- two distinct declared
coordinates of G, read on G's own piece at their canonical connected support,
agree in G's actual outside context and are separated by another boundaried
context. -/
noncomputable abbrev SparseTargetDefectResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
    (sparseDeclaredFamily data object) (sparseDeclaredSupport data object)

/-- Node `[20]`: the same target-defective identification of two declared
coordinates of G, with the bound target-defect geometry of its two readings on
G's piece at their canonical support. -/
noncomputable abbrev SparseTargetDefectStructureStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop := by
  classical
  exact ∃ first ∈ sparseDeclaredFamily data object,
    ∃ second ∈ sparseDeclaredFamily data object, first ≠ second ∧
      ∃ support : Finset object.Vertex,
        Graph.CanonicalSupport.select? object
            (sparseDeclaredSupport data object first ∪
              sparseDeclaredSupport data object second) = some support ∧
        Graph.BoundTargetDefectGeometry object support data.LengthOK
          (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
            support (sparseDeclaredSupport data object first))
          (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
            support (sparseDeclaredSupport data object second))

/-- Node `[132]`, blocker arm of `lem:sparse-pair-dependence-exit` with
`lem:mixed-sparse-spine-dependence` and
`prop:sparse-pair-independence-dichotomy`: no sparse surplus exit settles the
dependence, so at an object admitting no proper-support replacement a
rank-reducing attempted determination exhibits the blocker of type (d) or (e)
as concrete separated realizations, and the declared family attains full
target rank.  This is the arm the canonical blocker ledger `[134]` is
levied on. -/
noncomputable abbrev CanonicalBlockerRouteStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[132]`, blocker arm: G survives the sparse exits of its declared
  -- family, and at G's canonical activation the blocked pair of `[130]` has
  -- its canonical blocker `Φ_can(π) = min_≺ Blk(π)` of
  -- `def:canonical-blocker-ledger`.
  DeclaredSparseSurvivor data object ∧
    ∃ activation, canonicalPairActivation data object = some activation ∧
      Graph.HasSparsePairDEBlocker
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) activation
          (object.portPairSchedule data.threshold) ∧
      let recorded := Graph.recordSparsePairDEBlockers
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) activation
        (object.portPairSchedule data.threshold)
      ∃ pair ∈ object.portPairSchedule data.threshold,
        (recorded.blockers pair).Nonempty ∧
          ∃ blocker, Graph.FiniteObject.canonicalBlocker recorded pair =
            some blocker

/-- Node `[130]`, blocked/dependent arm
(`prop:sparse-pair-independence-dichotomy`, tex 4721): at G's canonical
pair-response activation (node `[125]`), the full schedule `Π(𝒜₀)` carries a
clause-(d)/(e) blocker of `def:surplus-blockers`. -/
noncomputable abbrev DependentPairFamilyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[130]`, no: at G's canonical activation, one pair of the full
  -- schedule carries a literal clause-(d)/(e) obstruction.
  ∃ activation, canonicalPairActivation data object = some activation ∧
    Graph.HasSparsePairDEBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation
        (object.portPairSchedule data.threshold)

/-- Node `[130]`, independent arm: at the same canonical activation of G, the
full schedule carries no clause-(d)/(e) blocker -- the exact complement of the
dependent arm about the one pair-response family `ℛ_Π` of G. -/
noncomputable abbrev IndependentPairFamilyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[130]`, yes: the same activation, and no blocker on the schedule.
  ∃ activation, canonicalPairActivation data object = some activation ∧
    ¬ Graph.HasSparsePairDEBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation
        (object.portPairSchedule data.threshold)

/-- Node `[131]`, `lem:mixed-sparse-spine-dependence` (tex 4872), on G's
canonical baseline spine family (node `[129]`) and G's full pair-response
schedule at its canonical activation (node `[125]`). -/
noncomputable abbrev MixedSparseSpineDependenceStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  by
  classical
  exact ∃ activation, canonicalPairActivation data object = some activation ∧
    ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
      let pairs := object.portPairSchedule data.threshold
      let pairFamily := activation.pairFamily pairs
      let mixedFamily : Finset (Sum spine.Coordinate object.PairCoordinate) :=
        spine.family.image Sum.inl ∪ pairFamily.image Sum.inr
      let mixedSupport : Sum spine.Coordinate object.PairCoordinate →
          Finset object.Vertex :=
        Sum.elim spine.coordinateSupport (by
          letI := object.vertices.decEq
          exact Graph.DeclaredSignature.Coordinate.support)
      -- `lem:mixed-sparse-spine-dependence`: if the union of G's spine
      -- family and G's pair-response family does not survive the admissible
      -- quotient system, a sparse exit of G's declared family occurs, or a
      -- scheduled pair carries a blocker of type (d)/(e): two of the mixed
      -- coordinates read on G's own piece at their canonical support are
      -- profile-separated or target-defective, or the attempted
      -- determination's support admits a target-complete replacement.
      (¬ ∀ declared : Graph.DeclaredQuotient
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          mixedFamily mixedSupport,
          declared.toRankQuotient.FunctionalOn ↑mixedFamily →
            Set.InjOn declared.label ↑mixedFamily) →
        DeclaredSparseSurplusExit data object ∨
          ∃ pair ∈ pairs,
            ∃ attempt : Graph.AttemptedQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object
                mixedFamily mixedSupport,
              (Graph.ResidualProfileSeparation object mixedFamily mixedSupport ∨
                Graph.ResidualTargetDefect
                  (Graph.HasCycleWithLength data.LengthOK) object
                  mixedFamily mixedSupport ∨
                Graph.Strategy.InterfaceReplacement.ReplacementSupport
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object
                  attempt.support)

/-- Node `[131]`, the two-sided exact cubic baseline budget at the current
residual's order and registered baseline. -/
noncomputable abbrev ExactCubicBaselineBudgetStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
      (2 * object.vertexCount) ^
        Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ∧
    (2 * Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
        object.vertexCount.choose 2 →
      (object.vertexCount - 1) ^
          Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
        Graph.cubicBaselineBudget object.vertexCount data.threshold *
          (2 * (data.threshold + 1)) ^
            Graph.cubicBaselineEdgeCount object.vertexCount data.threshold)

/-- Node `[131]`, the incremental skeleton room above the exact cubic
baseline and its surplus-slack bound. -/
noncomputable abbrev IncrementalSkeletonRoomStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.skeletonBudget object ≤
      Graph.cubicBaselineBudget object.vertexCount data.threshold *
        object.vertexCount ^
          (object.edgeCount -
            Graph.cubicBaselineEdgeCount object.vertexCount data.threshold) ∧
    2 * (object.edgeCount -
          Graph.cubicBaselineEdgeCount object.vertexCount data.threshold) ≤
      object.degreeSurplus data.threshold + 2

/-- `lem:skeleton-dominates` at the current residual's exact order and edge
count: the fixed-edge labelled skeleton class has exactly the registered
skeleton budget, and every canonical state map realizes at most that many
states. -/
noncomputable abbrev SkeletonDominatesStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Nat.card (Graph.PackedWindowRealization.Skeleton
      object.vertexCount object.edgeCount) = Graph.skeletonBudget object ∧
    ∀ (State : Type u)
      (stateOf : Graph.PackedWindowRealization.Skeleton
        object.vertexCount object.edgeCount → State),
      Nat.card (Set.range stateOf) ≤ Graph.skeletonBudget object

/-- `lem:sparse-upper-envelope`: `m + 2 ≤ (δ − 1)·n`, the manuscript's
`m ≤ 2n − 2` at its own `δ = 3`.  It is `lem:no-proper-core`'s degeneracy --
every proper subgraph misses the baseline, so the object less a vertex sitting
exactly at the baseline is `(δ − 1)`-degenerate -- spent against
`lem:deletion-critical`'s tight endpoint. -/
noncomputable abbrev SparseUpperEnvelopeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount) ∧
    let packing := canonicalWindowPacking data object
    (object.windowRemainderIncidences packing).card +
        (2 * (data.windowOrder - 1) * packing.card +
          (object.crossWindowIncidences packing).card) =
      data.threshold * (data.windowOrder * packing.card) +
        object.ambientSurplus (object.windowSupport packing) data.threshold

/-- `D_all` of a certified capacity-token ledger at the geometric caps
(`prop:single-graph-sparse-pressure-routing`). -/
noncomputable abbrev sparseCoupledExcess (data : Parameters)
    {object : Graph.FiniteObject.{u}} {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) : Nat :=
  certified.ledger.presented.coupledExcess certified.ledger.presented.tokenClass
    fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound

/-- Nodes `[134]`--`[136]`, `def:primitive-sparse-blocker-carrier` with
`lem:primitive-carrier-supply`, `def:capacity-token-ledger` with
`lem:capacity-token-supply` and `lem:token-ledger-no-overcount`, and
`def:same-token-patterns`: `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 3(δ−1)n`, the
manuscript's `≤ 6n`, spent against the sparse upper envelope the same node
proves; the three-summand token universe `𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W` with
`|𝔗_cap| = |𝔘_sp(G)| + 15p₁₃ + σ(G)` and `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, the
manuscript's `≤ 8n + σ(G)`, both unconditional; the four-case charge `Θ_cap`
landing in `𝔗_cap` with its fibre identity `|Π_blk| = Σ_t ℓ_cap(t)` read at the
whole blocked family; the fibre graph `H_t` with `e(H_t) = ℓ_cap(t)`; and the
existence of the object's capacity-token ledger at every declared
presentation. -/
noncomputable abbrev CapacityTokenLedgerStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The node-`[136]` presentation `𝔗_cap` of G: activation, carrier and the
  -- node-`[19]` packing, with every accounting identity proved there.
  ∃ capacity, canonicalCapacity data object = some capacity ∧
    CapacityLedgerSpec data object capacity

/-- Node `[137]`, `lem:exact-surplus-pair-charge-partition` with
`thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c): at the object's capacity-token
ledger, `C(𝒜₀,2)` decomposes exactly into `Π_free` and the class/token/role
fibres, the class and subtype loads sum to `|Π_blk| ≥ N_*(G)`, their supplies
sum to `|𝔗_cap|`, and a class with no role-homogeneous `L`-pattern is capped
by `Cap_hom(L)S_C`. -/
noncomputable abbrev RoleFibrePartitionSchema
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:exact-surplus-pair-charge-partition` with the classwise and
  -- subtype budgets, at G's canonical certified capacity-token ledger.
  ∃ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
    CertifiedLedgerSpec data object capacity certified

/-- Nodes `[137]`--`[143]`, `lem:capacity-token-high-load` with
`cor:forced-homogeneous-same-token-scale`,
`thm:sharp-classwise-homogeneous-token-budget` (e) and
`thm:sharp-surplus-overload-audit` (d): the object's *own* capacity-token
ledger realizes the coupled high-load display `C(s,2) ≤ E + L_max|𝔗_cap|`, a
role fibre there carries at least a `Q_st`-th of the load and all of the
forced demand `N_*(G)` up to the token supply, and contains a matching or a
star of size `ψ` of its own count. -/
noncomputable abbrev FibrePressureSchema
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:capacity-token-high-load` at G's canonical certified ledger.
  ∃ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
    Graph.FibrePressureAt certified

/-- Node `[137]`, `cor:spine-lower-bound-surplus-estimates`: a lower-bound
package of `def:spine-lower-bound-deficits` that bounds the pair schedule
bounds the surplus, `σ(G) ≤ 1 + √(2 D_win)`.  This is what the near-cubic
route `[138]` carries away from the block. -/
noncomputable abbrev SpineSurplusEstimateStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The actual node-`[138]` conclusion, derived from the concrete
  -- node-`[129]` deficit and node-`[131]` entropy ledger.
  object.degreeSurplus data.threshold ≤
    data.spineScale * Core.ceilSqrt object.vertexCount

/-- Node `[137]`, overload arm of `prop:single-graph-sparse-pressure-routing`
(b): at G's canonical certified capacity-token ledger the coupled excess
`D_all` at the geometric caps is positive.  The overloading token and role are
then the canonical ones (`canonicalOverloadTokenAt`), which `[139]`--`[143]`
read. -/
noncomputable abbrev SparsePressureOverloadSchema
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `prop:single-graph-sparse-pressure-routing` (b): `D_all > 0` at G's
  -- canonical certified ledger.
  ∃ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
    0 < sparseCoupledExcess data certified

/-- Node `[137]`, no arm of the coupled test `D_all > 0?`
(`prop:single-graph-sparse-pressure-routing` (a)): the exact negation of the
overload arm -- G's canonical certified capacity-token ledger does not have
positive coupled excess.  Node `[138]` derives `σ(G) ≤ C_sp ⌈√n⌉` from it at
that ledger. -/
noncomputable abbrev SparsePressureNearCubicStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `prop:single-graph-sparse-pressure-routing` (a): `D_all = 0` at G's
  -- canonical certified ledger -- the literal complement of the overload arm.
  ∀ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ →
      ¬ 0 < sparseCoupledExcess data certified

/-- Node `[139]`, yes arm: the overloading token of node `[137]` (the canonical
overload of G) lies in `𝔗_W`, so the branch enters the window-incidence audit
`[140]`. -/
noncomputable abbrev WindowClassOverloadStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  canonicalOverloadClass data object = some .windowIncidence

/-- Node `[139]`, no arm: the same overloading token of G lies outside `𝔗_W`. -/
noncomputable abbrev WindowClassAbsentStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ value, canonicalOverloadClass data object = some value ∧
    value ≠ .windowIncidence

/-- Node `[141]`, yes arm: the overloading token of G lies in `𝔗_R`, so the
branch enters the remainder-surplus audit `[142]`. -/
noncomputable abbrev RemainderClassOverloadStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  canonicalOverloadClass data object = some .remainderSurplus

/-- Node `[141]`, no arm: the same overloading token of G lies outside `𝔗_R`. -/
noncomputable abbrev RemainderClassAbsentStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ value, canonicalOverloadClass data object = some value ∧
    value ≠ .remainderSurplus

/-- Node `[143]`'s entry: on the no arms of `[139]` and `[141]` the overloading
token of G lies in the primitive class `𝔗_prim`. -/
noncomputable abbrev PrimitiveClassOverloadStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  canonicalOverloadClass data object = some .primitiveCarrier

/-- Node `[144]`, the tested half of
`thm:homogeneous-overload-geometric-closure`: at G's canonical certified
capacity-token ledger no token supports a role-homogeneous same-token
`L_geom`-matching or `L_geom`-star, at the counted routing-label alphabet. -/
noncomputable abbrev HomogeneousCapsHoldStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The subbranch hypothesis of `thm:homogeneous-overload-geometric-closure`
  -- at G's canonical certified ledger.
  ∃ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
    Graph.HomogeneousCapsHoldAt certified.ledger
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
      (Graph.WindowCurvature.Label data.windowOrder))

/-- Node `[144]`, the other arm: the exact complement of the fixed caps at the
same canonical ledger of G. -/
noncomputable abbrev HomogeneousCapsFailStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
    ¬ Graph.HomogeneousCapsHoldAt certified.ledger
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
      (Graph.WindowCurvature.Label data.windowOrder))

/-- Nodes `[140]`, `[142]`, `[143]`, the geometric audit of the overloading
token of G: its role fibre carries the canonical role-homogeneous same-token
`L_geom`-matching or `L_geom`-star, with every declared same-root connector
configuration.  `lem:same-token-bottleneck-routing` routes exactly this
pattern. -/
noncomputable abbrev HomogeneousBottleneckPatternSchema
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Nodes `[140]`, `[142]`, `[143]`: the canonical homogeneous pattern at the
  -- canonical overloading token and role of G.
  ∃ overload pattern, canonicalOverload data object = some overload ∧
    canonicalHomogeneousPatternAt data object overload.1.2 overload.2.1
      overload.2.2 = some pattern ∧
    HomogeneousPatternSpec data object overload.1.2 overload.2.1 overload.2.2
      pattern

/-- Node `[144]`, `cor:homogeneous-same-token-caps-close` at the counted
`L_geom` and at G's canonical certified ledger: every token load is at most
`M₀ = Cap_hom(L_geom)`, hence `|Π_blk| ≤ M₀|𝔗_cap|`,
`σ(G) ≤ 1 + 2M₀ + √(2E + 2M₀·scale)`, and the edge-count half
`m = (3/2)n + O(√n)`. -/
noncomputable abbrev HomogeneousBottleneckStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `cor:homogeneous-same-token-caps-close` at G's canonical ledger.
  ∃ (capacity : SurplusCapacity data object)
      (certified : SurplusCertified data object capacity),
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
    Graph.HomogeneousCapsCloseAt certified.ledger
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
      (Graph.WindowCurvature.Label data.windowOrder))

/-- Node `[125]`, `def:named-surplus-exits`: the selected object survives the
five sparse surplus exits.  This is the standing hypothesis every node of the
block reads, derived from the selection entry rather than assumed. -/
noncomputable abbrev SparseSurplusSurvivorStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:named-surplus-exits`: none of the five sparse-surplus conclusions
  -- occurs on this branch.
  DeclaredSparseSurvivor data object

/-- Node `[125]`, `def:active-surplus-demands` with
`lem:surviving-active-family`: the active family is the excess-port family,
it has `σ(G)` members, and every member carries its canonical return path. -/
noncomputable abbrev ActiveSurplusDemandsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:active-surplus-demands` with `lem:surviving-active-family`.
  Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
    data.threshold

/-! ### Exact negations of the family's branch tests

Each no-arm of a paper test is the literal negation of its yes-arm on the same
object.  What the paper derives on that arm is published by a separate row. -/

/-- Node `[132]`, blocker arm: no sparse surplus exit settles the dependence. -/
noncomputable abbrev BlockedPairNoExitStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ SparsePairExitStatement data object

end Hypostructure.Graph.Strategy.Spine
