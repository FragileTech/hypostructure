import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Classify the concrete overload witness already carried by the incoming
ledger according to whether its token lies in the window-incidence class. -/
noncomputable def windowOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .sparsePressureOverload) known]
    (windowFresh : K .windowClassOverload ∉ known)
    (outsideFresh : K .windowClassAbsent ∉ known) :
    Decision (K .windowClassOverload) (K .windowClassAbsent) previous :=
  Decision.run previous (K .windowClassOverload) (K .windowClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.windowOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .windowClassOverload).At current ⊕
          (K .windowClassAbsent).At current) from by
      obtain ⟨declared, ledger, routingLabelBound, token, role, tokenMem,
        _selected, rest⟩ := (previous.get (K .sparsePressureOverload)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence =>
          exact ⟨.inl ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, classified, rest⟩⟩
      | remainderSurplus =>
          exact ⟨.inr ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, by simpa [classified], rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, by simpa [classified], rest⟩⟩))
    windowFresh outsideFresh

/-- Node `[137]`, first production: `lem:exact-surplus-pair-charge-partition`
with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), read at the object's own
capacity-token ledger of node `[136]`.  Every pair of active demands is free or
lies in exactly one class/token/role fibre; the classwise and subtype budgets
are those fibres' own counts. -/
@[reducible] noncomputable def roleFibrePartitionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.roleFibrePartition
    { Requires := [K .capacityTokenLedger]
      Produces := [K .roleFibrePartition]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- Node `[137]` is entered only on the tokenized `[136]` residual; read
      -- that literal predecessor fact.
      let _ledger := inputs.get (K .capacityTokenLedger)
      .cons (key := K .roleFibrePartition)
        (show Value BranchState Presentation presentation data
            .roleFibrePartition inputs.current from
          ⟨Graph.roleFibrePartitionStatement inputs.current.object data.threshold
            data.windowOrder⟩)
        .nil)

@[reducible] noncomputable def pressureSpineSurplusEstimateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pressureSpineSurplusEstimate
    { Requires := [K .sparsePressureNearCubic]
      Produces := [K .spineSurplusEstimate]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .spineSurplusEstimate)
        (show Value BranchState Presentation presentation data
            .spineSurplusEstimate inputs.current from
          ⟨(inputs.get (K .sparsePressureNearCubic)).down⟩)
        .nil)

/-- Node `[140]`: the geometric audit of the concrete window-incidence class
selected by `[139]`.  The class fact fixes the routed arm; the audit itself is
the canonical counted-label theorem at the current object. -/
@[reducible] noncomputable def windowIncidenceAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowIncidenceAudit
    { Requires := [K .windowClassOverload]
      Produces := [K .windowIncidenceAudit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _selectedClass := inputs.get (K .windowClassOverload)
      .cons (key := K .windowIncidenceAudit)
        (show Value BranchState Presentation presentation data
            .windowIncidenceAudit inputs.current from
          ⟨Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder
            (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
              (Graph.WindowCurvature.Label data.windowOrder))
            .windowIncidence⟩)
        .nil)

/-- Node `[142]`: the geometric audit of the concrete remainder-surplus class
selected by `[141]`. -/
@[reducible] noncomputable def remainderSurplusAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderSurplusAudit
    { Requires := [K .remainderClassOverload]
      Produces := [K .remainderSurplusAudit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _selectedClass := inputs.get (K .remainderClassOverload)
      .cons (key := K .remainderSurplusAudit)
        (show Value BranchState Presentation presentation data
            .remainderSurplusAudit inputs.current from
          ⟨Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder
            (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
              (Graph.WindowCurvature.Label data.windowOrder))
            .remainderSurplus⟩)
        .nil)

/-- Node `[143]`: the geometric audit of the concrete primitive-carrier class
selected after the two negative class tests. -/
@[reducible] noncomputable def primitiveCarrierAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveCarrierAudit
    { Requires := [K .primitiveClassOverload]
      Produces := [K .primitiveCarrierAudit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _selectedClass := inputs.get (K .primitiveClassOverload)
      .cons (key := K .primitiveCarrierAudit)
        (show Value BranchState Presentation presentation data
            .primitiveCarrierAudit inputs.current from
          ⟨Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder
            (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
              (Graph.WindowCurvature.Label data.windowOrder))
            .primitiveCarrier⟩)
        .nil)

/-- Node `[143]`: normalize node `[141]`'s literal no-remainder residual to the
canonical primitive-class verdict consumed by the audit. -/
@[reducible] noncomputable def primitiveClassOverloadRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveClassOverload
    { Requires := [K .remainderClassAbsent]
      Produces := [K .primitiveClassOverload]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .primitiveClassOverload)
        ⟨(inputs.get (K .remainderClassAbsent)).down⟩ .nil)

/-- Node `[144]`, `cor:homogeneous-same-token-caps-close`: on the literal
fixed-caps residual, spend the already registered sparse slack identity and
publish the manuscript's homogeneous-cap closure statement. -/
@[reducible] noncomputable def homogeneousCapsCloseRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousCapsClose
    { Requires := [K .homogeneousCapsHold, K .sparseSlackSurplus]
      Produces := [K .homogeneousBottleneck]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .homogeneousBottleneck)
        (show Value BranchState Presentation presentation data
            .homogeneousBottleneck inputs.current from
          ⟨Graph.homogeneousCapsCloseStatement inputs.current.object
            (inputs.get (K .homogeneousCapsHold)).down
            (inputs.get (K .sparseSlackSurplus)).down⟩)
        .nil)

/-- Node `[125]`, `def:named-surplus-exits`: the selected minimal counterexample
survives the sparse surplus exits.  Each of the five conclusions is refuted
where the manuscript refutes it (`survivesSparseExits_of_selected`): (a) by the
selection's avoidance, (b) by `lem:context-universality`, (c) by
`lem:replacement`/`cor:uncompressible` (`K .replacementExclusion`), (d) by the
selection's minimality, (e) by `lem:suppressed-family-critical-cycle`.  The
row reads exactly the two facts it spends. -/
@[reducible] noncomputable def sparseSurplusSurvivorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivor
    { Requires := [K .selection, K .replacementExclusion]
      Produces := [K .sparseSurplusSurvivor]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let exclusion := (inputs.get (K .replacementExclusion)).down
      .cons (key := K .sparseSurplusSurvivor)
        (show Value BranchState Presentation presentation data
            .sparseSurplusSurvivor inputs.current from
          ⟨Graph.survivesSparseExits_of_selected selected.1
            (fun smaller lexSmaller baseline => selected.2 smaller lexSmaller baseline)
            exclusion⟩)
        .nil)

/-- Node `[144]`: route every declared same-token bottleneck of the current
residual.  Both hypotheses are read from the incoming exact ledger. -/
@[reducible] noncomputable def bottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.bottleneckRouting
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .bottleneckRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down.1
      .cons (key := K .bottleneckRouting)
        (show Value BranchState Presentation presentation data
            .bottleneckRouting inputs.current from
          ⟨by
            simp only [Holds]
            intro HighDegree Absorbing bottleneck windowFree
            exact bottleneck.outcome selection.1 uncompressible windowFree⟩)
        .nil)

/-- Node `[144]`, survivor arm: eliminate the absorbed outcome locally and
append the resulting Type-B handoff fact to the same ledger. -/
@[reducible] noncomputable def typeBHandoffRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBHandoff
    { Requires := [K .bottleneckRouting, K .sparseSurplusSurvivor]
      Produces := [K .typeBHandoff]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routed := (inputs.get (K .bottleneckRouting)).down
      let survivor := (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .typeBHandoff)
        (show Value BranchState Presentation presentation data
            .typeBHandoff inputs.current from
          ⟨by
            classical
            simp only [Holds] at routed ⊢
            intro HighDegree Absorbing bottleneck windowFree internal baseline
              contextEquivalent
            rcases routed HighDegree Absorbing bottleneck windowFree with
              absorbed | handoff
            · exfalso
              apply survivor
              rcases absorbed with defect | complete | delocalizes
              · obtain ⟨context, separated⟩ := defect
                exact absurd (contextEquivalent context) separated
              · refine .compression bottleneck.separation.switchSupport
                  ⟨bottleneck.separation.switchConnected,
                    bottleneck.separation.switchProper,
                    bottleneck.reading.quotient, ?_, baseline,
                    bottleneck.reading.lexicographicallySmaller, ?_⟩
                · have registered := bottleneck.reading.registered internal
                    bottleneck.reading.reduced
                    bottleneck.reading.reduced_ssubset.subset
                  exact registered.trans rfl
                · intro context
                  have equivalence := complete.2 context
                  intro target
                  have targetFull := equivalence.mp target
                  change Graph.HasCycleWithLength data.LengthOK
                    (Graph.glue
                      (bottleneck.reading.state bottleneck.reading.base)
                      context) at targetFull
                  rw [bottleneck.reading.baseIsPiece] at targetFull
                  exact targetFull
              · obtain ⟨representative, smaller, baselineObject, transfer⟩ :=
                  delocalizes
                exact .delocalization representative smaller baselineObject
                  transfer
            · exact handoff⟩)
        .nil)

/-! ## Nodes `[131]`, `[137]` and `[138]`: the entropy count, the certified capacity
ledger, and the square-root surplus estimate

`prop:sparse-entropy-sandwich-with-blockers` rests on one count —
`lem:independent-target-entropy` with `lem:skeleton-dominates`: the mixed family
`ℐ_spine ∪ ℛ_Π` realizes its full code among the labelled skeletons of the
current object.  Per the methodology it is a decision on the literal residual:
the yes arm carries the count and continues the manuscript's chain, the no arm is
the residual on which it fails, carried as its own branch.  On the yes arm the
rest is arithmetic already proved in `Graph.SparsePressureLedger`. -/

/-- The certified capacity ledger of `def:capacity-token-ledger` at a declared
presentation, from the facts nodes `[126]`--`[137]` put on the ledger:
`lem:sparse-slack-surplus` (`2m = δn + σ`), node `[130]`'s pair count,
`lem:sparse-upper-envelope`, the strict surplus lower bound of node `[19]`, and
the entropy count of `prop:sparse-entropy-sandwich-with-blockers` at that
presentation.  The entropy budget is `E_spine + (m − m₀)(⌊log₂ n⌋+1)`. -/
theorem certifiedLedger_of_facts (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (sandwich : BlockedPairEntropySandwichStatement data object)
    (scheduleCard : (object.portPairSchedule data.threshold).card =
      (object.degreeSurplus data.threshold).choose 2)
    (envelope : object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount)
    (slack : 2 * object.edgeCount =
      data.threshold * object.vertexCount + object.degreeSurplus data.threshold)
    (above : data.surplusThreshold object.vertexCount < object.degreeSurplus data.threshold)
    (presentation : Graph.CapacityPresentation.{u} object data.windowOrder) :
    Nonempty (Graph.CertifiedObjectCapacityLedger object data.threshold data.windowOrder
      data.surplusScale presentation) := by
  classical
  obtain ⟨Coordinate, family, coordinateSupport, _survives, demand, deficitLe, entropy⟩ :=
    sandwich presentation
  have degreeLower : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans baseline (object.minDegree_le_degree vertex)
  have handshake : data.threshold * object.vertexCount ≤ 2 * object.edgeCount := by omega
  have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
      object.edgeCount := by
    unfold Graph.cubicBaselineEdgeCount; omega
  have surplusPos : 0 < object.degreeSurplus data.threshold :=
    lt_of_le_of_lt (Nat.zero_le _) above
  have slackLe : object.edgeCount - Graph.cubicBaselineEdgeCount object.vertexCount
      data.threshold ≤ object.degreeSurplus data.threshold := by
    unfold Graph.cubicBaselineEdgeCount; omega
  have sizePos : 0 < object.vertexCount := by
    by_contra zero
    have empty : object.vertexCount = 0 := Nat.eq_zero_of_not_pos zero
    have edges := object.edgeCount_le_choose_two
    rw [empty] at edges
    simp at edges
    unfold Graph.FiniteObject.degreeSurplus at surplusPos
    omega
  obtain ⟨vertex, _⟩ : object.vertexFinset.Nonempty :=
    Finset.card_pos.mp (by rw [object.card_vertexFinset]; exact sizePos)
  exact ⟨Graph.certifiedLedger_of_sandwich presentation
    (le_trans (by norm_num) data.three_le_threshold) aboveEdges family.card
    (Graph.spineDeficit object.vertexCount data.threshold family.card) demand deficitLe
    slackLe entropy scheduleCard
    (object.capacityTokens_nonempty data.threshold presentation.packing vertex)
    (object.card_capacityTokens_le presentation.packingValid degreeLower
      data.three_le_threshold handshake envelope data.windowOrder_pos data.joinSlack)⟩

/-- `C_sp ≥ 2` and `⌈√n⌉ ≥ 1` at a nonempty object: the strict surplus lower bound
of node `[19]` puts `σ(G) ≥ 3`, hence `0 < n`.  Read off `K .surplusAbove`. -/
theorem vertexCount_pos_of_surplusAbove (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (above : data.surplusThreshold object.vertexCount < object.degreeSurplus data.threshold) :
    0 < object.vertexCount := by
  by_contra zero
  have empty : object.vertexCount = 0 := Nat.eq_zero_of_not_pos zero
  have edges := object.edgeCount_le_choose_two
  rw [empty] at edges
  simp at edges
  unfold Graph.FiniteObject.degreeSurplus at above
  omega

/-- The registered `C_sp` covers the universal quadratic-safety coefficient. -/
theorem quadraticSafety_le_spineScale (data : Data.{u}) :
    Graph.TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound) +
        (2 * data.surplusScale +
          2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound *
            (3 * (data.threshold - 1) + 2)) := by
  have := data.quadraticSafetyScale_le_twiceAdditive
  change Graph.TokenLoad.quadraticSafetyScale ≤
    2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound) at this
  omega

/-- Node `[131]`: the entropy count of `prop:sparse-entropy-sandwich` at the full
pair schedule — decided on the literal independent residual of `[130]`. -/
noncomputable def freePairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .skeletonDominates) known]
    (sandwichFresh : K .freePairEntropySandwich ∉ known)
    (unrealizedFresh : K .freePairCodeUnrealized ∉ known) :
    Decision (K .freePairEntropySandwich) (K .freePairCodeUnrealized) previous := by
  classical
  let _dominated := (previous.get (K .skeletonDominates)).down
  exact Decision.run previous (K .freePairEntropySandwich) (K .freePairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.freePairEntropyDichotomy
    (if realized : FreePairEntropySandwichStatement data current.object then
      .inl ⟨realized⟩
    else
      .inr ⟨realized⟩)
    sandwichFresh unrealizedFresh

/-- Node `[131]` → `[138]`, `cor:spine-lower-bound-surplus-estimates` at the free
pair schedule: from the entropy count, `lem:sparse-slack-surplus` and the
baseline demand, `σ(G) ≤ C_sp ⌈√n⌉`. -/
@[reducible] noncomputable def freePairSurplusEstimateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairSurplusEstimate
    { Requires := [K .freePairEntropySandwich, K .sparseSlackSurplus, K .surplusAbove]
      Produces := [K .spineSurplusEstimate]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .spineSurplusEstimate)
        (show Value BranchState Presentation presentation data
            .spineSurplusEstimate inputs.current from
          ⟨by
            classical
            let object := inputs.current.object
            obtain ⟨Coordinate, family, coordinateSupport, _survives, demand, deficitLe,
              entropy⟩ := (inputs.get (K .freePairEntropySandwich)).down
            have slack : 2 * object.edgeCount =
                data.threshold * object.vertexCount + object.degreeSurplus data.threshold :=
              (inputs.get (K .sparseSlackSurplus)).down
            have above : data.surplusThreshold object.vertexCount <
                object.degreeSurplus data.threshold :=
              (inputs.get (K .surplusAbove)).down
            have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
                data.threshold ≤ object.edgeCount := by
              unfold Graph.cubicBaselineEdgeCount; omega
            have surplusPos : 0 < object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _) above
            have slackLe : object.edgeCount - Graph.cubicBaselineEdgeCount
                object.vertexCount data.threshold ≤ object.degreeSurplus data.threshold := by
              unfold Graph.cubicBaselineEdgeCount; omega
            have estimate := Graph.surplus_le_scale_of_pairSandwich object
              (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
              (le_trans (by norm_num) data.three_le_threshold) aboveEdges family.card
              (Graph.spineDeficit object.vertexCount data.threshold family.card) demand
              deficitLe slackLe entropy (vertexCount_pos_of_surplusAbove data object above)
              (quadraticSafety_le_spineScale data)
            have scale : data.spineScale =
                2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                  data.routingLabelBound) +
                  (2 * data.surplusScale +
                    2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                      data.routingLabelBound * (3 * (data.threshold - 1) + 2)) := rfl
            change object.degreeSurplus data.threshold ≤
              data.spineScale * Core.ceilSqrt object.vertexCount
            rw [scale]
            exact estimate⟩)
        .nil)

/-- Node `[137]`: the entropy count of `prop:sparse-entropy-sandwich-with-blockers`
at every declared capacity presentation — decided on the literal `[137]`
residual after its first production. -/
noncomputable def blockedPairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .roleFibrePartition) known]
    (sandwichFresh : K .blockedPairEntropySandwich ∉ known)
    (unrealizedFresh : K .blockedPairCodeUnrealized ∉ known) :
    Decision (K .blockedPairEntropySandwich) (K .blockedPairCodeUnrealized) previous := by
  classical
  let _partition := (previous.get (K .roleFibrePartition)).down
  exact Decision.run previous (K .blockedPairEntropySandwich)
    (K .blockedPairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.blockedPairEntropyDichotomy
    (if realized : BlockedPairEntropySandwichStatement data current.object then
      .inl ⟨realized⟩
    else
      .inr ⟨realized⟩)
    sandwichFresh unrealizedFresh

/-- Node `[137]`, second production: `lem:capacity-token-high-load` with
`cor:forced-homogeneous-same-token-scale` and the two sharp budgets, at the
object's own certified capacity ledger — which exists at every declared
presentation once the entropy count is on the ledger. -/
@[reducible] noncomputable def fibrePressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fibrePressure
    { Requires := [K .blockedPairEntropySandwich, K .canonicalPairLedger,
        K .sparseUpperEnvelope, K .sparseSlackSurplus, K .surplusAbove]
      Produces := [K .fibrePressure]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fibrePressure)
        (show Value BranchState Presentation presentation data
            .fibrePressure inputs.current from
          ⟨by
            obtain ⟨_active, _certificate, _pairsEq, scheduleCard, _partition,
              _incidence, _multiplicity, _blocked⟩ :=
              (inputs.get (K .canonicalPairLedger)).down
            obtain ⟨envelope, _packing, _valid, _maximal, _joinIdentity⟩ :=
              (inputs.get (K .sparseUpperEnvelope)).down
            exact Graph.fibrePressureStatement inputs.current.object data.threshold
              data.windowOrder fun presentation =>
                ⟨(Classical.choice (certifiedLedger_of_facts data inputs.current.object
                  inputs.current.baseline
                  (inputs.get (K .blockedPairEntropySandwich)).down scheduleCard envelope
                  (inputs.get (K .sparseSlackSurplus)).down
                  (inputs.get (K .surplusAbove)).down presentation)).ledger⟩⟩)
        .nil)

/-- Node `[137]`, the coupled excess test `D_all > 0?` of
`prop:single-graph-sparse-pressure-routing`: either every capacity ledger of the
object respects the geometric caps — and then, at the certified ledger of the
canonical presentation, `σ(G) ≤ R_L(n) ≤ C_sp ⌈√n⌉`, the near-cubic route `[138]`
— or some ledger overloads and the coupled excess forces a role-homogeneous
same-token pattern, routed by its token class to `[139]`--`[143]`. -/
noncomputable def coupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .blockedPairEntropySandwich) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .surplusAbove) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous := by
  classical
  let _pressure := (previous.get (K .fibrePressure)).down
  exact Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.coupledExcessDichotomy
    (if capped : Graph.SparsePressureCapped current.object data.threshold
        data.windowOrder then
      .inl ⟨by
          obtain ⟨_active, _certificate, _pairsEq, scheduleCard, _partition,
            _incidence, _multiplicity, _blocked⟩ :=
            (previous.get (K .canonicalPairLedger)).down
          obtain ⟨envelope, _packing, _valid, _maximal, _joinIdentity⟩ :=
            (previous.get (K .sparseUpperEnvelope)).down
          have above : data.surplusThreshold current.object.vertexCount <
              current.object.degreeSurplus data.threshold :=
            (previous.get (K .surplusAbove)).down
          let canonical := Graph.CapacityPresentation.canonical current.object
            data.windowOrder data.windowOrder_pos
          obtain ⟨certified⟩ := certifiedLedger_of_facts data current.object
            current.baseline (previous.get (K .blockedPairEntropySandwich)).down
            scheduleCard envelope (previous.get (K .sparseSlackSurplus)).down above canonical
          have estimate := Graph.surplus_le_scale_of_capped canonical certified
            data.routingLabelBound capped (vertexCount_pos_of_surplusAbove data _ above)
            (quadraticSafety_le_spineScale data)
          have scale : data.spineScale =
              2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                data.routingLabelBound) +
                (2 * data.surplusScale +
                  2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                    data.routingLabelBound * (3 * (data.threshold - 1) + 2)) := rfl
          change current.object.degreeSurplus data.threshold ≤
            data.spineScale * Core.ceilSqrt current.object.vertexCount
          rw [scale]
          exact estimate⟩
    else
      .inr ⟨(Graph.sparsePressureRouting current.object data.threshold
        data.windowOrder).resolve_left capped⟩)
    nearCubicFresh overloadFresh

/-- Node `[141]`: classify the concrete overload witness, already known to be
outside the window-incidence class, according to whether its token lies in the
remainder-surplus class; the residual is otherwise primitive. -/
noncomputable def remainderOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .windowClassAbsent) known]
    (remainderFresh : K .remainderClassOverload ∉ known)
    (primitiveFresh : K .remainderClassAbsent ∉ known) :
    Decision (K .remainderClassOverload) (K .remainderClassAbsent) previous :=
  Decision.run previous (K .remainderClassOverload) (K .remainderClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.remainderOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .remainderClassOverload).At current ⊕
          (K .remainderClassAbsent).At current) from by
      obtain ⟨declared, ledger, routingLabelBound, token, role, tokenMem,
        outside, rest⟩ := (previous.get (K .windowClassAbsent)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence => exact absurd classified outside
      | remainderSurplus =>
          exact ⟨.inl ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, classified, rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, classified, rest⟩⟩))
    remainderFresh primitiveFresh

/-- Node `[144]`, the caps/pattern test of `thm:homogeneous-overload-geometric-closure`
at the counted routing-label alphabet: either every capacity ledger of the object
respects the fixed homogeneous caps, or some role fibre carries a role-homogeneous
same-token matching or star of size `L_geom`. -/
noncomputable def homogeneousCapsDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (capsFresh : K .homogeneousCapsHold ∉ known)
    (patternFresh : K .homogeneousBottleneckPattern ∉ known) :
    Decision (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern) previous := by
  classical
  letI := data.boundaryProfileFintype
  exact Decision.run previous (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
    `Hypostructure.Graph.Strategy.Spine.homogeneousCapsDichotomy
    (if caps : Graph.HomogeneousCapsHold current.object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) then
      .inl ⟨caps⟩
    else
      .inr ⟨Graph.homogeneousBottleneckPatternStatement_of_not_caps current.object caps⟩)
    capsFresh patternFresh

/-- Node `[144]`, the near-cubic outcome: `cor:homogeneous-same-token-caps-close`
at the certified ledger of the canonical presentation gives `σ(G) ≤ C_sp ⌈√n⌉`. -/
theorem capsClose_estimate (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (sandwich : BlockedPairEntropySandwichStatement data object)
    (scheduleCard : (object.portPairSchedule data.threshold).card =
      (object.degreeSurplus data.threshold).choose 2)
    (envelope : object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount)
    (slack : 2 * object.edgeCount =
      data.threshold * object.vertexCount + object.degreeSurplus data.threshold)
    (above : data.surplusThreshold object.vertexCount < object.degreeSurplus data.threshold)
    (close : letI := data.boundaryProfileFintype
      Graph.HomogeneousCapsCloseStatement object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))) :
    object.degreeSurplus data.threshold ≤ data.spineScale * Core.ceilSqrt object.vertexCount := by
  classical
  letI := data.boundaryProfileFintype
  let canonical := Graph.CapacityPresentation.canonical object data.windowOrder
    data.windowOrder_pos
  obtain ⟨certified⟩ := certifiedLedger_of_facts data object baseline sandwich scheduleCard
    envelope slack above canonical
  obtain ⟨_, _, pressure, _⟩ := close canonical certified.ledger
  have capEq : Graph.SameTokenBlockerRoles.homogeneousCapCharge
      (Graph.SameTokenRoutingGerms.patternBound
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))) =
      Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound := by
    simp only [Graph.SameTokenBlockerRoles.homogeneousTokenCap,
      Graph.SameTokenBlockerRoles.geometricPatternBound,
      Graph.SameTokenRoutingGerms.patternBound, Graph.SameTokenRoutingGerms.labelBound]
    rw [data.routingLabelBound_eq]
  rw [capEq] at pressure
  have estimate := certified.degreeSurplus_le_mul_ceilSqrt
    (vertexCount_pos_of_surplusAbove data object above)
    (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
    (quadraticSafety_le_spineScale data) pressure
  have scale : data.spineScale =
      2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
        data.routingLabelBound) +
        (2 * data.surplusScale +
          2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
            data.routingLabelBound * (3 * (data.threshold - 1) + 2)) := rfl
  rw [scale]
  exact estimate

end Hypostructure.Graph.Strategy.Spine
