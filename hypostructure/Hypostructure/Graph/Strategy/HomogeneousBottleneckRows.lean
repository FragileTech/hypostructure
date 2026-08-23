import Hypostructure.Graph.Strategy.SpineVocabulary
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
      obtain ⟨declared, ledger, token, role, tokenMem,
        _selected, rest⟩ := (previous.get (K .sparsePressureOverload)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence =>
          exact ⟨.inl ⟨declared, ledger, token, role,
            tokenMem, classified, rest⟩⟩
      | remainderSurplus =>
          exact ⟨.inr ⟨declared, ledger, token, role,
            tokenMem, by simpa [classified], rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨declared, ledger, token, role,
            tokenMem, by simpa [classified], rest⟩⟩))
    windowFresh outsideFresh

/-- Node `[137]`, first production: `lem:exact-surplus-pair-charge-partition`
with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), for the literal presentation and
free-side entropy count already written to the incoming ledger. -/
@[reducible] noncomputable def roleFibrePartitionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.roleFibrePartition
    { Requires := [K .blockedPairEntropySandwich, K .sparseSlackSurplus,
        K .surplusAbove]
      Produces := [K .roleFibrePartition]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .roleFibrePartition)
        (show Value BranchState Presentation presentation data
            .roleFibrePartition inputs.current from
          ⟨by
            classical
            let object := inputs.current.object
            obtain ⟨capacity, _primitiveEq, _primitiveLe, concrete,
                scheduleCard, Coordinate, family, coordinateSupport,
                _survives, demand, deficitLe, entropy⟩ :=
              (inputs.get (K .blockedPairEntropySandwich)).down
            have slack : 2 * object.edgeCount =
                data.threshold * object.vertexCount +
                  object.degreeSurplus data.threshold :=
              (inputs.get (K .sparseSlackSurplus)).down
            have above : data.surplusThreshold object.vertexCount <
                object.degreeSurplus data.threshold :=
              (inputs.get (K .surplusAbove)).down
            have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
                data.threshold ≤ object.edgeCount := by
              unfold Graph.cubicBaselineEdgeCount
              omega
            have surplusPos : 0 < object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _) above
            have slackLe : object.edgeCount -
                Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
                  object.degreeSurplus data.threshold := by
              unfold Graph.cubicBaselineEdgeCount
              omega
            have sizePos : 0 < object.vertexCount := by
              by_contra zero
              have empty : object.vertexCount = 0 := Nat.eq_zero_of_not_pos zero
              have edges := object.edgeCount_le_choose_two
              rw [empty] at edges
              simp at edges
              unfold Graph.FiniteObject.degreeSurplus at surplusPos
              omega
            obtain ⟨vertex, _vertexMem⟩ : object.vertexFinset.Nonempty :=
              Finset.card_pos.mp (by
                rw [object.card_vertexFinset]
                exact sizePos)
            let certified : Graph.CertifiedObjectCapacityLedger object
                data.threshold data.windowOrder data.surplusScale capacity :=
              Graph.certifiedLedger_of_sandwich capacity
                (le_trans (by norm_num) data.three_le_threshold) aboveEdges
                family.card
                (Graph.spineDeficit object.vertexCount data.threshold family.card)
                demand deficitLe slackLe entropy scheduleCard
                (object.capacityTokens_nonempty data.threshold capacity.packing vertex)
                concrete.2.1
            let ledger := certified.ledger
            refine ⟨capacity, certified, ?_⟩
            refine ⟨ledger.presented.choose_two_eq_free_add_sum_roleFibre
                ledger.presented.tokenClass,
              fun token => ledger.presented.load_eq_sum_roleFibre token,
              ledger.presented.classwise_split.1.1,
              ledger.presented.classwise_split.1.2,
              ledger.presented.classwise_split.2,
              ledger.presented.subtype_split.1.1,
              ledger.presented.subtype_split.2, ?_⟩
            intro patternBound positive value noMatching noStar
            exact ledger.presented.grainLoad_le_of_no_homogeneous
              ledger.presented.tokenClass value patternBound positive
              noMatching noStar⟩)
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

/-- Node `[140]`: audit the concrete window-incidence overload selected by
`[139]`.  The row reads that exact witness, derives its `L_geom` matching or
star, and publishes both the node-labelled audit and the canonical pattern
fact consumed at `[144]`; `ExactLedger` retains the class witness as ancestry. -/
@[reducible] noncomputable def windowIncidenceAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowIncidenceAudit
    { Requires := [K .windowClassOverload]
      Produces := [K .windowIncidenceAudit, K .homogeneousBottleneckPattern]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      letI := data.boundaryProfileFintype
      let overload : Graph.SparsePressureOverloadInClass inputs.current.object
          data.threshold data.windowOrder data.routingLabelBound
          .windowIncidence :=
        (inputs.get (K .windowClassOverload)).down
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        obtain ⟨declared, ledger, token, role, tokenMem, _selected, positive,
            absorbs, _quantitativePattern⟩ := overload
        have productPositive :
            0 < Graph.SameTokenBlockerRoles.sameTokenRoleBound *
              ledger.presented.tokens.card *
              ledger.presented.roleFibreExcess ledger.presented.tokenClass
                (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound) token role :=
          positive.trans_le absorbs
        have excessPositive :
            0 < ledger.presented.roleFibreExcess ledger.presented.tokenClass
              (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound) token role := by
          by_contra notPositive
          have zero : ledger.presented.roleFibreExcess
              ledger.presented.tokenClass
              (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound) token role = 0 :=
            Nat.eq_zero_of_not_pos notPositive
          simp [zero] at productPositive
        have large :
            (Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound - 1) *
                (2 * Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound - 3) <
              (ledger.presented.roleFibre token role).card := by
          unfold Graph.CapacityTokenLedger.roleFibreExcess at excessPositive
          exact Nat.sub_pos_iff_lt.mp excessPositive
        have structured := Graph.PatternFamily.exists_matching_or_star_of_lt_card
          (ledger.presented.roleFibre token role)
          (Graph.SameTokenBlockerRoles.geometricPatternBound
            data.routingLabelBound)
          (by simp [Graph.SameTokenBlockerRoles.geometricPatternBound])
          (ledger.presented.pairs_roleFibre token role) large
        refine ⟨declared, ledger, token, tokenMem, role, ?_⟩
        simpa [Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          data.routingLabelBound_eq] using structured
      .cons (key := K .windowIncidenceAudit)
        (show Value BranchState Presentation presentation data
            .windowIncidenceAudit inputs.current from
          ⟨pattern⟩)
        (.cons (key := K .homogeneousBottleneckPattern)
          (show Value BranchState Presentation presentation data
              .homogeneousBottleneckPattern inputs.current from
            ⟨pattern⟩)
          .nil))

/-- Node `[142]`: audit the concrete remainder-surplus overload selected by
`[141]`, publishing its exact `L_geom` pattern for `[144]`. -/
@[reducible] noncomputable def remainderSurplusAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderSurplusAudit
    { Requires := [K .remainderClassOverload]
      Produces := [K .remainderSurplusAudit, K .homogeneousBottleneckPattern]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      letI := data.boundaryProfileFintype
      let overload : Graph.SparsePressureOverloadInClass inputs.current.object
          data.threshold data.windowOrder data.routingLabelBound
          .remainderSurplus :=
        (inputs.get (K .remainderClassOverload)).down
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        obtain ⟨declared, ledger, token, role, tokenMem, _selected, positive,
            absorbs, _quantitativePattern⟩ := overload
        have productPositive :
            0 < Graph.SameTokenBlockerRoles.sameTokenRoleBound *
              ledger.presented.tokens.card *
              ledger.presented.roleFibreExcess ledger.presented.tokenClass
                (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound) token role :=
          positive.trans_le absorbs
        have excessPositive :
            0 < ledger.presented.roleFibreExcess ledger.presented.tokenClass
              (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound) token role := by
          by_contra notPositive
          have zero : ledger.presented.roleFibreExcess
              ledger.presented.tokenClass
              (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound) token role = 0 :=
            Nat.eq_zero_of_not_pos notPositive
          simp [zero] at productPositive
        have large :
            (Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound - 1) *
                (2 * Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound - 3) <
              (ledger.presented.roleFibre token role).card := by
          unfold Graph.CapacityTokenLedger.roleFibreExcess at excessPositive
          exact Nat.sub_pos_iff_lt.mp excessPositive
        have structured := Graph.PatternFamily.exists_matching_or_star_of_lt_card
          (ledger.presented.roleFibre token role)
          (Graph.SameTokenBlockerRoles.geometricPatternBound
            data.routingLabelBound)
          (by simp [Graph.SameTokenBlockerRoles.geometricPatternBound])
          (ledger.presented.pairs_roleFibre token role) large
        refine ⟨declared, ledger, token, tokenMem, role, ?_⟩
        simpa [Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          data.routingLabelBound_eq] using structured
      .cons (key := K .remainderSurplusAudit)
        (show Value BranchState Presentation presentation data
            .remainderSurplusAudit inputs.current from
          ⟨pattern⟩)
        (.cons (key := K .homogeneousBottleneckPattern)
          (show Value BranchState Presentation presentation data
              .homogeneousBottleneckPattern inputs.current from
            ⟨pattern⟩)
          .nil))

/-- Node `[143]`: audit the concrete primitive-carrier overload already
carried by `[141]`'s no-arm.  No audit-only re-key is inserted. -/
@[reducible] noncomputable def primitiveCarrierAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveCarrierAudit
    { Requires := [K .remainderClassAbsent]
      Produces := [K .primitiveCarrierAudit, K .homogeneousBottleneckPattern]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      letI := data.boundaryProfileFintype
      let overload : Graph.SparsePressureOverloadInClass inputs.current.object
          data.threshold data.windowOrder data.routingLabelBound
          .primitiveCarrier :=
        (inputs.get (K .remainderClassAbsent)).down
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        obtain ⟨declared, ledger, token, role, tokenMem, _selected, positive,
            absorbs, _quantitativePattern⟩ := overload
        have productPositive :
            0 < Graph.SameTokenBlockerRoles.sameTokenRoleBound *
              ledger.presented.tokens.card *
              ledger.presented.roleFibreExcess ledger.presented.tokenClass
                (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound) token role :=
          positive.trans_le absorbs
        have excessPositive :
            0 < ledger.presented.roleFibreExcess ledger.presented.tokenClass
              (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound) token role := by
          by_contra notPositive
          have zero : ledger.presented.roleFibreExcess
              ledger.presented.tokenClass
              (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound) token role = 0 :=
            Nat.eq_zero_of_not_pos notPositive
          simp [zero] at productPositive
        have large :
            (Graph.SameTokenBlockerRoles.geometricPatternBound
                data.routingLabelBound - 1) *
                (2 * Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound - 3) <
              (ledger.presented.roleFibre token role).card := by
          unfold Graph.CapacityTokenLedger.roleFibreExcess at excessPositive
          exact Nat.sub_pos_iff_lt.mp excessPositive
        have structured := Graph.PatternFamily.exists_matching_or_star_of_lt_card
          (ledger.presented.roleFibre token role)
          (Graph.SameTokenBlockerRoles.geometricPatternBound
            data.routingLabelBound)
          (by simp [Graph.SameTokenBlockerRoles.geometricPatternBound])
          (ledger.presented.pairs_roleFibre token role) large
        refine ⟨declared, ledger, token, tokenMem, role, ?_⟩
        simpa [Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          data.routingLabelBound_eq] using structured
      .cons (key := K .primitiveCarrierAudit)
        (show Value BranchState Presentation presentation data
            .primitiveCarrierAudit inputs.current from
          ⟨pattern⟩)
        (.cons (key := K .homogeneousBottleneckPattern)
          (show Value BranchState Presentation presentation data
              .homogeneousBottleneckPattern inputs.current from
            ⟨pattern⟩)
          .nil))

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

/-! ## Nodes `[131]`, `[137]` and `[138]`: the entropy count, the certified capacity
ledger, and the square-root surplus estimate

`prop:sparse-entropy-sandwich-with-blockers` rests on one count —
`lem:independent-target-entropy` with `lem:skeleton-dominates`: the mixed family
`ℐ_spine ∪ ℛ_Π` realizes its full code among the labelled skeletons of the
current object.  Per the methodology it is a decision on the literal residual:
the yes arm carries the count and continues the manuscript's chain, the no arm is
the residual on which it fails, carried as its own branch.  On the yes arm the
rest is arithmetic already proved in `Graph.SparsePressureLedger`. -/

/-- Node `[131]`: the entropy count of `prop:sparse-entropy-sandwich` at the full
pair schedule — decided on the literal independent residual of `[130]`. -/
noncomputable def freePairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .independentPairFamily) known]
    (sandwichFresh : K .freePairEntropySandwich ∉ known)
    (unrealizedFresh : K .freePairCodeUnrealized ∉ known) :
    Decision (K .freePairEntropySandwich) (K .freePairCodeUnrealized) previous := by
  classical
  let baseline := (previous.get (K .baselineSpineDemand)).down
  let Coordinate := Classical.choose baseline.2
  let coordinatePackage := Classical.choose_spec baseline.2
  let family := Classical.choose coordinatePackage
  let supportPackage := Classical.choose_spec coordinatePackage
  let coordinateSupport := Classical.choose supportPackage
  let properties := Classical.choose_spec supportPackage
  let survives := properties.1
  let demand := properties.2.1
  let deficitBound := properties.2.2
  let pairFacts := (previous.get (K .independentPairFamily)).down
  let active := Classical.choose pairFacts
  let activation := Graph.pairResponseActivation active
  let pairs := current.object.portPairSchedule data.threshold
  let responses := activation.pairFamily pairs
  let pairIndependentStatement : Prop :=
    ∀ attempt :
        let family := activation.pairFamily pairs
        let coordinateSupport : current.object.PairCoordinate →
            Finset current.object.Vertex := by
          letI := current.object.vertices.decEq
          exact Graph.DeclaredSignature.Coordinate.support
        Graph.AttemptedQuotient
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object family
          coordinateSupport,
      let family := activation.pairFamily pairs
      attempt.toRankQuotient.FunctionalOn ↑family →
        Set.InjOn attempt.label ↑family
  have pairIndependent : pairIndependentStatement :=
    Classical.choose_spec pairFacts
  have responseCard : responses.card =
      (current.object.degreeSurplus data.threshold).choose 2 := by
    rw [Graph.FiniteObject.DemandActivation.card_pairFamily]
    exact current.object.card_portPairSchedule fun vertex =>
      le_trans current.baseline (current.object.minDegree_le_degree vertex)
  let entropy : Prop :=
    pairIndependentStatement ∧
      2 ^ (family.card + responses.card) ≤ Graph.skeletonBudget current.object
  exact Decision.run previous (K .freePairEntropySandwich)
    (K .freePairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.freePairEntropyDichotomy
    (if realized : entropy then
      let count :
          2 ^ (family.card +
              (current.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget current.object := by
        simpa only [responseCard] using realized.2
      let handshake : data.threshold * current.object.vertexCount ≤
          2 * current.object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
          current.object data.threshold fun vertex =>
            le_trans current.baseline
              (current.object.minDegree_le_degree vertex)
      let above : Graph.cubicBaselineEdgeCount current.object.vertexCount
          data.threshold ≤ current.object.edgeCount :=
        Graph.cubicBaselineEdgeCount_le_edgeCount_of_handshake
          current.object data.threshold handshake
      let sandwich := Graph.entropySandwich_of_unblocked current.object
        (le_trans (by norm_num) data.three_le_threshold) above count demand
      let result : FreePairEntropySandwichStatement data current.object :=
        ⟨Coordinate, family, coordinateSupport, survives, demand,
          deficitBound, count, sandwich⟩
      .inl ⟨result⟩
    else
      let countFailure :
          ¬ 2 ^ (family.card +
              (current.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget current.object := by
        intro count
        apply realized
        refine ⟨pairIndependent, ?_⟩
        simpa only [responseCard] using count
      let result : FreePairCodeUnrealizedStatement data current.object :=
        ⟨Coordinate, family, coordinateSupport, survives, demand,
          deficitBound, countFailure⟩
      .inr ⟨result⟩)
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
              entropy, _sandwich⟩ :=
              (inputs.get (K .freePairEntropySandwich)).down
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
            have sizePos : 0 < object.vertexCount := by
              by_contra zero
              have empty : object.vertexCount = 0 := Nat.eq_zero_of_not_pos zero
              have edges := object.edgeCount_le_choose_two
              rw [empty] at edges
              simp at edges
              unfold Graph.FiniteObject.degreeSurplus at surplusPos
              omega
            have safety : Graph.TokenLoad.quadraticSafetyScale ≤
                2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                  data.routingLabelBound) +
                  (2 * data.surplusScale +
                    2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                      data.routingLabelBound * (3 * (data.threshold - 1) + 2)) := by
              have registered := data.quadraticSafetyScale_le_twiceAdditive
              change Graph.TokenLoad.quadraticSafetyScale ≤
                2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                  data.routingLabelBound) at registered
              omega
            have estimate := Graph.surplus_le_scale_of_pairSandwich object
              (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
              (le_trans (by norm_num) data.three_le_threshold) aboveEdges family.card
              (Graph.spineDeficit object.vertexCount data.threshold family.card) demand
              deficitLe slackLe entropy sizePos safety
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

/-- Node `[137]`: decide `prop:sparse-entropy-sandwich-with-blockers` on the
free side of the exact token map copied from `[136]`. -/
noncomputable def blockedPairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    (sandwichFresh : K .blockedPairEntropySandwich ∉ known)
    (unrealizedFresh : K .blockedPairCodeUnrealized ∉ known) :
    Decision (K .blockedPairEntropySandwich) (K .blockedPairCodeUnrealized) previous := by
  classical
  exact Decision.run previous (K .blockedPairEntropySandwich)
    (K .blockedPairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.blockedPairEntropyDichotomy
    (Classical.choice (show Nonempty
        ((K .blockedPairEntropySandwich).At current ⊕
          (K .blockedPairCodeUnrealized).At current) from by
      obtain ⟨capacity, primitiveEq, primitiveLe, concrete⟩ :=
        (previous.get (K .capacityTokenLedger)).down
      obtain ⟨_activePairFamily, _blockerCertificate, _pairsEq, scheduleCard,
          _partition, _incidence, _multiplicity, _blocked⟩ :=
        (previous.get (K .canonicalPairLedger)).down
      obtain ⟨_active, Coordinate, family, coordinateSupport, survives, demand,
          deficitBound⟩ := (previous.get (K .baselineSpineDemand)).down
      let count : Prop :=
        2 ^ (family.card +
            (Graph.freeSide current.object.vertexPairDecidableEq
              (current.object.portPairSchedule data.threshold)
            capacity.tokenOrder capacity.Eligible
            capacity.eligibleDecidable).card) ≤
          Graph.skeletonBudget current.object
      exact if realized : count then
        ⟨.inl ⟨capacity, primitiveEq, primitiveLe, concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives, demand, deficitBound,
          realized⟩⟩
      else
        ⟨.inr ⟨capacity, primitiveEq, primitiveLe, concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives, demand, deficitBound,
          realized⟩⟩))
    sandwichFresh unrealizedFresh

/-- Node `[137]`, second production: `lem:capacity-token-high-load` with
`cor:forced-homogeneous-same-token-scale` and the two sharp budgets, at the
same certified ledger whose count was just accepted. -/
@[reducible] noncomputable def fibrePressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fibrePressure
    { Requires := [K .roleFibrePartition]
      Produces := [K .fibrePressure]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fibrePressure)
        (show Value BranchState Presentation presentation data
            .fibrePressure inputs.current from
          ⟨by
            obtain ⟨presentation, certified, _partition⟩ :=
              (inputs.get (K .roleFibrePartition)).down
            let ledger := certified.ledger
            obtain ⟨token, tokenMem, role, display, roleBound, forced,
                pattern⟩ := ledger.presented.exists_forced_pattern
            exact ⟨presentation, certified, token, role, tokenMem, display,
              roleBound, forced, pattern⟩⟩)
        .nil)

/-- Node `[137]`, the coupled excess test `D_all > 0?` of
`prop:single-graph-sparse-pressure-routing`, on the certified ledger produced
immediately above: either it respects the geometric cap and gives `[138]`, or
its positive coupled excess selects one of `[140]`, `[142]`, `[143]`. -/
noncomputable def coupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .surplusAbove) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous := by
  classical
  exact Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.coupledExcessDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePressureNearCubic).At current ⊕
          (K .sparsePressureOverload).At current) from by
      obtain ⟨presentation, certified, _token, _role, _tokenMem, _display,
          _roleBound, _forced, _pattern⟩ :=
        (previous.get (K .fibrePressure)).down
      have above : data.surplusThreshold current.object.vertexCount <
          current.object.degreeSurplus data.threshold :=
        (previous.get (K .surplusAbove)).down
      exact if capped : Graph.SparsePressureCappedAt certified
          data.routingLabelBound then
        ⟨.inl ⟨by
          have sizePos : 0 < current.object.vertexCount := by
            by_contra zero
            have empty : current.object.vertexCount = 0 :=
              Nat.eq_zero_of_not_pos zero
            have edges := current.object.edgeCount_le_choose_two
            rw [empty] at edges
            simp at edges
            unfold Graph.FiniteObject.degreeSurplus at above
            omega
          have safety : Graph.TokenLoad.quadraticSafetyScale ≤
              2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                data.routingLabelBound) +
                (2 * data.surplusScale +
                  2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                    data.routingLabelBound * (3 * (data.threshold - 1) + 2)) := by
            have registered := data.quadraticSafetyScale_le_twiceAdditive
            change Graph.TokenLoad.quadraticSafetyScale ≤
              2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                data.routingLabelBound) at registered
            omega
          have estimate := Graph.surplus_le_scale_of_capped presentation certified
            data.routingLabelBound capped sizePos safety
          have scale : data.spineScale =
              2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                data.routingLabelBound) +
                (2 * data.surplusScale +
                  2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
                    data.routingLabelBound * (3 * (data.threshold - 1) + 2)) := rfl
          change current.object.degreeSurplus data.threshold ≤
            data.spineScale * Core.ceilSqrt current.object.vertexCount
          rw [scale]
          exact estimate⟩⟩
      else
        ⟨.inr ⟨by
          let ledger := certified.ledger
          have failure : Graph.CapacityTokenLedger.sparsePressureBound
                ledger.entropyBudget
                (Graph.SameTokenBlockerRoles.homogeneousTokenCap
                  data.routingLabelBound)
                (current.object.capacityTokenSupply data.threshold) <
              current.object.degreeSurplus data.threshold :=
            Nat.lt_of_not_ge capped
          obtain ⟨token, tokenMem, role, overload, excess, pattern⟩ :
              ∃ token ∈ ledger.presented.tokens,
                ∃ role : Graph.SameTokenBlockerRoles.Role,
                  0 < ledger.presented.coupledExcess
                      ledger.presented.tokenClass
                      (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                        data.routingLabelBound) ∧
                    ledger.presented.coupledExcess
                        ledger.presented.tokenClass
                        (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                          data.routingLabelBound) ≤
                      Graph.SameTokenBlockerRoles.sameTokenRoleBound *
                        ledger.presented.tokens.card *
                          ledger.presented.roleFibreExcess
                            ledger.presented.tokenClass
                            (fun _ =>
                              Graph.SameTokenBlockerRoles.geometricPatternBound
                                data.routingLabelBound) token role ∧
                    ((∃ structured ⊆ ledger.presented.roleFibre token role,
                        Graph.PatternFamily.IsMatching structured ∧
                          Graph.PatternFamily.patternThreshold
                              (ledger.presented.roleFibre token role).card ≤
                            structured.card) ∨
                      (∃ centre, ∃ structured ⊆
                          ledger.presented.roleFibre token role,
                        Graph.PatternFamily.IsStar structured centre ∧
                          Graph.PatternFamily.patternThreshold
                              (ledger.presented.roleFibre token role).card ≤
                            structured.card)) := by
            rcases ledger.presented.sparsePressureAlternative
                ledger.presented.tokenClass
                (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
                  data.routingLabelBound)
                (Graph.SameTokenBlockerRoles.homogeneousTokenCap
                  data.routingLabelBound)
                (current.object.capacityTokenSupply data.threshold)
                (fun _ => Nat.le_refl _) ledger.tokens_card_le with
              bounded | ⟨token, tokenMem, role, rest⟩
            · exact absurd bounded (Nat.not_le.mpr failure)
            · exact ⟨token, tokenMem, role, rest⟩
          exact ⟨presentation, ledger, token, role, tokenMem, trivial,
            overload, excess, pattern⟩⟩⟩))
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
      obtain ⟨declared, ledger, token, role, tokenMem,
        outside, rest⟩ := (previous.get (K .windowClassAbsent)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence => exact absurd classified outside
      | remainderSurplus =>
          exact ⟨.inl ⟨declared, ledger, token, role,
            tokenMem, classified, rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨declared, ledger, token, role,
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

end Hypostructure.Graph.Strategy.Spine
