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
      obtain ⟨active, declared, activationEq, ledger, token, role, tokenMem,
        _selected, rest⟩ := (previous.get (K .sparsePressureOverload)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence =>
          exact ⟨.inl ⟨active, declared, activationEq, ledger, token, role,
            tokenMem, classified, rest⟩⟩
      | remainderSurplus =>
          exact ⟨.inr ⟨active, declared, activationEq, ledger, token, role,
            tokenMem, by simpa [classified], rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨active, declared, activationEq, ledger, token, role,
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
            obtain ⟨active, capacity, activationEq, _primitiveEq,
                _primitiveLe, concrete,
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
            refine ⟨active, capacity, activationEq, certified, ?_⟩
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
      let routed := (inputs.get (K .windowClassOverload)).down
      let active := routed.choose
      let declared := routed.choose_spec.choose
      let activationEq := routed.choose_spec.choose_spec.1
      let overload : Graph.SparsePressureOverloadInClass inputs.current.object
          data.threshold data.windowOrder data.routingLabelBound
          declared .windowIncidence :=
        routed.choose_spec.choose_spec.2
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          declared
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        obtain ⟨ledger, token, role, tokenMem, _selected, positive,
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
        refine ⟨ledger, token, tokenMem, role, ?_⟩
        simpa [Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          data.routingLabelBound_eq] using structured
      .cons (key := K .windowIncidenceAudit)
        (show Value BranchState Presentation presentation data
            .windowIncidenceAudit inputs.current from
          ⟨active, declared, activationEq, pattern⟩)
        (.cons (key := K .homogeneousBottleneckPattern)
          (show Value BranchState Presentation presentation data
              .homogeneousBottleneckPattern inputs.current from
            ⟨active, declared, activationEq, pattern⟩)
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
      let routed := (inputs.get (K .remainderClassOverload)).down
      let active := routed.choose
      let declared := routed.choose_spec.choose
      let activationEq := routed.choose_spec.choose_spec.1
      let overload : Graph.SparsePressureOverloadInClass inputs.current.object
          data.threshold data.windowOrder data.routingLabelBound
          declared .remainderSurplus :=
        routed.choose_spec.choose_spec.2
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          declared
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        obtain ⟨ledger, token, role, tokenMem, _selected, positive,
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
        refine ⟨ledger, token, tokenMem, role, ?_⟩
        simpa [Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          data.routingLabelBound_eq] using structured
      .cons (key := K .remainderSurplusAudit)
        (show Value BranchState Presentation presentation data
            .remainderSurplusAudit inputs.current from
          ⟨active, declared, activationEq, pattern⟩)
        (.cons (key := K .homogeneousBottleneckPattern)
          (show Value BranchState Presentation presentation data
              .homogeneousBottleneckPattern inputs.current from
            ⟨active, declared, activationEq, pattern⟩)
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
      let routed := (inputs.get (K .remainderClassAbsent)).down
      let active := routed.choose
      let declared := routed.choose_spec.choose
      let activationEq := routed.choose_spec.choose_spec.1
      let overload : Graph.SparsePressureOverloadInClass inputs.current.object
          data.threshold data.windowOrder data.routingLabelBound
          declared .primitiveCarrier :=
        routed.choose_spec.choose_spec.2
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          declared
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        obtain ⟨ledger, token, role, tokenMem, _selected, positive,
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
        refine ⟨ledger, token, tokenMem, role, ?_⟩
        simpa [Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          data.routingLabelBound_eq] using structured
      .cons (key := K .primitiveCarrierAudit)
        (show Value BranchState Presentation presentation data
            .primitiveCarrierAudit inputs.current from
          ⟨active, declared, activationEq, pattern⟩)
        (.cons (key := K .homogeneousBottleneckPattern)
          (show Value BranchState Presentation presentation data
              .homogeneousBottleneckPattern inputs.current from
            ⟨active, declared, activationEq, pattern⟩)
          .nil))

/-! ## Node `[144]`: same-token bottleneck routing

The selected proof belongs here, inside one Type-A `factOnly` executor.  Its
inputs are the exact current-object facts already published by the branch; no
route, separator, label map, profile callback, or handoff object is accepted as
an argument.  The executor publishes the paper lemma and then its survivor
specialization monotonically.

The first remaining kernel obligation is deliberately exposed at the exact
mathematical step where it occurs.  `def:declared-coordinate-signature`
currently presents the eight supports used by `Z(π;t,r)` (including the
upstream canonical returns `R_p,R_q`), but the existing declarations do not
construct the paper's connector configurations or their graph-derived routing
labels from those supports.  The unresolved goal below is therefore the
paper's literal sparse-exit-or-Type-B conclusion.  No selector, replacement
datum, callback, or side carrier is postulated. -/

@[reducible] noncomputable def sameTokenBottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenBottleneckRouting
    { Requires := [K .homogeneousBottleneckPattern, K .activeSurplusDemands,
        K .cubicBaseline,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .sparseUpperEnvelope, K .maximalPacking,
        K .sparseSurplusSurvivor, K .selection, K .degreeProfileFibres,
        K .targetCompleteContextUniversality, K .replacementExclusion,
        K .uncompressible, K .noProperBaseline, K .remainderNormalized]
      Produces := [K .bottleneckRouting, K .typeBHandoff]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let patternFact :=
        (inputs.get (K .homogeneousBottleneckPattern)).down
      let routing : (K .bottleneckRouting).At inputs.current := ⟨by
          classical
          obtain ⟨patternActive, capacity, activationEq, concretePattern⟩ :=
            patternFact
          -- Read every paper hypothesis through the sealed ledger.  These are
          -- intentionally not repackaged into a route or callback record.
          have active := (inputs.get (K .activeSurplusDemands)).down
          have activeEq : patternActive = active := Subsingleton.elim _ _
          subst patternActive
          have cubic := (inputs.get (K .cubicBaseline)).down
          have _capacityLedger :=
            (inputs.get (K .capacityTokenLedger)).down
          have _pairLedger :=
            (inputs.get (K .canonicalPairLedger)).down
          have _blockerRoute :=
            (inputs.get (K .canonicalBlockerRoute)).down
          have _dependentFamily :=
            (inputs.get (K .dependentPairFamily)).down
          have _upperEnvelope :=
            (inputs.get (K .sparseUpperEnvelope)).down
          have _maximalPacking :=
            (inputs.get (K .maximalPacking)).down
          have _survivor := (inputs.get (K .sparseSurplusSurvivor)).down
          have _selection := (inputs.get (K .selection)).down
          have _profiles := (inputs.get (K .degreeProfileFibres)).down
          have _contexts :=
            (inputs.get (K .targetCompleteContextUniversality)).down
          have _replacement := (inputs.get (K .replacementExclusion)).down
          have _uncompressible := (inputs.get (K .uncompressible)).down
          have _noProperBaseline :=
            (inputs.get (K .noProperBaseline)).down
          have _remainderNormalized :=
            (inputs.get (K .remainderNormalized)).down
          refine ⟨active, capacity, activationEq, concretePattern, ?_⟩
          let object := inputs.current.object
          let activation := capacity.activation
          letI : DecidableEq object.Vertex := object.vertices.decEq
          obtain ⟨ledger, token, tokenMem, role, structured⟩ := concretePattern

          -- The support carried by the capacity token itself.  This is the
          -- source coordinate in `Z(π;t,r)`, computed by cases from `t` rather
          -- than supplied by a route object.
          let tokenSupport : Finset object.Vertex := by
            letI := object.vertices.decEq
            exact match token with
              | .boundaryWindow incidence => {incidence.1, incidence.2}
              | .crossWindow incidence => {incidence.1, incidence.2}
              | .remainder unit => {unit.1}
              | .primitive (.inl vertex) => {vertex}
              | .primitive (.inr (.inl incidence)) =>
                  {incidence.1, incidence.2}
              | .primitive (.inr (.inr port)) => {port.1, port.2}

          -- `T(p)`, read canonically from an active demand.  The empty branch
          -- only totalizes the function away from the pair schedule; every
          -- edge of the homogeneous pattern is proved below to consist of
          -- scheduled active demands.
          let selectedSupport (demand : object.Vertex × object.Vertex) :
              Finset object.Vertex :=
            if member : demand ∈ object.excessPorts data.threshold then
              (object.surplusPortOfMem member).support
            else ∅

          -- The local open/triangular coordinate of the paper's routing
          -- label, obtained from the actual shoulder graph.
          let portStatus (demand : object.Vertex × object.Vertex) :
              Graph.SameTokenRoutingGerms.PortStatus :=
            if _ : ∃ member : demand ∈ object.excessPorts data.threshold,
                ∃ left ∈ (object.surplusPortOfMem member).shoulders,
                  ∃ right ∈ (object.surplusPortOfMem member).shoulders,
                    left ≠ right ∧ object.graph.Adj left right then
              .triangular
            else
              .openPort

          have selectedSupport_card (demand : object.Vertex × object.Vertex)
              (member : demand ∈ object.excessPorts data.threshold) :
              (selectedSupport demand).card = data.threshold := by
            let port := object.surplusPortOfMem member
            have endpointNotShoulder : port.endpoint ∉ port.shoulders := by
              intro endpointShoulder
              exact object.graph.loopless.irrefl _
                ((port.mem_shoulders_iff port.endpoint).1 endpointShoulder).2
            obtain ⟨left, right, description, distinct⟩ :=
              active.shoulderPair demand member
            have shouldersEq : port.shoulders = {left, right} := by
              ext vertex
              rw [description]
              simp [or_comm]
            have shoulderCard : port.shoulders.card = 2 := by
              rw [shouldersEq]
              simp [distinct]
            have supportCard : port.support.card = data.threshold := by
              unfold Graph.FiniteObject.SurplusPort.support
              rw [Finset.card_insert_of_notMem endpointNotShoulder,
                shoulderCard, cubic]
            simpa only [selectedSupport, dif_pos member] using supportCard

          -- The boundary-degree profile of `T(p)`: enumerate its vertices in
          -- the object's fixed order and record their actual degrees in the
          -- induced active support.  The `Fin` bound is proved from
          -- `|T(p)| = threshold`, itself derived from the ledger's active-port
          -- shoulder pair and cubic-baseline facts.
          let boundaryProfile (demand : object.Vertex × object.Vertex) :
              data.BoundaryProfile := fun index => by
            if member : demand ∈ object.excessPorts data.threshold then
              let support := selectedSupport demand
              let ordered := object.orderedVertices.filter fun vertex =>
                vertex ∈ support
              if bound : index.1 < ordered.length then
                let vertex := ordered.get ⟨index.1, bound⟩
                have vertexMem : vertex ∈ support := by
                  have inside : vertex ∈ ordered :=
                    ordered.get_mem ⟨index.1, bound⟩
                  simp only [ordered, List.mem_filter, decide_eq_true_eq] at inside
                  exact inside.2
                have degreeBound :
                    (object.induce support).degree ⟨vertex, vertexMem⟩ <
                      data.threshold := by
                  have finiteBound :=
                    (object.induce support).degree_lt_vertexCount
                      ⟨vertex, vertexMem⟩
                  rw [Graph.FiniteObject.vertexCount_induce,
                    selectedSupport_card demand member] at finiteBound
                  exact finiteBound
                exact ⟨(object.induce support).degree ⟨vertex, vertexMem⟩,
                  degreeBound⟩
              else
                exact index
            else
              exact index

          -- The full bounded part of `Z(π;t,r)`: the token carrier, the
          -- canonical blocker support, `T(p),T(q)`, `R_p,R_q`, and the two
          -- response supports (the latter already occur in
          -- `activation.declaredSupport = T ∪ Γ`).
          let boundedSupport
              (pair : Finset (object.Vertex × object.Vertex)) :
              Finset object.Vertex := by
            letI := object.vertices.decEq
            exact tokenSupport ∪
              (Graph.FiniteObject.chargeSupport activation capacity.carrier
                pair ∪
                (pair.biUnion activation.declaredSupport ∪
                  pair.biUnion activation.returnSupport))

          -- The `P₁₃` coordinate consists of exactly the window positions
          -- met by the bounded routing support, read from presentations of the
          -- members of the actual maximal packing.
          let windowLabel
              (pair : Finset (object.Vertex × object.Vertex)) :
              Graph.WindowCurvature.Label data.windowOrder := by
            classical
            exact Finset.univ.filter fun index =>
              ∃ window ∈ capacity.packing,
                ∃ presentation :
                    Graph.TypeBDirectCycle.Presentation object data.windowOrder,
                  presentation.support = window ∧
                    presentation.coordinate index.1 ∈ boundedSupport pair

          let chordFlag
              (pair : Finset (object.Vertex × object.Vertex)) : Bool :=
            match Graph.FiniteObject.canonicalBlocker activation pair with
            | some (.arithmeticChordSet _) => true
            | _ => false

          -- `ρ_t(π)`, in the seven coordinates and order fixed by
          -- `def:same-token-routing-germs`.  The cardinality proof is part of
          -- the local call, so there is no off-pattern fallback label.  The
          -- endpoint coordinate is computed from the selected endpoint's
          -- actual position in the object's ordered two-element pair.
          let routingLabel
              (pair : Finset (object.Vertex × object.Vertex))
              (pairCard : pair.card = 2)
              (demand : object.Vertex × object.Vertex) :
              Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                (Graph.WindowCurvature.Label data.windowOrder) := by
            let first := pair.toList.get
              ⟨0, by simpa [pairCard] using (show 0 < pair.card by omega)⟩
            let second := pair.toList.get
              ⟨1, by simpa [pairCard] using (show 1 < pair.card by omega)⟩
            let endpoint : Fin 2 := if demand = first then 0 else 1
            exact (capacity.role pair,
              Graph.FiniteObject.CapacityToken.subtype token,
              endpoint,
              (portStatus first, portStatus second),
              (boundaryProfile first, boundaryProfile second),
              windowLabel pair, chordFlag pair)

          have selectedPairData :
              ∃ first second : Finset (object.Vertex × object.Vertex),
                ∃ left ∈ first, ∃ right ∈ second,
                  ∃ firstCard : first.card = 2,
                    ∃ secondCard : second.card = 2,
                      first ∈ ledger.presented.roleFibre token role ∧
                      second ∈ ledger.presented.roleFibre token role ∧
                      left ≠ right ∧
                        routingLabel first firstCard left =
                          routingLabel second secondCard right := by
            rcases structured with
                ⟨pattern, patternSubset, patternShape, large⟩ |
                ⟨centre, pattern, patternSubset, patternShape, large⟩
            · have pairs : ∀ edge ∈ pattern, edge.card = 2 := by
                intro edge edgeMem
                exact ledger.presented.pairs_roleFibre token role edge
                  (patternSubset edgeMem)
              let attached := pattern.attach
              let chosenDemand (edge : {edge // edge ∈ pattern}) :
                  object.Vertex × object.Vertex :=
                edge.1.toList.get ⟨0, by
                  rw [Finset.length_toList, pairs edge.1 edge.2]
                  omega⟩
              let attachedLabel (edge : {edge // edge ∈ pattern}) :=
                routingLabel edge.1 (pairs edge.1 edge.2) (chosenDemand edge)
              obtain ⟨first, firstMem, second, secondMem, different,
                  sameLabel⟩ :=
                Graph.SameTokenRoutingGerms.exists_same_routingLabel attached
                  attachedLabel (by
                    rw [show attached.card = pattern.card by simp [attached]]
                    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) large)
              have firstPattern : first.1 ∈ pattern := first.2
              have secondPattern : second.1 ∈ pattern := second.2
              let left := chosenDemand first
              let right := chosenDemand second
              have leftMem : left ∈ first.1 := by
                exact Finset.mem_toList.mp
                  (List.get_mem first.1.toList ⟨0, by
                    rw [Finset.length_toList, pairs first.1 first.2]
                    omega⟩)
              have rightMem : right ∈ second.1 := by
                exact Finset.mem_toList.mp
                  (List.get_mem second.1.toList ⟨0, by
                    rw [Finset.length_toList, pairs second.1 second.2]
                    omega⟩)
              have demandsDifferent : left ≠ right := by
                intro equal
                have edgeDifferent : first.1 ≠ second.1 := by
                  intro edgeEqual
                  exact different (Subtype.ext edgeEqual)
                exact patternShape first.1 firstPattern second.1 secondPattern
                  edgeDifferent left leftMem (equal ▸ rightMem)
              refine ⟨first.1, second.1, left, leftMem, right, rightMem,
                pairs first.1 firstPattern, pairs second.1 secondPattern,
                patternSubset firstPattern, patternSubset secondPattern,
                demandsDifferent, ?_⟩
              simpa only [attachedLabel] using sameLabel
            · have pairs : ∀ edge ∈ pattern, edge.card = 2 := by
                intro edge edgeMem
                exact ledger.presented.pairs_roleFibre token role edge
                  (patternSubset edgeMem)
              let attached := pattern.attach
              let chosenDemand (edge : {edge // edge ∈ pattern}) :
                  object.Vertex × object.Vertex :=
                (edge.1.erase centre).toList.get ⟨0, by
                  rw [Finset.length_toList,
                    Finset.card_erase_of_mem (patternShape edge.1 edge.2),
                    pairs edge.1 edge.2]
                  omega⟩
              let attachedLabel (edge : {edge // edge ∈ pattern}) :=
                routingLabel edge.1 (pairs edge.1 edge.2) (chosenDemand edge)
              obtain ⟨first, firstMem, second, secondMem, different,
                  sameLabel⟩ :=
                Graph.SameTokenRoutingGerms.exists_same_routingLabel attached
                  attachedLabel (by
                    rw [show attached.card = pattern.card by simp [attached]]
                    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) large)
              have firstPattern : first.1 ∈ pattern := first.2
              have secondPattern : second.1 ∈ pattern := second.2
              let left := chosenDemand first
              let right := chosenDemand second
              have leftErase : left ∈ first.1.erase centre := by
                exact Finset.mem_toList.mp
                  (List.get_mem (first.1.erase centre).toList ⟨0, by
                    rw [Finset.length_toList,
                      Finset.card_erase_of_mem
                        (patternShape first.1 firstPattern),
                      pairs first.1 firstPattern]
                    omega⟩)
              have rightErase : right ∈ second.1.erase centre := by
                exact Finset.mem_toList.mp
                  (List.get_mem (second.1.erase centre).toList ⟨0, by
                    rw [Finset.length_toList,
                      Finset.card_erase_of_mem
                        (patternShape second.1 secondPattern),
                      pairs second.1 secondPattern]
                    omega⟩)
              have leftNe : left ≠ centre := (Finset.mem_erase.mp leftErase).1
              have rightNe : right ≠ centre := (Finset.mem_erase.mp rightErase).1
              have leftMem : left ∈ first.1 := (Finset.mem_erase.mp leftErase).2
              have rightMem : right ∈ second.1 :=
                (Finset.mem_erase.mp rightErase).2
              have edgeEq : ∀ edge ∈ pattern, ∀ other,
                  other ≠ centre → other ∈ edge → edge = {centre, other} := by
                intro edge edgeMem other otherNe otherMem
                have centreMem := patternShape edge edgeMem
                refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
                · intro item inside
                  rcases Finset.mem_insert.mp inside with rfl | inside
                  · exact centreMem
                  · rw [Finset.mem_singleton.mp inside]
                    exact otherMem
                · rw [pairs edge edgeMem, Finset.card_insert_of_notMem
                      (by simp [Ne.symm otherNe]),
                    Finset.card_singleton]
              have firstEq := edgeEq first.1 firstPattern left leftNe leftMem
              have secondEq := edgeEq second.1 secondPattern right rightNe rightMem
              have demandsDifferent : left ≠ right := by
                intro equal
                apply different
                apply Subtype.ext
                rw [firstEq, secondEq, equal]
              refine ⟨first.1, second.1, left, leftMem, right, rightMem,
                pairs first.1 firstPattern, pairs second.1 secondPattern,
                patternSubset firstPattern, patternSubset secondPattern,
                demandsDifferent, ?_⟩
              simpa only [attachedLabel] using sameLabel
          obtain ⟨first, second, left, leftMem, right, rightMem,
            firstCard, secondCard, firstFibre, secondFibre,
            demandsDifferent, sameLabel⟩ := selectedPairData

          -- Read the two pattern edges back through the canonical token fibre.
          -- This recovers both the actual pair schedule and the equality
          -- `Θ_cap(πᵢ)=t`; neither is re-proved or carried separately.
          have firstTokenFibre : first ∈ ledger.presented.fibre token :=
            Graph.PatternFamily.roleFibre_subset _ _ _ firstFibre
          have secondTokenFibre : second ∈ ledger.presented.fibre token :=
            Graph.PatternFamily.roleFibre_subset _ _ _ secondFibre
          have firstSchedule : first ∈ object.portPairSchedule data.threshold :=
            ledger.presented.fibre_subset token firstTokenFibre
          have secondSchedule : second ∈ object.portPairSchedule data.threshold :=
            ledger.presented.fibre_subset token secondTokenFibre
          have leftActive : left ∈ object.excessPorts data.threshold :=
            (object.subset_excessPorts_of_mem_portPairSchedule data.threshold
              firstSchedule) leftMem
          have rightActive : right ∈ object.excessPorts data.threshold :=
            (object.subset_excessPorts_of_mem_portPairSchedule data.threshold
              secondSchedule) rightMem
          have firstCharge :
              Graph.FiniteObject.capacityCharge activation capacity.carrier
                data.threshold capacity.packing first = some token := by
            have labelled := (Finset.mem_filter.mp firstTokenFibre).2
            change Graph.CanonicalFibreLedger.canonicalLabel
                capacity.tokenOrder capacity.Eligible first = some token at labelled
            have charged : capacity.Eligible token first :=
              Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
            exact charged
          have secondCharge :
              Graph.FiniteObject.capacityCharge activation capacity.carrier
                data.threshold capacity.packing second = some token := by
            have labelled := (Finset.mem_filter.mp secondTokenFibre).2
            change Graph.CanonicalFibreLedger.canonicalLabel
                capacity.tokenOrder capacity.Eligible second = some token at labelled
            have charged : capacity.Eligible token second :=
              Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
            exact charged
          have leftBuffer : activation.localBuffer left = selectedSupport left := by
            simp only [activation, activationEq,
              Graph.recordSparsePairDEBlockers,
              Graph.pairResponseActivation_localBuffer_of_mem active leftActive,
              selectedSupport, dif_pos leftActive]
          have rightBuffer : activation.localBuffer right = selectedSupport right := by
            simp only [activation, activationEq,
              Graph.recordSparsePairDEBlockers,
              Graph.pairResponseActivation_localBuffer_of_mem active rightActive,
              selectedSupport, dif_pos rightActive]

          -- The current object is connected.  Otherwise its induced component
          -- through the selected demand would be a proper baseline object,
          -- contradicting the exact `noProperBaseline` ledger entry.
          have graphConnected : object.graph.Connected := by
            let root : object.Vertex := left.1
            let support : Finset object.Vertex :=
              object.vertexFinset.filter fun vertex =>
                object.graph.connectedComponentMk vertex =
                  object.graph.connectedComponentMk root
            by_contra disconnected
            have rootMem : root ∈ support := by simp [support]
            have supportCardLt : support.card < object.vertexCount := by
              have notAllReachable :
                  ¬ ∀ vertex : object.Vertex,
                    object.graph.Reachable root vertex := by
                intro allReachable
                apply disconnected
                exact object.graph.connected_iff_exists_forall_reachable.mpr
                  ⟨root, allReachable⟩
              push Not at notAllReachable
              obtain ⟨outside, unreachable⟩ := notAllReachable
              have outsideNotMem : outside ∉ support := by
                simp only [support, Finset.mem_filter,
                  object.mem_vertexFinset, true_and,
                  SimpleGraph.ConnectedComponent.eq]
                exact fun reachable => unreachable reachable.symm
              have strict : support ⊂ object.vertexFinset := by
                refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
                · intro vertex _
                  exact object.mem_vertexFinset vertex
                · intro equal
                  exact outsideNotMem
                    (equal ▸ object.mem_vertexFinset outside)
              simpa only [object.card_vertexFinset] using
                Finset.card_lt_card strict
            let component : Graph.ProperSubgraph object :=
              Graph.ProperSubgraph.ofInducedSupport object support supportCardLt
            letI : Nonempty component.value.Vertex := ⟨⟨root, rootMem⟩⟩
            have neighborSubset (vertex : component.value.Vertex) :
                object.graph.neighborSet vertex.1 ⊆
                  (support : Set object.Vertex) := by
              intro neighbor adjacent
              change neighbor ∈ support
              simp only [support, Finset.mem_filter, object.mem_vertexFinset,
                true_and, SimpleGraph.ConnectedComponent.eq]
              exact (show object.graph.Adj vertex.1 neighbor from adjacent).reachable.symm.trans
                (by
                  simpa only [support, Finset.mem_filter,
                    object.mem_vertexFinset, true_and,
                    SimpleGraph.ConnectedComponent.eq] using vertex.2)
            have componentMinimumDegree :
                data.threshold ≤ component.value.minDegree := by
              apply component.value.le_minDegree_of_forall_le_degree data.threshold
              intro vertex
              rw [show component.value.degree vertex = object.degree vertex.1 from
                object.degree_induce_of_neighborSet_subset support vertex
                  (neighborSubset vertex)]
              exact inputs.current.baseline.trans
                (object.minDegree_le_degree vertex.1)
            exact _noProperBaseline component componentMinimumDegree
          have connectedOn :
              Graph.SupportComponents.Connected.ConnectedOn object
                object.vertexFinset := by
            constructor
            · exact ⟨left.1, object.mem_vertexFinset _⟩
            · intro firstVertex secondVertex _ _
              obtain ⟨walk⟩ :=
                graphConnected.preconnected firstVertex secondVertex
              let path := walk.toPath
              exact ⟨path, path.isPath, fun vertex _ =>
                object.mem_vertexFinset vertex⟩

          -- `X_π` is the canonical connected support already defined by the
          -- declared pair-response API; the row selects no replacement
          -- support of its own.
          obtain ⟨firstPairSupport, firstPairSupportEq⟩ :=
            Option.isSome_iff_exists.mp
              (Graph.FiniteObject.DemandActivation.pairSupport_isSome_of_connected
                activation first connectedOn)
          obtain ⟨secondPairSupport, secondPairSupportEq⟩ :=
            Option.isSome_iff_exists.mp
              (Graph.FiniteObject.DemandActivation.pairSupport_isSome_of_connected
                activation second connectedOn)
          have firstPairSupportFacts :=
            Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
              firstPairSupportEq
          have secondPairSupportFacts :=
            Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
              secondPairSupportEq
          have leftSelected_subset_pairSupport :
              selectedSupport left ⊆ firstPairSupport := by
            intro vertex vertexMem
            apply firstPairSupportFacts.1
            apply Graph.FiniteObject.DemandActivation.declaredSupport_subset_pairSeed
              activation leftMem
            apply activation.localBuffer_subset_declaredSupport left
            rwa [leftBuffer]
          have rightSelected_subset_pairSupport :
              selectedSupport right ⊆ secondPairSupport := by
            intro vertex vertexMem
            apply secondPairSupportFacts.1
            apply Graph.FiniteObject.DemandActivation.declaredSupport_subset_pairSeed
              activation rightMem
            apply activation.localBuffer_subset_declaredSupport right
            rwa [rightBuffer]

          -- The primitive start is a function of the shared token itself.
          -- In particular both connector configurations are rooted at the
          -- same vertex; no caller-supplied root or route carrier appears.
          let tokenRoot : object.Vertex :=
            match token with
            | .boundaryWindow incidence => incidence.1
            | .crossWindow incidence => incidence.1
            | .remainder unit => unit.1
            | .primitive (.inl vertex) => vertex
            | .primitive (.inr (.inl incidence)) => incidence.1
            | .primitive (.inr (.inr port)) => port.2
          have tokenRoot_mem : tokenRoot ∈ tokenSupport := by
            rcases token with incidence | incidence | unit | item
            · simp [tokenRoot, tokenSupport]
            · simp [tokenRoot, tokenSupport]
            · simp [tokenRoot, tokenSupport]
            · rcases item with vertex | item
              · simp [tokenRoot, tokenSupport]
              · rcases item with incidence | port <;>
                  simp [tokenRoot, tokenSupport]

          -- The two exact same-token configurations are constructed next from
          -- the canonical blocker support and these ledger-read `T`, `R`, and
          -- `Γ` entries.
          skip
          ⟩
      let handoff : (K .typeBHandoff).At inputs.current := ⟨by
          obtain ⟨_, _, _, _pattern, outcome⟩ := routing.down
          rcases outcome with sparseExit | typeBHandoff
          · exact False.elim
              ((inputs.get (K .sparseSurplusSurvivor)).down sparseExit)
          · exact typeBHandoff⟩
      .cons (key := K .bottleneckRouting)
        routing
        (.cons (key := K .typeBHandoff) handoff .nil))

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
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
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
      let room := (previous.get (K .incrementalSkeletonRoom)).down.1
      let sandwich :
          2 ^ (current.object.degreeSurplus data.threshold).choose 2 ≤
            2 ^ Graph.spineDeficit current.object.vertexCount data.threshold
                family.card *
              current.object.vertexCount ^
                (current.object.edgeCount -
                  Graph.cubicBaselineEdgeCount current.object.vertexCount
                    data.threshold) := by
        have chain :
            2 ^ family.card *
                2 ^ (current.object.degreeSurplus data.threshold).choose 2 ≤
              2 ^ family.card *
                (2 ^ Graph.spineDeficit current.object.vertexCount
                    data.threshold family.card *
                  current.object.vertexCount ^
                    (current.object.edgeCount -
                      Graph.cubicBaselineEdgeCount current.object.vertexCount
                        data.threshold)) := by
          calc
            2 ^ family.card *
                  2 ^ (current.object.degreeSurplus data.threshold).choose 2
                = 2 ^ (family.card +
                    (current.object.degreeSurplus data.threshold).choose 2) := by
                    rw [pow_add]
            _ ≤ Graph.skeletonBudget current.object := count
            _ ≤ Graph.cubicBaselineBudget current.object.vertexCount
                    data.threshold *
                  current.object.vertexCount ^
                    (current.object.edgeCount -
                      Graph.cubicBaselineEdgeCount current.object.vertexCount
                        data.threshold) := room
            _ ≤ 2 ^ (family.card + Graph.spineDeficit
                    current.object.vertexCount data.threshold family.card) *
                  current.object.vertexCount ^
                    (current.object.edgeCount -
                      Graph.cubicBaselineEdgeCount current.object.vertexCount
                        data.threshold) :=
                Nat.mul_le_mul_right _ demand
            _ = 2 ^ family.card *
                  (2 ^ Graph.spineDeficit current.object.vertexCount
                      data.threshold family.card *
                    current.object.vertexCount ^
                      (current.object.edgeCount -
                        Graph.cubicBaselineEdgeCount current.object.vertexCount
                          data.threshold)) := by
                rw [pow_add, Nat.mul_assoc]
        exact Nat.le_of_mul_le_mul_left chain
          (Nat.two_pow_pos family.card)
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
      obtain ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete⟩ :=
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
        ⟨.inl ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives, demand, deficitBound,
          realized⟩⟩
      else
        ⟨.inr ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard,
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
            obtain ⟨active, presentation, activationEq, certified,
                _partition⟩ :=
              (inputs.get (K .roleFibrePartition)).down
            let ledger := certified.ledger
            obtain ⟨token, tokenMem, role, display, roleBound, forced,
                pattern⟩ := ledger.presented.exists_forced_pattern
            exact ⟨active, presentation, activationEq, certified, token, role,
              tokenMem, display, roleBound, forced, pattern⟩⟩)
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
      obtain ⟨active, presentation, activationEq, certified, _token, _role,
          _tokenMem, _display, _roleBound, _forced, _pattern⟩ :=
        (previous.get (K .fibrePressure)).down
      have above : data.surplusThreshold current.object.vertexCount <
          current.object.degreeSurplus data.threshold :=
        (previous.get (K .surplusAbove)).down
      let ledger := certified.ledger
      let patternBound := fun _ : Graph.SameTokenBlockerRoles.TokenClass =>
        Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound
      rcases Nat.eq_zero_or_pos (ledger.presented.coupledExcess
          ledger.presented.tokenClass patternBound) with balanced | overload
      · have capped : Graph.SparsePressureCappedAt certified
            data.routingLabelBound := by
          exact ledger.presented.demand_le_sparsePressureBound
            ledger.presented.tokenClass patternBound
            (Graph.SameTokenBlockerRoles.homogeneousTokenCap
              data.routingLabelBound)
            (current.object.capacityTokenSupply data.threshold)
            (fun _ => Nat.le_refl _) ledger.tokens_card_le balanced
        exact ⟨.inl ⟨by
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
      · exact ⟨.inr ⟨by
          obtain ⟨token, tokenMem, role, excess, pattern⟩ :=
            ledger.presented.exists_overloaded_roleFibre
              ledger.presented.tokenClass patternBound
          exact ⟨active, presentation, activationEq, ledger, token, role,
            tokenMem, trivial, overload, excess, pattern⟩⟩⟩))
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
      obtain ⟨active, declared, activationEq, ledger, token, role, tokenMem,
        outside, rest⟩ := (previous.get (K .windowClassAbsent)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence => exact absurd classified outside
      | remainderSurplus =>
          exact ⟨.inl ⟨active, declared, activationEq, ledger, token, role,
            tokenMem, classified, rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨active, declared, activationEq, ledger, token, role,
            tokenMem, classified, rest⟩⟩))
    remainderFresh primitiveFresh

end Hypostructure.Graph.Strategy.Spine
