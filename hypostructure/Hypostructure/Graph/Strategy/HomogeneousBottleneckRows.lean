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
star and every paper-declared same-root configuration on it, then publishes the
audit and canonical pattern fact consumed at `[144]` on the same `ExactLedger`. -/
@[reducible] noncomputable def windowIncidenceAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowIncidenceAudit
    { Requires := [K .windowClassOverload, K .capacityTokenLedger]
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
        let capacityFact := (inputs.get (K .capacityTokenLedger)).down
        let capacityProperties := capacityFact.choose_spec.choose_spec
        have connectedOn :
            Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object inputs.current.object.vertexFinset :=
          capacityProperties.2.2.2.2
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
        have configurations :
            ∀ pair ∈ ledger.presented.roleFibre token role,
              ∃ responseSupport : Finset inputs.current.object.Vertex,
                declared.activation.pairSupport pair = some responseSupport ∧
                  ∀ demand ∈ pair,
                    ∃ configuration :
                        Graph.SameTokenRoutingGerms.RoutingConfiguration
                          inputs.current.object
                          (declared.sameTokenRoutingSupport token pair)
                          (Graph.CapacityPresentation.tokenSupport token)
                          (declared.activation.localBuffer demand),
                      configuration.path.head? =
                        some (Graph.CapacityPresentation.tokenRoot token) ∧
                        configuration.path.getLast? = some demand.2 := by
          intro pair pairFibre
          have pairTokenFibre : pair ∈ ledger.presented.fibre token :=
            Graph.PatternFamily.roleFibre_subset _ _ _ pairFibre
          have pairSchedule :
              pair ∈ inputs.current.object.portPairSchedule data.threshold :=
            ledger.presented.fibre_subset token pairTokenFibre
          have pairSubset :
              pair ⊆ inputs.current.object.excessPorts data.threshold :=
            inputs.current.object.subset_excessPorts_of_mem_portPairSchedule
              data.threshold pairSchedule
          have charge :
              Graph.FiniteObject.capacityCharge declared.activation
                  declared.carrier data.threshold declared.packing pair =
                some token := by
            have labelled := (Finset.mem_filter.mp pairTokenFibre).2
            change Graph.CanonicalFibreLedger.canonicalLabel
                declared.tokenOrder declared.Eligible pair = some token at labelled
            have charged : declared.Eligible token pair :=
              Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
            exact charged
          exact Graph.CapacityPresentation.exists_sameRootRoutingConfigurationFamily_of_charge
              active declared
              activationEq pairSubset connectedOn charge
        refine ⟨ledger, token, tokenMem, role,
          Graph.CapacityPresentation.tokenRoot token, rfl, ?_⟩
        rcases structured with
            ⟨matching, matchingSubset, matchingShape, matchingLarge⟩ |
            ⟨centre, star, starSubset, starShape, starLarge⟩
        · refine Or.inl ⟨matching, matchingSubset, matchingShape, ?_, ?_⟩
          · change Fintype.card
                (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                  (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
              matching.card
            rw [← data.routingLabelBound_eq]
            simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
              matchingLarge
          · intro pair pairMem
            exact configurations pair (matchingSubset pairMem)
        · refine Or.inr ⟨centre, star, starSubset, starShape, ?_, ?_⟩
          · change Fintype.card
                (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                  (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
              star.card
            rw [← data.routingLabelBound_eq]
            simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
              starLarge
          · intro pair pairMem
            exact configurations pair (starSubset pairMem)
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
`[141]`, publishing its exact `L_geom` pattern and configuration family for `[144]`. -/
@[reducible] noncomputable def remainderSurplusAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderSurplusAudit
    { Requires := [K .remainderClassOverload, K .capacityTokenLedger]
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
        let capacityFact := (inputs.get (K .capacityTokenLedger)).down
        let capacityProperties := capacityFact.choose_spec.choose_spec
        have connectedOn :
            Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object inputs.current.object.vertexFinset :=
          capacityProperties.2.2.2.2
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
        have configurations :
            ∀ pair ∈ ledger.presented.roleFibre token role,
              ∃ responseSupport : Finset inputs.current.object.Vertex,
                declared.activation.pairSupport pair = some responseSupport ∧
                  ∀ demand ∈ pair,
                    ∃ configuration :
                        Graph.SameTokenRoutingGerms.RoutingConfiguration
                          inputs.current.object
                          (declared.sameTokenRoutingSupport token pair)
                          (Graph.CapacityPresentation.tokenSupport token)
                          (declared.activation.localBuffer demand),
                      configuration.path.head? =
                        some (Graph.CapacityPresentation.tokenRoot token) ∧
                        configuration.path.getLast? = some demand.2 := by
          intro pair pairFibre
          have pairTokenFibre : pair ∈ ledger.presented.fibre token :=
            Graph.PatternFamily.roleFibre_subset _ _ _ pairFibre
          have pairSchedule :
              pair ∈ inputs.current.object.portPairSchedule data.threshold :=
            ledger.presented.fibre_subset token pairTokenFibre
          have pairSubset :
              pair ⊆ inputs.current.object.excessPorts data.threshold :=
            inputs.current.object.subset_excessPorts_of_mem_portPairSchedule
              data.threshold pairSchedule
          have charge :
              Graph.FiniteObject.capacityCharge declared.activation
                  declared.carrier data.threshold declared.packing pair =
                some token := by
            have labelled := (Finset.mem_filter.mp pairTokenFibre).2
            change Graph.CanonicalFibreLedger.canonicalLabel
                declared.tokenOrder declared.Eligible pair = some token at labelled
            have charged : declared.Eligible token pair :=
              Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
            exact charged
          exact Graph.CapacityPresentation.exists_sameRootRoutingConfigurationFamily_of_charge
              active declared
              activationEq pairSubset connectedOn charge
        refine ⟨ledger, token, tokenMem, role,
          Graph.CapacityPresentation.tokenRoot token, rfl, ?_⟩
        rcases structured with
            ⟨matching, matchingSubset, matchingShape, matchingLarge⟩ |
            ⟨centre, star, starSubset, starShape, starLarge⟩
        · refine Or.inl ⟨matching, matchingSubset, matchingShape, ?_, ?_⟩
          · change Fintype.card
                (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                  (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
              matching.card
            rw [← data.routingLabelBound_eq]
            simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
              matchingLarge
          · intro pair pairMem
            exact configurations pair (matchingSubset pairMem)
        · refine Or.inr ⟨centre, star, starSubset, starShape, ?_, ?_⟩
          · change Fintype.card
                (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                  (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
              star.card
            rw [← data.routingLabelBound_eq]
            simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
              starLarge
          · intro pair pairMem
            exact configurations pair (starSubset pairMem)
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
carried by `[141]`'s no-arm, including every same-root configuration; no re-key. -/
@[reducible] noncomputable def primitiveCarrierAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveCarrierAudit
    { Requires := [K .remainderClassAbsent, K .capacityTokenLedger]
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
        let capacityFact := (inputs.get (K .capacityTokenLedger)).down
        let capacityProperties := capacityFact.choose_spec.choose_spec
        have connectedOn :
            Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object inputs.current.object.vertexFinset :=
          capacityProperties.2.2.2.2
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
        have configurations :
            ∀ pair ∈ ledger.presented.roleFibre token role,
              ∃ responseSupport : Finset inputs.current.object.Vertex,
                declared.activation.pairSupport pair = some responseSupport ∧
                  ∀ demand ∈ pair,
                    ∃ configuration :
                        Graph.SameTokenRoutingGerms.RoutingConfiguration
                          inputs.current.object
                          (declared.sameTokenRoutingSupport token pair)
                          (Graph.CapacityPresentation.tokenSupport token)
                          (declared.activation.localBuffer demand),
                      configuration.path.head? =
                        some (Graph.CapacityPresentation.tokenRoot token) ∧
                        configuration.path.getLast? = some demand.2 := by
          intro pair pairFibre
          have pairTokenFibre : pair ∈ ledger.presented.fibre token :=
            Graph.PatternFamily.roleFibre_subset _ _ _ pairFibre
          have pairSchedule :
              pair ∈ inputs.current.object.portPairSchedule data.threshold :=
            ledger.presented.fibre_subset token pairTokenFibre
          have pairSubset :
              pair ⊆ inputs.current.object.excessPorts data.threshold :=
            inputs.current.object.subset_excessPorts_of_mem_portPairSchedule
              data.threshold pairSchedule
          have charge :
              Graph.FiniteObject.capacityCharge declared.activation
                  declared.carrier data.threshold declared.packing pair =
                some token := by
            have labelled := (Finset.mem_filter.mp pairTokenFibre).2
            change Graph.CanonicalFibreLedger.canonicalLabel
                declared.tokenOrder declared.Eligible pair = some token at labelled
            have charged : declared.Eligible token pair :=
              Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
            exact charged
          exact Graph.CapacityPresentation.exists_sameRootRoutingConfigurationFamily_of_charge
              active declared
              activationEq pairSubset connectedOn charge
        refine ⟨ledger, token, tokenMem, role,
          Graph.CapacityPresentation.tokenRoot token, rfl, ?_⟩
        rcases structured with
            ⟨matching, matchingSubset, matchingShape, matchingLarge⟩ |
            ⟨centre, star, starSubset, starShape, starLarge⟩
        · refine Or.inl ⟨matching, matchingSubset, matchingShape, ?_, ?_⟩
          · change Fintype.card
                (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                  (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
              matching.card
            rw [← data.routingLabelBound_eq]
            simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
              matchingLarge
          · intro pair pairMem
            exact configurations pair (matchingSubset pairMem)
        · refine Or.inr ⟨centre, star, starSubset, starShape, ?_, ?_⟩
          · change Fintype.card
                (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                  (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
              star.card
            rw [← data.routingLabelBound_eq]
            simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
              starLarge
          · intro pair pairMem
            exact configurations pair (starSubset pairMem)
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

The row reads exactly the earlier manuscript facts used by the routing
argument: the sealed active-demand value (which already contains activation,
the two-shoulder description, and sparse-exit survival), cubic baseline, and
the sealed capacity/token presentation with its connectedness proof.  The
unresolved goal below remains the paper's literal sparse-exit-or-Type-B
conclusion.  No selector, callback, route record, or side carrier is
postulated. -/

@[reducible] noncomputable def sameTokenBottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenBottleneckRouting
    { Requires := [K .homogeneousBottleneckPattern,
        K .activeSurplusDemands,
        K .cubicBaseline, K .capacityTokenLedger]
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
          have activationFacts := active.activated
          have cubic := (inputs.get (K .cubicBaseline)).down
          have capacityLedger :=
            (inputs.get (K .capacityTokenLedger)).down
          have survivor := active.survives
          obtain ⟨_ledgerActive, _ledgerCapacity, _ledgerActivationEq,
              _primitiveCarrierCard, _primitiveCarrierBound,
              _concreteCapacityLedger, objectConnected⟩ := capacityLedger
          refine ⟨active, capacity, activationEq, concretePattern, ?_⟩
          let object := inputs.current.object
          let activation := capacity.activation
          letI : FinEnum object.Vertex := object.vertices
          letI : DecidableRel object.graph.Adj := object.decideAdj
          letI : DecidableEq object.Vertex := object.vertices.decEq
          -- The current-object baseline is part of the sealed residual itself.
          -- Name it here because the cubic-switch paragraph uses the actual
          -- minimum-degree hypothesis before it upgrades a surviving separator
          -- from degree three to degree at least four.
          have objectBaseline :
              Graph.MinimumDegreeAtLeast data.threshold object :=
            inputs.current.baseline
          -- Fact-sized projections used by the two routing cases.  Each comes
          -- directly from an `inputs.get` value or the capacity presentation
          -- sealed in the homogeneous-pattern entry.
          have noSparseExit := survivor
          have avoids : ¬ Graph.HasCycleWithLength data.LengthOK object :=
            fun cycle => noSparseExit (.dyadic cycle)
          have packingValid := capacity.packingValid
          have packingMaximal := capacity.packingMaximal
          obtain ⟨ledger, token, tokenMem, role, root, rootEq, structured⟩ :=
            concretePattern

          -- The token support and canonical root are already indices of the
          -- configurations carried by `structured`.  They are deliberately
          -- not reconstructed here: the producer has sealed both facts in the
          -- existing homogeneous-pattern entry, and `[144]` only reads them.
          -- No local support value or route carrier is introduced.

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
            obtain ⟨left, right, shoulderPair, shouldersDifferent⟩ :=
              active.shoulderPair demand member
            have shouldersEq : port.shoulders = {left, right} := by
              ext vertex
              rw [shoulderPair vertex]
              simp
            have shoulderCard :
                port.shoulders.card = data.threshold - 1 := by
              rw [shouldersEq, Finset.card_pair shouldersDifferent, cubic]
            simp only [selectedSupport, dif_pos member]
            unfold Graph.FiniteObject.SurplusPort.support
            rw [Finset.card_insert_of_notMem endpointNotShoulder, shoulderCard,
              cubic]

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
              Finset object.Vertex :=
            capacity.sameTokenRoutingSupport token pair

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

          -- The separated tails are read only up to their first entry in the
          -- selected core.  This is a local list operation on the two
          -- configurations already read from the homogeneous-pattern fact;
          -- it publishes no route or auxiliary proof object.
          have firstEntryPrefix
              (path : List object.Vertex) (selected : Finset object.Vertex)
              (lands : ∃ terminal,
                path.getLast? = some terminal ∧ terminal ∈ selected) :
              ∃ terminal initialSegment,
                initialSegment <+: path ∧
                  initialSegment.head? = path.head? ∧
                  initialSegment.getLast? = some terminal ∧
                  terminal ∈ selected ∧
                  ∀ vertex ∈ initialSegment,
                    vertex ∈ selected → vertex = terminal := by
            let meets : object.Vertex → Bool :=
              fun vertex => decide (vertex ∈ selected)
            obtain ⟨last, lastEq, lastSelected⟩ := lands
            have lastMem : last ∈ path := by
              obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp lastEq
              simp
            have meetsSome : ∃ vertex ∈ path, meets vertex :=
              ⟨last, lastMem, by simp [meets, lastSelected]⟩
            have indexLt : path.findIdx meets < path.length :=
              List.findIdx_lt_length_of_exists meetsSome
            let terminal := path[path.findIdx meets]
            let initialSegment := path.take (path.findIdx meets + 1)
            have terminalSelected : terminal ∈ selected := by
              have found : meets terminal :=
                List.findIdx_getElem (xs := path) (p := meets)
              simpa [meets] using found
            have split :
                initialSegment =
                  path.take (path.findIdx meets) ++ [terminal] := by
              simpa [initialSegment, terminal] using
                List.take_succ_eq_append_getElem indexLt
            refine ⟨terminal, initialSegment, ?_, ?_, ?_,
              terminalSelected, ?_⟩
            · simpa [initialSegment] using
                (List.take_prefix (path.findIdx meets + 1) path)
            · simp [initialSegment, List.head?_take]
            · rw [split]
              exact List.getLast?_concat
            · intro vertex member selectedMember
              rw [split, List.mem_append] at member
              rcases member with before | final
              · have absent : meets vertex = false :=
                  List.false_of_mem_take_findIdx before
                simp [meets, selectedMember] at absent
              · simpa using final

          -- Once the separated configurations have produced the paper's
          -- decorated envelope, publish exactly that produced handoff.  Its
          -- remainder admissibility is the downstream Type B lane's theorem,
          -- just as for the existing Type-A exit-`(7)` handoff.
          have handoff_of_envelope
              (core : Finset object.Vertex)
              (envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
                (handoffHighDegree data object)
                (handoffAbsorbing data object capacity.packing))
              (envelopeCore : envelope.core = core)
              (decorated : envelope.decorations.Nonempty) :
              SameTokenTypeBHandoffStatement data object := by
            refine ⟨capacity.packing, capacity.packingValid,
              capacity.packingMaximal, core, envelope, envelopeCore,
              decorated⟩

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

          have routedOutcome :
              Graph.SparseSurplusExit
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
                    object ∨
                SameTokenTypeBHandoffStatement data object := by
            rcases structured with
                ⟨pattern, patternSubset, patternShape, large, configurations⟩ |
                ⟨centre, pattern, patternSubset, patternShape, large,
                  configurations⟩
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
              have firstRoleFibre : first.1 ∈
                  ledger.presented.roleFibre token role :=
                patternSubset firstPattern
              have secondRoleFibre : second.1 ∈
                  ledger.presented.roleFibre token role :=
                patternSubset secondPattern
              have firstAssignedRole : capacity.role first.1 = role := by
                exact (Finset.mem_filter.mp firstRoleFibre).2
              have secondAssignedRole : capacity.role second.1 = role := by
                exact (Finset.mem_filter.mp secondRoleFibre).2
              have firstTokenFibre : first.1 ∈ ledger.presented.fibre token :=
                Graph.PatternFamily.roleFibre_subset _ _ _ firstRoleFibre
              have secondTokenFibre : second.1 ∈ ledger.presented.fibre token :=
                Graph.PatternFamily.roleFibre_subset _ _ _ secondRoleFibre
              have firstCapacityCharge :
                  Graph.FiniteObject.capacityCharge capacity.activation
                      capacity.carrier data.threshold capacity.packing first.1 =
                    some token := by
                have labelled := (Finset.mem_filter.mp firstTokenFibre).2
                change Graph.CanonicalFibreLedger.canonicalLabel
                    capacity.tokenOrder capacity.Eligible first.1 = some token at labelled
                have charged : capacity.Eligible token first.1 :=
                  Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
                exact charged
              have secondCapacityCharge :
                  Graph.FiniteObject.capacityCharge capacity.activation
                      capacity.carrier data.threshold capacity.packing second.1 =
                    some token := by
                have labelled := (Finset.mem_filter.mp secondTokenFibre).2
                change Graph.CanonicalFibreLedger.canonicalLabel
                    capacity.tokenOrder capacity.Eligible second.1 = some token at labelled
                have charged : capacity.Eligible token second.1 :=
                  Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
                exact charged
              have firstSchedule : first.1 ∈
                  object.portPairSchedule data.threshold :=
                ledger.presented.fibre_subset token firstTokenFibre
              have secondSchedule : second.1 ∈
                  object.portPairSchedule data.threshold :=
                ledger.presented.fibre_subset token secondTokenFibre
              have firstActiveSubset : first.1 ⊆
                  object.excessPorts data.threshold :=
                object.subset_excessPorts_of_mem_portPairSchedule
                  data.threshold firstSchedule
              have secondActiveSubset : second.1 ⊆
                  object.excessPorts data.threshold :=
                object.subset_excessPorts_of_mem_portPairSchedule
                  data.threshold secondSchedule
              have leftActive : left ∈ object.excessPorts data.threshold :=
                firstActiveSubset leftMem
              have rightActive : right ∈ object.excessPorts data.threshold :=
                secondActiveSubset rightMem
              obtain ⟨leftShoulder, leftOtherShoulder, leftShoulderPair,
                  leftShouldersDifferent⟩ := active.shoulderPair left leftActive
              obtain ⟨rightShoulder, rightOtherShoulder, rightShoulderPair,
                  rightShouldersDifferent⟩ := active.shoulderPair right rightActive
              have leftPortActivation := activationFacts left leftActive
                leftShoulder leftOtherShoulder leftShoulderPair
                leftShouldersDifferent
              have rightPortActivation := activationFacts right rightActive
                rightShoulder rightOtherShoulder rightShoulderPair
                rightShouldersDifferent
              have leftReturnEndpoint : left.2 ∈
                  (Graph.pairResponseActivation active).returnSupport left :=
                Graph.pairResponseActivation_endpoint_mem_returnSupport_of_mem
                  active leftActive
              have rightReturnEndpoint : right.2 ∈
                  (Graph.pairResponseActivation active).returnSupport right :=
                Graph.pairResponseActivation_endpoint_mem_returnSupport_of_mem
                  active rightActive
              have leftReturnConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object
                    ((Graph.pairResponseActivation active).returnSupport left) :=
                Graph.pairResponseActivation_connectedOn_returnSupport_of_mem
                  active leftActive
              have rightReturnConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object
                    ((Graph.pairResponseActivation active).returnSupport right) :=
                Graph.pairResponseActivation_connectedOn_returnSupport_of_mem
                  active rightActive
              obtain ⟨firstResponseSupport, firstResponseSupportEq,
                  firstConfigurations⟩ :=
                configurations first.1 firstPattern
              obtain ⟨secondResponseSupport, secondResponseSupportEq,
                  secondConfigurations⟩ :=
                configurations second.1 secondPattern
              have firstConfigurationExists :
                  ∃ configuration :
                      Graph.SameTokenRoutingGerms.RoutingConfiguration object
                        (capacity.sameTokenRoutingSupport token first.1)
                        (Graph.CapacityPresentation.tokenSupport token)
                        (capacity.activation.localBuffer left),
                    configuration.path.head? = some root ∧
                      configuration.path.getLast? = some left.2 :=
                firstConfigurations left leftMem
              have secondConfigurationExists :
                  ∃ configuration :
                      Graph.SameTokenRoutingGerms.RoutingConfiguration object
                        (capacity.sameTokenRoutingSupport token second.1)
                        (Graph.CapacityPresentation.tokenSupport token)
                        (capacity.activation.localBuffer right),
                    configuration.path.head? = some root ∧
                      configuration.path.getLast? = some right.2 :=
                secondConfigurations right rightMem
              obtain ⟨firstConfiguration, firstRoot, firstTerminalEndpoint⟩ :=
                firstConfigurationExists
              obtain ⟨secondConfiguration, secondRoot, secondTerminalEndpoint⟩ :=
                secondConfigurationExists
              have firstConnectorChain := firstConfiguration.chain
              have firstConnectorSimple := firstConfiguration.nodup
              have firstConnectorIssued := firstConfiguration.issued
              have firstConnectorInside := firstConfiguration.inside
              have firstConnectorLands := firstConfiguration.lands
              have secondConnectorChain := secondConfiguration.chain
              have secondConnectorSimple := secondConfiguration.nodup
              have secondConnectorIssued := secondConfiguration.issued
              have secondConnectorInside := secondConfiguration.inside
              have secondConnectorLands := secondConfiguration.lands
              have routingLabelsEqual :
                  routingLabel first.1 (pairs first.1 firstPattern) left =
                    routingLabel second.1 (pairs second.1 secondPattern) right := by
                simpa only [attachedLabel] using sameLabel
              have sameRoleLabel := congrArg (fun label => label.1)
                routingLabelsEqual
              have sameBlockerType := congrArg
                Graph.SameTokenBlockerRoles.Role.blocker sameRoleLabel
              have sameRoleTokenSubtype := congrArg
                Graph.SameTokenBlockerRoles.Role.token sameRoleLabel
              have sameRoleTokenClass := congrArg
                Graph.SameTokenBlockerRoles.tokenClass sameRoleTokenSubtype
              have sameTokenSubtypeLabel := congrArg (fun label => label.2.1)
                routingLabelsEqual
              have sameEndpointLabel := congrArg (fun label => label.2.2.1)
                routingLabelsEqual
              have samePortStatusLabel :=
                congrArg (fun label => label.2.2.2.1) routingLabelsEqual
              have sameBoundaryProfileLabel :=
                congrArg (fun label => label.2.2.2.2.1) routingLabelsEqual
              have sameBoundedPortProfileData := sameBoundaryProfileLabel
              have sameWindowLabel :=
                congrArg (fun label => label.2.2.2.2.2.1) routingLabelsEqual
              have sameSuppressedChordFlag :=
                congrArg (fun label => label.2.2.2.2.2.2) routingLabelsEqual
              have rootIsCanonical :
                  root = Graph.CapacityPresentation.tokenRoot token := rootEq
              have firstConfigurationCanonicalRoot :
                  firstConfiguration.path.head? =
                    some (Graph.CapacityPresentation.tokenRoot token) := by
                rw [firstRoot, rootIsCanonical]
              have secondConfigurationCanonicalRoot :
                  secondConfiguration.path.head? =
                    some (Graph.CapacityPresentation.tokenRoot token) := by
                rw [secondRoot, rootIsCanonical]
              let firstResponseCoordinate : object.PairCoordinate :=
                Graph.FiniteObject.DemandActivation.pairCoordinate first.1
                  firstResponseSupport
              let secondResponseCoordinate : object.PairCoordinate :=
                Graph.FiniteObject.DemandActivation.pairCoordinate second.1
                  secondResponseSupport
              let responseFamily : Finset object.PairCoordinate :=
                {firstResponseCoordinate, secondResponseCoordinate}
              let responseCoordinateSupport : object.PairCoordinate →
                  Finset object.Vertex :=
                Graph.DeclaredSignature.Coordinate.support
              have firstResponseCoordinateSupport :
                  responseCoordinateSupport firstResponseCoordinate =
                    firstResponseSupport := by
                rfl
              have secondResponseCoordinateSupport :
                  responseCoordinateSupport secondResponseCoordinate =
                    secondResponseSupport := by
                rfl
              have firstBaseResponseSupportEq :
                  (Graph.pairResponseActivation active).pairSupport first.1 =
                    some firstResponseSupport := by
                have selected := firstResponseSupportEq
                rw [activationEq] at selected
                simpa [Graph.FiniteObject.DemandActivation.pairSupport,
                  Graph.FiniteObject.DemandActivation.pairSeed,
                  Graph.recordSparsePairDEBlockers] using selected
              have secondBaseResponseSupportEq :
                  (Graph.pairResponseActivation active).pairSupport second.1 =
                    some secondResponseSupport := by
                have selected := secondResponseSupportEq
                rw [activationEq] at selected
                simpa [Graph.FiniteObject.DemandActivation.pairSupport,
                  Graph.FiniteObject.DemandActivation.pairSeed,
                  Graph.recordSparsePairDEBlockers] using selected
              let declaredResponseFamily := capacity.activation.pairFamily
                (object.portPairSchedule data.threshold)
              have firstResponseInDeclaredFamily :
                  firstResponseCoordinate ∈ declaredResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨first.1, firstSchedule, ?_⟩
                simp [firstResponseCoordinate, firstResponseSupportEq]
              have secondResponseInDeclaredFamily :
                  secondResponseCoordinate ∈ declaredResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨second.1, secondSchedule, ?_⟩
                simp [secondResponseCoordinate, secondResponseSupportEq]
              let baseResponseFamily :=
                (Graph.pairResponseActivation active).pairFamily
                  (object.portPairSchedule data.threshold)
              have firstResponseInBaseFamily :
                  firstResponseCoordinate ∈ baseResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨first.1, firstSchedule, ?_⟩
                simp [firstResponseCoordinate, firstBaseResponseSupportEq]
              have secondResponseInBaseFamily :
                  secondResponseCoordinate ∈ baseResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨second.1, secondSchedule, ?_⟩
                simp [secondResponseCoordinate, secondBaseResponseSupportEq]
              have responseFamily_subset_declared :
                  responseFamily ⊆ declaredResponseFamily := by
                intro coordinate member
                simp only [responseFamily, Finset.mem_insert,
                  Finset.mem_singleton] at member
                rcases member with rfl | rfl
                · exact firstResponseInDeclaredFamily
                · exact secondResponseInDeclaredFamily
              have responseFamily_subset_base :
                  responseFamily ⊆ baseResponseFamily := by
                intro coordinate member
                simp only [responseFamily, Finset.mem_insert,
                  Finset.mem_singleton] at member
                rcases member with rfl | rfl
                · exact firstResponseInBaseFamily
                · exact secondResponseInBaseFamily
              have responseCoordinatesDifferent :
                  firstResponseCoordinate ≠ secondResponseCoordinate := by
                intro equal
                apply different
                apply Subtype.ext
                simp only [firstResponseCoordinate, secondResponseCoordinate,
                  Graph.FiniteObject.DemandActivation.pairCoordinate] at equal
                exact Graph.DeclaredSignature.Coordinate.base.inj equal |>.2.1
              let commonSelectedSupport : Finset object.Vertex :=
                capacity.activation.localBuffer left ∪
                  capacity.activation.localBuffer right
              let parallelSeed : Finset object.Vertex :=
                boundedSupport first.1 ∪ boundedSupport second.1
              obtain ⟨parallelSupport, parallelSupportEq⟩ :=
                Option.isSome_iff_exists.mp
                  (Graph.CanonicalSupport.select?_isSome_of_connected
                    (object := object) (seed := parallelSeed) objectConnected)
              have parallelSupportFacts :=
                Graph.CanonicalSupport.mem_candidates_iff.mp
                  (Graph.CanonicalSupport.select?_mem_candidates
                    parallelSupportEq)
              have parallelSeedSubset : parallelSeed ⊆ parallelSupport :=
                parallelSupportFacts.1
              have parallelSupportConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object
                    parallelSupport :=
                parallelSupportFacts.2
              have firstResponseCarriedByParallelSupport :
                  responseCoordinateSupport firstResponseCoordinate ⊆
                    parallelSupport := by
                intro vertex member
                apply parallelSeedSubset
                change vertex ∈ boundedSupport first.1 ∪ boundedSupport second.1
                apply Finset.mem_union_left
                change vertex ∈ capacity.sameTokenRoutingSupport token first.1
                unfold Graph.CapacityPresentation.sameTokenRoutingSupport
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                unfold Graph.CapacityPresentation.pairConnectorSupport
                rw [firstResponseSupportEq]
                exact Finset.mem_union_left _ member
              have secondResponseCarriedByParallelSupport :
                  responseCoordinateSupport secondResponseCoordinate ⊆
                    parallelSupport := by
                intro vertex member
                apply parallelSeedSubset
                change vertex ∈ boundedSupport first.1 ∪ boundedSupport second.1
                apply Finset.mem_union_right
                change vertex ∈ capacity.sameTokenRoutingSupport token second.1
                unfold Graph.CapacityPresentation.sameTokenRoutingSupport
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                unfold Graph.CapacityPresentation.pairConnectorSupport
                rw [secondResponseSupportEq]
                exact Finset.mem_union_left _ member
              have routingDichotomy :
                  Graph.SameTokenRoutingGerms.Parallel
                      firstConfiguration.path secondConfiguration.path
                      commonSelectedSupport ∨
                    ∃ separator,
                      Graph.DecoratedHandoff.SeparatesAt
                        firstConfiguration.path secondConfiguration.path
                          separator := by
                have firstLandsCommon :
                    ∃ terminal,
                      firstConfiguration.path.getLast? = some terminal ∧
                        terminal ∈ commonSelectedSupport := by
                  obtain ⟨terminal, terminalLast, terminalInside⟩ :=
                    firstConnectorLands
                  exact ⟨terminal, terminalLast,
                    Finset.mem_union_left _ terminalInside⟩
                have secondLandsCommon :
                    ∃ terminal,
                      secondConfiguration.path.getLast? = some terminal ∧
                        terminal ∈ commonSelectedSupport := by
                  obtain ⟨terminal, terminalLast, terminalInside⟩ :=
                    secondConnectorLands
                  exact ⟨terminal, terminalLast,
                    Finset.mem_union_right _ terminalInside⟩
                rcases
                    Graph.SameTokenRoutingGerms.parallel_or_firstSeparator_of_same_root
                      commonSelectedSupport firstConfigurationCanonicalRoot
                        secondConfigurationCanonicalRoot
                        firstLandsCommon secondLandsCommon with
                  parallel | ⟨_firstSeparator, firstSeparatorEq, _notEntered⟩
                · exact Or.inl parallel
                · have diverges : Graph.SameTokenRoutingGerms.Diverges
                      firstConfiguration.path secondConfiguration.path := by
                    by_contra notDiverges
                    simp [Graph.SameTokenRoutingGerms.firstSeparator,
                      notDiverges] at firstSeparatorEq
                  have notFirstPrefix :
                      ¬ firstConfiguration.path <+:
                        secondConfiguration.path :=
                    fun prefixed =>
                      (Graph.SameTokenRoutingGerms.not_diverges_of_isPrefix
                        prefixed) diverges
                  have notSecondPrefix :
                      ¬ secondConfiguration.path <+:
                        firstConfiguration.path :=
                    fun prefixed =>
                      (Graph.SameTokenRoutingGerms.not_diverges_of_isPrefix_right
                        prefixed) diverges
                  exact Or.inr
                    (Graph.DecoratedHandoff.exists_separatesAt firstRoot
                      secondRoot notFirstPrefix notSecondPrefix)
              -- The parallel paragraph does not construct an arbitrary
              -- `AttemptedQuotient`: doing so would require the proper and
              -- closed representatives that the paragraph is meant to
              -- obtain.  Record instead the literal paper implication from
              -- the two declared coordinates and the connected common
              -- support.  Every premise below has already been read from the
              -- ledger or derived from its declared configurations.
              have parallelRoutes :
                  Graph.SameTokenRoutingGerms.Parallel
                      firstConfiguration.path secondConfiguration.path
                      commonSelectedSupport →
                    Graph.SupportComponents.Connected.ConnectedOn object
                        parallelSupport →
                    responseCoordinateSupport firstResponseCoordinate ⊆
                        parallelSupport →
                    responseCoordinateSupport secondResponseCoordinate ⊆
                        parallelSupport →
                    firstResponseCoordinate ≠ secondResponseCoordinate →
                    responseFamily ⊆ declaredResponseFamily →
                    responseFamily ⊆ baseResponseFamily →
                    (routingLabel first.1 (pairs first.1 firstPattern) left).2.2.2.2.1 =
                        (routingLabel second.1
                          (pairs second.1 secondPattern) right).2.2.2.2.1 →
                    routingLabel first.1 (pairs first.1 firstPattern) left =
                        routingLabel second.1
                          (pairs second.1 secondPattern) right →
                    Graph.SparseSurplusExit
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK)
                      data.LengthOK object := by
                skip
              rcases routingDichotomy with parallel |
                  ⟨separator, separatesAt⟩
              · exact Or.inl (parallelRoutes parallel parallelSupportConnected
                    firstResponseCarriedByParallelSupport
                    secondResponseCarriedByParallelSupport
                    responseCoordinatesDifferent responseFamily_subset_declared
                    responseFamily_subset_base sameBoundedPortProfileData
                    routingLabelsEqual)
              · exact by
                  obtain ⟨common, nextLeft, nextRight, tailLeft, tailRight,
                      leftDecomposition, rightDecomposition, nextDifferent⟩ :=
                    separatesAt
                  have separatorNextLeftAdj :
                      object.graph.Adj separator nextLeft := by
                    have chain := firstConnectorChain
                    rw [leftDecomposition] at chain
                    obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
                    exact (List.isChain_cons.mp rest).1 nextLeft (by simp)
                  have separatorNextRightAdj :
                      object.graph.Adj separator nextRight := by
                    have chain := secondConnectorChain
                    rw [rightDecomposition] at chain
                    obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
                    exact (List.isChain_cons.mp rest).1 nextRight (by simp)
                  have separatorMinimumDegree :
                      data.threshold ≤ object.degree separator :=
                    objectBaseline.trans (object.minDegree_le_degree separator)
                  -- The handoff tails end in the two selected demands.  Trim
                  -- each registered tail at its first entry into that literal
                  -- two-endpoint core; this is the manuscript's first-entry
                  -- operation, not an assumed remainder connector.
                  let core : Finset object.Vertex := {left.2, right.2}
                  have leftEndpointInside : left.2 ∈ core := by
                    simp [core]
                  have rightEndpointInside : right.2 ∈ core := by
                    simp [core]
                  have rawArmLeftChain :
                      (nextLeft :: tailLeft).IsChain object.graph.Adj := by
                    have chain := firstConnectorChain
                    rw [leftDecomposition] at chain
                    exact (List.isChain_cons.mp
                      (List.isChain_append.mp chain).2.1).2
                  have rawArmRightChain :
                      (nextRight :: tailRight).IsChain object.graph.Adj := by
                    have chain := secondConnectorChain
                    rw [rightDecomposition] at chain
                    exact (List.isChain_cons.mp
                      (List.isChain_append.mp chain).2.1).2
                  have rawArmLeftNodup : (nextLeft :: tailLeft).Nodup := by
                    have nodup := firstConnectorSimple
                    rw [leftDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).2
                  have rawArmRightNodup : (nextRight :: tailRight).Nodup := by
                    have nodup := secondConnectorSimple
                    rw [rightDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).2
                  have rawArmLeftLast :
                      (nextLeft :: tailLeft).getLast? = some left.2 := by
                    have last := firstTerminalEndpoint
                    rw [leftDecomposition] at last
                    simpa using last
                  have rawArmRightLast :
                      (nextRight :: tailRight).getLast? = some right.2 := by
                    have last := secondTerminalEndpoint
                    rw [rightDecomposition] at last
                    simpa using last
                  obtain ⟨firstTerminal, armLeft, armLeftPrefix,
                      armLeftHead, armLeftLast, firstTerminalInside,
                      armLeftFirstEntry⟩ :=
                    firstEntryPrefix (nextLeft :: tailLeft) core
                      ⟨left.2, rawArmLeftLast, leftEndpointInside⟩
                  obtain ⟨secondTerminal, armRight, armRightPrefix,
                      armRightHead, armRightLast, secondTerminalInside,
                      armRightFirstEntry⟩ :=
                    firstEntryPrefix (nextRight :: tailRight) core
                      ⟨right.2, rawArmRightLast, rightEndpointInside⟩
                  have armLeftIssued : armLeft.head? = some nextLeft := by
                    simpa using armLeftHead
                  have armRightIssued : armRight.head? = some nextRight := by
                    simpa using armRightHead
                  have armLeftChain : armLeft.IsChain object.graph.Adj := by
                    exact rawArmLeftChain.prefix armLeftPrefix
                  have armRightChain : armRight.IsChain object.graph.Adj := by
                    exact rawArmRightChain.prefix armRightPrefix
                  have armLeftNodup : armLeft.Nodup :=
                    armLeftPrefix.nodup rawArmLeftNodup
                  have armRightNodup : armRight.Nodup :=
                    armRightPrefix.nodup rawArmRightNodup
                  have separatorNotMemRawLeft :
                      separator ∉ nextLeft :: tailLeft := by
                    have nodup := firstConnectorSimple
                    rw [leftDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).1
                  have separatorNotMemRawRight :
                      separator ∉ nextRight :: tailRight := by
                    have nodup := secondConnectorSimple
                    rw [rightDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).1
                  have armLeftInterior :
                      ∀ vertex ∈ armLeft,
                        vertex ∈ core ∨ vertex = separator →
                          armLeft.getLast? = some vertex := by
                    intro vertex member alternatives
                    rcases alternatives with inside | rfl
                    · rw [armLeftFirstEntry vertex member inside]
                      exact armLeftLast
                    · exact False.elim
                        (separatorNotMemRawLeft (armLeftPrefix.subset member))
                  have armRightInterior :
                      ∀ vertex ∈ armRight,
                        vertex ∈ core ∨ vertex = separator →
                          armRight.getLast? = some vertex := by
                    intro vertex member alternatives
                    rcases alternatives with inside | rfl
                    · rw [armRightFirstEntry vertex member inside]
                      exact armRightLast
                    · exact False.elim
                        (separatorNotMemRawRight (armRightPrefix.subset member))

                  -- `S_z` is the framework's canonical minimum connected
                  -- support carrying precisely the two connector lists and
                  -- the two selected declared response supports.  This is the
                  -- support construction prescribed by the paper; it is not
                  -- a caller-supplied carrier.
                  let switchSeed : Finset object.Vertex :=
                    firstConfiguration.path.toFinset ∪
                      secondConfiguration.path.toFinset ∪
                        firstResponseSupport ∪ secondResponseSupport
                  obtain ⟨switchSupport, switchSupportEq⟩ :=
                    Option.isSome_iff_exists.mp
                      (Graph.CanonicalSupport.select?_isSome_of_connected
                        (object := object) (seed := switchSeed) objectConnected)
                  have switchSupportFacts :=
                    Graph.CanonicalSupport.mem_candidates_iff.mp
                      (Graph.CanonicalSupport.select?_mem_candidates
                        switchSupportEq)
                  have switchSeedSubset : switchSeed ⊆ switchSupport :=
                    switchSupportFacts.1
                  have switchConnected :
                      Graph.SupportComponents.Connected.ConnectedOn object
                        switchSupport :=
                    switchSupportFacts.2
                  have firstConfigurationCarriedBySwitch :
                      ∀ vertex ∈ firstConfiguration.path,
                        vertex ∈ switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    simp [switchSeed, member]
                  have secondConfigurationCarriedBySwitch :
                      ∀ vertex ∈ secondConfiguration.path,
                        vertex ∈ switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    simp [switchSeed, member]
                  have firstResponseCarriedBySwitch :
                      responseCoordinateSupport firstResponseCoordinate ⊆
                        switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    change vertex ∈
                      ((firstConfiguration.path.toFinset ∪
                          secondConfiguration.path.toFinset) ∪
                        firstResponseSupport) ∪ secondResponseSupport
                    apply Finset.mem_union_left
                    apply Finset.mem_union_right
                    rw [← firstResponseCoordinateSupport]
                    exact member
                  have secondResponseCarriedBySwitch :
                      responseCoordinateSupport secondResponseCoordinate ⊆
                        switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    change vertex ∈
                      ((firstConfiguration.path.toFinset ∪
                          secondConfiguration.path.toFinset) ∪
                        firstResponseSupport) ∪ secondResponseSupport
                    apply Finset.mem_union_right
                    rw [← secondResponseCoordinateSupport]
                    exact member
                  have switchCarriesResponseFamily :
                      ∀ coordinate ∈ responseFamily,
                        responseCoordinateSupport coordinate ⊆
                          switchSupport := by
                    intro coordinate member
                    simp only [responseFamily, Finset.mem_insert,
                      Finset.mem_singleton] at member
                    rcases member with rfl | rfl
                    · exact firstResponseCarriedBySwitch
                    · exact secondResponseCarriedBySwitch
                  -- At a cubic separator the paper routes the two declared
                  -- same-interface coordinates on `S_z` through its three
                  -- target-completeness alternatives.  State that literal
                  -- implication on all of its already-derived inputs; do not
                  -- prepackage the desired representatives as fields of an
                  -- `AttemptedQuotient`.
                  have switchRoutesAtCubic :
                      ∀ (cubicDegree :
                          object.degree separator = data.threshold),
                        (∃ rootIncidence,
                          object.graph.Adj rootIncidence separator ∧
                            rootIncidence ≠ nextLeft ∧
                            rootIncidence ≠ nextRight ∧
                            ∀ neighbour,
                              object.graph.Adj separator neighbour →
                                neighbour = rootIncidence ∨
                                  neighbour = nextLeft ∨
                                    neighbour = nextRight) →
                        token ∈ ledger.presented.tokens →
                        capacity.role first.1 = role →
                        capacity.role second.1 = role →
                        Graph.FiniteObject.capacityCharge capacity.activation
                            capacity.carrier data.threshold capacity.packing
                            first.1 = some token →
                        Graph.FiniteObject.capacityCharge capacity.activation
                            capacity.carrier data.threshold capacity.packing
                            second.1 = some token →
                        (Nonempty
                            (Graph.FiniteObject.SurplusPort.PortReturn object
                              left.1 left.2 leftShoulder leftOtherShoulder) ∧
                          (¬ object.graph.Adj leftShoulder leftOtherShoulder →
                            Nonempty
                              (Graph.FiniteObject.SurplusPort.OpenPortWitness
                                object data.LengthOK left.2 leftShoulder
                                  leftOtherShoulder)) ∧
                          (object.graph.Adj leftShoulder leftOtherShoulder →
                            object.graph.Adj left.2 leftShoulder ∧
                              object.graph.Adj leftShoulder leftOtherShoulder ∧
                                object.graph.Adj leftOtherShoulder left.2)) →
                        (Nonempty
                            (Graph.FiniteObject.SurplusPort.PortReturn object
                              right.1 right.2 rightShoulder rightOtherShoulder) ∧
                          (¬ object.graph.Adj rightShoulder rightOtherShoulder →
                            Nonempty
                              (Graph.FiniteObject.SurplusPort.OpenPortWitness
                                object data.LengthOK right.2 rightShoulder
                                  rightOtherShoulder)) ∧
                          (object.graph.Adj rightShoulder rightOtherShoulder →
                            object.graph.Adj right.2 rightShoulder ∧
                              object.graph.Adj rightShoulder rightOtherShoulder ∧
                                object.graph.Adj rightOtherShoulder right.2)) →
                        (∃ initial,
                          firstConfiguration.path.head? = some initial ∧
                            initial ∈
                              Graph.CapacityPresentation.tokenSupport token) →
                        (∃ initial,
                          secondConfiguration.path.head? = some initial ∧
                            initial ∈
                              Graph.CapacityPresentation.tokenSupport token) →
                        Graph.SupportComponents.Connected.ConnectedOn object
                            switchSupport →
                        (∀ vertex ∈ firstConfiguration.path,
                          vertex ∈ switchSupport) →
                        (∀ vertex ∈ secondConfiguration.path,
                          vertex ∈ switchSupport) →
                        (∀ coordinate ∈ responseFamily,
                          responseCoordinateSupport coordinate ⊆
                            switchSupport) →
                        responseFamily ⊆ declaredResponseFamily →
                        responseFamily ⊆ baseResponseFamily →
                        (routingLabel first.1
                            (pairs first.1 firstPattern) left).2.2.2.2.1 =
                          (routingLabel second.1
                            (pairs second.1 secondPattern) right).2.2.2.2.1 →
                        routingLabel first.1 (pairs first.1 firstPattern) left =
                          routingLabel second.1
                            (pairs second.1 secondPattern) right →
                        firstResponseCoordinate ≠ secondResponseCoordinate →
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                    skip
                  have cubicSeparatorRoutes :
                      object.degree separator = data.threshold →
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                    intro cubicDegree
                    have cubicCommonPrefixNonemptyOrSparseExit :
                        firstConfiguration.path.head? =
                            some (Graph.CapacityPresentation.tokenRoot token) →
                        secondConfiguration.path.head? =
                            some (Graph.CapacityPresentation.tokenRoot token) →
                        firstConfiguration.path =
                            common ++ separator :: nextLeft :: tailLeft →
                        secondConfiguration.path =
                            common ++ separator :: nextRight :: tailRight →
                        nextLeft ≠ nextRight →
                        Graph.SparseSurplusExit
                            (Graph.MinimumDegreeAtLeast data.threshold)
                            (Graph.HasCycleWithLength data.LengthOK)
                            data.LengthOK object ∨
                          common ≠ [] := by
                      skip
                    rcases cubicCommonPrefixNonemptyOrSparseExit
                        firstConfigurationCanonicalRoot
                        secondConfigurationCanonicalRoot leftDecomposition
                        rightDecomposition nextDifferent with sparseExit |
                        commonNonempty
                    · exact sparseExit
                    let rootIncidence := common.getLast commonNonempty
                    have rootIncidenceLast :
                        common.getLast? = some rootIncidence :=
                      List.getLast?_eq_some_getLast commonNonempty
                    have rootIncidenceAdj :
                        object.graph.Adj rootIncidence separator := by
                      have chain := firstConnectorChain
                      rw [leftDecomposition] at chain
                      obtain ⟨_, _, joint⟩ := List.isChain_append.mp chain
                      exact joint rootIncidence rootIncidenceLast separator (by simp)
                    have rootIncidenceNeLeft : rootIncidence ≠ nextLeft := by
                      have nodup := firstConnectorSimple
                      rw [leftDecomposition] at nodup
                      exact (List.nodup_append.mp nodup).2.2 rootIncidence
                        (List.getLast_mem commonNonempty) nextLeft (by simp)
                    have rootIncidenceNeRight : rootIncidence ≠ nextRight := by
                      have nodup := secondConnectorSimple
                      rw [rightDecomposition] at nodup
                      exact (List.nodup_append.mp nodup).2.2 rootIncidence
                        (List.getLast_mem commonNonempty) nextRight (by simp)
                    have separatorDegreeThree :
                        object.degree separator = 3 := cubicDegree.trans cubic
                    let usedIncidences : Finset object.Vertex :=
                      {rootIncidence, nextLeft, nextRight}
                    have usedIncidencesCard : usedIncidences.card = 3 := by
                      simp [usedIncidences, rootIncidenceNeLeft,
                        rootIncidenceNeRight, nextDifferent]
                    have usedIncidencesSubset :
                        usedIncidences ⊆ object.graph.neighborFinset separator := by
                      intro neighbour member
                      simp only [usedIncidences, Finset.mem_insert,
                        Finset.mem_singleton] at member
                      rcases member with rfl | rfl | rfl
                      · exact (SimpleGraph.mem_neighborFinset _ _ _).2
                          rootIncidenceAdj.symm
                      · exact (SimpleGraph.mem_neighborFinset _ _ _).2
                          separatorNextLeftAdj
                      · exact (SimpleGraph.mem_neighborFinset _ _ _).2
                          separatorNextRightAdj
                    have neighbourCard :
                        (object.graph.neighborFinset separator).card = 3 := by
                      exact separatorDegreeThree
                    have usedIncidencesEq : usedIncidences =
                        object.graph.neighborFinset separator :=
                      Finset.eq_of_subset_of_card_le usedIncidencesSubset (by
                        rw [usedIncidencesCard, neighbourCard])
                    have cubicIncidencesExhausted :
                        ∀ neighbour, object.graph.Adj separator neighbour →
                          neighbour = rootIncidence ∨
                            neighbour = nextLeft ∨ neighbour = nextRight := by
                      intro neighbour adjacent
                      have member : neighbour ∈ usedIncidences := by
                        rw [usedIncidencesEq]
                        exact (SimpleGraph.mem_neighborFinset _ _ _).2 adjacent
                      simpa [usedIncidences] using member
                    have cubicIncidencePackage :
                        ∃ rootIncidence,
                          object.graph.Adj rootIncidence separator ∧
                            rootIncidence ≠ nextLeft ∧
                            rootIncidence ≠ nextRight ∧
                            ∀ neighbour,
                              object.graph.Adj separator neighbour →
                                neighbour = rootIncidence ∨
                                  neighbour = nextLeft ∨
                                    neighbour = nextRight :=
                      ⟨rootIncidence, rootIncidenceAdj, rootIncidenceNeLeft,
                        rootIncidenceNeRight, cubicIncidencesExhausted⟩
                    exact switchRoutesAtCubic cubicDegree
                      cubicIncidencePackage tokenMem firstAssignedRole
                      secondAssignedRole firstCapacityCharge secondCapacityCharge
                      leftPortActivation rightPortActivation
                      firstConnectorIssued secondConnectorIssued switchConnected
                      firstConfigurationCarriedBySwitch
                      secondConfigurationCarriedBySwitch
                      switchCarriesResponseFamily
                      responseFamily_subset_declared responseFamily_subset_base
                      sameBoundedPortProfileData routingLabelsEqual
                      responseCoordinatesDifferent
                  have separatorNotCubic :
                      object.degree separator ≠ data.threshold := by
                    intro cubicDegree
                    exact noSparseExit (cubicSeparatorRoutes cubicDegree)
                  have separatorHigh :
                      handoffHighDegree data object separator := by
                    exact lt_of_le_of_ne separatorMinimumDegree
                      (Ne.symm separatorNotCubic)
                  have denied : ∀ centre firstNeighbour secondNeighbour,
                      ¬ handoffAbsorbing data object capacity.packing centre
                        firstNeighbour secondNeighbour :=
                    fun _ _ _ collision => avoids
                      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                        data.degenerateClosureRejected collision)
                  let envelope :=
                    Graph.DecoratedHandoff.envelopeOfFirstSeparator core
                      separator nextLeft nextRight nextDifferent
                      separatorNextLeftAdj separatorNextRightAdj
                      armLeft armRight armLeftIssued armRightIssued
                      armLeftChain armRightChain
                      armLeftNodup armRightNodup
                      ⟨firstTerminal, armLeftLast, firstTerminalInside⟩
                      ⟨secondTerminal, armRightLast, secondTerminalInside⟩
                      armLeftInterior armRightInterior separatorHigh avoids
                      (denied _ _ _) (denied _ _ _)
                  have envelopeCore : envelope.core = core := rfl
                  have decorated : envelope.decorations.Nonempty := by
                    simp [envelope,
                      Graph.DecoratedHandoff.envelopeOfFirstSeparator]
                  exact Or.inr
                    (handoff_of_envelope core envelope envelopeCore decorated)
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
              have firstRoleFibre : first.1 ∈
                  ledger.presented.roleFibre token role :=
                patternSubset firstPattern
              have secondRoleFibre : second.1 ∈
                  ledger.presented.roleFibre token role :=
                patternSubset secondPattern
              have firstAssignedRole : capacity.role first.1 = role := by
                exact (Finset.mem_filter.mp firstRoleFibre).2
              have secondAssignedRole : capacity.role second.1 = role := by
                exact (Finset.mem_filter.mp secondRoleFibre).2
              have firstTokenFibre : first.1 ∈ ledger.presented.fibre token :=
                Graph.PatternFamily.roleFibre_subset _ _ _ firstRoleFibre
              have secondTokenFibre : second.1 ∈ ledger.presented.fibre token :=
                Graph.PatternFamily.roleFibre_subset _ _ _ secondRoleFibre
              have firstCapacityCharge :
                  Graph.FiniteObject.capacityCharge capacity.activation
                      capacity.carrier data.threshold capacity.packing first.1 =
                    some token := by
                have labelled := (Finset.mem_filter.mp firstTokenFibre).2
                change Graph.CanonicalFibreLedger.canonicalLabel
                    capacity.tokenOrder capacity.Eligible first.1 = some token at labelled
                have charged : capacity.Eligible token first.1 :=
                  Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
                exact charged
              have secondCapacityCharge :
                  Graph.FiniteObject.capacityCharge capacity.activation
                      capacity.carrier data.threshold capacity.packing second.1 =
                    some token := by
                have labelled := (Finset.mem_filter.mp secondTokenFibre).2
                change Graph.CanonicalFibreLedger.canonicalLabel
                    capacity.tokenOrder capacity.Eligible second.1 = some token at labelled
                have charged : capacity.Eligible token second.1 :=
                  Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
                exact charged
              have firstSchedule : first.1 ∈
                  object.portPairSchedule data.threshold :=
                ledger.presented.fibre_subset token firstTokenFibre
              have secondSchedule : second.1 ∈
                  object.portPairSchedule data.threshold :=
                ledger.presented.fibre_subset token secondTokenFibre
              have firstActiveSubset : first.1 ⊆
                  object.excessPorts data.threshold :=
                object.subset_excessPorts_of_mem_portPairSchedule
                  data.threshold firstSchedule
              have secondActiveSubset : second.1 ⊆
                  object.excessPorts data.threshold :=
                object.subset_excessPorts_of_mem_portPairSchedule
                  data.threshold secondSchedule
              have leftActive : left ∈ object.excessPorts data.threshold :=
                firstActiveSubset leftMem
              have rightActive : right ∈ object.excessPorts data.threshold :=
                secondActiveSubset rightMem
              obtain ⟨leftShoulder, leftOtherShoulder, leftShoulderPair,
                  leftShouldersDifferent⟩ := active.shoulderPair left leftActive
              obtain ⟨rightShoulder, rightOtherShoulder, rightShoulderPair,
                  rightShouldersDifferent⟩ := active.shoulderPair right rightActive
              have leftPortActivation := activationFacts left leftActive
                leftShoulder leftOtherShoulder leftShoulderPair
                leftShouldersDifferent
              have rightPortActivation := activationFacts right rightActive
                rightShoulder rightOtherShoulder rightShoulderPair
                rightShouldersDifferent
              have leftReturnEndpoint : left.2 ∈
                  (Graph.pairResponseActivation active).returnSupport left :=
                Graph.pairResponseActivation_endpoint_mem_returnSupport_of_mem
                  active leftActive
              have rightReturnEndpoint : right.2 ∈
                  (Graph.pairResponseActivation active).returnSupport right :=
                Graph.pairResponseActivation_endpoint_mem_returnSupport_of_mem
                  active rightActive
              have leftReturnConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object
                    ((Graph.pairResponseActivation active).returnSupport left) :=
                Graph.pairResponseActivation_connectedOn_returnSupport_of_mem
                  active leftActive
              have rightReturnConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object
                    ((Graph.pairResponseActivation active).returnSupport right) :=
                Graph.pairResponseActivation_connectedOn_returnSupport_of_mem
                  active rightActive
              obtain ⟨firstResponseSupport, firstResponseSupportEq,
                  firstConfigurations⟩ :=
                configurations first.1 firstPattern
              obtain ⟨secondResponseSupport, secondResponseSupportEq,
                  secondConfigurations⟩ :=
                configurations second.1 secondPattern
              have firstConfigurationExists :
                  ∃ configuration :
                      Graph.SameTokenRoutingGerms.RoutingConfiguration object
                        (capacity.sameTokenRoutingSupport token first.1)
                        (Graph.CapacityPresentation.tokenSupport token)
                        (capacity.activation.localBuffer left),
                    configuration.path.head? = some root ∧
                      configuration.path.getLast? = some left.2 :=
                firstConfigurations left leftMem
              have secondConfigurationExists :
                  ∃ configuration :
                      Graph.SameTokenRoutingGerms.RoutingConfiguration object
                        (capacity.sameTokenRoutingSupport token second.1)
                        (Graph.CapacityPresentation.tokenSupport token)
                        (capacity.activation.localBuffer right),
                    configuration.path.head? = some root ∧
                      configuration.path.getLast? = some right.2 :=
                secondConfigurations right rightMem
              obtain ⟨firstConfiguration, firstRoot, firstTerminalEndpoint⟩ :=
                firstConfigurationExists
              obtain ⟨secondConfiguration, secondRoot, secondTerminalEndpoint⟩ :=
                secondConfigurationExists
              have firstConnectorChain := firstConfiguration.chain
              have firstConnectorSimple := firstConfiguration.nodup
              have firstConnectorIssued := firstConfiguration.issued
              have firstConnectorInside := firstConfiguration.inside
              have firstConnectorLands := firstConfiguration.lands
              have secondConnectorChain := secondConfiguration.chain
              have secondConnectorSimple := secondConfiguration.nodup
              have secondConnectorIssued := secondConfiguration.issued
              have secondConnectorInside := secondConfiguration.inside
              have secondConnectorLands := secondConfiguration.lands
              have routingLabelsEqual :
                  routingLabel first.1 (pairs first.1 firstPattern) left =
                    routingLabel second.1 (pairs second.1 secondPattern) right := by
                simpa only [attachedLabel] using sameLabel
              have sameRoleLabel := congrArg (fun label => label.1)
                routingLabelsEqual
              have sameBlockerType := congrArg
                Graph.SameTokenBlockerRoles.Role.blocker sameRoleLabel
              have sameRoleTokenSubtype := congrArg
                Graph.SameTokenBlockerRoles.Role.token sameRoleLabel
              have sameRoleTokenClass := congrArg
                Graph.SameTokenBlockerRoles.tokenClass sameRoleTokenSubtype
              have sameTokenSubtypeLabel := congrArg (fun label => label.2.1)
                routingLabelsEqual
              have sameEndpointLabel := congrArg (fun label => label.2.2.1)
                routingLabelsEqual
              have samePortStatusLabel :=
                congrArg (fun label => label.2.2.2.1) routingLabelsEqual
              have sameBoundaryProfileLabel :=
                congrArg (fun label => label.2.2.2.2.1) routingLabelsEqual
              have sameBoundedPortProfileData := sameBoundaryProfileLabel
              have sameWindowLabel :=
                congrArg (fun label => label.2.2.2.2.2.1) routingLabelsEqual
              have sameSuppressedChordFlag :=
                congrArg (fun label => label.2.2.2.2.2.2) routingLabelsEqual
              have rootIsCanonical :
                  root = Graph.CapacityPresentation.tokenRoot token := rootEq
              have firstConfigurationCanonicalRoot :
                  firstConfiguration.path.head? =
                    some (Graph.CapacityPresentation.tokenRoot token) := by
                rw [firstRoot, rootIsCanonical]
              have secondConfigurationCanonicalRoot :
                  secondConfiguration.path.head? =
                    some (Graph.CapacityPresentation.tokenRoot token) := by
                rw [secondRoot, rootIsCanonical]
              let firstResponseCoordinate : object.PairCoordinate :=
                Graph.FiniteObject.DemandActivation.pairCoordinate first.1
                  firstResponseSupport
              let secondResponseCoordinate : object.PairCoordinate :=
                Graph.FiniteObject.DemandActivation.pairCoordinate second.1
                  secondResponseSupport
              let responseFamily : Finset object.PairCoordinate :=
                {firstResponseCoordinate, secondResponseCoordinate}
              let responseCoordinateSupport : object.PairCoordinate →
                  Finset object.Vertex :=
                Graph.DeclaredSignature.Coordinate.support
              have firstResponseCoordinateSupport :
                  responseCoordinateSupport firstResponseCoordinate =
                    firstResponseSupport := by
                rfl
              have secondResponseCoordinateSupport :
                  responseCoordinateSupport secondResponseCoordinate =
                    secondResponseSupport := by
                rfl
              have firstBaseResponseSupportEq :
                  (Graph.pairResponseActivation active).pairSupport first.1 =
                    some firstResponseSupport := by
                have selected := firstResponseSupportEq
                rw [activationEq] at selected
                simpa [Graph.FiniteObject.DemandActivation.pairSupport,
                  Graph.FiniteObject.DemandActivation.pairSeed,
                  Graph.recordSparsePairDEBlockers] using selected
              have secondBaseResponseSupportEq :
                  (Graph.pairResponseActivation active).pairSupport second.1 =
                    some secondResponseSupport := by
                have selected := secondResponseSupportEq
                rw [activationEq] at selected
                simpa [Graph.FiniteObject.DemandActivation.pairSupport,
                  Graph.FiniteObject.DemandActivation.pairSeed,
                  Graph.recordSparsePairDEBlockers] using selected
              let declaredResponseFamily := capacity.activation.pairFamily
                (object.portPairSchedule data.threshold)
              have firstResponseInDeclaredFamily :
                  firstResponseCoordinate ∈ declaredResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨first.1, firstSchedule, ?_⟩
                simp [firstResponseCoordinate, firstResponseSupportEq]
              have secondResponseInDeclaredFamily :
                  secondResponseCoordinate ∈ declaredResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨second.1, secondSchedule, ?_⟩
                simp [secondResponseCoordinate, secondResponseSupportEq]
              let baseResponseFamily :=
                (Graph.pairResponseActivation active).pairFamily
                  (object.portPairSchedule data.threshold)
              have firstResponseInBaseFamily :
                  firstResponseCoordinate ∈ baseResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨first.1, firstSchedule, ?_⟩
                simp [firstResponseCoordinate, firstBaseResponseSupportEq]
              have secondResponseInBaseFamily :
                  secondResponseCoordinate ∈ baseResponseFamily := by
                apply Finset.mem_image.mpr
                refine ⟨second.1, secondSchedule, ?_⟩
                simp [secondResponseCoordinate, secondBaseResponseSupportEq]
              have responseFamily_subset_declared :
                  responseFamily ⊆ declaredResponseFamily := by
                intro coordinate member
                simp only [responseFamily, Finset.mem_insert,
                  Finset.mem_singleton] at member
                rcases member with rfl | rfl
                · exact firstResponseInDeclaredFamily
                · exact secondResponseInDeclaredFamily
              have responseFamily_subset_base :
                  responseFamily ⊆ baseResponseFamily := by
                intro coordinate member
                simp only [responseFamily, Finset.mem_insert,
                  Finset.mem_singleton] at member
                rcases member with rfl | rfl
                · exact firstResponseInBaseFamily
                · exact secondResponseInBaseFamily
              have responseCoordinatesDifferent :
                  firstResponseCoordinate ≠ secondResponseCoordinate := by
                intro equal
                apply different
                apply Subtype.ext
                simp only [firstResponseCoordinate, secondResponseCoordinate,
                  Graph.FiniteObject.DemandActivation.pairCoordinate] at equal
                exact Graph.DeclaredSignature.Coordinate.base.inj equal |>.2.1
              let commonSelectedSupport : Finset object.Vertex :=
                capacity.activation.localBuffer left ∪
                  capacity.activation.localBuffer right
              let parallelSeed : Finset object.Vertex :=
                boundedSupport first.1 ∪ boundedSupport second.1
              obtain ⟨parallelSupport, parallelSupportEq⟩ :=
                Option.isSome_iff_exists.mp
                  (Graph.CanonicalSupport.select?_isSome_of_connected
                    (object := object) (seed := parallelSeed) objectConnected)
              have parallelSupportFacts :=
                Graph.CanonicalSupport.mem_candidates_iff.mp
                  (Graph.CanonicalSupport.select?_mem_candidates
                    parallelSupportEq)
              have parallelSeedSubset : parallelSeed ⊆ parallelSupport :=
                parallelSupportFacts.1
              have parallelSupportConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object
                    parallelSupport :=
                parallelSupportFacts.2
              have firstResponseCarriedByParallelSupport :
                  responseCoordinateSupport firstResponseCoordinate ⊆
                    parallelSupport := by
                intro vertex member
                apply parallelSeedSubset
                change vertex ∈ boundedSupport first.1 ∪ boundedSupport second.1
                apply Finset.mem_union_left
                change vertex ∈ capacity.sameTokenRoutingSupport token first.1
                unfold Graph.CapacityPresentation.sameTokenRoutingSupport
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                unfold Graph.CapacityPresentation.pairConnectorSupport
                rw [firstResponseSupportEq]
                exact Finset.mem_union_left _ member
              have secondResponseCarriedByParallelSupport :
                  responseCoordinateSupport secondResponseCoordinate ⊆
                    parallelSupport := by
                intro vertex member
                apply parallelSeedSubset
                change vertex ∈ boundedSupport first.1 ∪ boundedSupport second.1
                apply Finset.mem_union_right
                change vertex ∈ capacity.sameTokenRoutingSupport token second.1
                unfold Graph.CapacityPresentation.sameTokenRoutingSupport
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                apply Finset.mem_union_right
                unfold Graph.CapacityPresentation.pairConnectorSupport
                rw [secondResponseSupportEq]
                exact Finset.mem_union_left _ member
              have routingDichotomy :
                  Graph.SameTokenRoutingGerms.Parallel
                      firstConfiguration.path secondConfiguration.path
                      commonSelectedSupport ∨
                    ∃ separator,
                      Graph.DecoratedHandoff.SeparatesAt
                        firstConfiguration.path secondConfiguration.path
                          separator := by
                have firstLandsCommon :
                    ∃ terminal,
                      firstConfiguration.path.getLast? = some terminal ∧
                        terminal ∈ commonSelectedSupport := by
                  obtain ⟨terminal, terminalLast, terminalInside⟩ :=
                    firstConnectorLands
                  exact ⟨terminal, terminalLast,
                    Finset.mem_union_left _ terminalInside⟩
                have secondLandsCommon :
                    ∃ terminal,
                      secondConfiguration.path.getLast? = some terminal ∧
                        terminal ∈ commonSelectedSupport := by
                  obtain ⟨terminal, terminalLast, terminalInside⟩ :=
                    secondConnectorLands
                  exact ⟨terminal, terminalLast,
                    Finset.mem_union_right _ terminalInside⟩
                rcases
                    Graph.SameTokenRoutingGerms.parallel_or_firstSeparator_of_same_root
                      commonSelectedSupport firstConfigurationCanonicalRoot
                        secondConfigurationCanonicalRoot
                        firstLandsCommon secondLandsCommon with
                  parallel | ⟨_firstSeparator, firstSeparatorEq, _notEntered⟩
                · exact Or.inl parallel
                · have diverges : Graph.SameTokenRoutingGerms.Diverges
                      firstConfiguration.path secondConfiguration.path := by
                    by_contra notDiverges
                    simp [Graph.SameTokenRoutingGerms.firstSeparator,
                      notDiverges] at firstSeparatorEq
                  have notFirstPrefix :
                      ¬ firstConfiguration.path <+:
                        secondConfiguration.path :=
                    fun prefixed =>
                      (Graph.SameTokenRoutingGerms.not_diverges_of_isPrefix
                        prefixed) diverges
                  have notSecondPrefix :
                      ¬ secondConfiguration.path <+:
                        firstConfiguration.path :=
                    fun prefixed =>
                      (Graph.SameTokenRoutingGerms.not_diverges_of_isPrefix_right
                        prefixed) diverges
                  exact Or.inr
                    (Graph.DecoratedHandoff.exists_separatesAt firstRoot
                      secondRoot notFirstPrefix notSecondPrefix)
              -- The star arm consumes the same literal parallel-identification
              -- implication as the matching arm.  No attempted quotient is
              -- staged here: its representative clauses are conclusions of
              -- this manuscript case, not inputs to a constructor.
              have parallelRoutes :
                  Graph.SameTokenRoutingGerms.Parallel
                      firstConfiguration.path secondConfiguration.path
                      commonSelectedSupport →
                    Graph.SupportComponents.Connected.ConnectedOn object
                        parallelSupport →
                    responseCoordinateSupport firstResponseCoordinate ⊆
                        parallelSupport →
                    responseCoordinateSupport secondResponseCoordinate ⊆
                        parallelSupport →
                    firstResponseCoordinate ≠ secondResponseCoordinate →
                    responseFamily ⊆ declaredResponseFamily →
                    responseFamily ⊆ baseResponseFamily →
                    (routingLabel first.1 (pairs first.1 firstPattern) left).2.2.2.2.1 =
                        (routingLabel second.1
                          (pairs second.1 secondPattern) right).2.2.2.2.1 →
                    routingLabel first.1 (pairs first.1 firstPattern) left =
                        routingLabel second.1
                          (pairs second.1 secondPattern) right →
                    Graph.SparseSurplusExit
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK)
                      data.LengthOK object := by
                skip
              rcases routingDichotomy with parallel |
                  ⟨separator, separatesAt⟩
              · exact Or.inl (parallelRoutes parallel parallelSupportConnected
                    firstResponseCarriedByParallelSupport
                    secondResponseCarriedByParallelSupport
                    responseCoordinatesDifferent responseFamily_subset_declared
                    responseFamily_subset_base sameBoundedPortProfileData
                    routingLabelsEqual)
              · exact by
                  obtain ⟨common, nextLeft, nextRight, tailLeft, tailRight,
                      leftDecomposition, rightDecomposition, nextDifferent⟩ :=
                    separatesAt
                  have separatorNextLeftAdj :
                      object.graph.Adj separator nextLeft := by
                    have chain := firstConnectorChain
                    rw [leftDecomposition] at chain
                    obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
                    exact (List.isChain_cons.mp rest).1 nextLeft (by simp)
                  have separatorNextRightAdj :
                      object.graph.Adj separator nextRight := by
                    have chain := secondConnectorChain
                    rw [rightDecomposition] at chain
                    obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
                    exact (List.isChain_cons.mp rest).1 nextRight (by simp)
                  have separatorMinimumDegree :
                      data.threshold ≤ object.degree separator :=
                    objectBaseline.trans (object.minDegree_le_degree separator)
                  let core : Finset object.Vertex := {left.2, right.2}
                  have leftEndpointInside : left.2 ∈ core := by
                    simp [core]
                  have rightEndpointInside : right.2 ∈ core := by
                    simp [core]
                  have rawArmLeftChain :
                      (nextLeft :: tailLeft).IsChain object.graph.Adj := by
                    have chain := firstConnectorChain
                    rw [leftDecomposition] at chain
                    exact (List.isChain_cons.mp
                      (List.isChain_append.mp chain).2.1).2
                  have rawArmRightChain :
                      (nextRight :: tailRight).IsChain object.graph.Adj := by
                    have chain := secondConnectorChain
                    rw [rightDecomposition] at chain
                    exact (List.isChain_cons.mp
                      (List.isChain_append.mp chain).2.1).2
                  have rawArmLeftNodup : (nextLeft :: tailLeft).Nodup := by
                    have nodup := firstConnectorSimple
                    rw [leftDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).2
                  have rawArmRightNodup : (nextRight :: tailRight).Nodup := by
                    have nodup := secondConnectorSimple
                    rw [rightDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).2
                  have rawArmLeftLast :
                      (nextLeft :: tailLeft).getLast? = some left.2 := by
                    have last := firstTerminalEndpoint
                    rw [leftDecomposition] at last
                    simpa using last
                  have rawArmRightLast :
                      (nextRight :: tailRight).getLast? = some right.2 := by
                    have last := secondTerminalEndpoint
                    rw [rightDecomposition] at last
                    simpa using last
                  obtain ⟨firstTerminal, armLeft, armLeftPrefix,
                      armLeftHead, armLeftLast, firstTerminalInside,
                      armLeftFirstEntry⟩ :=
                    firstEntryPrefix (nextLeft :: tailLeft) core
                      ⟨left.2, rawArmLeftLast, leftEndpointInside⟩
                  obtain ⟨secondTerminal, armRight, armRightPrefix,
                      armRightHead, armRightLast, secondTerminalInside,
                      armRightFirstEntry⟩ :=
                    firstEntryPrefix (nextRight :: tailRight) core
                      ⟨right.2, rawArmRightLast, rightEndpointInside⟩
                  have armLeftIssued : armLeft.head? = some nextLeft := by
                    simpa using armLeftHead
                  have armRightIssued : armRight.head? = some nextRight := by
                    simpa using armRightHead
                  have armLeftChain : armLeft.IsChain object.graph.Adj := by
                    exact rawArmLeftChain.prefix armLeftPrefix
                  have armRightChain : armRight.IsChain object.graph.Adj := by
                    exact rawArmRightChain.prefix armRightPrefix
                  have armLeftNodup : armLeft.Nodup :=
                    armLeftPrefix.nodup rawArmLeftNodup
                  have armRightNodup : armRight.Nodup :=
                    armRightPrefix.nodup rawArmRightNodup
                  have separatorNotMemRawLeft :
                      separator ∉ nextLeft :: tailLeft := by
                    have nodup := firstConnectorSimple
                    rw [leftDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).1
                  have separatorNotMemRawRight :
                      separator ∉ nextRight :: tailRight := by
                    have nodup := secondConnectorSimple
                    rw [rightDecomposition] at nodup
                    exact (List.nodup_cons.mp
                      (List.nodup_append.mp nodup).2.1).1
                  have armLeftInterior :
                      ∀ vertex ∈ armLeft,
                        vertex ∈ core ∨ vertex = separator →
                          armLeft.getLast? = some vertex := by
                    intro vertex member alternatives
                    rcases alternatives with inside | rfl
                    · rw [armLeftFirstEntry vertex member inside]
                      exact armLeftLast
                    · exact False.elim
                        (separatorNotMemRawLeft (armLeftPrefix.subset member))
                  have armRightInterior :
                      ∀ vertex ∈ armRight,
                        vertex ∈ core ∨ vertex = separator →
                          armRight.getLast? = some vertex := by
                    intro vertex member alternatives
                    rcases alternatives with inside | rfl
                    · rw [armRightFirstEntry vertex member inside]
                      exact armRightLast
                    · exact False.elim
                        (separatorNotMemRawRight (armRightPrefix.subset member))
                  let switchSeed : Finset object.Vertex :=
                    firstConfiguration.path.toFinset ∪
                      secondConfiguration.path.toFinset ∪
                        firstResponseSupport ∪ secondResponseSupport
                  obtain ⟨switchSupport, switchSupportEq⟩ :=
                    Option.isSome_iff_exists.mp
                      (Graph.CanonicalSupport.select?_isSome_of_connected
                        (object := object) (seed := switchSeed) objectConnected)
                  have switchSupportFacts :=
                    Graph.CanonicalSupport.mem_candidates_iff.mp
                      (Graph.CanonicalSupport.select?_mem_candidates
                        switchSupportEq)
                  have switchSeedSubset : switchSeed ⊆ switchSupport :=
                    switchSupportFacts.1
                  have switchConnected :
                      Graph.SupportComponents.Connected.ConnectedOn object
                        switchSupport :=
                    switchSupportFacts.2
                  have firstConfigurationCarriedBySwitch :
                      ∀ vertex ∈ firstConfiguration.path,
                        vertex ∈ switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    simp [switchSeed, member]
                  have secondConfigurationCarriedBySwitch :
                      ∀ vertex ∈ secondConfiguration.path,
                        vertex ∈ switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    simp [switchSeed, member]
                  have firstResponseCarriedBySwitch :
                      responseCoordinateSupport firstResponseCoordinate ⊆
                        switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    change vertex ∈
                      ((firstConfiguration.path.toFinset ∪
                          secondConfiguration.path.toFinset) ∪
                        firstResponseSupport) ∪ secondResponseSupport
                    apply Finset.mem_union_left
                    apply Finset.mem_union_right
                    rw [← firstResponseCoordinateSupport]
                    exact member
                  have secondResponseCarriedBySwitch :
                      responseCoordinateSupport secondResponseCoordinate ⊆
                        switchSupport := by
                    intro vertex member
                    apply switchSeedSubset
                    change vertex ∈
                      ((firstConfiguration.path.toFinset ∪
                          secondConfiguration.path.toFinset) ∪
                        firstResponseSupport) ∪ secondResponseSupport
                    apply Finset.mem_union_right
                    rw [← secondResponseCoordinateSupport]
                    exact member
                  have switchCarriesResponseFamily :
                      ∀ coordinate ∈ responseFamily,
                        responseCoordinateSupport coordinate ⊆
                          switchSupport := by
                    intro coordinate member
                    simp only [responseFamily, Finset.mem_insert,
                      Finset.mem_singleton] at member
                    rcases member with rfl | rfl
                    · exact firstResponseCarriedBySwitch
                    · exact secondResponseCarriedBySwitch
                  -- The star arm uses the same literal cubic switch
                  -- implication.  Its inputs are projections of the sealed
                  -- pattern and the two configurations; no quotient carrier
                  -- is constructed before the alternatives are proved.
                  have switchRoutesAtCubic :
                      ∀ (cubicDegree :
                          object.degree separator = data.threshold),
                        (∃ rootIncidence,
                          object.graph.Adj rootIncidence separator ∧
                            rootIncidence ≠ nextLeft ∧
                            rootIncidence ≠ nextRight ∧
                            ∀ neighbour,
                              object.graph.Adj separator neighbour →
                                neighbour = rootIncidence ∨
                                  neighbour = nextLeft ∨
                                    neighbour = nextRight) →
                        token ∈ ledger.presented.tokens →
                        capacity.role first.1 = role →
                        capacity.role second.1 = role →
                        Graph.FiniteObject.capacityCharge capacity.activation
                            capacity.carrier data.threshold capacity.packing
                            first.1 = some token →
                        Graph.FiniteObject.capacityCharge capacity.activation
                            capacity.carrier data.threshold capacity.packing
                            second.1 = some token →
                        (Nonempty
                            (Graph.FiniteObject.SurplusPort.PortReturn object
                              left.1 left.2 leftShoulder leftOtherShoulder) ∧
                          (¬ object.graph.Adj leftShoulder leftOtherShoulder →
                            Nonempty
                              (Graph.FiniteObject.SurplusPort.OpenPortWitness
                                object data.LengthOK left.2 leftShoulder
                                  leftOtherShoulder)) ∧
                          (object.graph.Adj leftShoulder leftOtherShoulder →
                            object.graph.Adj left.2 leftShoulder ∧
                              object.graph.Adj leftShoulder leftOtherShoulder ∧
                                object.graph.Adj leftOtherShoulder left.2)) →
                        (Nonempty
                            (Graph.FiniteObject.SurplusPort.PortReturn object
                              right.1 right.2 rightShoulder rightOtherShoulder) ∧
                          (¬ object.graph.Adj rightShoulder rightOtherShoulder →
                            Nonempty
                              (Graph.FiniteObject.SurplusPort.OpenPortWitness
                                object data.LengthOK right.2 rightShoulder
                                  rightOtherShoulder)) ∧
                          (object.graph.Adj rightShoulder rightOtherShoulder →
                            object.graph.Adj right.2 rightShoulder ∧
                              object.graph.Adj rightShoulder rightOtherShoulder ∧
                                object.graph.Adj rightOtherShoulder right.2)) →
                        (∃ initial,
                          firstConfiguration.path.head? = some initial ∧
                            initial ∈
                              Graph.CapacityPresentation.tokenSupport token) →
                        (∃ initial,
                          secondConfiguration.path.head? = some initial ∧
                            initial ∈
                              Graph.CapacityPresentation.tokenSupport token) →
                        Graph.SupportComponents.Connected.ConnectedOn object
                            switchSupport →
                        (∀ vertex ∈ firstConfiguration.path,
                          vertex ∈ switchSupport) →
                        (∀ vertex ∈ secondConfiguration.path,
                          vertex ∈ switchSupport) →
                        (∀ coordinate ∈ responseFamily,
                          responseCoordinateSupport coordinate ⊆
                            switchSupport) →
                        responseFamily ⊆ declaredResponseFamily →
                        responseFamily ⊆ baseResponseFamily →
                        (routingLabel first.1
                            (pairs first.1 firstPattern) left).2.2.2.2.1 =
                          (routingLabel second.1
                            (pairs second.1 secondPattern) right).2.2.2.2.1 →
                        routingLabel first.1 (pairs first.1 firstPattern) left =
                          routingLabel second.1
                            (pairs second.1 secondPattern) right →
                        firstResponseCoordinate ≠ secondResponseCoordinate →
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                    skip
                  have cubicSeparatorRoutes :
                      object.degree separator = data.threshold →
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                    intro cubicDegree
                    have cubicCommonPrefixNonemptyOrSparseExit :
                        firstConfiguration.path.head? =
                            some (Graph.CapacityPresentation.tokenRoot token) →
                        secondConfiguration.path.head? =
                            some (Graph.CapacityPresentation.tokenRoot token) →
                        firstConfiguration.path =
                            common ++ separator :: nextLeft :: tailLeft →
                        secondConfiguration.path =
                            common ++ separator :: nextRight :: tailRight →
                        nextLeft ≠ nextRight →
                        Graph.SparseSurplusExit
                            (Graph.MinimumDegreeAtLeast data.threshold)
                            (Graph.HasCycleWithLength data.LengthOK)
                            data.LengthOK object ∨
                          common ≠ [] := by
                      skip
                    rcases cubicCommonPrefixNonemptyOrSparseExit
                        firstConfigurationCanonicalRoot
                        secondConfigurationCanonicalRoot leftDecomposition
                        rightDecomposition nextDifferent with sparseExit |
                        commonNonempty
                    · exact sparseExit
                    let rootIncidence := common.getLast commonNonempty
                    have rootIncidenceLast :
                        common.getLast? = some rootIncidence :=
                      List.getLast?_eq_some_getLast commonNonempty
                    have rootIncidenceAdj :
                        object.graph.Adj rootIncidence separator := by
                      have chain := firstConnectorChain
                      rw [leftDecomposition] at chain
                      obtain ⟨_, _, joint⟩ := List.isChain_append.mp chain
                      exact joint rootIncidence rootIncidenceLast separator (by simp)
                    have rootIncidenceNeLeft : rootIncidence ≠ nextLeft := by
                      have nodup := firstConnectorSimple
                      rw [leftDecomposition] at nodup
                      exact (List.nodup_append.mp nodup).2.2 rootIncidence
                        (List.getLast_mem commonNonempty) nextLeft (by simp)
                    have rootIncidenceNeRight : rootIncidence ≠ nextRight := by
                      have nodup := secondConnectorSimple
                      rw [rightDecomposition] at nodup
                      exact (List.nodup_append.mp nodup).2.2 rootIncidence
                        (List.getLast_mem commonNonempty) nextRight (by simp)
                    have separatorDegreeThree :
                        object.degree separator = 3 := cubicDegree.trans cubic
                    let usedIncidences : Finset object.Vertex :=
                      {rootIncidence, nextLeft, nextRight}
                    have usedIncidencesCard : usedIncidences.card = 3 := by
                      simp [usedIncidences, rootIncidenceNeLeft,
                        rootIncidenceNeRight, nextDifferent]
                    have usedIncidencesSubset :
                        usedIncidences ⊆ object.graph.neighborFinset separator := by
                      intro neighbour member
                      simp only [usedIncidences, Finset.mem_insert,
                        Finset.mem_singleton] at member
                      rcases member with rfl | rfl | rfl
                      · exact (SimpleGraph.mem_neighborFinset _ _ _).2
                          rootIncidenceAdj.symm
                      · exact (SimpleGraph.mem_neighborFinset _ _ _).2
                          separatorNextLeftAdj
                      · exact (SimpleGraph.mem_neighborFinset _ _ _).2
                          separatorNextRightAdj
                    have neighbourCard :
                        (object.graph.neighborFinset separator).card = 3 := by
                      exact separatorDegreeThree
                    have usedIncidencesEq : usedIncidences =
                        object.graph.neighborFinset separator :=
                      Finset.eq_of_subset_of_card_le usedIncidencesSubset (by
                        rw [usedIncidencesCard, neighbourCard])
                    have cubicIncidencesExhausted :
                        ∀ neighbour, object.graph.Adj separator neighbour →
                          neighbour = rootIncidence ∨
                            neighbour = nextLeft ∨ neighbour = nextRight := by
                      intro neighbour adjacent
                      have member : neighbour ∈ usedIncidences := by
                        rw [usedIncidencesEq]
                        exact (SimpleGraph.mem_neighborFinset _ _ _).2 adjacent
                      simpa [usedIncidences] using member
                    have cubicIncidencePackage :
                        ∃ rootIncidence,
                          object.graph.Adj rootIncidence separator ∧
                            rootIncidence ≠ nextLeft ∧
                            rootIncidence ≠ nextRight ∧
                            ∀ neighbour,
                              object.graph.Adj separator neighbour →
                                neighbour = rootIncidence ∨
                                  neighbour = nextLeft ∨
                                    neighbour = nextRight :=
                      ⟨rootIncidence, rootIncidenceAdj, rootIncidenceNeLeft,
                        rootIncidenceNeRight, cubicIncidencesExhausted⟩
                    exact switchRoutesAtCubic cubicDegree
                      cubicIncidencePackage tokenMem firstAssignedRole
                      secondAssignedRole firstCapacityCharge secondCapacityCharge
                      leftPortActivation rightPortActivation
                      firstConnectorIssued secondConnectorIssued switchConnected
                      firstConfigurationCarriedBySwitch
                      secondConfigurationCarriedBySwitch
                      switchCarriesResponseFamily
                      responseFamily_subset_declared responseFamily_subset_base
                      sameBoundedPortProfileData routingLabelsEqual
                      responseCoordinatesDifferent
                  have separatorNotCubic :
                      object.degree separator ≠ data.threshold := by
                    intro cubicDegree
                    exact noSparseExit (cubicSeparatorRoutes cubicDegree)
                  have separatorHigh :
                      handoffHighDegree data object separator := by
                    exact lt_of_le_of_ne separatorMinimumDegree
                      (Ne.symm separatorNotCubic)
                  have denied : ∀ centre firstNeighbour secondNeighbour,
                      ¬ handoffAbsorbing data object capacity.packing centre
                        firstNeighbour secondNeighbour :=
                    fun _ _ _ collision => avoids
                      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                        data.degenerateClosureRejected collision)
                  let envelope :=
                    Graph.DecoratedHandoff.envelopeOfFirstSeparator core
                      separator nextLeft nextRight nextDifferent
                      separatorNextLeftAdj separatorNextRightAdj
                      armLeft armRight armLeftIssued armRightIssued
                      armLeftChain armRightChain
                      armLeftNodup armRightNodup
                      ⟨firstTerminal, armLeftLast, firstTerminalInside⟩
                      ⟨secondTerminal, armRightLast, secondTerminalInside⟩
                      armLeftInterior armRightInterior separatorHigh avoids
                      (denied _ _ _) (denied _ _ _)
                  have envelopeCore : envelope.core = core := rfl
                  have decorated : envelope.decorations.Nonempty := by
                    simp [envelope,
                      Graph.DecoratedHandoff.envelopeOfFirstSeparator]
                  exact Or.inr
                    (handoff_of_envelope core envelope envelopeCore decorated)
          exact routedOutcome
          ⟩
      let handoff : (K .typeBHandoff).At inputs.current := ⟨by
          obtain ⟨active, _, _, _pattern, outcome⟩ := routing.down
          rcases outcome with sparseExit | typeBHandoff
          · exact False.elim
              (active.survives sparseExit)
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
      let capacityFact := (previous.get (K .capacityTokenLedger)).down
      let active := capacityFact.choose
      let capacity := capacityFact.choose_spec.choose
      let capacityProperties := capacityFact.choose_spec.choose_spec
      have activationEq := capacityProperties.1
      have primitiveEq := capacityProperties.2.1
      have primitiveLe := capacityProperties.2.2.1
      have concrete := capacityProperties.2.2.2.1
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
