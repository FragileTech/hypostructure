import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[180]`'s accepted cycle is incompatible with the selected
counterexample fact already present on the same ExactLedger. -/
noncomputable instance instIncompatibleSelectionPairPowerOfTwoCycle :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .pairPowerOfTwoCycle) where
  contradiction := fun _current selection cycle =>
    selection.down.1 cycle.down

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
      obtain ⟨active, declared, activationEq, certified, token, role, tokenMem,
        _selected, rest⟩ := (previous.get (K .sparsePressureOverload)).down
      let ledger := certified.ledger
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence =>
          exact ⟨.inl ⟨active, declared, activationEq, certified, token, role,
            tokenMem, classified, rest⟩⟩
      | remainderSurplus =>
          exact ⟨.inr ⟨active, declared, activationEq, certified, token, role,
            tokenMem, by simpa [ledger, classified], rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨active, declared, activationEq, certified, token, role,
            tokenMem, by simpa [ledger, classified], rest⟩⟩))
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
                _survives, _realization, demand, deficitLe, entropy⟩ :=
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
          data.threshold data.windowOrder data.surplusScale data.routingLabelBound
          declared .windowIncidence :=
        routed.choose_spec.choose_spec.2
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          data.surplusScale data.routingLabelBound declared
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        let capacityFact := (inputs.get (K .capacityTokenLedger)).down
        let capacityProperties := capacityFact.choose_spec.choose_spec
        have connectedOn :
            Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object inputs.current.object.vertexFinset :=
          capacityProperties.2.2.2.2
        obtain ⟨certified, token, role, tokenMem, selected, positive,
            absorbs, quantitativePattern⟩ := overload
        let ledger := certified.ledger
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
        refine ⟨certified, token, role, tokenMem, positive, absorbs,
          quantitativePattern, .windowIncidence, selected,
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
          data.threshold data.windowOrder data.surplusScale data.routingLabelBound
          declared .remainderSurplus :=
        routed.choose_spec.choose_spec.2
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          data.surplusScale data.routingLabelBound declared
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        let capacityFact := (inputs.get (K .capacityTokenLedger)).down
        let capacityProperties := capacityFact.choose_spec.choose_spec
        have connectedOn :
            Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object inputs.current.object.vertexFinset :=
          capacityProperties.2.2.2.2
        obtain ⟨certified, token, role, tokenMem, selected, positive,
            absorbs, quantitativePattern⟩ := overload
        let ledger := certified.ledger
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
        refine ⟨certified, token, role, tokenMem, positive, absorbs,
          quantitativePattern, .remainderSurplus, selected,
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
          data.threshold data.windowOrder data.surplusScale data.routingLabelBound
          declared .primitiveCarrier :=
        routed.choose_spec.choose_spec.2
      let pattern : Graph.HomogeneousBottleneckPatternStatement
          inputs.current.object data.threshold data.windowOrder
          data.surplusScale data.routingLabelBound declared
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) := by
        classical
        let capacityFact := (inputs.get (K .capacityTokenLedger)).down
        let capacityProperties := capacityFact.choose_spec.choose_spec
        have connectedOn :
            Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object inputs.current.object.vertexFinset :=
          capacityProperties.2.2.2.2
        obtain ⟨certified, token, role, tokenMem, selected, positive,
            absorbs, quantitativePattern⟩ := overload
        let ledger := certified.ledger
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
        refine ⟨certified, token, role, tokenMem, positive, absorbs,
          quantitativePattern, .primitiveCarrier, selected,
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
parallel and cubic-switch cases construct their attempted declared quotient
locally on the connected support already proved in the case, and route it
through the framework's target-defect/compression/delocalization alternatives.
The row publishes only the paper's literal sparse-exit-or-Type-B conclusion.
No selector, callback, route record, or side carrier is postulated. -/

set_option maxHeartbeats 4000000 in
@[reducible] noncomputable def sameTokenBottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenBottleneckRouting
    { Requires := [K .homogeneousBottleneckPattern,
        K .activeSurplusDemands,
        K .cubicBaseline, K .capacityTokenLedger, K .selection,
        K .degreeProfileFibres, K .targetCompleteContextUniversality,
        K .replacementExclusion, K .uncompressible]
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
          have selection := (inputs.get (K .selection)).down
          have degreeProfileFibres :=
            (inputs.get (K .degreeProfileFibres)).down
          have contextUniversality :=
            (inputs.get (K .targetCompleteContextUniversality)).down
          have replacementExclusion :=
            (inputs.get (K .replacementExclusion)).down
          have uncompressible := (inputs.get (K .uncompressible)).down
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
          obtain ⟨certified, token, role, tokenMem, _positiveCoupledExcess,
              _multiplicityBound, _quantitativePattern, _sourceClass,
              _sourceClassEq, root, rootEq, structured⟩ := concretePattern
          let ledger := certified.ledger
          letI : Nonempty object.Vertex := ⟨root⟩

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
              SameTokenTypeBHandoffEnvelopeStatement data object := by
            refine ⟨capacity.packing, capacity.packingValid,
              capacity.packingMaximal, core, envelope, envelopeCore,
              decorated⟩

          -- The paper's cubic switch uses exactly three incidences at the first
          -- separator.  When the registered common prefix is nonempty, its last
          -- edge supplies the blocker-side incidence.  Immediate divergence at
          -- the token root is the same finite incidence calculation: the two
          -- registered next edges occupy two distinct neighbours and cubicity
          -- supplies the unique remaining neighbour.  Keeping this calculation
          -- here avoids assuming a nonempty prefix that the current connector
          -- schema does not promise.
          have cubicThirdIncidence
              (separator nextLeft nextRight : object.Vertex)
              (nextLeftAdj : object.graph.Adj separator nextLeft)
              (nextRightAdj : object.graph.Adj separator nextRight)
              (nextDifferent : nextLeft ≠ nextRight)
              (cubicDegree : object.degree separator = data.threshold) :
              ∃ rootIncidence,
                object.graph.Adj rootIncidence separator ∧
                  rootIncidence ≠ nextLeft ∧
                  rootIncidence ≠ nextRight ∧
                  ∀ neighbour,
                    object.graph.Adj separator neighbour →
                      neighbour = rootIncidence ∨
                        neighbour = nextLeft ∨ neighbour = nextRight := by
            let usedNext : Finset object.Vertex := {nextLeft, nextRight}
            have usedNextCard : usedNext.card = 2 := by
              simp [usedNext, nextDifferent]
            have usedNextSubset :
                usedNext ⊆ object.graph.neighborFinset separator := by
              intro neighbour member
              simp only [usedNext, Finset.mem_insert, Finset.mem_singleton] at member
              rcases member with rfl | rfl
              · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextLeftAdj
              · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextRightAdj
            have neighbourCard :
                (object.graph.neighborFinset separator).card = 3 := by
              exact cubicDegree.trans cubic
            have remaining : ∃ rootIncidence,
                rootIncidence ∈ object.graph.neighborFinset separator ∧
                  rootIncidence ∉ usedNext := by
              by_contra absent
              push_neg at absent
              have allUsed : object.graph.neighborFinset separator ⊆ usedNext := by
                intro neighbour member
                exact absent neighbour member
              have counted := Finset.card_le_card allUsed
              rw [neighbourCard, usedNextCard] at counted
              omega
            obtain ⟨rootIncidence, rootMember, rootFresh⟩ := remaining
            have rootAdj : object.graph.Adj rootIncidence separator :=
              ((SimpleGraph.mem_neighborFinset _ _ _).1 rootMember).symm
            have rootNeLeft : rootIncidence ≠ nextLeft := by
              intro equal
              apply rootFresh
              simp [usedNext, equal]
            have rootNeRight : rootIncidence ≠ nextRight := by
              intro equal
              apply rootFresh
              simp [usedNext, equal]
            let usedIncidences : Finset object.Vertex :=
              {rootIncidence, nextLeft, nextRight}
            have usedIncidencesCard : usedIncidences.card = 3 := by
              simp [usedIncidences, rootNeLeft, rootNeRight, nextDifferent]
            have usedIncidencesSubset :
                usedIncidences ⊆ object.graph.neighborFinset separator := by
              intro neighbour member
              simp only [usedIncidences, Finset.mem_insert,
                Finset.mem_singleton] at member
              rcases member with rfl | rfl | rfl
              · exact rootMember
              · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextLeftAdj
              · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextRightAdj
            have usedIncidencesEq : usedIncidences =
                object.graph.neighborFinset separator :=
              Finset.eq_of_subset_of_card_le usedIncidencesSubset (by
                rw [usedIncidencesCard, neighbourCard])
            refine ⟨rootIncidence, rootAdj, rootNeLeft, rootNeRight, ?_⟩
            intro neighbour adjacent
            have member : neighbour ∈ usedIncidences := by
              rw [usedIncidencesEq]
              exact (SimpleGraph.mem_neighborFinset _ _ _).2 adjacent
            simpa [usedIncidences] using member

          have cubicIncidenceOfSeparation
              (firstPath secondPath common : List object.Vertex)
              (separator nextLeft nextRight : object.Vertex)
              (tailLeft tailRight : List object.Vertex)
              (firstChain : firstPath.IsChain object.graph.Adj)
              (secondChain : secondPath.IsChain object.graph.Adj)
              (firstNodup : firstPath.Nodup)
              (secondNodup : secondPath.Nodup)
              (leftDecomposition :
                firstPath = common ++ separator :: nextLeft :: tailLeft)
              (rightDecomposition :
                secondPath = common ++ separator :: nextRight :: tailRight)
              (nextDifferent : nextLeft ≠ nextRight)
              (cubicDegree : object.degree separator = data.threshold) :
              ∃ rootIncidence,
                object.graph.Adj rootIncidence separator ∧
                  rootIncidence ≠ nextLeft ∧
                  rootIncidence ≠ nextRight ∧
                  ∀ neighbour,
                    object.graph.Adj separator neighbour →
                      neighbour = rootIncidence ∨
                        neighbour = nextLeft ∨ neighbour = nextRight := by
            have nextLeftAdj : object.graph.Adj separator nextLeft := by
              have chain := firstChain
              rw [leftDecomposition] at chain
              obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
              exact (List.isChain_cons.mp rest).1 nextLeft (by simp)
            have nextRightAdj : object.graph.Adj separator nextRight := by
              have chain := secondChain
              rw [rightDecomposition] at chain
              obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
              exact (List.isChain_cons.mp rest).1 nextRight (by simp)
            by_cases commonEmpty : common = []
            · exact cubicThirdIncidence separator nextLeft nextRight nextLeftAdj
                nextRightAdj nextDifferent cubicDegree
            · let rootIncidence := common.getLast commonEmpty
              have rootIncidenceLast :
                  common.getLast? = some rootIncidence :=
                List.getLast?_eq_some_getLast commonEmpty
              have rootIncidenceAdj :
                  object.graph.Adj rootIncidence separator := by
                have chain := firstChain
                rw [leftDecomposition] at chain
                obtain ⟨_, _, joint⟩ := List.isChain_append.mp chain
                exact joint rootIncidence rootIncidenceLast separator (by simp)
              have rootIncidenceNeLeft : rootIncidence ≠ nextLeft := by
                have nodup := firstNodup
                rw [leftDecomposition] at nodup
                exact (List.nodup_append.mp nodup).2.2 rootIncidence
                  (List.getLast_mem commonEmpty) nextLeft (by simp)
              have rootIncidenceNeRight : rootIncidence ≠ nextRight := by
                have nodup := secondNodup
                rw [rightDecomposition] at nodup
                exact (List.nodup_append.mp nodup).2.2 rootIncidence
                  (List.getLast_mem commonEmpty) nextRight (by simp)
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
                · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextLeftAdj
                · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextRightAdj
              have neighbourCard :
                  (object.graph.neighborFinset separator).card = 3 :=
                cubicDegree.trans cubic
              have usedIncidencesEq : usedIncidences =
                  object.graph.neighborFinset separator :=
                Finset.eq_of_subset_of_card_le usedIncidencesSubset (by
                  rw [usedIncidencesCard, neighbourCard])
              refine ⟨rootIncidence, rootIncidenceAdj, rootIncidenceNeLeft,
                rootIncidenceNeRight, ?_⟩
              intro neighbour adjacent
              have member : neighbour ∈ usedIncidences := by
                rw [usedIncidencesEq]
                exact (SimpleGraph.mem_neighborFinset _ _ _).2 adjacent
              simpa [usedIncidences] using member

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

          -- Route one actual declared identification by the framework theorem
          -- implementing `def:admissible-rank-quotient`.  The first arm is
          -- excluded by the registered common boundary-degree fibre; the
          -- remaining three arms are exactly sparse exits (b)--(d).  No case
          -- of `AttemptedQuotient.route` is reproved here.
          have routeAttemptedIdentification
              {family : Finset (Graph.FiniteObject.PairCoordinate object)}
              {coordinateSupport :
                Graph.FiniteObject.PairCoordinate object →
                  Finset object.Vertex}
              (attempt : Graph.AttemptedQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                object family coordinateSupport)
              (reducing : ¬ Set.InjOn attempt.label ↑family)
              (sameFibre : ∀ left right,
                attempt.Identifies left right →
                  left.boundaryDegreeProfile =
                    right.boundaryDegreeProfile) :
              Graph.SparseSurplusExit
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                data.LengthOK object := by
            rcases attempt.route reducing with
              profiles | defect | replacement |
                ⟨representative, smaller, baseline, transfer⟩
            · obtain ⟨leftPiece, rightPiece, identified, different⟩ :=
                profiles
              exact False.elim
                (different (sameFibre leftPiece rightPiece identified))
            · obtain ⟨leftPiece, rightPiece, identified, targetDefect⟩ :=
                defect
              exact .targetDefect (family := family)
                (coordinateSupport := coordinateSupport) (attempt := attempt)
                (reducing := reducing) leftPiece rightPiece identified
                targetDefect
            · exact .compression attempt.support replacement
            · exact .delocalization representative smaller baseline transfer

          -- Construct the manuscript's attempted same-token identification on
          -- the literal connected support that carries the two response
          -- coordinates.  The quotient records the common boundary-degree
          -- fibre.  To verify its conditional admissibility clauses, compare
          -- the support's own piece with the same piece after adjoining one
          -- disjoint accepted quadrilateral.  The boundary profile is
          -- unchanged, while the actual outside reconstructs the avoided
          -- object on the source side and the augmented side contains the
          -- registered quadrilateral.  Thus target-completeness would be
          -- contradictory, and `AttemptedQuotient.route` returns precisely
          -- the paper's target-defective sparse exit.
          have attemptedResponseQuotient
              {family : Finset (Graph.FiniteObject.PairCoordinate object)}
              {coordinateSupport :
                Graph.FiniteObject.PairCoordinate object →
                  Finset object.Vertex}
              (support : Finset object.Vertex)
              (connected :
                Graph.SupportComponents.Connected.ConnectedOn object support)
              (carries : ∀ coordinate ∈ family,
                coordinateSupport coordinate ⊆ support)
              (anchor firstCoordinate secondCoordinate :
                Graph.FiniteObject.PairCoordinate object)
              (anchorMem : anchor ∈ family) :
              ∃ attempt : Graph.AttemptedQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK)
                  object family coordinateSupport,
                attempt.support = support ∧
                  attempt.label firstCoordinate =
                    attempt.label secondCoordinate ∧
                  ∀ leftPiece rightPiece,
                    attempt.Identifies leftPiece rightPiece →
                      leftPiece.boundaryDegreeProfile =
                        rightPiece.boundaryDegreeProfile := by
            let boundary :=
              Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
                object support
            let source :=
              Graph.Strategy.InterfaceReplacement.SupportAtom.piece
                object support
            let Four : Type u := ULift.{u} (Fin 4)
            let oldEmbedding :
                (boundary.Vertex ⊕ source.Internal) ↪
                  (boundary.Vertex ⊕ (source.Internal ⊕ Four)) :=
              { toFun := fun vertex =>
                  match vertex with
                  | .inl label => .inl label
                  | .inr internal => .inr (.inl internal)
                inj' := by
                  intro firstVertex secondVertex equal
                  cases firstVertex <;> cases secondVertex <;> simp_all }
            let fourEmbedding : Four ↪
                (boundary.Vertex ⊕ (source.Internal ⊕ Four)) :=
              { toFun := fun vertex => .inr (.inr vertex)
                inj' := by
                  intro firstVertex secondVertex equal
                  simpa using equal }
            let augmented : Graph.BoundaryPiece boundary :=
              { Internal := source.Internal ⊕ Four
                internalVertices := by
                  letI : FinEnum source.Internal := source.internalVertices
                  letI : FinEnum Four := inferInstance
                  infer_instance
                graph := source.graph.map oldEmbedding ⊔
                  (⊤ : SimpleGraph Four).map fourEmbedding
                decideAdj := Classical.decRel _ }
            have profileEq : source.boundaryDegreeProfile =
                augmented.boundaryDegreeProfile := by
              funext label
              unfold Graph.BoundaryPiece.boundaryDegreeProfile
                Graph.BoundaryPiece.boundaryDegree
              rw [Graph.FiniteObject.degree_eq_ncard_neighborSet,
                Graph.FiniteObject.degree_eq_ncard_neighborSet]
              have neighbours :
                  augmented.graph.neighborSet (.inl label) =
                    oldEmbedding ''
                      source.graph.neighborSet (.inl label) := by
                ext vertex
                simp only [SimpleGraph.mem_neighborSet]
                constructor
                · intro adjacent
                  change
                    (source.graph.map oldEmbedding ⊔
                      (⊤ : SimpleGraph Four).map fourEmbedding).Adj
                        (.inl label) vertex at adjacent
                  rcases adjacent with old | square
                  · rw [SimpleGraph.map_adj] at old
                    obtain ⟨left, right, edge, leftEq, rightEq⟩ := old
                    cases left with
                    | inl leftLabel =>
                        have leftLabelEq : leftLabel = label := by
                          simpa [oldEmbedding] using leftEq
                        refine ⟨right, ?_, rightEq⟩
                        simpa [leftLabelEq] using edge
                    | inr leftInternal =>
                        simp [oldEmbedding] at leftEq
                  · rw [SimpleGraph.map_adj] at square
                    obtain ⟨left, right, _edge, leftEq, _rightEq⟩ := square
                    simp [fourEmbedding] at leftEq
                · rintro ⟨vertex, adjacent, rfl⟩
                  apply show
                    (source.graph.map oldEmbedding ⊔
                      (⊤ : SimpleGraph Four).map fourEmbedding).Adj
                        (oldEmbedding (.inl label))
                        (oldEmbedding vertex) from ?_
                  exact Or.inl ((SimpleGraph.map_adj_apply).2 adjacent)
              change
                (source.graph.neighborSet (.inl label)).ncard =
                  (augmented.graph.neighborSet (.inl label)).ncard
              rw [neighbours,
                Set.ncard_image_of_injective _ oldEmbedding.injective]
            have sourceAvoids :
                ¬ Graph.HasCycleWithLength data.LengthOK
                  (Graph.glue source
                    (Graph.Strategy.InterfaceReplacement.SupportAtom.outside
                      object support)) := by
              intro target
              apply avoids
              exact
                ((Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant.iff_of_iso
                  ⟨(Graph.Strategy.InterfaceReplacement.SupportAtom.decomposition
                    object support).reconstructionIso⟩).mp target
            have augmentedTarget :
                Graph.HasCycleWithLength data.LengthOK
                  (Graph.glue augmented
                    (Graph.Strategy.InterfaceReplacement.SupportAtom.outside
                      object support)) := by
              let zero : Four := ULift.up 0
              let one : Four := ULift.up 1
              let two : Four := ULift.up 2
              let three : Four := ULift.up 3
              have fourAdj (left right : Four) (different : left ≠ right) :
                  augmented.graph.Adj
                    (fourEmbedding left) (fourEmbedding right) := by
                apply Or.inr
                rw [SimpleGraph.map_adj_apply]
                simpa using different
              let walk : augmented.graph.Walk
                  (fourEmbedding zero) (fourEmbedding zero) :=
                .cons (fourAdj zero one (by decide))
                  (.cons (fourAdj one two (by decide))
                    (.cons (fourAdj two three (by decide))
                      (.cons (fourAdj three zero (by decide)) .nil)))
              have isCycle : walk.IsCycle := by
                dsimp only [walk]
                rw [SimpleGraph.Walk.cons_isCycle_iff]
                constructor
                · rw [SimpleGraph.Walk.isPath_def]
                  simp [zero, one, two, three, fourEmbedding]
                  all_goals decide
                · simp [zero, one, two, three, fourEmbedding]
                  all_goals decide
              let certificate :
                  Graph.CycleCertificate augmented.pack data.LengthOK :=
                { vertex := fourEmbedding zero
                  walk := walk
                  isCycle := isCycle
                  length_ok := by
                    change data.LengthOK 4
                    exact data.quadrilateralAccepted }
              exact
                ⟨certificate.mapHom (Graph.pieceHom augmented _)
                  (Graph.pieceEmbedding augmented _).injective⟩
            let attempt : Graph.AttemptedQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                object family coordinateSupport :=
              { support := support
                connected := connected
                carries := carries
                Label := PUnit
                Value := ULift.{u + 1, u}
                  (Graph.BoundaryDegreeProfile boundary)
                label := fun _ => PUnit.unit
                value := fun piece _ =>
                  ULift.up piece.boundaryDegreeProfile
                properRepresentative := by
                  intro _proper _reducing complete
                  have sameValues : ∀ coordinate ∈ family,
                      ULift.up source.boundaryDegreeProfile =
                        ULift.up augmented.boundaryDegreeProfile := by
                    intro _coordinate _member
                    exact congrArg ULift.up profileEq
                  have universal := (complete source augmented sameValues).2
                  exact
                    (sourceAvoids
                      ((universal
                        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside
                          object support)).mpr augmentedTarget)).elim
                closedRepresentative := by
                  intro _covers _reducing complete
                  have sameValues : ∀ coordinate ∈ family,
                      ULift.up source.boundaryDegreeProfile =
                        ULift.up augmented.boundaryDegreeProfile := by
                    intro _coordinate _member
                    exact congrArg ULift.up profileEq
                  have universal := (complete source augmented sameValues).2
                  exact
                    (sourceAvoids
                      ((universal
                        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside
                          object support)).mpr augmentedTarget)).elim }
            refine ⟨attempt, rfl, rfl, ?_⟩
            intro leftPiece rightPiece identified
            exact congrArg ULift.down (identified anchor anchorMem)

          -- Every recorded type-(e) obstruction already carries the exact
          -- failed-response quotient obtained at `[132]`.  Read that retained
          -- obstruction from the activation instead of constructing another
          -- quotient at `[144]`: its final disjunction is literally sparse
          -- exit (b) or sparse exit (c).  This applies even when an earlier
          -- blocker clause (a)--(d) is the pair's canonical capacity charge.
          have responseObstructionRoutes
              (pair : Finset (object.Vertex × object.Vertex))
              (coordinate : Graph.FiniteObject.PairCoordinate object)
              (obstructs : coordinate ∈
                capacity.activation.responseObstructions pair) :
              Graph.SparseSurplusExit
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                data.LengthOK object := by
            have recordedObstructs : coordinate ∈
                ((Graph.recordSparsePairDEBlockers
                  (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                  (LengthOK := data.LengthOK)
                  (Graph.pairResponseActivation active)
                  (object.portPairSchedule data.threshold)).responseObstructions
                    pair) := by
              rw [← activationEq]
              exact obstructs
            have obstruction :
                Graph.SparsePairDEResponseObstructionAt
                  (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                  (LengthOK := data.LengthOK)
                  (Graph.pairResponseActivation active)
                  (object.portPairSchedule data.threshold) pair := by
              simp only [Graph.recordSparsePairDEBlockers] at recordedObstructs
              split at recordedObstructs
              next present => exact present
              next absent => simp at recordedObstructs
            obtain ⟨attempt, _functional, reducing, _determination,
                defect | replacement⟩ := obstruction
            · obtain ⟨leftPiece, rightPiece, identified,
                targetDefect⟩ := defect
              let family := (Graph.pairResponseActivation active).pairFamily
                (object.portPairSchedule data.threshold)
              let coordinateSupport : object.PairCoordinate →
                  Finset object.Vertex := by
                letI := object.vertices.decEq
                exact Graph.DeclaredSignature.Coordinate.support
              exact .targetDefect (family := family)
                (coordinateSupport := coordinateSupport) (attempt := attempt)
                (reducing := reducing) leftPiece rightPiece identified
                targetDefect
            · exact .compression attempt.support replacement

          -- If type (e) is the canonical role, canonical-blocker membership
          -- supplies the recorded response coordinate consumed above.
          have targetResponseRoleRoutes
              (pair : Finset (object.Vertex × object.Vertex))
              (assigned : capacity.role pair = role)
              (targetRole : role.blocker =
                Graph.SameTokenBlockerRoles.BlockerKind.targetResponse) :
              Graph.SparseSurplusExit
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                data.LengthOK object := by
            have canonicalKind :
                ((Graph.FiniteObject.canonicalBlocker capacity.activation pair).map
                    Graph.FiniteObject.Blocker.kind).getD
                    .sharedDeclaredSupport = role.blocker := by
              have roleEq := congrArg
                Graph.SameTokenBlockerRoles.Role.blocker assigned
              simpa [Graph.CapacityPresentation.role,
                Graph.FiniteObject.capacityRole] using roleEq
            cases selectedBlocker :
                Graph.FiniteObject.canonicalBlocker capacity.activation pair with
            | none =>
                simp [selectedBlocker, targetRole] at canonicalKind
            | some blocker =>
                have blockerKind : Graph.FiniteObject.Blocker.kind blocker =
                    Graph.SameTokenBlockerRoles.BlockerKind.targetResponse := by
                  simpa [selectedBlocker, targetRole] using canonicalKind
                have blockerMem :=
                  Graph.FiniteObject.canonicalBlocker_mem
                    capacity.activation selectedBlocker
                cases blocker with
                | sharedDeclaredSupport item => cases blockerKind
                | sharedReturnSupport item => cases blockerKind
                | sharedLocalBuffer vertex => cases blockerKind
                | boundaryProfile coordinate => cases blockerKind
                | arithmeticChordSet chords => cases blockerKind
                | targetResponse coordinate =>
                    have obstructs : coordinate ∈
                        capacity.activation.responseObstructions pair := by
                      simpa [Graph.FiniteObject.DemandActivation.blockers] using
                        blockerMem
                    exact responseObstructionRoutes pair coordinate obstructs

          have routedOutcome :
              Graph.SparseSurplusExit
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
                    object ∨
                SameTokenTypeBHandoffEnvelopeStatement data object := by
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
              -- The parallel paragraph applies the local graph realization
              -- above to the two declared coordinates and their connected
              -- common support.  Every premise below has already been read
              -- from the ledger or derived from its declared configurations.
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
                intros
                have supportDependenceExit :
                    Graph.SparseSurplusExit
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK)
                      data.LengthOK object := by
                  have quotientRealization :
                      ∃ attempt : Graph.AttemptedQuotient
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          object responseFamily responseCoordinateSupport,
                        attempt.support = parallelSupport ∧
                          attempt.label firstResponseCoordinate =
                            attempt.label secondResponseCoordinate ∧
                          ∀ leftPiece rightPiece,
                            attempt.Identifies leftPiece rightPiece →
                              leftPiece.boundaryDegreeProfile =
                                rightPiece.boundaryDegreeProfile := by
                    exact attemptedResponseQuotient parallelSupport
                      parallelSupportConnected
                      (by
                        intro coordinate member
                        simp only [responseFamily, Finset.mem_insert,
                          Finset.mem_singleton] at member
                        rcases member with rfl | rfl
                        · exact firstResponseCarriedByParallelSupport
                        · exact secondResponseCarriedByParallelSupport)
                      firstResponseCoordinate firstResponseCoordinate
                      secondResponseCoordinate (by simp [responseFamily])
                  obtain ⟨attempt, _supportEq, identifiesCoordinates,
                      sameFibre⟩ := quotientRealization
                  have reducing :
                      ¬ Set.InjOn attempt.label ↑responseFamily := by
                    intro injective
                    apply responseCoordinatesDifferent
                    apply injective
                    · simp [responseFamily]
                    · simp [responseFamily]
                    · exact identifiesCoordinates
                  exact routeAttemptedIdentification attempt reducing sameFibre
                by_cases firstResponded : ∃ coordinate, coordinate ∈
                    capacity.activation.responseObstructions first.1
                · obtain ⟨coordinate, obstructs⟩ := firstResponded
                  exact responseObstructionRoutes first.1 coordinate obstructs
                · by_cases secondResponded : ∃ coordinate, coordinate ∈
                      capacity.activation.responseObstructions second.1
                  · obtain ⟨coordinate, obstructs⟩ := secondResponded
                    exact responseObstructionRoutes second.1 coordinate obstructs
                  · by_cases targetRole : role.blocker =
                        Graph.SameTokenBlockerRoles.BlockerKind.targetResponse
                    · exact targetResponseRoleRoutes first.1 firstAssignedRole
                        targetRole
                    · exact supportDependenceExit
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
                    intros
                    have supportDependenceExit :
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                      have quotientRealization :
                          ∃ attempt : Graph.AttemptedQuotient
                              (Graph.MinimumDegreeAtLeast data.threshold)
                              (Graph.HasCycleWithLength data.LengthOK)
                              object responseFamily responseCoordinateSupport,
                            attempt.support = switchSupport ∧
                              attempt.label firstResponseCoordinate =
                                attempt.label secondResponseCoordinate ∧
                              ∀ leftPiece rightPiece,
                                attempt.Identifies leftPiece rightPiece →
                                  leftPiece.boundaryDegreeProfile =
                                    rightPiece.boundaryDegreeProfile := by
                        exact attemptedResponseQuotient switchSupport
                          switchConnected switchCarriesResponseFamily
                          firstResponseCoordinate firstResponseCoordinate
                          secondResponseCoordinate (by simp [responseFamily])
                      obtain ⟨attempt, _supportEq, identifiesCoordinates,
                          sameFibre⟩ := quotientRealization
                      have reducing :
                          ¬ Set.InjOn attempt.label ↑responseFamily := by
                        intro injective
                        apply responseCoordinatesDifferent
                        apply injective
                        · simp [responseFamily]
                        · simp [responseFamily]
                        · exact identifiesCoordinates
                      exact routeAttemptedIdentification attempt reducing sameFibre
                    by_cases firstResponded : ∃ coordinate, coordinate ∈
                        capacity.activation.responseObstructions first.1
                    · obtain ⟨coordinate, obstructs⟩ := firstResponded
                      exact responseObstructionRoutes first.1 coordinate obstructs
                    · by_cases secondResponded : ∃ coordinate, coordinate ∈
                          capacity.activation.responseObstructions second.1
                      · obtain ⟨coordinate, obstructs⟩ := secondResponded
                        exact responseObstructionRoutes second.1 coordinate obstructs
                      · by_cases targetRole : role.blocker =
                            Graph.SameTokenBlockerRoles.BlockerKind.targetResponse
                        · exact targetResponseRoleRoutes first.1
                            firstAssignedRole targetRole
                        · exact supportDependenceExit
                  have cubicSeparatorRoutes :
                      object.degree separator = data.threshold →
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                    intro cubicDegree
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
                      cubicIncidenceOfSeparation firstConfiguration.path
                        secondConfiguration.path common separator nextLeft
                        nextRight tailLeft tailRight firstConnectorChain
                        secondConnectorChain firstConnectorSimple
                        secondConnectorSimple leftDecomposition rightDecomposition
                        nextDifferent cubicDegree
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
              -- The star arm consumes the same local graph-realized
              -- parallel-identification implication as the matching arm.
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
                intros
                have supportDependenceExit :
                    Graph.SparseSurplusExit
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK)
                      data.LengthOK object := by
                  have quotientRealization :
                      ∃ attempt : Graph.AttemptedQuotient
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          object responseFamily responseCoordinateSupport,
                        attempt.support = parallelSupport ∧
                          attempt.label firstResponseCoordinate =
                            attempt.label secondResponseCoordinate ∧
                          ∀ leftPiece rightPiece,
                            attempt.Identifies leftPiece rightPiece →
                              leftPiece.boundaryDegreeProfile =
                                rightPiece.boundaryDegreeProfile := by
                    exact attemptedResponseQuotient parallelSupport
                      parallelSupportConnected
                      (by
                        intro coordinate member
                        simp only [responseFamily, Finset.mem_insert,
                          Finset.mem_singleton] at member
                        rcases member with rfl | rfl
                        · exact firstResponseCarriedByParallelSupport
                        · exact secondResponseCarriedByParallelSupport)
                      firstResponseCoordinate firstResponseCoordinate
                      secondResponseCoordinate (by simp [responseFamily])
                  obtain ⟨attempt, _supportEq, identifiesCoordinates,
                      sameFibre⟩ := quotientRealization
                  have reducing :
                      ¬ Set.InjOn attempt.label ↑responseFamily := by
                    intro injective
                    apply responseCoordinatesDifferent
                    apply injective
                    · simp [responseFamily]
                    · simp [responseFamily]
                    · exact identifiesCoordinates
                  exact routeAttemptedIdentification attempt reducing sameFibre
                by_cases firstResponded : ∃ coordinate, coordinate ∈
                    capacity.activation.responseObstructions first.1
                · obtain ⟨coordinate, obstructs⟩ := firstResponded
                  exact responseObstructionRoutes first.1 coordinate obstructs
                · by_cases secondResponded : ∃ coordinate, coordinate ∈
                      capacity.activation.responseObstructions second.1
                  · obtain ⟨coordinate, obstructs⟩ := secondResponded
                    exact responseObstructionRoutes second.1 coordinate obstructs
                  · by_cases targetRole : role.blocker =
                        Graph.SameTokenBlockerRoles.BlockerKind.targetResponse
                    · exact targetResponseRoleRoutes first.1 firstAssignedRole
                        targetRole
                    · exact supportDependenceExit
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
                    intros
                    have supportDependenceExit :
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                      have quotientRealization :
                          ∃ attempt : Graph.AttemptedQuotient
                              (Graph.MinimumDegreeAtLeast data.threshold)
                              (Graph.HasCycleWithLength data.LengthOK)
                              object responseFamily responseCoordinateSupport,
                            attempt.support = switchSupport ∧
                              attempt.label firstResponseCoordinate =
                                attempt.label secondResponseCoordinate ∧
                              ∀ leftPiece rightPiece,
                                attempt.Identifies leftPiece rightPiece →
                                  leftPiece.boundaryDegreeProfile =
                                    rightPiece.boundaryDegreeProfile := by
                        exact attemptedResponseQuotient switchSupport
                          switchConnected switchCarriesResponseFamily
                          firstResponseCoordinate firstResponseCoordinate
                          secondResponseCoordinate (by simp [responseFamily])
                      obtain ⟨attempt, _supportEq, identifiesCoordinates,
                          sameFibre⟩ := quotientRealization
                      have reducing :
                          ¬ Set.InjOn attempt.label ↑responseFamily := by
                        intro injective
                        apply responseCoordinatesDifferent
                        apply injective
                        · simp [responseFamily]
                        · simp [responseFamily]
                        · exact identifiesCoordinates
                      exact routeAttemptedIdentification attempt reducing sameFibre
                    by_cases firstResponded : ∃ coordinate, coordinate ∈
                        capacity.activation.responseObstructions first.1
                    · obtain ⟨coordinate, obstructs⟩ := firstResponded
                      exact responseObstructionRoutes first.1 coordinate obstructs
                    · by_cases secondResponded : ∃ coordinate, coordinate ∈
                          capacity.activation.responseObstructions second.1
                      · obtain ⟨coordinate, obstructs⟩ := secondResponded
                        exact responseObstructionRoutes second.1 coordinate obstructs
                      · by_cases targetRole : role.blocker =
                            Graph.SameTokenBlockerRoles.BlockerKind.targetResponse
                        · exact targetResponseRoleRoutes first.1
                            firstAssignedRole targetRole
                        · exact supportDependenceExit
                  have cubicSeparatorRoutes :
                      object.degree separator = data.threshold →
                        Graph.SparseSurplusExit
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          data.LengthOK object := by
                    intro cubicDegree
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
                      cubicIncidenceOfSeparation firstConfiguration.path
                        secondConfiguration.path common separator nextLeft
                        nextRight tailLeft tailRight firstConnectorChain
                        secondConnectorChain firstConnectorSimple
                        secondConnectorSimple leftDecomposition rightDecomposition
                        nextDifferent cubicDegree
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
          obtain ⟨active, capacity, activationEq, pattern, outcome⟩ := routing.down
          rcases outcome with sparseExit | typeBHandoff
          · exact False.elim
              (active.survives sparseExit)
          · exact ⟨active, capacity, activationEq, pattern, typeBHandoff⟩⟩
      .cons (key := K .bottleneckRouting)
        routing
        (.cons (key := K .typeBHandoff) handoff .nil))

/-- **Node `[65]`, the literal same-token Type B handoff lane.**  Read the
decorated envelope produced at `[144]` from the current `ExactLedger` and append
the common Type B entry for those same objects.  The packing, core, envelope,
decorations, and all arm/fan-safety fields are retained verbatim; this row does
not manufacture a canonical negative component or an indexed cold-corridor
carrier. -/
@[reducible] noncomputable def sameTokenTypeBFanEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenTypeBFanEntry
    { Requires := [K .typeBHandoff]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let handoff := (inputs.get (K .typeBHandoff)).down
      .cons (key := K .typeBFanEntry)
        ⟨by
          obtain ⟨_active, _capacity, _activationEq, _pattern, envelope⟩ := handoff
          apply Or.inr
          apply Or.inr
          exact envelope⟩
        .nil)

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

/-- Node `[125]`, `def:named-surplus-exits`: test the paper's five named
sparse-surplus exits on the literal incoming ledger.  The left arm publishes
the concrete exit; the right arm publishes exactly its negation, namely that
the current object survives all five exits.  This is the manuscript's
"after sparse exits" branch point: selection and replacement facts are not
re-proved here.  Every target-defect inhabitant retains the concrete
rank-reducing attempted quotient supplied by its originating residual; no
arbitrary boundary defect or `DeclaredQuotient` is fabricated here. -/
noncomputable def sparseSurplusSurvivorDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (exitFresh : K .sparsePairExit ∉ known)
    (survivorFresh : K .sparseSurplusSurvivor ∉ known) :
    Decision (K .sparsePairExit) (K .sparseSurplusSurvivor) previous :=
  Decision.run previous (K .sparsePairExit) (K .sparseSurplusSurvivor)
    `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivorDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePairExit).At current ⊕
          (K .sparseSurplusSurvivor).At current) from by
      by_cases exit : Graph.SparseSurplusExit
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK current.object
      · exact ⟨.inl ⟨exit⟩⟩
      · exact ⟨.inr ⟨exit⟩⟩))
    exitFresh survivorFresh

/-- Node `[125]`, named sparse-exit routing.  Four constructors are literal
terminals against facts already present in the incoming residual.  The
target-defect constructor alone survives, retaining its concrete attempted
quotient as the paper's target-defect handoff. -/
@[reducible] noncomputable def sparseSurplusExitRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusExitRouting
    { Requires := [K .sparsePairExit, K .selection,
        K .replacementExclusion]
      Produces := [K .sparseTargetDefectResidual]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let exit := (inputs.get (K .sparsePairExit)).down
      let selected := (inputs.get (K .selection)).down
      let replacementExcluded :=
        (inputs.get (K .replacementExclusion)).down
      .cons (key := K .sparseTargetDefectResidual)
        (show Value BranchState Presentation presentation data
            .sparseTargetDefectResidual inputs.current from ⟨by
          cases exit with
          | dyadic cycle =>
              exact (selected.1 cycle).elim
          | targetDefect family coordinateSupport attempt reducing reduced full
              identified defect =>
              exact ⟨_, family, coordinateSupport, attempt, reducing,
                reduced, full, identified, defect⟩
          | compression support replacement =>
              exact (replacementExcluded support replacement).elim
          | delocalization representative smaller baseline transfer =>
              exact (selected.1
                (transfer (selected.2 representative smaller baseline))).elim
          | suppressionChord family certificate violates =>
              let expanded := family.expandCycle certificate
              have accepted : data.LengthOK expanded.walk.length := by
                rw [expanded.length_eq]
                exact violates
              have cycle : Graph.HasCycleWithLength data.LengthOK
                  inputs.current.object :=
                ⟨⟨family.sourceVertex certificate.vertex, expanded.walk,
                  expanded.isCycle, accepted⟩⟩
              exact (selected.1 cycle).elim⟩)
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
  have survives := properties.1
  have realization : Nonempty
      (Graph.BaselineCodeRealization current.object family) := properties.2.1
  have demand : Graph.cubicBaselineBudget current.object.vertexCount
      data.threshold ≤ 2 ^ (family.card + Graph.spineDeficit
        current.object.vertexCount data.threshold family.card) := properties.2.2.1
  have deficitBound : Graph.spineDeficit current.object.vertexCount
      data.threshold family.card ≤ data.surplusScale * current.object.vertexCount :=
    properties.2.2.2
  let pairFacts := (previous.get (K .independentPairFamily)).down
  let active := Classical.choose pairFacts
  let activation := Graph.pairResponseActivation active
  let pairs := current.object.portPairSchedule data.threshold
  let responses := activation.pairFamily pairs
  have pairBlockerFree : ¬ Graph.HasSparsePairDEBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation pairs :=
    Classical.choose_spec pairFacts
  have responseCard : responses.card =
      (current.object.degreeSurplus data.threshold).choose 2 := by
    rw [Graph.FiniteObject.DemandActivation.card_pairFamily]
    exact current.object.card_portPairSchedule fun vertex =>
      le_trans current.baseline (current.object.minDegree_le_degree vertex)
  let entropy : Prop :=
    2 ^ (family.card + responses.card) ≤ Graph.skeletonBudget current.object
  exact Decision.run previous (K .freePairEntropySandwich)
    (K .freePairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.freePairEntropyDichotomy
    (if realized : entropy then
      let count :
          2 ^ (family.card +
              (current.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget current.object := by
        simpa only [entropy, responseCard] using realized
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
        ⟨Coordinate, family, coordinateSupport, survives, realization, demand,
          deficitBound, count, sandwich⟩
      .inl ⟨result⟩
    else
      let countFailure :
          ¬ 2 ^ (family.card +
              (current.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget current.object := by
        simpa only [entropy, responseCard] using realized
      have scheduleCard : pairs.card =
          (current.object.degreeSurplus data.threshold).choose 2 :=
        current.object.card_portPairSchedule fun vertex =>
          le_trans current.baseline
            (current.object.minDegree_le_degree vertex)
      have countFailureOnSchedule :
          ¬ 2 ^ (family.card + pairs.card) ≤
            Graph.skeletonBudget current.object := by
        simpa only [scheduleCard] using countFailure
      let baselineRealization := Classical.choice realization
      have pairsNonempty : pairs.Nonempty :=
        freeSide_nonempty_of_baseline_realized baselineRealization
          countFailureOnSchedule
      let firstWitness :
          FirstFailedPairExtension current.object family pairs :=
        firstFailedPairExtensionOf baselineRealization countFailureOnSchedule
      let result : FreePairCodeUnrealizedStatement data current.object :=
        ⟨active, Coordinate, family, coordinateSupport, pairBlockerFree,
          survives, realization, demand, deficitBound, scheduleCard,
          countFailureOnSchedule, pairsNonempty, ⟨firstWitness⟩⟩
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
            obtain ⟨Coordinate, family, coordinateSupport, _survives,
              _realization, demand, deficitLe, entropy, _sandwich⟩ :=
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

/-- Node `[137]`: assemble the exact token map, canonical pair schedule, and
node-`[129]` baseline realization through their ledger keys before deciding the
free-side entropy count. -/
@[reducible] noncomputable def blockedPairEntropySetupRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairEntropySetup
    { Requires := [K .capacityTokenLedger, K .canonicalPairLedger,
        K .baselineSpineDemand]
      Produces := [K .blockedPairEntropySetup]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedPairEntropySetup)
        (show Value BranchState Presentation presentation data
            .blockedPairEntropySetup inputs.current from
          ⟨by
            let capacityFact :=
              (inputs.get (K .capacityTokenLedger)).down
            let active := capacityFact.choose
            let capacity := capacityFact.choose_spec.choose
            let capacityProperties := capacityFact.choose_spec.choose_spec
            have activationEq := capacityProperties.1
            have primitiveEq := capacityProperties.2.1
            have primitiveLe := capacityProperties.2.2.1
            have concrete := capacityProperties.2.2.2.1
            obtain ⟨_activePairFamily, _blockerCertificate, _pairsEq,
                scheduleCard, _partition, _incidence, _multiplicity,
                _blocked⟩ :=
              (inputs.get (K .canonicalPairLedger)).down
            obtain ⟨_active, Coordinate, family, coordinateSupport,
                properties⟩ :=
              (inputs.get (K .baselineSpineDemand)).down
            exact ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
              concrete, scheduleCard, Coordinate, family, coordinateSupport,
              properties⟩⟩)
        .nil)

/-- Node `[137]`: decide the free-side entropy count from the exact setup
assembled by `blockedPairEntropySetupRow`. -/
noncomputable def blockedPairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .blockedPairEntropySetup) known]
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
          concrete, scheduleCard, Coordinate, family, coordinateSupport,
          properties⟩ :=
        (previous.get (K .blockedPairEntropySetup)).down
      have survives := properties.1
      have realizationExists : Nonempty
          (Graph.BaselineCodeRealization current.object family) := properties.2.1
      have demand : Graph.cubicBaselineBudget current.object.vertexCount
          data.threshold ≤ 2 ^ (family.card + Graph.spineDeficit
            current.object.vertexCount data.threshold family.card) := properties.2.2.1
      have deficitBound : Graph.spineDeficit current.object.vertexCount
          data.threshold family.card ≤ data.surplusScale * current.object.vertexCount :=
        properties.2.2.2
      let realization := Classical.choice realizationExists
      let free := Graph.freeSide current.object.vertexPairDecidableEq
        (current.object.portPairSchedule data.threshold)
        capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable
      let count : Prop :=
        2 ^ (family.card + free.card) ≤
          Graph.skeletonBudget current.object
      exact if realized : count then
        ⟨.inl ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives, realizationExists,
          demand, deficitBound, realized⟩⟩
      else
        have freeNonempty : free.Nonempty :=
          freeSide_nonempty_of_baseline_realized realization realized
        let firstWitness : FirstFailedPairExtension current.object family free :=
          firstFailedPairExtensionOf realization realized
        ⟨.inr ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives,
          realizationExists, demand, deficitBound, realized, freeNonempty,
          ⟨firstWitness⟩⟩⟩))
    sandwichFresh unrealizedFresh

/-! ## Node `[178]`: normalize the first failed pair extension

The two count-failure routes retain different pair sets, but both now carry
the same mathematical datum: an actually realized baseline code and the least
pair extension at which the mixed count fails.  These rows read that witness
from the route's exact key and attach the failed pair's canonical connected
response support `X_π`. -/

/-- Node `[178]` on the full pair schedule selected at `[131]`. -/
@[reducible] noncomputable def freePairOverlapFirstFailureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairOverlapFirstFailure
    { Requires := [K .freePairCodeUnrealized, K .noProperBaseline]
      Produces := [K .pairOverlapFirstFailure]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapFirstFailure)
        (show Value BranchState Presentation presentation data
            .pairOverlapFirstFailure inputs.current from
          ⟨by
            obtain ⟨active, Coordinate, family, coordinateSupport,
                blockerFree, _survives, realizationExists, _demand, _deficitBound,
                _scheduleCard, _countFailure, pairSetNonempty,
                firstFailureExists⟩ :=
              (inputs.get (K .freePairCodeUnrealized)).down
            let realization := Classical.choice realizationExists
            let firstFailure := Classical.choice firstFailureExists
            exact ⟨PairOverlapFirstFailure.of data inputs.current.object active
              Coordinate family coordinateSupport realization
              (inputs.current.object.portPairSchedule data.threshold)
              pairSetNonempty (by intro pair member; exact member)
              (by
                intro pair pairMem
                constructor
                · intro obstruction
                  exact blockerFree ⟨pair, pairMem, Or.inl obstruction⟩
                · intro obstruction
                  exact blockerFree ⟨pair, pairMem, Or.inr obstruction⟩)
              firstFailure
              (inputs.get (K .noProperBaseline)).down.2⟩⟩)
        .nil)

/-- Node `[178]` on the literal capacity-free side selected at `[137]`. -/
@[reducible] noncomputable def blockedPairOverlapFirstFailureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairOverlapFirstFailure
    { Requires := [K .blockedPairCodeUnrealized, K .noProperBaseline]
      Produces := [K .pairOverlapFirstFailure]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapFirstFailure)
        (show Value BranchState Presentation presentation data
            .pairOverlapFirstFailure inputs.current from
          ⟨by
            obtain ⟨active, capacity, activationEq, _primitiveEq,
                _primitiveLe, _concrete, _scheduleCard, Coordinate, family,
                coordinateSupport, _survives, realizationExists, _demand,
                _deficitBound, _countFailure, pairSetNonempty,
                firstFailureExists⟩ :=
              (inputs.get (K .blockedPairCodeUnrealized)).down
            let pairSet := Graph.freeSide
              inputs.current.object.vertexPairDecidableEq
              (inputs.current.object.portPairSchedule data.threshold)
              capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable
            let realization := Classical.choice realizationExists
            let firstFailure := Classical.choice firstFailureExists
            let activation := Graph.pairResponseActivation active
            let recorded := Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK) activation
              (inputs.current.object.portPairSchedule data.threshold)
            have pairSetBlockerFree : ∀ pair, pair ∈ pairSet →
                ¬ Graph.SparsePairDEProfileObstructionAt
                    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                    (LengthOK := data.LengthOK) activation
                      (inputs.current.object.portPairSchedule data.threshold) pair ∧
                  ¬ Graph.SparsePairDEResponseObstructionAt
                    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                    (LengthOK := data.LengthOK) activation
                      (inputs.current.object.portPairSchedule data.threshold) pair := by
              intro pair pairMem
              have freeRecorded : pair ∈ capacity.activation.freePairs
                  data.threshold :=
                capacity.freeSide_subset_activationFree pairMem
              have freeParts :
                  pair ∈ inputs.current.object.portPairSchedule data.threshold ∧
                    ¬ (Graph.CanonicalFibreLedger.canonicalLabel
                      Graph.SameTokenBlockerRoles.canonicalBlockerOrder
                      capacity.activation.Blocks pair).isSome := by
                simpa [Graph.FiniteObject.DemandActivation.freePairs,
                  Graph.FiniteObject.freePairs,
                  Graph.CanonicalFibreLedger.unassigned] using freeRecorded
              have noRecordedBlocker :
                  ¬ (recorded.blockers pair).Nonempty := by
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
              constructor
              · intro obstruction
                apply noRecordedBlocker
                let coordinate :=
                  Graph.FiniteObject.DemandActivation.pairCoordinate pair
                    ((activation.pairSupport pair).getD ∅)
                have member : coordinate ∈
                    recorded.profileObstructions pair := by
                  simp [recorded, Graph.recordSparsePairDEBlockers,
                    obstruction, coordinate]
                exact (recorded.exists_blocks_iff_blockers_nonempty pair).mp
                  ⟨.boundaryProfile, recorded.blocks_boundaryProfile member⟩
              · intro obstruction
                apply noRecordedBlocker
                let coordinate :=
                  Graph.FiniteObject.DemandActivation.pairCoordinate pair
                    ((activation.pairSupport pair).getD ∅)
                have member : coordinate ∈
                    recorded.responseObstructions pair := by
                  simp [recorded, Graph.recordSparsePairDEBlockers,
                    obstruction, coordinate]
                exact (recorded.exists_blocks_iff_blockers_nonempty pair).mp
                  ⟨.targetResponse, recorded.blocks_targetResponse member⟩
            exact ⟨PairOverlapFirstFailure.of data inputs.current.object active
              Coordinate family coordinateSupport realization pairSet
              pairSetNonempty (by
                intro pair member
                have membership :
                    pair ∈ inputs.current.object.portPairSchedule data.threshold ∧
                      Graph.CanonicalFibreLedger.canonicalLabel
                        capacity.tokenOrder capacity.Eligible pair = none := by
                  simpa [pairSet, Graph.freeSide,
                    Graph.CanonicalFibreLedger.unassigned] using member
                exact membership.1) pairSetBlockerFree firstFailure
              (inputs.get (K .noProperBaseline)).down.2⟩⟩)
        .nil)

/-- **`def:pair-overlap-system` at node `[178]`.**

Both count-failure routes have already been normalized to the same exact
first-failure key.  This row reads that key and the retained connectivity fact,
selects every canonical pair support `X_π`, and publishes the manuscript's
literal conditional-fibre overlap system. -/
@[reducible] noncomputable def pairOverlapSystemRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairOverlapSystem
    { Requires := [K .pairOverlapFirstFailure, K .noProperBaseline]
      Produces := [K .pairOverlapSystem]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => by
      classical
      let object := inputs.current.object
      let first := Classical.choice
        (inputs.get (K .pairOverlapFirstFailure)).down
      let activation := Graph.pairResponseActivation first.active
      let connectedOn :
          Graph.SupportComponents.Connected.ConnectedOn object
            object.vertexFinset :=
        Graph.SupportComponents.Connected.connectedOn_vertexFinset
          object (inputs.get (K .noProperBaseline)).down.2
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
      let Skeleton := model.Skeleton
      let Baseline :=
        {coordinate // coordinate ∈ first.baselineFamily} → Bool
      let baselineState : Skeleton → Baseline :=
        fun member => first.baselineRealization.response member.1

      have failedFamilyObstruction : failedFamily.Nonempty ∧
          ¬ model.RealizingOrder (LengthOK := data.LengthOK)
            failedFamily := by
        refine ⟨failedFamilyNonempty, ?_⟩
        rintro ⟨order, realizes⟩
        let coordinateResponse : Skeleton →
            Fin failedFamily.card → PairResponseState data :=
          fun member index =>
            model.response (LengthOK := data.LengthOK) member (order index).1
        have branching : ∀ (index : Fin failedFamily.card)
            (member : Skeleton),
            2 ≤ Nat.card {state // ∃ candidate : Skeleton,
              baselineState candidate = baselineState member ∧
                (∀ earlier : Fin failedFamily.card,
                  earlier.1 < index.1 →
                    coordinateResponse candidate earlier =
                      coordinateResponse member earlier) ∧
                coordinateResponse candidate index = state} := by
          intro index member
          let Narrow := model.conditionalValues (LengthOK := data.LengthOK)
            failedFamily order member index
          let Broad := {state // ∃ candidate : Skeleton,
            baselineState candidate = baselineState member ∧
              (∀ earlier : Fin failedFamily.card,
                earlier.1 < index.1 →
                  coordinateResponse candidate earlier =
                    coordinateResponse member earlier) ∧
              coordinateResponse candidate index = state}
          let Candidate := {candidate : Skeleton //
            baselineState candidate = baselineState member ∧
              ∀ earlier : Fin failedFamily.card,
                earlier.1 < index.1 →
                  coordinateResponse candidate earlier =
                    coordinateResponse member earlier}
          let toBroad : Candidate → Broad := fun candidate =>
            ⟨coordinateResponse candidate.1 index,
              ⟨candidate.1, candidate.2.1, candidate.2.2, rfl⟩⟩
          have toBroadSurjective : Function.Surjective toBroad := by
            intro state
            obtain ⟨candidate, baseEq, earlierEq, responseEq⟩ := state.2
            refine ⟨⟨candidate, baseEq, earlierEq⟩, ?_⟩
            apply Subtype.ext
            exact responseEq
          letI : Finite Candidate := inferInstance
          letI : Finite Broad :=
            Finite.of_surjective toBroad toBroadSurjective
          let narrowToBroad : Narrow → Broad := fun state =>
            ⟨state.1, by
              obtain ⟨candidate, sameCode, earlierEq, responseEq⟩ := state.2
              have baseEq : baselineState candidate = baselineState member :=
                congrArg Prod.snd sameCode
              exact ⟨candidate, baseEq, earlierEq, responseEq⟩⟩
          have narrowToBroadInjective : Function.Injective narrowToBroad := by
            intro left right equal
            apply Subtype.ext
            exact congrArg (fun value : Broad => value.1) equal
          exact (realizes member index).trans
            (Nat.card_le_card_of_injective narrowToBroad
              narrowToBroadInjective)
        have lower : Nat.card Baseline * 2 ^ failedFamily.card ≤
            Nat.card Skeleton := by
          letI : Fintype Skeleton := Fintype.ofFinite Skeleton
          letI : Fintype Baseline := Fintype.ofFinite Baseline
          let signature (length : Nat) (bound : length ≤ failedFamily.card)
              (member : Skeleton) :
              Baseline × (Fin length → PairResponseState data) :=
            (baselineState member, fun index =>
              coordinateResponse member (Fin.castLE bound index))
          let prefixes (length : Nat) (bound : length ≤ failedFamily.card) :
              Finset (Baseline × (Fin length → PairResponseState data)) :=
            Finset.univ.image (signature length bound)
          have baselineSurjective : Function.Surjective baselineState := by
            intro assignment
            obtain ⟨member, realizesAssignment⟩ :=
              first.baselineRealization.realized assignment
            exact ⟨member, realizesAssignment⟩
          have baseCard : Nat.card Baseline ≤
              (prefixes 0 (Nat.zero_le failedFamily.card)).card := by
            have onto : Function.Surjective
                (signature 0 (Nat.zero_le failedFamily.card)) := by
              rintro ⟨value, empty⟩
              obtain ⟨member, memberEq⟩ := baselineSurjective value
              refine ⟨member, ?_⟩
              apply Prod.ext memberEq
              funext index
              exact Fin.elim0 index
            have imageEq : prefixes 0 (Nat.zero_le failedFamily.card) =
                Finset.univ := by
              ext value
              simp only [prefixes, Finset.mem_image, Finset.mem_univ,
                true_and]
              constructor
              · intro _
                trivial
              · intro _
                exact onto value
            rw [imageEq, Finset.card_univ, Nat.card_eq_fintype_card]
            simp
          have step : ∀ length
              (successorBound : length + 1 ≤ failedFamily.card),
              2 * (prefixes length
                (Nat.le_trans (Nat.le_add_right length 1)
                  successorBound)).card ≤
                (prefixes (length + 1) successorBound).card := by
            intro length successorBound
            let lengthBound : length ≤ failedFamily.card :=
              Nat.le_trans (Nat.le_add_right length 1) successorBound
            let currentPrefixes := prefixes length lengthBound
            let nextPrefixes := prefixes (length + 1) successorBound
            let project :
                Baseline × (Fin (length + 1) → PairResponseState data) →
                  Baseline × (Fin length → PairResponseState data) :=
              fun state => (state.1, fun index => state.2 index.castSucc)
            have mapsTo : Set.MapsTo project ↑nextPrefixes
                ↑currentPrefixes := by
              intro next nextMem
              obtain ⟨member, _, memberEq⟩ := Finset.mem_image.mp nextMem
              subst next
              apply Finset.mem_image.mpr
              refine ⟨member, Finset.mem_univ _, ?_⟩
              apply Prod.ext rfl
              funext index
              rfl
            have fibreTwo : ∀ pref ∈ currentPrefixes,
                2 ≤ {next ∈ nextPrefixes | project next = pref}.card := by
              intro pref prefMem
              obtain ⟨member, _, memberEq⟩ := Finset.mem_image.mp prefMem
              subst pref
              let coordinate : Fin failedFamily.card := ⟨length, by omega⟩
              let Values := {state // ∃ candidate : Skeleton,
                baselineState candidate = baselineState member ∧
                  (∀ earlier : Fin failedFamily.card,
                    earlier.1 < coordinate.1 →
                      coordinateResponse candidate earlier =
                        coordinateResponse member earlier) ∧
                  coordinateResponse candidate coordinate = state}
              have twoValues : 2 ≤ Nat.card Values :=
                branching coordinate member
              have positive : 0 < Nat.card Values :=
                lt_of_lt_of_le (by omega) twoValues
              letI : Finite Values := (Nat.card_pos_iff.mp positive).2
              have notSubsingleton : ¬ Subsingleton Values := by
                intro subsingleton
                have atMostOne : Nat.card Values ≤ 1 :=
                  Finite.card_le_one_iff_subsingleton.mpr subsingleton
                omega
              have distinctValues : ∃ left right : Values, left ≠ right := by
                by_contra absent
                push Not at absent
                exact notSubsingleton ⟨absent⟩
              obtain ⟨leftValue, rightValue, valuesDifferent⟩ :=
                distinctValues
              obtain ⟨left, leftBase, leftEarlier, leftResponse⟩ :=
                leftValue.2
              obtain ⟨right, rightBase, rightEarlier, rightResponse⟩ :=
                rightValue.2
              let leftSignature :=
                signature (length + 1) successorBound left
              let rightSignature :=
                signature (length + 1) successorBound right
              have leftMem : leftSignature ∈ nextPrefixes := by
                simp [leftSignature, nextPrefixes, prefixes]
              have rightMem : rightSignature ∈ nextPrefixes := by
                simp [rightSignature, nextPrefixes, prefixes]
              have leftProject : project leftSignature =
                  signature length lengthBound member := by
                apply Prod.ext leftBase
                funext index
                apply leftEarlier
                change index.1 < length
                exact index.2
              have rightProject : project rightSignature =
                  signature length lengthBound member := by
                apply Prod.ext rightBase
                funext index
                apply rightEarlier
                change index.1 < length
                exact index.2
              have signaturesDifferent : leftSignature ≠ rightSignature := by
                intro equal
                have lastEqual := congrFun (congrArg Prod.snd equal)
                  (Fin.last length)
                have lastCoordinate :
                    Fin.castLE successorBound (Fin.last length) = coordinate := by
                  apply Fin.ext
                  rfl
                have responseEqual : coordinateResponse left coordinate =
                    coordinateResponse right coordinate := by
                  simpa [leftSignature, rightSignature, signature,
                    lastCoordinate] using lastEqual
                apply valuesDifferent
                apply Subtype.ext
                exact leftResponse.symm.trans
                  (responseEqual.trans rightResponse)
              let chosen : Finset
                  (Baseline × (Fin (length + 1) → PairResponseState data)) :=
                {leftSignature, rightSignature}
              have chosenSubset : chosen ⊆
                  {next ∈ nextPrefixes |
                    project next = signature length lengthBound member} := by
                intro next nextMem
                simp only [chosen, Finset.mem_insert,
                  Finset.mem_singleton] at nextMem
                rcases nextMem with rfl | rfl
                · simp [leftMem, leftProject]
                · simp [rightMem, rightProject]
              have chosenCard : chosen.card = 2 := by
                simp [chosen, signaturesDifferent]
              rw [← chosenCard]
              exact Finset.card_le_card chosenSubset
            rw [Finset.card_eq_sum_card_fiberwise mapsTo]
            calc
              2 * currentPrefixes.card =
                  ∑ pref ∈ currentPrefixes, 2 := by simp [Nat.mul_comm]
              _ ≤ ∑ pref ∈ currentPrefixes,
                  {next ∈ nextPrefixes | project next = pref}.card := by
                gcongr with pref prefMem
                exact fibreTwo pref prefMem
          have prefixGrowth : ∀ length
              (bound : length ≤ failedFamily.card),
              Nat.card Baseline * 2 ^ length ≤
                (prefixes length bound).card := by
            intro length bound
            induction length with
            | zero => simpa using baseCard
            | succ length ih =>
                have previousBound : length ≤ failedFamily.card := by omega
                have doubled := Nat.mul_le_mul_left 2 (ih previousBound)
                have next := step length
                  (by simpa [Nat.add_comm] using bound)
                calc
                  Nat.card Baseline * 2 ^ (length + 1) =
                      2 * (Nat.card Baseline * 2 ^ length) := by
                    rw [pow_succ]
                    ac_rfl
                  _ ≤ 2 * (prefixes length previousBound).card := doubled
                  _ ≤ (prefixes (length + 1) bound).card := by
                    simpa [previousBound] using next
          have rangeBound :
              (prefixes failedFamily.card le_rfl).card ≤ Nat.card Skeleton := by
            calc
              (prefixes failedFamily.card le_rfl).card ≤
                  (Finset.univ : Finset Skeleton).card :=
                Finset.card_image_le
              _ = Nat.card Skeleton := by
                rw [Finset.card_univ, Nat.card_eq_fintype_card]
          exact (prefixGrowth failedFamily.card le_rfl).trans rangeBound
        have baselineCard : Nat.card Baseline =
            2 ^ first.baselineFamily.card := by
          dsimp [Baseline]
          rw [Nat.card_fun]
          simp [Nat.card_congr first.baselineFamily.equivFin]
        have skeletonCard : Nat.card Skeleton = Graph.skeletonBudget object := by
          dsimp [Skeleton, Graph.SparsePairSkeletonModel.Skeleton]
          simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
            Graph.PackedWindowRealization.card_skeleton
              object.vertexCount object.edgeCount
        apply first.firstFailure.failedNext
        calc
          2 ^ (first.baselineFamily.card +
                (first.firstFailure.index + 1)) =
              2 ^ first.baselineFamily.card * 2 ^ horizon := by
            rw [pow_add]
          _ = Nat.card Baseline * 2 ^ failedFamily.card := by
            rw [baselineCard, failedFamilyCard]
          _ ≤ Nat.card Skeleton := lower
          _ = Graph.skeletonBudget object := skeletonCard
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
          failedFamily_obstruction := by
            simpa [model] using failedFamilyObstruction }
      exact .cons (key := K .pairOverlapSystem)
        (show Value BranchState Presentation presentation data
            .pairOverlapSystem inputs.current from ⟨⟨system⟩⟩)
        .nil)

/-- Node `[178]` / open node `[182]`: decide the manuscript's conditional
factorization assertion on the one exact pair-response system already stored
in the ledger.  The positive arm is the sole input of
`lem:pair-failure-overlap`; the negative arm retains that same system as the
uncovered residual and asserts no blocker, exit, quotient, or contradiction. -/
noncomputable def pairConditionalFactorizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairOverlapSystem) known]
    (factorizationFresh : K .pairConditionalFactorization ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known) :
    Decision (K .pairConditionalFactorization)
      (K .pairConditionalFactorizationResidual) previous := by
  classical
  let system := Classical.choice
    (previous.get (K .pairOverlapSystem)).down
  exact Decision.run previous (K .pairConditionalFactorization)
    (K .pairConditionalFactorizationResidual)
    `Hypostructure.Graph.Strategy.Spine.pairConditionalFactorizationDichotomy
    (if factorization : system.ConditionalFactorization then
      .inl ⟨⟨system, factorization⟩⟩
    else
      .inr ⟨⟨.factorization system factorization⟩⟩)
    factorizationFresh residualFresh

/-- **`lem:pair-failure-overlap` at node `[178]`.**

The row reads the exact failed response system together with the affirmative
conditional-factorization fact from the ledger.  It proves only the paper's
inclusion-minimal overlap conclusion.  A nonfactorizing system cannot enter
this row; it remains at node `[182]`. -/
@[reducible] noncomputable def pairFailureOverlapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairFailureOverlap
    { Requires := [K .pairConditionalFactorization]
      Produces := [K .pairFailureOverlap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => by
      classical
      let factorizationFact := Classical.choice
        (inputs.get (K .pairConditionalFactorization)).down
      let system := factorizationFact.1
      have factorization : system.ConditionalFactorization :=
        factorizationFact.2
      let candidates := system.failedFamily.powerset.filter system.obstruction
      have candidatesNonempty : candidates.Nonempty := by
        refine ⟨system.failedFamily, ?_⟩
        simp [candidates, PairOverlapSystem.obstruction,
          PairOverlapSystem.realizingOrder,
          PairOverlapSystem.toSkeletonModel,
          system.failedFamily_nonempty, system.failedFamily_obstruction]
      let selected := candidates.exists_minimal candidatesNonempty
      let family := Classical.choose selected
      have selectedFacts : family ∈ candidates ∧
          ∀ candidate ∈ candidates, candidate ⊆ family →
            family ⊆ candidate := by
        exact Classical.choose_spec selected
      have familyFacts : family ⊆ system.failedFamily ∧
          system.obstruction family := by
        simpa [candidates] using selectedFacts.1
      have minimal : system.minimalObstruction family := by
        refine ⟨familyFacts.2, ?_⟩
        intro proper properSubset properNonempty
        by_contra notRealizing
        have properMem : proper ∈ candidates := by
          simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨properSubset.subset.trans familyFacts.1,
            ⟨properNonempty, notRealizing⟩⟩
        exact properSubset.2
          (selectedFacts.2 proper properMem properSubset.subset)
      have overlapWitness : ∃ left ∈ family, ∃ right ∈ family,
          left ≠ right ∧ system.toSkeletonModel.Overlaps left right := by
        by_contra absent
        push Not at absent
        have separated : system.toSkeletonModel.PairwiseSeparated family := by
          intro left leftMem right rightMem different overlap
          exact absent left leftMem right rightMem different overlap
        exact minimal.1.2 (factorization.separated family separated)
      have connected :
          Graph.SupportComponents.Connected.ConnectedOn inputs.current.object
            (system.overlapSupport family) := by
        let object := inputs.current.object
        let model := system.toSkeletonModel
        have familyNonempty : family.Nonempty := minimal.1.1
        have notRealizing :
            ¬ model.RealizingOrder (LengthOK := data.LengthOK) family := by
          simpa [model, PairOverlapSystem.realizingOrder] using minimal.1.2
        have properRealizing : ∀ proper, proper ⊂ family → proper.Nonempty →
            model.RealizingOrder (LengthOK := data.LengthOK) proper := by
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
        have joined := factorization.concatenate left right
          leftNonempty rightNonempty disjoint noCross
          (properRealizing left leftProper leftNonempty)
          (properRealizing right rightProper rightNonempty)
        have familyUnionEq : model.familyUnion left right = family := by
          unfold Graph.SparsePairSkeletonModel.familyUnion
          exact unionEq
        rw [familyUnionEq] at joined
        exact joined
      let overlap : PairFailureOverlap data inputs.current.object :=
        { system := system
          family := family
          factorization := factorization
          minimal := minimal
          overlapWitness := overlapWitness
          connected := connected }
      exact .cons (key := K .pairFailureOverlap)
        (show Value BranchState Presentation presentation data
            .pairFailureOverlap inputs.current from ⟨⟨overlap⟩⟩)
        .nil)

/-- **Node `[179]`, canonical demand-return input.**

The failed pair is not unpacked by Assembly.  This sealed row reads the exact
node-`[178]` obstruction, recovers its two active demands from membership in
the object's pair schedule, and publishes their already selected canonical
returns and graph-derived `ℓ_ret` bound on the same monotone ledger. -/
@[reducible] noncomputable def pairDemandReturnsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairDemandReturns
    { Requires := [K .pairFailureOverlap]
      Produces := [K .pairDemandReturns]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairDemandReturns)
        (show Value BranchState Presentation presentation data
            .pairDemandReturns inputs.current from
          ⟨⟨PairDemandReturns.of
            (Classical.choice
              (inputs.get (K .pairFailureOverlap)).down)⟩⟩)
        .nil)

/-- Node `[179]` / open node `[182]`: test the five alternatives of
`lem:pair-system-realizability` on the one exact overlap obstruction already
stored in the ledger. -/
noncomputable def pairSystemRealizabilityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairDemandReturns) known]
    (coveredFresh : K .pairSystemRealizability ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known) :
    Decision (K .pairSystemRealizability)
      (K .pairConditionalFactorizationResidual) previous := by
  classical
  let returns := Classical.choice
    (previous.get (K .pairDemandReturns)).down
  exact Decision.run previous (K .pairSystemRealizability)
    (K .pairConditionalFactorizationResidual)
    `Hypostructure.Graph.Strategy.Spine.pairSystemRealizabilityDichotomy
    (if covered : Nonempty (PairSystemRealizabilityOutcome returns) then
      .inl ⟨⟨returns, covered⟩⟩
    else
      .inr ⟨⟨.systemRealizability returns covered⟩⟩)
    coveredFresh residualFresh

/-- Node `[179]`: split the already-published five-way theorem into its
closed/routed alternatives (i)--(iv) and its serial alternative (v). -/
noncomputable def pairSystemOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairSystemRealizability) known]
    (earlyFresh : K .pairSystemEarlyOutcome ∉ known)
    (serialFresh : K .pairSerialDemandSystem ∉ known) :
    Decision (K .pairSystemEarlyOutcome) (K .pairSerialDemandSystem)
      previous := by
  classical
  let package := Classical.choice
    (previous.get (K .pairSystemRealizability)).down
  let outcome := Classical.choice package.2
  exact Decision.run previous (K .pairSystemEarlyOutcome)
    (K .pairSerialDemandSystem)
    `Hypostructure.Graph.Strategy.Spine.pairSystemOutcomeDichotomy
    (match outcome with
    | .early early => .inl ⟨⟨early⟩⟩
    | .serial serial _same => .inr ⟨⟨serial⟩⟩)
    earlyFresh serialFresh

/-- Alternatives (i)--(iv) of node `[179]` are either already contradictory
to the selected/survivor facts or are the literal common Type B entry.  This
row publishes that entry only after reading all three facts from ExactLedger. -/
@[reducible] noncomputable def pairSystemEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairSystemEarlyTypeBEntry
    { Requires := [K .pairSystemEarlyOutcome, K .selection,
        K .sparseSurplusSurvivor]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        (show Value BranchState Presentation presentation data
            .typeBFanEntry inputs.current from ⟨by
          let outcome := Classical.choice
            (inputs.get (K .pairSystemEarlyOutcome)).down
          match outcome with
          | .targetCycle cycle =>
              exact False.elim ((inputs.get (K .selection)).down.1 cycle)
          | .sparseExit exit =>
              exact False.elim
                ((inputs.get (K .sparseSurplusSurvivor)).down exit)
          | .typeB entry => exact entry⟩)
        .nil)

/-- Node `[180]` / open node `[182]`: test the exact serial system against the
corrected full-modulus arithmetic and the two periodic-response routes claimed
by `lem:pair-system-increment-arithmetic`. -/
noncomputable def pairIncrementCoveredDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    (coveredFresh : K .pairIncrementCovered ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known) :
    Decision (K .pairIncrementCovered)
      (K .pairConditionalFactorizationResidual) previous := by
  classical
  let serial := Classical.choice
    (previous.get (K .pairSerialDemandSystem)).down
  exact Decision.run previous (K .pairIncrementCovered)
    (K .pairConditionalFactorizationResidual)
    `Hypostructure.Graph.Strategy.Spine.pairIncrementCoveredDichotomy
    (if covered : Nonempty (PairIncrementOutcome serial) then
      .inl ⟨⟨serial, covered⟩⟩
    else
      .inr ⟨⟨.incrementArithmetic serial covered⟩⟩)
    coveredFresh residualFresh

/-- Node `[180]`: split its published exhaustive alternative into the periodic
route and the corrected direct arithmetic input. -/
noncomputable def pairIncrementOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairIncrementCovered) known]
    (earlyFresh : K .pairIncrementEarlyOutcome ∉ known)
    (arithmeticFresh : K .pairSerialArithmetic ∉ known) :
    Decision (K .pairIncrementEarlyOutcome) (K .pairSerialArithmetic)
      previous := by
  classical
  let package := Classical.choice
    (previous.get (K .pairIncrementCovered)).down
  let outcome := Classical.choice package.2
  exact Decision.run previous (K .pairIncrementEarlyOutcome)
    (K .pairSerialArithmetic)
    `Hypostructure.Graph.Strategy.Spine.pairIncrementOutcomeDichotomy
    (match outcome with
    | .early early => .inl ⟨⟨early⟩⟩
    | .arithmetic arithmetic => .inr ⟨⟨package.1, ⟨arithmetic⟩⟩⟩)
    earlyFresh arithmeticFresh

/-- The periodic sparse-exit/Type-B alternative of node `[180]`, normalized
to the common Type B entry after eliminating the survivor-incompatible exit. -/
@[reducible] noncomputable def pairIncrementEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairIncrementEarlyTypeBEntry
    { Requires := [K .pairIncrementEarlyOutcome, K .sparseSurplusSurvivor]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        (show Value BranchState Presentation presentation data
            .typeBFanEntry inputs.current from ⟨by
          let outcome := Classical.choice
            (inputs.get (K .pairIncrementEarlyOutcome)).down
          match outcome with
          | .sparseExit exit =>
              exact False.elim
                ((inputs.get (K .sparseSurplusSurvivor)).down exit)
          | .typeB entry => exact entry⟩)
        .nil)

/-- Node `[180]`, direct arithmetic arm.  The row applies the canonical serial
spectrum API, recovers the actual simple cycle stored by `[179]`, proves its
exponent is at least two from simple-cycle length, and publishes the accepted
cycle. -/
@[reducible] noncomputable def pairPowerOfTwoCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairPowerOfTwoCycle
    { Requires := [K .pairSerialArithmetic]
      Produces := [K .pairPowerOfTwoCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => by
      classical
      let package := Classical.choice
        (inputs.get (K .pairSerialArithmetic)).down
      let serial := package.1
      let arithmetic := Classical.choice package.2
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
        (data.lengthOK_iff_powerOfTwo (2 ^ exponent)).2
          (Core.DyadicLength.powerOfTwoLength_of_exists
            ⟨exponent, exponentLower, rfl⟩)
      let certificate : Graph.CycleCertificate inputs.current.object
          data.LengthOK :=
        { vertex := cycle.vertex
          walk := cycle.walk
          isCycle := cycle.isCycle
          length_ok := by simpa [cycle.length_eq] using accepted }
      exact .cons (key := K .pairPowerOfTwoCycle)
        (show Value BranchState Presentation presentation data
            .pairPowerOfTwoCycle inputs.current from
          ⟨⟨certificate⟩⟩)
        .nil)

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
          exact ⟨active, presentation, activationEq, certified, token, role,
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
      obtain ⟨active, declared, activationEq, certified, token, role, tokenMem,
        outside, rest⟩ := (previous.get (K .windowClassAbsent)).down
      let ledger := certified.ledger
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence => exact absurd classified outside
      | remainderSurplus =>
          exact ⟨.inl ⟨active, declared, activationEq, certified, token, role,
            tokenMem, classified, rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨active, declared, activationEq, certified, token, role,
            tokenMem, classified, rest⟩⟩))
    remainderFresh primitiveFresh

end Hypostructure.Graph.Strategy.Spine
