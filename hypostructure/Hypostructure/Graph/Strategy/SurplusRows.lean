import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.ObjectCapacityLedger

/-!
# The sparse surplus branch: the activation rows

Nodes `[126]`--`[128]` of the non-near-cubic branch, the arm node `[19]` sends
an object whose degree surplus exceeds the registered scale threshold.

Each row is one atomic Strategy over the one canonical `ExactLedger`.  A row
reads its prerequisites by exact semantic key through sealed `FactInputs`,
proves the manuscript's statement about the residual's own object, and commits
exactly that statement.  Nothing is transported outside the ledger and no row
names a producer or an execution position.

* `sparseSlackSurplusRow` is `lem:sparse-slack-surplus`.  The manuscript's two
  displays, `σ(G) = n − 6 − 2λ` and `m = (3/2)n + (1/2)σ(G)`, are one identity
  cleared of division and of the `λ = 2n − 3 − m` abbreviation: `2m = δn + σ(G)`
  at the registered baseline.  It is an identity of the surplus observable's own
  definition once the handshake bound `δn ≤ 2m` is available, and that bound is
  the standing baseline read off the residual.
* `activeSurplusFamilyRow` is `lem:sparse-excess-port-extraction` together with
  the family statement of `lem:surviving-active-family`: the excess selector has
  exactly `σ(G)` members, and each of them is a port whose centre is strictly
  above the baseline, whose endpoint sits exactly at it, and which therefore
  carries exactly `δ − 1` shoulders.  The endpoint's degree is node `[10]`'s
  independence spent, not re-proved: the row reads the committed
  slack-independence fact.
* `sparsePortActivationRow` is `lem:sparse-port-activation` clauses (a)--(d).
  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`, which `lem:bridgeless` --
  the edge contraction of `Graph/Contraction.lean` -- supplies from the same
  minimality and avoidance; clause (c) is the suppression witness `Q_p`, which
  minimality and avoidance supply through `TightVertexSuppression`; clause (d)
  is the triangle of a triangular port.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[126]`: the sparse slack identity -/

/-- `lem:sparse-slack-surplus`, cleared of division: `2m = δn + σ(G)`.

The manuscript writes `m = (3/2)n + (1/2)σ(G)` and, with `λ = 2n − 3 − m`,
`σ(G) = n − 6 − 2λ`; substituting the abbreviation turns the second display into
the first, and doubling the first is the exact `Nat` identity committed here.
The only input is the standing baseline, which the executor reads off the
residual rather than from a fact. -/
@[reducible] noncomputable def sparseSlackSurplusRow
    (sparseSlackSurplus :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (2 * input.object.edgeCount =
        data.threshold * input.object.vertexCount +
          input.object.degreeSurplus data.threshold) →
      sparseSlackSurplus.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSlackSurplus
    (sourceFreeManifest sparseSlackSurplus)
    (fun inputs =>
      let handshake : data.threshold * inputs.current.object.vertexCount ≤
          2 * inputs.current.object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
          inputs.current.object data.threshold fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
      .cons (key := sparseSlackSurplus)
        (encode inputs.current (by
          unfold Graph.FiniteObject.degreeSurplus
          omega))
        .nil)

/-! ## Node `[127]`: the excess selector and its count -/

/-- `lem:sparse-excess-port-extraction`, and with it the family half of
`lem:surviving-active-family`.

`|𝒫_exc| = σ(G)` is the count of the excess selector; the per-port clauses are
the manuscript's *"the vertex `h` has degree at least `4`, the vertex `x` has
degree `3`, and `N_G(x) = {h, a_p, b_p}`"*, stated at the registered baseline as
`δ < d(c(p))`, `d(x(p)) = δ`, and `|s(p)| = δ − 1`.

Node `[10]`'s independence is consumed, not re-proved: it is the committed
slack-independence fact, and it is exactly what forces a port's endpoint down to
the baseline. -/
@[reducible] noncomputable def activeSurplusFamilyRow
    (slackIndependent activeSurplusFamily :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : slackIndependent ≠ activeSurplusFamily)
    (independentOf : (input : Input BranchState Presentation presentation data) →
      slackIndependent.At input →
      ∀ left right : input.object.Vertex,
        data.threshold < input.object.degree left →
        data.threshold < input.object.degree right →
        ¬ input.object.graph.Adj left right)
    (encode : (input : Input BranchState Presentation presentation data) →
      ((input.object.excessPorts data.threshold).card =
          input.object.degreeSurplus data.threshold ∧
        ∀ pair : input.object.Vertex × input.object.Vertex,
          ∀ member : pair ∈ input.object.excessPorts data.threshold,
            data.threshold < input.object.degree pair.1 ∧
              input.object.degree pair.2 = data.threshold ∧
              (input.object.surplusPortOfMem member).shoulders.card =
                data.threshold - 1) →
      activeSurplusFamily.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusFamily
    (rowManifest slackIndependent activeSurplusFamily distinct)
    (fun inputs =>
      let object := inputs.current.object
      let baseline : ∀ vertex : object.Vertex,
          data.threshold ≤ object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (object.minDegree_le_degree vertex)
      let independent := independentOf inputs.current (inputs.get slackIndependent)
      .cons (key := activeSurplusFamily)
        (encode inputs.current
          ⟨object.card_excessPorts baseline, fun _pair member =>
            ⟨Graph.FiniteObject.centre_high_of_mem_excessPorts member,
              (object.surplusPortOfMem member).endpoint_degree_eq baseline
                independent,
              (object.surplusPortOfMem member).card_shoulders baseline
                independent⟩⟩)
        .nil)

/-! ## Node `[128]`: port activation -/

/-- `lem:sparse-port-activation`, clauses (a)--(d).

At a selected port whose endpoint carries a shoulder *pair* -- which at the
manuscript's `δ = 3` is every selected port, by the previous row's `|s(p)| =
δ − 1` -- the two cases of the lemma are:

* the port is *open*, and suppressing its endpoint gives a strictly smaller
  object meeting the baseline; minimality supplies an accepted cycle there,
  avoidance forces it through the inserted shoulder chord, and the
  reconstruction returns the simple shoulder-to-shoulder path `Q_p ⊆ G − x(p)`
  whose restored length is accepted.  That is the manuscript's `2^{j(p)} − 1`
  with `j(p) ≥ 2`, at whatever accepted set is registered;
* the port is *triangular*, and the triangle `x a_p b_p x` is present.

Clause (a) is the shoulder pair itself, which is the row's own hypothesis at
each port.  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`: the port's own
edge is not a bridge, because contracting it gives a strictly smaller object
still meeting the baseline, and minimality and avoidance close it exactly as
they close the suppression.  Its first edge after `x(p)` is a shoulder. -/
@[reducible] noncomputable def sparsePortActivationRow
    (selection sparsePortActivation :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ sparsePortActivation)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (minimalOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        smaller.LexicographicallySmaller input.object →
        data.threshold ≤ smaller.minDegree →
        Graph.HasCycleWithLength data.LengthOK smaller)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ pair : input.object.Vertex × input.object.Vertex,
        ∀ member : pair ∈ input.object.excessPorts data.threshold,
          ∀ left right : input.object.Vertex,
            (∀ vertex : input.object.Vertex,
              vertex ∈ (input.object.surplusPortOfMem member).shoulders ↔
                (vertex = left ∨ vertex = right)) →
            left ≠ right →
            Nonempty (Graph.FiniteObject.SurplusPort.PortReturn
                input.object pair.1 pair.2 left right) ∧
              (¬ input.object.graph.Adj left right →
                Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness
                  input.object data.LengthOK pair.2 left right)) ∧
              (input.object.graph.Adj left right →
                input.object.graph.Adj pair.2 left ∧
                  input.object.graph.Adj left right ∧
                  input.object.graph.Adj right pair.2)) →
      sparsePortActivation.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparsePortActivation
    (rowManifest selection sparsePortActivation distinct)
    (fun inputs =>
      let object := inputs.current.object
      let fact := inputs.get selection
      let avoids := avoidsOf inputs.current fact
      let minimal := minimalOf inputs.current fact
      .cons (key := sparsePortActivation)
        (encode inputs.current fun _pair member left right shoulders distinct =>
          ⟨(object.surplusPortOfMem member).portReturn_of_minimal
              shoulders inputs.current.baseline avoids minimal,
            fun openPort =>
              (object.surplusPortOfMem member).openPortWitness_of_minimal
                shoulders distinct openPort inputs.current.baseline avoids
                minimal,
            fun adjacent =>
              (object.surplusPortOfMem member).triangle_of_shoulders_adj
                (shoulders left |>.2 (Or.inl rfl))
                (shoulders right |>.2 (Or.inr rfl)) adjacent⟩)
        .nil)

/-! ## Node `[129]`: the active family and baseline demand -/

/-- `def:baseline-spine-demand` at the strict branch's already-built active
family.

The paper does not obtain this demand from node `[21]`.  The completed active
family of `[128]` and the sparse-exit survivor of `[125]` are read from the
incoming exact ledger.  Exit-freeness makes the concrete baseline family
independently target-testable; choosing the cubic baseline exponent itself as
its cardinality gives canonical deficit zero, hence the required linear bound.
The witness, deficit, and bound are all registered in this node's one paper
fact. -/
@[reducible] noncomputable def baselineSpineDemandRow
    (activeSurplusDemands sparseSurplusSurvivor baselineSpineDemand :
      FactKey (Input BranchState Presentation presentation data))
    (activeIs : activeSurplusDemands = K .activeSurplusDemands)
    (survivorIs : sparseSurplusSurvivor = K .sparseSurplusSurvivor)
    (baselineIs : baselineSpineDemand = K .baselineSpineDemand)
    (activeSurvivor : activeSurplusDemands ≠ sparseSurplusSurvivor)
    (activeBaseline : activeSurplusDemands ≠ baselineSpineDemand)
    (survivorBaseline : sparseSurplusSurvivor ≠ baselineSpineDemand)
    (twoLe : 2 ≤ data.threshold) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  by
    subst activeSurplusDemands
    subst sparseSurplusSurvivor
    subst baselineSpineDemand
    exact
      factOnly `Hypostructure.Graph.Strategy.Spine.baselineSpineDemand
        { Requires := [K .activeSurplusDemands, K .sparseSurplusSurvivor]
          Produces := [K .baselineSpineDemand]
          requiresUnique := by simp [activeSurvivor]
          producesUnique := by simp
          producesNonempty := by simp }
        (fun inputs =>
          .cons (key := K .baselineSpineDemand)
            (show Value BranchState Presentation presentation data .baselineSpineDemand
                inputs.current from
              ⟨by
                classical
                simp only [Holds]
                change Graph.ActiveSurplusDemands
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
                    inputs.current.object data.threshold ∧
                  ∃ (Coordinate : Type u) (family : Finset Coordinate)
                    (coordinateSupport : Coordinate →
                      Finset inputs.current.object.Vertex),
                    Graph.IsBaselineSpineDemand
                        (inputs.current.object.declaredQuotientSystem
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          family coordinateSupport)
                        inputs.current.object.vertexCount data.threshold
                        (Graph.spineDeficit inputs.current.object.vertexCount
                          data.threshold family.card) ∧
                      Graph.spineDeficit inputs.current.object.vertexCount
                          data.threshold family.card ≤
                        data.surplusScale * inputs.current.object.vertexCount
                let bits := Graph.cubicBaselineExponent
                  inputs.current.object.vertexCount data.threshold
                let Coordinate := inputs.current.object.BaselineSpineCoordinate bits
                let family := inputs.current.object.baselineSpineFamily bits
                let coordinateSupport := inputs.current.object.baselineSpineSupport
                  (bits := bits)
                have familyCard : family.card = bits := by
                  simp [family]
                let survivor := (inputs.get (K .sparseSurplusSurvivor)).down
                have testable := Graph.survives_of_exitFree
                  (family := family) (coordinateSupport := coordinateSupport)
                  survivor.1 survivor.2
                have demand := Graph.isBaselineSpineDemand_of_package
                  (inputs.current.object.declaredQuotientSystem
                  (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK)
                    family coordinateSupport)
                  inputs.current.object.vertexCount twoLe bits testable (by omega)
                refine ⟨(inputs.get (K .activeSurplusDemands)).down,
                  Coordinate, family, coordinateSupport, ?_, ?_⟩
                · simpa [familyCard] using demand
                · rw [familyCard]
                  simp [bits, Graph.spineDeficit]⟩)
            .nil)

/-! ## Node `[132]`: route the dependent pair family -/

/-- Node `[130]`: construct the full response family from the active-family
fact on the literal `[129]` ledger, then retain exactly the paper's independent
or dependent arm. -/
noncomputable def pairResponseIndependenceDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .activeSurplusDemands) known]
    (independentFresh : K .independentPairFamily ∉ known)
    (dependentFresh : K .dependentPairFamily ∉ known) :
    Decision (K .independentPairFamily) (K .dependentPairFamily) previous :=
  Decision.run previous (K .independentPairFamily) (K .dependentPairFamily)
    `Hypostructure.Graph.Strategy.Spine.pairResponseIndependenceDichotomy
    (Classical.choice (show Nonempty
        ((K .independentPairFamily).At current ⊕
          (K .dependentPairFamily).At current) from by
      let active := (previous.get (K .activeSurplusDemands)).down
      let activation := Graph.pairResponseActivation active
      let pairs := current.object.portPairSchedule data.threshold
      let family := activation.pairFamily pairs
      let coordinateSupport : current.object.PairCoordinate →
          Finset current.object.Vertex := by
        letI := current.object.vertices.decEq
        exact Graph.DeclaredSignature.Coordinate.support
      by_cases independent : ∀ attempt : Graph.AttemptedQuotient
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object family
          coordinateSupport,
          Set.InjOn attempt.label ↑family
      · exact ⟨.inl ⟨active, independent⟩⟩
      · push_neg at independent
        exact ⟨.inr ⟨active, independent⟩⟩))
    independentFresh dependentFresh

/-- `lem:sparse-pair-dependence-exit` on the literal residual produced by
node `[130]`.  The attempted quotient and its failure of injectivity are read
from that residual's exact ledger.  The two conclusions are distinct decision
arms, and `Decision.run` preserves the complete incoming ancestry on either
arm. -/
noncomputable def blockedPairRoutingDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .dependentPairFamily) known]
    (exitFresh : K .sparsePairExit ∉ known)
    (blockerFresh : K .canonicalBlockerRoute ∉ known) :
    Decision (K .sparsePairExit) (K .canonicalBlockerRoute) previous :=
  Decision.run previous (K .sparsePairExit) (K .canonicalBlockerRoute)
    `Hypostructure.Graph.Strategy.Spine.blockedPairRoutingDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePairExit).At current ⊕
          (K .canonicalBlockerRoute).At current) from by
      obtain ⟨active, attempt, reducing⟩ :=
        (previous.get (K .dependentPairFamily)).down
      let activation := Graph.pairResponseActivation active
      let pairs := current.object.portPairSchedule data.threshold
      rcases Graph.sparsePairDependence_exit_or_blocker activation pairs attempt
          reducing with exit | blocker
      · exact ⟨.inl ⟨exit⟩⟩
      · exact ⟨.inr ⟨active, blocker⟩⟩))
    exitFresh blockerFresh

/-! ## Node `[134]`: canonical blocker ledger -/

/-- The canonical blocker ledger on the literal blocker residual of `[132]`.
The executor records that certified type-(d)/(e) obstruction in the same
activation, then publishes the full-pair count, the blocked/free partition,
the canonical-fibre no-overcount identity, and an exhibited blocked pair. -/
@[reducible] noncomputable def canonicalPairLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalPairLedger
    { Requires := [K .canonicalBlockerRoute]
      Produces := [K .canonicalPairLedger]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalPairLedger)
        (show Value BranchState Presentation presentation data
            .canonicalPairLedger inputs.current from
          ⟨by
            obtain ⟨active, certificate⟩ :=
              (inputs.get (K .canonicalBlockerRoute)).down
            let activation := Graph.pairResponseActivation active
            let pairs := inputs.current.object.portPairSchedule data.threshold
            let recorded := Graph.recordSparsePairDEBlocker activation pairs certificate
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            refine ⟨active, certificate, rfl,
              ?_, ?_, ?_, ?_, ?_⟩
            · exact inputs.current.object.card_portPairSchedule baseline
            · simpa [recorded] using
                recorded.card_blockedPairs_add_card_unblockedPairs data.threshold
            · exact recorded.card_canonicalIncidenceLedger data.threshold
            · exact recorded.card_blockedPairs_eq_sum_blockerMultiplicity data.threshold
            · exact Graph.recordedSparsePairDEBlocker_nonempty activation pairs
                certificate⟩)
        .nil)

/-! ## Node `[135]`: exact window-join pressure -/

@[reducible] noncomputable def exactWindowJoinPressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.exactWindowJoinPressure
    { Requires := [K .maximalPacking, K .noProperBaseline,
        K .tightEndpoint, K .surplusAbove]
      Produces := [K .sparseUpperEnvelope]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseUpperEnvelope)
        (show Value BranchState Presentation presentation data
            .sparseUpperEnvelope inputs.current from
          ⟨by
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have surplusPositive :
                0 < inputs.current.object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _)
                (inputs.get (K .surplusAbove)).down
            have edgePositive : 0 < inputs.current.object.edgeCount :=
              inputs.current.object.edgeCount_pos_of_degreeSurplus_pos
                surplusPositive
            have envelope := inputs.current.object.edgeCount_add_two_le
              data.three_le_threshold
              (inputs.get (K .noProperBaseline)).down
              (inputs.get (K .tightEndpoint)).down edgePositive
            obtain ⟨_, packing, valid, maximal, _⟩ :=
              (inputs.get (K .maximalPacking)).down
            exact ⟨envelope, packing, valid, maximal,
              inputs.current.object.exact_window_join_identity valid baseline⟩⟩)
        .nil)

/-! ## Node `[136]`: capacity-token ledger -/

@[reducible] noncomputable def capacityTokenLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.capacityTokenLedger
    { Requires := [K .canonicalPairLedger, K .sparseUpperEnvelope]
      Produces := [K .capacityTokenLedger]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .capacityTokenLedger)
        (show Value BranchState Presentation presentation data
            .capacityTokenLedger inputs.current from
          ⟨by
            obtain ⟨active, certificate, _pairsEq, scheduleCard,
                _partition, _incidence, _multiplicity, _blocked⟩ :=
              (inputs.get (K .canonicalPairLedger)).down
            obtain ⟨envelope, packing, valid, maximal, _joinIdentity⟩ :=
              (inputs.get (K .sparseUpperEnvelope)).down
            let activation := Graph.recordSparsePairDEBlocker
              (Graph.pairResponseActivation active)
              (inputs.current.object.portPairSchedule data.threshold) certificate
            have pairCard : certificate.choose.card = 2 :=
              Graph.card_of_mem_portPairSchedule inputs.current.object data.threshold
                certificate.choose_spec.1
            have pairNonempty : certificate.choose.Nonempty :=
              Finset.card_pos.mp (by omega : 0 < certificate.choose.card)
            let port := pairNonempty.choose
            let presentation : inputs.current.object.CarrierPresentation
                inputs.current.object.PairCoordinate
                inputs.current.object.PairCoordinate := {
              coordinateSupport := by
                letI := inputs.current.object.vertices.decEq
                exact Graph.DeclaredSignature.Coordinate.support
              chordEnds := fun _ => (port.1, port.1)
              chordPort := fun _ => port }
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have handshake : data.threshold * inputs.current.object.vertexCount ≤
                2 * inputs.current.object.edgeCount :=
              Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
                inputs.current.object data.threshold baseline
            refine ⟨inputs.current.object.PairCoordinate,
              inputs.current.object.PairCoordinate, activation, presentation,
              packing, valid, maximal, ⟨?_, ?_⟩, ?_⟩
            · exact inputs.current.object.card_primitiveCarrier baseline
            · exact inputs.current.object.card_primitiveCarrier_le baseline
                data.three_le_threshold handshake envelope
            · refine ⟨inputs.current.object.card_capacityTokens_add_internalMass
                  valid baseline, ?_, ?_, ?_, ?_, ?_⟩
              · exact inputs.current.object.card_capacityTokens_le valid baseline
                  data.three_le_threshold handshake envelope data.windowOrder_pos
                  data.joinSlack
              · intro pair token charged
                exact Graph.FiniteObject.capacityCharge_mem_capacityTokens
                  activation presentation data.threshold packing charged
              · rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
                    (object := inputs.current.object) (threshold := data.threshold)
                    (packing := packing)]
                exact Graph.FiniteObject.card_chargedPairs_eq_sum_load
                  activation presentation data.threshold packing
              · intro blocked carried
                exact Graph.FiniteObject.chargedPairs_eq_of_blocked
                  activation presentation data.threshold packing blocked carried
              · intro token
                exact ⟨Graph.FiniteObject.tokenFibre_subset activation presentation
                    data.threshold packing token,
                  fun pair member =>
                    Graph.FiniteObject.card_of_mem_tokenFibre activation presentation
                      data.threshold packing member,
                  Graph.FiniteObject.card_tokenFibre_eq_pairMultiplicity activation
                    presentation data.threshold packing token⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
