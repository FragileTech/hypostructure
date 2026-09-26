import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.SameTokenRoutingArms
import Hypostructure.Graph.QuadrilateralAttemptedQuotient

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

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

@[reducible] noncomputable def sameTokenBottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenBottleneckRouting
    { Requires := [K .homogeneousBottleneckPattern,
        K .activeSurplusDemands,
        K .cubicBaseline, K .capacityTokenLedger, K .selection,
        K .bridgeless,
        K .highCentreNormalForm,
        K .degreeProfileFibres, K .targetCompleteContextUniversality,
        K .replacementExclusion, K .uncompressible]
      Produces := [K .bottleneckRouting, K .typeBHandoff]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let patternFact :=
        (inputs.get (K .homogeneousBottleneckPattern)).down
      have routedBoth :
          Holds BranchState Presentation presentation data .bottleneckRouting
              inputs.current.object ∧
            (Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
                inputs.current.object ∨
              SameTokenTypeBHandoffStatement data.toParameters inputs.current.object) := by
          classical
          -- Read every paper hypothesis through the sealed ledger.  These are
          -- intentionally not repackaged into a route or callback record.  The
          -- current-object baseline is part of the sealed residual itself; the
          -- cubic-switch paragraph uses it before it upgrades a surviving
          -- separator from degree three to degree at least four.  Once read,
          -- the current object is generalized, so the routing argument below
          -- is elaborated over an abstract object rather than the input record.
          have patternRead := patternFact
          have activeRead := (inputs.get (K .activeSurplusDemands)).down
          have cubicRead := (inputs.get (K .cubicBaseline)).down
          have capacityLedgerRead := (inputs.get (K .capacityTokenLedger)).down
          have selectionRead := (inputs.get (K .selection)).down
          have bridgelessRead := (inputs.get (K .bridgeless)).down
          have highCentreRead := (inputs.get (K .highCentreNormalForm)).down
          have degreeProfileRead := (inputs.get (K .degreeProfileFibres)).down
          have contextRead :=
            (inputs.get (K .targetCompleteContextUniversality)).down
          have replacementRead := (inputs.get (K .replacementExclusion)).down
          have uncompressibleRead := (fun support compressible => (inputs.get (K .uncompressible)).down support
        (Graph.Strategy.InterfaceReplacement.replacementSupportOfCompressibleSupport _ _ _ _
          compressible))
          have baselineRead :
              Graph.MinimumDegreeAtLeast data.threshold inputs.current.object :=
            inputs.current.baseline
          revert patternRead activeRead cubicRead capacityLedgerRead
            selectionRead bridgelessRead highCentreRead degreeProfileRead
            contextRead replacementRead uncompressibleRead baselineRead
          generalize inputs.current.object = object
          intro patternFact active cubicFact capacityLedger selection bridgeless
            highCentreNormalForm degreeProfileFibres contextUniversality
            replacementExclusion uncompressible objectBaseline
          obtain ⟨patternActive, capacity, activationEq, concretePattern⟩ :=
            patternFact
          have activeEq : patternActive = active := Subsingleton.elim _ _
          subst patternActive
          have activationFacts := active.activated
          have cubic := cubicFact.1
          have survivor := active.survives
          obtain ⟨_ledgerActive, _ledgerCapacity, _ledgerActivationEq,
              _primitiveCarrierCard, _primitiveCarrierBound,
              _concreteCapacityLedger, objectConnected⟩ := capacityLedger
          refine (fun (outcome :
              Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
                  object ∨
                (SameTokenTypeBHandoffEnvelopeStatement data.toParameters object ∧
                  SameTokenTypeBHandoffStatement data.toParameters object)) =>
            ⟨⟨active, capacity, activationEq, concretePattern,
                Or.imp_right And.left outcome⟩,
              Or.imp_right And.right outcome⟩) ?_
          let activation := capacity.activation
          letI : FinEnum object.Vertex := object.vertices
          letI : DecidableRel object.graph.Adj := object.decideAdj
          letI : DecidableEq object.Vertex := object.vertices.decEq
          -- Edge sets for the physical two-arm attachment skeleton.  These
          -- remain local to this owner and are instantiated only on the
          -- envelope actually constructed below.
          let armEdgeSet (path : List object.Vertex) :
              Finset (Sym2 object.Vertex) :=
            ((path.zip path.tail).toFinset).image
              (fun pair => s(pair.1, pair.2))
          let coreEdgeSet (support : Finset object.Vertex) :
              Finset (Sym2 object.Vertex) :=
            support.biUnion fun vertex =>
              ((support.filter fun other => object.graph.Adj vertex other).image
                fun other => s(vertex, other))
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

          -- Once the separated configurations have produced the paper's
          -- decorated envelope, publish exactly that produced handoff.  Its
          -- remainder admissibility is the downstream Type B lane's theorem,
          -- just as for the existing Type-A exit-`(7)` handoff.
          have handoff_of_envelope
              (core : Finset object.Vertex)
              (envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
                (handoffHighDegree data.toParameters object)
                (handoffAbsorbing data.toParameters object capacity.packing))
              (envelopeCore : envelope.core = core)
              (decorated : envelope.decorations.Nonempty) :
              SameTokenTypeBHandoffEnvelopeStatement data.toParameters object := by
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

          -- The published routing label of `def:same-token-routing-germs`
          -- (`sameTokenActualRoutingLabel`) is this owner's `ρ_t(π)` on every
          -- pair of the certified source pattern.
          have actualRoutingLabel_eq
              (pattern : Finset (Finset (object.Vertex × object.Vertex)))
              (patternSubset : pattern ⊆ ledger.presented.roleFibre token role)
              (pair : Finset (object.Vertex × object.Vertex)) (pairMem : pair ∈ pattern)
              (pairCard : pair.card = 2)
              (demand : object.Vertex × object.Vertex) (demandMem : demand ∈ pair) :
              sameTokenActualRoutingLabel data.toParameters object active cubic capacity certified
                  token role pattern patternSubset pair pairMem demand demandMem =
                routingLabel pair pairCard demand := by
            have fibreMem := patternSubset pairMem
            have scheduleMem : pair ∈ object.portPairSchedule data.threshold :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp fibreMem).1).1
            have pairFacts : pair ⊆ object.excessPorts data.threshold ∧ pair.card = 2 :=
              Finset.mem_powersetCard.mp scheduleMem
            unfold sameTokenActualRoutingLabel
            dsimp only
            refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl
              (Prod.ext (Prod.ext ?_ ?_) (Prod.ext rfl ?_)))))
            rotate_left 2
            · simp only [routingLabel, chordFlag, activation]
              generalize Graph.FiniteObject.canonicalBlocker capacity.activation
                pair = blocker
              rcases blocker with _ | blocker
              · rfl
              · cases blocker <;> rfl
            all_goals
              funext index
              simp only [routingLabel, boundaryProfile, selectedSupport]
              split_ifs with hu bound
              · apply Fin.ext
                dsimp only
                have degreeCongr : ∀ (S T : Finset object.Vertex), S = T → ∀ (i : Nat)
                    (b₁ : i < (List.filter (fun vertex => decide (vertex ∈ S))
                      object.orderedVertices).length)
                    (b₂ : i < (List.filter (fun vertex => decide (vertex ∈ T))
                      object.orderedVertices).length)
                    (p₁ : (List.filter (fun vertex => decide (vertex ∈ S))
                      object.orderedVertices).get ⟨i, b₁⟩ ∈ S)
                    (p₂ : (List.filter (fun vertex => decide (vertex ∈ T))
                      object.orderedVertices).get ⟨i, b₂⟩ ∈ T),
                    (object.induce S).degree ⟨_, p₁⟩ = (object.induce T).degree ⟨_, p₂⟩ := by
                  intro S T equal
                  subst equal
                  intros
                  rfl
                refine degreeCongr _ _ ?_ _ _ _ _ _
                split_ifs
                rfl
              · exfalso
                apply bound
                refine lt_of_lt_of_eq index.2 (Eq.symm ?_)
                have nodup : (List.filter (fun vertex => decide
                    (vertex ∈ (Graph.FiniteObject.surplusPortOfMem hu).support))
                    object.orderedVertices).Nodup :=
                  List.Nodup.filter _ FinEnum.nodup_toList
                rw [← List.toFinset_card_of_nodup nodup]
                have card := selectedSupport_card _ hu
                simp only [selectedSupport, dif_pos hu] at card
                have orderedSet : (List.filter (fun vertex => decide
                    (vertex ∈ (Graph.FiniteObject.surplusPortOfMem hu).support))
                    object.orderedVertices).toFinset =
                      (Graph.FiniteObject.surplusPortOfMem hu).support := by
                  ext vertex
                  simp [Graph.FiniteObject.orderedVertices, FinEnum.mem_toList]
                rw [orderedSet]
                exact card
              · exact absurd (pairFacts.1 (Finset.mem_toList.mp (List.get_mem _ _))) hu

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
                (SameTokenTypeBHandoffEnvelopeStatement data.toParameters object ∧
                  SameTokenTypeBHandoffStatement data.toParameters object) := by
            obtain ⟨pattern, patternSubset, patternShape, large, configurations,
                pairs, first, second, different, left, right, leftMem, rightMem,
                demandsDifferent, routingLabelsEqual⟩ :
                ∃ pattern,
                ∃ patternSubset : pattern ⊆ ledger.presented.roleFibre token role,
                  (Graph.PatternFamily.IsMatching pattern ∨
                    ∃ centre, Graph.PatternFamily.IsStar pattern centre) ∧
                  Graph.SameTokenRoutingGerms.patternBound
                      (Graph.SameTokenRoutingGerms.RoutingLabel
                        data.BoundaryProfile
                        (Graph.WindowCurvature.Label data.windowOrder)) ≤
                    pattern.card ∧
                  (∀ pair ∈ pattern,
                    ∃ responseSupport : Finset object.Vertex,
                      capacity.activation.pairSupport pair =
                          some responseSupport ∧
                        ∀ demand ∈ pair,
                          ∃ configuration :
                              Graph.SameTokenRoutingGerms.RoutingConfiguration
                                object (capacity.sameTokenRoutingSupport token pair)
                                (Graph.CapacityPresentation.tokenSupport token)
                                (capacity.activation.localBuffer demand),
                            configuration.path.head? = some root ∧
                              configuration.path.getLast? = some demand.2) ∧
                  ∃ pairs : ∀ edge ∈ pattern, edge.card = 2,
                  ∃ first second : {edge // edge ∈ pattern}, first ≠ second ∧
                  ∃ left right : object.Vertex × object.Vertex,
                  ∃ _leftMem : left ∈ first.1, ∃ _rightMem : right ∈ second.1,
                    left ≠ right ∧
                      routingLabel first.1 (pairs first.1 first.2) left =
                        routingLabel second.1 (pairs second.1 second.2) right := by
              -- The matching and star arms differ only in how the two
              -- equal-label demands are read from their pattern edges; the
              -- routing paragraph below is common to both.
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
                exact ⟨pattern, patternSubset, Or.inl patternShape, large,
                  configurations, pairs, first, second, different, left, right,
                  leftMem, rightMem, demandsDifferent,
                  by simpa only [attachedLabel] using sameLabel⟩
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
                exact ⟨pattern, patternSubset, Or.inr ⟨centre, patternShape⟩, large,
                  configurations, pairs, first, second, different, left, right,
                  leftMem, rightMem, demandsDifferent,
                  by simpa only [attachedLabel] using sameLabel⟩
            have firstPattern : first.1 ∈ pattern := first.2
            have secondPattern : second.1 ∈ pattern := second.2
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
            obtain ⟨firstConfiguration, secondConfiguration,
                firstValid, secondValid, maximalPrefix⟩ :=
              Graph.SameTokenRoutingArms.exists_maximal_commonPrefix
                (fun (configuration :
                    Graph.SameTokenRoutingGerms.RoutingConfiguration object
                      (capacity.sameTokenRoutingSupport token first.1)
                      (Graph.CapacityPresentation.tokenSupport token)
                      (capacity.activation.localBuffer left)) =>
                  configuration.path)
                (fun (configuration :
                    Graph.SameTokenRoutingGerms.RoutingConfiguration object
                      (capacity.sameTokenRoutingSupport token second.1)
                      (Graph.CapacityPresentation.tokenSupport token)
                      (capacity.activation.localBuffer right)) =>
                  configuration.path)
                (fun (configuration :
                    Graph.SameTokenRoutingGerms.RoutingConfiguration object
                      (capacity.sameTokenRoutingSupport token first.1)
                      (Graph.CapacityPresentation.tokenSupport token)
                      (capacity.activation.localBuffer left)) =>
                  configuration.path.head? = some root ∧
                    configuration.path.getLast? = some left.2)
                (fun (configuration :
                    Graph.SameTokenRoutingGerms.RoutingConfiguration object
                      (capacity.sameTokenRoutingSupport token second.1)
                      (Graph.CapacityPresentation.tokenSupport token)
                      (capacity.activation.localBuffer right)) =>
                  configuration.path.head? = some root ∧
                    configuration.path.getLast? = some right.2)
                (fun (configuration :
                    Graph.SameTokenRoutingGerms.RoutingConfiguration object
                      (capacity.sameTokenRoutingSupport token first.1)
                      (Graph.CapacityPresentation.tokenSupport token)
                      (capacity.activation.localBuffer left)) _ =>
                  configuration.nodup)
                firstConfigurationExists secondConfigurationExists
            obtain ⟨firstRoot, firstTerminalEndpoint⟩ := firstValid
            obtain ⟨secondRoot, secondTerminalEndpoint⟩ := secondValid
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
            -- The support-dependence paragraph, used verbatim by the
            -- parallel and cubic-switch cases: on any connected support
            -- carrying both declared response coordinates, a recorded
            -- type-(e) obstruction or the type-(e) role routes directly, and
            -- otherwise the profile-recording attempted identification of
            -- the two distinct coordinates is rank reducing, so
            -- `AttemptedQuotient.route` returns a sparse exit.
            have supportRoutes :
                ∀ support : Finset object.Vertex,
                  Graph.SupportComponents.Connected.ConnectedOn object support →
                  (∀ coordinate ∈ responseFamily,
                    responseCoordinateSupport coordinate ⊆ support) →
                  Graph.SparseSurplusExit
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK)
                    data.LengthOK object := by
              intro support supportConnected supportCarries
              have supportDependenceExit :
                  Graph.SparseSurplusExit
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK)
                    data.LengthOK object := by
                obtain ⟨attempt, _supportEq, identifiesCoordinates,
                    sameFibre⟩ :=
                  Graph.AttemptedQuotient.exists_profileQuotient_of_avoids
                    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                    data.quadrilateralAccepted avoids support
                    supportConnected supportCarries
                    firstResponseCoordinate firstResponseCoordinate
                    secondResponseCoordinate (by simp [responseFamily])
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
              intro _parallel connected _firstCarried _secondCarried
                _different _declared _base _profile _label
              exact supportRoutes parallelSupport connected (by
                intro coordinate member
                simp only [responseFamily, Finset.mem_insert,
                  Finset.mem_singleton] at member
                rcases member with rfl | rfl
                · exact firstResponseCarriedByParallelSupport
                · exact secondResponseCarriedByParallelSupport)
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
                  Graph.SameTokenRoutingArms.exists_firstEntryPrefix (nextLeft :: tailLeft) core
                    ⟨left.2, rawArmLeftLast, leftEndpointInside⟩
                obtain ⟨secondTerminal, armRight, armRightPrefix,
                    armRightHead, armRightLast, secondTerminalInside,
                    armRightFirstEntry⟩ :=
                  Graph.SameTokenRoutingArms.exists_firstEntryPrefix (nextRight :: tailRight) core
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
                have armLeftSingletonOfStartCore :
                    nextLeft ∈ core → armLeft = [nextLeft] := by
                  intro startCore
                  have startArm : nextLeft ∈ armLeft :=
                    List.mem_of_mem_head? (by simp [armLeftIssued])
                  have startTerminal : nextLeft = firstTerminal :=
                    armLeftFirstEntry nextLeft startArm startCore
                  have lastStart : armLeft.getLast? = some nextLeft := by
                    simpa [startTerminal] using armLeftLast
                  exact Graph.SameTokenRoutingArms.eq_singleton_of_head_last_nodup armLeft nextLeft
                    armLeftIssued lastStart armLeftNodup
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
                  exact supportRoutes switchSupport switchConnected
                    switchCarriesResponseFamily
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
                    Graph.SameTokenRoutingArms.cubic_incidence_of_separation object.graph
                      firstConfiguration.path
                      secondConfiguration.path common separator nextLeft
                      nextRight tailLeft tailRight firstConnectorChain
                      secondConnectorChain firstConnectorSimple
                      secondConnectorSimple leftDecomposition rightDecomposition
                      nextDifferent (cubicDegree.trans cubic)
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
                    handoffHighDegree data.toParameters object separator := by
                  exact lt_of_le_of_ne separatorMinimumDegree
                    (Ne.symm separatorNotCubic)
                have separatorNormalForm :
                    Graph.NormalForm object data.threshold separator :=
                  highCentreNormalForm separator separatorHigh
                have nextLeftCubic :
                    object.degree nextLeft = data.threshold :=
                  separatorNormalForm.neighbourTight separatorNextLeftAdj
                have nextRightCubic :
                    object.degree nextRight = data.threshold :=
                  separatorNormalForm.neighbourTight separatorNextRightAdj
                have denied : ∀ centre firstNeighbour secondNeighbour,
                    ¬ handoffAbsorbing data.toParameters object capacity.packing centre
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
                let skeleton : Finset (Sym2 object.Vertex) :=
                  (armEdgeSet (envelope.arm separator nextLeft) ∪
                    armEdgeSet (envelope.arm separator nextRight) ∪
                    {s(separator, nextLeft), s(separator, nextRight)}) ∪
                    coreEdgeSet envelope.core
                have skeletonEq : skeleton =
                    (armEdgeSet armLeft ∪ armEdgeSet armRight ∪
                      {s(separator, nextLeft), s(separator, nextRight)}) ∪
                      coreEdgeSet core := by
                  simp [skeleton, envelope,
                    Graph.DecoratedHandoff.envelopeOfFirstSeparator,
                    nextDifferent.symm]
                have saturatedLeftForcesCrossing :
                    (∀ edge ∈ object.graph.incidenceFinset nextLeft,
                      edge ∈ skeleton) →
                      nextLeft ∈ armRight := by
                  intro allIncidentInSkeleton
                  have leftDegreeAtLeastThree :
                      3 ≤ object.graph.degree nextLeft := by
                    have lower : 3 ≤ object.degree nextLeft := by
                      rw [nextLeftCubic]
                      exact data.three_le_threshold
                    change 3 ≤ object.graph.degree nextLeft at lower
                    exact lower
                  apply Graph.SameTokenRoutingArms.mem_other_arm_of_saturated object.graph
                    separator
                    nextLeft nextRight left.2 right.2 armLeft armRight
                    separatorNextLeftAdj.ne' nextDifferent
                    armLeftIssued armLeftNodup
                  · intro inCore
                    exact armLeftSingletonOfStartCore
                      (show nextLeft ∈ core from inCore)
                  · exact leftDegreeAtLeastThree
                  · intro edge incident
                    simpa only [skeletonEq, core] using
                      allIncidentInSkeleton edge incident
                have crossingSuppliesRightShortcut :
                    nextLeft ∈ armRight →
                      ∃ before after : List object.Vertex,
                        ∃ shortcut :
                          Graph.SameTokenRoutingGerms.RoutingConfiguration
                            object
                            (capacity.sameTokenRoutingSupport token second.1)
                            (Graph.CapacityPresentation.tokenSupport token)
                            (capacity.activation.localBuffer right),
                          tailRight = before ++ nextLeft :: after ∧
                            shortcut.path =
                              common ++ separator :: nextLeft :: after ∧
                            shortcut.path.head? =
                              secondConfiguration.path.head? ∧
                            shortcut.path.getLast? =
                              secondConfiguration.path.getLast? := by
                  intro crossing
                  have inRaw : nextLeft ∈ nextRight :: tailRight :=
                    armRightPrefix.subset crossing
                  have inTail : nextLeft ∈ tailRight := by
                    rcases List.mem_cons.mp inRaw with equal | inside
                    · exact False.elim (nextDifferent equal)
                    · exact inside
                  exact Graph.SameTokenRoutingArms.RoutingConfiguration.exists_sourcePreserving_shortcut
                    secondConfiguration
                    common separator nextLeft nextRight tailRight
                    rightDecomposition separatorNextLeftAdj inTail
                have crossingExcluded : nextLeft ∉ armRight := by
                  intro crossing
                  obtain ⟨before, after, shortcut, _tailEq,
                      shortcutPath, shortcutHead, shortcutLast⟩ :=
                    crossingSuppliesRightShortcut crossing
                  have shortcutValid :
                      shortcut.path.head? = some root ∧
                        shortcut.path.getLast? = some right.2 :=
                    ⟨shortcutHead.trans secondRoot,
                      shortcutLast.trans secondTerminalEndpoint⟩
                  have maximalComparison :=
                    maximalPrefix firstConfiguration shortcut
                      ⟨firstRoot, firstTerminalEndpoint⟩ shortcutValid
                  have prefixBounds :=
                    Graph.SameTokenRoutingArms.commonPrefixLength_shortcut common
                    separator nextLeft nextRight tailLeft tailRight after
                    nextDifferent
                  have oldPrefix :
                      Graph.SameTokenRoutingGerms.commonPrefixLength
                        firstConfiguration.path secondConfiguration.path =
                          common.length + 1 := by
                    rw [leftDecomposition, rightDecomposition]
                    exact prefixBounds.1
                  have shortcutPrefix :
                      common.length + 2 ≤
                        Graph.SameTokenRoutingGerms.commonPrefixLength
                          firstConfiguration.path shortcut.path := by
                    rw [leftDecomposition, shortcutPath]
                    exact prefixBounds.2
                  omega
                have outsideSkeletonIncidence :
                    ∃ edge ∈ object.graph.incidenceFinset nextLeft,
                      edge ∉ skeleton := by
                  classical
                  by_contra noEdge
                  apply crossingExcluded
                  apply saturatedLeftForcesCrossing
                  intro edge incident
                  by_contra outside
                  exact noEdge ⟨edge, incident, outside⟩
                have outsideSkeletonNeighbour :
                    ∃ neighbour : object.Vertex,
                      object.graph.Adj nextLeft neighbour ∧
                        s(nextLeft, neighbour) ∉ skeleton := by
                  obtain ⟨edge, incident, outside⟩ :=
                    outsideSkeletonIncidence
                  have inIncidenceSet :
                      edge ∈ object.graph.incidenceSet nextLeft :=
                    (object.graph.mem_incidenceFinset nextLeft edge).mp
                      incident
                  obtain ⟨neighbour, edgeEq⟩ :=
                    Sym2.mem_iff_exists.mp inIncidenceSet.2
                  refine ⟨neighbour, ?_, ?_⟩
                  · have graphIncidence :
                        s(nextLeft, neighbour) ∈
                          object.graph.incidenceSet nextLeft := by
                      simpa only [edgeEq] using inIncidenceSet
                    exact (object.graph.mem_incidenceSet nextLeft
                      neighbour).mp graphIncidence
                  · simpa only [edgeEq] using outside
                let envelopeRegion : Finset object.Vertex :=
                  core ∪ armLeft.toFinset ∪ armRight.toFinset ∪
                    {separator}
                have outsideSkeletonLocation :
                    ∃ neighbour : object.Vertex,
                      object.graph.Adj nextLeft neighbour ∧
                        s(nextLeft, neighbour) ∉ skeleton ∧
                        neighbour ≠ separator ∧
                        (neighbour ∈ core ∨
                          (neighbour ∉ core ∧ neighbour ∈ armLeft) ∨
                          (neighbour ∉ core ∧ neighbour ∉ armLeft ∧
                            neighbour ∈ armRight) ∨
                          neighbour ∉ envelopeRegion) := by
                  obtain ⟨neighbour, adjacent, outside⟩ :=
                    outsideSkeletonNeighbour
                  have notCentre : neighbour ≠ separator := by
                    intro equal
                    subst neighbour
                    have centreEdge :
                        s(separator, nextLeft) ∈ skeleton := by
                      rw [skeletonEq]
                      simp
                    apply outside
                    rw [Sym2.eq_swap (a := nextLeft)
                      (b := separator)]
                    exact centreEdge
                  refine ⟨neighbour, adjacent, outside, notCentre, ?_⟩
                  by_cases inCore : neighbour ∈ core
                  · exact Or.inl inCore
                  · by_cases inLeft : neighbour ∈ armLeft
                    · exact Or.inr (Or.inl ⟨inCore, inLeft⟩)
                    · by_cases inRight : neighbour ∈ armRight
                      · exact Or.inr (Or.inr
                          (Or.inl ⟨inCore, inLeft, inRight⟩))
                      · exact Or.inr (Or.inr (Or.inr (by
                          simp [envelopeRegion, inCore, inLeft,
                            inRight, notCentre])))
                have outsideSkeletonReturn :
                    ∃ neighbour : object.Vertex,
                      ∃ adjacent : object.graph.Adj nextLeft neighbour,
                        s(nextLeft, neighbour) ∉ skeleton ∧
                          (⟨nextLeft, neighbour, adjacent⟩ :
                            Graph.EdgeContraction object).HasReturn := by
                  obtain ⟨neighbour, adjacent, outside⟩ :=
                    outsideSkeletonNeighbour
                  exact ⟨neighbour, adjacent, outside,
                    bridgeless ⟨nextLeft, neighbour, adjacent⟩⟩
                have envelopeCore : envelope.core = core := rfl
                have decorated : envelope.decorations.Nonempty := by
                  simp [envelope,
                    Graph.DecoratedHandoff.envelopeOfFirstSeparator]
                exact Or.inr ⟨handoff_of_envelope core envelope envelopeCore
                    decorated, by
                  obtain ⟨neighbour, adjacent, outside, notCentre, _location⟩ :=
                    outsideSkeletonLocation
                  have labelEq :=
                    (actualRoutingLabel_eq pattern patternSubset first.1
                      firstPattern (pairs first.1 firstPattern) left
                      leftMem).trans
                    (routingLabelsEqual.trans
                      (actualRoutingLabel_eq pattern patternSubset second.1
                        secondPattern (pairs second.1 secondPattern) right
                        rightMem).symm)
                  unfold SameTokenTypeBHandoffStatement
                  intro armEdges coreEdges firstEntry
                  refine ⟨active, capacity, activationEq, cubic, certified, ?_⟩
                  intro sourceLedger
                  refine ⟨token, role, tokenMem, _positiveCoupledExcess,
                    _multiplicityBound, _quantitativePattern, _sourceClass,
                    _sourceClassEq, root, rootEq, ?_⟩
                  intro configuration valid routed sourceEnvelope
                  have source : routed pattern ∧
                      sourceEnvelope pattern patternSubset :=
                    ⟨⟨large, configurations⟩,
                    first.1, firstPattern, second.1, secondPattern,
                    fun edgeEqual => different (Subtype.ext edgeEqual),
                    left, leftMem, right, rightMem, labelEq,
                    firstConfiguration, secondConfiguration,
                    ⟨firstRoot, firstTerminalEndpoint⟩,
                    ⟨secondRoot, secondTerminalEndpoint⟩, maximalPrefix,
                    separator, nextLeft, nextRight, common, tailLeft,
                    tailRight, leftDecomposition, rightDecomposition,
                    nextDifferent, armLeft, armRight,
                    ⟨armLeftPrefix, armLeftHead, firstTerminal,
                      firstTerminalInside, armLeftLast, armLeftFirstEntry⟩,
                    ⟨armRightPrefix, armRightHead, secondTerminal,
                      secondTerminalInside, armRightLast,
                      armRightFirstEntry⟩,
                    separatorNextLeftAdj, separatorNextRightAdj,
                    armLeftIssued, armRightIssued, armLeftChain,
                    armRightChain, armLeftNodup, armRightNodup,
                    ⟨firstTerminal, armLeftLast, firstTerminalInside⟩,
                    ⟨secondTerminal, armRightLast, secondTerminalInside⟩,
                    armLeftInterior, armRightInterior, separatorHigh, avoids,
                    denied _ _ _, denied _ _ _, envelope, rfl,
                    nextLeft, by simp, neighbour, adjacent, notCentre,
                    outside⟩
                  rcases patternShape with matching | ⟨centre, star⟩
                  · exact Or.inl ⟨pattern, patternSubset, matching, source⟩
                  · exact Or.inr ⟨centre, pattern, patternSubset, star, source⟩⟩
          exact routedOutcome
      let routing : (K .bottleneckRouting).At inputs.current := ⟨routedBoth.1⟩
      let handoff : (K .typeBHandoff).At inputs.current := ⟨by
          rcases routedBoth.2 with sparseExit | typeBHandoff
          · exact False.elim
              ((inputs.get (K .activeSurplusDemands)).down.survives sparseExit)
          · exact typeBHandoff⟩
      .cons (key := K .bottleneckRouting)
        routing
        (.cons (key := K .typeBHandoff) handoff .nil))

end Hypostructure.Graph.Strategy.Spine
