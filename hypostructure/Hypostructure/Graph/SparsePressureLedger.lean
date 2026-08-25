import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.SparseEntropySandwich

/-!
# From the entropy sandwich to the object's certified capacity ledger and the
square-root surplus estimate

Nodes `[131]`, `[137]` and `[138]` of the sparse surplus branch, at the level of
the finite arithmetic the rows commit.

* `prop:sparse-entropy-sandwich-with-blockers`, in the log-cleared form
  `entropySandwich` already proves, followed by `log₂`: from
  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)` and `C(N,m₀) ≤ 2^{|ℐ_spine| + E}` one gets
  `|Π_free| ≤ E + (m − m₀)(⌊log₂ n⌋ + 1)` (`freeCount_le_of_sandwich`); with
  `lem:incremental-skeleton-room`'s `2(m − m₀) ≤ σ + 2` that is the manuscript's
  `E_spine(n) + (½σ(G) + 1) log₂ n`.
* `def:capacity-token-ledger` at a declared presentation, certified with the
  node-`[129]` deficit and that budget (`certifiedLedger_of_sandwich`), which is
  what `[137]`'s second production and `[138]`'s estimate consume.
* `cor:spine-lower-bound-surplus-estimates` / `[138]`: at the full pair schedule
  (`prop:sparse-entropy-sandwich`), `C(σ,2)` is bounded by the same budget, so
  `σ(G) ≤ C_sp ⌈√n⌉` by the generic quadratic absorption
  (`surplus_le_scale_of_pairSandwich`); and at a capped capacity ledger
  (`prop:single-graph-sparse-pressure-routing` (a)) the same estimate follows
  from `R_L(n)` (`surplus_le_scale_of_capped`).

Nothing here decides whether the entropy count holds: that is the node's own
decision on its residual.  These are the consequences it commits once it does.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- Every vertex of the canonical blocker support lies in the already declared
connector core `X_π ∪ ⋃ R_p`.  This is the clause-by-clause support
reading needed to turn the paper's blocker object into a connector; no support
or path is supplied by a caller. -/
theorem CapacityPresentation.chargeSupport_subset_pairConnectorSupport
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold order : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (capacity : CapacityPresentation object threshold order)
    (activationEq : capacity.activation =
      recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairSubset : pair ⊆ object.excessPorts threshold)
    (connected : SupportComponents.Connected.ConnectedOn object
      object.vertexFinset) :
    FiniteObject.chargeSupport capacity.activation capacity.carrier pair ⊆
      capacity.pairConnectorSupport pair := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let base := pairResponseActivation active
  have pairSupportSome :=
    FiniteObject.DemandActivation.pairSupport_isSome_of_connected
      capacity.activation pair connected
  obtain ⟨support, selected⟩ := Option.isSome_iff_exists.mp pairSupportSome
  have supportFacts :=
    FiniteObject.DemandActivation.pairSupport_mem_candidates selected
  have selectedBase : base.pairSupport pair = some support := by
    have recordedSelected := selected
    rw [activationEq] at recordedSelected
    simpa [base, FiniteObject.DemandActivation.pairSupport,
      FiniteObject.DemandActivation.pairSeed,
      recordSparsePairDEBlockers] using recordedSelected
  intro vertex vertexMem
  rcases blockerCase : FiniteObject.canonicalBlocker capacity.activation pair with
    _ | blocker
  · simp [FiniteObject.chargeSupport, blockerCase] at vertexMem
  · have blockerMem :=
      FiniteObject.canonicalBlocker_mem capacity.activation blockerCase
    simp only [FiniteObject.chargeSupport, blockerCase] at vertexMem
    have inSupport (member : vertex ∈ support) :
        vertex ∈ capacity.pairConnectorSupport pair := by
      unfold CapacityPresentation.pairConnectorSupport
      rw [selected]
      exact Finset.mem_union_left _ member
    have inReturn {demand : object.Vertex × object.Vertex}
        (demandMem : demand ∈ pair)
        (member : vertex ∈ capacity.activation.returnSupport demand) :
        vertex ∈ capacity.pairConnectorSupport pair := by
      unfold CapacityPresentation.pairConnectorSupport
      rw [selected]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨demand, demandMem, member⟩)
    have inSeed {demand : object.Vertex × object.Vertex}
        (demandMem : demand ∈ pair)
        (member : vertex ∈ capacity.activation.declaredSupport demand) :
        vertex ∈ capacity.pairConnectorSupport pair := by
      apply inSupport
      apply supportFacts.1
      exact FiniteObject.DemandActivation.declaredSupport_subset_pairSeed
        capacity.activation demandMem member
    cases blocker with
    | sharedDeclaredSupport item =>
        obtain ⟨left, leftMem, _right, _rightMem, _distinct, shared⟩ :=
          (FiniteObject.DemandActivation.sharedDeclaredSupport_mem_blockers_iff
            capacity.activation).mp blockerMem
        cases item with
        | vertex root =>
            have equality : vertex = root := by
              simpa [FiniteObject.Blocker.declaredSupport] using vertexMem
            subst vertex
            exact inSeed leftMem
              (FiniteObject.DemandActivation.mem_both_of_vertex_mem_sharedItems
                shared).1
        | incidence incidence =>
            have endpoint : vertex = incidence.1 ∨ vertex = incidence.2 := by
              simpa [FiniteObject.Blocker.declaredSupport] using vertexMem
            have endpoints :=
              FiniteObject.DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems
                shared
            rcases endpoint with rfl | rfl
            · exact inSeed leftMem endpoints.1
            · exact inSeed leftMem endpoints.2.1
    | sharedReturnSupport item =>
        obtain ⟨left, leftMem, _right, _rightMem, _distinct, shared⟩ :=
          (FiniteObject.DemandActivation.sharedReturnSupport_mem_blockers_iff
            capacity.activation).mp blockerMem
        cases item with
        | vertex root =>
            have equality : vertex = root := by
              simpa [FiniteObject.Blocker.declaredSupport] using vertexMem
            subst vertex
            exact inReturn leftMem
              (FiniteObject.DemandActivation.mem_both_of_vertex_mem_sharedItems
                shared).1
        | incidence incidence =>
            have endpoint : vertex = incidence.1 ∨ vertex = incidence.2 := by
              simpa [FiniteObject.Blocker.declaredSupport] using vertexMem
            have endpoints :=
              FiniteObject.DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems
                shared
            rcases endpoint with rfl | rfl
            · exact inReturn leftMem endpoints.1
            · exact inReturn leftMem endpoints.2.1
    | sharedLocalBuffer root =>
        have equality : vertex = root := by
          simpa [FiniteObject.Blocker.declaredSupport] using vertexMem
        subst vertex
        obtain ⟨left, leftMem, _right, _rightMem, _distinct,
            leftLocal, _rightLocal⟩ :=
          (FiniteObject.DemandActivation.sharedLocalBuffer_mem_blockers_iff
            capacity.activation).mp blockerMem
        exact inSeed leftMem
          (capacity.activation.localBuffer_subset_declaredSupport left leftLocal)
    | boundaryProfile coordinate =>
        have coordinateMem :
            coordinate ∈ capacity.activation.profileObstructions pair := by
          simpa [FiniteObject.DemandActivation.blockers] using blockerMem
        have recordedMem : coordinate ∈
            (recordSparsePairDEBlockers (Baseline := Baseline)
              (LengthOK := LengthOK) base
              (object.portPairSchedule threshold)).profileObstructions pair := by
          simpa [base, activationEq] using coordinateMem
        have coordinateEq := coordinate_eq_of_mem_recordedProfileObstructions
          (Baseline := Baseline) (LengthOK := LengthOK) base
          (object.portPairSchedule threshold) recordedMem
        have member : vertex ∈ support := by
          simpa [FiniteObject.Blocker.declaredSupport,
            CapacityPresentation.carrier, coordinateEq,
            FiniteObject.DemandActivation.pairCoordinate, selectedBase] using vertexMem
        exact inSupport member
    | targetResponse coordinate =>
        have coordinateMem :
            coordinate ∈ capacity.activation.responseObstructions pair := by
          simpa [FiniteObject.DemandActivation.blockers] using blockerMem
        have recordedMem : coordinate ∈
            (recordSparsePairDEBlockers (Baseline := Baseline)
              (LengthOK := LengthOK) base
              (object.portPairSchedule threshold)).responseObstructions pair := by
          simpa [base, activationEq] using coordinateMem
        have coordinateEq := coordinate_eq_of_mem_recordedResponseObstructions
          (Baseline := Baseline) (LengthOK := LengthOK) base
          (object.portPairSchedule threshold) recordedMem
        have member : vertex ∈ support := by
          simpa [FiniteObject.Blocker.declaredSupport,
            CapacityPresentation.carrier, coordinateEq,
            FiniteObject.DemandActivation.pairCoordinate, selectedBase] using vertexMem
        exact inSupport member
    | arithmeticChordSet chords =>
        have chordsMem : chords ∈ capacity.activation.chordObstructions pair := by
          simpa [FiniteObject.DemandActivation.blockers] using blockerMem
        have baseChordsMem : chords ∈ base.chordObstructions pair := by
          simpa [base, activationEq, recordSparsePairDEBlockers] using chordsMem
        have obstruction :=
          suppressionObstruction_of_mem_pairResponseChordObstructions active
            baseChordsMem
        have chordsSubset := chords_subset_pair_of_suppressionObstruction obstruction
        have expanded : vertex ∈ chords.biUnion (fun chord =>
            let ends := pairResponseChordEnds active chord
            {ends.1, ends.2}) := by
          simpa [FiniteObject.Blocker.declaredSupport,
            CapacityPresentation.carrier, base, activationEq,
            recordSparsePairDEBlockers] using vertexMem
        obtain ⟨demand, demandChord, vertexEnd⟩ := Finset.mem_biUnion.mp expanded
        have demandPair := chordsSubset demandChord
        have demandActive := pairSubset demandPair
        have endsLocal := pairResponseChordEnds_mem_localBuffer active demandActive
        have endpointLocal : vertex ∈ base.localBuffer demand := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using
            (show vertex = (pairResponseChordEnds active demand).1 ∨
                vertex = (pairResponseChordEnds active demand).2 from
              by simpa using vertexEnd).elim
              (fun equality => equality ▸ endsLocal.1)
              (fun equality => equality ▸ endsLocal.2)
        have endpointDeclared : vertex ∈ base.declaredSupport demand :=
          base.localBuffer_subset_declaredSupport demand endpointLocal
        have capacityDeclared :
            vertex ∈ capacity.activation.declaredSupport demand := by
          simpa [base, activationEq, recordSparsePairDEBlockers] using
            endpointDeclared
        exact inSeed demandPair capacityDeclared

/-- A pair charged to `t` contains the canonical root of `t` in its declared
connector core.  The geometric charge cases read this directly from
`supp(B_π)`; the primitive shoulder-chord case reads the selected port named
by the actual recorded chord obstruction. -/
theorem CapacityPresentation.tokenRoot_mem_pairConnectorSupport_of_charge
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold order : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (capacity : CapacityPresentation object threshold order)
    (activationEq : capacity.activation =
      recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    {token : FiniteObject.CapacityToken object}
    (pairSubset : pair ⊆ object.excessPorts threshold)
    (connected : SupportComponents.Connected.ConnectedOn object
      object.vertexFinset)
    (charged : FiniteObject.capacityCharge capacity.activation capacity.carrier
      threshold capacity.packing pair = some token) :
    CapacityPresentation.tokenRoot token ∈
      capacity.pairConnectorSupport pair := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have chargeSubset := capacity.chargeSupport_subset_pairConnectorSupport
    active activationEq pairSubset connected
  rw [FiniteObject.capacityCharge] at charged
  rcases windowCase : FiniteObject.windowJoinChoice capacity.activation
      capacity.carrier capacity.packing pair with _ | incidence
  · rw [windowCase] at charged
    rcases crossCase : FiniteObject.crossWindowChoice capacity.activation
        capacity.carrier capacity.packing pair with _ | incidence
    · rw [crossCase] at charged
      rcases remainderCase : FiniteObject.remainderVertexChoice
          capacity.activation capacity.carrier threshold capacity.packing pair with
        _ | vertex
      · rw [remainderCase] at charged
        rcases blockerCase : FiniteObject.canonicalBlocker capacity.activation pair with
          _ | blocker
        · rw [blockerCase] at charged
          cases charged
        · rw [blockerCase, Option.map_eq_some_iff] at charged
          obtain ⟨item, carrier, rfl⟩ := charged
          have blockerMem :=
            FiniteObject.canonicalBlocker_mem capacity.activation blockerCase
          cases blocker with
          | sharedDeclaredSupport blockerItem =>
              cases blockerItem with
              | vertex root =>
                  rw [FiniteObject.Blocker.carrier] at carrier
                  cases carrier
                  apply chargeSubset
                  simp [FiniteObject.chargeSupport, blockerCase,
                    FiniteObject.Blocker.declaredSupport,
                    CapacityPresentation.tokenRoot]
              | incidence incidence =>
                  rw [FiniteObject.Blocker.carrier] at carrier
                  cases carrier
                  apply chargeSubset
                  simp [FiniteObject.chargeSupport, blockerCase,
                    FiniteObject.Blocker.declaredSupport,
                    CapacityPresentation.tokenRoot]
          | sharedReturnSupport blockerItem =>
              cases blockerItem with
              | vertex root =>
                  rw [FiniteObject.Blocker.carrier] at carrier
                  cases carrier
                  apply chargeSubset
                  simp [FiniteObject.chargeSupport, blockerCase,
                    FiniteObject.Blocker.declaredSupport,
                    CapacityPresentation.tokenRoot]
              | incidence incidence =>
                  rw [FiniteObject.Blocker.carrier] at carrier
                  cases carrier
                  apply chargeSubset
                  simp [FiniteObject.chargeSupport, blockerCase,
                    FiniteObject.Blocker.declaredSupport,
                    CapacityPresentation.tokenRoot]
          | sharedLocalBuffer root =>
              rw [FiniteObject.Blocker.carrier] at carrier
              cases carrier
              apply chargeSubset
              simp [FiniteObject.chargeSupport, blockerCase,
                FiniteObject.Blocker.declaredSupport,
                CapacityPresentation.tokenRoot]
          | boundaryProfile coordinate =>
              rw [FiniteObject.Blocker.carrier,
                Option.map_eq_some_iff] at carrier
              obtain ⟨root, rootHead, rfl⟩ := carrier
              apply chargeSubset
              simp only [FiniteObject.chargeSupport, blockerCase]
              simp only [FiniteObject.Blocker.declaredSupport,
                CapacityPresentation.tokenRoot]
              simpa using List.mem_of_mem_head? rootHead
          | targetResponse coordinate =>
              rw [FiniteObject.Blocker.carrier,
                Option.map_eq_some_iff] at carrier
              obtain ⟨root, rootHead, rfl⟩ := carrier
              apply chargeSubset
              simp only [FiniteObject.chargeSupport, blockerCase]
              simp only [FiniteObject.Blocker.declaredSupport,
                CapacityPresentation.tokenRoot]
              simpa using List.mem_of_mem_head? rootHead
          | arithmeticChordSet chords =>
              rw [FiniteObject.Blocker.carrier,
                Option.map_eq_some_iff] at carrier
              obtain ⟨port, portHead, rfl⟩ := carrier
              have portChosen : port ∈
                  (chords.image capacity.carrier.chordPort ∩
                    object.excessPorts threshold) := by
                simpa using List.mem_of_mem_head? portHead
              have portActive := (Finset.mem_inter.mp portChosen).2
              have portImage := (Finset.mem_inter.mp portChosen).1
              obtain ⟨chord, chordMem, chordPortEq⟩ :=
                Finset.mem_image.mp portImage
              have chordPortConcrete : capacity.carrier.chordPort = id := by
                simp [CapacityPresentation.carrier, activationEq,
                  recordSparsePairDEBlockers]
              have chordEq : chord = port := by
                simpa [chordPortConcrete] using chordPortEq
              subst chord
              have chordsMem :
                  chords ∈ capacity.activation.chordObstructions pair := by
                simpa [FiniteObject.DemandActivation.blockers] using blockerMem
              have baseChordsMem : chords ∈
                  (pairResponseActivation active).chordObstructions pair := by
                simpa [activationEq, recordSparsePairDEBlockers] using chordsMem
              have obstruction :=
                suppressionObstruction_of_mem_pairResponseChordObstructions
                  active baseChordsMem
              have portPair :=
                chords_subset_pair_of_suppressionObstruction obstruction chordMem
              have pairSupportSome :=
                FiniteObject.DemandActivation.pairSupport_isSome_of_connected
                  capacity.activation pair connected
              obtain ⟨support, selected⟩ :=
                Option.isSome_iff_exists.mp pairSupportSome
              have supportFacts :=
                FiniteObject.DemandActivation.pairSupport_mem_candidates selected
              have endpointLocal :
                  port.2 ∈ capacity.activation.localBuffer port := by
                have baseLocal : port.2 ∈
                    (pairResponseActivation active).localBuffer port := by
                  rw [pairResponseActivation_localBuffer_of_mem active portActive]
                  exact FiniteObject.SurplusPort.endpoint_mem_support _
                simpa [activationEq, recordSparsePairDEBlockers] using baseLocal
              have endpointSupport : port.2 ∈ support := by
                apply supportFacts.1
                apply FiniteObject.DemandActivation.declaredSupport_subset_pairSeed
                  capacity.activation portPair
                exact capacity.activation.localBuffer_subset_declaredSupport
                  port endpointLocal
              unfold CapacityPresentation.pairConnectorSupport
              rw [selected]
              exact Finset.mem_union_left _ endpointSupport
      · rw [remainderCase] at charged
        cases charged
        apply chargeSubset
        have inside : vertex ∈
            (object.remainderSupport capacity.packing).filter fun candidate =>
              candidate ∈ FiniteObject.chargeSupport capacity.activation
                capacity.carrier pair ∧ threshold < object.degree candidate := by
          simpa [FiniteObject.remainderVertexChoice] using
            List.mem_of_mem_head? remainderCase
        exact (Finset.mem_filter.mp inside).2.1
    · rw [crossCase] at charged
      cases charged
      apply chargeSubset
      have inside : incidence ∈
          (object.crossWindowIncidences capacity.packing).filter fun candidate =>
            candidate.1 ∈ FiniteObject.chargeSupport capacity.activation
                capacity.carrier pair ∧
              candidate.2 ∈ FiniteObject.chargeSupport capacity.activation
                capacity.carrier pair := by
        simpa [FiniteObject.crossWindowChoice] using
          List.mem_of_mem_head? crossCase
      exact (Finset.mem_filter.mp inside).2.1
  · rw [windowCase] at charged
    cases charged
    apply chargeSubset
    have inside : incidence ∈
        (object.windowRemainderIncidences capacity.packing).filter fun candidate =>
          candidate.1 ∈ FiniteObject.chargeSupport capacity.activation
              capacity.carrier pair ∧
            candidate.2 ∈ FiniteObject.chargeSupport capacity.activation
              capacity.carrier pair := by
      simpa [FiniteObject.windowJoinChoice] using
        List.mem_of_mem_head? windowCase
    exact (Finset.mem_filter.mp inside).2.1

/-- The connector core carried by the concrete capacity presentation is
connected: it is `X_π` with the active demands' already canonical returns
glued at their selected endpoints. -/
theorem CapacityPresentation.pairConnectorSupport_connectedOn
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold order : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (capacity : CapacityPresentation object threshold order)
    (activationEq : capacity.activation =
      recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairSubset : pair ⊆ object.excessPorts threshold)
    (connected : SupportComponents.Connected.ConnectedOn object
      object.vertexFinset) :
    SupportComponents.Connected.ConnectedOn object
      (capacity.pairConnectorSupport pair) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨support, selected⟩ := Option.isSome_iff_exists.mp
    (FiniteObject.DemandActivation.pairSupport_isSome_of_connected
      capacity.activation pair connected)
  have selectedRecorded := selected
  rw [activationEq] at selectedRecorded
  have joined := recordedPairConnector_connectedOn active pairSubset
    selectedRecorded
  unfold CapacityPresentation.pairConnectorSupport
  rw [selected]
  simpa [activationEq, recordSparsePairDEBlockers] using joined

/-- The paper-declared same-token connector configuration, derived from the
registered active-family and capacity-presentation facts.  Its root is the
canonical root of the shared token, and its support is exactly the existing
`Z(π;t,r)` support definition. -/
theorem CapacityPresentation.exists_sameRootRoutingConfiguration_of_charge
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold order : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (capacity : CapacityPresentation object threshold order)
    (activationEq : capacity.activation =
      recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    {token : FiniteObject.CapacityToken object}
    (pairSubset : pair ⊆ object.excessPorts threshold)
    (connected : SupportComponents.Connected.ConnectedOn object
      object.vertexFinset)
    (charged : FiniteObject.capacityCharge capacity.activation capacity.carrier
      threshold capacity.packing pair = some token)
    {demand : object.Vertex × object.Vertex} (demandMem : demand ∈ pair) :
    ∃ configuration : SameTokenRoutingGerms.RoutingConfiguration object
        (capacity.sameTokenRoutingSupport token pair)
          (CapacityPresentation.tokenSupport token)
          (capacity.activation.localBuffer demand),
      configuration.path.head? =
        some (CapacityPresentation.tokenRoot token) ∧
      configuration.path.getLast? = some demand.2 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have demandActive := pairSubset demandMem
  have connectorConnected := capacity.pairConnectorSupport_connectedOn
    active activationEq pairSubset connected
  have rootConnector := capacity.tokenRoot_mem_pairConnectorSupport_of_charge
    active activationEq pairSubset connected charged
  have rootSource := CapacityPresentation.tokenRoot_mem_tokenSupport token
  have endpointLocal : demand.2 ∈ capacity.activation.localBuffer demand := by
    have baseLocal : demand.2 ∈
        (pairResponseActivation active).localBuffer demand := by
      rw [pairResponseActivation_localBuffer_of_mem active demandActive]
      exact FiniteObject.SurplusPort.endpoint_mem_support _
    simpa [activationEq, recordSparsePairDEBlockers] using baseLocal
  have selectedNonempty :
      (capacity.activation.localBuffer demand).Nonempty :=
    ⟨demand.2, endpointLocal⟩
  have selectedSubset : capacity.activation.localBuffer demand ⊆
      capacity.pairConnectorSupport pair := by
    intro vertex vertexLocal
    obtain ⟨support, selected⟩ := Option.isSome_iff_exists.mp
      (FiniteObject.DemandActivation.pairSupport_isSome_of_connected
        capacity.activation pair connected)
    have vertexSupport : vertex ∈ support := by
      apply (FiniteObject.DemandActivation.pairSupport_mem_candidates selected).1
      apply FiniteObject.DemandActivation.declaredSupport_subset_pairSeed
        capacity.activation demandMem
      exact capacity.activation.localBuffer_subset_declaredSupport demand vertexLocal
    unfold CapacityPresentation.pairConnectorSupport
    rw [selected]
    exact Finset.mem_union_left _ vertexSupport
  have connectorSubset : capacity.pairConnectorSupport pair ⊆
      capacity.sameTokenRoutingSupport token pair := by
    intro vertex member
    unfold CapacityPresentation.sameTokenRoutingSupport
    exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _ member)))
  obtain ⟨walk, isPath, inside⟩ :=
    connectorConnected.2 rootConnector (selectedSubset endpointLocal)
  let configuration := SameTokenRoutingGerms.RoutingConfiguration.ofWalk walk
    isPath rootSource
      (fun item member => connectorSubset (inside item member)) endpointLocal
  refine ⟨configuration, ?_, ?_⟩
  · change walk.support.head? =
      some (CapacityPresentation.tokenRoot token)
    rw [List.head?_eq_some_head walk.support_ne_nil, walk.head_support]
  · change walk.support.getLast? = some demand.2
    rw [List.getLast?_eq_getLast_of_ne_nil walk.support_ne_nil,
      walk.getLast_support]

/-- The canonical response support `X_π` and all declared same-token
configurations of one charged pair, published together.  This is the package
the homogeneous-pattern rows retain for node `[144]`: a consumer never chooses
`X_π` again after reading the ledger entry. -/
theorem CapacityPresentation.exists_sameRootRoutingConfigurationFamily_of_charge
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold order : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (capacity : CapacityPresentation object threshold order)
    (activationEq : capacity.activation =
      recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) (object.portPairSchedule threshold))
    {pair : Finset (object.Vertex × object.Vertex)}
    {token : FiniteObject.CapacityToken object}
    (pairSubset : pair ⊆ object.excessPorts threshold)
    (connected : SupportComponents.Connected.ConnectedOn object
      object.vertexFinset)
    (charged : FiniteObject.capacityCharge capacity.activation capacity.carrier
      threshold capacity.packing pair = some token) :
    ∃ responseSupport : Finset object.Vertex,
      capacity.activation.pairSupport pair = some responseSupport ∧
        ∀ demand ∈ pair,
          ∃ configuration : SameTokenRoutingGerms.RoutingConfiguration object
              (capacity.sameTokenRoutingSupport token pair)
                (CapacityPresentation.tokenSupport token)
                (capacity.activation.localBuffer demand),
            configuration.path.head? =
                some (CapacityPresentation.tokenRoot token) ∧
              configuration.path.getLast? = some demand.2 := by
  obtain ⟨responseSupport, selected⟩ := Option.isSome_iff_exists.mp
    (FiniteObject.DemandActivation.pairSupport_isSome_of_connected
      capacity.activation pair connected)
  refine ⟨responseSupport, selected, ?_⟩
  intro demand demandMem
  exact capacity.exists_sameRootRoutingConfiguration_of_charge active
    activationEq pairSubset connected charged demandMem

/-- `n^k ≤ 2^{k(⌊log₂ n⌋+1)}`. -/
theorem pow_le_two_pow_mul_log2_succ (n k : Nat) :
    n ^ k ≤ 2 ^ (k * (Nat.log2 n + 1)) := by
  rw [Nat.pow_mul']
  exact Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_log2_self) k

/-- **`prop:sparse-entropy-sandwich-with-blockers`, after `log₂`.**  From the
entropy count on the mixed family and the baseline demand,
`|Π_free| ≤ E + (m − m₀)(⌊log₂ n⌋ + 1)`. -/
theorem freeCount_le_of_sandwich (object : FiniteObject.{u})
    {baselineDegree spineCount freeCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + freeCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    freeCount ≤ deficit +
      (object.edgeCount - cubicBaselineEdgeCount object.vertexCount baselineDegree) *
        (Nat.log2 object.vertexCount + 1) := by
  have sandwich := entropySandwich object baseline above entropy demand
  set slack := object.edgeCount - cubicBaselineEdgeCount object.vertexCount baselineDegree
  have bound : 2 ^ freeCount ≤ 2 ^ (deficit + slack * (Nat.log2 object.vertexCount + 1)) := by
    calc 2 ^ freeCount ≤ 2 ^ deficit * object.vertexCount ^ slack := sandwich
      _ ≤ 2 ^ deficit * 2 ^ (slack * (Nat.log2 object.vertexCount + 1)) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow_mul_log2_succ _ _)
      _ = 2 ^ (deficit + slack * (Nat.log2 object.vertexCount + 1)) := by rw [pow_add]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 bound

/-- **The object's certified capacity ledger at a declared presentation, from
the sandwich.**  `def:capacity-token-ledger` with `lem:capacity-token-supply`,
node `[130]`'s pair count, `𝔗_cap ≠ ∅`, and the entropy budget
`E + (m − m₀)(⌊log₂ n⌋+1)` of `prop:sparse-entropy-sandwich-with-blockers`. -/
noncomputable def certifiedLedger_of_sandwich {object : FiniteObject.{u}}
    {threshold order deficitScale : Nat}
    (data : CapacityPresentation object threshold order)
    (baseline : 2 ≤ threshold)
    (above : cubicBaselineEdgeCount object.vertexCount threshold ≤ object.edgeCount)
    (spineCount deficit : Nat)
    (demand : cubicBaselineBudget object.vertexCount threshold ≤
      2 ^ (spineCount + deficit))
    (deficit_le : deficit ≤ deficitScale * object.vertexCount)
    (slack_le : object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold ≤
      object.degreeSurplus threshold)
    (entropy : 2 ^ (spineCount +
      (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        data.tokenOrder data.Eligible data.eligibleDecidable).card) ≤ skeletonBudget object)
    (scheduleCard : (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2)
    (orderNonempty : data.tokens.Nonempty)
    (supply : data.tokens.card ≤
      object.capacityTokenSupply threshold + object.degreeSurplus threshold) :
    CertifiedObjectCapacityLedger object threshold order deficitScale data where
  ledger := ObjectCapacityLedger.ofCapacityCharge data scheduleCard orderNonempty
    (deficit + (object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold) *
      (Nat.log2 object.vertexCount + 1))
    (freeCount_le_of_sandwich object baseline above entropy demand) supply
  spineDeficit := deficit
  edgeSlack := object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold
  entropyBudget_eq := by
    simp only [ObjectCapacityLedger.ofCapacityCharge]
    ring
  spineDeficit_le := deficit_le
  edgeSlack_le := slack_le

/-- **`[138]` from `prop:single-graph-sparse-pressure-routing` (a).**  When every
capacity ledger of the object respects the geometric cap, the certified ledger
at any presentation gives `σ(G) ≤ C_sp ⌈√n⌉` by the generic quadratic
absorption, with `C_sp` derived from the routing alphabet, the baseline degree
and the deficit scale exactly as the presentation registers it. -/
theorem surplus_le_scale_of_capped {object : FiniteObject.{u}}
    {threshold order deficitScale : Nat}
    (data : CapacityPresentation object threshold order)
    (certified : CertifiedObjectCapacityLedger object threshold order deficitScale data)
    (routingLabelBound : Nat)
    (capped : SparsePressureCappedAt certified routingLabelBound)
    (sizePos : 0 < object.vertexCount)
    (safety : TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * homogeneousTokenCap routingLabelBound) +
        (2 * deficitScale + 2 * homogeneousTokenCap routingLabelBound *
          (3 * (threshold - 1) + 2))) :
    object.degreeSurplus threshold ≤
      (2 * (1 + 2 * homogeneousTokenCap routingLabelBound) +
        (2 * deficitScale + 2 * homogeneousTokenCap routingLabelBound *
          (3 * (threshold - 1) + 2))) * Core.ceilSqrt object.vertexCount := by
  exact certified.degreeSurplus_le_mul_ceilSqrt sizePos
    (homogeneousTokenCap routingLabelBound) safety capped

/-- **`[138]` at the full pair schedule** (`prop:sparse-entropy-sandwich`,
`cor:spine-lower-bound-surplus-estimates`): if the free-pair code
`2^{|ℐ_spine| + C(σ,2)}` is realized within the skeleton budget, then
`σ(G) ≤ C_sp ⌈√n⌉`. -/
theorem surplus_le_scale_of_pairSandwich (object : FiniteObject.{u})
    {threshold deficitScale : Nat} (cap : Nat)
    (baseline : 2 ≤ threshold)
    (above : cubicBaselineEdgeCount object.vertexCount threshold ≤ object.edgeCount)
    (spineCount deficit : Nat)
    (demand : cubicBaselineBudget object.vertexCount threshold ≤
      2 ^ (spineCount + deficit))
    (deficit_le : deficit ≤ deficitScale * object.vertexCount)
    (slack_le : object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold ≤
      object.degreeSurplus threshold)
    (entropy : 2 ^ (spineCount + (object.degreeSurplus threshold).choose 2) ≤
      skeletonBudget object)
    (sizePos : 0 < object.vertexCount)
    (safety : TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * cap) + (2 * deficitScale + 2 * cap * (3 * (threshold - 1) + 2))) :
    object.degreeSurplus threshold ≤
      (2 * (1 + 2 * cap) + (2 * deficitScale + 2 * cap * (3 * (threshold - 1) + 2))) *
        Core.ceilSqrt object.vertexCount := by
  set slack := object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold
  have package := freeCount_le_of_sandwich object baseline above entropy demand
  have root := TokenLoad.demand_le_of_package (object.degreeSurplus threshold)
    (deficit + slack * (Nat.log2 object.vertexCount + 1)) package
  apply TokenLoad.demand_le_mul_ceilSqrt object.vertexCount (object.degreeSurplus threshold)
    deficit slack cap deficitScale (3 * (threshold - 1) + 2) _ sizePos deficit_le slack_le
    _ le_rfl safety
  calc object.degreeSurplus threshold
      ≤ 1 + Nat.sqrt (2 * (deficit + slack * (Nat.log2 object.vertexCount + 1))) := root
    _ ≤ 1 + 2 * cap +
        Nat.sqrt (2 * (deficit + (Nat.log2 object.vertexCount + 1) * slack) +
          2 * (cap * ((3 * (threshold - 1) + 2) * object.vertexCount))) := by
        have inner : 2 * (deficit + slack * (Nat.log2 object.vertexCount + 1)) ≤
            2 * (deficit + (Nat.log2 object.vertexCount + 1) * slack) +
              2 * (cap * ((3 * (threshold - 1) + 2) * object.vertexCount)) := by
          rw [Nat.mul_comm slack]
          omega
        have := Nat.sqrt_le_sqrt inner
        omega

end Hypostructure.Graph
