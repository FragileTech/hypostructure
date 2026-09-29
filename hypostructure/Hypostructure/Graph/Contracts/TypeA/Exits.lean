import Hypostructure.Graph.Contracts.TypeA.Support

/-!
# Contracts: the saturated Type A exits

Proof-agnostic contract lemmas for `def:typeA-saturated-exits` at the objects of
the object fixed upstream: the overloaded port of the visible receiver of
`X₀` (exits `(1)`--`(3)`), the exit-chain receiver and its canonical witnessed
peeling sequence (exit `(4)`, `lem:typeA-exit4-discharge`,
`lem:typeA-saturated-handoff`, `lem:typeA-exit4-peeling-charge`), the terminal
state `P₄(w)` (exits `(5)`--`(8)`), and the canonical exit-`(6)`
delocalization (`lem:proper-smearing`, `lem:no-silent-global-smearing`).
The closures are `lem:typeA-exits-discharged`.
-/

namespace Hypostructure.Graph.Contracts.TypeA

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-! ## Exits `(1)`--`(3)`, nodes `[95]`--`[100]` -/

/-- Node `[96]`: a Mersenne anchored return through the overloaded port closes
a target cycle (`lem:return-equivalence`), which the return-avoidance
invariant excludes. -/
theorem typeAExitOneReturn_contradiction
    (avoidance : ReturnAvoidanceStatement data object)
    (exit : TypeAExitOneReturnStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, chosen, _port, portPinned, return',
    accepted⟩ := exit
  exact Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint
    data.LengthOK avoidance
    (Graph.VisibleEntry.mem_completionPorts.mp
      (visiblePort_mem_completionPorts data object chosen portPinned)).1
    return' accepted

/-- Node `[98]`: two internally disjoint receiver-entry returns through the
overloaded port with accepted total length glue into a target cycle
(`lem:typeA-common-port-return-cycle`). -/
theorem typeAExitTwoTheta_contradiction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (exit : TypeAExitTwoThetaStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, chosen, _port, portPinned, pair⟩ := exit
  exact avoids
    (Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough
      (visiblePort_mem_completionPorts data object chosen portPinned) pair)

/-- Node `[100]`: a failed legal-label relation at a common packed window of
two returns through the overloaded port builds a cycle of accepted length
(`lem:labels`); the degenerate closure of length `2` is not accepted. -/
theorem typeAExitThreeCycle
    (degenerate : ¬ data.LengthOK 2)
    (exit : TypeAExitThreeCollisionStatement data object) :
    TypeAExitThreeCycleStatement data object := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, _port, _portPinned, collision⟩ :=
    exit
  exact Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision degenerate
    (labelCollision_of_exitThreeThrough collision)

/-- Node `[100]` closes: the accepted cycle contradicts the selection's target
avoidance. -/
theorem typeAExitThreeCycle_contradiction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cycle : TypeAExitThreeCycleStatement data object) : False :=
  avoids cycle

/-- The overloaded port of a state is a completion port of its receiver: it is
the head of the canonical overloaded-port order. -/
theorem canonicalOverloadedPortAt_mem_completionPorts
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    {peeled : Finset object.Vertex} {port : object.Vertex}
    (pinned : canonicalOverloadedPortAt data object piece receiver peeled =
      some port) :
    port ∈ Graph.VisibleEntry.completionPorts object piece receiver := by
  classical
  have member : port ∈ Graph.ExitFour.overloadedPortOrder piece data.threshold
      data.dischargeScale receiver peeled :=
    List.mem_of_mem_head? pinned
  have data' :
      port ∈ Graph.VisibleEntry.completionPorts object piece receiver ∧
        data.dischargeScale ≤ (Graph.ExitFour.unpeeledVisibleLoadsAt piece
          data.threshold receiver port peeled).card := by
    simpa [Graph.ExitFour.overloadedPortOrder, object.mem_orderedVertices port]
      using member
  exact data'.1

/-! ## Exits `(1)`--`(3)` after peeling (node `[102]` → `[89]` → `[93]`) -/

/-- Node `[96]` after peeling: a Mersenne anchored return through the
overloaded port of the terminal state closes a target cycle. -/
theorem typeAPeeledExitOneReturn_contradiction
    (avoidance : ReturnAvoidanceStatement data object)
    (exit : TypeAPeeledExitOneReturnStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, _port, portPinned, return',
    accepted⟩ := exit
  exact Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint
    data.LengthOK avoidance
    (Graph.VisibleEntry.mem_completionPorts.mp
      (canonicalOverloadedPortAt_mem_completionPorts data object portPinned)).1
    return' accepted

/-- Node `[98]` after peeling: exit `(2)` at the overloaded port of the terminal
state closes a target cycle. -/
theorem typeAPeeledExitTwoTheta_contradiction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (exit : TypeAPeeledExitTwoThetaStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, _port, portPinned, pair⟩ := exit
  exact avoids
    (Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough
      (canonicalOverloadedPortAt_mem_completionPorts data object portPinned) pair)

/-- Node `[100]` after peeling: exit `(3)` at the overloaded port of the
terminal state builds a cycle of accepted length. -/
theorem typeAPeeledExitThreeCycle
    (degenerate : ¬ data.LengthOK 2)
    (exit : TypeAPeeledExitThreeCollisionStatement data object) :
    TypeAExitThreeCycleStatement data object := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, _port, _portPinned, collision⟩ :=
    exit
  exact Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision degenerate
    (labelCollision_of_exitThreeThrough collision)

/-! ## The exit-chain receiver -/

/-- The exit-chain receiver of `X₀` sits at the degree baseline. -/
theorem exitReceiver_degree
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    (zero : object.ambientSurplus piece data.threshold = 0)
    (chosen : canonicalExitReceiverAt data object piece = some receiver) :
    object.degree receiver = data.threshold :=
  degree_eq_threshold_of_ambientSurplus_eq_zero object baseline zero receiver
    (canonicalExitReceiverAt_spec_of_eq_some chosen).1.1

/-! ## `lem:typeA-exit4-finite-descent` at `G` -/

/-- The canonical witnessed peeling sequence of the exit-chain receiver stops
at its terminal set, a witnessed fixed point inside the routed loads. -/
theorem typeAExitFourFiniteDescent
    (entry : TypeASaturatedExitEntryStatement data object) :
    TypeAExitFourFiniteDescentFact data object := by
  obtain ⟨piece, pinned, receiver, chosen, _⟩ := entry
  exact ⟨piece, pinned, receiver, chosen,
    canonicalTerminalPeeled_step data object piece receiver,
    canonicalPeel_subset_routedLoads data object piece receiver _,
    canonicalPeel_peeledByWitnesses data object piece receiver _⟩

/-! ## Exit `(4)`, node `[101]` -/

/-- At a saturated receiver of internal-degree baseline the two lanes of
`lem:typeA-exit4-residual-routing` are exhaustive, so the absence of the lane's
exit-`(4)` witness is exactly `ExitFourFreeAt`; on the visible lane the absence
also gives the retained target-completeness of every selected response pair
(`lem:typeA-unpeeled-visible-routing`). -/
theorem exitFourFreeAt_of_not_exitFourAt
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (exact : object.degree receiver = data.threshold)
    (isReceiver : object.IsReceiver piece data.threshold receiver)
    (saturated : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver peeled)
    (absent : ¬ ExitFourAt data object piece receiver peeled) :
    ExitFourFreeAt data object piece receiver peeled := by
  classical
  rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess piece
      data.threshold data.dischargeScale receiver peeled exact isReceiver
      saturated with visible | silent
  · obtain ⟨package⟩ := Graph.ExitFour.visibleFourUnpeeledPackage piece
      data.threshold data.dischargeScale receiver peeled visible
    have none : ¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
        ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
            data.threshold data.dischargeScale receiver package.outside peeled,
          witness.load = load :=
      fun occurs => absent (Or.inl ⟨package, occurs⟩)
    refine Or.inl ⟨package, none, ?_⟩
    rcases package.exists_witness_or_pairwise_targetComplete
        (Target := Graph.HasCycleWithLength data.LengthOK) with
      ⟨witness, selected⟩ | complete
    · exact False.elim (none ⟨witness, witness.load, selected, rfl⟩)
    · exact complete
  · exact Or.inr ⟨silent, fun occurs => absent (Or.inr ⟨silent, occurs⟩)⟩

/-- The terminal receiver of `X₀` sits at the degree baseline. -/
theorem terminalReceiver_degree
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    (zero : object.ambientSurplus piece data.threshold = 0)
    (chosen : canonicalTerminalReceiverAt data object piece = some receiver) :
    object.degree receiver = data.threshold :=
  degree_eq_threshold_of_ambientSurplus_eq_zero object baseline zero receiver
    (canonicalTerminalReceiverAt_spec_of_eq_some chosen).1.1

/-- At its terminal set a saturated terminal receiver is exit-`(4)`-free
(`lem:typeA-saturated-handoff`: the peeling stops only when no witness
remains). -/
theorem exitFourFreeAt_terminal
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    (zero : object.ambientSurplus piece data.threshold = 0)
    (chosen : canonicalTerminalReceiverAt data object piece = some receiver) :
    ExitFourFreeAt data object piece receiver
      (canonicalTerminalPeeled data object piece receiver) := by
  have spec := canonicalTerminalReceiverAt_spec_of_eq_some chosen
  have none := canonicalTerminalPeeled_witness_eq_none data object piece receiver
    spec.2
  refine exitFourFreeAt_of_not_exitFourAt data object
    (terminalReceiver_degree data object baseline zero chosen) spec.1 spec.2 ?_
  intro occurs
  exact canonicalExitFourWitnessAt_eq_none_iff.mp none
    ((exitFourAt_iff_exists_witnessSpec data object piece receiver _).mp occurs)

/-- Node `[101]`, no arm, at the terminal state: whatever lane reached it, the
terminal receiver is saturated at its terminal set and exit `(4)` is absent
there. -/
theorem typeASaturatedHandoffExitFourFree_of_terminal
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (low : TypeALowSurplusStatement data object)
    {fact : Finset object.Vertex → object.Vertex → Finset object.Vertex → Prop}
    (state : AtTerminalState data object fact) :
    TypeASaturatedHandoffExitFourFreeStatement data object := by
  obtain ⟨piece, pinned, zero, receiver, chosen, _⟩ := canonicalPin_merge low state
  exact ⟨piece, pinned, receiver, chosen,
    (canonicalTerminalReceiverAt_spec_of_eq_some chosen).2,
    exitFourFreeAt_terminal data object baseline zero chosen⟩

/-- Node `[101]` after peeling, on the visible lane (after node `[99]`). -/
theorem typeASaturatedHandoffExitFourFree_of_peeledExitThreeFree
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (low : TypeALowSurplusStatement data object)
    (three : TypeAPeeledExitThreeFreeStatement data object) :
    TypeASaturatedHandoffExitFourFreeStatement data object :=
  typeASaturatedHandoffExitFourFree_of_terminal data object baseline low
    (fact := fun piece receiver peeled =>
      ∃ port, canonicalOverloadedPortAt data object piece receiver peeled =
          some port ∧ ¬ ExitThreeThrough data object piece receiver port) three

/-- Node `[101]` after peeling, on the silent lane (after node `[94]`). -/
theorem typeASaturatedHandoffExitFourFree_of_peeledSilentExcess
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (low : TypeALowSurplusStatement data object)
    (silent : TypeAPeeledSilentExcessStatement data object) :
    TypeASaturatedHandoffExitFourFreeStatement data object :=
  typeASaturatedHandoffExitFourFree_of_terminal data object baseline low
    (fact := fun piece receiver peeled =>
      Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
        data.dischargeScale receiver peeled) silent

/-- Node `[101]`, no arm: with no exit `(4)` at the entry state the canonical
sequence never moves, so the entry receiver is saturated at its terminal set
`P₄(w) = ∅`; it is the terminal receiver, and exits `(5)`--`(8)` are asked
there. -/
theorem typeASaturatedHandoffExitFourFree_of_absent
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (low : TypeALowSurplusStatement data object)
    (entry : TypeASaturatedExitEntryStatement data object)
    (absent : TypeAExitFourAbsentStatement data object) :
    TypeASaturatedHandoffExitFourFreeStatement data object := by
  obtain ⟨piece, pinned, stateEntry, stateAbsent⟩ := canonicalPin_merge entry absent
  obtain ⟨receiver, chosen, saturated, noExit⟩ :=
    canonicalPin_merge stateEntry stateAbsent
  have none : canonicalExitFourWitnessAt data object piece receiver ∅ = Option.none :=
    canonicalExitFourWitnessAt_eq_none_iff.mpr fun found =>
      noExit ((exitFourAt_iff_exists_witnessSpec data object piece receiver ∅).mpr
        found)
  have terminal := canonicalTerminalPeeled_eq_empty_of_none data object piece
    receiver none
  have terminalSaturated : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver
      (canonicalTerminalPeeled data object piece receiver) := by
    rw [terminal]
    exact saturated
  exact typeASaturatedHandoffExitFourFree_of_terminal data object baseline low
    (fact := fun _ _ _ => True)
    ⟨piece, pinned, receiver,
      canonicalTerminalReceiverAt_eq_of_exit chosen terminalSaturated, trivial⟩

/-! ## Node `[102]`: the exit-`(4)` peel -/

/-- `lem:typeA-exit4-discharge` at the canonical witness of the entry state:
its routed load is adjoined, the result is the first step of the canonical
sequence, it stays inside the routed loads, and the residual load drops by
exactly one. -/
theorem typeAExitFourPeeled
    (entry : TypeASaturatedExitEntryStatement data object)
    (exit : TypeASaturatedHandoffExitFourStatement data object) :
    TypeAExitFourPeeledStatement data object := by
  obtain ⟨piece, pinned, stateEntry, stateExit⟩ := canonicalPin_merge entry exit
  obtain ⟨receiver, chosen, saturated, occurs⟩ :=
    canonicalPin_merge stateEntry stateExit
  obtain ⟨witness, found, _⟩ := canonicalExitFourWitnessAt_spec
    ((exitFourAt_iff_exists_witnessSpec data object piece receiver ∅).mp occurs)
  exact ⟨piece, pinned, receiver, chosen, witness, found,
    canonicalPeel_one_of_some data object piece receiver saturated found,
    Graph.ExitFour.Witness.nextPeeled_subset_routedLoads witness
      (Finset.empty_subset _),
    Graph.ExitFour.Witness.residualLoad_nextPeeled witness⟩

/-! ## Node `[102]` → `[89]`: the recompute-`L₄` retest -/

/-- `lem:typeA-exit4-peeling-charge` at every receiver: when no receiver of the
piece is saturated at its terminal set, each has nonnegative remaining charge,
`L₄(w) ≤ s·q(w) − 1`. -/
theorem receiverDischarged_of_not_terminalSaturated
    {piece : Finset object.Vertex}
    (unsaturated : ¬ ∃ receiver, TerminalSaturatedSpec data object piece receiver) :
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      1 + Graph.ExitFour.residualLoad piece data.threshold receiver
          (canonicalTerminalPeeled data object piece receiver) ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver :=
  fun receiver isReceiver =>
    (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
      data.dischargeScale receiver _).mp
      fun saturated => unsaturated ⟨receiver, isReceiver, saturated⟩

/-- `lem:typeA-unsaturated-discharge` on the unpeeled loads
(`lem:typeA-exit4-peeling-charge`): a zero-surplus support with total routing
whose receivers satisfy `1 + L₄(w) ≤ s·q(w)` has
`|V(X)| ≤ s·def⁺(X) + Σ_w |P₄(w)|`. -/
theorem card_le_scaled_deficiency_add_peeled
    (support : Finset object.Vertex) (threshold scale : Nat)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold)
    (routes : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver)
    (peeled : object.Vertex → Finset object.Vertex)
    (unsaturated : ∀ receiver : object.Vertex,
      object.IsReceiver support threshold receiver →
      1 + Graph.ExitFour.residualLoad support threshold receiver
          (peeled receiver) ≤
        scale * object.missingPorts support threshold receiver) :
    support.card ≤ scale * object.positiveDeficiency support threshold +
      ∑ receiver ∈ object.receivers support threshold, (peeled receiver).card := by
  classical
  have deficiency : scale * object.positiveDeficiency support threshold =
      ∑ receiver ∈ object.receivers support threshold,
        scale * object.missingPorts support threshold receiver := by
    unfold Graph.FiniteObject.positiveDeficiency
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not support
      (fun vertex => object.internalDegree support vertex = threshold)
      (fun vertex => scale * (threshold - object.internalDegree support vertex))]
    have vanishes : ∑ vertex ∈ support.filter
        (fun vertex => object.internalDegree support vertex = threshold),
        scale * (threshold - object.internalDegree support vertex) = 0 := by
      refine Finset.sum_eq_zero fun vertex member => ?_
      rw [(Finset.mem_filter.mp member).2]
      simp
    rw [vanishes, Nat.zero_add,
      ← Graph.FiniteObject.receivers_eq_filter_not object support threshold capped]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have perReceiver : ∀ receiver ∈ object.receivers support threshold,
      1 + object.routedLoad support threshold receiver ≤
        scale * object.missingPorts support threshold receiver +
          (peeled receiver).card := by
    intro receiver member
    have bound := unsaturated receiver (Graph.FiniteObject.mem_receivers.mp member)
    have split : object.routedLoad support threshold receiver ≤
        Graph.ExitFour.residualLoad support threshold receiver (peeled receiver) +
          (peeled receiver).card := by
      unfold Graph.FiniteObject.routedLoad Graph.ExitFour.residualLoad
        Graph.ExitFour.unpeeledLoads
      convert (@Finset.card_le_card_sdiff_add_card _
        (object.routedLoads support threshold receiver) (peeled receiver)
        (Graph.vertexDecEq object))
    omega
  have paid : ∑ receiver ∈ object.receivers support threshold,
      (1 + object.routedLoad support threshold receiver) ≤
        ∑ receiver ∈ object.receivers support threshold,
          (scale * object.missingPorts support threshold receiver +
            (peeled receiver).card) :=
    Finset.sum_le_sum perReceiver
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul, mul_one,
    Graph.FiniteObject.sum_routedLoad object support threshold routes] at paid
  have split := Graph.FiniteObject.card_receivers_add_card_fullVertices object
    support threshold capped
  rw [deficiency]
  omega

/-- Node `[91]` after peeling at `X₀`. -/
theorem typeAPeeledUnsaturatedDischarge
    (routing : TypeAReceiverRoutingStatement data object)
    (low : TypeALowSurplusStatement data object)
    (discharged : TypeAExitFourReceiverDischargedStatement data object) :
    TypeAPeeledUnsaturatedDischargeStatement data object := by
  obtain ⟨piece, pinned, surplus, bound⟩ := canonicalPin_merge low discharged
  exact ⟨piece, pinned,
    card_le_scaled_deficiency_add_peeled object piece data.threshold
      data.dischargeScale
      (Graph.DecoratedAbsorption.capped_of_ambientSurplus_zero object piece
        data.threshold surplus)
      (typeAReceiverRouting_at data object routing pinned)
      (canonicalTerminalPeeled data object piece) bound⟩

/-- Node `[94]` after peeling (`lem:typeA-unpeeled-silent-routing`): at a
saturated terminal state with no overloaded port the residual excess is
nonempty and silent. -/
theorem typeAPeeledSilentExcess
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (low : TypeALowSurplusStatement data object)
    (noVisible : TypeAPeeledNoVisibleEntryStatement data object) :
    TypeAPeeledSilentExcessStatement data object := by
  obtain ⟨piece, pinned, zero, receiver, chosen, none⟩ :=
    canonicalPin_merge low noVisible
  have spec := canonicalTerminalReceiverAt_spec_of_eq_some chosen
  refine ⟨piece, pinned, receiver, chosen, ?_⟩
  rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess piece
      data.threshold data.dischargeScale receiver _
      (terminalReceiver_degree data object baseline zero chosen) spec.1
      spec.2 with visible | silent
  · exact (none (Graph.ExitFour.visibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver _ visible)).elim
  · exact silent

/-! ## Exit `(5)`, node `[104]` -/

/-- Node `[104]`, stated about G: the exit-`(5)` compression of a selected
trace basin at the terminal state is a piece `X'` (G's retained reading of
`B_u`) with the basin's boundary-degree profile, the degree baseline once glued
into `G − B_u`, no target cycle in `glue X' (G − B_u)`, and strictly smaller —
the G-form hypotheses of `lem:replacement` (`CompressibleSupport`), which
`cor:uncompressible` (node `[14]`) excludes. -/
theorem typeAExitFive_contradiction
    (uncompressible : UncompressibleStatement data object)
    (exit : TypeAExitFiveStatement data object) : False := by
  obtain ⟨piece, _pinned, _receiver, _chosen, _state, _load, _eligible, basin,
    _selected, compression⟩ := exit
  obtain ⟨retained, _retainedSubset, _changed, profile, targetFree, connected,
    proper, baseline, smaller⟩ := compression
  exact uncompressible basin ⟨connected, proper,
    Graph.Route8.PresentedEntry.retainedReading object piece basin
      data.threshold data.LengthOK
      (Graph.Route8.PresentedEntry.retainedBaseCoordinates object piece
        retained), profile, baseline, smaller, targetFree⟩

/-! ## Exit `(6)`, node `[106]` -/

/-- `lem:proper-smearing`: the canonical delocalization's proper enlarging
support is a replacement support. -/
theorem typeAExitSixProper_of_scope
    (proper : TypeAExitSixProperScopeStatement data object) :
    TypeAExitSixProperStatement data object := by
  obtain ⟨piece, pinned, receiver, chosen, delocalization, found, outside⟩ := proper
  exact ⟨piece, pinned, receiver, chosen, delocalization, found,
    delocalization.2.properReplacement outside⟩

/-- `lem:no-silent-global-smearing`: the canonical delocalization adjoins all
of `G` and supplies a strictly smaller closed representative. -/
theorem typeAExitSixGlobal_of_scope
    (global : TypeAExitSixGlobalScopeStatement data object) :
    TypeAExitSixGlobalStatement data object := by
  obtain ⟨piece, pinned, receiver, chosen, delocalization, found, covers⟩ :=
    global
  exact ⟨piece, pinned, receiver, chosen, delocalization, found, covers,
    Classical.choose_spec (delocalization.2.closedRepresentative covers)⟩

/-- Node `[106]`, proper scope: the replacement contradicts `lem:replacement`. -/
theorem typeAExitSixProper_contradiction
    (exclusion : ReplacementExclusionStatement data object)
    (exit : TypeAExitSixProperStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, delocalization, _found,
    replacement⟩ := exit
  exact exclusion _ replacement

/-- Node `[106]`, whole-graph scope: the strictly smaller closed representative
contradicts the minimality of the selected counterexample. -/
theorem typeAExitSixGlobal_contradiction
    (_avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (exit : TypeAExitSixGlobalStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, _delocalization, _found,
    _covers, smaller, representativeBaseline, targetFree⟩ := exit
  exact targetFree (minimal _ smaller representativeBaseline)

/-! ## Node `[108]`: the decorated handoff envelope of exit `(7)` -/

/-- **Node `[108]`** (`lem:typeA-high-degree-handoff`, tex 11110): the
exit-`(7)` separation of the terminal state is the canonical separation of
`X₀`, and its decorated handoff fan envelope exists: the separator has degree at
least `4` (`lem:typeA-cubic-switch-absorption`), above the registered baseline,
and the exit-`(3)` absorbing clause (a label collision of `P₀`) is refuted by
target avoidance. -/
theorem typeAExitSevenEnvelope
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (cubic : data.threshold = 3) (degenerate : ¬ data.LengthOK 2)
    (handoff : TypeAExitSevenHandoffStatement data object) :
    TypeAExitSevenEnvelopeStatement data object := by
  obtain ⟨piece, pinned, receiver, chosen, zero, _noSix, load, eligible,
    separated⟩ := handoff
  have stateSpec : ExitSevenStateSpec data object piece (receiver, load) :=
    ⟨chosen, eligible, separated⟩
  obtain ⟨separation, separationEq, spec⟩ :=
    canonicalHandoffSeparationAt_state ⟨_, stateSpec⟩
  have sameReceiver : separation.1.1 = receiver :=
    Option.some.inj (spec.1.symm.trans chosen)
  have eligibleAt : EligibleLoadAt data object piece receiver
      (canonicalTerminalPeeled data object piece receiver) separation.1.2 := by
    have := spec.2.1
    rw [sameReceiver] at this
    exact this
  have envelope := canonicalHandoffEnvelopeAt_isSome (HighDegree :=
      handoffHighDegree data object)
    (Absorbing := handoffAbsorbing data object (canonicalWindowPacking data object))
    avoids
    (fun separated _ => by
      have four := Graph.DecoratedHandoff.four_le_degree_of_surviving
        separated.2.surviving
      show data.threshold < object.degree separated.2.separation.separator
      omega)
    (fun _centre _first _second collision =>
      avoids (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        degenerate collision))
    ⟨_, separatorHandoffSpec_of_exitSevenStateSpec stateSpec⟩
  obtain ⟨built, builtEq⟩ := Option.isSome_iff_exists.mp envelope
  exact ⟨piece, pinned, receiver, chosen, zero,
    ⟨separation, separationEq, sameReceiver, eligibleAt⟩, built, builtEq⟩

/-! ## The switch at the separator, stated about G -/

/-- **Node `[102]` at G** (Lean improvement): the canonical exit-(4) witness is
a Q4 member (Q1–Q3 and Q5 are empty at a target-avoiding G), and its switch is
the target-cycle arm: a proper double-edge switch whose switched graph carries
an accepted cycle through an exchanged edge. -/
theorem typeAExitFourSwitchCycle
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (exitFour : TypeASaturatedHandoffExitFourStatement data object) :
    TypeAExitFourSwitchCycleStatement data object := by
  obtain ⟨piece, pinned, receiver, chosen, occurs⟩ := exitFour
  obtain ⟨witness, found, _spec⟩ := canonicalExitFourWitnessAt_spec
    ((exitFourAt_iff_exists_witnessSpec data object piece receiver ∅).mp occurs)
  obtain ⟨datum, memberEq⟩ :=
    Graph.ExitFour.CanonicalMember.exists_q4_of_avoids avoids witness.member
  exact ⟨piece, pinned, receiver, chosen, witness, found, datum, memberEq,
    Graph.ExitFour.Q4TargetDefect.forced_cycle avoids datum⟩

/-- **Node `[108]` at G**: the canonical handoff separation survives, so its
switch at `z` (constructed from G) has no accepted cycle and its separator has
an unused ambient incidence; the switch keeps every degree and the edge count,
so the switched graph is a counterexample of G's size. -/
theorem typeAExitSevenSwitch
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (envelope : TypeAExitSevenEnvelopeStatement data object) :
    TypeAExitSevenSwitchStatement data object := by
  obtain ⟨piece, pinned, _receiver, _chosen, _zero,
    ⟨separated, separatedEq, _sameReceiver, _eligible⟩, _built⟩ := envelope
  obtain ⟨targetFree, onBoundary, _notEnlarging⟩ :=
    Graph.DecoratedHandoff.Surviving.of_avoids avoids separated.2.surviving
  obtain ⟨switchedBaseline, vertices, edges, _free, notSmaller⟩ :=
    separated.2.separation.switched_sameSize baseline targetFree
  exact ⟨piece, pinned, separated, separatedEq, targetFree, onBoundary,
    switchedBaseline, vertices, edges, notSmaller⟩

end Hypostructure.Graph.Contracts.TypeA
