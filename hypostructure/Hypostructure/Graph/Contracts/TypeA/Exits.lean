import Hypostructure.Graph.Contracts.TypeA.Support

/-!
# Contracts: the saturated Type A exits

Proof-agnostic contract lemmas for `def:typeA-saturated-exits`: the exact
complement of every exit test, the closures of the closed exits
(`lem:typeA-exits-discharged`), the exit-`(4)` peel
(`lem:typeA-exit4-discharge`), the finite descent to an unsaturated receiver
(`lem:typeA-saturated-handoff`, `lem:typeA-exit4-peeling-charge`), the two
scopes of exit `(6)` (`lem:proper-smearing`, `lem:no-silent-global-smearing`),
and the route-`8` residual state of exit `(8)`.
-/

namespace Hypostructure.Graph.Contracts.TypeA

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-! ## Exit `(1)`, node `[95]` -/

theorem typeAExitOneFree_of_not_return
    (exit : ¬ TypeAExitOneReturnStatement data object) :
    TypeAExitOneFreeStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver saturated package return' accepted
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, saturated, package, return', accepted⟩

/-- Node `[96]`: a Mersenne anchored return through a completion port closes a
target cycle (`lem:return-equivalence`), which the return-avoidance invariant
excludes. -/
theorem typeAExitOneReturn_contradiction
    (avoidance : ReturnAvoidanceStatement data object)
    (exit : TypeAExitOneReturnStatement data object) : False := by
  obtain ⟨_packing, _canonical, _valid, _maximal, _component, _present, _charge,
    _surplus, _receiver, _isReceiver, _saturated, package, return', accepted⟩ :=
    exit
  exact Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint
    data.LengthOK avoidance
    (Graph.VisibleEntry.mem_completionPorts.mp package.port).1 return' accepted

/-! ## Exit `(2)`, node `[97]` -/

theorem typeAExitTwoFree_of_not_theta
    (exit : ¬ TypeAExitTwoThetaStatement data object) :
    TypeAExitTwoFreeStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver saturated package theta
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, saturated, package, theta⟩

/-- Node `[98]`: two internally disjoint receiver-entry returns through one
port with accepted total length glue into a target cycle
(`lem:typeA-common-port-return-cycle`). -/
theorem typeAExitTwoTheta_contradiction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (exit : TypeAExitTwoThetaStatement data object) : False := by
  obtain ⟨_packing, _canonical, _valid, _maximal, _component, _present, _charge,
    _surplus, _receiver, _isReceiver, _saturated, package, pair⟩ := exit
  exact avoids
    (Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough package.port pair)

/-! ## Exit `(3)`, node `[99]` -/

theorem typeAExitThreeFree_of_not_collision
    (exit : ¬ TypeAExitThreeCollisionStatement data object) :
    TypeAExitThreeFreeStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver saturated package collision
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, saturated, package, collision⟩

/-- Node `[100]`: a failed legal-label relation at a shared window builds a
cycle of accepted length (`lem:labels`); the degenerate closure of length `2`
is not accepted. -/
theorem typeAExitThreeCollision_contradiction
    (degenerate : ¬ data.LengthOK 2)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (exit : TypeAExitThreeCollisionStatement data object) : False := by
  obtain ⟨_packing, _canonical, _valid, _maximal, _component, _present, _charge,
    _surplus, _receiver, _isReceiver, _saturated, _package, collision⟩ := exit
  exact avoids
    (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision degenerate
      collision)

/-! ## `lem:typeA-exit4-finite-descent` at the entry state -/

/-- The finite exit-`(4)` descent from the entry state of the exit segment:
for any retained family of peeling sets closed under one peeling step,
repeated peeling from the entry state reaches a terminal retained state or an
unsaturated retained state, because every step lowers the residual load. -/
theorem typeAExitFourFiniteDescent
    (entry : TypeASaturatedExitEntryStatement data object) :
    TypeAExitFourFiniteDescentFact data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, startPeeled, startInside, startSaturated,
    _startWitnessed⟩ := entry
  refine ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, startPeeled, startInside, startSaturated, ?_⟩
  intro Retained Terminal startRetained step
  exact Graph.ExitFour.terminal_or_unsaturated_from _ data.threshold
    data.dischargeScale receiver startInside startRetained step

/-! ## Exit `(4)`, node `[101]`

At a saturated receiver of internal-degree baseline the two lanes of
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

theorem exitFourAt_of_not_exitFourFreeAt
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (exact : object.degree receiver = data.threshold)
    (isReceiver : object.IsReceiver piece data.threshold receiver)
    (saturated : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver peeled)
    (notFree : ¬ ExitFourFreeAt data object piece receiver peeled) :
    ExitFourAt data object piece receiver peeled := by
  by_contra absent
  exact notFree
    (exitFourFreeAt_of_not_exitFourAt data object exact isReceiver saturated
      absent)

/-- An exit-`(4)` witness of either lane supplies the next routed load to
peel. -/
theorem ExitFourAt.exists_witness
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (exit : ExitFourAt data object piece receiver peeled) :
    Nonempty (Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
      piece data.threshold data.dischargeScale receiver peeled) := by
  rcases exit with ⟨_package, witness, _load, _selected, _equal⟩ |
    ⟨_silent, witness, _supported⟩
  · exact ⟨witness⟩
  · exact ⟨witness⟩

theorem typeAExitFourAbsent_of_not_exitFour
    (exit : ¬ TypeASaturatedHandoffExitFourStatement data object) :
    TypeAExitFourAbsentStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated witnessed occurs
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, witnessed, occurs⟩

/-- Node `[101]`, no arm: the entry state of the exit segment has no exit
`(4)`, so it is the saturated exit-`(4)`-free state on which exits
`(5)`--`(8)` are asked. -/
theorem typeASaturatedHandoffExitFourFree_of_absent
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (entry : TypeASaturatedExitEntryStatement data object)
    (absent : TypeAExitFourAbsentStatement data object) :
    TypeASaturatedHandoffExitFourFreeStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, witnessed⟩ := entry
  have exact := degree_eq_threshold_of_ambientSurplus_eq_zero object baseline
    zero receiver isReceiver.1
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, inside, saturated,
    exitFourFreeAt_of_not_exitFourAt data object exact isReceiver saturated
      (absent packing canonical valid maximal component present negative zero
        receiver isReceiver peeled inside saturated witnessed)⟩

/-! ## Node `[102]`: the exit-`(4)` peel -/

/-- `lem:typeA-exit4-discharge`: the witness's routed load is adjoined to the
peeling set, which stays inside the routed loads, and the residual load drops by
exactly one. -/
theorem typeAExitFourPeeled
    (exit : TypeASaturatedHandoffExitFourStatement data object) :
    TypeAExitFourPeeledStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, witnessed,
    occurs⟩ := exit
  obtain ⟨witness⟩ := ExitFourAt.exists_witness data object occurs
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, inside, saturated, witnessed, witness,
    witness.unpeeled,
    Graph.ExitFour.Witness.nextPeeled_subset_routedLoads witness inside,
    Graph.ExitFour.Witness.residualLoad_nextPeeled witness⟩

/-! ## Node `[102]` → `[89]`: the recompute-`L₄` retest -/

theorem typeAExitFourExhausted_of_not_free
    (free : ¬ TypeASaturatedHandoffExitFourFreeStatement data object) :
    TypeAExitFourExhaustedStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated exitFree
  exact free ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, exitFree⟩

/-- `lem:typeA-saturated-handoff` and `lem:typeA-exit4-peeling-charge`: when
every saturated peeling state still realizes exit `(4)`, repeated peeling from
the peeled state of node `[102]` reaches a witnessed peeling set at which the
receiver is unsaturated, and its remaining receiver charge is nonnegative. -/
theorem typeAExitFourReceiverDischarged
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (peeled : TypeAExitFourPeeledStatement data object)
    (exhausted : TypeAExitFourExhaustedStatement data object) :
    TypeAExitFourReceiverDischargedStatement data object := by
  classical
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, start, _startInside, _startSaturated,
    startWitnessed, witness, _unpeeled, nextInside, _drop⟩ := peeled
  let piece := object.pieceSupport (object.remainderSupport packing) component
  have exact := degree_eq_threshold_of_ambientSurplus_eq_zero object baseline
    zero receiver isReceiver.1
  have descent := Graph.ExitFour.terminal_or_unsaturated_from piece
    data.threshold data.dischargeScale receiver
    (Retained := Graph.ExitFour.PeeledByWitnesses
      (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
      data.dischargeScale receiver)
    (Terminal := fun _ => False)
    nextInside
    (Graph.ExitFour.peeledByWitnesses_nextPeeled startWitnessed witness)
    (by
      intro state stateInside stateWitnessed stateSaturated
      have occurs := exitFourAt_of_not_exitFourFreeAt data object exact
        isReceiver stateSaturated
        (exhausted packing canonical valid maximal component present negative
          zero receiver isReceiver state stateInside stateSaturated)
      obtain ⟨next⟩ := ExitFourAt.exists_witness data object occurs
      exact Or.inr ⟨next.load, next.routed, next.fresh,
        Graph.ExitFour.peeledByWitnesses_nextPeeled stateWitnessed next⟩)
  rcases descent with ⟨_final, _finalInside, _finalWitnessed, impossible⟩ |
    ⟨final, finalInside, finalWitnessed, finalUnsaturated⟩
  · exact impossible.elim
  · exact ⟨packing, canonical, valid, maximal, component, present, negative,
      zero, receiver, isReceiver, final, finalInside, finalWitnessed,
      finalUnsaturated,
      (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
        data.dischargeScale receiver final).mp finalUnsaturated⟩

/-! ## Exit `(5)`, nodes `[103]`--`[104]` -/

theorem typeAExitFiveFree_of_not_exitFive
    (exit : ¬ TypeAExitFiveStatement data object) :
    TypeAExitFiveFreeStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated exitFree compression
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, exitFree,
    compression⟩

/-- Node `[104]`: a target-complete proper-support compression of a selected
trace basin is a compressible proper atom, which `cor:uncompressible`
excludes. -/
theorem typeAExitFive_contradiction
    (uncompressible : UncompressibleStatement data object)
    (exit : TypeAExitFiveStatement data object) : False := by
  obtain ⟨packing, _canonical, _valid, _maximal, component, _present, _charge,
    _surplus, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
    _exitFree, _load, _eligible, basin, _selected, compression⟩ := exit
  obtain ⟨retained, _retainedSubset, _changed, complete, connected, proper,
    baseline, smaller⟩ := compression
  let piece := object.pieceSupport (object.remainderSupport packing) component
  apply uncompressible basin
  refine ⟨connected, proper, ?_⟩
  refine ⟨Graph.Route8.PresentedEntry.retainedReading object piece basin
      data.threshold data.LengthOK
      (Graph.Route8.PresentedEntry.retainedBaseCoordinates object piece
        retained), ?_, baseline, smaller, ?_⟩
  · exact complete.profile_eq
  · exact fun outside => complete.contextEquivalent outside

/-! ## Exit `(6)`, nodes `[105]`--`[106]` -/

theorem typeAExitSixFree_of_not_exitSix
    (exit : ¬ TypeAExitSixStatement data object) :
    TypeAExitSixFreeStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated exitFree noFive delocalizes
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, exitFree, noFive,
    delocalizes⟩

theorem typeAExitSixGlobalScope_of_not_proper
    (proper : ¬ TypeAExitSixProperScopeStatement data object) :
    TypeAExitSixGlobalScopeStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated exitFree noFive properAt
  exact proper ⟨packing, canonical, valid, maximal, component, present,
    negative, zero, receiver, isReceiver, peeled, inside, saturated, exitFree,
    noFive, properAt⟩

/-- `lem:proper-smearing`: a delocalization adjoining a proper support is a
replacement of that support. -/
theorem typeAExitSixProper_of_scope
    (proper : TypeAExitSixProperScopeStatement data object) :
    TypeAExitSixProperStatement data object := by
  obtain ⟨_packing, _canonical, _valid, _maximal, _component, _present,
    _negative, _zero, _receiver, _isReceiver, _peeled, _inside, _saturated,
    _exitFree, _noFive, _load, _eligible, _basin, _selected, delocalization,
    vertex, outside⟩ := proper
  exact ⟨_, delocalization.properReplacement ⟨vertex, outside⟩⟩

/-- `lem:no-silent-global-smearing`: when no delocalization of an exit-`(6)`
state adjoins a proper support, the delocalization of the committed exit-`(6)`
state adjoins all of `G` and supplies a strictly smaller closed
representative. -/
theorem typeAExitSixGlobal_of_scope
    (six : TypeAExitSixStatement data object)
    (global : TypeAExitSixGlobalScopeStatement data object) :
    TypeAExitSixGlobalStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, exitFree, noFive,
    load, eligible, basin, selected, ⟨delocalization⟩⟩ := six
  have covers : ∀ vertex, vertex ∈ delocalization.quotient.support := by
    intro vertex
    by_contra outside
    exact global packing canonical valid maximal component present negative
      zero receiver isReceiver peeled inside saturated exitFree noFive
      ⟨load, eligible, basin, selected, delocalization, vertex, outside⟩
  exact delocalization.closedRepresentative covers

/-- Node `[106]`, proper scope: the replacement contradicts `lem:replacement`
(`cor:uncompressible`'s replacement exclusion). -/
theorem typeAExitSixProper_contradiction
    (exclusion : ReplacementExclusionStatement data object)
    (exit : TypeAExitSixProperStatement data object) : False := by
  obtain ⟨support, replacement⟩ := exit
  exact exclusion support replacement

/-- Node `[106]`, whole-graph scope: the strictly smaller closed representative
contradicts the minimality of the selected counterexample. -/
theorem typeAExitSixGlobal_contradiction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (exit : TypeAExitSixGlobalStatement data object) : False := by
  obtain ⟨representative, smaller, representativeBaseline, transfer⟩ := exit
  exact avoids (transfer (minimal representative smaller representativeBaseline))

/-! ## Exit `(7)` and the route-`8` residual, nodes `[107]`--`[109]` -/

theorem typeAExitSevenAbsent_of_not_handoff
    (exit : ¬ TypeAExitSevenHandoffStatement data object) :
    TypeAExitSevenAbsentStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated exitFree noFive noSix produced
  exact exit ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, exitFree, noFive,
    noSix, produced⟩

/-- Node `[109]`: the exit-`(4)`-free state of the exit segment, at which exits
`(5)`, `(6)` and `(7)` all fail, is the route-`8` residual. -/
theorem typeAExitSevenFree
    (exitFree : TypeASaturatedHandoffExitFourFreeStatement data object)
    (five : TypeAExitFiveFreeStatement data object)
    (six : TypeAExitSixFreeStatement data object)
    (seven : TypeAExitSevenAbsentStatement data object) :
    TypeAExitSevenFreeStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, peeled, inside, saturated, fourFree⟩ := exitFree
  have noFive := five packing canonical valid maximal component present negative
    zero receiver isReceiver peeled inside saturated fourFree
  have noSix := six packing canonical valid maximal component present negative
    zero receiver isReceiver peeled inside saturated fourFree noFive
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, peeled, inside, saturated, fourFree, noFive, noSix,
    seven packing canonical valid maximal component present negative zero
      receiver isReceiver peeled inside saturated fourFree noFive noSix⟩

theorem typeAExitEightNotSilent_of_not_silent
    (silent : ¬ SelectedSilentExitSevenFree data object) :
    TypeAExitEightNotSilentStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver peeled inside saturated fourFree noFive noSix origin
  exact silent ⟨packing, canonical, valid, maximal, component, present,
    negative, zero, receiver, isReceiver, peeled, inside, saturated, fourFree,
    noFive, noSix, origin⟩

end Hypostructure.Graph.Contracts.TypeA
