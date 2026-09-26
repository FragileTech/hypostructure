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

/-- Node `[100]`: a failed legal-label relation at a shared window builds a
cycle of accepted length (`lem:labels`); the degenerate closure of length `2`
is not accepted. -/
theorem typeAExitThreeCollision_contradiction
    (degenerate : ¬ data.LengthOK 2)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (exit : TypeAExitThreeCollisionStatement data object) : False := by
  obtain ⟨_piece, _pinned, _receiver, _chosen, _port, _portPinned, collision⟩ :=
    exit
  exact avoids
    (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision degenerate
      collision)

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

/-- Node `[101]`, no arm: with no exit `(4)` at the entry state the canonical
sequence never moves, so the terminal state is the entry state, saturated and
exit-`(4)`-free; exits `(5)`--`(8)` are asked there. -/
theorem typeASaturatedHandoffExitFourFree_of_absent
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (low : TypeALowSurplusStatement data object)
    (entry : TypeASaturatedExitEntryStatement data object)
    (absent : TypeAExitFourAbsentStatement data object) :
    TypeASaturatedHandoffExitFourFreeStatement data object := by
  obtain ⟨piece, pinned, zero, stateEntry, stateAbsent⟩ :=
    canonicalPin_merge low (canonicalPin_merge entry absent)
  obtain ⟨receiver, chosen, saturated, noExit⟩ :=
    canonicalPin_merge stateEntry stateAbsent
  have none : canonicalExitFourWitnessAt data object piece receiver ∅ = Option.none :=
    canonicalExitFourWitnessAt_eq_none_iff.mpr fun found =>
      noExit ((exitFourAt_iff_exists_witnessSpec data object piece receiver ∅).mpr
        found)
  have terminal := canonicalTerminalPeeled_eq_empty_of_none data object piece
    receiver none
  refine ⟨piece, pinned, receiver, chosen, ?_⟩
  show ExitFourFreeStateAt data object piece receiver
    (canonicalTerminalPeeled data object piece receiver)
  rw [terminal]
  exact ⟨saturated,
    exitFourFreeAt_of_not_exitFourAt data object
      (exitReceiver_degree data object baseline zero chosen)
      (canonicalExitReceiverAt_spec_of_eq_some chosen).1 saturated noExit⟩

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

/-- At the terminal set a still-saturated exit-chain receiver is
exit-`(4)`-free (`lem:typeA-saturated-handoff`: the peeling stops only when no
witness remains). -/
theorem exitFourFreeAt_terminal
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    (zero : object.ambientSurplus piece data.threshold = 0)
    (chosen : canonicalExitReceiverAt data object piece = some receiver)
    (saturated : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver
      (canonicalTerminalPeeled data object piece receiver)) :
    ExitFourFreeAt data object piece receiver
      (canonicalTerminalPeeled data object piece receiver) := by
  have none := canonicalTerminalPeeled_witness_eq_none data object piece receiver
    saturated
  refine exitFourFreeAt_of_not_exitFourAt data object
    (exitReceiver_degree data object baseline zero chosen)
    (canonicalExitReceiverAt_spec_of_eq_some chosen).1 saturated ?_
  intro occurs
  exact canonicalExitFourWitnessAt_eq_none_iff.mp none
    ((exitFourAt_iff_exists_witnessSpec data object piece receiver _).mp occurs)

/-- `lem:typeA-exit4-peeling-charge`: an unsaturated receiver at the terminal
set has nonnegative remaining receiver charge. -/
theorem receiverDischarged_of_not_saturated
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (unsaturated : ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver peeled) :
    1 + Graph.ExitFour.residualLoad piece data.threshold receiver peeled ≤
      data.dischargeScale * object.missingPorts piece data.threshold receiver :=
  (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
    data.dischargeScale receiver peeled).mp unsaturated

/-! ## Exit `(5)`, node `[104]` -/

/-- Node `[104]`: a target-complete proper-support compression of a selected
trace basin at the terminal state is a compressible proper atom, which
`cor:uncompressible` excludes. -/
theorem typeAExitFive_contradiction
    (uncompressible : UncompressibleStatement data object)
    (exit : TypeAExitFiveStatement data object) : False := by
  obtain ⟨piece, _pinned, _receiver, _chosen, _state, _load, _eligible, basin,
    _selected, compression⟩ := exit
  obtain ⟨retained, _retainedSubset, _changed, complete, connected, proper,
    baseline, smaller⟩ := compression
  apply uncompressible basin
  refine ⟨connected, proper, ?_⟩
  refine ⟨Graph.Route8.PresentedEntry.retainedReading object piece basin
      data.threshold data.LengthOK
      (Graph.Route8.PresentedEntry.retainedBaseCoordinates object piece
        retained), ?_, baseline, smaller, ?_⟩
  · exact complete.profile_eq
  · exact fun outside => complete.contextEquivalent outside

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
  obtain ⟨_piece, _pinned, _receiver, _chosen, delocalization, _found, covers⟩ :=
    global
  exact delocalization.2.closedRepresentative covers

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
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (exit : TypeAExitSixGlobalStatement data object) : False := by
  obtain ⟨representative, smaller, representativeBaseline, transfer⟩ := exit
  exact avoids (transfer (minimal representative smaller representativeBaseline))

end Hypostructure.Graph.Contracts.TypeA
