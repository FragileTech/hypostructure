import Hypostructure.Graph.Statements.TypeA
import Hypostructure.Graph.SubcubicReach
import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.WindowRemainder
import Hypostructure.Graph.TypeADischarge
import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.PortReturnExistence
import Hypostructure.Graph.DecoratedAbsorption

/-!
# Contracts: the Type A support, its receivers, and the saturation split

Proof-agnostic contract lemmas for the Type A branch of a minimum-degree cycle
spine, from the Type A/Type B split of a negative support to the visible-first
excess count.  Every lemma is stated over a `Graph.FiniteObject` and the
registered `Parameters`; every paper assumption is an explicit hypothesis, and
each conclusion is exactly the library statement it proves.

The split lemmas (`*_of_not_*`) are the exact complements used by the branch
decisions: each turns the failure of an existential alternative into its
universal negation, stated in the positive form the paper writes.
-/

namespace Hypostructure.Graph.Contracts.TypeA

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-! ## Zero surplus against the baseline -/

/-- On a support of zero assigned surplus, every vertex sits exactly at the
minimum-degree baseline. -/
theorem degree_eq_threshold_of_ambientSurplus_eq_zero
    {threshold : Nat} (baseline : Graph.MinimumDegreeAtLeast threshold object)
    {piece : Finset object.Vertex}
    (zero : object.ambientSurplus piece threshold = 0) :
    ∀ vertex ∈ piece, object.degree vertex = threshold := by
  intro vertex member
  have lower : threshold ≤ object.degree vertex :=
    le_trans baseline (object.minDegree_le_degree vertex)
  have summand : object.degree vertex - threshold = 0 :=
    Finset.sum_eq_zero_iff.mp zero vertex member
  omega

/-! ## Node `[62]`: the Type A / Type B split -/

/-- The no arm of the surplus test is the exact negation of the yes arm. -/
theorem typeALowSurplus_of_not_typeBHighSurplus
    (high : ¬ TypeBHighSurplusStatement data object) :
    TypeALowSurplusStatement data object := by
  intro packing valid maximal component present _piece negative
  by_contra positive
  exact high ⟨packing, valid, maximal, component, present, negative,
    Nat.pos_of_ne_zero positive⟩

/-! ## Node `[86]`: the Type A support -/

/-- `def:typeA-support`: the negative canonical piece of the selected maximal
packing has `σ(X) = 0`, so its negative net charge is `s·def⁺(X) < |V(X)|`. -/
theorem typeASupport
    (negative : NegativeSupportStatement data object)
    (low : TypeALowSurplusStatement data object) :
    TypeASupportStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, charge⟩ :=
    negative
  have zero := low packing valid maximal component present charge
  refine ⟨packing, canonical, valid, maximal, component, present, charge, zero,
    ?_⟩
  have charge' := charge
  unfold Graph.FiniteObject.NegativeNetCharge at charge'
  rw [zero] at charge'
  simpa using charge'

/-! ## Node `[87]`: bounded Type A supports -/

/-- `P₁₃`-freeness, diameter and cardinality of a Type A support: shortest
internal paths are induced, so they have at most `windowOrder − 2` edges, and
the subcubic breadth-first count bounds the support. -/
theorem typeABoundedSupport
    (cubic : data.threshold = 3) (orderThree : 3 ≤ data.windowOrder)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (normalized : RemainderNormalizedStatement data object)
    (support : TypeASupportStatement data object) :
    TypeABoundedSupportStatement data object := by
  classical
  obtain ⟨packing, _canonical, valid, maximal, component, present, negative,
    zeroSurplus, _deficiency⟩ := support
  let piece := object.pieceSupport (object.remainderSupport packing) component
  have inside : piece ⊆ object.remainderSupport packing :=
    object.pieceSupport_subset (object.remainderSupport packing) component
  have connected :
      Graph.SupportComponents.Connected.ConnectedOn object piece :=
    Graph.SupportComponents.Connected.connectedOn_of_mem_order object
      (object.remainderSupport packing)
      ((object.mem_canonicalPieces (object.remainderSupport packing)).mp present)
  have pieceFree : Graph.InducedPathFree (object.induce piece) data.windowOrder :=
    object.inducedPathFree_induce_of_forall
      (fun inner contained =>
        (normalized packing valid maximal inner (contained.trans inside)).1)
  have exactDegree : ∀ vertex ∈ piece, object.degree vertex = data.threshold :=
    degree_eq_threshold_of_ambientSurplus_eq_zero object baseline zeroSurplus
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have bounded : ∀ left ∈ piece, ∀ right ∈ piece,
      ∃ path : object.graph.Walk left right,
        path.IsPath ∧
          (∀ vertex ∈ path.support, vertex ∈ piece) ∧
          path.length ≤ data.windowOrder - 2 := by
    intro left leftMem right rightMem
    obtain ⟨initial, _initialPath, initialInside⟩ :=
      connected.2 leftMem rightMem
    let induced := initial.induce (↑piece : Set object.Vertex) initialInside
    obtain ⟨shortest, shortestPath, shortestLength⟩ :=
      induced.reachable.exists_path_of_dist
    have shortestBound : shortest.length ≤ data.windowOrder - 2 :=
      Graph.shortestPath_length_le_order_sub_two (object.induce piece)
        data.windowOrder orderThree shortest shortestPath shortestLength
        pieceFree
    let embedding := object.induceEmbedding piece
    let ambient := shortest.map embedding.toHom
    have ambientPath : ambient.IsPath :=
      (SimpleGraph.Walk.map_isPath_iff_of_injective embedding.injective).2
        shortestPath
    have ambientInside : ∀ vertex ∈ ambient.support, vertex ∈ piece := by
      intro vertex member
      simp only [ambient, SimpleGraph.Walk.support_map, List.mem_map] at member
      obtain ⟨inner, _innerMem, rfl⟩ := member
      exact inner.2
    have ambientLength : ambient.length ≤ data.windowOrder - 2 := by
      rw [SimpleGraph.Walk.length_map]
      exact shortestBound
    exact ⟨ambient, ambientPath, ambientInside, ambientLength⟩
  obtain ⟨root, rootMem⟩ := connected.1
  have pieceSubset : piece ⊆
      Graph.SubcubicReach.reach object.graph piece root
        (data.windowOrder - 2) root := by
    intro vertex vertexMem
    obtain ⟨path, pathIsPath, pathInside, pathLength⟩ :=
      bounded root rootMem vertex vertexMem
    exact (Graph.SubcubicReach.mem_reach object.graph).2
      ⟨path, pathIsPath, pathLength,
        (fun z zMem => pathInside z (List.mem_of_mem_dropLast zMem)),
        fun notNil same => by
          have atStart :=
            (pathIsPath.getVert_eq_start_iff_of_not_nil (i := 1) notNil).1 same
          exact absurd atStart (by decide)⟩
  have cardinality : piece.card ≤
      1 + data.threshold * (2 ^ (data.windowOrder - 2) - 1) := by
    calc
      piece.card ≤
          (Graph.SubcubicReach.reach object.graph piece root
            (data.windowOrder - 2) root).card :=
        Finset.card_le_card pieceSubset
      _ ≤ 1 + data.threshold * (2 ^ (data.windowOrder - 2) - 1) := by
        have reachBound :=
          Graph.SubcubicReach.card_reach_le (G := object.graph) (S := piece)
            (fun vertex vertexMem => by
              simpa [Graph.FiniteObject.degree, cubic] using
                le_of_eq (exactDegree vertex vertexMem))
            root (data.windowOrder - 2)
        simpa [cubic] using reachBound
  exact ⟨packing, valid, maximal, component, present, negative, zeroSurplus,
    pieceFree, bounded, cardinality⟩

/-! ## Node `[88]`: receiver routing and the threshold algebra -/

/-- `lem:typeA-receiver-loads` and `lem:typeA-threshold-algebra` at every
zero-surplus subregion of a maximal packing's remainder. -/
theorem typeAReceiverRouting
    (normalized : RemainderNormalizedStatement data object) :
    TypeAReceiverRoutingStatement data object := by
  classical
  intro packing valid maximal piece inside surplus
  have noCore : ∀ inner : Finset object.Vertex, inner ⊆ piece →
      ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce inner) :=
    fun inner contained =>
      (normalized packing valid maximal inner (contained.trans inside)).2
  refine ⟨fun vertex member full => ?_, fun receiver isReceiver => ?_⟩
  · obtain ⟨_target, trace⟩ :=
      object.exists_traceTo_of_no_baseline_subsupport piece data.threshold
        noCore member (le_of_eq full.symm)
    obtain ⟨found, routed⟩ :=
      Option.isSome_iff_exists.mp (object.isSome_traceReceiver?_of_traceTo trace)
    exact ⟨found, routed,
      object.isReceiver_of_traceTo
        (object.traceTo_of_traceReceiver?_eq_some routed)⟩
  · exact ⟨object.saturationThreshold_eq piece data.threshold
      data.dischargeScale isReceiver.2,
      object.saturationThreshold_le piece data.threshold data.dischargeScale
        receiver⟩

/-! ## Node `[89]`: the saturation split -/

/-- The no arm of the saturation test is the exact negation of its yes arm,
in the subtraction-free form `1 + L(w) ≤ s·q(w)`. -/
theorem typeAUnsaturatedReceivers_of_not_saturated
    (saturated : ¬ TypeASaturatedReceiverStatement data object) :
    TypeAUnsaturatedReceiversStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver
  refine (object.not_saturated_iff _ data.threshold data.dischargeScale
    receiver).mp ?_
  exact fun full => saturated ⟨packing, canonical, valid, maximal, component,
    present, negative, zero, receiver, isReceiver, full⟩

/-! ## Nodes `[90]`--`[92]`: the unsaturated discharge and its closure -/

/-- `lem:typeA-unsaturated-discharge`: at a Type A support all of whose
receivers are unsaturated, `|V(X)| ≤ s·def⁺(X)`. -/
theorem typeAUnsaturatedDischarge
    (routing : TypeAReceiverRoutingStatement data object)
    (unsaturated : TypeAUnsaturatedReceiversStatement data object) :
    TypeAUnsaturatedDischargeStatement data object := by
  intro packing canonical valid maximal component present _piece negative surplus
  let piece := object.pieceSupport (object.remainderSupport packing) component
  have inside : piece ⊆ object.remainderSupport packing :=
    object.pieceSupport_subset (object.remainderSupport packing) component
  exact Graph.FiniteObject.unsaturatedDischarge object piece data.threshold
    data.dischargeScale
    (Graph.DecoratedAbsorption.capped_of_ambientSurplus_zero object piece data.threshold surplus)
    (routing packing valid maximal piece inside surplus).1
    (unsaturated packing canonical valid maximal component present negative
      surplus)

/-- Node `[92]`: the unsaturated discharge `|V(X)| ≤ s·def⁺(X)` contradicts the
Type A support's `s·def⁺(X) < |V(X)|`. -/
theorem typeASupport_unsaturatedDischarge_contradiction
    (support : TypeASupportStatement data object)
    (discharge : TypeAUnsaturatedDischargeStatement data object) : False := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, deficiency⟩ := support
  have bound := discharge packing canonical valid maximal component present
    negative zero
  exact absurd bound (not_le.mpr deficiency)

/-! ## `lem:typeA-port-return` -/

/-- Every completion port of every receiver of the saturated Type A support
carries an anchored return (`lem:bridgeless`, through the selected minimal
counterexample). -/
theorem typeAPortReturn
    (twoLe : 2 ≤ data.threshold)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      smaller.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (saturated : TypeASaturatedReceiverStatement data object) :
    TypeAPortReturnStatement data object := by
  obtain ⟨packing, _canonical, valid, maximal, component, present, negative,
    zero, selectedReceiver, selectedIsReceiver, selectedSaturated⟩ := saturated
  refine ⟨packing, valid, maximal, component, present, negative, zero,
    ⟨selectedReceiver, selectedIsReceiver, selectedSaturated⟩, ?_⟩
  intro receiver _receiverIsReceiver outside port
  exact Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts
    (LengthOK := data.LengthOK) twoLe baseline avoids minimal _ receiver outside
    port

/-- Every eligible completion port (no common baseline neighbour) of every
receiver of the saturated Type A support carries an anchored return of
power-of-two length, read off the contraction of the port edge.  The manuscript
has no such corollary and no label for it. -/
theorem portPowerReturn
    (contractionCritical : ContractionCriticalStatement data object)
    (saturated : TypeASaturatedReceiverStatement data object) :
    PortPowerReturnStatement data object := by
  obtain ⟨packing, _canonical, valid, maximal, component, present, negative,
    zero, selectedReceiver, selectedIsReceiver, selectedSaturated⟩ := saturated
  refine ⟨packing, valid, maximal, component, present, negative, zero,
    ⟨selectedReceiver, selectedIsReceiver, selectedSaturated⟩, ?_⟩
  intro receiver _receiverIsReceiver outside outsideMem noCommonCubic
  have adjacent : object.graph.Adj receiver outside :=
    (Graph.VisibleEntry.mem_completionPorts.mp outsideMem).1
  let contraction : Graph.EdgeContraction object := ⟨outside, receiver, adjacent.symm⟩
  obtain ⟨path, exponent, lower, pathLength⟩ :=
    contractionCritical contraction (by
      intro common outsideCommon receiverCommon
      exact noCommonCubic common receiverCommon outsideCommon)
  let return' := Graph.VisibleEntry.anchoredReturnOfSeveredPath adjacent path
  refine ⟨return', exponent, lower, ?_⟩
  simpa [return', Graph.VisibleEntry.anchoredReturnOfSeveredPath] using pathLength

/-! ## Node `[93]`: the visible-entry split -/

/-- The no arm of the visible-entry test is the exact negation of its yes
arm. -/
theorem typeANoVisibleEntry_of_not_visibleEntry
    (visible : ¬ TypeAVisibleEntryStatement data object) :
    TypeANoVisibleEntryStatement data object := by
  intro packing canonical valid maximal component present _piece negative zero
    receiver isReceiver saturated package
  exact visible ⟨packing, canonical, valid, maximal, component, present,
    negative, zero, receiver, isReceiver, saturated, package⟩

/-! ## Node `[94]`: the visible-first excess -/

/-- `lem:typeA-silent-excess-count`: at a Type A support no saturated receiver
of which has an overloaded completion port, the visible-first excess is silent
and carries the whole excess, `|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`; the selected
saturated receiver's residual excess is nonempty and silent. -/
theorem typeAVisibleFirstExcess
    (scalePos : 0 < data.dischargeScale)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (routing : TypeAReceiverRoutingStatement data object)
    (saturated : TypeASaturatedReceiverStatement data object)
    (noVisible : TypeANoVisibleEntryStatement data object) :
    TypeAVisibleFirstExcessStatement data object := by
  classical
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, selectedReceiver, selectedIsReceiver, selectedSaturated⟩ := saturated
  let piece := object.pieceSupport (object.remainderSupport packing) component
  have inside : piece ⊆ object.remainderSupport packing :=
    object.pieceSupport_subset (object.remainderSupport packing) component
  have routed := routing packing valid maximal piece inside zero
  have exactDegree : ∀ vertex ∈ piece, object.degree vertex = data.threshold :=
    degree_eq_threshold_of_ambientSurplus_eq_zero object baseline zero
  have capped : ∀ vertex ∈ piece,
      object.internalDegree piece vertex ≤ data.threshold :=
    Graph.DecoratedAbsorption.capped_of_ambientSurplus_zero object piece data.threshold zero
  have noVisibleAt : ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      object.Saturated piece data.threshold data.dischargeScale receiver →
      ¬ Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
        data.dischargeScale receiver ∅ := by
    intro receiver isReceiver full overloaded
    exact noVisible packing canonical valid maximal component present negative
      zero receiver isReceiver full
      (Graph.ExitFour.visibleFourUnpeeledPackage piece data.threshold
        data.dischargeScale receiver ∅ overloaded)
  have noVisiblePorts : ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      object.Saturated piece data.threshold data.dischargeScale receiver →
      ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece receiver,
        (Graph.VisibleEntry.visibleLoadsAt object piece data.threshold receiver
          outside).card + 1 ≤ data.dischargeScale := by
    intro receiver isReceiver full outside port
    have notOverloaded : ¬ data.dischargeScale ≤
        (Graph.VisibleEntry.visibleLoadsAt object piece data.threshold receiver
          outside).card := by
      intro overloaded
      apply noVisibleAt receiver isReceiver full
      refine ⟨outside, port, ?_⟩
      have atEmpty :
          Graph.ExitFour.unpeeledVisibleLoadsAt piece data.threshold receiver
              outside ∅ =
            Graph.VisibleEntry.visibleLoadsAt object piece data.threshold
              receiver outside := by
        ext load
        constructor
        · intro member
          exact (Finset.mem_inter.mp member).1
        · intro member
          exact Finset.mem_inter.mpr ⟨member, by
            simp [Graph.ExitFour.unpeeledLoads,
              Graph.VisibleEntry.visibleLoadsAt_subset object piece
                data.threshold receiver outside member]⟩
      exact atEmpty.symm ▸ overloaded
    omega
  have supportBound :=
    Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency
      object piece data.threshold data.dischargeScale scalePos exactDegree
      capped routed.1 noVisiblePorts
  have selectedAfter : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale selectedReceiver ∅ :=
    (Graph.ExitFour.saturatedAfter_empty piece data.threshold
      data.dischargeScale selectedReceiver).mpr selectedSaturated
  have selectedSilent : Graph.ExitFour.SilentUnpeeledExcessAt piece
      data.threshold data.dischargeScale selectedReceiver ∅ := by
    rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
        piece data.threshold data.dischargeScale selectedReceiver ∅
        (exactDegree selectedReceiver selectedIsReceiver.1)
        selectedIsReceiver selectedAfter with overloaded | silent
    · exact False.elim
        (noVisibleAt selectedReceiver selectedIsReceiver selectedSaturated
          overloaded)
    · exact silent
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    noVisibleAt, selectedReceiver, selectedIsReceiver, selectedSaturated,
    selectedSilent, supportBound⟩

/-! ## The shared entry of the saturated exit segment -/

/-- The visible lane enters the exit segment at the empty peeling set of its
saturated receiver (`lem:typeA-unpeeled-visible-routing`). -/
theorem typeASaturatedExitEntry_of_visibleEntry
    (visible : TypeAVisibleEntryStatement data object) :
    TypeASaturatedExitEntryStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, receiver, isReceiver, saturated, _package⟩ := visible
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, ∅, Finset.empty_subset _,
    (Graph.ExitFour.saturatedAfter_empty _ data.threshold
      data.dischargeScale receiver).mpr saturated,
    Graph.ExitFour.peeledByWitnesses_empty _ _ data.threshold
      data.dischargeScale receiver⟩

/-- The silent lane enters the same exit segment at the empty peeling set of
the node-`[94]` receiver (`lem:typeA-unpeeled-silent-routing`). -/
theorem typeASaturatedExitEntry_of_visibleFirstExcess
    (excess : TypeAVisibleFirstExcessStatement data object) :
    TypeASaturatedExitEntryStatement data object := by
  obtain ⟨packing, canonical, valid, maximal, component, present, negative,
    zero, _noVisible, receiver, isReceiver, saturated, _silent, _count⟩ :=
    excess
  exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
    receiver, isReceiver, ∅, Finset.empty_subset _,
    (Graph.ExitFour.saturatedAfter_empty _ data.threshold
      data.dischargeScale receiver).mpr saturated,
    Graph.ExitFour.peeledByWitnesses_empty _ _ data.threshold
      data.dischargeScale receiver⟩

end Hypostructure.Graph.Contracts.TypeA
