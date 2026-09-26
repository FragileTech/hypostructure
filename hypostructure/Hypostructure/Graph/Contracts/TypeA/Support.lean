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
spine, from the Type A/Type B split of the negative support to the visible-first
excess count.  Every lemma is stated over a `Graph.FiniteObject` and the
registered `Parameters`, at the objects of the object fixed upstream: the
node-`[61]` negative support `X₀ = canonicalNegativePiece`, its saturated
receiver, and its visible receiver.  Every paper assumption is an explicit
hypothesis, and each conclusion is exactly the library statement it proves.
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

/-! ## `X₀` -/

/-- The negative support of node `[61]` exists: `K .negativeSupport` is the
existence premise of `canonicalNegativeComponent`. -/
theorem canonicalNegativePiece_isSome
    (negative : NegativeSupportStatement data object) :
    ∃ piece, canonicalNegativePiece data object = some piece := by
  obtain ⟨_, exists_⟩ := (negativeSupportStatement_iff data object).mp negative
  obtain ⟨component, eq, _⟩ := canonicalNegativeComponent_spec exists_
  exact ⟨_, (canonicalNegativePiece_eq_some_iff).mpr ⟨component, eq, rfl⟩⟩

/-- The canonical packing is a maximal valid packing, read off
`K .negativeSupport`. -/
theorem canonicalWindowPacking_valid_maximal_of_negativeSupport
    (negative : NegativeSupportStatement data object) :
    object.IsWindowPacking data.windowOrder (canonicalWindowPacking data object) ∧
      ∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
          ∃ member ∈ canonicalWindowPacking data object, ¬ Disjoint window member :=
  ((negativeSupportStatement_iff data object).mp negative).1

/-- What `X₀` is: a connected canonical piece of `R(P₀)` with negative net
charge. -/
theorem canonicalNegativePiece_facts {piece : Finset object.Vertex}
    (pinned : canonicalNegativePiece data object = some piece) :
    ∃ component ∈ object.canonicalPieces (canonicalRemainder data object),
      object.pieceSupport (canonicalRemainder data object) component = piece ∧
      piece ⊆ canonicalRemainder data object ∧
      Graph.SupportComponents.Connected.ConnectedOn object piece ∧
      object.NegativeNetCharge piece data.threshold data.dischargeScale := by
  obtain ⟨component, eq, rfl⟩ := (canonicalNegativePiece_eq_some_iff).mp pinned
  obtain ⟨present, negative⟩ := canonicalNegativeComponent_spec_of_eq_some eq
  exact ⟨component, present, rfl,
    object.pieceSupport_subset (canonicalRemainder data object) component,
    Graph.SupportComponents.Connected.connectedOn_of_mem_order object
      (canonicalRemainder data object)
      ((object.mem_canonicalPieces (canonicalRemainder data object)).mp present),
    negative⟩

/-- The Type B arm of node `[62]` at `X₀`, unfolded to the canonical component
of `R(P₀)` whose support `X₀` is. -/
theorem typeBHighSurplus_support (typeB : TypeBHighSurplusStatement data object) :
    ∃ component ∈ object.canonicalPieces (canonicalRemainder data object),
      canonicalNegativePiece data object =
          some (object.pieceSupport (canonicalRemainder data object) component) ∧
        object.NegativeNetCharge
          (object.pieceSupport (canonicalRemainder data object) component)
          data.threshold data.dischargeScale ∧
        0 < object.ambientSurplus
          (object.pieceSupport (canonicalRemainder data object) component)
          data.threshold := by
  obtain ⟨piece, pinned, positive⟩ := typeB
  obtain ⟨component, present, rfl, _, _, negative⟩ :=
    canonicalNegativePiece_facts data object pinned
  exact ⟨component, present, pinned, negative, positive⟩

/-! ## Node `[86]`: the Type A support -/

/-- `def:typeA-support` at `X₀`: `σ(X₀) = 0`, so its negative net charge is
`s·def⁺(X₀) < |V(X₀)|`. -/
theorem typeASupport (low : TypeALowSurplusStatement data object) :
    TypeASupportStatement data object := by
  obtain ⟨piece, pinned, zero⟩ := low
  obtain ⟨_, _, _, _, _, charge⟩ := canonicalNegativePiece_facts data object pinned
  refine ⟨piece, pinned, ?_⟩
  unfold Graph.FiniteObject.NegativeNetCharge at charge
  rw [zero] at charge
  simpa using charge

/-! ## Node `[87]`: the bounded Type A support -/

/-- `P₁₃`-freeness, diameter and cardinality of `X₀`: shortest internal paths
are induced, so they have at most `windowOrder − 2` edges, and the subcubic
breadth-first count bounds the support. -/
theorem typeABoundedSupport
    (cubic : data.threshold = 3) (orderThree : 3 ≤ data.windowOrder)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (negativeSupport : NegativeSupportStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    (low : TypeALowSurplusStatement data object) :
    TypeABoundedSupportStatement data object := by
  classical
  obtain ⟨piece, pinned, zeroSurplus⟩ := low
  obtain ⟨_component, _present, _eq, inside, connected, _negative⟩ :=
    canonicalNegativePiece_facts data object pinned
  obtain ⟨valid, maximal⟩ :=
    canonicalWindowPacking_valid_maximal_of_negativeSupport data object
      negativeSupport
  have pieceFree : Graph.InducedPathFree (object.induce piece) data.windowOrder :=
    object.inducedPathFree_induce_of_forall
      (fun inner contained =>
        (normalized _ valid maximal inner (contained.trans inside)).1)
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
  exact ⟨piece, pinned, pieceFree, bounded, cardinality⟩

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

/-- The routing fact at `X₀`: every vertex of internal degree `δ` of `X₀` is
routed to a receiver. -/
theorem typeAReceiverRouting_at
    (negativeSupport : NegativeSupportStatement data object)
    (routing : TypeAReceiverRoutingStatement data object)
    {piece : Finset object.Vertex}
    (pinned : canonicalNegativePiece data object = some piece)
    (zero : object.ambientSurplus piece data.threshold = 0) :
    ∀ vertex ∈ piece,
      object.internalDegree piece vertex = data.threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece data.threshold vertex = some receiver ∧
          object.IsReceiver piece data.threshold receiver := by
  obtain ⟨valid, maximal⟩ :=
    canonicalWindowPacking_valid_maximal_of_negativeSupport data object
      negativeSupport
  obtain ⟨_, _, _, inside, _, _⟩ := canonicalNegativePiece_facts data object pinned
  exact (routing _ valid maximal piece inside zero).1

/-! ## Node `[89]`: the saturation split -/

/-- The no arm of the saturation test at `X₀`: no receiver is saturated, in the
subtraction-free form `1 + L(w) ≤ s·q(w)`. -/
theorem unsaturated_of_not_saturated {piece : Finset object.Vertex}
    (saturated : ¬ ∃ receiver, SaturatedReceiverSpec data object piece receiver) :
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      1 + object.routedLoad piece data.threshold receiver ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver := by
  intro receiver isReceiver
  refine (object.not_saturated_iff piece data.threshold data.dischargeScale
    receiver).mp ?_
  exact fun full => saturated ⟨receiver, isReceiver, full⟩

/-! ## Nodes `[90]`--`[92]`: the unsaturated discharge and its closure -/

/-- `lem:typeA-unsaturated-discharge` at `X₀`: when every receiver of `X₀` is
unsaturated, `|V(X₀)| ≤ s·def⁺(X₀)`. -/
theorem typeAUnsaturatedDischarge
    (negativeSupport : NegativeSupportStatement data object)
    (routing : TypeAReceiverRoutingStatement data object)
    (low : TypeALowSurplusStatement data object)
    (unsaturated : TypeAUnsaturatedReceiversStatement data object) :
    TypeAUnsaturatedDischargeStatement data object := by
  obtain ⟨piece, pinned, surplus, bound⟩ := canonicalPin_merge low unsaturated
  exact ⟨piece, pinned,
    Graph.FiniteObject.unsaturatedDischarge object piece data.threshold
      data.dischargeScale
      (Graph.DecoratedAbsorption.capped_of_ambientSurplus_zero object piece
        data.threshold surplus)
      (typeAReceiverRouting_at data object negativeSupport routing pinned surplus)
      bound⟩

/-- Node `[92]`: the unsaturated discharge `|V(X₀)| ≤ s·def⁺(X₀)` contradicts
the Type A support's `s·def⁺(X₀) < |V(X₀)|`. -/
theorem typeASupport_unsaturatedDischarge_contradiction
    (support : TypeASupportStatement data object)
    (discharge : TypeAUnsaturatedDischargeStatement data object) : False := by
  obtain ⟨_piece, _pinned, deficiency, bound⟩ := canonicalPin_merge support discharge
  exact absurd bound (not_le.mpr deficiency)

/-! ## `lem:typeA-port-return` -/

/-- Every completion port of every receiver of `X₀` carries an anchored return
(`lem:bridgeless`, through the selected minimal counterexample). -/
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
  obtain ⟨piece, pinned, _⟩ := saturated
  refine ⟨piece, pinned, ?_⟩
  intro receiver _receiverIsReceiver outside port
  exact Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts
    (LengthOK := data.LengthOK) twoLe baseline avoids minimal _ receiver outside
    port

/-! ## Node `[93]`: the visible-entry split -/

/-- The no arm of the visible-entry test at `X₀`. -/
theorem noVisible_of_not_visibleReceiver {piece : Finset object.Vertex}
    (visible : ¬ ∃ receiver, VisibleReceiverSpec data object piece receiver) :
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      object.Saturated piece data.threshold data.dischargeScale receiver →
      ¬ Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece
        data.threshold data.dischargeScale receiver ∅) :=
  fun receiver isReceiver saturated package =>
    visible ⟨receiver, isReceiver, saturated, package⟩

/-- On the visible arm the visible receiver of `X₀` and its overloaded port at
the empty peeling set exist. -/
theorem visibleEntry_pins (visible : TypeAVisibleEntryStatement data object) :
    ∃ piece, canonicalNegativePiece data object = some piece ∧
      ∃ receiver, canonicalVisibleReceiverAt data object piece = some receiver ∧
        ∃ port, canonicalOverloadedPortAt data object piece receiver ∅ =
          some port := by
  obtain ⟨piece, pinned, exists_⟩ := visible
  obtain ⟨receiver, chosen, _, _, ⟨package⟩⟩ :=
    canonicalVisibleReceiverAt_spec exists_
  exact ⟨piece, pinned, receiver, chosen, package.outside,
    VisibleFourUnpeeledPackage.outside_eq_canonicalOverloadedPortAt package⟩

/-- The pinned overloaded port of the visible receiver is one of its
completion ports. -/
theorem visiblePort_mem_completionPorts {piece : Finset object.Vertex}
    {receiver port : object.Vertex}
    (chosen : canonicalVisibleReceiverAt data object piece = some receiver)
    (pinned : canonicalOverloadedPortAt data object piece receiver ∅ = some port) :
    port ∈ Graph.VisibleEntry.completionPorts object piece receiver := by
  obtain ⟨_, _, ⟨package⟩⟩ := canonicalVisibleReceiverAt_spec_of_eq_some chosen
  have eq := VisibleFourUnpeeledPackage.outside_eq_canonicalOverloadedPortAt package
  rw [pinned] at eq
  cases eq
  exact package.port

/-! ## Node `[94]`: the visible-first excess -/

/-- `lem:typeA-silent-excess-count` at `X₀` and its node-`[89]` receiver `w₀`:
when no saturated receiver of `X₀` has an overloaded completion port, the
visible-first excess is silent and carries the whole excess,
`|V(X₀)| ≤ S_sil^exc(X₀) + s·def⁺(X₀)`, and `w₀`'s residual excess is nonempty
and silent. -/
theorem typeAVisibleFirstExcess
    (scalePos : 0 < data.dischargeScale)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (negativeSupport : NegativeSupportStatement data object)
    (routing : TypeAReceiverRoutingStatement data object)
    (low : TypeALowSurplusStatement data object)
    (saturated : TypeASaturatedReceiverStatement data object)
    (noVisible : TypeANoVisibleEntryStatement data object) :
    TypeAVisibleFirstExcessStatement data object := by
  classical
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  obtain ⟨piece, pinned, zero, exists_, noVisibleAt⟩ :=
    canonicalPin_merge low (canonicalPin_merge saturated noVisible)
  obtain ⟨selectedReceiver, chosen, selectedIsReceiver, selectedSaturated⟩ :=
    canonicalSaturatedReceiverAt_spec exists_
  have routed :=
    typeAReceiverRouting_at data object negativeSupport routing pinned zero
  have exactDegree : ∀ vertex ∈ piece, object.degree vertex = data.threshold :=
    degree_eq_threshold_of_ambientSurplus_eq_zero object baseline zero
  have capped : ∀ vertex ∈ piece,
      object.internalDegree piece vertex ≤ data.threshold :=
    Graph.DecoratedAbsorption.capped_of_ambientSurplus_zero object piece
      data.threshold zero
  have noVisibleOverload : ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      object.Saturated piece data.threshold data.dischargeScale receiver →
      ¬ Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
        data.dischargeScale receiver ∅ := by
    intro receiver isReceiver full overloaded
    exact noVisibleAt receiver isReceiver full
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
      apply noVisibleOverload receiver isReceiver full
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
      capped routed noVisiblePorts
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
        (noVisibleOverload selectedReceiver selectedIsReceiver selectedSaturated
          overloaded)
    · exact silent
  exact ⟨piece, pinned, selectedReceiver, chosen, noVisibleOverload,
    selectedSaturated, selectedSilent, supportBound⟩

/-! ## The shared entry of the saturated exit segment -/

/-- The visible lane enters the exit segment at the empty peeling set of the
visible receiver of `X₀` (`lem:typeA-unpeeled-visible-routing`). -/
theorem typeASaturatedExitEntry_of_exitThreeFree
    (three : TypeAExitThreeFreeStatement data object) :
    TypeASaturatedExitEntryStatement data object := by
  obtain ⟨piece, pinned, receiver, chosen, _⟩ := three
  have exit : canonicalExitReceiverAt data object piece = some receiver := by
    simp [canonicalExitReceiverAt, chosen]
  obtain ⟨_, saturated, _⟩ := canonicalVisibleReceiverAt_spec_of_eq_some chosen
  exact ⟨piece, pinned, receiver, exit,
    (Graph.ExitFour.saturatedAfter_empty _ data.threshold
      data.dischargeScale receiver).mpr saturated⟩

/-- The silent lane enters the same exit segment at the empty peeling set of
the node-`[89]` receiver of `X₀` (`lem:typeA-unpeeled-silent-routing`). -/
theorem typeASaturatedExitEntry_of_visibleFirstExcess
    (excess : TypeAVisibleFirstExcessStatement data object)
    (noVisible : TypeANoVisibleEntryStatement data object) :
    TypeASaturatedExitEntryStatement data object := by
  obtain ⟨piece, pinned, ⟨receiver, chosen, origin⟩, none⟩ :=
    canonicalPin_merge excess noVisible
  have visibleNone : canonicalVisibleReceiverAt data object piece = Option.none :=
    canonicalVisibleReceiverAt_eq_none_iff.mpr
      fun ⟨other, isReceiver, saturated, package⟩ =>
        none other isReceiver saturated package
  have exit : canonicalExitReceiverAt data object piece = some receiver := by
    simp [canonicalExitReceiverAt, visibleNone, chosen]
  exact ⟨piece, pinned, receiver, exit,
    (Graph.ExitFour.saturatedAfter_empty _ data.threshold
      data.dischargeScale receiver).mpr origin.2.1⟩

end Hypostructure.Graph.Contracts.TypeA
