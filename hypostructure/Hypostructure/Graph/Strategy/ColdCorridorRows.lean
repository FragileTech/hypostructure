import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily

/-!
# The cold branch, nodes `[145]`--`[154]`

This module contains only paper-node operations on the literal current
`ExactLedger`: two exclusive decisions and the atomic facts currently proved
through node `[152]`.  No alternate state or detached implication is exported;
the concrete germ family required at `[153]` remains a fact of that residual.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[146]`: decide the route-8 threshold on node `[145]`'s residual. -/
noncomputable def coldRoute8Dichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (belowFresh : K .coldRoute8Below ∉ known)
    (atOrAboveFresh : K .coldRoute8AtOrAbove ∉ known) :
    Decision (K .coldRoute8Below) (K .coldRoute8AtOrAbove) previous := by
  classical
  let _split := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .coldRoute8Below) (K .coldRoute8AtOrAbove)
    `Hypostructure.Graph.Strategy.Spine.coldRoute8Dichotomy
    (if below : ColdRoute8BelowStatement data current.object then
      .inl ⟨below⟩
    else
      .inr ⟨below⟩)
    belowFresh atOrAboveFresh

/-- Node `[148]`: decide the live-hot entropy comparison on `[146]`'s no arm. -/
noncomputable def coldHotEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (overflowFresh : K .coldHotEntropyOverflow ∉ known)
    (capFresh : K .coldHotEntropyCap ∉ known) :
    Decision (K .coldHotEntropyOverflow) (K .coldHotEntropyCap) previous := by
  classical
  let _split := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .coldHotEntropyOverflow) (K .coldHotEntropyCap)
    `Hypostructure.Graph.Strategy.Spine.coldHotEntropyDichotomy
    (if overflow : ColdHotEntropyOverflowStatement data current.object then
      .inl ⟨overflow⟩
    else
      .inr ⟨Nat.le_of_not_lt overflow⟩)
    overflowFresh capFresh

/-! Node `[149]`: the live-hot overflow arm closes by the entropy comparison.
The density cap is available after the cold branch closes. -/

/-- Node `[150]`: derive the exact cleared cold-mass inequality. -/
@[reducible] noncomputable def coldMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldMass
    { Requires := [K .hotColdPartition, K .coldHotEntropyCap]
      Produces := [K .coldMass]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      let hotBound := (inputs.get (K .coldHotEntropyCap)).down
      .cons (key := K .coldMass)
        ⟨by
          classical
          let packing := canonicalWindowPacking data inputs.current.object
          let hot := canonicalHotWindows data inputs.current.object
          let cold := canonicalColdWindows data inputs.current.object
          let _partition := split
          change coldWindowBitRate data inputs.current.object * hot.card ≤
            coldSkeletonAllowance data inputs.current.object at hotBound
          have hotSubset : hot ⊆ packing := by
            rcases split with ⟨_, _, _, hotFacts, _, _, _⟩
            exact hotFacts.1
          have count : packing.card = hot.card + cold.card := by
            have := (Finset.card_sdiff_add_card_eq_card hotSubset).symm
            rw [Nat.add_comm] at this
            exact this
          change ColdMassStatement data inputs.current.object
          simpa [ColdMassStatement] using
            Graph.ColdCorridor.hotFailure_coldMass
              (coldWindowBitRate data inputs.current.object) 0 0
              (coldSkeletonAllowance data inputs.current.object)
              hot.card cold.card packing.card count (by simpa using hotBound)⟩
        .nil)

/-- Node `[151]`: charge each non-ambient-cubic cold window injectively to a
positive-surplus vertex of the current object. -/
@[reducible] noncomputable def coldAmbientCubicRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldAmbientCubic
    { Requires := [K .hotColdPartition, K .surplusAtOrBelow,
        K .selection]
      Produces := [K .coldAmbientCubic]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      let nearCubic := (inputs.get (K .surplusAtOrBelow)).down
      let _selected := (inputs.get (K .selection)).down
      .cons (key := K .coldAmbientCubic)
        ⟨by
          classical
          rcases split with
            ⟨valid, _attains, _maximal, _hotIff, coldIff, _disjoint, _cover⟩
          have coldSubset : canonicalColdWindows data inputs.current.object ⊆
              canonicalWindowPacking data inputs.current.object := by
            intro window member
            exact (coldIff window).mp member |>.1
          change ColdAmbientCubicStatement data inputs.current.object
          refine ⟨?_, nearCubic⟩
          let object := inputs.current.object
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          letI : FinEnum object.Vertex := object.vertices
          letI : Fintype object.Vertex := inferInstance
          let ambient : Finset object.Vertex := Finset.univ.filter fun vertex =>
            data.threshold < object.degree vertex
          let bad : Finset (Finset object.Vertex) := cold.filter fun window =>
            ¬ AmbientCubicWindow data object window
          have baselineDegree : ∀ vertex : object.Vertex,
              data.threshold ≤ object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline
              (object.minDegree_le_degree vertex)
          have existsHigh (window : {window // window ∈ bad}) :
              ∃ vertex ∈ window.1, data.threshold < object.degree vertex := by
            have notCubic := (Finset.mem_filter.mp window.property).2
            simp only [AmbientCubicWindow] at notCubic
            push Not at notCubic
            obtain ⟨vertex, member, different⟩ := notCubic
            have lower := baselineDegree vertex
            exact ⟨vertex, member, by omega⟩
          let chosen : {window // window ∈ bad} → {vertex // vertex ∈ ambient} :=
            fun window => ⟨Classical.choose (existsHigh window),
              Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                (Classical.choose_spec (existsHigh window)).2⟩⟩
          have chosenMem (window : {window // window ∈ bad}) :
              (chosen window).1 ∈ window.1 :=
            (Classical.choose_spec (existsHigh window)).1
          have chosenInjective : Function.Injective chosen := by
            intro left right same
            apply Subtype.ext
            by_contra different
            have leftPacking : left.1 ∈ packing :=
              coldSubset (Finset.mem_filter.mp left.property).1
            have rightPacking : right.1 ∈ packing :=
              coldSubset (Finset.mem_filter.mp right.property).1
            have disjoint := valid.2 left.1 leftPacking right.1 rightPacking different
            have sameVertex : (chosen left).1 = (chosen right).1 :=
              congrArg Subtype.val same
            exact (Finset.disjoint_left.mp disjoint)
              (chosenMem left) (sameVertex.symm ▸ chosenMem right)
          have badCard : bad.card ≤ ambient.card := by
            simpa using Fintype.card_le_of_injective chosen chosenInjective
          have ambientCard : ambient.card ≤ object.degreeSurplus data.threshold := by
            calc
              ambient.card = ∑ _vertex ∈ ambient, 1 := by simp
              _ ≤ ∑ vertex ∈ ambient,
                    (object.degree vertex - data.threshold) := by
                exact Finset.sum_le_sum fun vertex member => by
                  have high := (Finset.mem_filter.mp member).2
                  omega
              _ ≤ ∑ vertex ∈ (Finset.univ : Finset object.Vertex),
                    (object.degree vertex - data.threshold) := by
                exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
              _ = object.degreeSurplus data.threshold := by
                simpa [Graph.FiniteObject.ambientSurplus] using
                  object.ambientSurplus_univ_eq_degreeSurplus
                    data.threshold baselineDegree
          have badBound : bad.card ≤ object.degreeSurplus data.threshold :=
            badCard.trans ambientCard
          have splitCard := cold.card_filter_add_card_filter_not
            (AmbientCubicWindow data object)
          change cold.card ≤
            (cold.filter (AmbientCubicWindow data object)).card +
              object.degreeSurplus data.threshold
          rw [← splitCard]
          convert Nat.add_le_add_left badBound
            (cold.filter (AmbientCubicWindow data object)).card using 1
          ⟩
        .nil)

/-- Node `[152]`: derive the branch-excess inequality from node `[151]`. -/
@[reducible] noncomputable def coldStubExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldStubExcess
    { Requires := [K .hotColdPartition, K .coldAmbientCubic]
      Produces := [K .coldSelectedBranchExcess,
        K .coldAmbientCubicStubExcess, K .coldStubExcess]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      let exactStubs : ColdAmbientCubicStubExcessStatement data
          inputs.current.object := by
        classical
        let object := inputs.current.object
        let packing := canonicalWindowPacking data object
        let cold := canonicalColdWindows data object
        let cubicWindows := cold.filter (AmbientCubicWindow data object)
        rcases split with
          ⟨valid, _attains, _maximal, _hotFacts, coldIff, _hotCold, _cover⟩
        intro window member
        have packingMem : window ∈ packing :=
          (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
        have stubCount :=
          Graph.ColdCorridor.externalStubList_length_add_internal_eq_stubCount
            object window (valid.1 window packingMem)
              (Finset.mem_filter.mp member).2
        simpa only [coldExternalStubCount] using
          Nat.eq_sub_of_add_eq stubCount
      .cons (key := K .coldSelectedBranchExcess)
        ⟨by
          classical
          let object := inputs.current.object
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          let cubicWindows := cold.filter (AmbientCubicWindow data object)
          rcases split with
            ⟨valid, _attains, _maximal, _hotFacts, coldIff, _hotCold, _cover⟩
          have cubicSubset : cubicWindows ⊆ packing := by
            intro window member
            exact (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
          have cubicDisjoint : ∀ left ∈ cubicWindows, ∀ right ∈ cubicWindows,
              left ≠ right → Disjoint left right := by
            intro left leftMem right rightMem different
            exact valid.2 left (cubicSubset leftMem) right (cubicSubset rightMem) different
          change ColdSelectedBranchExcessStatement data object
          refine ⟨?_, ?_⟩
          · rw [Graph.ColdCorridor.card_allSelectedStubs object cubicWindows
                cubicDisjoint]
            calc
              ∑ window ∈ cubicWindows,
                    ((Graph.ColdCorridor.interiorStubList object window).length - 2) =
                  ∑ _window ∈ cubicWindows,
                    coldInteriorBranchExcess data := by
                refine Finset.sum_congr rfl fun window member => ?_
                have packingMem : window ∈ packing :=
                  (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
                have induces : object.InducesWindow data.windowOrder window :=
                  valid.1 window packingMem
                have cubicDegree : ∀ vertex ∈ window,
                    object.degree vertex = data.threshold :=
                  (Finset.mem_filter.mp member).2
                obtain ⟨ends, endsSubset, endsCard, interior, endpoints⟩ :=
                  Graph.FiniteObject.exists_ends_externalNeighbours window
                    data.three_le_windowOrder induces cubicDegree
                have interiorVertices : window.filter (fun vertex =>
                    (object.externalNeighbours window vertex).card = 1) =
                    window \ ends := by
                  ext vertex
                  simp only [Finset.mem_filter, Finset.mem_sdiff]
                  constructor
                  · rintro ⟨vertexMem, one⟩
                    refine ⟨vertexMem, ?_⟩
                    intro vertexEnd
                    have count := endpoints vertex vertexEnd
                    rw [data.threshold_eq_three] at count
                    omega
                  · rintro ⟨vertexMem, notEnd⟩
                    refine ⟨vertexMem, ?_⟩
                    have count := interior vertex vertexMem notEnd
                    simpa [data.threshold_eq_three] using count
                have interiorLength :
                    (Graph.ColdCorridor.interiorStubList object window).length =
                      data.windowOrder - 2 := by
                  rw [Graph.ColdCorridor.interiorStubList_length_eq_sum,
                    interiorVertices]
                  calc
                    ∑ vertex ∈ window \ ends,
                          (object.externalNeighbours window vertex).card =
                        ∑ _vertex ∈ window \ ends, 1 := by
                      refine Finset.sum_congr rfl fun vertex vertexMem => ?_
                      simpa [data.threshold_eq_three] using
                        interior vertex (Finset.mem_sdiff.1 vertexMem).1
                          (Finset.mem_sdiff.1 vertexMem).2
                    _ = (window \ ends).card := by simp
                    _ = window.card - ends.card :=
                      Finset.card_sdiff_of_subset endsSubset
                    _ = data.windowOrder - 2 := by rw [induces.2, endsCard]
                rw [interiorLength]
                rfl
              _ = coldInteriorBranchExcess data * cubicWindows.card := by
                simp [Nat.mul_comm]
          · intro stub stubMem
            have represented : ∃ window ∈ cubicWindows,
                stub ∈ Graph.ColdCorridor.selectedStubs object window := by
              change stub ∈
                Graph.ColdCorridor.allSelectedStubs object cubicWindows at stubMem
              simpa only [Graph.ColdCorridor.allSelectedStubs,
                Finset.mem_biUnion] using stubMem
            obtain ⟨window, windowMem, stubInWindow⟩ := represented
            refine ⟨window, ⟨windowMem, stubInWindow⟩, ?_⟩
            intro other otherFacts
            rcases otherFacts with ⟨otherMem, stubInOther⟩
            by_contra different
            have disjoint := cubicDisjoint window windowMem other otherMem
              (Ne.symm different)
            exact Finset.disjoint_left.mp disjoint
              (Graph.ColdCorridor.mem_selectedStubs_isStub object stubInWindow).1
              (Graph.ColdCorridor.mem_selectedStubs_isStub object stubInOther).1⟩
        (.cons (key := K .coldAmbientCubicStubExcess) ⟨exactStubs⟩
          (.cons (key := K .coldStubExcess)
            ⟨by
              classical
              change ColdStubExcessStatement data inputs.current.object
              simpa [ColdStubExcessStatement, ColdAmbientCubicStatement] using
                Graph.ColdCorridor.branchExcess_ge_of_cubic
                  (coldInteriorBranchExcess data)
                  ((canonicalColdWindows data inputs.current.object).filter
                    (AmbientCubicWindow data inputs.current.object)).card
                  (canonicalColdWindows data inputs.current.object).card
                  (inputs.current.object.degreeSurplus data.threshold) cubic.1⟩
            .nil)))

/-! ## Node `[153]`: the exact finite form of "positive for sufficiently large n"

`lem:cold-germ-extraction`, with node `[168]`'s endpoint repair, bounds the
selected interior germ family below by `9C/D_cold − o(n)`;
`thm:cold-branch-quantitative-closure` uses that "the
displayed lower bound is positive for all sufficiently large `n`".  In exact
finite form the two `o(n)` losses of `[151]`--`[153]` are `perWindow·σ(G)` (the
non-ambient-cubic windows) and `(threshold+1)·B_cold·σ(G)` (the oriented
high-to-subcubic candidate loss), so the branch that forces a germ is
`(perWindow + (threshold+1)·B_cold)·σ(G) < perWindow·C`, and
its complement is where the spine continues to `[24]`. -/

/-- Node `[153]`'s exhaustive comparison on the literal `[152]` residual. -/
noncomputable def coldMassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldStubExcess) known]
    (linearFresh : K .coldMassLinear ∉ known)
    (boundedFresh : K .coldMassBounded ∉ known) :
    Decision (K .coldMassLinear) (K .coldMassBounded) previous := by
  classical
  let _stubs := (previous.get (K .coldStubExcess)).down
  exact Decision.run previous (K .coldMassLinear) (K .coldMassBounded)
    `Hypostructure.Graph.Strategy.Spine.coldMassDichotomy
    (if linear : ColdMassLinearStatement data current.object then
      .inl ⟨linear⟩
    else
      .inr ⟨by
        change ¬ ((coldInteriorBranchExcess data +
            (data.threshold + 1) *
              Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
          current.object.degreeSurplus data.threshold <
            coldInteriorBranchExcess data *
              (canonicalColdWindows data current.object).card) at linear
        change coldInteriorBranchExcess data *
            (canonicalColdWindows data current.object).card ≤
          (coldInteriorBranchExcess data +
            (data.threshold + 1) *
              Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
            current.object.degreeSurplus data.threshold
        exact Nat.le_of_not_lt linear⟩)
    linearFresh boundedFresh

/-! ## Node `[153]`, `def:cold-corridor-first-failure`: the cold return corridors

*"Order the boundary stubs of `K` lexicographically … choose inside `K` the
lexicographically first simple path joining the outside endpoint of `hᵢ` to the
outside endpoint of `hᵢ₊₁`.  Together with the two boundary stubs this path is
the cold return corridor of `ε`.  Thus each selected branch-excess half-edge has
exactly one corridor."*  The two-stub clause is `lem:bridgeless` read from the
ledger; the connection is the component's own. -/
@[reducible] noncomputable def coldReturnCorridorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldReturnCorridors
    { Requires := [K .bridgeless, K .hotColdPartition]
      Produces := [K .coldReturnCorridors]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridgeless := (inputs.get (K .bridgeless)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .coldReturnCorridors)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          let cubic := (canonicalColdWindows data object).filter
            (AmbientCubicWindow data object)
          let packing := canonicalWindowPacking data object
          let windows := coldCorridorWindows data object
          change HotColdWindowStatement data object at split
          obtain ⟨_validPacking, _attains, _maximal, _hot,
            coldIff, _disjoint, _cover⟩ := split
          change ColdReturnCorridorsStatement data object
          simp only [ColdReturnCorridorsStatement]
          refine ⟨?_, ?_, ?_⟩
          · intro component outside entry
            exact ⟨Graph.ColdCorridor.corridorOfOutsideComponent object windows
              component outside bridgeless entry, rfl⟩
          · intro epsilon
            by_cases outsideFoot : epsilon.1.2 ∉ windows
            · left
              have selected := Graph.ColdCorridor.selected_facts object cubic
                ⟨epsilon.1, epsilon.property⟩
              let component := Graph.ColdCorridor.outsideComponentOf object windows
                epsilon.1.2 outsideFoot
              have outside :=
                Graph.ColdCorridor.outsideComponentOf_isOutsideComponent object
                  windows epsilon.1.2 outsideFoot
              have footMem : epsilon.1.2 ∈ component :=
                Graph.ColdCorridor.foot_mem_outsideComponentOf object windows
                  epsilon.1.2 outsideFoot
              have sourceInWindows : epsilon.1.1 ∈ windows := by
                obtain ⟨window, windowMember, sourceMember⟩ :=
                  (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                    selected.1
                have windowPacking : window ∈ packing :=
                  ((coldIff window).1 (Finset.mem_filter.1 windowMember).1).1
                change epsilon.1.1 ∈ Graph.ColdCorridor.windowsOf object packing
                exact (Graph.ColdCorridor.mem_windowsOf object packing _).2
                  ⟨window, windowPacking, sourceMember⟩
              have boundaryMember : (epsilon.1.2, epsilon.1.1) ∈
                  Graph.ColdCorridor.boundaryStubs object windows component :=
                (Graph.ColdCorridor.mem_boundaryStubs_iff object windows component
                  (epsilon.1.2, epsilon.1.1)).2
                  ⟨footMem, sourceInWindows, selected.2.symm⟩
              let corridor := Graph.ColdCorridor.corridorOfBoundaryStub object
                windows component outside bridgeless
                (epsilon.1.2, epsilon.1.1) boundaryMember
              exact ⟨outsideFoot, component, corridor, outside,
                Graph.ColdCorridor.Corridor.corridorOfBoundaryStub_entryStub object windows
                  component outside bridgeless (epsilon.1.2, epsilon.1.1)
                  boundaryMember⟩
            · exact Or.inr (not_not.mp outsideFoot)
          · have partition := Finset.card_filter_add_card_filter_not
              (s := Graph.ColdCorridor.allSelectedStubs object cubic)
              (fun stub => stub.2 ∉ windows)
            simpa only [not_not] using partition.symm⟩
        .nil)

/-! ## Node `[145]`, declared F4 support registry

`def:cold-corridor-first-failure` reaches this residual only after the Type-B
and route-8 handoff edges have been taken.  This owner therefore publishes the
exact empty active F4 registry; the occurrence row reads it through
`inputs.get`. -/
@[reducible] noncomputable def coldDeclaredHandoffLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldDeclaredHandoffLedger
    { Requires := []
      Produces := [K .coldDeclaredHandoffLedger]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldDeclaredHandoffLedger)
        ⟨⟨fun _support => False, fun _support impossible => impossible⟩⟩
        .nil)

/-! ## Node `[153]`, `lem:cold-corridor-first-failure`: routing

This is the joint owner of `K .coldCorridorState` and
`K .coldFailureRouting`.  It reads the selected-stub partition from
`K .coldReturnCorridors`, constructs the current finite prefix-code
presentation from the literal corridor and its bounded active interface, and
performs the terminal-or-first-repeat construction locally in this atomic
executor.  Its support, offset, relational label, embedded-incidence, and
labelled-degree data are all read from the current graph.  In particular, the
former `(support.card, head ∈ support)` surrogate is absent: equal retained
values mean equal labelled embedded data for the declared coordinate.

The second representative is selected only from the retained finite-state
class: it preserves the inherited boundary-degree profile and baseline, while
the target response is left to the manuscript's (F2)/G2 test.  In particular
the executor does not call `CanonicalPiece.cutStateRepresentative`, whose
all-context `ContextEquivalent` field would circularly erase that alternative.

The separately named (F1)--(F4) consequences are committed in the same atomic
row.  Candidate overlap and mass accounting belong to
`lem:cold-germ-extraction` and are not published under this key. -/

set_option maxHeartbeats 1600000 in
@[reducible] noncomputable def coldCorridorStateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldCorridorState
    { Requires := [K .coldReturnCorridors, K .hotColdPartition]
      Produces := [K .coldCorridorState]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let corridors := (inputs.get (K .coldReturnCorridors)).down
      let split := (inputs.get (K .hotColdPartition)).down
      let state : ColdCorridorStateStatement data inputs.current.object := by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          let cubic := (canonicalColdWindows data object).filter
            (AmbientCubicWindow data object)
          let packing := canonicalWindowPacking data object
          let windows := coldCorridorWindows data object
          let Selected := {stub : object.Vertex × object.Vertex //
            stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic}
          change HotColdWindowStatement data object at split
          obtain ⟨validPacking, _attains, _maximal, _hot,
            coldIff, _disjoint, _cover⟩ := split
          have cubicWindow : ∀ window ∈ cubic,
              object.InducesWindow data.windowOrder window := by
            intro window member
            have coldMember : window ∈ canonicalColdWindows data object :=
              (Finset.mem_filter.mp member).1
            have packingMember : window ∈ canonicalWindowPacking data object :=
              (coldIff window).mp coldMember |>.1
            exact validPacking.1 window packingMember
          have packingWindow : ∀ window ∈ packing,
              object.InducesWindow data.windowOrder window := by
            intro window member
            exact validPacking.1 window member
          change ColdReturnCorridorsStatement data object at corridors
          simp only [ColdReturnCorridorsStatement] at corridors
          obtain ⟨_componentwise, partition, _cardinality⟩ := corridors
          have corridorExists : ∀ epsilon : ColdEligibleHalfEdge data object,
              ∃ (component : Finset object.Vertex)
                (corridor : Graph.ColdCorridor.Corridor object windows component),
                Graph.ColdCorridor.IsOutsideComponent object windows component ∧
                  corridor.entryStub = (epsilon.1.2, epsilon.1.1) := by
            intro epsilon
            let selectedEpsilon : Selected := ⟨epsilon.1, epsilon.property.1⟩
            rcases partition selectedEpsilon with outside | crossWindow
            · obtain ⟨_outsideFoot, component, corridor, outsideComponent,
                  entry⟩ := outside
              exact ⟨component, corridor, outsideComponent, entry⟩
            · exact (epsilon.property.2 crossWindow).elim
          let componentAt : ColdEligibleHalfEdge data object → Finset object.Vertex :=
            fun epsilon => Classical.choose (corridorExists epsilon)
          let corridorAt : (epsilon : ColdEligibleHalfEdge data object) →
              Graph.ColdCorridor.Corridor object windows (componentAt epsilon) :=
            fun epsilon => Classical.choose (Classical.choose_spec
              (corridorExists epsilon))
          have corridorFacts : ∀ epsilon : ColdEligibleHalfEdge data object,
              Graph.ColdCorridor.IsOutsideComponent object windows
                  (componentAt epsilon) ∧
                (corridorAt epsilon).entryStub =
                  (epsilon.1.2, epsilon.1.1) := by
            intro epsilon
            exact Classical.choose_spec (Classical.choose_spec
              (corridorExists epsilon))
          let entryWindowAt : ColdEligibleHalfEdge data object →
              Finset object.Vertex := fun epsilon =>
            Classical.choose
              ((Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                (Graph.ColdCorridor.selected_facts object cubic
                  (⟨epsilon.1, epsilon.2.1⟩ :
                    ColdSelectedHalfEdge data object)).1)
          let successorWindowAt : (epsilon : ColdEligibleHalfEdge data object) →
              Finset object.Vertex := fun epsilon => by
            have boundaryMember : (corridorAt epsilon).successorStub ∈
                Graph.ColdCorridor.boundaryStubs object windows
                  (componentAt epsilon) := List.get_mem _ _
            have inWindows : (corridorAt epsilon).successorStub.2 ∈ windows :=
              ((Graph.ColdCorridor.mem_boundaryStubs_iff object windows
                (componentAt epsilon) _).1 boundaryMember).2.1
            exact Classical.choose
              ((Graph.ColdCorridor.mem_windowsOf object packing
                (corridorAt epsilon).successorStub.2).1 inWindows)
          let activeAt := fun (epsilon : ColdEligibleHalfEdge data object)
              (segment : (corridorAt epsilon).Segment) =>
            entryWindowAt epsilon ∪ successorWindowAt epsilon ∪
              ({(corridorAt epsilon).entryStub.1,
                (corridorAt epsilon).head segment} : Finset object.Vertex)
          let offsetAt : object.Vertex → Fin data.coldSignature.windowOrder :=
            fun vertex => by
              by_cases contained : ∃ window ∈ packing, vertex ∈ window
              · let window := Classical.choose contained
                have windowFacts := Classical.choose_spec contained
                have windowMember : window ∈ packing := windowFacts.1
                have vertexMember : vertex ∈ window := windowFacts.2
                have induced := packingWindow window windowMember
                letI : FinEnum (object.induce window).Vertex :=
                  (object.induce window).vertices
                let embedding := Classical.choice induced.1
                have cardInduced :
                    Fintype.card (object.induce window).Vertex = window.card := by
                  simpa [FiniteObject.vertexCount,
                    FinEnum.card_eq_fintypeCard] using
                    object.vertexCount_induce window
                have embeddingSurjective : Function.Surjective embedding := by
                  exact ((Fintype.bijective_iff_injective_and_card embedding).2
                    ⟨embedding.injective, by
                      rw [Fintype.card_fin, cardInduced, induced.2]⟩).2
                exact Classical.choose (embeddingSurjective ⟨vertex, vertexMember⟩)
              · exact
                  ⟨(FinEnum.equiv vertex).1 % data.coldSignature.windowOrder,
                    Nat.mod_lt _ data.coldSignature.windowOrder_pos⟩
          let supportOn := fun (activeSet : Finset object.Vertex)
              (_clause : data.coldSignature.Clause)
              (generator : Graph.ColdCorridor.Coordinate
                (Graph.ColdCorridor.interfaceWidth data.windowOrder)) => by
            let active := activeSet.toList
            let valid := generator.support.filter fun position =>
              position.1 < active.length
            exact valid.attach.image fun position => by
              have member := position.property
              change position.1 ∈ generator.support.filter
                (fun slot => slot.1 < active.length) at member
              exact active.get ⟨position.1.1,
                (Finset.mem_filter.1 member).2⟩
          let valueOn : (activeSet : Finset object.Vertex) →
              (clause : data.coldSignature.Clause) →
              (generator : data.coldSignature.Generator clause) →
              data.coldSignature.Value clause generator :=
            fun activeSet clause generator => by
            let width := Graph.ColdCorridor.interfaceWidth data.windowOrder
            let active := activeSet.toList
            let activePositions : Finset (Fin width) :=
              Finset.univ.filter fun position => position.1 < active.length
            let supportPositions : Finset (Fin width) :=
              generator.support.filter fun position => position.1 < active.length
            let incidences : Finset (Fin width × Fin width) :=
              (generator.support.product activePositions).filter fun incidence =>
                if leftBound : incidence.1.1 < active.length then
                  if rightBound : incidence.2.1 < active.length then
                    object.graph.Adj
                      (active.get ⟨incidence.1.1, leftBound⟩)
                      (active.get ⟨incidence.2.1, rightBound⟩)
                  else False
                else False
            let labelNeighbors : Finset (Fin width) :=
              activePositions.filter fun position =>
                if labelBound : generator.anchor.1 < active.length then
                  if positionBound : position.1 < active.length then
                    object.graph.Adj
                      (active.get ⟨generator.anchor.1, labelBound⟩)
                      (active.get ⟨position.1, positionBound⟩)
                  else False
                else False
            have labelDegreeBound : labelNeighbors.card ≤ width := by
              calc
                labelNeighbors.card ≤ activePositions.card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
                _ ≤ (Finset.univ : Finset (Fin width)).card :=
                  Finset.card_le_card (Finset.subset_univ _)
                _ = width := Fintype.card_fin width
            change Graph.ColdCorridor.EmbeddedCoordinateValue width clause generator
            exact (supportPositions, incidences,
              ⟨labelNeighbors.card, Nat.lt_succ_of_le labelDegreeBound⟩)
          let supportAt := fun (epsilon : ColdEligibleHalfEdge data object)
              (segment : (corridorAt epsilon).Segment) =>
            supportOn (activeAt epsilon segment)
          let valueAt : (epsilon : ColdEligibleHalfEdge data object) →
              (corridorAt epsilon).Segment →
              (clause : data.coldSignature.Clause) →
              (generator : data.coldSignature.Generator clause) →
              data.coldSignature.Value clause generator :=
            fun epsilon segment => valueOn (activeAt epsilon segment)
          let presentationAt : ColdEligibleHalfEdge data object →
              Graph.ColdCorridor.Presentation data.coldSignature object :=
            fun epsilon => (corridorAt epsilon).presentation data.coldSignature
              (activeAt epsilon) offsetAt (supportAt epsilon) (valueAt epsilon)
          let indexAt : (epsilon : ColdEligibleHalfEdge data object) →
              (corridorAt epsilon).Segment → (presentationAt epsilon).Segment :=
            fun _epsilon segment => ULift.up segment
          let makeGerm : (support : Finset object.Vertex) →
              support.card ≤ Graph.ColdCorridor.exchangeBound data.coldSignature →
              Graph.SupportComponents.Connected.ConnectedOn object support →
              (∃ vertex, vertex ∉ support) →
              Graph.ColdCorridor.Record data.coldSignature →
              Graph.ColdCorridor.BoundedGerm data.coldSignature
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object :=
            fun support bounded connected proper record => by
              let atom := Graph.ColdCorridor.rowAtom object support connected proper
              let reading : Graph.CanonicalPiece atom.interface → Prop :=
                fun candidate =>
                  candidate.toPiece.boundaryDegreeProfile =
                      atom.piece.boundaryDegreeProfile ∧
                    ∀ outside : Graph.OutsideContext atom.interface,
                      Graph.MinimumDegreeAtLeast data.threshold
                          (Graph.glue atom.piece outside) →
                        Graph.MinimumDegreeAtLeast data.threshold
                          (Graph.glue candidate.toPiece outside)
              have sourceReading : reading atom.piece.toCanonical := by
                refine ⟨?_, ?_⟩
                · rw [Graph.BoundaryPiece.toCanonical_toPiece]
                  exact atom.piece.transport_boundaryDegreeProfile _
                · intro outside sourceBaseline
                  exact
                    ((Graph.minimumDegreeAtLeast_isomorphismInvariant
                      data.threshold).iff_of_iso
                        (atom.piece.toCanonical_glue_isomorphic outside)).2
                      sourceBaseline
              have realizable : ∃ candidate, reading candidate :=
                ⟨atom.piece.toCanonical, sourceReading⟩
              let selected :=
                Graph.CanonicalPiece.canonicalRepresentative reading realizable
              have selectedReading : reading selected :=
                Graph.CanonicalPiece.canonicalRepresentative_reading reading
                  realizable
              have pieceSizeLe : atom.piece.internalVertexCount ≤ support.card := by
                let embedding : atom.piece.Internal →
                    {vertex // vertex ∈ support} :=
                  fun vertex => ⟨vertex.1, vertex.2.1⟩
                have injective : Function.Injective embedding := by
                  intro left right same
                  apply Subtype.ext
                  exact congrArg
                    (fun vertex : {vertex // vertex ∈ support} => vertex.1) same
                letI : FinEnum atom.piece.Internal := atom.piece.internalVertices
                letI : Fintype atom.piece.Internal :=
                  @FinEnum.instFintype atom.piece.Internal
                    atom.piece.internalVertices
                have cardBound := Fintype.card_le_of_injective embedding injective
                change @FinEnum.card atom.piece.Internal
                    atom.piece.internalVertices ≤ support.card
                rw [FinEnum.card_eq_fintypeCard]
                simpa using cardBound
              have selectedBound : selected.toPiece.internalVertexCount ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature := by
                calc
                  selected.toPiece.internalVertexCount = selected.size := by simp
                  _ ≤ atom.piece.toCanonical.size :=
                    Graph.CanonicalPiece.canonicalRepresentative_size_le
                      reading realizable sourceReading
                  _ = atom.piece.internalVertexCount := rfl
                  _ ≤ support.card := pieceSizeLe
                  _ ≤ Graph.ColdCorridor.exchangeBound data.coldSignature := bounded
              have sourceBaseline :
                  Graph.MinimumDegreeAtLeast data.threshold
                    (Graph.glue atom.piece atom.outside) :=
                ((Graph.minimumDegreeAtLeast_isomorphismInvariant
                  data.threshold).iff_of_iso ⟨atom.reconstructionIso⟩).mpr
                    inputs.current.baseline
              exact
                { support := support
                  bounded := bounded
                  connected := connected
                  proper := proper
                  canonical := selected.toPiece
                  canonicalBounded := selectedBound
                  sameProfile := selectedReading.1
                  baseline := selectedReading.2 atom.outside sourceBaseline
                  record := record }
          have germExists : ∀ epsilon : ColdEligibleHalfEdge data object,
              ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object,
                (corridorAt epsilon).FirstFailureGermWitness
                  (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
                  (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                  (presentationAt epsilon) (indexAt epsilon) germ := by
            intro epsilon
            let corridor := corridorAt epsilon
            let presentation := presentationAt epsilon
            let index := indexAt epsilon
            rcases corridor.exists_firstFailure presentation index
                ULift.up_injective with terminal | repeated
            · let support := corridor.prefixSupport corridor.statesRead
              let terminalSegment : corridor.Segment :=
                ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
              let record := corridor.recordAt presentation index terminalSegment
              have supportBound : support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature := by
                have supportCard :=
                  corridor.prefixSupport_card_le corridor.statesRead
                have terminalBound : corridor.statesRead ≤
                    Graph.ColdCorridor.stateBound data.coldSignature := terminal
                have budgetPositive : 1 ≤
                    Graph.ColdCorridor.interfaceBudget data.coldSignature := by
                  unfold Graph.ColdCorridor.interfaceBudget
                  omega
                change support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature
                dsimp [support]
                unfold Graph.ColdCorridor.exchangeBound
                omega
              let germ := makeGerm support supportBound
                (corridor.prefixSupport_connectedOn corridor.statesRead)
                (corridor.prefixSupport_proper (corridorFacts epsilon).1
                  corridor.statesRead) record
              refine ⟨germ, supportBound, ?_, Or.inl ⟨terminal, rfl, ?_⟩⟩
              · intro vertex member
                exact corridor.prefixSupport_subset_inside
                  corridor.statesRead vertex member
              · rfl
            · obtain ⟨left, right, rightBound, before, same, first⟩ := repeated
              let support := corridor.intervalSupport left right
              let record := corridor.recordAt presentation index left
              have supportBound : support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature := by
                have supportCard := corridor.intervalSupport_card_le left right
                have budgetPositive : 1 ≤
                    Graph.ColdCorridor.interfaceBudget data.coldSignature := by
                  unfold Graph.ColdCorridor.interfaceBudget
                  omega
                change support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature
                dsimp [support]
                unfold Graph.ColdCorridor.exchangeBound
                omega
              let germ := makeGerm support supportBound
                (corridor.intervalSupport_connectedOn left right)
                (corridor.intervalSupport_proper (corridorFacts epsilon).1
                  left right) record
              have recordSame : corridor.recordAt presentation index left =
                  corridor.recordAt presentation index right := by
                unfold Graph.ColdCorridor.Corridor.recordAt
                have boundaryDegrees :
                    presentation.boundaryDegrees (index left) =
                      presentation.boundaryDegrees (index right) := by
                  simpa only [Graph.ColdCorridor.Presentation.state] using
                    congrArg Graph.ColdCorridor.CutState.boundaryDegrees same
                have halfEdges : presentation.halfEdges (index left) =
                    presentation.halfEdges (index right) := by
                  simpa only [Graph.ColdCorridor.Presentation.state] using
                    congrArg Graph.ColdCorridor.CutState.halfEdges same
                have offsets : presentation.offsets (index left) =
                    presentation.offsets (index right) := by
                  simpa only [Graph.ColdCorridor.Presentation.state] using
                    congrArg Graph.ColdCorridor.CutState.offsets same
                rw [boundaryDegrees, halfEdges, offsets, same]
              refine ⟨germ, supportBound, ?_, Or.inr
                ⟨left, right, rightBound, before, same,
                  presentation.reading_eq_of_state_eq same, first, rfl, rfl,
                    recordSame⟩⟩
              · intro vertex member
                exact corridor.intervalSupport_subset_inside left right vertex member
          let outsideIncidence := fun epsilon =>
            Classical.choose (germExists epsilon)
          have crossGermExists : ∀ epsilon : ColdCrossWindowHalfEdge data object,
              ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object,
                germ.support = {epsilon.1.1, epsilon.1.2} := by
            intro epsilon
            let selectedEpsilon : Selected := ⟨epsilon.1, epsilon.property.1⟩
            have selectedFacts :=
              Graph.ColdCorridor.selected_facts object cubic selectedEpsilon
            obtain ⟨sourceWindow, sourceWindowMem, sourceMem⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                selectedFacts.1
            obtain ⟨targetWindow, targetWindowMem, targetMem⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object packing epsilon.1.2).1
                epsilon.property.2
            let support : Finset object.Vertex := {epsilon.1.1, epsilon.1.2}
            have adjacent : object.graph.Adj epsilon.1.1 epsilon.1.2 := by
              simpa only [selectedEpsilon] using selectedFacts.2
            have connected :
                Graph.SupportComponents.Connected.ConnectedOn object support := by
              refine ⟨⟨epsilon.1.1, by simp [support]⟩, ?_⟩
              intro left right leftMem rightMem
              simp only [support, Finset.mem_insert, Finset.mem_singleton] at leftMem rightMem
              rcases leftMem with rfl | rfl <;> rcases rightMem with rfl | rfl
              · exact ⟨SimpleGraph.Walk.nil, by simp, by simp [support]⟩
              · have isPath : (SimpleGraph.Walk.cons adjacent
                    SimpleGraph.Walk.nil).IsPath :=
                  (SimpleGraph.Walk.cons_isPath_iff adjacent
                    SimpleGraph.Walk.nil).2 ⟨by simp, by simpa using adjacent.ne⟩
                refine ⟨SimpleGraph.Walk.cons adjacent
                    SimpleGraph.Walk.nil, isPath, ?_⟩
                simp [support]
              · have isPath : (SimpleGraph.Walk.cons adjacent.symm
                    SimpleGraph.Walk.nil).IsPath :=
                  (SimpleGraph.Walk.cons_isPath_iff adjacent.symm
                    SimpleGraph.Walk.nil).2 ⟨by simp, by simpa using adjacent.symm.ne⟩
                refine ⟨SimpleGraph.Walk.cons adjacent.symm
                    SimpleGraph.Walk.nil, isPath, ?_⟩
                simp [support]
              · exact ⟨SimpleGraph.Walk.nil, by simp, by simp [support]⟩
            have proper : ∃ vertex, vertex ∉ support := by
              have sourceCard : sourceWindow.card = data.windowOrder :=
                (cubicWindow sourceWindow sourceWindowMem).2
              have supportCard : support.card ≤ 2 := by
                exact (Finset.card_insert_le _ _).trans
                  (Nat.succ_le_succ (Finset.card_singleton _).le)
              have notContained : ¬ sourceWindow ⊆ support := by
                intro contained
                have cardBound := Finset.card_le_card contained
                have orderBound := data.five_le_windowOrder
                omega
              obtain ⟨vertex, _sourceMem, notSupport⟩ :=
                Finset.not_subset.mp notContained
              exact ⟨vertex, notSupport⟩
            have bounded : support.card ≤
                Graph.ColdCorridor.exchangeBound data.coldSignature := by
              have supportCard : support.card ≤ 2 := by
                exact (Finset.card_insert_le _ _).trans
                  (Nat.succ_le_succ (Finset.card_singleton _).le)
              unfold Graph.ColdCorridor.exchangeBound
                Graph.ColdCorridor.interfaceBudget
              omega
            let endpointAt : Fin 2 → object.Vertex := fun position =>
              if position = 0 then epsilon.1.1 else epsilon.1.2
            let reverseEndpointAt : Fin 2 → object.Vertex := fun position =>
              if position = 0 then epsilon.1.2 else epsilon.1.1
            let boundedDegree : Fin 2 →
                Fin (data.coldSignature.degreeBound + 1) := fun position =>
              ⟨min (object.degree (endpointAt position))
                  data.coldSignature.degreeBound,
                Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
            let halfEdgeCode : Fin 2 →
                Fin (data.coldSignature.degreeBound + 1) := fun position =>
              ⟨min ((FinEnum.equiv
                    (endpointAt position, reverseEndpointAt position)).1)
                  data.coldSignature.degreeBound,
                Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
            let directState : Graph.ColdCorridor.CutState data.coldSignature :=
              { boundaryDegrees := boundedDegree
                halfEdges := halfEdgeCode
                offsets := fun position => offsetAt (endpointAt position)
                declared := fun clause generator =>
                  some (valueOn support clause generator) }
            let record : Graph.ColdCorridor.Record data.coldSignature :=
              { boundaryDegrees := boundedDegree
                stubs := halfEdgeCode
                offsets := fun position => offsetAt (endpointAt position)
                state := directState
                truth := false }
            let germ := makeGerm support bounded connected proper record
            exact ⟨germ, rfl⟩
          let crossIncidence := fun epsilon =>
            Classical.choose (crossGermExists epsilon)
          have componentInR : ∀ epsilon : ColdEligibleHalfEdge data object,
              componentAt epsilon ⊆ object.remainderSupport packing := by
            intro epsilon vertex vertexMember
            apply Finset.mem_sdiff.2
            refine ⟨Finset.mem_univ vertex, ?_⟩
            have outsideWindows : vertex ∉ windows :=
              Finset.disjoint_left.1 (corridorFacts epsilon).1.1
                vertexMember
            intro inPackedSupport
            apply outsideWindows
            exact inPackedSupport
          refine ⟨outsideIncidence, componentAt, corridorAt, presentationAt, indexAt,
            ?_, ?_, ?_, componentInR, ?_, crossIncidence, ?_⟩
          · intro epsilon
            refine ⟨(corridorFacts epsilon).1, (corridorFacts epsilon).2,
              ULift.up_injective, Classical.choose_spec (germExists epsilon)⟩
          · intro epsilon segment
            change (activeAt epsilon segment).card ≤
              Graph.ColdCorridor.interfaceWidth data.windowOrder
            have entryFacts := Classical.choose_spec
              ((Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                (Graph.ColdCorridor.selected_facts object cubic
                  (⟨epsilon.1, epsilon.2.1⟩ :
                    ColdSelectedHalfEdge data object)).1)
            have entryCard : (entryWindowAt epsilon).card = data.windowOrder :=
              (cubicWindow (entryWindowAt epsilon) entryFacts.1).2
            have boundaryMember : (corridorAt epsilon).successorStub ∈
                Graph.ColdCorridor.boundaryStubs object windows
                  (componentAt epsilon) := List.get_mem _ _
            have successorInside : (corridorAt epsilon).successorStub.2 ∈ windows :=
              ((Graph.ColdCorridor.mem_boundaryStubs_iff object windows
                (componentAt epsilon) _).1 boundaryMember).2.1
            have successorFacts := Classical.choose_spec
              ((Graph.ColdCorridor.mem_windowsOf object packing
                (corridorAt epsilon).successorStub.2).1 successorInside)
            have successorCard : (successorWindowAt epsilon).card =
                data.windowOrder :=
              (packingWindow (successorWindowAt epsilon) successorFacts.1).2
            have pairCard :
                ({(corridorAt epsilon).entryStub.1,
                  (corridorAt epsilon).head segment} :
                    Finset object.Vertex).card ≤ 2 := by
              exact (Finset.card_insert_le _ _).trans
                (Nat.succ_le_succ (Finset.card_singleton _).le)
            calc
              (activeAt epsilon segment).card ≤
                  (entryWindowAt epsilon ∪ successorWindowAt epsilon).card +
                    ({(corridorAt epsilon).entryStub.1,
                      (corridorAt epsilon).head segment} :
                        Finset object.Vertex).card := by
                simpa [activeAt] using
                  (Finset.card_union_le
                    (entryWindowAt epsilon ∪ successorWindowAt epsilon)
                    ({(corridorAt epsilon).entryStub.1,
                      (corridorAt epsilon).head segment} :
                        Finset object.Vertex))
              _ ≤ ((entryWindowAt epsilon).card +
                    (successorWindowAt epsilon).card) + 2 :=
                Nat.add_le_add
                  (Finset.card_union_le (entryWindowAt epsilon)
                    (successorWindowAt epsilon)) pairCard
              _ ≤ Graph.ColdCorridor.interfaceWidth data.windowOrder := by
                rw [entryCard, successorCard]
                unfold Graph.ColdCorridor.interfaceWidth
                omega
          · intro epsilon crossWindow
            obtain ⟨sourceWindow, sourceMember, sourceInside⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                (Graph.ColdCorridor.selected_facts object cubic epsilon).1
            obtain ⟨targetWindow, targetMember, targetInside⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object packing epsilon.1.2).1
                crossWindow
            exact ⟨sourceWindow, sourceMember, targetWindow, targetMember,
              sourceInside, targetInside,
              (Graph.ColdCorridor.selected_facts object cubic epsilon).2⟩
          · intro epsilon vertex vertexMember
            apply componentInR epsilon
            obtain ⟨inner, _innerMember, rfl⟩ := List.mem_map.1 vertexMember
            exact inner.2
          · intro epsilon
            exact Classical.choose_spec (crossGermExists epsilon)
      .cons (key := K .coldCorridorState) ⟨state⟩ .nil)

/-- Node `[153]`: select the first event in the manuscript's ordered
(F1)--(F5) list for every retained cold corridor. -/
@[reducible] noncomputable def coldFirstFailureOccurrenceRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureOccurrence
    { Requires := [K .coldCorridorState, K .coldDeclaredHandoffLedger]
      Produces := [K .coldFirstFailureOccurrence]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let state := (inputs.get (K .coldCorridorState)).down
      let handoffLedger := (inputs.get (K .coldDeclaredHandoffLedger)).down
      let Handoff : Finset inputs.current.object.Vertex → Prop :=
        Classical.choose handoffLedger
      let handoffAbsent := Classical.choose_spec handoffLedger
      let occurrence : ColdFirstFailureOccurrenceStatement data
          inputs.current.object := by
        classical
        let object := inputs.current.object
        letI : FinEnum object.Vertex := object.vertices
        refine ⟨⟨Handoff, handoffAbsent, state, ?_⟩⟩
        intro Eligible incidence stateOne componentAt stateTwo corridorAt stateTail
          presentationAt indexAt epsilon
        let indexTail := Classical.choose_spec stateTail
        let stateFacts := (Classical.choose_spec indexTail).1
        let germ := incidence epsilon
        let corridor := corridorAt epsilon
        let presentation := presentationAt epsilon
        let index := indexAt epsilon
        let packing := canonicalWindowPacking data object
        let cycleAt : corridor.Segment → Prop := fun segment =>
          ∃ windowSupport ∈ packing,
            ∃ window : Graph.ColdCorridor.Window object data.windowOrder,
              (∀ vertex, vertex ∈ windowSupport ↔
                ∃ position, window.place position = vertex) ∧
              corridor.FirstFailureCycle window data.LengthOK segment
        let defectAt : corridor.Segment → Prop := fun segment =>
          ∃ left : corridor.Segment,
            left.1 < segment.1 ∧
              Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation
                index (Graph.HasCycleWithLength data.LengthOK)
                (fun stage => corridor.prefixSupport stage.1) left segment
        let compressionAt : corridor.Segment → Prop := fun segment =>
          ∃ failure : Graph.ColdCorridor.Corridor.FirstFailureCompression corridor
              presentation index (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK)
              (fun stage => corridor.prefixSupport stage.1),
            failure.stage = segment
        let handoffAt : corridor.Segment → Prop := fun segment =>
          Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff segment
        let germAt : corridor.Segment → Prop := fun segment =>
          (corridor.TerminalCorridor data.coldSignature ∧
            germ.support = corridor.prefixSupport corridor.statesRead ∧
            (let terminal : corridor.Segment :=
              ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
             germ.record = corridor.recordAt presentation index terminal) ∧
            segment.1 = corridor.inside.1.length) ∨
          ∃ left right : corridor.Segment,
            right.1 ≤ Graph.ColdCorridor.stateBound data.coldSignature ∧
            left.1 < right.1 ∧
            presentation.state (index left) = presentation.state (index right) ∧
            (∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
              presentation.support (index left) coordinate ⊆
                  ↑(presentation.activeInterface (index left)) →
                presentation.reading (index left) coordinate =
                  presentation.reading (index right) coordinate) ∧
            (∀ earlierLeft earlierRight : corridor.Segment,
              earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
                presentation.state (index earlierLeft) ≠
                  presentation.state (index earlierRight)) ∧
            germ.support = corridor.intervalSupport left right ∧
            germ.record = corridor.recordAt presentation index left ∧
            germ.record = corridor.recordAt presentation index right ∧
            segment = right
        let failureAt : corridor.Segment → Prop := fun segment =>
          ColdFirstFailureEvent data object corridor presentation index germ
            Handoff segment
        change ∃ first : corridor.Segment,
          failureAt first ∧
            ∀ earlier : corridor.Segment, earlier.1 < first.1 →
              ¬ failureAt earlier
        have germWitness : corridor.FirstFailureGermWitness
            (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
            (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
            presentation index germ :=
          (stateFacts epsilon).2.2.2
        have germEvent : ∃ segment : corridor.Segment, germAt segment := by
          rcases germWitness.2.2 with terminal | repeated
          · let segment : corridor.Segment :=
              ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
            exact ⟨segment, Or.inl
              ⟨terminal.1, terminal.2.1, terminal.2.2, rfl⟩⟩
          · obtain ⟨left, right, rightBound, before, same, readings, first,
              supportEq, leftRecord, rightRecord⟩ := repeated
            exact ⟨right, Or.inr
              ⟨left, right, rightBound, before, same, readings, first,
                supportEq, leftRecord, rightRecord, rfl⟩⟩
        let failures : Finset corridor.Segment :=
          Finset.univ.filter failureAt
        have failuresNonempty : failures.Nonempty := by
          obtain ⟨segment, event⟩ := germEvent
          exact ⟨segment, Finset.mem_filter.2 ⟨Finset.mem_univ _,
            .germ event⟩⟩
        let first := failures.min' failuresNonempty
        have firstMember : first ∈ failures :=
          Finset.min'_mem failures failuresNonempty
        refine ⟨first, (Finset.mem_filter.1 firstMember).2, ?_⟩
        intro earlier earlierBefore earlierFailure
        have earlierMember : earlier ∈ failures :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, earlierFailure⟩
        have firstLeEarlier := Finset.min'_le failures earlier earlierMember
        exact (Nat.not_lt_of_ge firstLeEarlier) earlierBefore
      .cons (key := K .coldFirstFailureOccurrence) ⟨occurrence⟩ .nil)

/-- The concrete sparse-exit route supplied by (F2). -/
theorem coldFailureDefectRoutes
    (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectRoutesStatement data object := by
      intro windows component corridor presentation index left right
      intro failure
      classical
      let support := corridor.prefixSupport right.1
      let reduced :=
        Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece
          object support (corridor.prefixSupport left.1)
      let full :=
        Graph.Strategy.InterfaceReplacement.SupportAtom.piece object support
      let family : Finset (ULift.{u} (Fin 2)) := Finset.univ
      let coordinateSupport : ULift.{u} (Fin 2) →
          Finset object.Vertex := fun _ => ∅
      let attempt : Graph.AttemptedQuotient
          (Coordinate := ULift.{u} (Fin 2))
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK)
          object family coordinateSupport :=
        { support := support
          connected := corridor.prefixSupport_connectedOn right.1
          carries := by
            intro coordinate member vertex vertexMember
            simp [coordinateSupport] at vertexMember
          Label := ULift.{u + 1} Unit
          Value := ULift.{u + 1} Unit
          label := fun _ => ULift.up ()
          value := fun _ _ => ULift.up ()
          properRepresentative := by
            intro _proper _reducing complete
            exfalso
            obtain ⟨outside, separates⟩ := failure.2
            apply separates
            exact (complete reduced full
              (by intro coordinate member; rfl)).2 outside
          closedRepresentative := by
            intro _closed _reducing complete
            exfalso
            obtain ⟨outside, separates⟩ := failure.2
            apply separates
            exact (complete reduced full
              (by intro coordinate member; rfl)).2 outside }
      have reducing : ¬ Set.InjOn attempt.label ↑family := by
        intro injective
        have equal : ULift.up (0 : Fin 2) = ULift.up 1 :=
          injective (by simp [family]) (by simp [family]) rfl
        have downEqual : (0 : Fin 2) = 1 := congrArg ULift.down equal
        omega
      have identified : attempt.Identifies reduced full := by
        intro coordinate member
        rfl
      exact .targetDefect family coordinateSupport attempt reducing
        reduced full identified failure.2

/-- The F2-free context-equivalence conclusion on the same two prefixes. -/
theorem coldFailureDefectEquivalent
    (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectEquivalentStatement data object := by
      intro windows component corridor presentation index left right
        excluded same
      classical
      intro outside
      by_contra distinguishes
      exact excluded ⟨same, ⟨outside, distinguishes⟩⟩

/-- The complete local content of (F2), assembled from the two sealed fields
before it is packaged in the dependent exact-ledger output. -/
theorem coldFailureDefectFact
    (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectStatement data object :=
  { routes := coldFailureDefectRoutes data object
    equivalent := coldFailureDefectEquivalent data object }

set_option maxHeartbeats 1600000 in
/-- Node `[153]`, (F2): register the concrete sparse-exit route and the
F2-free context equivalence on the current object. -/
@[reducible] noncomputable def coldFailureDefectRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
    { Requires := []
      Produces := [K .coldFailureDefect, K .coldFailureDefectRoute]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let failureDefect := coldFailureDefectFact data inputs.current.object
      .cons (key := K .coldFailureDefect) ⟨failureDefect⟩
        (.cons (key := K .coldFailureDefectRoute)
          ⟨coldFailureDefectRoutes data inputs.current.object⟩ .nil))


/-- Node `[153]`, (F1): the selected residual contains no target cycle. -/
@[reducible] noncomputable def coldFailureCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCycle
    { Requires := [K .selection]
      Produces := [K .coldFailureCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      .cons (key := K .coldFailureCycle)
        ⟨by
          intro windows component corridor order window segment failure
          exact selected.1
            (Graph.ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle
              failure)⟩
        .nil)

/-- Node `[153]`, (F3): uncompressibility excludes a smaller proper
representative on the current residual. -/
@[reducible] noncomputable def coldFailureCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
    { Requires := [K .uncompressible]
      Produces := [K .coldFailureCompression]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .coldFailureCompression)
        ⟨by
          intro windows component corridor presentation index support
          exact Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
            uncompressible⟩
        .nil)

/-- Node `[153]`, (F4): a declared Type-B/route-8 support is returned to
the already-declared handoff ledger. -/
@[reducible] noncomputable def coldFailureHandoffRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureHandoff
    { Requires := []
      Produces := [K .coldFailureHandoff]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _inputs =>
      .cons (key := K .coldFailureHandoff)
        ⟨by
          intro windows component corridor Handoff segment failure
          exact Graph.ColdCorridor.Corridor.handoff_mem failure⟩
        .nil)

/-- The least high-degree segment of a non-subcubic retained prefix. -/
theorem coldFirstHighOfNotBounded
    {object : Graph.FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (n threshold : Nat)
    (notBounded : ¬ ∀ vertex ∈ corridor.prefixSupport n,
      object.degree vertex ≤ threshold) :
    ∃ first : corridor.Segment,
      first.1 ≤ n ∧ threshold < object.degree (corridor.head first) ∧
        ∀ earlier : corridor.Segment, earlier.1 < first.1 →
          object.degree (corridor.head earlier) ≤ threshold := by
  classical
  push Not at notBounded
  obtain ⟨vertex, vertexMember, vertexHigh⟩ := notBounded
  obtain ⟨inner, innerMember, innerEq⟩ :=
    (corridor.mem_prefixSupport n vertex).1 vertexMember
  obtain ⟨segmentIndex, indexEq, _indexBound⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMember
  have segmentBound : segmentIndex ≤ n := by
    have takeLength := SimpleGraph.Walk.take_length corridor.inside.1 n
    omega
  have segmentIndexLt : segmentIndex < corridor.inside.1.length + 1 := by
    have takeLength := SimpleGraph.Walk.take_length corridor.inside.1 n
    have lengthBound : (corridor.inside.1.take n).length ≤
        corridor.inside.1.length := by omega
    omega
  let segment : corridor.Segment := ⟨segmentIndex, segmentIndexLt⟩
  have headEq : corridor.head segment = vertex := by
    have takeEq : (corridor.inside.1.take n).getVert segmentIndex =
        corridor.inside.1.getVert segmentIndex := by
      rw [SimpleGraph.Walk.take_getVert]
      simp [Nat.min_eq_right segmentBound]
    exact congrArg Subtype.val (takeEq.symm.trans indexEq) |>.trans innerEq
  let highSegments : Finset corridor.Segment :=
    Finset.univ.filter fun current =>
      current.1 ≤ n ∧ threshold < object.degree (corridor.head current)
  have highNonempty : highSegments.Nonempty := by
    refine ⟨segment, Finset.mem_filter.2
      ⟨Finset.mem_univ _, segmentBound, ?_⟩⟩
    simpa [headEq] using vertexHigh
  let first := highSegments.min' highNonempty
  have firstMember : first ∈ highSegments :=
    Finset.min'_mem highSegments highNonempty
  have firstFacts := (Finset.mem_filter.1 firstMember).2
  refine ⟨first, firstFacts.1, firstFacts.2, ?_⟩
  intro earlier earlierBefore
  apply le_of_not_gt
  intro earlierHigh
  have earlierMember : earlier ∈ highSegments :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _,
      le_trans (Nat.le_of_lt earlierBefore) firstFacts.1, earlierHigh⟩
  have firstLeEarlier := Finset.min'_le highSegments earlier earlierMember
  exact (Nat.not_lt_of_ge firstLeEarlier) earlierBefore

/-- The first-high handoff conclusion obtained from the retained corridor
state.  This is the manuscript's bounded-prefix/high-degree dichotomy. -/
theorem coldHandoffTransferFact
    {data : Data.{u}} {object : Graph.FiniteObject.{u}}
    (state : ColdCorridorStateStatement data object) :
    ColdFirstHighHandoffStatement data object := by
  classical
  change ColdFirstHighHandoffStatement data object
  simp only [ColdFirstHighHandoffStatement]
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := coldCorridorWindows data object
  intro retained
  have retainedEq : retained = state := Subsingleton.elim _ _
  subst retained
  intro epsilon
  let incidence := Classical.choose state
  let stateOne := Classical.choose_spec state
  let componentAt := Classical.choose stateOne
  let stateTwo := Classical.choose_spec stateOne
  let corridorAt := Classical.choose stateTwo
  let stateTail := Classical.choose_spec stateTwo
  let presentationAt := Classical.choose stateTail
  let indexAt := Classical.choose (Classical.choose_spec stateTail)
  let stateFacts := (Classical.choose_spec
    (Classical.choose_spec stateTail)).1
  let traceEnd := fun routed : ColdEligibleHalfEdge data object =>
    Classical.choose
      (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
        (corridorAt routed) (presentationAt routed) (indexAt routed)
        (incidence routed) (stateFacts routed).2.2.2)
  by_cases subcubic : ∀ vertex ∈
      (corridorAt epsilon).prefixSupport (traceEnd epsilon),
        object.degree vertex ≤ data.threshold
  · exact Or.inl subcubic
  · obtain ⟨first, firstBound, firstHigh, earlierBound⟩ :=
      coldFirstHighOfNotBounded (corridorAt epsilon)
        (traceEnd epsilon) data.threshold subcubic
    refine Or.inr ⟨first, firstBound, firstHigh, earlierBound, ?_⟩
    let corridor := corridorAt epsilon
    have entryWindowFacts := Classical.choose_spec
      ((Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
        (Graph.ColdCorridor.selected_facts object cubic
          (⟨epsilon.1, epsilon.2.1⟩ : ColdSelectedHalfEdge data object)).1)
    have sourceSubcubic : object.degree epsilon.1.1 ≤ data.threshold := by
      exact le_of_eq ((Finset.mem_filter.1 entryWindowFacts.1).2
        epsilon.1.1 entryWindowFacts.2)
    by_cases firstZero : first.1 = 0
    · let root := epsilon.1.1
      have headEq : corridor.head first = epsilon.1.2 := by
        simpa [corridor, corridorAt, Graph.ColdCorridor.Corridor.head,
          Graph.ColdCorridor.Corridor.entryStub,
          Graph.ColdCorridor.stubFoot, firstZero] using
            congrArg Prod.fst (stateFacts epsilon).2.1
      have adjacent : object.graph.Adj (corridor.head first) root := by
        rw [headEq]
        exact (Graph.ColdCorridor.selected_facts object cubic
          (⟨epsilon.1, epsilon.2.1⟩ :
            ColdSelectedHalfEdge data object)).2.symm
      refine ⟨root, adjacent, sourceSubcubic, ?_⟩
      refine (Graph.SubcubicReach.mem_reach object.graph).2
        ⟨SimpleGraph.Walk.nil, by simp, by simp, ?_, ?_⟩
      · simp
      · simp
    · have firstPositive : 0 < first.1 := Nat.pos_of_ne_zero firstZero
      let previous : corridor.Segment := ⟨first.1 - 1, by
        dsimp [corridor]
        omega⟩
      let root := corridor.head previous
      have previousBefore : previous.1 < first.1 := by
        dsimp [previous]
        omega
      have rootSubcubic : object.degree root ≤ data.threshold :=
        earlierBound previous previousBefore
      have adjacent : object.graph.Adj (corridor.head first) root := by
        have step := corridor.inside.1.adj_getVert_succ
          (i := previous.1) (by
            change previous.1 < (corridorAt epsilon).inside.1.length
            have firstLt := first.2
            dsimp [previous]
            omega)
        change object.graph.Adj
          (corridor.inside.1.getVert first.1).1
          (corridor.inside.1.getVert previous.1).1
        have succEq : previous.1 + 1 = first.1 := by
          dsimp [previous]
          omega
        rw [← succEq]
        exact step.symm
      have prefixSubcubic : ∀ vertex ∈
          corridor.prefixSupport previous.1,
            object.degree vertex ≤ data.threshold := by
        intro vertex member
        obtain ⟨inner, innerMember, innerEq⟩ :=
          (corridor.mem_prefixSupport previous.1 vertex).1 member
        obtain ⟨segmentIndex, indexEq, indexBound⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMember
        have segmentLe : segmentIndex ≤ previous.1 := by
          have takeLength := SimpleGraph.Walk.take_length
            corridor.inside.1 previous.1
          omega
        let segment : corridor.Segment :=
          ⟨segmentIndex, by
            have previousLt : previous.1 < corridor.inside.1.length := by
              change previous.1 < (corridorAt epsilon).inside.1.length
              have firstLt := first.2
              dsimp [previous]
              omega
            omega⟩
        have segmentBefore : segment.1 < first.1 :=
          lt_of_le_of_lt segmentLe previousBefore
        have headEq : corridor.head segment = vertex := by
          have takeEq :
              (corridor.inside.1.take previous.1).getVert segmentIndex =
                corridor.inside.1.getVert segmentIndex := by
            rw [SimpleGraph.Walk.take_getVert]
            simp [Nat.min_eq_right segmentLe]
          exact congrArg Subtype.val
            (takeEq.symm.trans indexEq) |>.trans innerEq
        simpa [corridor, headEq] using earlierBound segment segmentBefore
      let short := corridor.inside.1.take previous.1
      let embedding := object.induceEmbedding (componentAt epsilon)
      let backwards := short.reverse.map embedding.toHom
      have shortEnd :
          embedding (corridor.inside.1.getVert previous.1) = root := rfl
      have shortStart : embedding
          (Graph.ColdCorridor.stubFoot object windows
            (componentAt epsilon) corridor.entry) =
            corridor.entryStub.1 := rfl
      let toFoot : object.graph.Walk root corridor.entryStub.1 :=
        backwards.copy shortEnd shortStart
      have entryMember : corridor.entryStub ∈
          Graph.ColdCorridor.boundaryStubs object windows
            (componentAt epsilon) := List.get_mem _ _
      have entryAdjacent : object.graph.Adj corridor.entryStub.1
          corridor.entryStub.2 :=
        ((Graph.ColdCorridor.mem_boundaryStubs_iff object windows
          (componentAt epsilon) corridor.entryStub).1 entryMember).2.2
      let joined : object.graph.Walk root corridor.entryStub.2 :=
        toFoot.concat entryAdjacent
      have sourceEq : corridor.entryStub.2 = epsilon.1.1 :=
        congrArg Prod.snd (stateFacts epsilon).2.1
      let sourceWalk : object.graph.Walk root epsilon.1.1 :=
        joined.copy rfl sourceEq
      let path := sourceWalk.toPath
      refine ⟨root, adjacent, rootSubcubic, ?_⟩
      refine (Graph.SubcubicReach.mem_reach object.graph).2
        ⟨path.1, path.2, ?_, ?_, ?_⟩
      · calc
          path.1.length ≤ sourceWalk.length :=
            sourceWalk.length_bypass_le_length
          _ = short.length + 1 := by
            simp [sourceWalk, joined, toFoot, backwards]
          _ ≤ previous.1 + 1 := by
            simp [short, SimpleGraph.Walk.take_length]
          _ ≤ Graph.ColdCorridor.exchangeBound data.coldSignature + 2 := by
            have stateBound : traceEnd epsilon ≤
                Graph.ColdCorridor.stateBound data.coldSignature := by
              dsimp [traceEnd]
              exact (Classical.choose_spec
                (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
                  (Graph.minimumDegreeAtLeast_isomorphismInvariant
                    data.threshold)
                  (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                  corridor (presentationAt epsilon) (indexAt epsilon)
                  (incidence epsilon) (stateFacts epsilon).2.2.2)).1
            unfold Graph.ColdCorridor.exchangeBound
            dsimp [previous]
            omega
      · intro current currentMember
        have currentSourceWalk : current ∈ sourceWalk.support :=
          SimpleGraph.Walk.support_toPath_subset_support sourceWalk
            (List.mem_of_mem_dropLast currentMember)
        simp only [sourceWalk, SimpleGraph.Walk.support_copy,
          joined, SimpleGraph.Walk.support_concat,
          List.mem_append, List.mem_singleton] at currentSourceWalk
        rcases currentSourceWalk with currentBackwards | currentSource
        · simp only [toFoot, SimpleGraph.Walk.support_copy,
            backwards, SimpleGraph.Walk.support_map,
            SimpleGraph.Walk.support_reverse, List.mem_map]
            at currentBackwards
          obtain ⟨inner, innerMember, innerEq⟩ := currentBackwards
          refine Finset.mem_filter.2 ⟨object.mem_vertexFinset _, ?_⟩
          apply prefixSubcubic current
          exact (corridor.mem_prefixSupport previous.1 current).2
            ⟨inner, by simpa [short] using innerMember, innerEq⟩
        · refine Finset.mem_filter.2 ⟨object.mem_vertexFinset _, ?_⟩
          simpa [currentSource, sourceEq] using sourceSubcubic
      · intro nonnil same
        have firstAdjacent := path.1.adj_getVert_succ
          (i := 0) (by
            simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using nonnil)
        exact firstAdjacent.ne
          (by simpa [SimpleGraph.Walk.getVert_zero, same])

/-! Node `[153]`: eliminate (F1)--(F4) on the literal surviving-cold
residual and retain the manuscript's (F5) conclusion. -/

set_option maxHeartbeats 1600000 in
@[reducible] noncomputable def coldFirstFailureRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureRouting
    { Requires := [K .coldFirstFailureOccurrence, K .coldFailureCycle,
        K .coldFailureDefectRoute,
        K .coldFailureCompression, K .coldFailureHandoff,
        K .sparseSurplusSurvivor]
      Produces := [K .coldFailureRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let occurrence := (inputs.get (K .coldFirstFailureOccurrence)).down
      let failureCycle := (inputs.get (K .coldFailureCycle)).down
      let failureDefectRoute :=
        (inputs.get (K .coldFailureDefectRoute)).down
      let failureCompression := (inputs.get (K .coldFailureCompression)).down
      let failureHandoff := (inputs.get (K .coldFailureHandoff)).down
      let sparseSurvivor := (inputs.get (K .sparseSurplusSurvivor)).down
      let occurrenceData := Classical.choice occurrence
      let surviving : ColdSurvivingFirstFailureStatement data
          inputs.current.object :=
        Classical.choice (show Nonempty
            (ColdSurvivingFirstFailureStatement data inputs.current.object) from
          by
            refine ⟨⟨⟨occurrenceData, ?_⟩⟩⟩
            intro epsilon
            obtain ⟨first, event, minimal⟩ := occurrenceData.occurs epsilon
            cases event with
            | cycle cycle =>
                exact (failureCycle _ _ _ _ _ _
                  (Classical.choose_spec
                    (Classical.choose_spec cycle).2).2).elim
            | defect defect =>
                exact (sparseSurvivor
                  (failureDefectRoute _ _ _ _ _ (Classical.choose defect) first
                    (Classical.choose_spec defect).2)).elim
            | compression compression =>
                exact (failureCompression _ _ _ _ _ _
                  ⟨Classical.choose compression⟩).elim
            | handoff handoff =>
                obtain ⟨support, supportHandoff, _⟩ :=
                  failureHandoff _ _ _ _ _ handoff
                exact (occurrenceData.handoffAbsent support supportHandoff).elim
            | germ germ => exact ⟨⟨first, germ, minimal⟩⟩)
      .cons (key := K .coldFailureRouting)
        ⟨⟨sparseSurvivor, surviving⟩⟩
        .nil)

/-- Node `[153]`: publish the bounded-prefix/first-high handoff conclusion
from the retained corridor state. -/
@[reducible] noncomputable def coldHandoffTransferRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldHandoffTransfer
    { Requires := [K .coldCorridorState]
      Produces := [K .coldHandoffTransfer]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let state := (inputs.get (K .coldCorridorState)).down
      .cons (key := K .coldHandoffTransfer)
        ⟨coldHandoffTransferFact state⟩ .nil)

/-! ## Node `[162]`, `lem:dense-cold-pass`: terminality in the remainder

The corridor producer records that its component and selected path lie in the
normalized remainder of the fixed maximal packing.  This row consumes that
literal state together with node `[27]`'s normalization fact.  The canonical
path is shortest by `FinitePathSelection.selectOfReachable_length_le`; an
induced-`P_windowOrder`-free remainder therefore bounds its length by
`windowOrder - 2`, which is below the registered cold-state bound. -/
@[reducible] noncomputable def denseColdCorridorsTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.denseColdCorridorsTerminal
    { Requires := [K .coldCorridorState, K .remainderNormalized,
        K .hotColdPartition]
      Produces := [K .denseColdCorridorsTerminal]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let state := (inputs.get (K .coldCorridorState)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .denseColdCorridorsTerminal)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change HotColdWindowStatement data object at split
          change ColdCorridorStateStatement data object at state
          obtain ⟨validPacking, _attains, maximal, _hot,
            _coldIff, _disjoint, _cover⟩ := split
          change DenseColdCorridorsTerminalStatement data object
          refine ⟨state, ?_⟩
          let stateOne := Classical.choose_spec state
          let componentAt := Classical.choose stateOne
          let stateTwo := Classical.choose_spec stateOne
          let corridorAt := Classical.choose stateTwo
          let stateTail := Classical.choose_spec stateTwo
          let _presentationAt := Classical.choose stateTail
          let stateBundle := Classical.choose_spec
            (Classical.choose_spec stateTail)
          have componentInR := stateBundle.2.2.2.1
          change ∀ epsilon : ColdEligibleHalfEdge data object,
            Graph.ColdCorridor.Corridor.TerminalCorridor
              (corridorAt epsilon) data.coldSignature
          intro epsilon
          let component := componentAt epsilon
          let corridor := corridorAt epsilon
          have componentFree : Graph.InducedPathFree (object.induce component)
              data.windowOrder :=
            object.inducedPathFree_induce_of_forall
              (fun support inside =>
                (normalized (canonicalWindowPacking data object) validPacking
                  maximal support
                  (inside.trans (componentInR epsilon))).1)
          obtain ⟨shortest, shortestPath, shortestLength⟩ :=
            corridor.connected.exists_path_of_dist
          have shortestBound : shortest.length ≤ data.windowOrder - 2 :=
            Graph.shortestPath_length_le_order_sub_two
              (object.induce component) data.windowOrder
              data.three_le_windowOrder shortest shortestPath shortestLength
              componentFree
          have selectedBound : corridor.inside.1.length ≤ shortest.length := by
            exact corridor.inside_length_le ⟨shortest, shortestPath⟩
          change corridor.statesRead ≤
            Graph.ColdCorridor.stateBound data.coldSignature
          have orderBound :=
            Graph.ColdCorridor.windowOrder_le_stateBound data.coldSignature
          have threeLeOrder := data.three_le_windowOrder
          change corridor.inside.1.length + 1 ≤
            Graph.ColdCorridor.stateBound data.coldSignature
          rw [data.coldSignature_windowOrder] at orderBound
          omega⟩
        .nil)

/-! ## Node `[153]`, `lem:cold-germ-extraction`: exchange bound and extraction

The first-failure cold exchange is bounded by `M_cold` (`exchange_card_le`),
and an occurrence-indexed candidate family with the paper's overlap bound has
a disjoint subfamily of size at least `|𝒢_cand|/D_cold` (greedy independent
set, `coldGermOccurrenceExtractionLocal`).  Positivity belongs to the later
linear arm, not to this finite extraction theorem. -/
@[reducible] noncomputable def coldGermExtractionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermExtraction
    { Requires := [K .coldFailureRouting]
      Produces := [K .coldExchangeBound, K .coldGermExtraction]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let routing := (inputs.get (K .coldFailureRouting)).down
      let exchange : ColdExchangeBoundStatement data inputs.current.object :=
        ⟨routing, fun windows component corridor terminal =>
          corridor.exchange_card_le terminal⟩
      .cons (key := K .coldExchangeBound)
        ⟨exchange⟩
        (.cons (key := K .coldGermExtraction)
          ⟨⟨exchange, Graph.ColdCorridor.coldGermOccurrenceExtractionLocal⟩⟩
          .nil))

/-! ## Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate family

The candidates are exactly the manuscript's complete repaired occurrence
family: outside-corridor F5 prefixes and immediate two-vertex terminal germs
for selected cross-window incidences.  A noncandidate occurrence is charged
at its first high-to-subcubic edge; there is no separate conditional or
unbounded cross-window loss. -/
set_option maxHeartbeats 4000000 in
@[reducible] noncomputable def coldGermCandidatesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermCandidates
    { Requires := [K .coldFailureRouting, K .coldGermExtraction,
        K .coldHandoffTransfer]
      Produces := [K .coldGermCandidates]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routing := (inputs.get (K .coldFailureRouting)).down
      let extraction := (inputs.get (K .coldGermExtraction)).down
      let handoff := (inputs.get (K .coldHandoffTransfer)).down
      .cons (key := K .coldGermCandidates)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          letI : DecidableEq object.Vertex := object.vertices.decEq
          letI : DecidableRel object.graph.Adj := object.decideAdj
          let cold := canonicalColdWindows data object
          let cubic := cold.filter (AmbientCubicWindow data object)
          let windows := coldCorridorWindows data object
          let Eligible := ColdEligibleHalfEdge data object
          let Cross := ColdCrossWindowHalfEdge data object
          let Occurrence := ColdGermOccurrence data object
          let Selected := ColdSelectedHalfEdge data object
          change ColdFailureRoutingStatement data object at routing
          let classified := coldRoutedClassified data object routing
          let classification := Classical.choose_spec routing.surviving.holds
          let state := classified.state
          change ColdCorridorStateStatement data object at state
          let outsideIncidence : Eligible →
              Graph.ColdCorridor.BoundedGerm data.coldSignature
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object :=
            coldOccurrenceIncidence data object classified
          let corridorAt := coldOccurrenceCorridorAt data object classified
          let presentationAt :=
            coldOccurrencePresentationAt data object classified
          let indexAt := coldOccurrenceIndexAt data object classified
          let stateFacts := coldOccurrenceStateFacts data object classified
          let traceEnd := coldRoutedTraceEnd data object routing
          let traceFacts := fun epsilon : Eligible => Classical.choose_spec
            (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
              (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
              (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
              (corridorAt epsilon) (presentationAt epsilon) (indexAt epsilon)
              (outsideIncidence epsilon) (stateFacts epsilon).2.2.2)
          let firstFailureGerm :=
            ColdFirstFailureGermOccurrence data object classified
          let firstFailureHandoff :=
            ColdFirstFailureHandoffOccurrence data object classified
          let stateOne := Classical.choose_spec state
          let stateTwo := Classical.choose_spec (Classical.choose_spec stateOne)
          let stateBundle := Classical.choose_spec (Classical.choose_spec stateTwo)
          let crossIncidence := coldRoutedCrossIncidence data object routing
          let crossFacts := Classical.choose_spec stateBundle.2.2.2.2.2
          let incidence := coldRoutedOccurrenceIncidence data object routing
          let candidates := coldRoutedCandidates data object routing
          have occurrenceStubInjective : Function.Injective
              (@ColdGermOccurrence.stub data object) := by
            intro left right same
            cases left with
            | inl left =>
                cases right with
                | inl right =>
                    exact congrArg Sum.inl (Subtype.ext same)
                | inr right =>
                    exfalso
                    have targetSame := congrArg Prod.snd same
                    exact left.property.2 (targetSame ▸ right.property.2)
            | inr left =>
                cases right with
                | inl right =>
                    exfalso
                    have targetSame := congrArg Prod.snd same
                    exact right.property.2 (targetSame.symm ▸ left.property.2)
                | inr right =>
                    exact congrArg Sum.inr (Subtype.ext same)
          change ColdExchangeBoundStatement data object ∧
            Graph.ColdCorridor.ColdGermOccurrenceExtractionLocal data.coldSignature
              data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object at extraction
          have candidateFamily :
              Graph.ColdCorridor.CandidateGermOccurrenceFamily data.coldSignature
                data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object incidence candidates := by
            apply Graph.ColdCorridor.overlap_card_le_of_vertex_multiplicity
              (support := fun epsilon => (incidence epsilon).support)
              (supportBound := Graph.ColdCorridor.exchangeBound data.coldSignature)
              (multiplicityBound :=
                Graph.ColdCorridor.overlapBound data.threshold data.coldSignature)
            · intro epsilon _epsilonMem
              exact (incidence epsilon).bounded
            · intro vertex
              let through := candidates.filter fun epsilon =>
                vertex ∈ (incidence epsilon).support
              let subcubic := object.vertexFinset.filter fun current =>
                object.degree current ≤ data.threshold
              let reach := @Graph.SubcubicReach.reach object.Vertex
                (@FinEnum.instFintype _ object.vertices) object.graph
                subcubic vertex
                (Graph.ColdCorridor.exchangeBound data.coldSignature + 2) vertex
              let sourceRegion := reach ∩ Graph.ColdCorridor.windowsOf object cubic
              have throughToIncidences : through.card ≤
                  (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
                    pair.1 ∈ sourceRegion).card := by
                exact Finset.card_le_card_of_injOn
                  (@ColdGermOccurrence.stub data object)
                  (by
                    intro occurrence occurrenceMem
                    have occurrenceCandidate :=
                      (Finset.mem_filter.1 occurrenceMem).1
                    have vertexMem := (Finset.mem_filter.1 occurrenceMem).2
                    have selectedMem : ColdGermOccurrence.stub occurrence ∈
                        Graph.ColdCorridor.allSelectedStubs object cubic := by
                      cases occurrence with
                      | inl epsilon => exact epsilon.property.1
                      | inr epsilon => exact epsilon.property.1
                    let selected : Selected :=
                      ⟨ColdGermOccurrence.stub occurrence, selectedMem⟩
                    have selectedFacts :=
                      Graph.ColdCorridor.selected_facts object cubic selected
                    have sourceReach :
                        (ColdGermOccurrence.stub occurrence).1 ∈ reach := by
                      cases occurrence with
                      | inl epsilon =>
                          have prefixSubcubic :
                              ∀ current ∈ (corridorAt epsilon).prefixSupport
                                  (traceEnd epsilon),
                                object.degree current ≤ data.threshold :=
                            (Finset.mem_filter.1 occurrenceCandidate).2.2
                          have facts := stateFacts epsilon
                          have sourceSubcubic :
                              object.degree (corridorAt epsilon).entryStub.2 ≤
                                data.threshold := by
                            obtain ⟨window, windowMem, stubMem⟩ :=
                              (Graph.ColdCorridor.mem_windowsOf object cubic
                                epsilon.1.1).1 selectedFacts.1
                            have ambient := (Finset.mem_filter.1 windowMem).2
                            have entryEq : (corridorAt epsilon).entryStub.2 =
                                epsilon.1.1 := by
                              simpa only [corridorAt, coldOccurrenceCorridorAt] using
                                congrArg Prod.snd facts.2.1
                            rw [entryEq]
                            exact le_of_eq (ambient epsilon.1.1 stubMem)
                          have vertexMemOutside :
                              vertex ∈ (outsideIncidence epsilon).support := by
                            simpa [incidence] using vertexMem
                          have reached :=
                            Graph.ColdCorridor.Corridor.FirstFailureGermWitness.source_mem_subcubicReach_of_trace
                              (corridorAt epsilon) (outsideIncidence epsilon)
                              (traceEnd epsilon) (traceFacts epsilon).1
                              (traceFacts epsilon).2 data.threshold
                              prefixSubcubic sourceSubcubic vertexMemOutside
                          have entryEq : (corridorAt epsilon).entryStub.2 =
                              epsilon.1.1 := by
                            simpa only [corridorAt, coldOccurrenceCorridorAt] using
                              congrArg Prod.snd facts.2.1
                          rw [entryEq] at reached
                          exact reached
                      | inr epsilon =>
                          have supportBound : ∀ current ∈
                              (crossIncidence epsilon).support,
                                object.degree current ≤ data.threshold :=
                            (Finset.mem_filter.1 occurrenceCandidate).2
                          have sourceBound :
                              object.degree epsilon.1.1 ≤ data.threshold := by
                            apply supportBound epsilon.1.1
                            rw [crossFacts epsilon]
                            simp
                          have targetBound :
                              object.degree epsilon.1.2 ≤ data.threshold := by
                            apply supportBound epsilon.1.2
                            rw [crossFacts epsilon]
                            simp
                          have vertexPair : vertex = epsilon.1.1 ∨
                              vertex = epsilon.1.2 := by
                            rw [crossFacts epsilon] at vertexMem
                            simpa using vertexMem
                          rcases vertexPair with rfl | rfl
                          · exact Graph.SubcubicReach.self_mem_reach object.graph
                              subcubic epsilon.1.1
                              (Graph.ColdCorridor.exchangeBound
                                data.coldSignature + 2) epsilon.1.1
                          · exact Graph.SubcubicReach.adjacent_mem_reach object.graph
                              subcubic selectedFacts.2.symm
                              (Finset.mem_filter.2
                                ⟨Finset.mem_univ _, targetBound⟩)
                              selectedFacts.2.ne (by omega)
                    refine Finset.mem_filter.2
                      ⟨(object.mem_incidences_iff
                          (ColdGermOccurrence.stub occurrence)).2 selectedFacts.2, ?_⟩
                    exact Finset.mem_inter.2
                      ⟨sourceReach, selectedFacts.1⟩)
                  (by
                    intro left _leftMem right _rightMem same
                    exact occurrenceStubInjective same)
              have sourceRegionBounded : ∀ current ∈ sourceRegion,
                  object.degree current ≤ data.threshold := by
                intro current currentMem
                obtain ⟨window, windowMem, currentMem⟩ :=
                  (Graph.ColdCorridor.mem_windowsOf object cubic current).1
                    (Finset.mem_inter.1 currentMem).2
                exact le_of_eq ((Finset.mem_filter.1 windowMem).2 current currentMem)
              have incidenceBound :=
                Graph.ColdCorridor.card_incidences_filter_fst_le object
                  sourceRegion data.threshold sourceRegionBounded
              have cubicBound : ∀ current ∈ subcubic,
                  object.graph.degree current ≤ 3 := by
                intro current currentMem
                have bounded := (Finset.mem_filter.1 currentMem).2
                have graphDegree : object.graph.degree current =
                    (object.graph.neighborSet current).ncard := by
                  rw [Set.ncard_eq_toFinset_card']
                  rfl
                calc
                  object.graph.degree current =
                      (object.graph.neighborSet current).ncard := graphDegree
                  _ = object.degree current :=
                    (object.degree_eq_ncard_neighborSet current).symm
                  _ ≤ 3 := by simpa [data.threshold_eq_three] using bounded
              have reachBound := Graph.SubcubicReach.card_reach_le object.graph
                subcubic cubicBound vertex
                (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
              have stubExcessBound : data.threshold ≤
                  Graph.ColdCorridor.stubExcess data.threshold data.coldSignature := by
                rw [Graph.ColdCorridor.stubExcess, data.threshold_eq_three,
                  data.coldSignature_windowOrder]
                have orderBound := data.three_le_windowOrder
                omega
              calc
                through.card ≤
                    (object.incidences.filter
                      fun pair : object.Vertex × object.Vertex =>
                        pair.1 ∈ sourceRegion).card := throughToIncidences
                _ ≤ data.threshold * sourceRegion.card := incidenceBound
                _ ≤ data.threshold * reach.card :=
                  Nat.mul_le_mul_left _ (Finset.card_le_card Finset.inter_subset_left)
                _ ≤ data.threshold *
                    (1 + data.threshold *
                      (2 ^ (Graph.ColdCorridor.exchangeBound data.coldSignature + 2) - 1)) := by
                  apply Nat.mul_le_mul_left
                  simpa [reach, data.threshold_eq_three] using reachBound
                _ ≤ Graph.ColdCorridor.stubExcess data.threshold data.coldSignature *
                    (1 + data.threshold *
                      (2 ^ (Graph.ColdCorridor.exchangeBound data.coldSignature + 2) - 1)) :=
                  Nat.mul_le_mul_right _ stubExcessBound
                _ = Graph.ColdCorridor.overlapBound data.threshold
                    data.coldSignature := rfl
          obtain ⟨disjointFamily, extracted⟩ :=
            extraction.2 Occurrence (Classical.decEq Occurrence) incidence candidates
              candidateFamily
          have failureClassified : ∀ epsilon : Eligible,
              firstFailureGerm epsilon := by
            intro epsilon
            simpa only [firstFailureHandoff, firstFailureGerm] using
              classification epsilon
          have noncandidateClassified : ∀ occurrence : Occurrence,
              occurrence ∉ candidates →
                ∃ charged root : object.Vertex,
                  data.threshold < object.degree charged ∧
                    object.graph.Adj charged root ∧
                    object.degree root ≤ data.threshold ∧
                    (ColdGermOccurrence.stub occurrence).1 ∈
                      @Graph.SubcubicReach.reach object.Vertex
                        (@FinEnum.instFintype _ object.vertices) object.graph
                        (object.vertexFinset.filter fun current =>
                          object.degree current ≤ data.threshold)
                        root
                        (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                        root := by
            intro occurrence notCandidate
            cases occurrence with
            | inl epsilon =>
                rcases handoff state epsilon with subcubic | high
                · exfalso
                  apply notCandidate
                  exact Finset.mem_filter.2
                    ⟨Finset.mem_univ _, failureClassified epsilon, subcubic⟩
                · obtain ⟨first, _bound, firstHigh, _earlier,
                      root, adjacent, rootSubcubic, sourceReach⟩ := high
                  exact ⟨(corridorAt epsilon).head first, root, firstHigh,
                    adjacent, rootSubcubic, sourceReach⟩
            | inr epsilon =>
                have notSubcubic : ¬ ∀ vertex ∈
                    (crossIncidence epsilon).support,
                      object.degree vertex ≤ data.threshold := by
                  intro subcubic
                  exact notCandidate (Finset.mem_filter.2
                    ⟨Finset.mem_univ _, subcubic⟩)
                push_neg at notSubcubic
                obtain ⟨charged, chargedMem, chargedHigh⟩ := notSubcubic
                have chargedPair : charged = epsilon.1.1 ∨
                    charged = epsilon.1.2 := by
                  rw [crossFacts epsilon] at chargedMem
                  simpa using chargedMem
                have selectedFacts := Graph.ColdCorridor.selected_facts object cubic
                  (⟨epsilon.1, epsilon.property.1⟩ : Selected)
                obtain ⟨sourceWindow, sourceWindowMem, sourceMem⟩ :=
                  (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                    selectedFacts.1
                have sourceDegree : object.degree epsilon.1.1 = data.threshold :=
                  (Finset.mem_filter.1 sourceWindowMem).2 epsilon.1.1 sourceMem
                have chargedEq : charged = epsilon.1.2 := by
                  rcases chargedPair with sourceEq | targetEq
                  · subst charged
                    omega
                  · exact targetEq
                subst charged
                refine ⟨epsilon.1.2, epsilon.1.1, chargedHigh,
                  selectedFacts.2.symm, le_of_eq sourceDegree, ?_⟩
                exact Graph.SubcubicReach.self_mem_reach object.graph
                  (object.vertexFinset.filter fun current =>
                    object.degree current ≤ data.threshold)
                  epsilon.1.1
                  (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                  epsilon.1.1
          have eligibleUniverseCount : (Finset.univ : Finset Eligible).card =
              ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
                fun stub => stub.2 ∉ windows).card := by
            let filtered :=
              (Graph.ColdCorridor.allSelectedStubs object cubic).filter
                fun stub => stub.2 ∉ windows
            let toFiltered : Eligible → {stub // stub ∈ filtered} :=
              fun epsilon => ⟨epsilon.1, Finset.mem_filter.2 epsilon.property⟩
            let fromFiltered : {stub // stub ∈ filtered} → Eligible :=
              fun epsilon => ⟨epsilon.1, Finset.mem_filter.1 epsilon.property⟩
            let equivalence : Eligible ≃ {stub // stub ∈ filtered} :=
              { toFun := toFiltered
                invFun := fromFiltered
                left_inv := by intro epsilon; apply Subtype.ext; rfl
                right_inv := by intro epsilon; apply Subtype.ext; rfl }
            calc
              (Finset.univ : Finset Eligible).card = Fintype.card Eligible :=
                Finset.card_univ
              _ = Fintype.card {stub // stub ∈ filtered} :=
                Fintype.card_congr equivalence
              _ = filtered.card := Fintype.card_coe filtered
              _ = ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
                    fun stub => stub.2 ∉ windows).card := rfl
          have crossUniverseCount : (Finset.univ : Finset Cross).card =
              ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
                fun stub => stub.2 ∈ windows).card := by
            let filtered :=
              (Graph.ColdCorridor.allSelectedStubs object cubic).filter
                fun stub => stub.2 ∈ windows
            let toFiltered : Cross → {stub // stub ∈ filtered} :=
              fun epsilon => ⟨epsilon.1, Finset.mem_filter.2 epsilon.property⟩
            let fromFiltered : {stub // stub ∈ filtered} → Cross :=
              fun epsilon => ⟨epsilon.1, Finset.mem_filter.1 epsilon.property⟩
            let equivalence : Cross ≃ {stub // stub ∈ filtered} :=
              { toFun := toFiltered
                invFun := fromFiltered
                left_inv := by intro epsilon; apply Subtype.ext; rfl
                right_inv := by intro epsilon; apply Subtype.ext; rfl }
            calc
              (Finset.univ : Finset Cross).card = Fintype.card Cross :=
                Finset.card_univ
              _ = Fintype.card {stub // stub ∈ filtered} :=
                Fintype.card_congr equivalence
              _ = filtered.card := Fintype.card_coe filtered
              _ = ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
                    fun stub => stub.2 ∈ windows).card := rfl
          have selectedPartition :
              (Graph.ColdCorridor.allSelectedStubs object cubic).card =
                ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
                    fun stub => stub.2 ∉ windows).card +
                  ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
                    fun stub => stub.2 ∈ windows).card := by
            have partition := Finset.card_filter_add_card_filter_not
              (s := Graph.ColdCorridor.allSelectedStubs object cubic)
              (fun stub => stub.2 ∉ windows)
            simpa only [not_not] using partition.symm
          have occurrenceUniverseCount :
              (Finset.univ : Finset Occurrence).card =
                (Graph.ColdCorridor.allSelectedStubs object cubic).card := by
            calc
              (Finset.univ : Finset Occurrence).card = Fintype.card Occurrence :=
                Finset.card_univ
              _ = Fintype.card Eligible + Fintype.card Cross :=
                Fintype.card_sum
              _ = (Finset.univ : Finset Eligible).card +
                    (Finset.univ : Finset Cross).card := by simp
              _ = (Graph.ColdCorridor.allSelectedStubs object cubic).card := by
                rw [eligibleUniverseCount, crossUniverseCount, selectedPartition]
          have candidateCount : candidates.card ≤
              (Finset.univ : Finset Occurrence).card :=
            Finset.card_le_card (Finset.subset_univ _)
          let corridorLoss :=
            (Finset.univ : Finset Occurrence).card - candidates.card
          have corridorCount : (Finset.univ : Finset Occurrence).card =
              candidates.card + corridorLoss := by
            simpa only [corridorLoss] using
              (Nat.add_sub_of_le candidateCount).symm
          have totalCount :
              (Graph.ColdCorridor.allSelectedStubs object cubic).card =
                candidates.card + corridorLoss := by
            rw [← occurrenceUniverseCount, corridorCount]
          let losses := (Finset.univ : Finset Occurrence).filter fun occurrence =>
            occurrence ∉ candidates
          have lossCard : losses.card = corridorLoss := by
            have partition := Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset Occurrence))
              (fun occurrence => occurrence ∈ candidates)
            have candidateFilter :
                ((Finset.univ : Finset Occurrence).filter fun occurrence =>
                  occurrence ∈ candidates) = candidates := by
              ext occurrence
              simp
            rw [candidateFilter] at partition
            have lossFilter :
                ((Finset.univ : Finset Occurrence).filter fun occurrence =>
                  occurrence ∉ candidates) = losses := rfl
            rw [lossFilter] at partition
            omega
          let chargePair : Occurrence → object.Vertex × object.Vertex :=
            fun occurrence =>
              if missing : occurrence ∉ candidates then
                let witness := noncandidateClassified occurrence missing
                (Classical.choose witness,
                  Classical.choose (Classical.choose_spec witness))
              else
                ((ColdGermOccurrence.stub occurrence).1,
                  (ColdGermOccurrence.stub occurrence).1)
          have chargeFacts : ∀ occurrence : Occurrence,
              occurrence ∉ candidates →
                data.threshold < object.degree (chargePair occurrence).1 ∧
                  object.graph.Adj (chargePair occurrence).1
                    (chargePair occurrence).2 ∧
                  object.degree (chargePair occurrence).2 ≤ data.threshold ∧
                  (ColdGermOccurrence.stub occurrence).1 ∈
                    @Graph.SubcubicReach.reach object.Vertex
                      (@FinEnum.instFintype _ object.vertices) object.graph
                      (object.vertexFinset.filter fun current =>
                        object.degree current ≤ data.threshold)
                      (chargePair occurrence).2
                      (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                      (chargePair occurrence).2 := by
            intro occurrence missing
            dsimp only [chargePair]
            rw [dif_pos missing]
            exact Classical.choose_spec
              (Classical.choose_spec (noncandidateClassified occurrence missing))
          let highIncidences := object.incidences.filter
            fun pair : object.Vertex × object.Vertex =>
              data.threshold < object.degree pair.1 ∧
                object.degree pair.2 ≤ data.threshold
          let sourceFibre := fun pair : object.Vertex × object.Vertex =>
            (Finset.univ : Finset Occurrence).filter fun occurrence =>
              (ColdGermOccurrence.stub occurrence).1 ∈
                @Graph.SubcubicReach.reach object.Vertex
                  (@FinEnum.instFintype _ object.vertices) object.graph
                  (object.vertexFinset.filter fun current =>
                    object.degree current ≤ data.threshold)
                  pair.2
                  (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                  pair.2
          have lossesCovered : losses ⊆ highIncidences.biUnion sourceFibre := by
            intro occurrence occurrenceMem
            have missing := (Finset.mem_filter.1 occurrenceMem).2
            have facts := chargeFacts occurrence missing
            have chargeMember : chargePair occurrence ∈ highIncidences := by
              refine Finset.mem_filter.2
                ⟨(object.mem_incidences_iff (chargePair occurrence)).2 facts.2.1,
                  facts.1, facts.2.2.1⟩
            exact Finset.mem_biUnion.2
              ⟨chargePair occurrence, chargeMember,
                Finset.mem_filter.2 ⟨Finset.mem_univ _, facts.2.2.2⟩⟩
          have sourceFibreBound : ∀ pair ∈ highIncidences,
              (sourceFibre pair).card ≤
                Graph.ColdCorridor.overlapBound data.threshold
                  data.coldSignature := by
            intro pair pairMem
            let subcubic := object.vertexFinset.filter fun current =>
              object.degree current ≤ data.threshold
            let reach := @Graph.SubcubicReach.reach object.Vertex
              (@FinEnum.instFintype _ object.vertices) object.graph
              subcubic pair.2
              (Graph.ColdCorridor.exchangeBound data.coldSignature + 2) pair.2
            let sourceRegion := reach ∩ Graph.ColdCorridor.windowsOf object cubic
            have fibreToIncidences : (sourceFibre pair).card ≤
                (object.incidences.filter fun incidencePair :
                    object.Vertex × object.Vertex =>
                  incidencePair.1 ∈ sourceRegion).card := by
              exact Finset.card_le_card_of_injOn
                (@ColdGermOccurrence.stub data object)
                (by
                  intro occurrence occurrenceMem
                  have sourceReach := (Finset.mem_filter.1 occurrenceMem).2
                  have selectedMem : ColdGermOccurrence.stub occurrence ∈
                      Graph.ColdCorridor.allSelectedStubs object cubic := by
                    cases occurrence with
                    | inl epsilon => exact epsilon.property.1
                    | inr epsilon => exact epsilon.property.1
                  have selectedFacts := Graph.ColdCorridor.selected_facts object cubic
                    (⟨ColdGermOccurrence.stub occurrence, selectedMem⟩ : Selected)
                  refine Finset.mem_filter.2
                    ⟨(object.mem_incidences_iff
                        (ColdGermOccurrence.stub occurrence)).2 selectedFacts.2, ?_⟩
                  exact Finset.mem_inter.2 ⟨sourceReach, selectedFacts.1⟩)
                (by
                  intro left _leftMem right _rightMem same
                  exact occurrenceStubInjective same)
            have sourceRegionBounded : ∀ current ∈ sourceRegion,
                object.degree current ≤ data.threshold := by
              intro current currentMem
              obtain ⟨window, windowMem, currentMem⟩ :=
                (Graph.ColdCorridor.mem_windowsOf object cubic current).1
                  (Finset.mem_inter.1 currentMem).2
              exact le_of_eq
                ((Finset.mem_filter.1 windowMem).2 current currentMem)
            have incidenceBound :=
              Graph.ColdCorridor.card_incidences_filter_fst_le object
                sourceRegion data.threshold sourceRegionBounded
            have cubicBound : ∀ current ∈ subcubic,
                object.graph.degree current ≤ 3 := by
              intro current currentMem
              have bounded := (Finset.mem_filter.1 currentMem).2
              have graphDegree : object.graph.degree current =
                  (object.graph.neighborSet current).ncard := by
                rw [Set.ncard_eq_toFinset_card']
                rfl
              calc
                object.graph.degree current =
                    (object.graph.neighborSet current).ncard := graphDegree
                _ = object.degree current :=
                  (object.degree_eq_ncard_neighborSet current).symm
                _ ≤ 3 := by simpa [data.threshold_eq_three] using bounded
            have reachBound := Graph.SubcubicReach.card_reach_le object.graph
              subcubic cubicBound pair.2
              (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
            have stubExcessBound : data.threshold ≤
                Graph.ColdCorridor.stubExcess data.threshold
                  data.coldSignature := by
              rw [Graph.ColdCorridor.stubExcess, data.threshold_eq_three,
                data.coldSignature_windowOrder]
              have orderBound := data.three_le_windowOrder
              omega
            calc
              (sourceFibre pair).card ≤
                  (object.incidences.filter fun incidencePair :
                      object.Vertex × object.Vertex =>
                    incidencePair.1 ∈ sourceRegion).card := fibreToIncidences
              _ ≤ data.threshold * sourceRegion.card := incidenceBound
              _ ≤ data.threshold * reach.card :=
                Nat.mul_le_mul_left _
                  (Finset.card_le_card Finset.inter_subset_left)
              _ ≤ data.threshold *
                  (1 + data.threshold *
                    (2 ^ (Graph.ColdCorridor.exchangeBound
                      data.coldSignature + 2) - 1)) := by
                apply Nat.mul_le_mul_left
                simpa [reach, data.threshold_eq_three] using reachBound
              _ ≤ Graph.ColdCorridor.stubExcess data.threshold
                    data.coldSignature *
                  (1 + data.threshold *
                    (2 ^ (Graph.ColdCorridor.exchangeBound
                      data.coldSignature + 2) - 1)) :=
                Nat.mul_le_mul_right _ stubExcessBound
              _ = Graph.ColdCorridor.overlapBound data.threshold
                  data.coldSignature := rfl
          have lossesPerHighIncidence : losses.card ≤
              highIncidences.card *
                Graph.ColdCorridor.overlapBound data.threshold
                  data.coldSignature := by
            calc
              losses.card ≤ (highIncidences.biUnion sourceFibre).card :=
                Finset.card_le_card lossesCovered
              _ ≤ ∑ pair ∈ highIncidences, (sourceFibre pair).card :=
                Finset.card_biUnion_le
              _ ≤ ∑ _pair ∈ highIncidences,
                    Graph.ColdCorridor.overlapBound data.threshold
                      data.coldSignature :=
                Finset.sum_le_sum sourceFibreBound
              _ = highIncidences.card *
                    Graph.ColdCorridor.overlapBound data.threshold
                      data.coldSignature := by simp
          let highVertices := (Finset.univ : Finset object.Vertex).filter
            fun vertex => data.threshold < object.degree vertex
          let incidencesFromHigh := object.incidences.filter
            fun pair : object.Vertex × object.Vertex => pair.1 ∈ highVertices
          have highIncidencesSubset : highIncidences ⊆ incidencesFromHigh := by
            intro pair pairMem
            have facts := (Finset.mem_filter.1 pairMem).2
            exact Finset.mem_filter.2
              ⟨(Finset.mem_filter.1 pairMem).1,
                Finset.mem_filter.2 ⟨Finset.mem_univ _, facts.1⟩⟩
          have incidencesFromHighBound : incidencesFromHigh.card ≤
              ∑ vertex ∈ highVertices, object.degree vertex := by
            dsimp only [incidencesFromHigh]
            exact Graph.ColdCorridor.card_incidences_filter_fst_le_sum_degree
              object highVertices
          have highDegreeSumBound :
              (∑ vertex ∈ highVertices, object.degree vertex) ≤
                (data.threshold + 1) *
                  object.ambientSurplus highVertices data.threshold := by
            unfold Graph.FiniteObject.ambientSurplus
            calc
              (∑ vertex ∈ highVertices, object.degree vertex) ≤
                  ∑ vertex ∈ highVertices,
                    (data.threshold + 1) *
                      (object.degree vertex - data.threshold) := by
                exact Finset.sum_le_sum fun vertex vertexMem => by
                  have high := (Finset.mem_filter.1 vertexMem).2
                  have oneLe : 1 ≤ object.degree vertex - data.threshold := by
                    omega
                  have multiplied := Nat.mul_le_mul_left data.threshold oneLe
                  have multiplied' : data.threshold ≤ data.threshold *
                      (object.degree vertex - data.threshold) := by
                    calc
                      data.threshold = data.threshold * 1 := by simp
                      _ ≤ data.threshold *
                          (object.degree vertex - data.threshold) := multiplied
                  calc
                    object.degree vertex = data.threshold +
                        (object.degree vertex - data.threshold) := by omega
                    _ ≤ data.threshold *
                          (object.degree vertex - data.threshold) +
                        (object.degree vertex - data.threshold) :=
                      Nat.add_le_add_right multiplied'
                        (object.degree vertex - data.threshold)
                    _ = (data.threshold + 1) *
                        (object.degree vertex - data.threshold) := by ring
              _ = (data.threshold + 1) *
                    ∑ vertex ∈ highVertices,
                      (object.degree vertex - data.threshold) := by
                exact (Finset.mul_sum highVertices
                  (fun vertex => object.degree vertex - data.threshold)
                  (data.threshold + 1)).symm
          have baselineDegree : ∀ vertex : object.Vertex,
              data.threshold ≤ object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline (object.minDegree_le_degree vertex)
          have highIncidencesBound : highIncidences.card ≤
              (data.threshold + 1) * object.degreeSurplus data.threshold := by
            calc
              highIncidences.card ≤ incidencesFromHigh.card :=
                Finset.card_le_card highIncidencesSubset
              _ ≤ ∑ vertex ∈ highVertices, object.degree vertex :=
                incidencesFromHighBound
              _ ≤ (data.threshold + 1) *
                    object.ambientSurplus highVertices data.threshold :=
                highDegreeSumBound
              _ ≤ (data.threshold + 1) *
                    object.degreeSurplus data.threshold :=
                Nat.mul_le_mul_left _
                  (object.ambientSurplus_le_degreeSurplus highVertices
                    data.threshold baselineDegree)
          have routedLossBound : corridorLoss ≤
              (data.threshold + 1) *
                Graph.ColdCorridor.overlapBound data.threshold
                  data.coldSignature * object.degreeSurplus data.threshold := by
            calc
              corridorLoss = losses.card := lossCard.symm
              _ ≤ highIncidences.card *
                    Graph.ColdCorridor.overlapBound data.threshold
                      data.coldSignature := lossesPerHighIncidence
              _ ≤ ((data.threshold + 1) *
                    object.degreeSurplus data.threshold) *
                    Graph.ColdCorridor.overlapBound data.threshold
                      data.coldSignature :=
                Nat.mul_le_mul_right _ highIncidencesBound
              _ = (data.threshold + 1) *
                    Graph.ColdCorridor.overlapBound data.threshold
                      data.coldSignature * object.degreeSurplus data.threshold := by
                ring
          have quantitative :
              (Graph.ColdCorridor.allSelectedStubs object cubic).card ≤
                disjointFamily.card *
                    Graph.ColdCorridor.extractionDenominator data.threshold
                      data.coldSignature +
                  corridorLoss := by
            have cover := extracted.2.2
            omega
          change ColdGermCandidatesStatement data object
          simp only [ColdGermCandidatesStatement]
          refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            ?_⟩
          simp only [ColdGermFamilyWitness]
          exact ⟨rfl, rfl, candidateFamily, extracted,
            noncandidateClassified, corridorCount, totalCount,
            routedLossBound, quantitative⟩
        ⟩
        .nil)
/-! ## Node `[153]`, `lem:cold-germ-extraction`: strict positivity

On the linear arm, the selected `9C` mass is strictly larger than the sum of
the non-ambient-window loss and the first-high incidence loss.  The exact
count and charge bound retained above therefore make the candidate family,
and hence its greedy disjoint subfamily, nonempty. -/
@[reducible] noncomputable def coldGermFamilyPositiveRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermFamilyPositive
    { Requires := [K .coldGermCandidates, K .coldMassLinear,
        K .coldSelectedBranchExcess, K .coldStubExcess]
      Produces := [K .coldGermFamilyPositive]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let family := (inputs.get (K .coldGermCandidates)).down
      let linear := (inputs.get (K .coldMassLinear)).down
      let selectedExcess := (inputs.get (K .coldSelectedBranchExcess)).down
      let stubExcess := (inputs.get (K .coldStubExcess)).down
      .cons (key := K .coldGermFamilyPositive)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          let cold := canonicalColdWindows data object
          let cubic := cold.filter (AmbientCubicWindow data object)
          let selected := Graph.ColdCorridor.allSelectedStubs object cubic
          let perWindow := coldInteriorBranchExcess data
          change ColdGermCandidatesStatement data object at family
          change ColdMassLinearStatement data object at linear
          change ColdSelectedBranchExcessStatement data object at selectedExcess
          change ColdStubExcessStatement data object at stubExcess
          rcases family with
            ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness⟩
          simp only [ColdGermFamilyWitness] at familyWitness
          rcases familyWitness with
            ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
              noncandidateClassified, occurrenceCount, selectedCount,
              lossBound, quantitative⟩
          have lossSmall : corridorLoss < selected.card := by
            have selectedExact := selectedExcess.1
            change selected.card = perWindow * cubic.card at selectedExact
            change perWindow * cold.card ≤
              perWindow * cubic.card +
                perWindow * object.degreeSurplus data.threshold at stubExcess
            change (perWindow + (data.threshold + 1) *
                Graph.ColdCorridor.overlapBound data.threshold
                  data.coldSignature) * object.degreeSurplus data.threshold <
              perWindow * cold.card at linear
            change corridorLoss ≤ (data.threshold + 1) *
                Graph.ColdCorridor.overlapBound data.threshold
                  data.coldSignature * object.degreeSurplus data.threshold at lossBound
            rw [Nat.add_mul] at linear
            rw [selectedExact]
            omega
          have candidatePositive : 0 < candidates.card := by
            change selected.card = candidates.card + corridorLoss at selectedCount
            omega
          have disjointPositive : 0 < disjointFamily.card :=
            Graph.ColdCorridor.coldGerm_nonempty extracted.2.2 candidatePositive
          change ColdGermFamilyPositiveStatement data object
          simp only [ColdGermFamilyPositiveStatement]
          exact ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            by
              simp only [ColdGermFamilyWitness]
              exact ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
                noncandidateClassified, occurrenceCount, selectedCount,
                lossBound, quantitative⟩,
            disjointPositive⟩⟩
        .nil)
/-! ## Node `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy

On the absorbed-configuration residual every selected branch-excess half-edge
`ε` of an ambient-cubic cold window has a return corridor (`lem:bridgeless`)
and a first-failure exchange germ; the lemma's dichotomy is *per half-edge*,
by whether the germ's support `J` meets a vertex above the threshold.  Case
(i): `J` is subcubic, so `ε`'s germ is a candidate of `lem:cold-germ-extraction`
and is charged in full.  Case (ii): `J` contains a vertex `z` above the
threshold; node `[10]` (`K .slackIndependent`) makes every neighbour of `z`
sit exactly at the threshold, so `z` is a heavy centre.  The row publishes
that dichotomy for every selected half-edge, on the literal residual; the
exhaustive object-level decision that follows (`absorbedGermDichotomy`) only
chooses which continuation closes the branch. -/
set_option maxHeartbeats 4000000 in
@[reducible] noncomputable def absorbedGermSplitRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermSplit
    { Requires := [K .coldGermCandidates, K .coldHandoffTransfer,
        K .slackIndependent]
      Produces := [K .absorbedGermSplit]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let family := (inputs.get (K .coldGermCandidates)).down
      let handoff := (inputs.get (K .coldHandoffTransfer)).down
      let independent := (inputs.get (K .slackIndependent)).down
      .cons (key := K .absorbedGermSplit)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
          letI : Fintype (ColdEligibleHalfEdge data object) :=
            coldEligibleHalfEdgeFintype data object
          change ColdGermCandidatesStatement data object at family
          rcases family with
            ⟨routing, _incidence, _candidates, _disjointFamily, _corridorLoss,
              _familyWitness⟩
          change AbsorbedGermSplitStatement data inputs.current.object
          simp only [AbsorbedGermSplitStatement]
          refine ⟨routing, ?_⟩
          intro epsilon
          let classified := coldRoutedClassified data object routing
          let state := classified.state
          rcases handoff state epsilon with subcubic | high
          · apply Or.inl
            exact Finset.mem_filter.2
              ⟨Finset.mem_univ _,
                Classical.choose_spec routing.surviving.holds epsilon,
                subcubic⟩
          · rcases high with
              ⟨first, firstBound, firstHigh, earlierBound, _root⟩
            refine Or.inr ⟨first, firstBound, firstHigh, earlierBound,
              fun neighbour adjacent => ?_⟩
            apply le_antisymm
            · by_contra above
              push Not at above
              exact independent ((coldOccurrenceCorridorAt data object classified
                epsilon).head first) neighbour firstHigh above adjacent
            · exact le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree neighbour)⟩
        .nil)

/-! ## Nodes `[174]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ split

On the absorbed-germ residual (`[173]`'s no arm), node `[175]` tests whether
the literal case-(i) occurrence class is nonempty.  The yes arm records only
that exact predicate as `K .coldPositiveGerm`; node `[176]` obtains the
candidate extraction from its existing node-`[153]` owner.  Independently of
that test, `absorbedGermSplitRow` retains the case-(ii) witness for every
occurrence outside the candidate set, so mixed families continue through both
paper routes without losing either subfamily.  On the no arm the same
complement is the whole selected family. -/
noncomputable def absorbedGermDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    (positiveFresh : K .coldPositiveGerm ∉ known)
    (absorbedFresh : K .absorbedGermFanData ∉ known) :
    Decision (K .coldPositiveGerm) (K .absorbedGermFanData) previous := by
  classical
  let split := (previous.get (K .absorbedGermSplit)).down
  let object := current.object
  letI : FinEnum object.Vertex := object.vertices
  change AbsorbedGermSplitStatement data object at split
  simp only [AbsorbedGermSplitStatement] at split
  let routing := Classical.choose split
  let alternatives := Classical.choose_spec split
  let routedCandidates := coldRoutedCandidates data object routing
  exact Decision.run previous (K .coldPositiveGerm) (K .absorbedGermFanData)
    `Hypostructure.Graph.Strategy.Spine.absorbedGermDichotomy
    (if positive : 0 < routedCandidates.card then
      .inl ⟨by
        change ColdPositiveGermStatement data object
        exact ⟨routing, positive⟩⟩
    else
      .inr ⟨by
        let family := (previous.get (K .coldGermCandidates)).down
        change ColdGermCandidatesStatement data object at family
        rcases family with
          ⟨familyRouting, incidence, candidates, disjointFamily, corridorLoss,
            familyWitness⟩
        have routingEq : familyRouting = routing := Subsingleton.elim _ _
        subst familyRouting
        change AbsorbedGermFanDataStatement data object
        simp only [AbsorbedGermFanDataStatement]
        refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
          familyWitness, ?_⟩
        intro epsilon _notCandidate
        rcases alternatives epsilon with candidate | high
        · exact (positive (Finset.card_pos.2 ⟨_, candidate⟩)).elim
        · exact high⟩)
    positiveFresh absorbedFresh

/-- Node `[177]` on `[175]`'s positive arm.  The node-`[153]` package already
contains the exact candidate/loss identity and the `B_cold·σ(G)` loss bound;
the per-incidence split supplies the least-high witness on its complement.
This owner combines those two previously proved facts in the ledger.  It is
run before the decorated-envelope owner, so a mixed family publishes its
complete case-(ii) accounting without re-proving node `[153]`. -/
@[reducible] noncomputable def absorbedGermFanDataRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanData
    { Requires := [K .absorbedGermSplit, K .coldGermCandidates]
      Produces := [K .absorbedGermFanData]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .absorbedGermSplit)).down
      let family := (inputs.get (K .coldGermCandidates)).down
      .cons (key := K .absorbedGermFanData)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change AbsorbedGermSplitStatement data object at split
          change ColdGermCandidatesStatement data object at family
          simp only [AbsorbedGermSplitStatement] at split
          obtain ⟨splitRouting, alternatives⟩ := split
          obtain ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness⟩ := family
          have routingEq : splitRouting = routing := Subsingleton.elim _ _
          subst splitRouting
          change AbsorbedGermFanDataStatement data object
          simp only [AbsorbedGermFanDataStatement]
          refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            familyWitness, ?_⟩
          intro epsilon notCandidate
          rcases alternatives epsilon with candidate | high
          · exact (notCandidate candidate).elim
          · exact high⟩
        .nil)

/-- Node `[176]`: the positive class chosen at `[175]` is the exact candidate
set inside node `[153]`'s retained extraction.  Hence the already-published
greedy extraction theorem makes that same disjoint family nonempty. -/
@[reducible] noncomputable def absorbedGermFamilyPositiveRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFamilyPositive
    { Requires := [K .coldPositiveGerm, K .coldGermCandidates]
      Produces := [K .coldGermFamilyPositive]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let positive := (inputs.get (K .coldPositiveGerm)).down
      let family := (inputs.get (K .coldGermCandidates)).down
      .cons (key := K .coldGermFamilyPositive)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change ColdPositiveGermStatement data object at positive
          change ColdGermCandidatesStatement data object at family
          rcases positive with ⟨positiveRouting, positiveCard⟩
          rcases family with
            ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness⟩
          have routingEq : positiveRouting = routing := Subsingleton.elim _ _
          subst positiveRouting
          simp only [ColdGermFamilyWitness] at familyWitness
          rcases familyWitness with
            ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
              noncandidateClassified, occurrenceCount, selectedCount,
              lossBound, quantitative⟩
          have candidatePositive : 0 < candidates.card := by
            rw [candidatesEq]
            exact positiveCard
          have disjointPositive : 0 < disjointFamily.card :=
            Graph.ColdCorridor.coldGerm_nonempty extracted.2.2 candidatePositive
          change ColdGermFamilyPositiveStatement data object
          refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            ?_, disjointPositive⟩
          simp only [ColdGermFamilyWitness]
          exact ⟨incidenceEq, candidatesEq, candidateFamily, extracted,
            noncandidateClassified, occurrenceCount, selectedCount,
            lossBound, quantitative⟩⟩
        .nil)

/-! ## Node `[177]`, `lem:absorbed-germ-fan-data` (ii): decorated handoff fan data

For every occurrence in `[175]`'s case-(ii) complement, let `z` be the first
high vertex on its retained first-failure corridor.  The row uses the literal
prefix `J = corridor.prefixSupport traceEnd` as the counted core.  It proves
that `J` is connected and lies in the canonical remainder, takes `H = {z}` and
`K_z = N_G(z)`, and supplies an arm from every assigned neighbour to `J`.
The selection excludes every accepted fan return and label collision, while
`remainderNormalized` and `uncompressible` establish the remaining
`DecoratedHandoff.Admissible` clauses.  The high-degree bound gives two
distinct assigned neighbours.  Thus the value published at
`K .typeBFanEntry` is the manuscript's actual assigned-support/decorated-
envelope destination for the direct `[177] → [65]` edge.  No negative-charge
or zero-surplus premise is asserted at this handoff. -/
set_option maxHeartbeats 8000000 in
@[reducible] noncomputable def absorbedGermFanEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.absorbedGermFanEnvelope
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .absorbedGermFanData]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      let fanData := (inputs.get (K .absorbedGermFanData)).down
      .cons (key := K .typeBFanEntry)
        ⟨by
          classical
          letI : FinEnum inputs.current.object.Vertex :=
            inputs.current.object.vertices
          letI : Fintype inputs.current.object.Vertex := inferInstance
          letI : DecidableRel inputs.current.object.graph.Adj :=
            inputs.current.object.decideAdj
          change TypeBFanEntryStatement data inputs.current.object
          apply Or.inr
          apply Or.inl
          simp only [AbsorbedGermDecoratedAssignedSupportStatement]
          change AbsorbedGermFanDataStatement data inputs.current.object at fanData
          simp only [AbsorbedGermFanDataStatement] at fanData
          obtain ⟨routing, _incidence, _candidates, _disjointFamily,
              _corridorLoss, _familyWitness, fanData⟩ := fanData
          refine ⟨routing, ?_⟩
          intro epsilon notCandidate
          obtain ⟨firstIndex, firstBound, high, earlierBound,
              neighboursCubic⟩ := fanData epsilon notCandidate
          let classified := coldRoutedClassified data inputs.current.object routing
          let state := classified.state
          let stateOne := Classical.choose_spec state
          let componentAt := Classical.choose stateOne
          let stateTwo := Classical.choose_spec stateOne
          let corridorAt := Classical.choose stateTwo
          let stateThree := Classical.choose_spec stateTwo
          let presentationAt := Classical.choose stateThree
          let stateFour := Classical.choose_spec stateThree
          let indexAt := Classical.choose stateFour
          let stateBundle := Classical.choose_spec stateFour
          let routed : ColdEligibleHalfEdge data inputs.current.object := epsilon
          let component := componentAt routed
          let corridor := corridorAt routed
          let _presentation := presentationAt routed
          let _index := indexAt routed
          let centre := corridor.head firstIndex
          change data.threshold < inputs.current.object.degree centre at high
          change (∀ neighbour : inputs.current.object.Vertex,
            inputs.current.object.graph.Adj centre neighbour →
              inputs.current.object.degree neighbour = data.threshold) at neighboursCubic
          refine ⟨centre, ⟨routing, epsilon, rfl, firstIndex, rfl,
            firstBound, high, earlierBound, neighboursCubic, ?_⟩⟩
          let traceEnd := coldRoutedTraceEnd data inputs.current.object routing epsilon
          change firstIndex.1 ≤ traceEnd at firstBound
          let core := corridor.prefixSupport traceEnd
          have centreCore : centre ∈ core := by
            apply (corridor.mem_prefixSupport traceEnd centre).2
            refine ⟨corridor.inside.1.getVert firstIndex.1, ?_, rfl⟩
            have member := SimpleGraph.Walk.getVert_mem_support
              (corridor.inside.1.take traceEnd) firstIndex.1
            simpa only [SimpleGraph.Walk.take_getVert,
              Nat.min_eq_right firstBound] using member
          have coreInside : core ⊆ inputs.current.object.remainderSupport
              (canonicalWindowPacking data inputs.current.object) := by
            exact (corridor.prefixSupport_subset_component traceEnd).trans
              (stateBundle.2.2.2.1 routed)
          have avoids : ¬ Graph.HasCycleWithLength data.LengthOK
              inputs.current.object := selected.1
          have denied : ∀ c a b,
              ¬ handoffAbsorbing data inputs.current.object
                (canonicalWindowPacking data inputs.current.object) c a b :=
            fun _ _ _ collision => avoids
              (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                data.degenerateClosureRejected collision)
          let assigned := inputs.current.object.graph.neighborFinset centre
          let arm := fun next : inputs.current.object.Vertex =>
            if next ∈ core then [next] else [next, centre]
          let envelope : Graph.DecoratedHandoff.Envelope inputs.current.object
              data.LengthOK (handoffHighDegree data inputs.current.object)
              (handoffAbsorbing data inputs.current.object
                (canonicalWindowPacking data inputs.current.object)) :=
            { core := core
              decorations := {centre}
              decorations_high := by
                intro current member
                simp only [Finset.mem_singleton] at member
                simpa [member] using high
              assigned := fun _ => assigned
              assigned_nonempty := by
                intro current member
                simp only [Finset.mem_singleton] at member
                subst current
                apply Finset.card_pos.mp
                rw [show assigned.card = inputs.current.object.degree centre by
                  simp [assigned, Graph.FiniteObject.degree,
                    SimpleGraph.card_neighborFinset_eq_degree]]
                exact Nat.zero_lt_of_lt high
              assigned_adj := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                exact (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
              arm := fun _ next => arm next
              arm_issued := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                by_cases nextCore : next ∈ core <;> simp [arm, nextCore]
              arm_chain := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                have adjacent :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
                by_cases nextCore : next ∈ core
                · simp [arm, nextCore]
                · simpa [arm, nextCore] using adjacent.symm
              arm_nodup := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                have adjacent :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
                by_cases nextCore : next ∈ core
                · simp [arm, nextCore]
                · simp [arm, nextCore, adjacent.ne.symm]
              arm_lands := by
                intro current member next nextMember
                simp only [Finset.mem_singleton] at member
                subst current
                by_cases nextCore : next ∈ core
                · exact ⟨next, by simp [arm, nextCore], nextCore⟩
                · exact ⟨centre, by simp [arm, nextCore], centreCore⟩
              arm_interior := by
                intro current member next nextMember vertex vertexMember alternative
                simp only [Finset.mem_singleton] at member
                subst current
                have adjacent :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 nextMember
                by_cases nextCore : next ∈ core
                · simp only [arm, if_pos nextCore, List.mem_singleton] at vertexMember
                  simp [vertexMember, arm, nextCore]
                · simp only [arm, if_neg nextCore, List.mem_cons,
                    List.not_mem_nil, or_false] at vertexMember
                  rcases vertexMember with rfl | rfl
                  · exfalso
                    simp only [Finset.mem_singleton] at alternative
                    rcases alternative with inCore | equal | equal
                    · exact nextCore inCore
                    · exact adjacent.ne equal.symm
                    · exact adjacent.ne equal.symm
                  · simp [arm, nextCore]
              fanSafe := by
                intro current member first firstMember second secondMember different
                simp only [Finset.mem_singleton] at member
                subst current
                have firstAdj :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 firstMember
                have secondAdj :=
                  (SimpleGraph.mem_neighborFinset _ _ _).1 secondMember
                exact ⟨Graph.DecoratedHandoff.fanSafe_geometric firstAdj secondAdj
                    different avoids,
                  denied centre first second⟩ }
          have packingSpec := Classical.choose_spec
            (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
          have packingMaximal : ∀ window : Finset inputs.current.object.Vertex,
              inputs.current.object.InducesWindow data.windowOrder window →
                ∃ member ∈ canonicalWindowPacking data inputs.current.object,
                  ¬ Disjoint window member := by
            intro window induced
            exact inputs.current.object.exists_mem_not_disjoint_of_card_eq
              data.windowOrder_pos packingSpec.1 packingSpec.2 induced
          have coreSafe : handoffWindowFree data inputs.current.object core := by
            constructor
            · intro window subset induced
              exact (normalized (canonicalWindowPacking data inputs.current.object)
                packingSpec.1 packingMaximal window
                  (subset.trans coreInside)).1 induced
            · intro internal subset
              exact (normalized (canonicalWindowPacking data inputs.current.object)
                packingSpec.1 packingMaximal internal
                  (subset.trans coreInside)).2
          have admissible : Graph.DecoratedHandoff.Admissible
              inputs.current.object data.LengthOK
              (handoffUncompressible data inputs.current.object)
              (handoffWindowFree data inputs.current.object) envelope :=
            Graph.DecoratedHandoff.admissible_of_envelope avoids coreSafe
              uncompressible
          have assignedTwo : 1 < assigned.card := by
            rw [show assigned.card = inputs.current.object.degree centre by
              simp [assigned, Graph.FiniteObject.degree,
                SimpleGraph.card_neighborFinset_eq_degree]]
            have thresholdLower := data.three_le_threshold
            omega
          obtain ⟨first, firstMember, second, secondMember, different⟩ :=
            Finset.one_lt_card.mp assignedTwo
          have firstAssigned : first ∈ envelope.assigned centre := by
            simpa [envelope] using firstMember
          have secondAssigned : second ∈ envelope.assigned centre := by
            simpa [envelope] using secondMember
          refine And.intro (corridor.prefixSupport_connectedOn traceEnd) ?_
          refine And.intro coreInside ?_
          refine Exists.intro envelope ?_
          refine And.intro rfl ?_
          refine And.intro rfl ?_
          refine And.intro admissible ?_
          refine Exists.intro first ?_
          refine Exists.intro second ?_
          exact And.intro different (And.intro firstAssigned secondAssigned)
        ⟩
        .nil)

/-! ## Nodes `[154]`--`[156]`, `lem:cold-bounded-germ-trichotomy` and
`lem:cold-increment-arithmetic`

Every length-changing cold bounded germ of the current residual is hit-realized
(G1, refuted by the selection's target avoidance), hit-distinguished (G2, a
target-defective identification, routed to the target-defect ledger), or silent
(G3, a target-complete compression of a proper support, refuted by
`cor:uncompressible`).  The increment arithmetic clauses are the framework's
`ColdIncrementArithmetic` lemmas.  The routed conclusion `K .coldGermRouted` is
G2 for every surviving length-changing germ. -/
@[reducible] noncomputable def coldGermTrichotomyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermTrichotomy
    { Requires := [K .coldGermCandidates, K .selection, K .uncompressible]
      Produces := [K .coldGermRealized, K .coldGermDistinguished,
        K .coldGermSilent, K .coldGermRouted]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let candidates := (inputs.get (K .coldGermCandidates)).down
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
          (Graph.HasCycleWithLength data.LengthOK) :=
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      let notRealizing : ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) inputs.current.object,
          ¬ germ.Realizing :=
        fun germ realizing =>
          selected.1 (germ.target_of_realizing targetInvariant realizing)
      let notSilent : ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) inputs.current.object,
          germ.increment < 0 → ¬ germ.Neutral :=
        fun germ shorter neutral =>
          uncompressible germ.support
            (germ.compressibleSupport_of_not_distinguishing shorter neutral.2)
      .cons (key := K .coldGermRealized)
        ⟨⟨candidates, notRealizing, fun germ => germ.trichotomy⟩⟩
        (.cons (key := K .coldGermDistinguished)
          ⟨⟨candidates, fun germ Profile profile distinguishing =>
            germ.not_targetComplete_of_distinguishing profile distinguishing⟩⟩
          (.cons (key := K .coldGermSilent)
            ⟨⟨notSilent,
              fun germ => germ.not_lengthChanging_iff,
              fun increment base copies length positive overlapping lower upper
                  accepted =>
                Graph.ColdCorridor.exists_not_survivesSmear_of_mem_interval
                  positive overlapping lower upper accepted,
              fun increment base exponent residue positive small reached congruent
                  accepted =>
                Graph.ColdCorridor.exists_not_survivesSmear_of_pow_congruent
                  positive small reached congruent accepted,
              fun increment base _ wide criterion =>
                Graph.ColdCorridor.exists_hit_of_orderOf_lt (base := base) wide criterion,
              fun transient exponent odd past =>
                Graph.ColdCorridor.pow_mod_of_le past⟩⟩
            (.cons (key := K .coldGermRouted)
              ⟨⟨candidates, fun germ shorter =>
                have distinguishing :=
                  Graph.ColdCorridor.boundedGerm_not_survives notRealizing notSilent
                    germ shorter
                ⟨distinguishing,
                  fun Profile profile =>
                    germ.not_targetComplete_of_distinguishing profile distinguishing,
                  Or.inl distinguishing⟩⟩⟩
              .nil))))

/-! ## Node `[157]`, `lem:cold-same-interface-table` and
`lem:cold-short-self-return-filter`

Every row of the finite same-interface table is routed: no row is realizing, and
a row is handed off or distinguishing (a row that is neither is a compression of
its own proper support, excluded at `[14]`); the short self-return exceptions
survive their smear and are routed the same way; and the table is finite. -/
@[reducible] noncomputable def coldSameInterfaceTableRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldSameInterfaceTable
    { Requires := [K .coldGermCandidates, K .selection, K .uncompressible]
      Produces := [K .coldSameInterfaceTable]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let candidates := (inputs.get (K .coldGermCandidates)).down
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
          (Graph.HasCycleWithLength data.LengthOK) :=
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      .cons (key := K .coldSameInterfaceTable)
        ⟨⟨candidates, fun Handoff row =>
            Graph.ColdCorridor.row_closed targetInvariant selected.1
              uncompressible row,
          fun Handoff self =>
            Graph.ColdCorridor.selfReturn_closed targetInvariant selected.1
              uncompressible self,
          fun length failed =>
            Graph.ColdCorridor.exists_accepted_of_not_survivesSmear failed,
          rfl,
          fun Handoff row => row.increment_eq_zero⟩⟩
        .nil)

/-! ## Node `[168]`: the stub structure of the ambient-cubic cold windows

`lem:cold-window-stub-excess` counted `15` external stubs per ambient-cubic
window; here they are located: the two path endpoints carry `δ − 1` stubs each
and every interior vertex carries `δ − 2` (`Graph/WindowStubStructure.lean`).
This is what the symmetric-pair analysis of the dense residual charges: two
internally disjoint strands leaving one attachment vertex need two stubs there,
so a genuine symmetric strand pair attaches only at endpoints, a window
carries at most one, and the `(order − 2)(δ − 2)` interior stubs are asymmetric
single-stub attachments. -/
@[reducible] noncomputable def coldWindowStubStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldWindowStubStructure
    { Requires := [K .hotColdPartition]
      Produces := [K .coldWindowStubStructure]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .coldWindowStubStructure)
        ⟨by
          classical
          intro window member
          have windowMem : window ∈ canonicalWindowPacking data inputs.current.object :=
            Finset.sdiff_subset (Finset.mem_filter.1 member).1
          have cubic : ∀ vertex ∈ window, inputs.current.object.degree vertex = data.threshold :=
            (Finset.mem_filter.1 member).2
          have induces : inputs.current.object.InducesWindow data.windowOrder window :=
            split.1.1 window windowMem
          obtain ⟨ends, endsSubset, endsCard, interior, endpoints⟩ :=
            Graph.FiniteObject.exists_ends_externalNeighbours window
              data.three_le_windowOrder induces cubic
          exact ⟨ends, endsSubset, endsCard, interior, endpoints,
            Graph.FiniteObject.interior_stubs_le_asymmetric window
              data.three_le_windowOrder induces cubic⟩⟩
        .nil)

/-! ## Node `[169]`, `def:blocked-class`: the trivial neutral germ residual

*"On the trivial neutral germ residual, `G ∈ 𝓑(𝒫)`, and every window of `G` is
blocked at every scale."*  The row publishes exactly that: the object's own
labelled skeleton has the baseline minimum degree, contains every packed window
at its labelled position, and — the object having no accepted cycle at all
(`K .selection`) — no accepted cycle passes through a window; and the blocked
class is dominated by the skeleton budget (`lem:skeleton-dominates`,
`rem:blocked-class-checks` (a): the class is the *near-cubic* one).  Nodes
`[170]`--`[172]` (`lem:scale-additivity`, `lem:blocked-graphs-compress`,
`lem:system-increment-arithmetic`) are stated over this class. -/
@[reducible] noncomputable def blockedClassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedClassMember
    { Requires := [K .selection, K .hotColdPartition,
        K .coldCanonicalReplacementTrivial]
      Produces := [K .blockedClassMember]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := (inputs.get (K .selection)).down.1
      let split := (inputs.get (K .hotColdPartition)).down
      let _trivial :=
        (inputs.get (K .coldCanonicalReplacementTrivial)).down
      .cons (key := K .blockedClassMember)
        ⟨Graph.BlockedClass.minDegree_objectSkeleton inputs.current.object data.threshold
            inputs.current.baseline,
          Graph.BlockedClass.objectSkeleton_blocked inputs.current.object data.windowOrder
            data.LengthOK (canonicalWindowPacking data inputs.current.object) split.1 avoids,
          Graph.BlockedClass.card_blocked_le_skeletonBudget inputs.current.object
            data.threshold data.windowOrder data.LengthOK _⟩
        .nil)

/-! ## Node `[163]`, `lem:neutral-germ-symmetry`: the symmetry split

A neutral equal-length terminal germ carries no target information; it is a
symmetry.  The manuscript's question is whether its second representative is
graph-realized as a genuine second strand.  The yes-arm is the two-strand route
`[167]`; the no-arm is the canonical-replacement route `[165]`--`[166]`.
Canonical order is deliberately absent from this decision.  Both arms retain
the exact marked configuration read from the incoming `ExactLedger`. -/
@[reducible] noncomputable def neutralEqualLengthTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.neutralEqualLengthTerminal
    { Requires := [K .coldGermFamilyPositive, K .denseColdCorridorsTerminal,
        K .selection]
      Produces := [K .coldNeutralEqualLengthTerminal]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let positive := (inputs.get (K .coldGermFamilyPositive)).down
      let terminal := (inputs.get (K .denseColdCorridorsTerminal)).down
      let selected := (inputs.get (K .selection)).down
      .cons (key := K .coldNeutralEqualLengthTerminal)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change ColdGermFamilyPositiveStatement data object at positive
          rcases positive with
            ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness, positiveCard⟩
          obtain ⟨epsilon, epsilonMem⟩ := Finset.card_pos.mp positiveCard
          let germ := incidence epsilon
          have active : ActiveColdGermStatement data object germ := by
            refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness, ?_⟩
            exact ⟨epsilon, epsilonMem, rfl⟩
          let baselineInvariant :=
            Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold
          let targetInvariant :=
            (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
          let Reading : Graph.CanonicalPiece germ.atom.interface → Prop :=
            fun candidate =>
              Graph.CanonicalPiece.CutStateReading
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK)
                  germ.piece candidate ∧
                (Graph.glue candidate.toPiece germ.atom.outside).edgeCount =
                  (Graph.glue germ.piece germ.atom.outside).edgeCount
          have sourceCutState :
              Graph.CanonicalPiece.CutStateReading
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                germ.piece germ.piece.toCanonical :=
            Graph.CanonicalPiece.cutStateReading_toCanonical
              baselineInvariant targetInvariant germ.piece
          have sourceEdgeCount :
              (Graph.glue germ.piece.toCanonical.toPiece germ.atom.outside).edgeCount =
                (Graph.glue germ.piece germ.atom.outside).edgeCount :=
            Graph.FiniteObject.edgeCount_eq_of_isomorphic
              (germ.piece.toCanonical_glue_isomorphic germ.atom.outside)
          have sourceReading : Reading germ.piece.toCanonical :=
            ⟨sourceCutState, sourceEdgeCount⟩
          have realizable : ∃ candidate, Reading candidate :=
            ⟨germ.piece.toCanonical, sourceReading⟩
          let canonical :=
            Graph.CanonicalPiece.canonicalRepresentative Reading realizable
          have canonicalReading : Reading canonical :=
            Graph.CanonicalPiece.canonicalRepresentative_reading Reading realizable
          have canonicalSizeLe :
              canonical.size ≤ germ.piece.internalVertexCount := by
            calc
              canonical.size ≤ germ.piece.toCanonical.size :=
                Graph.CanonicalPiece.canonicalRepresentative_size_le
                  Reading realizable sourceReading
              _ = germ.piece.internalVertexCount := rfl
          have sourceAvoids :
              ¬ Graph.HasCycleWithLength data.LengthOK
                  (Graph.glue germ.piece germ.atom.outside) := by
            intro hit
            exact selected.1
              ((targetInvariant.iff_of_iso
                ⟨germ.atom.reconstructionIso⟩).mp hit)
          have sourceBaseline :
              Graph.MinimumDegreeAtLeast data.threshold
                (Graph.glue germ.piece germ.atom.outside) :=
            (baselineInvariant.iff_of_iso
              ⟨germ.atom.reconstructionIso⟩).mpr
                inputs.current.baseline
          have canonicalNotShorter :
              ¬ canonical.size < germ.piece.internalVertexCount := by
            intro shorter
            have cutState := canonicalReading.1
            have swappedBaseline :
                Graph.MinimumDegreeAtLeast data.threshold
                  (Graph.glue canonical.toPiece germ.atom.outside) :=
              cutState.2.2 germ.atom.outside sourceBaseline
            have swappedAvoids :
                ¬ Graph.HasCycleWithLength data.LengthOK
                    (Graph.glue canonical.toPiece germ.atom.outside) := by
              intro hit
              exact sourceAvoids ((cutState.2.1 germ.atom.outside).mp hit)
            have swappedSmaller :
                Graph.FiniteObject.LexicographicallySmaller
                  (Graph.glue canonical.toPiece germ.atom.outside) object := by
              refine (Graph.FiniteObject.lexicographicallySmaller_congr_right
                ⟨germ.atom.reconstructionIso⟩).mp ?_
              apply Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt
              have sourcePieceCount :
                  germ.atom.piece.internalVertexCount =
                    germ.piece.internalVertexCount := rfl
              simp only [Graph.glue_vertexCount,
                Graph.CanonicalPiece.toPiece_internalVertexCount]
              rw [sourcePieceCount]
              omega
            exact swappedAvoids
              (selected.2 (Graph.glue canonical.toPiece germ.atom.outside)
                swappedSmaller swappedBaseline)
          have canonicalEqualLength :
              canonical.size = germ.piece.internalVertexCount :=
            Nat.le_antisymm canonicalSizeLe
              (Nat.le_of_not_gt canonicalNotShorter)
          let representative :=
            if RefinedLexicographicallySmaller
                (Graph.glue canonical.toPiece germ.atom.outside) object then
              canonical
            else
              germ.piece.toCanonical
          have representativeReading : Reading representative := by
            dsimp only [representative]
            split
            · exact canonicalReading
            · exact sourceReading
          have equalLength :
              representative.size = germ.piece.internalVertexCount := by
            dsimp only [representative]
            split
            · exact canonicalEqualLength
            · rfl
          have canonicalPosition :
              representative = germ.piece.toCanonical ∨
                (Graph.CanonicalPiece.Precedes representative
                    germ.piece.toCanonical ∧
                  RefinedLexicographicallySmaller
                    (Graph.glue representative.toPiece germ.atom.outside)
                    object) := by
            classical
            dsimp only [representative]
            split <;> rename_i decrease
            · by_cases same : canonical = germ.piece.toCanonical
              · exact Or.inl same
              · exact Or.inr ⟨
                  Graph.CanonicalPiece.canonicalRepresentative_precedes
                    Reading realizable sourceReading (Ne.symm same),
                  decrease⟩
            · exact Or.inl rfl
          refine ⟨terminal, germ, representative, ?_⟩
          change ActiveColdGermStatement data object germ ∧
            (Graph.CanonicalPiece.CutStateReading
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                germ.piece representative ∧
              (Graph.glue representative.toPiece germ.atom.outside).edgeCount =
                (Graph.glue germ.piece germ.atom.outside).edgeCount) ∧
            representative.size = germ.piece.internalVertexCount ∧
            (representative = germ.piece.toCanonical ∨
              (Graph.CanonicalPiece.Precedes representative
                  germ.piece.toCanonical ∧
                RefinedLexicographicallySmaller
                  (Graph.glue representative.toPiece germ.atom.outside)
                  object)) ∧
            ¬ Graph.HasCycleWithLength data.LengthOK
                (Graph.glue germ.piece germ.atom.outside)
          exact ⟨active, representativeReading, equalLength,
            canonicalPosition, sourceAvoids⟩
        ⟩
        .nil)

noncomputable def neutralGermSymmetryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldNeutralEqualLengthTerminal) known]
    (canonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known)
    (genuineFresh : K .coldGenuineSecondStrand ∉ known) :
    Decision (K .coldCanonicalNeutralConfiguration)
      (K .coldGenuineSecondStrand) previous := by
  classical
  let neutral := (previous.get (K .coldNeutralEqualLengthTerminal)).down
  let germ := Classical.choose neutral.2
  let representative := Classical.choose (Classical.choose_spec neutral.2)
  let configuration := Classical.choose_spec
    (Classical.choose_spec neutral.2)
  exact Decision.run previous (K .coldCanonicalNeutralConfiguration)
    (K .coldGenuineSecondStrand)
    `Hypostructure.Graph.Strategy.Spine.neutralGermSymmetryDichotomy
    (if realized : ∃ config : Graph.TwoStrand.Configuration,
        GenuineSecondStrandConfiguration data current.object germ representative config then
      let config := Classical.choose realized
      .inr ⟨germ, representative, config, configuration,
        Classical.choose_spec realized⟩
    else
      .inl ⟨germ, representative, configuration, realized⟩)
    canonicalFresh genuineFresh

/-! ## Node `[167]`, `lem:two-strand-check`: the literal finite check

The genuine arm of `[163]` retains the two ambient strands and the window
segment.  This owner constructs the cycles of lengths `2ℓ` and `ℓ+d` from
those paths.  Either dyadic arm contradicts the selected graph's target
avoidance; the only produced fact is the exact finite-enumeration survivor
consumed by `[168]`. -/
@[reducible] noncomputable def twoStrandSurvivorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.twoStrandSurvivor
    { Requires := [K .selection, K .coldGenuineSecondStrand]
      Produces := [K .coldTwoStrandSurvivor]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let genuine := (inputs.get (K .coldGenuineSecondStrand)).down
      .cons (key := K .coldTwoStrandSurvivor)
        ⟨by
          classical
          change GenuineSecondStrandStatement data inputs.current.object at genuine
          change TwoStrandSurvivorStatement data inputs.current.object
          obtain ⟨germ, representative, config, neutral, realized⟩ := genuine
          obtain ⟨witness⟩ := realized
          refine ⟨germ, representative, config, neutral, ⟨witness⟩, ?_⟩
          apply Graph.TwoStrand.mem_survivors.2
          refine ⟨witness.length_le, witness.gap_lt, ?_⟩
          intro dyadic
          rcases dyadic with segmentDyadic | pairDyadic
          · let segmentCycle : Graph.CommonEndpointsCycle inputs.current.object :=
              { ends := (witness.left, witness.right)
                forward := witness.firstStrand
                backward := witness.windowSegment
                forward_isPath := witness.firstStrand_isPath
                backward_isPath := witness.windowSegment_isPath
                internallyDisjoint := witness.firstSegment_internallyDisjoint
                nondegenerate := witness.firstSegment_nondegenerate }
            apply selected.1
            refine ⟨segmentCycle.target data.LengthOK ?_⟩
            have accepted : data.LengthOK config.segmentClosing :=
              (data.lengthOK_iff_powerOfTwo config.segmentClosing).2 segmentDyadic
            simpa [segmentCycle, Graph.TwoStrand.Configuration.segmentClosing,
              witness.firstStrand_length, witness.windowSegment_length] using accepted
          · let pairCycle : Graph.CommonEndpointsCycle inputs.current.object :=
              { ends := (witness.left, witness.right)
                forward := witness.firstStrand
                backward := witness.secondStrand
                forward_isPath := witness.firstStrand_isPath
                backward_isPath := witness.secondStrand_isPath
                internallyDisjoint := witness.strands_internallyDisjoint
                nondegenerate := witness.pair_nondegenerate }
            apply selected.1
            refine ⟨pairCycle.target data.LengthOK ?_⟩
            have accepted : data.LengthOK config.pairClosing :=
              (data.lengthOK_iff_powerOfTwo config.pairClosing).2 pairDyadic
            simpa [pairCycle, Graph.TwoStrand.Configuration.pairClosing,
              witness.firstStrand_length, witness.secondStrand_length,
              two_mul] using accepted⟩
        .nil)

/-! ## Node `[168]`, `lem:symmetric-pair-endpoint`

The selected occurrence retained at `[163]` is one of the nine interior
single-stub incidences of its ambient-cubic window.  The two distinct stubs of
a genuine pair force each attachment into the two-endpoint set published by
`coldWindowStubStructureRow`.  Hence the selected occurrence cannot be one of
the pair's four endpoint stubs. -/

noncomputable instance instIncompatibleTwoStrandSurvivorEndpointExclusion :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded) where
  contradiction := fun _residual survivor excluded =>
    excluded.down survivor.down

@[reducible] noncomputable def symmetricPairEndpointExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.symmetricPairEndpointExclusion
    { Requires := [K .coldWindowStubStructure, K .coldTwoStrandSurvivor]
      Produces := [K .coldSymmetricPairExcluded]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let stubStructure := (inputs.get (K .coldWindowStubStructure)).down
      let incoming := (inputs.get (K .coldTwoStrandSurvivor)).down
      .cons (key := K .coldSymmetricPairExcluded)
        ⟨by
          classical
          change TwoStrandSurvivorStatement data inputs.current.object at incoming
          change ¬ TwoStrandSurvivorStatement data inputs.current.object
          intro survivor
          obtain ⟨germ, representative, config, neutral, realized, survives⟩ := survivor
          obtain ⟨witness⟩ := realized
          have windowMember : witness.window ∈
              (canonicalColdWindows data inputs.current.object).filter
                (AmbientCubicWindow data inputs.current.object) :=
            Finset.mem_filter.2 ⟨witness.window_mem, witness.window_cubic⟩
          obtain ⟨ends, _endsSubset, _endsCard, interior, endpoints,
              _interiorCount⟩ := stubStructure witness.window windowMember
          have leftTwo : 2 ≤
              (inputs.current.object.externalNeighbours witness.window
                witness.left).card :=
            Finset.one_lt_card.mpr
              ⟨witness.leftFirst, witness.leftFirst_mem,
                witness.leftSecond, witness.leftSecond_mem,
                witness.leftStubs_distinct⟩
          have rightTwo : 2 ≤
              (inputs.current.object.externalNeighbours witness.window
                witness.right).card :=
            Finset.one_lt_card.mpr
              ⟨witness.rightFirst, witness.rightFirst_mem,
                witness.rightSecond, witness.rightSecond_mem,
                witness.rightStubs_distinct⟩
          have leftEnd : witness.left ∈ ends := by
            by_contra notEnd
            have one := interior witness.left witness.left_mem notEnd
            rw [data.threshold_eq_three] at one
            omega
          have rightEnd : witness.right ∈ ends := by
            by_contra notEnd
            have one := interior witness.right witness.right_mem notEnd
            rw [data.threshold_eq_three] at one
            omega
          have leftEndpointCount :
              (inputs.current.object.externalNeighbours witness.window
                witness.left).card = 2 := by
            have count := endpoints witness.left leftEnd
            simpa [data.threshold_eq_three] using count
          have rightEndpointCount :
              (inputs.current.object.externalNeighbours witness.window
                witness.right).card = 2 := by
            have count := endpoints witness.right rightEnd
            simpa [data.threshold_eq_three] using count
          have selectedInterior :=
            Graph.ColdCorridor.mem_selectedStubs_isInterior
              inputs.current.object witness.origin_mem_window
          have originFoot :
              (ColdGermOccurrence.stub witness.origin).1 = witness.left ∨
                (ColdGermOccurrence.stub witness.origin).1 = witness.right := by
            rcases witness.origin_is_pair_stub with h | h | h | h
            · exact Or.inl (congrArg Prod.fst h)
            · exact Or.inl (congrArg Prod.fst h)
            · exact Or.inr (congrArg Prod.fst h)
            · exact Or.inr (congrArg Prod.fst h)
          rcases originFoot with foot | foot
          · rw [foot] at selectedInterior
            omega
          · rw [foot] at selectedInterior
            omega⟩
        .nil)

/-! ## Node `[165]`, `lem:refined-minimality-swap`: the canonical exchange

The no-arm of `[163]` enters the canonical-replacement case.  This row proves
the manuscript's exchange uniformly: for every neutral configuration, if its
canonical representative `E` is different from the corridor piece `Q`, gluing
`E` into the retained outside context preserves the baseline, target
avoidance, vertex count, and edge count, and replaces `Q` by a strict
predecessor in the fixed canonical piece order.  The refined-minimality
contradiction belongs to node `[166]`.
-/
@[reducible] noncomputable def canonicalReplacementSwapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalReplacementSwap
    { Requires := [K .coldCanonicalNeutralConfiguration]
      Produces := [K .coldCanonicalReplacementSwap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let canonical :=
        (inputs.get (K .coldCanonicalNeutralConfiguration)).down
      .cons (key := K .coldCanonicalReplacementSwap)
        ⟨by
          classical
          change CanonicalNeutralConfigurationStatement data
            inputs.current.object at canonical
          change CanonicalReplacementSwapStatement data inputs.current.object
          obtain ⟨_markedGerm, _markedRepresentative, _markedConfiguration,
            _notRealized⟩ := canonical
          intro germ representative configuration different
          dsimp only
          obtain ⟨_active, representativeReading, equalSize, canonicalPosition,
            sourceAvoids⟩ := configuration
          let baselineInvariant :=
            Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold
          have reconstruction :
              (Graph.glue germ.piece germ.atom.outside).Isomorphic
                inputs.current.object :=
            ⟨germ.atom.reconstructionIso⟩
          have sourceBaseline :
              Graph.MinimumDegreeAtLeast data.threshold
                (Graph.glue germ.piece germ.atom.outside) :=
            (baselineInvariant.iff_of_iso reconstruction).mpr
              inputs.current.baseline
          have swappedBaseline :
              Graph.MinimumDegreeAtLeast data.threshold
                (Graph.glue representative.toPiece germ.atom.outside) :=
            representativeReading.1.2.2 germ.atom.outside sourceBaseline
          have swappedAvoids :
              ¬ Graph.HasCycleWithLength data.LengthOK
                (Graph.glue representative.toPiece germ.atom.outside) := by
            intro hit
            exact sourceAvoids
              ((representativeReading.1.2.1 germ.atom.outside).mp hit)
          have vertexCountEq :
              (Graph.glue representative.toPiece germ.atom.outside).vertexCount =
                inputs.current.object.vertexCount := by
            calc
              (Graph.glue representative.toPiece
                  germ.atom.outside).vertexCount =
                  (Graph.glue germ.piece germ.atom.outside).vertexCount := by
                    simp only [Graph.glue_vertexCount,
                      Graph.CanonicalPiece.toPiece_internalVertexCount]
                    omega
              _ = inputs.current.object.vertexCount :=
                Graph.FiniteObject.vertexCount_eq_of_isomorphic reconstruction
          have edgeCountEq :
              (Graph.glue representative.toPiece germ.atom.outside).edgeCount =
                inputs.current.object.edgeCount := by
            calc
              (Graph.glue representative.toPiece
                  germ.atom.outside).edgeCount =
                  (Graph.glue germ.piece germ.atom.outside).edgeCount :=
                    representativeReading.2
              _ = inputs.current.object.edgeCount :=
                Graph.FiniteObject.edgeCount_eq_of_isomorphic reconstruction
          obtain ⟨representativePrecedes, refinedDecrease⟩ :=
            canonicalPosition.resolve_left different
          exact ⟨swappedBaseline, swappedAvoids, vertexCountEq, edgeCountEq,
            representativePrecedes, refinedDecrease⟩⟩
        .nil)

/-! ## Node `[166]`: refined minimality forces the trivial replacement -/

@[reducible] noncomputable def canonicalReplacementTrivialRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalReplacementTrivial
    { Requires := [K .selection, K .coldCanonicalReplacementSwap]
      Produces := [K .coldCanonicalReplacementTrivial]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let swap := (inputs.get (K .coldCanonicalReplacementSwap)).down
      .cons (key := K .coldCanonicalReplacementTrivial)
        ⟨by
          classical
          change CanonicalReplacementSwapStatement data inputs.current.object at swap
          change CanonicalReplacementTrivialStatement data inputs.current.object
          intro germ representative configuration
          by_contra different
          let swapped := Graph.glue representative.toPiece germ.atom.outside
          obtain ⟨baseline, avoids, _vertexCount, _edgeCount,
              _precedes, refinedDecrease⟩ :=
            swap germ representative configuration different
          have smaller :
              (refinedProgress BranchState Presentation presentation data).Smaller
                swapped inputs.current.object :=
            (refinedProgress_smaller_iff BranchState Presentation presentation data).2
              refinedDecrease
          exact avoids
            (selected.2.refinedMinimal swapped smaller baseline)⟩
        .nil)

/-! ## `lem:refined-minimality-swap`, the size split of the canonical replacement

On the residual where a neutral germ has a canonical replacement piece
`E ≠ Q[x,y]`, the fixed canonical order compares sizes first: either `E` has
strictly fewer internal vertices — then exchanging `Q` for `E` is a strictly
smaller counterexample and the `[4]` minimality closes (node `[165]`) — or `E`
has the same size, which is the tie-break of node `[166]`. -/
noncomputable def canonicalSwapSizeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    (smallerFresh : K .coldCanonicalSwapSmaller ∉ known)
    (sameFresh : K .coldCanonicalSwapSameSize ∉ known) :
    Decision (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize) previous := by
  classical
  let _proper := (previous.get (K .coldCanonicalNeutralConfiguration)).down
  exact Decision.run previous (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize)
    `Hypostructure.Graph.Strategy.Spine.canonicalSwapSizeDichotomy
    (if smaller : ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object,
        germ.Neutral ∧
          (germCanonicalRepresentative data germ).size < germ.piece.internalVertexCount then
      .inl ⟨smaller⟩
    else
      .inr ⟨by
        intro germ neutral lt
        exact smaller ⟨germ, neutral, lt⟩⟩)
    smallerFresh sameFresh

/-! ## The route-8 rate failure, `rem:route8-carrier-margin` read exactly

When the private-carrier rate `τ < 3/13` of node `[120]` fails on a residual that
already carries the hot/cold ledger of the fixed packing, the manuscript's
delicate density interval (row 2 of `tab:cold-branch-ledger`) is handled by the
hot/cold pass; in exact form its residue is decided by the cold family: if the
cold family is nonempty, the failure is carried by cold windows whose selected
corridors are charged as in `[174]`--`[177]` (absorbed germs or genuine germs);
if it is empty, every packed window is hot at the exact skeleton budget and the
rate still fails — the exact budget-edge corner.  This is that decision on the
literal residual. -/
noncomputable def coldFamilyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (positiveFresh : K .coldFamilyPositive ∉ known)
    (emptyFresh : K .coldFamilyEmpty ∉ known) :
    Decision (K .coldFamilyPositive) (K .coldFamilyEmpty) previous := by
  classical
  let _split := (previous.get (K .hotColdPartition)).down
  exact Decision.run previous (K .coldFamilyPositive) (K .coldFamilyEmpty)
    `Hypostructure.Graph.Strategy.Spine.coldFamilyDichotomy
    (if positive : 0 < (canonicalColdWindows data current.object).card then
      .inl ⟨positive⟩
    else
      .inr ⟨Nat.eq_zero_of_not_pos positive⟩)
    positiveFresh emptyFresh

/-! ## `thm:cold-branch-quantitative-closure`: no terminal cold residual

With the germs routed and the table closed, no local terminal cold pattern
remains on this residual: the branch is closed by routing, exactly as the
manuscript's Part XI leaves are drawn. -/
@[reducible] noncomputable def coldBranchClosedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldBranchClosed
    { Requires := [K .coldGermExtraction, K .coldGermRouted,
        K .coldSameInterfaceTable]
      Produces := [K .coldBranchClosed]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let extraction := (inputs.get (K .coldGermExtraction)).down
      let routed := (inputs.get (K .coldGermRouted)).down
      let table := (inputs.get (K .coldSameInterfaceTable)).down
      .cons (key := K .coldBranchClosed)
        ⟨Graph.ColdCorridor.noTerminalColdResidual_of_routing extraction.2
          (fun germ shorter =>
            let routedGerm := routed.2 germ shorter
            ⟨routedGerm.1, routedGerm.2.1⟩)
          table.2.1 table.2.2.1⟩
        .nil)

/-! ## Node `[24]`: `prop:p13-density`, after the cold branch

"cold branch begins; continued at `[145]`--`[157]`; after closure,
`θ ≤ θ_win + o(1)`."  On the `[153]` bounded arm the cold mass is
`C ≤ (1 + (threshold+1)·B_cold)·σ(G)`; with
`lem:hot-failure-cold-mass` (`K .coldMass`,
`bitRate·|𝒫| ≤ bitRate·C + allowance`) and the near-cubic surplus bound
`σ(G) ≤ T(n)` (`K .coldAmbientCubic`) this is the manuscript's window-only
density cap with its exact `o(1)`. -/
@[reducible] noncomputable def densityBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.finiteDensityBudget
    { Requires := [K .coldMass, K .coldMassBounded, K .coldAmbientCubic,
        K .hotColdPartition]
      Produces := [K .densityCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let mass := (inputs.get (K .coldMass)).down
      let bounded := (inputs.get (K .coldMassBounded)).down
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .densityCap)
        ⟨by
          classical
          let object := inputs.current.object
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          let perWindow := coldInteriorBranchExcess data
          have perWindowPos : 0 < perWindow := by
            have order := data.five_le_windowOrder
            simp only [perWindow, coldInteriorBranchExcess,
              Graph.ColdCorridor.branchExcessOf]
            omega
          let overlap := Graph.ColdCorridor.overlapBound data.threshold data.coldSignature
          let highLoss := (data.threshold + 1) * overlap
          have coldBound : cold.card ≤
              (1 + highLoss) * object.degreeSurplus data.threshold := by
            change perWindow * cold.card ≤
              (perWindow + highLoss) * object.degreeSurplus data.threshold at bounded
            have : perWindow * cold.card ≤
                perWindow * ((1 + highLoss) * object.degreeSurplus data.threshold) := by
              refine bounded.trans ?_
              have : perWindow + highLoss ≤ perWindow * (1 + highLoss) := by
                have := Nat.mul_le_mul_right highLoss perWindowPos
                rw [Nat.mul_add]; omega
              rw [← Nat.mul_assoc]
              exact Nat.mul_le_mul_right _ this
            exact Nat.le_of_mul_le_mul_left this perWindowPos
          have surplusBound : object.degreeSurplus data.threshold ≤
              data.surplusThreshold object.vertexCount := by
            change (cold.card ≤ (cold.filter (AmbientCubicWindow data object)).card +
              object.degreeSurplus data.threshold) ∧
              object.degreeSurplus data.threshold ≤
                data.surplusThreshold object.vertexCount at cubic
            exact cubic.2
          have packingCard : packing.card = object.windowPackingNumber data.windowOrder := by
            rcases split with ⟨_, attains, _, _, _, _, _⟩
            exact attains
          change coldWindowBitRate data object * packing.card ≤
            coldWindowBitRate data object * cold.card +
              coldSkeletonAllowance data object at mass
          change 2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
              object.windowPackingNumber data.windowOrder) ≤
            (Graph.dyadicScaleCount object + 1) *
              (data.threshold * object.vertexCount +
                data.surplusThreshold object.vertexCount) +
            data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
              data.surplusThreshold object.vertexCount
          rw [← packingCard]
          have coldTerm : 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
              cold.card ≤
              data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                data.surplusThreshold object.vertexCount := by
            calc 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                  cold.card
                ≤ 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                    ((1 + highLoss) * data.surplusThreshold object.vertexCount) :=
                  Nat.mul_le_mul_left _ (coldBound.trans
                    (Nat.mul_le_mul_left (1 + highLoss) surplusBound))
              _ = data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                    data.surplusThreshold object.vertexCount := by
                  simp only [Data.densitySlack, highLoss, overlap]; ring
          simp only [coldWindowBitRate, coldSkeletonAllowance] at mass
          have key := le_trans mass (Nat.add_le_add_right coldTerm _)
          calc 2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
                packing.card)
              = 2 * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                  packing.card := by ring
            _ ≤ data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                  data.surplusThreshold object.vertexCount +
                (Graph.dyadicScaleCount object + 1) *
                  (data.threshold * object.vertexCount +
                    data.surplusThreshold object.vertexCount) := key
            _ = (Graph.dyadicScaleCount object + 1) *
                  (data.threshold * object.vertexCount +
                    data.surplusThreshold object.vertexCount) +
                data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                  data.surplusThreshold object.vertexCount := by ring⟩
        .nil)


end Hypostructure.Graph.Strategy.Spine
