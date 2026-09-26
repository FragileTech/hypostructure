import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! Node `[149]`: the live-hot overflow arm closes by the entropy comparison.
The density cap is available after the cold branch closes. -/

/-- Node `[150]`: derive the exact cleared cold-mass inequality. -/
@[reducible] noncomputable def coldMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldMass
    { Requires := [K .hotColdPartition, K .coldHotEntropyCap]
      Produces := [K .coldMass]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      let hotBound := (inputs.get (K .coldHotEntropyCap)).down
      .cons (key := K .coldMass)
        ⟨by
          classical
          let packing := canonicalWindowPacking data.toParameters inputs.current.object
          let hot := canonicalHotWindows data.toParameters inputs.current.object
          let cold := canonicalColdWindows data.toParameters inputs.current.object
          let _partition := split
          change coldWindowBitRate data.toParameters inputs.current.object * hot.card ≤
            coldSkeletonAllowance data.toParameters inputs.current.object at hotBound
          have hotSubset : hot ⊆ packing := by
            rcases split with ⟨_, _, _, hotFacts, _, _, _⟩
            exact hotFacts.1
          have count : packing.card = hot.card + cold.card := by
            have := (Finset.card_sdiff_add_card_eq_card hotSubset).symm
            rw [Nat.add_comm] at this
            exact this
          change ColdMassStatement data.toParameters inputs.current.object
          simpa [ColdMassStatement] using
            Graph.ColdCorridor.hotFailure_coldMass
              (coldWindowBitRate data.toParameters inputs.current.object) 0 0
              (coldSkeletonAllowance data.toParameters inputs.current.object)
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
      requiresUnique := by key_fresh
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
          have coldSubset : canonicalColdWindows data.toParameters inputs.current.object ⊆
              canonicalWindowPacking data.toParameters inputs.current.object := by
            intro window member
            exact (coldIff window).mp member |>.1
          change ColdAmbientCubicStatement data.toParameters inputs.current.object
          refine ⟨?_, nearCubic⟩
          let object := inputs.current.object
          let packing := canonicalWindowPacking data.toParameters object
          let cold := canonicalColdWindows data.toParameters object
          letI : FinEnum object.Vertex := object.vertices
          letI : Fintype object.Vertex := inferInstance
          let ambient : Finset object.Vertex := Finset.univ.filter fun vertex =>
            data.threshold < object.degree vertex
          let bad : Finset (Finset object.Vertex) := cold.filter fun window =>
            ¬ AmbientCubicWindow data.toParameters object window
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
            (AmbientCubicWindow data.toParameters object)
          change cold.card ≤
            (cold.filter (AmbientCubicWindow data.toParameters object)).card +
              object.degreeSurplus data.threshold
          rw [← splitCard]
          convert Nat.add_le_add_left badBound
            (cold.filter (AmbientCubicWindow data.toParameters object)).card using 1
          ⟩
        .nil)

/-- Node `[152]`: derive the branch-excess inequality from node `[151]`. -/
@[reducible] noncomputable def coldStubExcessRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldStubExcess
    { Requires := [K .hotColdPartition, K .coldAmbientCubic]
      Produces := [K .coldSelectedBranchExcess,
        K .coldAmbientCubicStubExcess, K .coldStubExcess]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      let exactStubs : ColdAmbientCubicStubExcessStatement data.toParameters
          inputs.current.object := by
        classical
        let object := inputs.current.object
        let packing := canonicalWindowPacking data.toParameters object
        let cold := canonicalColdWindows data.toParameters object
        let cubicWindows := cold.filter (AmbientCubicWindow data.toParameters object)
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
          let packing := canonicalWindowPacking data.toParameters object
          let cold := canonicalColdWindows data.toParameters object
          let cubicWindows := cold.filter (AmbientCubicWindow data.toParameters object)
          rcases split with
            ⟨valid, _attains, _maximal, _hotFacts, coldIff, _hotCold, _cover⟩
          have cubicSubset : cubicWindows ⊆ packing := by
            intro window member
            exact (coldIff window).mp (Finset.mem_filter.mp member).1 |>.1
          have cubicDisjoint : ∀ left ∈ cubicWindows, ∀ right ∈ cubicWindows,
              left ≠ right → Disjoint left right := by
            intro left leftMem right rightMem different
            exact valid.2 left (cubicSubset leftMem) right (cubicSubset rightMem) different
          change ColdSelectedBranchExcessStatement data.toParameters object
          refine ⟨?_, ?_⟩
          · rw [Graph.ColdCorridor.card_allSelectedStubs object cubicWindows
                cubicDisjoint]
            calc
              ∑ window ∈ cubicWindows,
                    ((Graph.ColdCorridor.interiorStubList object window).length - 2) =
                  ∑ _window ∈ cubicWindows,
                    coldInteriorBranchExcess data.toParameters := by
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
              _ = coldInteriorBranchExcess data.toParameters * cubicWindows.card := by
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
              change ColdStubExcessStatement data.toParameters inputs.current.object
              simpa [ColdStubExcessStatement, ColdAmbientCubicStatement] using
                Graph.ColdCorridor.branchExcess_ge_of_cubic
                  (coldInteriorBranchExcess data.toParameters)
                  ((canonicalColdWindows data.toParameters inputs.current.object).filter
                    (AmbientCubicWindow data.toParameters inputs.current.object)).card
                  (canonicalColdWindows data.toParameters inputs.current.object).card
                  (inputs.current.object.degreeSurplus data.threshold) cubic.1⟩
            .nil)))

/-! ## Node `[153]`: the exact finite form of "positive for all sufficiently large `n`"

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
    (if linear : ColdMassLinearStatement data.toParameters current.object then
      .inl ⟨linear⟩
    else
      .inr ⟨by
        change ¬ ((coldInteriorBranchExcess data.toParameters +
            (data.threshold + 1) *
              Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
          current.object.degreeSurplus data.threshold <
            coldInteriorBranchExcess data.toParameters *
              (canonicalColdWindows data.toParameters current.object).card) at linear
        change coldInteriorBranchExcess data.toParameters *
            (canonicalColdWindows data.toParameters current.object).card ≤
          (coldInteriorBranchExcess data.toParameters +
            (data.threshold + 1) *
              Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
            current.object.degreeSurplus data.threshold
        exact Nat.le_of_not_lt linear⟩)
    linearFresh boundedFresh

end Hypostructure.Graph.Strategy.Spine
