import Hypostructure.Graph.Strategy.SpineRows
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
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    (belowFresh : K .coldRoute8Below ∉ known)
    (atOrAboveFresh : K .coldRoute8AtOrAbove ∉ known) :
    Decision (K .coldRoute8Below) (K .coldRoute8AtOrAbove) previous := by
  classical
  let _split := (previous.get (K .coldWindowLedgerSplit)).down
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
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    (overflowFresh : K .coldHotEntropyOverflow ∉ known)
    (capFresh : K .coldHotEntropyCap ∉ known) :
    Decision (K .coldHotEntropyOverflow) (K .coldHotEntropyCap) previous := by
  classical
  let _split := (previous.get (K .coldWindowLedgerSplit)).down
  exact Decision.run previous (K .coldHotEntropyOverflow) (K .coldHotEntropyCap)
    `Hypostructure.Graph.Strategy.Spine.coldHotEntropyDichotomy
    (if overflow : ColdHotEntropyOverflowStatement data current.object then
      .inl ⟨overflow⟩
    else
      .inr ⟨Nat.le_of_not_lt overflow⟩)
    overflowFresh capFresh

/-! Node `[149]`: the former row that published `K .densityCap` on `[148]`'s
overflow arm from a cap on all windows is deleted; on the manuscript's DAG the
live-hot overflow arm closes by the entropy comparison and the density cap is
available only after the cold branch closes. -/

/-- Node `[145]`: append the canonical hot/cold split. -/
@[reducible] noncomputable def coldWindowLedgerSplitRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldWindowLedgerSplit
    { Requires := [K .hotColdPartition]
      Produces := [K .coldWindowLedgerSplit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldWindowLedgerSplit)
        ⟨(inputs.get (K .hotColdPartition)).down⟩
        .nil)

/-- Node `[150]`: derive the exact cleared cold-mass inequality. -/
@[reducible] noncomputable def coldMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldMass
    { Requires := [K .coldWindowLedgerSplit, K .coldHotEntropyCap]
      Produces := [K .coldMass]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
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
    { Requires := [K .coldWindowLedgerSplit, K .surplusAtOrBelow,
        K .selection]
      Produces := [K .coldAmbientCubic]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
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
    { Requires := [K .coldAmbientCubic]
      Produces := [K .coldStubExcess]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      .cons (key := K .coldStubExcess)
        ⟨by
          classical
          change ColdStubExcessStatement data inputs.current.object
          simpa [ColdStubExcessStatement, ColdAmbientCubicStatement] using
            Graph.ColdCorridor.branchExcess_ge_of_cubic
              (Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data))
              ((canonicalColdWindows data inputs.current.object).filter
                (AmbientCubicWindow data inputs.current.object)).card
              (canonicalColdWindows data inputs.current.object).card
              (inputs.current.object.degreeSurplus data.threshold) cubic.1⟩
        .nil)

/-! ## Node `[153]`: the exact finite form of "positive for sufficiently large n"

`lem:cold-germ-extraction` bounds the germ family from below by
`13C/D_cold − o(n)`; `thm:cold-branch-quantitative-closure` uses that "the
displayed lower bound is positive for all sufficiently large `n`".  In exact
finite form the two `o(n)` losses of `[151]`--`[153]` are `perWindow·σ(G)` (the
non-ambient-cubic windows) and `B_cold·σ(G)` (the high-degree candidate loss), so
the branch that forces a germ is `(perWindow + B_cold)·σ(G) < perWindow·C`, and
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
        change ¬ ((Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) +
            Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
          current.object.degreeSurplus data.threshold <
            Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) *
              (canonicalColdWindows data current.object).card) at linear
        change Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) *
            (canonicalColdWindows data current.object).card ≤
          (Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) +
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
    { Requires := [K .bridgeless]
      Produces := [K .coldReturnCorridors]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridgeless := (inputs.get (K .bridgeless)).down
      .cons (key := K .coldReturnCorridors)
        ⟨fun component outside entry =>
          ⟨Graph.ColdCorridor.corridorOfOutsideComponent inputs.current.object
            (coldAmbientCubicSupport data inputs.current.object) component
            outside bridgeless entry, rfl⟩⟩
        .nil)

/-! ## Node `[153]`, `lem:cold-corridor-first-failure`: cut-states and routing

On the linear arm every selected branch-excess half-edge has a cold return
corridor whose first failure is one of (F1)--(F5).  This row publishes the
cut-state facts of `def:cold-corridor-first-failure` and the routing of
(F1)--(F4) together with the existence of a first failure, exactly as the
lemma states them, from the selected object's target avoidance (`K .selection`)
and `cor:uncompressible` (`K .uncompressible`).  Nothing is constructed: each
clause is universally quantified over the object's own corridors. -/
@[reducible] noncomputable def coldFirstFailureRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureRouting
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .coldCorridorState, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression,
        K .coldFailureHandoff, K .coldFailureRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .coldCorridorState)
        ⟨by
          intro presentation
          refine ⟨?_, ?_, ?_⟩
          · intro left right same coordinate inside
            exact presentation.reading_eq_of_state_eq same coordinate inside
          · intro segments
            exact presentation.exists_state_eq_of_stateBound_lt segments
          · intro boundary carrier left right
            exact ⟨fun excluded same =>
                presentation.contextEquivalent_of_state_eq excluded same,
              fun same separated =>
                presentation.firstFailureResponse_of_not_contextEquivalent same
                  separated⟩⟩
        (.cons (key := K .coldFailureCycle)
          ⟨by
            intro windows component corridor order window segment failure
            exact selected.1
              (Graph.ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle
                failure)⟩
          (.cons (key := K .coldFailureDefect)
            ⟨by
              intro windows component corridor presentation index boundary carrier
                left right
              exact ⟨fun Profile profile failure =>
                  Graph.ColdCorridor.Corridor.not_targetComplete_of_firstFailureDefect
                    (Profile := Profile) (profile := profile) failure,
                fun excluded same =>
                  Graph.ColdCorridor.Corridor.contextEquivalent_of_not_firstFailureDefect
                    excluded same⟩⟩
            (.cons (key := K .coldFailureCompression)
              ⟨by
                intro windows component corridor presentation index support
                exact Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
                  uncompressible⟩
              (.cons (key := K .coldFailureHandoff)
                ⟨by
                  intro windows component corridor Handoff segment failure
                  exact Graph.ColdCorridor.Corridor.handoff_mem failure⟩
                (.cons (key := K .coldFailureRouting)
                  ⟨by
                    change ColdFailureRoutingStatement data inputs.current.object
                    refine ⟨fun _packing _hot cold _split => ⟨_, rfl⟩, ?_⟩
                    intro windows component corridor presentation index injective
                    exact corridor.exists_firstFailure presentation index injective⟩
                  .nil))))))

/-! ## Node `[153]`, `lem:cold-germ-extraction`: exchange bound and extraction

The first-failure cold exchange is bounded by `M_cold` (`exchange_card_le`),
and a candidate family with the paper's overlap bound has a positive disjoint
subfamily of size at least `|𝒢_cand|/D_cold` (greedy independent set,
`coldGermExtractionLocal`).  Both are published on the same residual, on top of
the routing facts. -/
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
          ⟨⟨exchange, Graph.ColdCorridor.coldGermExtractionLocal⟩⟩
          .nil))

/-! ## Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate family

*"Every selected branch-excess half-edge yields a bounded germ … at most
`3(Q_cold + 1)` selected half-edges yield the same germ … the high-degree loss
is `o(n)` … the candidate family has overlap degree at most `M_cold·B_cold`, so
a disjoint subfamily of size at least `|𝒢_cand|/D_cold` exists."*  On the
current residual: the candidate family is the family of first-failure exchange
germs of the selected branch-excess half-edges of the ambient-cubic cold windows
(`candidateGerms`), read through `lem:bridgeless` and the ledger's window
partition; its count is `selected_le_candidates`, its overlap bound is
`candidateGerms_overlap_le`, its positivity is node `[153]`'s linear arm, and its
disjoint subfamily is the ledger's `lem:cold-germ-extraction`. -/
set_option maxHeartbeats 800000 in
@[reducible] noncomputable def coldGermCandidatesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermCandidates
    { Requires := [K .bridgeless, K .coldWindowLedgerSplit, K .coldAmbientCubic,
        K .coldMassLinear, K .coldGermExtraction]
      Produces := [K .coldGermCandidates]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridgeless := (inputs.get (K .bridgeless)).down
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
      let ambient := (inputs.get (K .coldAmbientCubic)).down
      let linear := (inputs.get (K .coldMassLinear)).down
      let extraction := (inputs.get (K .coldGermExtraction)).down
      .cons (key := K .coldGermCandidates)
        ⟨by
          classical
          let object := inputs.current.object
          have three := data.threshold_eq_three
          have baseline : Graph.MinimumDegreeAtLeast 3 object := by
            have := inputs.current.baseline
            change Graph.MinimumDegreeAtLeast data.threshold object at this
            rw [three] at this
            exact this
          have large : 2 < object.vertexCount :=
            Graph.ColdCorridor.two_lt_vertexCount_of_minDegree baseline
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          let cubic := cold.filter (AmbientCubicWindow data object)
          have cubicSub : cubic ⊆ packing :=
            (Finset.filter_subset _ _).trans Finset.sdiff_subset
          have valid : object.IsWindowPacking data.windowOrder packing := split.1
          have induced : ∀ window ∈ cubic, object.InducesWindow data.windowOrder window :=
            fun window member => valid.1 window (cubicSub member)
          have disjoint : ∀ left ∈ cubic, ∀ right ∈ cubic, left ≠ right →
              Disjoint left right :=
            fun left leftMem right rightMem => valid.2 left (cubicSub leftMem) right
              (cubicSub rightMem)
          have windowsCubic : ∀ vertex ∈ Graph.ColdCorridor.windowsOf object cubic,
              object.degree vertex = 3 := by
            intro vertex member
            obtain ⟨window, windowMem, vertexMem⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object cubic vertex).1 member
            have := (Finset.mem_filter.1 windowMem).2 vertex vertexMem
            rw [three] at this
            exact this
          have perWindowEq : Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) =
              3 * data.windowOrder - 2 * (data.windowOrder - 1) - 2 := by
            simp only [Graph.ColdCorridor.branchExcessOf, coldExternalStubCount, three]
          have coldCount : cold.card ≤ cubic.card + object.degreeSurplus 3 := by
            change cold.card ≤ cubic.card + object.degreeSurplus data.threshold ∧ _ at ambient
            rw [three] at ambient
            exact ambient.1
          change (Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) +
              Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
              object.degreeSurplus data.threshold <
            Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) * cold.card
            at linear
          change ColdExchangeBoundStatement data object ∧
            Graph.ColdCorridor.ColdGermExtractionLocal data.coldSignature
              data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object at extraction
          rw [three] at linear extraction
          change ColdGermCandidatesStatement data object
          simp only [ColdGermCandidatesStatement]
          rw [three]
          have count := Graph.ColdCorridor.selected_le_candidates data.coldSignature
            (Graph.HasCycleWithLength data.LengthOK) object cubic baseline bridgeless large
            induced disjoint windowsCubic
          rw [← perWindowEq] at count
          let candidates := Graph.ColdCorridor.candidateGerms data.coldSignature 3
            (Graph.HasCycleWithLength data.LengthOK) object cubic baseline bridgeless large
          have candidateFamily : Graph.ColdCorridor.CandidateGermFamily data.coldSignature 3
              (Graph.MinimumDegreeAtLeast 3) (Graph.HasCycleWithLength data.LengthOK)
              object candidates := by
            refine ⟨?_, ?_⟩
            · by_contra empty
              have zero : candidates.card = 0 := Nat.eq_zero_of_not_pos empty
              rw [zero, Nat.mul_zero, Nat.zero_add] at count
              have := Nat.mul_le_mul_left
                (Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data)) coldCount
              rw [Nat.mul_add, Nat.add_mul] at *
              omega
            · intro candidate member
              have overlap := Graph.ColdCorridor.candidateGerms_overlap_le data.coldSignature
                (Graph.HasCycleWithLength data.LengthOK) object cubic baseline bridgeless large
                candidate member
              convert overlap using 2
              exact Finset.filter_congr_decidable _ _ _
          obtain ⟨disjointFamily, extracted⟩ := extraction.2 candidates candidateFamily
          exact ⟨candidates, disjointFamily, candidateFamily, extracted, count⟩⟩
        .nil)

/-! ## Nodes `[174]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ split

On the absorbed-germ residual (`[173]`'s no arm) the linear cold count of
`[174]` is not needed by the extraction: node `[175]` decides, per the selected
branch-excess half-edges of the ambient-cubic cold windows, whether some
first-failure exchange germ has a subcubic support.  If one does, the candidate
family of `lem:cold-germ-extraction` is positive and the germs are routed as in
`[153]`--`[157]` (node `[176]`); if none does, every selected corridor meets a
vertex of degree above the threshold — a heavy centre by node `[10]` — and the
half-edge is decorated handoff fan data for Type B (node `[177]`,
`K .absorbedGermFanData`).  This is that decision on the literal residual; its
yes arm publishes exactly `K .coldGermCandidates` (the count clause is
`selected_le_candidates`, the overlap clause `candidateGerms_overlap_le`, the
positivity the decision itself, the extraction `K .coldGermExtraction`). -/
noncomputable def absorbedGermDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    [FactKeys.Has (K .coldGermExtraction) known]
    (candidatesFresh : K .coldGermCandidates ∉ known)
    (absorbedFresh : K .absorbedGermFanData ∉ known) :
    Decision (K .coldGermCandidates) (K .absorbedGermFanData) previous := by
  classical
  let bridgeless := (previous.get (K .bridgeless)).down
  let split := (previous.get (K .coldWindowLedgerSplit)).down
  let extraction := (previous.get (K .coldGermExtraction)).down
  let object := current.object
  have three := data.threshold_eq_three
  have baseline3 : Graph.MinimumDegreeAtLeast 3 object := by
    have := current.baseline
    change Graph.MinimumDegreeAtLeast data.threshold object at this
    rw [three] at this
    exact this
  have large : 2 < object.vertexCount :=
    Graph.ColdCorridor.two_lt_vertexCount_of_minDegree baseline3
  let packing := canonicalWindowPacking data object
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let candidates := Graph.ColdCorridor.candidateGerms data.coldSignature 3
    (Graph.HasCycleWithLength data.LengthOK) object cubic baseline3 bridgeless large
  exact Decision.run previous (K .coldGermCandidates) (K .absorbedGermFanData)
    `Hypostructure.Graph.Strategy.Spine.absorbedGermDichotomy
    (if positive : 0 < candidates.card then
      .inl ⟨by
        have cubicSub : cubic ⊆ packing :=
          (Finset.filter_subset _ _).trans Finset.sdiff_subset
        have valid : object.IsWindowPacking data.windowOrder packing := split.1
        have induced : ∀ window ∈ cubic, object.InducesWindow data.windowOrder window :=
          fun window member => valid.1 window (cubicSub member)
        have disjoint : ∀ left ∈ cubic, ∀ right ∈ cubic, left ≠ right →
            Disjoint left right :=
          fun left leftMem right rightMem => valid.2 left (cubicSub leftMem) right
            (cubicSub rightMem)
        have windowsCubic : ∀ vertex ∈ Graph.ColdCorridor.windowsOf object cubic,
            object.degree vertex = 3 := by
          intro vertex member
          obtain ⟨window, windowMem, vertexMem⟩ :=
            (Graph.ColdCorridor.mem_windowsOf object cubic vertex).1 member
          have := (Finset.mem_filter.1 windowMem).2 vertex vertexMem
          rw [three] at this
          exact this
        have perWindowEq : Graph.ColdCorridor.branchExcessOf (coldExternalStubCount data) =
            3 * data.windowOrder - 2 * (data.windowOrder - 1) - 2 := by
          simp only [Graph.ColdCorridor.branchExcessOf, coldExternalStubCount, three]
        change ColdExchangeBoundStatement data object ∧
          Graph.ColdCorridor.ColdGermExtractionLocal data.coldSignature
            data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object at extraction
        rw [three] at extraction
        change ColdGermCandidatesStatement data object
        simp only [ColdGermCandidatesStatement]
        rw [three]
        have count := Graph.ColdCorridor.selected_le_candidates data.coldSignature
          (Graph.HasCycleWithLength data.LengthOK) object cubic baseline3 bridgeless large
          induced disjoint windowsCubic
        rw [← perWindowEq] at count
        have candidateFamily : Graph.ColdCorridor.CandidateGermFamily data.coldSignature 3
            (Graph.MinimumDegreeAtLeast 3) (Graph.HasCycleWithLength data.LengthOK)
            object candidates := by
          refine ⟨positive, ?_⟩
          intro candidate member
          have overlap := Graph.ColdCorridor.candidateGerms_overlap_le data.coldSignature
            (Graph.HasCycleWithLength data.LengthOK) object cubic baseline3 bridgeless large
            candidate member
          convert overlap using 2
          exact Finset.filter_congr_decidable _ _ _
        obtain ⟨disjointFamily, extracted⟩ := extraction.2 candidates candidateFamily
        exact ⟨candidates, disjointFamily, candidateFamily, extracted, count⟩⟩
    else
      .inr ⟨by
        change AbsorbedGermFanDataStatement data object
        simp only [AbsorbedGermFanDataStatement]
        rw [three]
        intro baseline' bridgeless' large' stub
        have empty : candidates = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_not_pos positive)
        by_contra none
        push_neg at none
        have member : Graph.ColdCorridor.stubGerm data.coldSignature 3
            (Graph.HasCycleWithLength data.LengthOK) object cubic baseline3 bridgeless large
              stub ∈ candidates := by
          simp only [candidates, Graph.ColdCorridor.candidateGerms, Finset.mem_filter,
            Finset.mem_image, Finset.mem_attach, true_and]
          exact ⟨⟨stub, rfl⟩, none⟩
        rw [empty] at member
        exact Finset.notMem_empty _ member⟩)
    candidatesFresh absorbedFresh

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
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .coldGermRealized, K .coldGermDistinguished,
        K .coldGermSilent, K .coldGermRouted]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
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
        ⟨⟨notRealizing, fun germ => germ.trichotomy⟩⟩
        (.cons (key := K .coldGermDistinguished)
          ⟨fun germ Profile profile distinguishing =>
            germ.not_targetComplete_of_distinguishing profile distinguishing⟩
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
              ⟨fun germ shorter =>
                have distinguishing :=
                  Graph.ColdCorridor.boundedGerm_not_survives notRealizing notSilent
                    germ shorter
                ⟨distinguishing, fun Profile profile =>
                  germ.not_targetComplete_of_distinguishing profile distinguishing⟩⟩
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
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .coldSameInterfaceTable]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
          (Graph.HasCycleWithLength data.LengthOK) :=
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      .cons (key := K .coldSameInterfaceTable)
        ⟨⟨fun Handoff row =>
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

/-! ## Node `[167]`: the stub structure of the ambient-cubic cold windows

`lem:cold-window-stub-excess` counted `15` external stubs per ambient-cubic
window; here they are located: the two path endpoints carry `δ − 1` stubs each
and every interior vertex carries `δ − 2` (`Graph/WindowStubStructure.lean`).
This is what the symmetric-pair analysis of the dense residual charges: two
internally disjoint strands leaving one attachment vertex need two stubs there,
so a genuine symmetric strand pair (`[167]`) attaches only at endpoints, a window
carries at most one, and the `(order − 2)(δ − 2)` interior stubs are asymmetric
single-stub attachments. -/
@[reducible] noncomputable def coldWindowStubStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldWindowStubStructure
    { Requires := [K .coldWindowLedgerSplit]
      Produces := [K .coldWindowStubStructure]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
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
    { Requires := [K .selection, K .coldWindowLedgerSplit]
      Produces := [K .blockedClassMember]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := (inputs.get (K .selection)).down.1
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
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
symmetry.  The manuscript splits it by the nature of its second representative:
either `E` is a canonical replacement piece different from the corridor piece
`Q[x,y]` (node `[165]`, closed by the refined minimality of
`lem:refined-minimality-swap`), or every neutral germ has `E = Q[x,y]` (the
state that minimality forces; on it the neutral row exchanges nothing, and a
genuine second *strand* is excluded at interior selected half-edges by the stub
structure `[167]`--`[168]`).  This is that decision on the literal residual. -/
noncomputable def neutralGermSymmetryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldWindowStubStructure) known]
    (properFresh : K .coldProperNeutralGerm ∉ known)
    (trivialFresh : K .coldTrivialNeutralGerms ∉ known) :
    Decision (K .coldProperNeutralGerm) (K .coldTrivialNeutralGerms) previous := by
  classical
  let _structure := (previous.get (K .coldWindowStubStructure)).down
  exact Decision.run previous (K .coldProperNeutralGerm) (K .coldTrivialNeutralGerms)
    `Hypostructure.Graph.Strategy.Spine.neutralGermSymmetryDichotomy
    (if proper : ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object,
        germ.Neutral ∧
          Graph.CanonicalPiece.Precedes (germCanonicalRepresentative data germ)
            germ.piece.toCanonical then
      .inl ⟨proper⟩
    else
      .inr ⟨by
        intro germ neutral precedes
        exact proper ⟨germ, neutral, precedes⟩⟩)
    properFresh trivialFresh

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
    [FactKeys.Has (K .coldProperNeutralGerm) known]
    (smallerFresh : K .coldCanonicalSwapSmaller ∉ known)
    (sameFresh : K .coldCanonicalSwapSameSize ∉ known) :
    Decision (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize) previous := by
  classical
  let _proper := (previous.get (K .coldProperNeutralGerm)).down
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
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    (positiveFresh : K .coldFamilyPositive ∉ known)
    (emptyFresh : K .coldFamilyEmpty ∉ known) :
    Decision (K .coldFamilyPositive) (K .coldFamilyEmpty) previous := by
  classical
  let _split := (previous.get (K .coldWindowLedgerSplit)).down
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
        ⟨Graph.ColdCorridor.noTerminalColdResidual_of_routing extraction.2 routed
          table.1 table.2.1⟩
        .nil)

/-! ## Node `[24]`: `prop:p13-density`, after the cold branch

"cold branch begins; continued at `[145]`--`[157]`; after closure,
`θ ≤ θ_win + o(1)`."  On the `[153]` bounded arm the cold mass is
`C ≤ (1 + B_cold)·σ(G)`; with `lem:hot-failure-cold-mass` (`K .coldMass`,
`bitRate·|𝒫| ≤ bitRate·C + allowance`) and the near-cubic surplus bound
`σ(G) ≤ T(n)` (`K .coldAmbientCubic`) this is the manuscript's window-only
density cap with its exact `o(1)`. -/
@[reducible] noncomputable def densityBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.finiteDensityBudget
    { Requires := [K .coldMass, K .coldMassBounded, K .coldAmbientCubic,
        K .coldWindowLedgerSplit]
      Produces := [K .densityCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let mass := (inputs.get (K .coldMass)).down
      let bounded := (inputs.get (K .coldMassBounded)).down
      let cubic := (inputs.get (K .coldAmbientCubic)).down
      let split := (inputs.get (K .coldWindowLedgerSplit)).down
      .cons (key := K .densityCap)
        ⟨by
          classical
          let object := inputs.current.object
          let packing := canonicalWindowPacking data object
          let cold := canonicalColdWindows data object
          let perWindow := Graph.ColdCorridor.branchExcessOf
            (coldExternalStubCount data)
          have perWindowPos : 0 < perWindow := by
            have order := data.windowOrder_pos
            have three := data.three_le_threshold
            have : data.threshold * data.windowOrder ≥ 3 * data.windowOrder :=
              Nat.mul_le_mul_right _ three
            simp only [perWindow, Graph.ColdCorridor.branchExcessOf,
              coldExternalStubCount]
            omega
          let overlap := Graph.ColdCorridor.overlapBound data.threshold data.coldSignature
          have coldBound : cold.card ≤ (1 + overlap) * object.degreeSurplus data.threshold := by
            change perWindow * cold.card ≤
              (perWindow + overlap) * object.degreeSurplus data.threshold at bounded
            have : perWindow * cold.card ≤
                perWindow * ((1 + overlap) * object.degreeSurplus data.threshold) := by
              refine bounded.trans ?_
              have : perWindow + overlap ≤ perWindow * (1 + overlap) := by
                have := Nat.mul_le_mul_right overlap perWindowPos
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
                    ((1 + overlap) * data.surplusThreshold object.vertexCount) :=
                  Nat.mul_le_mul_left _ (coldBound.trans
                    (Nat.mul_le_mul_left (1 + overlap) surplusBound))
              _ = data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
                    data.surplusThreshold object.vertexCount := by
                  simp only [Data.densitySlack, overlap]; ring
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
