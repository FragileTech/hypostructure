import Hypostructure.Graph.Statements.ColdGerm
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily

/-!
# Contracts: the cold return corridors and the neutral germ `[153]`, `[165]`--`[167]`

Proof-agnostic contract lemmas for `def:cold-corridor-first-failure` (the
return corridors and the declared F4 registry), `lem:refined-minimality-swap`,
and `lem:two-strand-check`.  Each lemma is stated over a `Graph.FiniteObject`
with the registered `Parameters` as a parameter and every paper hypothesis
explicit; its conclusion is exactly the statement of the fact it proves.  This
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Node `[153]`, `def:cold-corridor-first-failure`: the cold return
corridors.**  In a bridgeless object every outside component has a corridor at
each entry; a selected branch-excess half-edge whose foot is outside the cold
windows is the entry stub of the corridor of its outside component, otherwise
its foot lies in another cold window; and the selected stubs split exactly by
that alternative. -/
theorem coldReturnCorridors_of_bridgeless (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (bridgeless : BridgelessStatement object)
    (split : HotColdWindowStatement data object) :
    ColdReturnCorridorsStatement data object := by
  classical
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
        change epsilon.1.1 ∈ Graph.ColdCorridor.windowsOf object cubic
        exact selected.1
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
    simpa only [not_not] using partition.symm

/-- **`lem:refined-minimality-swap`: the canonical exchange** (the paper's
universal statement).  For every neutral configuration whose canonical
representative `E` differs from the corridor piece `Q`, gluing `E` into the
retained outside context preserves the baseline, target avoidance, vertex count
and edge count, and replaces `Q` by a strict predecessor in the fixed canonical
piece order. -/
theorem canonicalReplacementSwap_at (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (representative : Graph.CanonicalPiece germ.atom.interface)
    (configuration :
      NeutralEqualLengthTerminalConfigurationAt data object germ representative)
    (different : representative ≠ germ.piece.toCanonical) :
    let swapped := Graph.glue representative.toPiece germ.atom.outside
    Graph.MinimumDegreeAtLeast data.threshold swapped ∧
      ¬ Graph.HasCycleWithLength data.LengthOK swapped ∧
      swapped.vertexCount = object.vertexCount ∧
      swapped.edgeCount = object.edgeCount ∧
      Graph.CanonicalPiece.Precedes representative germ.piece.toCanonical ∧
      RefinedLexicographicallySmaller swapped object := by
  classical
  dsimp only
  obtain ⟨_active, representativeReading, equalSize, canonicalPosition,
    sourceAvoids⟩ := configuration
  let baselineInvariant :=
    Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold
  have reconstruction :
      (Graph.glue germ.piece germ.atom.outside).Isomorphic object :=
    ⟨germ.atom.reconstructionIso⟩
  have sourceBaseline :
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue germ.piece germ.atom.outside) :=
    (baselineInvariant.iff_of_iso reconstruction).mpr baseline
  have swappedBaseline :
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue representative.toPiece germ.atom.outside) :=
    representativeReading.1.2.2 sourceBaseline
  have swappedAvoids :
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue representative.toPiece germ.atom.outside) := by
    intro hit
    exact sourceAvoids
      (representativeReading.1.2.1.mp hit)
  have vertexCountEq :
      (Graph.glue representative.toPiece germ.atom.outside).vertexCount =
        object.vertexCount := by
    calc
      (Graph.glue representative.toPiece
          germ.atom.outside).vertexCount =
          (Graph.glue germ.piece germ.atom.outside).vertexCount := by
            simp only [Graph.glue_vertexCount,
              Graph.CanonicalPiece.toPiece_internalVertexCount]
            omega
      _ = object.vertexCount :=
        Graph.FiniteObject.vertexCount_eq_of_isomorphic reconstruction
  have edgeCountEq :
      (Graph.glue representative.toPiece germ.atom.outside).edgeCount =
        object.edgeCount := by
    calc
      (Graph.glue representative.toPiece
          germ.atom.outside).edgeCount =
          (Graph.glue germ.piece germ.atom.outside).edgeCount :=
            representativeReading.2
      _ = object.edgeCount :=
        Graph.FiniteObject.edgeCount_eq_of_isomorphic reconstruction
  obtain ⟨representativePrecedes, refinedDecrease⟩ :=
    canonicalPosition.resolve_left different
  exact ⟨swappedBaseline, swappedAvoids, vertexCountEq, edgeCountEq,
    representativePrecedes, refinedDecrease⟩

/-- **Node `[165]`, at the marked configuration.**  On node `[163]`'s no-arm
the marked configuration of node `[406]` exists; the canonical exchange is the
universal lemma at it. -/
theorem canonicalReplacementSwap_of_neutral (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (neutral : CanonicalNeutralConfigurationStatement data object) :
    CanonicalReplacementSwapStatement data object := by
  obtain ⟨marked, markedEq, _noStrand⟩ := neutral
  exact ⟨marked, markedEq,
    canonicalReplacementSwap_at data object baseline marked.1 marked.2
      (markedNeutralGerm?_spec_of_eq_some data object markedEq)⟩

/-- **Node `[166]`: refined minimality forces the trivial replacement.**  A
different canonical representative would give, by the exchange of `[165]`, a
baseline target-avoiding object strictly smaller in the refined `(|V|,|E|,Φ)`
order, contradicting the refined minimality of the selected object. -/
theorem canonicalReplacementTrivial_of_swap
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (swap : CanonicalReplacementSwapStatement data object) :
    CanonicalReplacementTrivialStatement data object := by
  classical
  obtain ⟨marked, markedEq, exchange⟩ := swap
  refine ⟨marked, markedEq, ?_⟩
  by_contra different
  let swapped := Graph.glue marked.2.toPiece marked.1.atom.outside
  obtain ⟨baseline, avoids, _vertexCount, _edgeCount,
      _precedes, refinedDecrease⟩ := exchange different
  have smaller :
      (refinedProgress BranchState Presentation presentation data).Smaller
        swapped object :=
    (refinedProgress_smaller_iff BranchState Presentation presentation data).2
      refinedDecrease
  exact avoids
    (selected.2.refinedMinimal swapped smaller baseline)

/-- **`lem:refined-minimality-swap`, the same-size arm** at the marked
configuration is the exact complement of the strictly-smaller arm. -/
theorem coldCanonicalSwapSameSize_of_not_smaller (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (neutral : CanonicalNeutralConfigurationStatement data object)
    (smaller : ¬ ColdCanonicalSwapSmallerStatement data object) :
    ColdCanonicalSwapSameSizeStatement data object := by
  obtain ⟨marked, markedEq, _noStrand⟩ := neutral
  exact ⟨marked, markedEq, fun lt => smaller ⟨marked, markedEq, lt⟩⟩

/-- **Node `[167]`, `lem:two-strand-check`: the literal finite check.**  The
genuine arm retains the two ambient strands and the window segment; they close
cycles of lengths `ℓ + d` and `2ℓ`.  With the dyadic target, either dyadic arm
is an accepted cycle, which the target-avoiding object does not have, so the
configuration is a finite-enumeration survivor. -/
theorem twoStrandSurvivor_of_genuine (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (lengthOK_iff_powerOfTwo : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (genuine : GenuineSecondStrandStatement data object) :
    TwoStrandSurvivorStatement data object := by
  classical
  change GenuineSecondStrandStatement data object at genuine
  change TwoStrandSurvivorStatement data object
  obtain ⟨marked, markedEq, config, realized⟩ := genuine
  obtain ⟨witness⟩ := realized
  refine ⟨marked, markedEq, config, ⟨witness⟩, ?_⟩
  apply Graph.TwoStrand.mem_survivors.2
  refine ⟨witness.length_le, witness.gap_lt, ?_⟩
  intro dyadic
  rcases dyadic with segmentDyadic | pairDyadic
  · let segmentCycle : Graph.CommonEndpointsCycle object :=
      { ends := (witness.left, witness.right)
        forward := witness.firstStrand
        backward := witness.windowSegment
        forward_isPath := witness.firstStrand_isPath
        backward_isPath := witness.windowSegment_isPath
        internallyDisjoint := witness.firstSegment_internallyDisjoint
        nondegenerate := witness.firstSegment_nondegenerate }
    apply avoids
    refine ⟨segmentCycle.target data.LengthOK ?_⟩
    have accepted : data.LengthOK config.segmentClosing :=
      (lengthOK_iff_powerOfTwo config.segmentClosing).2 segmentDyadic
    simpa [segmentCycle, Graph.TwoStrand.Configuration.segmentClosing,
      witness.firstStrand_length, witness.windowSegment_length] using accepted
  · let pairCycle : Graph.CommonEndpointsCycle object :=
      { ends := (witness.left, witness.right)
        forward := witness.firstStrand
        backward := witness.secondStrand
        forward_isPath := witness.firstStrand_isPath
        backward_isPath := witness.secondStrand_isPath
        internallyDisjoint := witness.strands_internallyDisjoint
        nondegenerate := witness.pair_nondegenerate }
    apply avoids
    refine ⟨pairCycle.target data.LengthOK ?_⟩
    have accepted : data.LengthOK config.pairClosing :=
      (lengthOK_iff_powerOfTwo config.pairClosing).2 pairDyadic
    simpa [pairCycle, Graph.TwoStrand.Configuration.pairClosing,
      witness.firstStrand_length, witness.secondStrand_length,
      two_mul] using accepted

/-- **The symmetric endpoint pair is excluded.**  On the cubic baseline every
window vertex with two external stubs is an end vertex, while the origin of a
two-strand configuration is a selected interior stub whose foot is one of the
two pair endpoints; so no two-strand survivor exists. -/
theorem coldSymmetricPairExcluded_of_stubStructure (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (thresholdEq : data.threshold = 3)
    (stubStructure : ColdWindowStubStructureStatement data object) :
    ColdSymmetricPairExcludedStatement data object := by
  classical
  change ¬ TwoStrandSurvivorStatement data object
  intro survivor
  obtain ⟨⟨germ, representative⟩, -, config, realized, -⟩ := survivor
  obtain ⟨witness⟩ := realized
  have windowMember : witness.window ∈
      (canonicalColdWindows data object).filter
        (AmbientCubicWindow data object) :=
    Finset.mem_filter.2 ⟨witness.window_mem, witness.window_cubic⟩
  obtain ⟨ends, _endsSubset, _endsCard, interior, endpoints,
      _interiorCount⟩ := stubStructure witness.window windowMember
  have leftTwo : 2 ≤
      (object.externalNeighbours witness.window witness.left).card :=
    Finset.one_lt_card.mpr
      ⟨witness.leftFirst, witness.leftFirst_mem,
        witness.leftSecond, witness.leftSecond_mem,
        witness.leftStubs_distinct⟩
  have rightTwo : 2 ≤
      (object.externalNeighbours witness.window witness.right).card :=
    Finset.one_lt_card.mpr
      ⟨witness.rightFirst, witness.rightFirst_mem,
        witness.rightSecond, witness.rightSecond_mem,
        witness.rightStubs_distinct⟩
  have leftEnd : witness.left ∈ ends := by
    by_contra notEnd
    have one := interior witness.left witness.left_mem notEnd
    omega
  have rightEnd : witness.right ∈ ends := by
    by_contra notEnd
    have one := interior witness.right witness.right_mem notEnd
    omega
  have leftEndpointCount :
      (object.externalNeighbours witness.window witness.left).card = 2 := by
    have count := endpoints witness.left leftEnd
    omega
  have rightEndpointCount :
      (object.externalNeighbours witness.window witness.right).card = 2 := by
    have count := endpoints witness.right rightEnd
    omega
  have selectedInterior :=
    Graph.ColdCorridor.mem_selectedStubs_isInterior
      object witness.origin_mem_window
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
    omega

end Hypostructure.Graph.Contracts.Spine
