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
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let genuine := (inputs.get (K .coldGenuineSecondStrand)).down
      .cons (key := K .coldTwoStrandSurvivor)
        ⟨by
          classical
          change GenuineSecondStrandStatement data.toParameters inputs.current.object at genuine
          change TwoStrandSurvivorStatement data.toParameters inputs.current.object
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

@[reducible] noncomputable def symmetricPairEndpointExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.symmetricPairEndpointExclusion
    { Requires := [K .coldWindowStubStructure, K .coldTwoStrandSurvivor]
      Produces := [K .coldSymmetricPairExcluded]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let stubStructure := (inputs.get (K .coldWindowStubStructure)).down
      let incoming := (inputs.get (K .coldTwoStrandSurvivor)).down
      .cons (key := K .coldSymmetricPairExcluded)
        ⟨by
          classical
          change TwoStrandSurvivorStatement data.toParameters inputs.current.object at incoming
          change ¬ TwoStrandSurvivorStatement data.toParameters inputs.current.object
          intro survivor
          obtain ⟨germ, representative, config, neutral, realized, survives⟩ := survivor
          obtain ⟨witness⟩ := realized
          have windowMember : witness.window ∈
              (canonicalColdWindows data.toParameters inputs.current.object).filter
                (AmbientCubicWindow data.toParameters inputs.current.object) :=
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

end Hypostructure.Graph.Strategy.Spine
