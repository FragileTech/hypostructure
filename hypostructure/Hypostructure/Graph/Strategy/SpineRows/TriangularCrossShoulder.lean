import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## `lem:triangular-cross-shoulder`

Two distinct cross edges either share a shoulder, giving that shoulder four
distinct neighbours, or are disjoint and close with the two shoulder chords
to the manuscript's quadrilateral.  Target safety removes the latter case. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def triangularCrossShoulderRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.triangularCrossShoulder
    { Requires := [K .selection, K .triangularFanCore,
        K .triangularFirstLanding]
      Produces := [K .triangularCrossShoulder]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := (inputs.get (K .selection)).down.1
      let _fanCore := (inputs.get (K .triangularFanCore)).down
      let _firstLanding := (inputs.get (K .triangularFirstLanding)).down
      .cons (key := K .triangularCrossShoulder) ⟨by
        change TriangularCrossShoulderStatement data inputs.current.object
        classical
        intro centre centreHeavy ports portsNonempty portsSubset shoulders
          crossTriangular shoulderSpec crossSpec first firstMem second secondMem
          firstNeSecond
        dsimp only
        have chordOfDistinct : ∀ endpoint ∈ ports,
            ∀ left ∈ shoulders endpoint, ∀ right ∈ shoulders endpoint,
              left ≠ right → inputs.current.object.graph.Adj left right := by
          intro endpoint endpointMem left leftMem right rightMem leftNeRight
          obtain ⟨left₀, right₀, left₀Mem, right₀Mem, left₀NeRight₀, chord⟩ :=
            (shoulderSpec endpoint endpointMem).2.2
          have pairEq : ({left₀, right₀} :
              Finset inputs.current.object.Vertex) = shoulders endpoint :=
            Finset.eq_of_subset_of_card_le (by
              intro candidate candidateMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at candidateMem
              rcases candidateMem with h | h
              · simpa [h] using left₀Mem
              · simpa [h] using right₀Mem) (by
                simp [left₀NeRight₀, (shoulderSpec endpoint endpointMem).2.1])
          have every : ∀ vertex ∈ shoulders endpoint,
              vertex = left₀ ∨ vertex = right₀ := by
            intro vertex vertexMem
            have : vertex ∈ ({left₀, right₀} :
                Finset inputs.current.object.Vertex) := by
              rw [pairEq]
              exact vertexMem
            simpa using this
          rcases every left leftMem with rfl | rfl <;>
            rcases every right rightMem with rfl | rfl
          · exact (leftNeRight rfl).elim
          · exact chord
          · exact chord.symm
          · exact (leftNeRight rfl).elim
        have fourNeighbours : ∀ vertex a b c d,
            inputs.current.object.graph.Adj vertex a →
            inputs.current.object.graph.Adj vertex b →
            inputs.current.object.graph.Adj vertex c →
            inputs.current.object.graph.Adj vertex d →
            a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
              4 ≤ inputs.current.object.degree vertex := by
          intro vertex a b c d va vb vc vd ab ac ad bc bd cd
          have subset : ({a, b, c, d} :
              Finset inputs.current.object.Vertex) ⊆
                (inputs.current.object.orderedNeighbors vertex).toFinset := by
            intro candidate candidateMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at candidateMem
            rcases candidateMem with rfl | rfl | rfl | rfl
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using va
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using vb
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using vc
            · simpa [inputs.current.object.mem_orderedNeighbors_iff] using vd
          have cardFour : ({a, b, c, d} :
              Finset inputs.current.object.Vertex).card = 4 := by
            simp [ab, ac, ad, bc, bd, cd]
          have count := Finset.card_le_card subset
          rw [List.toFinset_card_of_nodup
            (inputs.current.object.orderedNeighbors_nodup vertex),
            inputs.current.object.orderedNeighbors_length] at count
          simpa [cardFour] using count
        have highOfDistinct : ∀ source target source' target',
            (crossTriangular first source target ∧
              crossTriangular second target source) →
            (crossTriangular first source' target' ∧
              crossTriangular second target' source') →
            (source ≠ source' ∨ target ≠ target') →
              ∃ shoulder,
                (shoulder ∈ shoulders first ∨ shoulder ∈ shoulders second) ∧
                  4 ≤ inputs.current.object.degree shoulder := by
          intro source target source' target' edge edge' distinct
          have firstEdge := (crossSpec first source target).mp edge.1
          have secondEdge := (crossSpec second target source).mp edge.2
          have firstEdge' := (crossSpec first source' target').mp edge'.1
          have secondEdge' := (crossSpec second target' source').mp edge'.2
          by_cases sameSource : source = source'
          · have targetNe : target ≠ target' := by
              rcases distinct with sourceNe | targetNe
              · exact (sourceNe sameSource).elim
              · exact targetNe
            subst source'
            obtain ⟨other, otherMem, otherNe, sourceOther⟩ :
                ∃ other ∈ shoulders first, other ≠ source ∧
                  inputs.current.object.graph.Adj source other := by
              obtain ⟨left, right, leftMem, rightMem, leftNeRight, chord⟩ :=
                (shoulderSpec first firstMem).2.2
              have sourceCases : source = left ∨ source = right := by
                have pairEq : ({left, right} :
                    Finset inputs.current.object.Vertex) = shoulders first :=
                  Finset.eq_of_subset_of_card_le (by
                    intro vertex vertexMem
                    simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
                    rcases vertexMem with h | h
                    · simpa [h] using leftMem
                    · simpa [h] using rightMem) (by
                      simp [leftNeRight, (shoulderSpec first firstMem).2.1])
                have : source ∈ ({left, right} :
                    Finset inputs.current.object.Vertex) := by
                  rw [pairEq]
                  exact firstEdge.2.1
                simpa using this
              rcases sourceCases with rfl | rfl
              · exact ⟨right, rightMem, leftNeRight.symm, chord⟩
              · exact ⟨left, leftMem, leftNeRight, chord.symm⟩
            refine ⟨source, Or.inl firstEdge.2.1, ?_⟩
            exact fourNeighbours source first other target target'
              (((shoulderSpec first firstMem).1 source).mp firstEdge.2.1).1.symm
              sourceOther firstEdge.2.2.1 firstEdge'.2.2.1
              ((((shoulderSpec first firstMem).1 other).mp otherMem).1.ne)
              firstEdge.2.2.2.1.symm firstEdge'.2.2.2.1.symm
              (by exact fun h => firstEdge.2.2.2.2.1 (h ▸ otherMem))
              (by exact fun h => firstEdge'.2.2.2.2.1 (h ▸ otherMem)) targetNe
          · by_cases sameTarget : target = target'
            · subst target'
              have sourceNe : source ≠ source' := sameSource
              obtain ⟨other, otherMem, otherNe, targetOther⟩ :
                  ∃ other ∈ shoulders second, other ≠ target ∧
                    inputs.current.object.graph.Adj target other := by
                obtain ⟨left, right, leftMem, rightMem, leftNeRight, chord⟩ :=
                  (shoulderSpec second secondMem).2.2
                have targetCases : target = left ∨ target = right := by
                  have pairEq : ({left, right} :
                      Finset inputs.current.object.Vertex) = shoulders second :=
                    Finset.eq_of_subset_of_card_le (by
                      intro vertex vertexMem
                      simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
                      rcases vertexMem with h | h
                      · simpa [h] using leftMem
                      · simpa [h] using rightMem) (by
                        simp [leftNeRight, (shoulderSpec second secondMem).2.1])
                  have : target ∈ ({left, right} :
                      Finset inputs.current.object.Vertex) := by
                    rw [pairEq]
                    exact secondEdge.2.1
                  simpa using this
                rcases targetCases with rfl | rfl
                · exact ⟨right, rightMem, leftNeRight.symm, chord⟩
                · exact ⟨left, leftMem, leftNeRight, chord.symm⟩
              refine ⟨target, Or.inr secondEdge.2.1, ?_⟩
              exact fourNeighbours target second other source source'
                (((shoulderSpec second secondMem).1 target).mp secondEdge.2.1).1.symm
                targetOther secondEdge.2.2.1 secondEdge'.2.2.1
                ((((shoulderSpec second secondMem).1 other).mp otherMem).1.ne)
                secondEdge.2.2.2.1.symm secondEdge'.2.2.2.1.symm
                (by exact fun h => secondEdge.2.2.2.2.1 (h ▸ otherMem))
                (by exact fun h => secondEdge'.2.2.2.2.1 (h ▸ otherMem)) sourceNe
            · have sourceChord := chordOfDistinct first firstMem source
                firstEdge.2.1 source' firstEdge'.2.1 sameSource
              have targetChord := chordOfDistinct second secondMem target
                secondEdge.2.1 target' secondEdge'.2.1 sameTarget
              have sourceNeTarget' : source ≠ target' := by
                intro equality
                exact secondEdge.2.2.2.2.1 (equality ▸ secondEdge'.2.1)
              have targetNeSource' : target ≠ source' := by
                intro equality
                exact firstEdge.2.2.2.2.1 (equality ▸ firstEdge'.2.1)
              exact (Graph.not_quadrilateral avoids data.quadrilateralAccepted
                firstEdge.2.2.1 targetChord secondEdge'.2.2.1 sourceChord.symm
                sourceNeTarget' targetNeSource').elim
        refine ⟨highOfDistinct, ?_⟩
        intro low source target source' target' edge edge'
        by_cases sameSource : source = source'
        · refine ⟨sameSource, ?_⟩
          by_contra targetNe
          obtain ⟨shoulder, shoulderMem, high⟩ :=
            highOfDistinct source target source' target' edge edge'
              (Or.inr targetNe)
          exact (Nat.not_lt_of_ge high) (low shoulder shoulderMem)
        · obtain ⟨shoulder, shoulderMem, high⟩ :=
            highOfDistinct source target source' target' edge edge'
              (Or.inl sameSource)
          exact ((Nat.not_lt_of_ge high) (low shoulder shoulderMem)).elim⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
