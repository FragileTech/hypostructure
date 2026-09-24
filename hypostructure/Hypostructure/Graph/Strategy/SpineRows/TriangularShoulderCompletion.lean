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

/-! ## `lem:triangular-shoulder-completion`

The row is the paper's four-part bookkeeping lemma.  It reads the literal
normal form and triangular-core facts and publishes the completion statement
on the same residual. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def triangularShoulderCompletionRow :
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
    `Hypostructure.Graph.Strategy.Spine.triangularShoulderCompletion
    { Requires := [K .highCentreNormalForm, K .triangularFanCore]
      Produces := [K .triangularShoulderCompletion]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      .cons (key := K .triangularShoulderCompletion) ⟨by
        change TriangularShoulderCompletionStatement data inputs.current.object
        classical
        intro centre centreHeavy endpoint endpointMem
        have centreEndpoint :=
          (Graph.mem_triangularEndpoints_iff.mp endpointMem).1
        have centreHigh : Graph.IsHighCentre inputs.current.object
            data.threshold centre :=
          Nat.lt_trans (Nat.lt_succ_self data.threshold) centreHeavy
        have nf := normal centre centreHigh
        obtain ⟨left, right, leftShoulder, rightShoulder, leftRight⟩ :=
          (Graph.mem_triangularEndpoints_iff.mp endpointMem).2
        have endpointDegree := nf.neighbourTight centreEndpoint
        have neighbourCard (vertex : inputs.current.object.Vertex) :
            (inputs.current.object.orderedNeighbors vertex).toFinset.card =
              inputs.current.object.degree vertex := by
          rw [List.toFinset_card_of_nodup
            (inputs.current.object.orderedNeighbors_nodup vertex),
            inputs.current.object.orderedNeighbors_length vertex]
        have thirdNeighbour (vertex first second : inputs.current.object.Vertex)
            (firstAdj : inputs.current.object.graph.Adj vertex first)
            (secondAdj : inputs.current.object.graph.Adj vertex second)
            (different : first ≠ second)
            (three : 3 ≤ inputs.current.object.degree vertex) :
            ∃ target, inputs.current.object.graph.Adj vertex target ∧
              target ≠ first ∧ target ≠ second := by
          by_contra absent
          push_neg at absent
          have subset :
              (inputs.current.object.orderedNeighbors vertex).toFinset ⊆
                {first, second} := by
            intro target targetMem
            have adjacent : inputs.current.object.graph.Adj vertex target := by
              simpa [inputs.current.object.mem_orderedNeighbors_iff] using targetMem
            rcases eq_or_ne target first with rfl | targetFirst
            · simp
            have targetSecond := absent target adjacent targetFirst
            simp [targetSecond]
          have bound := Finset.card_le_card subset
          rw [neighbourCard] at bound
          have pairCard : ({first, second} : Finset inputs.current.object.Vertex).card = 2 := by
            simp [different]
          rw [pairCard] at bound
          omega
        have exhaustThree (vertex first second third target :
            inputs.current.object.Vertex)
            (degreeThree : inputs.current.object.degree vertex = 3)
            (firstAdj : inputs.current.object.graph.Adj vertex first)
            (secondAdj : inputs.current.object.graph.Adj vertex second)
            (thirdAdj : inputs.current.object.graph.Adj vertex third)
            (firstSecond : first ≠ second) (firstThird : first ≠ third)
            (secondThird : second ≠ third)
            (targetAdj : inputs.current.object.graph.Adj vertex target) :
            target = first ∨ target = second ∨ target = third := by
          by_contra distinct
          push_neg at distinct
          rcases distinct with ⟨targetFirst, targetSecond, targetThird⟩
          have subset : ({first, second, third, target} :
              Finset inputs.current.object.Vertex) ⊆
              (inputs.current.object.orderedNeighbors vertex).toFinset := by
            intro item itemMem
            simp only [Finset.mem_insert, Finset.mem_singleton] at itemMem
            rcases itemMem with rfl | rfl | rfl | rfl
            all_goals simpa [inputs.current.object.mem_orderedNeighbors_iff]
          have four : 4 ≤
              ({first, second, third, target} :
                Finset inputs.current.object.Vertex).card := by
            simp [targetFirst, targetSecond, targetThird, firstSecond,
              firstThird, secondThird, targetFirst.symm, targetSecond.symm,
              targetThird.symm, firstSecond.symm, firstThird.symm,
              secondThird.symm]
          have bound := Finset.card_le_card subset
          rw [neighbourCard, degreeThree] at bound
          omega
        have shoulderCompletion (shoulder other : inputs.current.object.Vertex)
            (shoulderData : Graph.IsShoulder inputs.current.object centre endpoint shoulder)
            (otherData : Graph.IsShoulder inputs.current.object centre endpoint other)
            (shoulderOther : inputs.current.object.graph.Adj shoulder other)
            (different : shoulder ≠ other) :
            ∃ target, inputs.current.object.graph.Adj shoulder target ∧
              target ≠ endpoint ∧ target ≠ shoulder ∧ target ≠ other := by
          have three : 3 ≤ inputs.current.object.degree shoulder :=
            le_trans data.three_le_threshold
              (le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree shoulder))
          obtain ⟨target, targetAdj, targetEndpoint, targetOther⟩ :=
            thirdNeighbour shoulder endpoint other shoulderData.1.symm shoulderOther
              otherData.1.ne three
          exact ⟨target, targetAdj, targetEndpoint, targetAdj.ne.symm, targetOther⟩
        refine ⟨left, right, leftShoulder, rightShoulder, leftRight.ne, leftRight,
          ?_, ?_, ?_, ?_⟩
        · intro shoulder shoulderCases
          rcases shoulderCases with shoulderEq | shoulderEq
          · subst shoulder
            simpa [leftRight.ne] using
              shoulderCompletion left right leftShoulder rightShoulder leftRight
                leftRight.ne
          · subst shoulder
            obtain ⟨target, adjacent, endpointNe, rightNe, leftNe⟩ :=
              shoulderCompletion right left rightShoulder leftShoulder leftRight.symm
                leftRight.ne.symm
            exact ⟨target, adjacent, endpointNe, leftNe, rightNe⟩
        · intro both
          exact nf.inducedMatching both.1 centreEndpoint both.2 leftRight.ne
            leftShoulder.1.symm rightShoulder.1
        · intro shoulder shoulderCases centreShoulder
          have degreeShoulder := nf.neighbourTight centreShoulder
          have degreeShoulderThree :
              inputs.current.object.degree shoulder = 3 := by
            rw [degreeShoulder, data.threshold_eq_three]
          refine ⟨degreeShoulder, ?_⟩
          intro target
          constructor
          · rintro ⟨targetAdj, targetEndpoint, targetLeft, targetRight⟩
            rcases shoulderCases with shoulderEq | shoulderEq
            · subst shoulder
              rcases exhaustThree left centre endpoint right target
                  degreeShoulderThree centreShoulder.symm leftShoulder.1.symm leftRight
                  centreEndpoint.ne rightShoulder.2.symm rightShoulder.1.ne targetAdj with
                rfl | rfl | rfl
              · rfl
              · exact (targetEndpoint rfl).elim
              · exact (targetRight rfl).elim
            · subst shoulder
              rcases exhaustThree right centre endpoint left target
                  degreeShoulderThree centreShoulder.symm rightShoulder.1.symm leftRight.symm
                  centreEndpoint.ne leftShoulder.2.symm leftShoulder.1.ne targetAdj with
                rfl | rfl | rfl
              · rfl
              · exact (targetEndpoint rfl).elim
              · exact (targetLeft rfl).elim
          · intro targetCentre
            subst target
            refine ⟨centreShoulder.symm, centreEndpoint.ne, ?_, ?_⟩
            · exact leftShoulder.2.symm
            · exact rightShoulder.2.symm
        · intro shoulder target shoulderCases targetAdj targetEndpoint targetLeft
            targetRight centreTarget
          by_cases targetCentre : target = centre
          · exact targetCentre
          have endpointDegreeThree : inputs.current.object.degree endpoint = 3 := by
            rw [endpointDegree, data.threshold_eq_three]
          have endpointTarget : ¬ inputs.current.object.graph.Adj endpoint target := by
            intro adjacent
            rcases exhaustThree endpoint centre left right target endpointDegreeThree
                centreEndpoint.symm leftShoulder.1 rightShoulder.1
                leftShoulder.2.symm rightShoulder.2.symm leftRight.ne adjacent with
              targetCentre' | targetLeft' | targetRight'
            · exact targetCentre targetCentre'
            · exact targetLeft targetLeft'
            · exact targetRight targetRight'
          rcases shoulderCases with shoulderEq | shoulderEq
          · subst shoulder
            exact False.elim (nf.noCommonNeighbourOutside centreEndpoint centreTarget
              targetEndpoint.symm endpointTarget leftShoulder.2
              leftShoulder.1 targetAdj.symm)
          · subst shoulder
            exact False.elim (nf.noCommonNeighbourOutside centreEndpoint centreTarget
              targetEndpoint.symm endpointTarget rightShoulder.2
              rightShoulder.1 targetAdj.symm)
        ⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
