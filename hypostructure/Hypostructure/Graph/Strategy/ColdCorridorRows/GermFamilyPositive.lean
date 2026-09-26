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
      requiresUnique := by key_fresh
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

end Hypostructure.Graph.Strategy.Spine
