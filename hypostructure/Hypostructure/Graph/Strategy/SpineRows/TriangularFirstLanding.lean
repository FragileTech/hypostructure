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

/-! ## `lem:triangular-first-landing`

The row reads the literal triangular-core predicates.  Shoulder completion
excludes every noncentral landing in `N(h)`; core membership then leaves only
another port's shoulder, while nonmembership is exactly the outside arm. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def triangularFirstLandingRow :
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
    `Hypostructure.Graph.Strategy.Spine.triangularFirstLanding
    { Requires := [K .triangularFanCore, K .triangularShoulderCompletion,
        K .triangularPortReturn]
      Produces := [K .triangularFirstLanding]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fanCore := (inputs.get (K .triangularFanCore)).down
      let shoulderCompletion :=
        (inputs.get (K .triangularShoulderCompletion)).down
      let portReturns := (inputs.get (K .triangularPortReturn)).down
      .cons (key := K .triangularFirstLanding) ⟨by
        change TriangularFirstLandingStatement data inputs.current.object
        classical
        intro centre centreHeavy ports portsNonempty portsSubset shoulders core
          completion central crossTriangular outside shoulderSpec coreSpec
          completionSpec centralSpec crossSpec outsideSpec endpoint shoulder target
          incidence
        -- Read the exact core witness on this family; the supplied predicates
        -- are its literal definitions, and no alternate carrier is introduced.
        have _coreWitness :=
          fanCore centre centreHeavy ports portsNonempty portsSubset
        obtain ⟨endpointMem, shoulderMem, shoulderTarget, targetEndpoint,
          targetNotOwnShoulders⟩ :=
            (completionSpec endpoint shoulder target).mp incidence
        have endpointTriangular := portsSubset endpointMem
        -- `lem:triangular-port-return` is the inherited nonvacuity fact for the
        -- same port; first-landing classification then uses its shoulder data.
        obtain ⟨_leftReturn, _rightReturn, _leftReturnShoulder,
          _rightReturnShoulder, _returnDistinct, _returnWitness⟩ :=
            portReturns centre centreHeavy endpoint endpointTriangular
        obtain ⟨left, right, leftShoulder, rightShoulder, leftNeRight,
          leftRight, _completes, _notBothCentral, centralOnly⟩ :=
            shoulderCompletion centre centreHeavy endpoint endpointTriangular
        have shoulderData := shoulderSpec endpoint endpointMem
        have pairSubset : ({left, right} :
            Finset inputs.current.object.Vertex) ⊆ shoulders endpoint := by
          intro vertex vertexMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at vertexMem
          rcases vertexMem with vertexEq | vertexEq
          · subst vertex
            exact (shoulderData.1 left).2 leftShoulder
          · subst vertex
            exact (shoulderData.1 right).2 rightShoulder
        have pairCard : ({left, right} :
            Finset inputs.current.object.Vertex).card = 2 := by
          simp [leftNeRight]
        have pairEq : ({left, right} :
            Finset inputs.current.object.Vertex) = shoulders endpoint :=
          Finset.eq_of_subset_of_card_le pairSubset (by
            rw [shoulderData.2.1, pairCard])
        have shoulderCases : shoulder = left ∨ shoulder = right := by
          have : shoulder ∈ ({left, right} :
              Finset inputs.current.object.Vertex) := by
            rw [pairEq]
            exact shoulderMem
          simpa using this
        have targetNotLeft : target ≠ left := by
          intro equality
          apply targetNotOwnShoulders
          rw [equality]
          exact (shoulderData.1 left).2 leftShoulder
        have targetNotRight : target ≠ right := by
          intro equality
          apply targetNotOwnShoulders
          rw [equality]
          exact (shoulderData.1 right).2 rightShoulder
        have noOtherNeighbour :
            inputs.current.object.graph.Adj centre target → target = centre := by
          intro centreTarget
          exact centralOnly.2 shoulder target shoulderCases shoulderTarget
            targetEndpoint targetNotLeft targetNotRight centreTarget
        have targetNotPorts : target ∉ ports := by
          intro targetPort
          have centreTarget :=
            (Graph.mem_triangularEndpoints_iff.mp (portsSubset targetPort)).1
          have targetCentre := noOtherNeighbour centreTarget
          subst target
          exact centreTarget.ne rfl
        have centreInCore : centre ∈ core :=
          (coreSpec centre).2 (Or.inl rfl)
        have crossNotOutside (crossing :
            crossTriangular endpoint shoulder target) :
            ¬ outside endpoint shoulder target := by
          intro external
          obtain ⟨_, other, otherMem, otherNe, targetShoulder⟩ :=
            (crossSpec endpoint shoulder target).mp crossing
          have targetCore : target ∈ core :=
            (coreSpec target).2
              (Or.inr (Or.inr ⟨other, otherMem, targetShoulder⟩))
          exact (outsideSpec endpoint shoulder target).mp external |>.2.1 targetCore
        have outsideNotCross (external : outside endpoint shoulder target) :
            ¬ crossTriangular endpoint shoulder target := by
          intro crossing
          exact crossNotOutside crossing external
        have centralNotCross (centralLanding :
            central endpoint shoulder target) :
            ¬ crossTriangular endpoint shoulder target := by
          intro crossing
          have targetCentre :=
            (centralSpec endpoint shoulder target).mp centralLanding |>.2
          obtain ⟨_, other, otherMem, _otherNe, targetShoulder⟩ :=
            (crossSpec endpoint shoulder target).mp crossing
          have targetNotCentre :=
            ((shoulderSpec other otherMem).1 target).1 targetShoulder |>.2
          exact targetNotCentre targetCentre
        have centralNotOutside (centralLanding :
            central endpoint shoulder target) :
            ¬ outside endpoint shoulder target := by
          intro external
          have targetCentre :=
            (centralSpec endpoint shoulder target).mp centralLanding |>.2
          exact (outsideSpec endpoint shoulder target).mp external |>.2.1
            (targetCentre ▸ centreInCore)
        have crossNotCentral (crossing :
            crossTriangular endpoint shoulder target) :
            ¬ central endpoint shoulder target := by
          intro centralLanding
          exact centralNotCross centralLanding crossing
        have outsideNotCentral (external : outside endpoint shoulder target) :
            ¬ central endpoint shoulder target := by
          intro centralLanding
          exact centralNotOutside centralLanding external
        refine ⟨?_, noOtherNeighbour, targetNotPorts⟩
        by_cases targetCentre : target = centre
        · have centralLanding : central endpoint shoulder target :=
            (centralSpec endpoint shoulder target).2 ⟨incidence, targetCentre⟩
          exact Or.inl ⟨centralLanding, centralNotCross centralLanding,
            centralNotOutside centralLanding⟩
        · by_cases targetCore : target ∈ core
          · rcases (coreSpec target).1 targetCore with
              targetCentre' | targetPort | ⟨other, otherMem, targetShoulder⟩
            · exact (targetCentre targetCentre').elim
            · exact (targetNotPorts targetPort).elim
            · have otherNe : other ≠ endpoint := by
                intro equality
                subst other
                exact targetNotOwnShoulders targetShoulder
              have crossing : crossTriangular endpoint shoulder target :=
                (crossSpec endpoint shoulder target).2
                  ⟨incidence, other, otherMem, otherNe, targetShoulder⟩
              exact Or.inr (Or.inl ⟨crossing, crossNotCentral crossing,
                crossNotOutside crossing⟩)
          · have targetNotAdjacent :
                ¬ inputs.current.object.graph.Adj centre target := by
              intro adjacent
              exact targetCentre (noOtherNeighbour adjacent)
            have external : outside endpoint shoulder target :=
              (outsideSpec endpoint shoulder target).2
                ⟨incidence, targetCore, targetNotAdjacent⟩
            exact Or.inr (Or.inr ⟨external, outsideNotCentral external,
              outsideNotCross external⟩)⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
