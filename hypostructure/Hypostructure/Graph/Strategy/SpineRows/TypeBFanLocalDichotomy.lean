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

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBFanLocalDichotomyRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBFanLocalDichotomy
    { Requires := [K .highCentreNormalForm, K .typeBFanHeavyCentre,
        K .sameCenterOpenPortCompatibility]
      Produces := [K .typeBFanLocalDichotomy]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let heavy := (inputs.get (K .typeBFanHeavyCentre)).down
      let compatibility :=
        (inputs.get (K .sameCenterOpenPortCompatibility)).down
      let localAt : ∀ centre : inputs.current.object.Vertex,
          Graph.IsHighCentre inputs.current.object data.threshold centre →
            ((∃ left right : inputs.current.object.Vertex,
                Graph.FanCompatible inputs.current.object centre left right) ∨
              inputs.current.object.degree centre - 2 ≤
                (Graph.triangularEndpoints inputs.current.object centre).card) := by
        intro centre high
        classical
        by_cases pair : ∃ left right : inputs.current.object.Vertex,
            Graph.FanCompatible inputs.current.object centre left right
        · exact Or.inl pair
        · apply Or.inr
          have inside : ∀ endpoint ∈
              Graph.openEndpoints inputs.current.object centre,
                inputs.current.object.graph.Adj centre endpoint := by
            intro endpoint member
            exact (Graph.mem_openEndpoints_iff.mp member).1
          have clique : ∀ first ∈
              Graph.openEndpoints inputs.current.object centre,
              ∀ second ∈ Graph.openEndpoints inputs.current.object centre,
                first ≠ second →
                  inputs.current.object.graph.Adj first second := by
            intro first firstMember second secondMember different
            by_cases adjacent : inputs.current.object.graph.Adj first second
            · exact adjacent
            · exact False.elim <| pair ⟨first, second,
                compatibility centre high first second
                  (Graph.mem_openEndpoints_iff.mp firstMember).1
                  (Graph.mem_openEndpoints_iff.mp secondMember).1 different
                  adjacent (Graph.mem_openEndpoints_iff.mp firstMember).2
                  (Graph.mem_openEndpoints_iff.mp secondMember).2⟩
          have openAtMostTwo := Graph.card_le_two_of_pairwise_adj
            (normal centre high)
            (Graph.openEndpoints inputs.current.object centre) inside clique
          have partition := Graph.openEndpoints_card_add_triangularEndpoints_card
            inputs.current.object centre
          omega
      .cons (key := K .typeBFanLocalDichotomy)
        (show Value BranchState Presentation presentation data
            .typeBFanLocalDichotomy inputs.current from
          ⟨by
            change TypeBFanLocalDichotomyStatement data inputs.current.object
            unfold TypeBFanLocalDichotomyStatement
            rcases heavy with canonical | absorbed | sameToken
            · apply Or.inl
              obtain ⟨packing, valid, maximal, component, present, centres, assigned,
                _heavyWitness⟩ := canonical
              refine ⟨packing, valid, maximal, component, present, centres, assigned, ?_⟩
              intro centre member centreHeavy
              have highCentre :=
                TypeBAssignedCentres.high data inputs.current.object assigned centre member
              rcases localAt centre highCentre with
                compatible | triangular
              · exact Or.inl compatible
              · exact Or.inr ⟨triangular,
                  Graph.three_le_triangularEndpoints_card data.three_le_threshold
                    centreHeavy triangular⟩
            · apply Or.inr
              apply Or.inl
              refine ⟨absorbed.1, ?_⟩
              obtain ⟨germ, centre, witness, centreHeavy⟩ := absorbed.2
              refine ⟨germ, centre, witness, centreHeavy, ?_⟩
              have highCentre : Graph.IsHighCentre inputs.current.object
                  data.threshold centre := by
                rcases witness with ⟨routing, epsilon, germEq, firstIndex,
                  centreEq, indexLe, high, tail⟩
                exact high
              rcases localAt centre highCentre with
                compatible | triangular
              · exact Or.inl compatible
              · exact Or.inr ⟨triangular,
                  Graph.three_le_triangularEndpoints_card data.three_le_threshold
                    centreHeavy triangular⟩
            · apply Or.inr
              apply Or.inr
              obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
                  _heavyWitness⟩ := sameToken
              refine ⟨packing, valid, maximal, core, envelope, coreEq, nonempty, ?_⟩
              intro centre member centreHeavy
              have highCentre : Graph.IsHighCentre inputs.current.object
                  data.threshold centre := by
                exact envelope.decorations_high centre member
              rcases localAt centre highCentre with
                compatible | triangular
              · exact Or.inl compatible
              · exact Or.inr ⟨triangular,
                  Graph.three_le_triangularEndpoints_card data.three_le_threshold
                    centreHeavy triangular⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
