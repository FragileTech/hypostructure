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

/-! ## Nodes `[90]`--`[91]`: unsaturated Type A discharging

`lem:typeA-unsaturated-discharge`, read from nodes `[88]` and `[90]`.  The row
publishes the exact integral conclusion `|V(X)| ≤ s * def⁺(X)` for the same
negative Type A support quantified by the incoming facts.  The canonical
routing and the unsaturated receiver inequalities are both read by semantic
key. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAUnsaturatedDischargeRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischarge
    { Requires := [K .typeAReceiverRouting, K .typeAUnsaturatedReceivers]
      Produces := [K .typeAUnsaturatedDischarge]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routing := (show Value BranchState Presentation presentation data
          .typeAReceiverRouting inputs.current from
        inputs.get (K .typeAReceiverRouting)).down
      let unsaturated := (show Value BranchState Presentation presentation data
          .typeAUnsaturatedReceivers inputs.current from
        inputs.get (K .typeAUnsaturatedReceivers)).down
      .cons (key := K .typeAUnsaturatedDischarge)
        (show Value BranchState Presentation presentation data
            .typeAUnsaturatedDischarge inputs.current from ⟨by
          obtain ⟨packing, valid, maximal, component, present, negative,
            surplus, receiverBound⟩ := unsaturated
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          have inside : piece ⊆ inputs.current.object.remainderSupport packing :=
            inputs.current.object.pieceSupport_subset
              (inputs.current.object.remainderSupport packing) component
          have exactDegree : ∀ vertex ∈ piece,
              inputs.current.object.degree vertex = data.threshold := by
            intro vertex member
            have lower : data.threshold ≤ inputs.current.object.degree vertex :=
              le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have summand :
                inputs.current.object.degree vertex - data.threshold = 0 :=
              Nat.eq_zero_of_le_zero
                (surplus ▸ Finset.single_le_sum
                  (f := fun other =>
                    inputs.current.object.degree other - data.threshold)
                  (fun _ _ => Nat.zero_le _) member)
            omega
          have capped : ∀ vertex ∈ piece,
              inputs.current.object.internalDegree piece vertex ≤
                data.threshold :=
            fun vertex member => (exactDegree vertex member) ▸
              inputs.current.object.internalDegree_le_degree piece vertex
          have discharged :=
            Graph.FiniteObject.unsaturatedDischarge inputs.current.object
              piece data.threshold data.dischargeScale capped
              (routing packing valid maximal piece inside surplus).1
              receiverBound
          exact ⟨packing, valid, maximal, component, present, negative,
            surplus, discharged⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
