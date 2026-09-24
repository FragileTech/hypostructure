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

/-! ## Nodes `[78]`--`[79]` at the ordinary Type B entry: the degree-four fan profile

`cor:degree-four-local-activation` and the profile Part VII's panel opens with, on
the ordinary Type B support of node `[64]`.  Node `[78]` is the no arm of `[68]`,
already committed (`K .typeBFanDegreeFourCentres`): every assigned fan centre of
the support sits exactly at `δ + 1`.  This row reads that law and the normal form
and commits `[79]`'s readings at every such centre: the activation dichotomy is
`Graph.heavyCentreLocalDichotomy` — the same theorem `[69]` uses — with `k = δ + 1`
giving `δ − 1` triangular ports (the manuscript's "at least `4 − |U| ≥ 2`"), and
the three readings are `TypeBFanIncidence.degreeFourProfile`: centre surplus `1`,
`c ≤ k`, and `D_B = c − (δ − (k+1)α)` at the registered discharge scale; nothing
writes `7/4`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBFanDegreeFourProfileRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeFourProfile
    { Requires := [K .highCentreNormalForm, K .typeBFanDegreeFourCentres]
      Produces := [K .typeBFanDegreeFourProfile]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let degreeFour := (inputs.get (K .typeBFanDegreeFourCentres)).down
      .cons (key := K .typeBFanDegreeFourProfile)
        (show Value BranchState Presentation presentation data
            .typeBFanDegreeFourProfile inputs.current from
          ⟨by
            change TypeBFanDegreeFourProfileStatement data inputs.current.object
            unfold TypeBFanDegreeFourProfileStatement
            rcases degreeFour with canonical | absorbed | sameToken
            · apply Or.inl
              obtain ⟨packing, valid, maximal, component, present, centres, assigned,
                degrees⟩ := canonical
              refine ⟨packing, valid, maximal, component, present, centres, assigned, ?_⟩
              intro centre member
              have high :=
                TypeBAssignedCentres.high data inputs.current.object assigned centre member
              have degree := degrees centre member
              refine ⟨degree, ?_, ?_, ?_⟩
              · rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
                  compatible | triangular
                · exact Or.inl compatible
                · refine Or.inr ?_
                  rw [degree] at triangular
                  omega
              · omega
              · intro fanEnvelope
                obtain ⟨_surplus, counted, identity, _range⟩ :=
                  Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                    data.threshold data.dischargeScale fanEnvelope degree
                exact ⟨counted, identity⟩
            · apply Or.inr
              apply Or.inl
              refine ⟨absorbed.1, ?_⟩
              intro germ centre witness
              have degree := absorbed.2 germ centre witness
              refine ⟨degree, ?_, ?_, ?_⟩
              · have high : Graph.IsHighCentre inputs.current.object
                    data.threshold centre := by
                  rcases witness with ⟨routing, epsilon, germEq, firstIndex,
                    centreEq, indexLe, high, tail⟩
                  exact high
                rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
                  compatible | triangular
                · exact Or.inl compatible
                · refine Or.inr ?_
                  rw [degree] at triangular
                  omega
              · omega
              · intro fanEnvelope
                obtain ⟨_surplus, counted, identity, _range⟩ :=
                  Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                    data.threshold data.dischargeScale fanEnvelope degree
                exact ⟨counted, identity⟩
            · apply Or.inr
              apply Or.inr
              obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
                  degrees⟩ := sameToken
              refine ⟨packing, valid, maximal, core, envelope, coreEq, nonempty, ?_⟩
              intro centre member
              have degree := degrees centre member
              have high : Graph.IsHighCentre inputs.current.object
                  data.threshold centre := by
                exact envelope.decorations_high centre member
              refine ⟨degree, ?_, ?_, ?_⟩
              · rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
                  compatible | triangular
                · exact Or.inl compatible
                · refine Or.inr ?_
                  rw [degree] at triangular
                  omega
              · omega
              · intro fanEnvelope
                obtain ⟨_surplus, counted, identity, _range⟩ :=
                  Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                    data.threshold data.dischargeScale fanEnvelope degree
                exact ⟨counted, identity⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
