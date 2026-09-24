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

/-! ## Node `[74]`/`[82]`: the hybrid B1 fan ledger

`lem:typeB-hybrid-B1`, and with it `lem:typeB-hybrid-incidence-budget`,
`def:typeB-hybrid-incidence` and parts (a)--(b) of
`prop:fan-closed-port-typeB-routing`.  This row supplies the *local* payment
before the global B2 split, so B2's success and minimal-obstruction arms both
retain it: at every certificate-marked centre of an assigned Type B support,
the non-`h` incidences of its cubic-closed neighbours
are pairwise distinct carriers, they split into `I_W` and `I_N`, their half-credit
pays `D_B`, the non-window half-credit covers the remaining demand `D_N`, and two
cubic-closed neighbours already make `D_B` positive.

Two prerequisites, both consumed.  `selection` supplies the avoidance that kills
the quadrilateral `u — h — v — z — u`, which is the whole reason two cubic-closed
neighbours cannot share a carrier.  `fanCertificateMarked` supplies both the
labelling and `[70]`'s cap at that same centre and on that same assigned support;
with the registered `fanCapSlack` this is the slack `k + 1 ≤ s·δ` the payment
spends — the manuscript's "and `k ≤ 8`".

`typeBDirectCycleFree` is *not* declared.  The manuscript states the budget lemma
under "none of the direct-cycle conclusions occurs", but its proof of the
disjointness uses only target-safety at a `4`-cycle and the simplicity of `G`, and no other clause reads it either; the
fact is on this branch's index because the row runs after the direct-cycle half
of node `[72]`/`[81]`, and that is a property of the cursor rather than of the
manifest.  Declaring it would be a false dependency. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def hybridEntryRow :
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
    `Hypostructure.Graph.Strategy.Spine.hybridEntry
    { Requires := [K .selection, K .fanCertificateMarked]
      Produces := [K .typeBHybridEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => Classical.choice <| by
      let avoids := (inputs.get (K .selection)).down.1
      rcases (inputs.get (K .fanCertificateMarked)).down with
        support | absorbed | sameToken
      · obtain ⟨packing, valid, maximal, component, present, centres, assigned,
          marked⟩ := support
        exact ⟨.cons (key := K .typeBHybridEntry)
          (⟨.inl ⟨packing, valid, maximal, component, present, centres, assigned,
            fun centre member high envelope windowSupport => by
              -- The marked fan's cap, and with it the manuscript's `k ≤ 8`.
              obtain ⟨_marking, capped⟩ := marked centre member
              have slack :
                  inputs.current.object.degree centre + 1 ≤
                    data.dischargeScale * data.threshold :=
                le_trans (Nat.succ_le_succ capped) data.fanCapSlack
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · intro left leftMember right rightMember different shared
                  leftIncidence rightIncidence
                exact Graph.TypeBHybridIncidence.endpoints_not_shared avoids
                  data.quadrilateralAccepted
                  (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp leftMember)
                  (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp rightMember)
                  different leftIncidence rightIncidence
              · exact Graph.TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences
                  _ _ _ _ _
              · exact Graph.TypeBHybridIncidence.hybridCapacity_pays _ _ _ _ _ _
                  data.three_le_threshold slack
              · exact Graph.TypeBHybridIncidence.nonWindowCredit_ge_demand _ _ _ _
                  _ _ data.three_le_threshold slack
              · intro two_le
                exact Graph.TypeBHybridIncidence.positive_deficit_of_two_le_closedCount
                  _ _ _ _ _ two_le high data.highCentreDeficitSlack⟩⟩)
          .nil⟩
      · obtain ⟨envelopes, marked⟩ := absorbed
        refine ⟨.cons (key := K .typeBHybridEntry)
          (⟨Or.inr (Or.inl ⟨⟨envelopes, marked⟩, ?_⟩)⟩) .nil⟩
        intro germ centre witness envelope windowSupport
        obtain ⟨_marking, capped⟩ := marked germ centre witness
        have slack :
            inputs.current.object.degree centre + 1 ≤
              data.dischargeScale * data.threshold :=
          le_trans (Nat.succ_le_succ capped) data.fanCapSlack
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro left leftMember right rightMember different shared
            leftIncidence rightIncidence
          exact Graph.TypeBHybridIncidence.endpoints_not_shared avoids
            data.quadrilateralAccepted
            (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp leftMember)
            (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp rightMember)
            different leftIncidence rightIncidence
        · exact Graph.TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences
            _ _ _ _ _
        · exact Graph.TypeBHybridIncidence.hybridCapacity_pays _ _ _ _ _ _
            data.three_le_threshold slack
        · exact Graph.TypeBHybridIncidence.nonWindowCredit_ge_demand _ _ _ _
            _ _ data.three_le_threshold slack
        · intro two_le
          have high : Graph.IsHighCentre inputs.current.object
              data.threshold centre := by
            rcases witness with ⟨routing, epsilon, germEq, firstIndex,
              centreEq, indexLe, high, tail⟩
            exact high
          exact Graph.TypeBHybridIncidence.positive_deficit_of_two_le_closedCount
            _ _ _ _ _ two_le high data.highCentreDeficitSlack
      · obtain ⟨packing, valid, maximal, core, handoff, coreEq, nonempty,
            marked⟩ := sameToken
        refine ⟨.cons (key := K .typeBHybridEntry)
          (⟨Or.inr (Or.inr ⟨packing, valid, maximal, core, handoff, coreEq,
            nonempty, marked, ?_⟩)⟩) .nil⟩
        intro centre member envelope windowSupport
        obtain ⟨_marking, capped⟩ := marked centre member
        have slack :
            inputs.current.object.degree centre + 1 ≤
              data.dischargeScale * data.threshold :=
          le_trans (Nat.succ_le_succ capped) data.fanCapSlack
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro left leftMember right rightMember different shared
            leftIncidence rightIncidence
          exact Graph.TypeBHybridIncidence.endpoints_not_shared avoids
            data.quadrilateralAccepted
            (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp leftMember)
            (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp rightMember)
            different leftIncidence rightIncidence
        · exact Graph.TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences
            _ _ _ _ _
        · exact Graph.TypeBHybridIncidence.hybridCapacity_pays _ _ _ _ _ _
            data.three_le_threshold slack
        · exact Graph.TypeBHybridIncidence.nonWindowCredit_ge_demand _ _ _ _
            _ _ data.three_le_threshold slack
        · intro two_le
          exact Graph.TypeBHybridIncidence.positive_deficit_of_two_le_closedCount
            _ _ _ _ _ two_le (handoff.decorations_high centre member)
              data.highCentreDeficitSlack)
    0 0

end Hypostructure.Graph.Strategy.Spine
