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

/-! ## Node `[72]`, first half: is a direct fan-window cycle present?

`lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`.  Before
any incidence credit is counted, the four direct configurations are removed
structurally: a same-window closed neighbour whose label gap closes a cycle, two
closed neighbours whose wedge through the centre closes one, two whose closed
labels interlace, and two with incidences to distinct packed windows.  Each
display *builds* a cycle whose length the manuscript's arithmetic side condition
declares accepted, so the arm that takes the configuration is uninhabited on a
branch whose object avoids those lengths -- which is why this row's yes arm
closes and its no arm carries `def:direct-cycle-free-closed-pair` forward.

Nothing here writes `{2, 6}` or `{0, 4, 12}`.  Each side condition is
`data.LengthOK` of the length of its own cycle; at the registered target and
window order those readings are exactly the manuscript's sets.

The split is `Classical.em` on the literal carrier's configuration proposition.
The yes arm retains an actual centre and direct configuration; the no arm
records their absence at every applicable centre.  This is a `Decision`: the
arm not taken is absent from the taken branch's key index. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def directCycleDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .fanCertificateMarked) known]
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBDirectCycle) (K .typeBDirectCycleFree) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    `Hypostructure.Graph.Strategy.Spine.directCycleDichotomy
    (by
      classical
      apply Classical.choice
      rcases (ExactLedger.get previous (K .fanCertificateMarked)).down with
        support | absorbed | sameToken
      · obtain ⟨packing, valid, maximal, component, present, centres, assigned,
          _marked⟩ := support
        by_cases configuration :
            ∃ centre ∈ centres,
              Graph.IsHighCentre current.object data.threshold centre ∧
                Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                  data.windowOrder data.LengthOK packing centre
        · exact ⟨.inl ⟨.inl ⟨packing, valid, maximal, component, present, centres,
              assigned, configuration⟩⟩⟩
        · exact ⟨.inr ⟨.inl ⟨packing, valid, maximal, component, present, centres,
              assigned, fun centre member high present =>
                configuration ⟨centre, member, high, present⟩⟩⟩⟩
      · by_cases configuration :
            ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) current.object)
                (centre : current.object.Vertex),
              AbsorbedGermFanEnvelopeWitness data current.object germ centre ∧
                Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                  data.windowOrder data.LengthOK
                  (canonicalWindowPacking data current.object) centre
        · exact ⟨.inl ⟨Or.inr (Or.inl ⟨absorbed, configuration⟩)⟩⟩
        · exact ⟨.inr ⟨Or.inr (Or.inl ⟨absorbed,
            fun germ centre witness present =>
              configuration ⟨germ, centre, witness, present⟩⟩)⟩⟩
      · obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
          marked⟩ := sameToken
        by_cases configuration :
            ∃ centre ∈ envelope.decorations,
              Graph.IsHighCentre current.object data.threshold centre ∧
                Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                  data.windowOrder data.LengthOK packing centre
        · exact ⟨.inl ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
            envelope, coreEq, nonempty, marked, configuration⟩)⟩⟩
        · exact ⟨.inr ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
            envelope, coreEq, nonempty, marked,
            fun centre member high present =>
              configuration ⟨centre, member, high, present⟩⟩)⟩⟩)
    cycleFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
