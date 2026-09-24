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

/-! ## Node `[123]`: `thm:large-budget-route8-only`, the pressure descent

The manuscript's deterministic procedure on the object-level census
(`Graph/Route8Pressure`): from the empty peeling, a stage with the stage rate
`(δs+1)|∂R| + δ·slack + δ|P₄| < δ|R|` (`def:typeA-peeling-reduced-ledger`'s
`D̃_A^{P₄} ≥ (¼ − τ)|R| − o(|R|)`) has a two-carrier entry of the peeled ledger
(`lem:typeA-peeling-reduced-reduction`); a target-defect entry — its load carries
an exit-(4) witness at its receiver with the current peeled loads
(`lem:typeA-pressure-is-exit4-peel`) — is peeled and the number of unpeeled entries
drops (`lem:typeA-exit4-finite-descent`, `Λ₄`); the procedure therefore ends at a
stage with a true (route-8) two-carrier entry, sent to node `[124]`, or at a stage
where the stage rate fails.  The row reads the unified deficit, burden, entry,
and surviving-stage facts and publishes the procedure's outcome. -/
/-! ## Node `[86]`: `lem:typeA-exclusion`

*"Consequently a Type A support with `N₀(X) < 0` must carry an admissible
route-8 residual profile, produce the Type B handoff, or contain an exit-(4)
witness for a routed load."*  Stated over the canonical pieces of every
maximal-packing remainder of the selected minimal counterexample.  Per
`rem:unified-covers-exit4`, the residual arm quantifies the route-8 entries of
every saturated receiver over both its silent excess and, at each overloaded
port, its selected visible unpeeled loads: exits (5) and (6) close per load
against `K .uncompressible`/`K .replacementExclusion` and the selection's own
minimality (`lem:typeA-exits-discharged`), a surviving separator produces the
decorated envelope (`lem:typeA-cubic-switch-absorption` +
`lem:typeA-high-degree-handoff`), and the label-collision absorbing clause is
denied by target avoidance (`lem:labels`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExclusionRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAExclusion
    { Requires := [K .selection, K .replacementExclusion, K .cubicBaseline]
      Produces := [K .typeAExclusion]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let exclusion := (inputs.get (K .replacementExclusion)).down
      let cubic := (inputs.get (K .cubicBaseline)).down.1
      .cons (key := K .typeAExclusion)
        (show Value BranchState Presentation presentation data
            .typeAExclusion inputs.current from
          ⟨by
            classical
            dsimp only [Holds]
            letI : DecidableEq inputs.current.object.Vertex :=
              inputs.current.object.vertices.decEq
            intro packing valid maximal piece _subset connected negative
              zeroSurplus
            have avoids :
                ¬ Graph.HasCycleWithLength data.LengthOK
                  inputs.current.object := selection.1
            have minimality : ∀ representative : Graph.FiniteObject.{u},
                representative.LexicographicallySmaller inputs.current.object →
                Graph.MinimumDegreeAtLeast data.threshold representative →
                Graph.HasCycleWithLength data.LengthOK representative :=
              fun representative lex base =>
                selection.2 representative lex base
            -- The four-way per-load classification, derived once per routed
            -- load of any receiver: the exit-(4) witness, the route-8 entry,
            -- the exit-(5) trace-response quotient, or the exit-(7) surviving
            -- separator together with the decorated handoff envelope it
            -- produces.
            have perLoad : ∀ receiver : inputs.current.object.Vertex,
                ∀ load ∈ inputs.current.object.routedLoads piece
                    data.threshold receiver,
                (∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold data.dischargeScale receiver ∅,
                  witness.load = load) ∨
                  Graph.Route8.TraceBasin.Route8Entry inputs.current.object
                    piece data.threshold data.LengthOK receiver load ∨
                  (∃ basin : Finset inputs.current.object.Vertex,
                    Graph.Route8.TraceBasin.select? inputs.current.object piece
                        data.threshold receiver load = some basin ∧
                      ∃ retained,
                        Graph.Route8.TraceBasin.TraceResponseQuotient
                          inputs.current.object piece data.threshold
                          data.LengthOK receiver load basin retained) ∨
                  ((∃ basin : Finset inputs.current.object.Vertex,
                      Graph.Route8.TraceBasin.TraceSurvivingSeparator
                        inputs.current.object piece data.threshold
                        data.LengthOK receiver load basin) ∧
                    HandoffProduced data inputs.current.object packing
                      piece) := by
              intro receiver load routed
              by_cases quotient : ∃ basin : Finset inputs.current.object.Vertex,
                  Graph.Route8.TraceBasin.select? inputs.current.object piece
                      data.threshold receiver load = some basin ∧
                    ∃ retained,
                      Graph.Route8.TraceBasin.TraceResponseQuotient
                        inputs.current.object piece data.threshold
                        data.LengthOK receiver load basin retained
              · exact Or.inr (Or.inr (Or.inl quotient))
              by_cases separated : ∃ basin : Finset inputs.current.object.Vertex,
                  Graph.Route8.TraceBasin.TraceSurvivingSeparator
                    inputs.current.object piece data.threshold data.LengthOK
                    receiver load basin
              · refine Or.inr (Or.inr (Or.inr ⟨separated, ?_⟩))
                obtain ⟨basin, separator⟩ := separated
                obtain ⟨envelope, coreEq, decorated⟩ :=
                  Graph.Route8.TraceBasin.exists_envelope_of_traceSurvivingSeparator
                    (HighDegree := handoffHighDegree data inputs.current.object)
                    (Absorbing :=
                      handoffAbsorbing data inputs.current.object packing)
                    separator avoids
                    (fun vertex high => by
                      show data.threshold < inputs.current.object.degree vertex
                      rw [cubic]
                      exact high)
                    (fun centre first second collision =>
                      avoids
                        (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                          data.degenerateClosureRejected collision))
                exact ⟨envelope, coreEq, decorated⟩
              · rcases Graph.Route8.TraceBasin.exists_witness_or_route8Entry
                    (scale := data.dischargeScale) connected routed
                    (fun basin selectedEq quotientAt =>
                      quotient ⟨basin, selectedEq, quotientAt⟩)
                    exclusion avoids minimality
                    (not_exists.1 separated) with witness | entry
                · exact Or.inl witness
                · exact Or.inr (Or.inl entry)
            -- The published loads are routed loads of their receiver.
            have silentRouted : ∀ receiver : inputs.current.object.Vertex,
                ∀ load ∈ Graph.VisibleEntry.silentExcess inputs.current.object
                    piece data.threshold data.dischargeScale receiver,
                load ∈ inputs.current.object.routedLoads piece data.threshold
                  receiver := fun receiver load loadMem =>
              Graph.Route8.TraceBasin.silentExcess_subset_routedLoads
                inputs.current.object piece data.threshold data.dischargeScale
                receiver loadMem
            have selectedRouted :
                ∀ receiver outside : inputs.current.object.Vertex,
                ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                    data.threshold data.dischargeScale receiver outside ∅,
                load ∈ inputs.current.object.routedLoads piece data.threshold
                  receiver := by
              intro receiver outside load loadMem
              have inOrder := List.mem_of_mem_take loadMem
              have member : load ∈ Graph.ExitFour.unpeeledVisibleLoadsAt piece
                  data.threshold receiver outside ∅ := by
                simpa [inputs.current.object.mem_orderedVertices load] using
                  inOrder
              have unpeeled : load ∈ Graph.ExitFour.unpeeledLoads piece
                  data.threshold receiver ∅ :=
                (Finset.mem_inter.1 member).2
              rw [Graph.ExitFour.mem_unpeeledLoads] at unpeeled
              exact unpeeled.1
            refine ⟨?_, ?_⟩
            · -- The trichotomy, collapsed from the four-way split exactly as
              -- before: a witness feeds arm 1, a produced envelope feeds
              -- arm 3.
              by_cases witnessed : ∃ receiver : inputs.current.object.Vertex,
                  inputs.current.object.IsReceiver piece data.threshold
                      receiver ∧
                    Nonempty (Graph.ExitFour.Witness
                      (Graph.HasCycleWithLength data.LengthOK) piece
                      data.threshold data.dischargeScale receiver ∅)
              · exact Or.inl witnessed
              by_cases handoff :
                  HandoffProduced data inputs.current.object packing piece
              · exact Or.inr (Or.inr handoff)
              refine Or.inr (Or.inl ?_)
              intro receiver receiverMem
              have isReceiver : inputs.current.object.IsReceiver piece
                  data.threshold receiver :=
                Graph.FiniteObject.mem_receivers.mp
                  (Finset.mem_filter.1 receiverMem).1
              have collapse : ∀ load ∈ inputs.current.object.routedLoads piece
                  data.threshold receiver,
                  Graph.Route8.TraceBasin.Route8Entry inputs.current.object
                      piece data.threshold data.LengthOK receiver load ∨
                    ∃ basin : Finset inputs.current.object.Vertex,
                      Graph.Route8.TraceBasin.select? inputs.current.object
                          piece data.threshold receiver load = some basin ∧
                        ∃ retained,
                          Graph.Route8.TraceBasin.TraceResponseQuotient
                            inputs.current.object piece data.threshold
                            data.LengthOK receiver load basin retained := by
                intro load routed
                rcases perLoad receiver load routed with
                  ⟨witness, _⟩ | entry | quotient | ⟨_, produced⟩
                · exact absurd ⟨receiver, isReceiver, ⟨witness⟩⟩ witnessed
                · exact Or.inl entry
                · exact Or.inr quotient
                · exact absurd produced handoff
              constructor
              · intro load loadMem
                exact collapse load (silentRouted receiver load loadMem)
              · intro outside _portMem _overloaded load loadMem
                exact collapse load
                  (selectedRouted receiver outside load loadMem)
            · -- The additive per-load publication, read off the same four-way
              -- split at each saturated receiver.
              intro receiver _receiverMem
              constructor
              · intro load loadMem
                exact perLoad receiver load (silentRouted receiver load loadMem)
              · intro outside _portMem _overloaded load loadMem
                exact perLoad receiver load
                  (selectedRouted receiver outside load loadMem)⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
