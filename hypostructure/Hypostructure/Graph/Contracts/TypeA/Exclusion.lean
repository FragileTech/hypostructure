import Hypostructure.Graph.Contracts.TypeA.Exits
import Hypostructure.Graph.Statements.RouteEight

/-!
# Contracts: the Type A exclusion lemma

`lem:typeA-exclusion` (via `lem:density-mersenne`) at one connected negative
zero-surplus support, instantiated at the canonical pieces of `G`'s fixed
packing `P₀`.
-/

namespace Hypostructure.Graph.Contracts.TypeA

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- `lem:typeA-exclusion` at one connected support: it leaves through the
target-defect exit, the silent-core residual profile, or the decorated
handoff.  Each unpaid silent load and each selected visible unpeeled load of a
saturated receiver realizes the four-way split of
`lem:typeA-reduced-silent-residual` with the exit-`(7)` routing of
`lem:typeA-exits-discharged`, and the three alternatives collect that split. -/
theorem typeAExclusionTrichotomy_of_connected
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : Graph.FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      Graph.HasCycleWithLength data.LengthOK representative)
    (exclusion : ReplacementExclusionStatement data object)
    {piece : Finset object.Vertex}
    (connected : Graph.SupportComponents.Connected.ConnectedOn object piece)
    (negative : object.NegativeNetCharge piece data.threshold data.dischargeScale)
    (zeroSurplus : object.ambientSurplus piece data.threshold = 0)
    (routing : ZeroSurplusRoutingAt data object piece) :
    TypeAExclusionTrichotomy data object piece := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have perLoad : ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale,
      ∀ load ∈ object.routedLoads piece data.threshold receiver,
      (∃ witness : Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) piece
          data.threshold data.dischargeScale receiver ∅,
        witness.load = load) ∨
        Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
          data.LengthOK receiver load ∨
        (∃ basin : Finset object.Vertex,
          Graph.Route8.TraceBasin.select? object piece data.threshold receiver
              load = some basin ∧
            ∃ retained,
              Graph.Route8.TraceBasin.TraceResponseQuotient object piece
                data.threshold data.LengthOK receiver load basin retained) ∨
        ((∃ basin : Finset object.Vertex,
            Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece
              data.threshold data.LengthOK receiver load basin) ∧
          SeparatorHandoffAt data object piece) := by
    intro receiver receiverSaturated load routed
    by_cases quotient : ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object piece data.threshold receiver
            load = some basin ∧
          ∃ retained,
            Graph.Route8.TraceBasin.TraceResponseQuotient object piece
              data.threshold data.LengthOK receiver load basin retained
    · exact Or.inr (Or.inr (Or.inl quotient))
    by_cases separated : ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece
          data.threshold data.LengthOK receiver load basin
    · -- Exit (7): the surviving first separator at this receiver
      -- is `SeparatorHandoffAt` of the piece (`lem:typeA-high-degree-handoff`).
      obtain ⟨basin, separator⟩ := separated
      exact Or.inr (Or.inr (Or.inr ⟨⟨basin, separator⟩,
        receiver, (Finset.mem_filter.1 receiverSaturated).1, load, separator⟩))
    · rcases Graph.Route8.TraceBasin.exists_witness_or_route8Entry
          (scale := data.dischargeScale) connected routed
          (fun basin selectedEq quotientAt =>
            quotient ⟨basin, selectedEq, quotientAt⟩)
          exclusion avoids minimality
          (not_exists.1 separated) with witness | entry
      · exact Or.inl witness
      · exact Or.inr (Or.inl entry)
  have silentRouted : ∀ receiver : object.Vertex,
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
      load ∈ object.routedLoads piece data.threshold receiver :=
    fun receiver _load loadMem =>
      Graph.Route8.TraceBasin.silentExcess_subset_routedLoads object piece
        data.threshold data.dischargeScale receiver loadMem
  have selectedRouted : ∀ receiver outside : object.Vertex,
      ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
          data.threshold data.dischargeScale receiver outside ∅,
      load ∈ object.routedLoads piece data.threshold receiver := by
    intro receiver outside load loadMem
    have inOrder := List.mem_of_mem_take loadMem
    have member : load ∈ Graph.ExitFour.unpeeledVisibleLoadsAt piece
        data.threshold receiver outside ∅ := by
      simpa [object.mem_orderedVertices load] using inOrder
    have unpeeled : load ∈ Graph.ExitFour.unpeeledLoads piece data.threshold
        receiver ∅ :=
      (Finset.mem_inter.1 member).2
    rw [Graph.ExitFour.mem_unpeeledLoads] at unpeeled
    exact unpeeled.1
  by_cases witnessed : ∃ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver ∧
        Nonempty (Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
          data.dischargeScale receiver ∅)
  · exact Or.inl witnessed
  by_cases handoff : SeparatorHandoffAt data object piece
  · exact Or.inr (Or.inr handoff)
  refine Or.inr (Or.inl ⟨?_, ?_⟩)
  · -- `lem:typeA-unsaturated-discharge` (the 3/7/11 charge): with `σ(X) = 0`
    -- and total routing, all receivers unsaturated would give
    -- `|V(X)| ≤ s·def⁺(X)`, against `N₀(X) < 0`.
    by_contra noSaturated
    have bound := Graph.FiniteObject.card_le_scaled_deficiency_of_no_saturated
      object piece data.threshold data.dischargeScale zeroSurplus routing.1
      (fun receiver isReceiver saturated => noSaturated
        ⟨receiver, Finset.mem_filter.2
          ⟨Graph.FiniteObject.mem_receivers.mpr isReceiver, saturated⟩⟩)
    unfold Graph.FiniteObject.NegativeNetCharge at negative
    rw [zeroSurplus] at negative
    omega
  intro receiver receiverMem
  have isReceiver : object.IsReceiver piece data.threshold receiver :=
    Graph.FiniteObject.mem_receivers.mp (Finset.mem_filter.1 receiverMem).1
  have collapse : ∀ load ∈ object.routedLoads piece data.threshold receiver,
      Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
          data.LengthOK receiver load ∨
        ∃ basin : Finset object.Vertex,
          Graph.Route8.TraceBasin.select? object piece data.threshold
              receiver load = some basin ∧
            ∃ retained,
              Graph.Route8.TraceBasin.TraceResponseQuotient object piece
                data.threshold data.LengthOK receiver load basin retained := by
    intro load routed
    rcases perLoad receiver receiverMem load routed with
      ⟨witness, _⟩ | entry | quotient | ⟨_, produced⟩
    · exact absurd ⟨receiver, isReceiver, ⟨witness⟩⟩ witnessed
    · exact Or.inl entry
    · exact Or.inr quotient
    · exact absurd produced handoff
  constructor
  · intro load loadMem
    exact collapse load (silentRouted receiver load loadMem)
  · intro outside _portMem _overloaded load loadMem
    exact collapse load (selectedRouted receiver outside load loadMem)

/-- `lem:typeA-exclusion` at the canonical pieces of `P₀`: every canonical piece
of `R(P₀)` is connected and lies in `R(P₀)`, so node `[13]`'s normalization
routes it (`zeroSurplusRoutingAt_of_normalized`), and a negative zero-surplus
one realizes the trichotomy, its residual-profile alternative at an existing
saturated receiver. -/
theorem typeAExclusion
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : Graph.FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      Graph.HasCycleWithLength data.LengthOK representative)
    (exclusion : ReplacementExclusionStatement data object)
    (normalized : RemainderNormalizedStatement data object) :
    TypeAExclusionStatement data object := by
  intro component componentMem negative zeroSurplus
  exact typeAExclusionTrichotomy_of_connected data object avoids minimality
    exclusion
    (Graph.SupportComponents.Connected.connectedOn_of_mem_order object _
      ((Graph.FiniteObject.mem_canonicalPieces _ _).1 componentMem))
    negative zeroSurplus
    (zeroSurplusRoutingAt_of_normalized data object normalized
      (object.pieceSupport_subset _ component) zeroSurplus)

end Hypostructure.Graph.Contracts.TypeA
