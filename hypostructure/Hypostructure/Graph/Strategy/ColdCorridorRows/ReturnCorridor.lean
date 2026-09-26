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

/-! ## Node `[153]`, `def:cold-corridor-first-failure`: the cold return corridors

*"Order the boundary stubs of `K` lexicographically … choose inside `K` the
lexicographically first simple path joining the outside endpoint of `hᵢ` to the
outside endpoint of `hᵢ₊₁`.  Together with the two boundary stubs this path is
the cold return corridor of `ε`.  Thus each selected branch-excess half-edge has
exactly one corridor."*  The two-stub clause is `lem:bridgeless` read from the
ledger; the connection is the component's own. -/
@[reducible] noncomputable def coldReturnCorridorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldReturnCorridors
    { Requires := [K .bridgeless, K .hotColdPartition]
      Produces := [K .coldReturnCorridors]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridgeless := (inputs.get (K .bridgeless)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .coldReturnCorridors)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          let cubic := (canonicalColdWindows data object).filter
            (AmbientCubicWindow data object)
          let packing := canonicalWindowPacking data object
          let windows := coldCorridorWindows data object
          change HotColdWindowStatement data object at split
          obtain ⟨_validPacking, _attains, _maximal, _hot,
            coldIff, _disjoint, _cover⟩ := split
          change ColdReturnCorridorsStatement data object
          simp only [ColdReturnCorridorsStatement]
          refine ⟨?_, ?_, ?_⟩
          · intro component outside entry
            exact ⟨Graph.ColdCorridor.corridorOfOutsideComponent object windows
              component outside bridgeless entry, rfl⟩
          · intro epsilon
            by_cases outsideFoot : epsilon.1.2 ∉ windows
            · left
              have selected := Graph.ColdCorridor.selected_facts object cubic
                ⟨epsilon.1, epsilon.property⟩
              let component := Graph.ColdCorridor.outsideComponentOf object windows
                epsilon.1.2 outsideFoot
              have outside :=
                Graph.ColdCorridor.outsideComponentOf_isOutsideComponent object
                  windows epsilon.1.2 outsideFoot
              have footMem : epsilon.1.2 ∈ component :=
                Graph.ColdCorridor.foot_mem_outsideComponentOf object windows
                  epsilon.1.2 outsideFoot
              have sourceInWindows : epsilon.1.1 ∈ windows := by
                obtain ⟨window, windowMember, sourceMember⟩ :=
                  (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                    selected.1
                have windowPacking : window ∈ packing :=
                  ((coldIff window).1 (Finset.mem_filter.1 windowMember).1).1
                change epsilon.1.1 ∈ Graph.ColdCorridor.windowsOf object packing
                exact (Graph.ColdCorridor.mem_windowsOf object packing _).2
                  ⟨window, windowPacking, sourceMember⟩
              have boundaryMember : (epsilon.1.2, epsilon.1.1) ∈
                  Graph.ColdCorridor.boundaryStubs object windows component :=
                (Graph.ColdCorridor.mem_boundaryStubs_iff object windows component
                  (epsilon.1.2, epsilon.1.1)).2
                  ⟨footMem, sourceInWindows, selected.2.symm⟩
              let corridor := Graph.ColdCorridor.corridorOfBoundaryStub object
                windows component outside bridgeless
                (epsilon.1.2, epsilon.1.1) boundaryMember
              exact ⟨outsideFoot, component, corridor, outside,
                Graph.ColdCorridor.Corridor.corridorOfBoundaryStub_entryStub object windows
                  component outside bridgeless (epsilon.1.2, epsilon.1.1)
                  boundaryMember⟩
            · exact Or.inr (not_not.mp outsideFoot)
          · have partition := Finset.card_filter_add_card_filter_not
              (s := Graph.ColdCorridor.allSelectedStubs object cubic)
              (fun stub => stub.2 ∉ windows)
            simpa only [not_not] using partition.symm⟩
        .nil)

/-! ## Node `[145]`, declared F4 support registry

`def:cold-corridor-first-failure` reaches this residual only after the Type-B
and route-8 handoff edges have been taken.  This owner therefore publishes the
exact empty active F4 registry; the occurrence row reads it through
`inputs.get`. -/
@[reducible] noncomputable def coldDeclaredHandoffLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldDeclaredHandoffLedger
    { Requires := []
      Produces := [K .coldDeclaredHandoffLedger]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldDeclaredHandoffLedger)
        ⟨⟨fun _support => False, fun _support impossible => impossible⟩⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
