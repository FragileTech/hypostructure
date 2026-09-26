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

/-! ## Node `[162]`, `lem:dense-cold-pass`: terminality in the remainder

The corridor producer records that its component and selected path lie in the
normalized remainder of the fixed maximal packing.  This row consumes that
literal state together with node `[27]`'s normalization fact.  The canonical
path is shortest by `FinitePathSelection.selectOfReachable_length_le`; an
induced-`P_windowOrder`-free remainder therefore bounds its length by
`windowOrder - 2`, which is below the registered cold-state bound. -/
@[reducible] noncomputable def denseColdCorridorsTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.denseColdCorridorsTerminal
    { Requires := [K .coldCorridorState, K .remainderNormalized,
        K .hotColdPartition]
      Produces := [K .denseColdCorridorsTerminal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let state := (inputs.get (K .coldCorridorState)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .denseColdCorridorsTerminal)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change HotColdWindowStatement data.toParameters object at split
          change ColdCorridorStateStatement data.toParameters object at state
          obtain ⟨validPacking, _attains, maximal, _hot,
            _coldIff, _disjoint, _cover⟩ := split
          change DenseColdCorridorsTerminalStatement data.toParameters object
          refine ⟨state, ?_⟩
          let stateOne := Classical.choose_spec state
          let componentAt := Classical.choose stateOne
          let stateTwo := Classical.choose_spec stateOne
          let corridorAt := Classical.choose stateTwo
          let stateTail := Classical.choose_spec stateTwo
          let _presentationAt := Classical.choose stateTail
          let stateBundle := Classical.choose_spec
            (Classical.choose_spec stateTail)
          have componentInR := stateBundle.2.2.2.1
          change ∀ epsilon : ColdEligibleHalfEdge data.toParameters object,
            Graph.ColdCorridor.Corridor.TerminalCorridor
              (corridorAt epsilon) data.coldSignature
          intro epsilon
          let component := componentAt epsilon
          let corridor := corridorAt epsilon
          have componentFree : Graph.InducedPathFree (object.induce component)
              data.windowOrder :=
            object.inducedPathFree_induce_of_forall
              (fun support inside =>
                (normalized (canonicalWindowPacking data.toParameters object) validPacking
                  maximal support
                  (inside.trans (componentInR epsilon))).1)
          obtain ⟨shortest, shortestPath, shortestLength⟩ :=
            corridor.connected.exists_path_of_dist
          have shortestBound : shortest.length ≤ data.windowOrder - 2 :=
            Graph.shortestPath_length_le_order_sub_two
              (object.induce component) data.windowOrder
              data.three_le_windowOrder shortest shortestPath shortestLength
              componentFree
          have selectedBound : corridor.inside.1.length ≤ shortest.length := by
            exact corridor.inside_length_le ⟨shortest, shortestPath⟩
          change corridor.statesRead ≤
            Graph.ColdCorridor.stateBound data.coldSignature
          have orderBound :=
            Graph.ColdCorridor.windowOrder_le_stateBound data.coldSignature
          have threeLeOrder := data.three_le_windowOrder
          change corridor.inside.1.length + 1 ≤
            Graph.ColdCorridor.stateBound data.coldSignature
          rw [data.coldSignature_windowOrder] at orderBound
          omega⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
