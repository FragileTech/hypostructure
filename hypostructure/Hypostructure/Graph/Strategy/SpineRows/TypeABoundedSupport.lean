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

/-! ## Node `[87]`: the bounded selected Type A support

The selected support from `[86]` is a canonical connected piece of the
remainder.  Node `[27]` therefore makes its induced graph
`P_windowOrder`-free.  Between two vertices, take a shortest path in that
induced graph.  Every subpath is again shortest, so an ambient chord would
force two nonconsecutive indices to have distance one; hence the path is
induced.  Its length is at most `windowOrder - 2`.

Zero assigned surplus, together with the standing baseline, makes every
vertex of this same piece have degree `threshold = 3`.  Rooting the piece at
one of its vertices and applying the subcubic breadth-first bound at radius
`windowOrder - 2` gives
`1 + threshold * (2^(windowOrder - 2) - 1)`.  In the registered Erdős–Gyárfás
presentation these are exactly `diam(X) ≤ 11` and `|X| ≤ 6142`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeABoundedSupportRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeABoundedSupport
    { Requires := [K .typeALowSurplus, K .remainderNormalized]
      Produces := [K .typeABoundedSupport]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let low := (show Value BranchState Presentation presentation data
          .typeALowSurplus inputs.current from
        inputs.get (K .typeALowSurplus)).down
      let normalized := (show Value BranchState Presentation presentation data
          .remainderNormalized inputs.current from
        inputs.get (K .remainderNormalized)).down
      .cons (key := K .typeABoundedSupport)
        (show Value BranchState Presentation presentation data
            .typeABoundedSupport inputs.current from ⟨by
          classical
          obtain ⟨packing, _canonical, valid, maximal, component, present, negative,
            zeroSurplus⟩ := low
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          have inside : piece ⊆ inputs.current.object.remainderSupport packing :=
            inputs.current.object.pieceSupport_subset
              (inputs.current.object.remainderSupport packing) component
          have connected :
              Graph.SupportComponents.Connected.ConnectedOn
                inputs.current.object piece :=
            Graph.SupportComponents.Connected.connectedOn_of_mem_order
              inputs.current.object
              (inputs.current.object.remainderSupport packing)
              ((inputs.current.object.mem_canonicalPieces
                (inputs.current.object.remainderSupport packing)).mp present)
          have pieceFree : Graph.InducedPathFree
              (inputs.current.object.induce piece) data.windowOrder :=
            inputs.current.object.inducedPathFree_induce_of_forall
              (fun inner contained =>
                (normalized packing valid maximal inner
                  (contained.trans inside)).1)
          have exactDegree : ∀ vertex ∈ piece,
              inputs.current.object.degree vertex = data.threshold := by
            intro vertex member
            have lower : data.threshold ≤
                inputs.current.object.degree vertex :=
              le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have summand :
                inputs.current.object.degree vertex - data.threshold = 0 :=
              Nat.eq_zero_of_le_zero
                (zeroSurplus ▸ Finset.single_le_sum
                  (f := fun other =>
                    inputs.current.object.degree other - data.threshold)
                  (fun _ _ => Nat.zero_le _) member)
            omega
          letI : FinEnum inputs.current.object.Vertex :=
            inputs.current.object.vertices
          letI : Fintype inputs.current.object.Vertex := inferInstance
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          letI : DecidableRel inputs.current.object.graph.Adj :=
            inputs.current.object.decideAdj
          have bounded : ∀ left ∈ piece, ∀ right ∈ piece,
              ∃ path : inputs.current.object.graph.Walk left right,
                path.IsPath ∧
                  (∀ vertex ∈ path.support, vertex ∈ piece) ∧
                  path.length ≤ data.windowOrder - 2 := by
            intro left leftMem right rightMem
            obtain ⟨initial, _initialPath, initialInside⟩ :=
              connected.2 leftMem rightMem
            let induced := initial.induce
              (↑piece : Set inputs.current.object.Vertex) initialInside
            obtain ⟨shortest, shortestPath, shortestLength⟩ :=
              induced.reachable.exists_path_of_dist
            have shortestBound :
                shortest.length ≤ data.windowOrder - 2 := by
              exact Graph.shortestPath_length_le_order_sub_two
                (inputs.current.object.induce piece) data.windowOrder
                data.three_le_windowOrder shortest shortestPath shortestLength
                pieceFree
            let embedding := inputs.current.object.induceEmbedding piece
            let ambient := shortest.map embedding.toHom
            have ambientPath : ambient.IsPath :=
              (SimpleGraph.Walk.map_isPath_iff_of_injective
                embedding.injective).2 shortestPath
            have ambientInside : ∀ vertex ∈ ambient.support,
                vertex ∈ piece := by
              intro vertex member
              simp only [ambient, SimpleGraph.Walk.support_map,
                List.mem_map] at member
              obtain ⟨inner, _innerMem, rfl⟩ := member
              exact inner.2
            have ambientLength :
                ambient.length ≤ data.windowOrder - 2 := by
              rw [SimpleGraph.Walk.length_map]
              exact shortestBound
            exact ⟨ambient, ambientPath, ambientInside, ambientLength⟩
          obtain ⟨root, rootMem⟩ := connected.1
          have pieceSubset : piece ⊆
              Graph.SubcubicReach.reach inputs.current.object.graph piece
                root (data.windowOrder - 2) root := by
            intro vertex vertexMem
            obtain ⟨path, pathIsPath, pathInside, pathLength⟩ :=
              bounded root rootMem vertex vertexMem
            exact (Graph.SubcubicReach.mem_reach
              inputs.current.object.graph).2
              ⟨path, pathIsPath, pathLength,
                (fun z zMem =>
                  pathInside z (List.mem_of_mem_dropLast zMem)),
                fun notNil same => by
                  have atStart :=
                    (pathIsPath.getVert_eq_start_iff_of_not_nil
                      (i := 1) notNil).1 same
                  exact absurd atStart (by decide)⟩
          have cardinality : piece.card ≤
              1 + data.threshold *
                (2 ^ (data.windowOrder - 2) - 1) := by
            calc
              piece.card ≤
                  (Graph.SubcubicReach.reach inputs.current.object.graph piece
                    root (data.windowOrder - 2) root).card :=
                Finset.card_le_card pieceSubset
              _ ≤ 1 + data.threshold *
                  (2 ^ (data.windowOrder - 2) - 1) := by
                have reachBound :=
                  Graph.SubcubicReach.card_reach_le
                    (G := inputs.current.object.graph) (S := piece)
                    (fun vertex vertexMem => by
                      simpa [Graph.FiniteObject.degree,
                        data.threshold_eq_three] using
                          le_of_eq (exactDegree vertex vertexMem))
                    root (data.windowOrder - 2)
                simpa [data.threshold_eq_three] using reachBound
          exact ⟨packing, valid, maximal, component, present, negative,
            zeroSurplus, pieceFree, bounded, cardinality⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
