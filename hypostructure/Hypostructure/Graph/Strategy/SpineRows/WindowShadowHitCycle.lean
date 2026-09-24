import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.WindowShadowHit

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The recorded-hit certificate (O1), with its actual simple cycle and exact
length. All vertices and walks belong to the executor's current object. -/
@[reducible] noncomputable def windowShadowHitCycleRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowHitCycle
    { Requires := []
      Produces := [K .windowShadowHitCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowHitCycle)
        (show Value BranchState Presentation presentation data
            .windowShadowHitCycle inputs.current from ⟨by
          classical
          intro window x y a b corridor corridorPath corridorAvoids
            attachA attachB edgesDistinct hit
          obtain ⟨arc, arcPath, arcLength, arcWindow⟩ :=
            Graph.WindowShadowHit.exists_window_arc window a b
          let tail := corridor.append (SimpleGraph.Walk.cons attachB arc)
          have tailPath : tail.IsPath := by
            have supportEq : tail.support = corridor.support ++
                (SimpleGraph.Walk.cons attachB arc).support.tail :=
              SimpleGraph.Walk.support_append _ _
            rw [SimpleGraph.Walk.isPath_def, supportEq,
              SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_append]
            refine ⟨corridorPath.support_nodup, arcPath.support_nodup, ?_⟩
            intro v vCorridor v' vArc
            obtain ⟨i, rfl⟩ := arcWindow v' vArc
            intro same
            exact corridorAvoids i (same ▸ vCorridor)
          have edgeFresh : s(window a, x) ∉ tail.edges := by
            intro member
            rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
              List.mem_append, List.mem_cons] at member
            rcases member with corridorEdge | attachEdge | arcEdge
            · exact corridorAvoids a
                (corridor.fst_mem_support_of_mem_edges corridorEdge)
            · exact edgesDistinct (by
                rw [Sym2.eq_swap] at attachEdge
                exact attachEdge)
            · obtain ⟨i, eq⟩ :=
                arcWindow x (arc.snd_mem_support_of_mem_edges arcEdge)
              exact corridorAvoids i (eq ▸ corridor.start_mem_support)
          let cycle := SimpleGraph.Walk.cons attachA tail
          have isCycle : cycle.IsCycle :=
            (SimpleGraph.Walk.cons_isCycle_iff tail attachA).mpr
              ⟨tailPath, edgeFresh⟩
          have length : cycle.length =
              corridor.length + 2 + Nat.dist a.1 b.1 := by
            simp only [cycle, tail, SimpleGraph.Walk.length_cons,
              SimpleGraph.Walk.length_append, arcLength]
            omega
          refine ⟨cycle, isCycle, length, ?_⟩
          rw [length]
          exact Graph.WindowAttachmentShadow.accepted_of_mem_shadow hit⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
