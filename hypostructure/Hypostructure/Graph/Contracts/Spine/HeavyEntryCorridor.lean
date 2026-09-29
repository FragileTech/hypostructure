import Hypostructure.Graph.Statements.HeavyEntryCorridor

/-!
# Contracts: the retained cold corridors of G as induced paths

Proof-agnostic contract lemma for `Statements/HeavyEntryCorridor.lean`.  Its one
hypothesis is the ledger fact `K .windowFreeGeometry`, the window-free geometry of the
canonical maximal packing; the rest is the shortestness of G's canonical corridor
(`Graph/ColdCorridorRuns.lean`).

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.HeavyEntryCorridor

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

/-- The deleted windows `X_cold` lie in the window support of the canonical packing. -/
theorem coldCorridorWindows_subset (data : Parameters) (object : Graph.FiniteObject.{u}) :
    coldCorridorWindows data object ⊆
      Graph.FiniteObject.windowSupport (canonicalWindowPacking data object) := by
  classical
  intro v hv
  unfold coldCorridorWindows at hv
  rw [Graph.ColdCorridor.mem_windowsOf] at hv
  obtain ⟨window, hwindow, hvw⟩ := hv
  have inPacking : window ∈ canonicalWindowPacking data object := by
    simp only [canonicalColdWindows, Finset.mem_filter, Finset.mem_sdiff] at hwindow
    exact hwindow.1.1
  exact Graph.FiniteObject.mem_windowSupport inPacking hvw

/-- **`ColdCorridorInducedRunsStatement` from the window-free geometry of `P₀`.** -/
theorem coldCorridorInducedRuns_holds (data : Parameters) (object : Graph.FiniteObject.{u})
    (geometry : Graph.JointObject.WindowFreeGeometry object
      (canonicalWindowPacking data object)) :
    ColdCorridorInducedRunsStatement data object := by
  intro occurrence epsilon
  have outside := (coldOccurrenceStateFacts data object occurrence epsilon).1
  refine ⟨fun i j hij hj => ?_, fun i j hij hj joined => ?_⟩
  · exact Graph.ColdCorridor.Corridor.inside_induced
      (coldOccurrenceCorridorAt data object occurrence epsilon) hij hj
  · refine Graph.ColdCorridor.Corridor.inside_run_short
      (coldOccurrenceCorridorAt data object occurrence epsilon) outside
      {v | v ∉ (↑(Graph.FiniteObject.windowSupport
        (canonicalWindowPacking data object)) : Set object.Vertex)} ?_ ?_ hij hj joined
    · intro v hv hvw
      exact hv (coldCorridorWindows_subset data object (Finset.mem_coe.1 hvw))
    · intro u v reach
      obtain ⟨k, g, hk, walk, g0, gk, _⟩ := geometry.1 _ (fun v hv => hv) u v reach
      exact ⟨k, hk, g, walk, g0, gk⟩

end Hypostructure.Graph.Contracts.Spine.HeavyEntryCorridor
