import Hypostructure.Graph.AtomResponse
import Hypostructure.Graph.Induced
import Hypostructure.Graph.ReceiverExhaustion

/-!
# Target-defective graph peeling

This module turns a decidable, graph-derived defect predicate into the exact
finite peeling data consumed by receiver exhaustion.  The vertex order is the
order already stored in `FiniteObject`; the state is an active vertex support;
and termination is measured by its cardinality.
-/

namespace Hypostructure.Graph.TargetDefectivePeel

open Hypostructure

universe u uAmbient uBranch uData

/-- A target-defect test on the vertices of one finite graph.  Applications
provide only the semantic predicate and its decision procedure; scheduling and
accounting are derived below from the graph. -/
structure Profile (object : FiniteObject.{u}) where
  Defective : object.Vertex → Prop
  defectiveDecidable : DecidablePred Defective

namespace Profile

variable {object : FiniteObject.{u}} (profile : Profile object)

/-- The canonical defect schedule, retaining the graph's declared order. -/
def schedule : List object.Vertex :=
  let _ := profile.defectiveDecidable
  object.orderedVertices.filter fun vertex => decide (profile.Defective vertex)

@[simp]
theorem mem_schedule_iff (vertex : object.Vertex) :
    vertex ∈ profile.schedule ↔ profile.Defective vertex := by
  letI := profile.defectiveDecidable
  simp [schedule]

theorem schedule_nodup : profile.schedule.Nodup :=
  List.Nodup.filter _ object.orderedVertices_nodup

/-- Initially every graph vertex is active. -/
def initial (_profile : Profile object) : Finset object.Vertex :=
  object.vertexFinset

/-- The remaining graph is induced by the active support. -/
def residualObject (_profile : Profile object)
    (state : Finset object.Vertex) : FiniteObject :=
  object.induce state

/-- The well-founded measure is derived from the active support. -/
def measure (_profile : Profile object)
    (state : Finset object.Vertex) : Nat := state.card

@[simp]
theorem initial_measure :
    profile.measure profile.initial = object.vertexCount := by
  simp [measure, initial]

/-- One proof-carrying peel removes an active target-defective vertex. -/
structure Step (state : Finset object.Vertex) where
  vertex : object.Vertex
  active : vertex ∈ state
  defective : profile.Defective vertex

namespace Step

variable {profile} {state : Finset object.Vertex}

/-- The exact successor support. -/
def next (step : profile.Step state) : Finset object.Vertex :=
  @Finset.erase object.Vertex object.vertices.decEq state step.vertex

/-- The exact induced graph after the peel. -/
def residualObject (step : profile.Step state) : FiniteObject :=
  profile.residualObject step.next

@[simp]
theorem measure_next_lt (step : profile.Step state) :
    profile.measure step.next < profile.measure state := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simpa [Profile.measure, next] using Finset.card_erase_lt_of_mem step.active

theorem next_ssubset (step : profile.Step state) :
    step.next ⊂ state := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨by simpa [next] using Finset.erase_subset step.vertex state, by
      intro equal
      have erased : step.vertex ∉ step.next := by simp [next]
      exact erased (equal.symm ▸ step.active)⟩

end Step

/-- Active defects in canonical graph order. -/
def activeSchedule (state : Finset object.Vertex) : List object.Vertex :=
  let _ : DecidableEq object.Vertex := object.vertices.decEq
  profile.schedule.filter fun vertex => decide (vertex ∈ state)

theorem activeSchedule_nodup (state : Finset object.Vertex) :
    (profile.activeSchedule state).Nodup :=
  List.Nodup.filter _ profile.schedule_nodup

@[simp]
theorem mem_activeSchedule_iff (state : Finset object.Vertex)
    (vertex : object.Vertex) :
    vertex ∈ profile.activeSchedule state ↔
      vertex ∈ state ∧ profile.Defective vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [activeSchedule, and_comm]

/-- The first scheduled active defect, when one exists. -/
def firstStep? (state : Finset object.Vertex) : Option (profile.Step state) := by
  match first : profile.activeSchedule state with
  | [] => exact none
  | vertex :: _ =>
      exact some {
        vertex := vertex
        active := (profile.mem_activeSchedule_iff state vertex).mp
          (by simp [first]) |>.1
        defective := (profile.mem_activeSchedule_iff state vertex).mp
          (by simp [first]) |>.2 }

/-- Every peel chain has at most as many feedback steps as graph vertices:
the initial measure is computed from the graph, and every step decreases it. -/
theorem measure_le_vertexCount (state : Finset object.Vertex)
    (subset : state ⊆ profile.initial) :
    profile.measure state ≤ object.vertexCount := by
  rw [← profile.initial_measure]
  exact Finset.card_le_card subset

end Profile

/-- Inject a certified graph peel directly into the receiver-exhaustion peel
exit.  No exit number or application-specific continuation is involved. -/
def toReceiverPeel
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {CycleLengthOK : Nat → Prop}
    {interface : ReceiverExhaustion.TargetInterface P T CycleLengthOK}
    {Handoff Residual : Core.Strategy.ProblemInput P → Type uData}
    {input : Core.Strategy.ProblemInput P}
    {object : FiniteObject.{uData}} {profile : Profile object}
    {state : Finset object.Vertex}
    (step : profile.Step state) :
    ReceiverExhaustion.Exit interface
      (fun _ => profile.Step state) Handoff Residual input :=
  .peel step

end Hypostructure.Graph.TargetDefectivePeel
