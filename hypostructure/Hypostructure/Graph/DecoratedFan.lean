import Hypostructure.Graph.Finite
import Hypostructure.Graph.ReceiverExhaustion

/-!
# Proof-carrying decorated fans

A decorated fan is finite graph data: one hub, a finite rim support, and a
simple hub-to-rim walk for every rim vertex.  Distinct decorations have
disjoint interiors.  Its deterministic schedule and all size bounds are
derived from the packed graph rather than supplied as numeric parameters.
-/

namespace Hypostructure.Graph.DecoratedFan

open Hypostructure

universe u uAmbient uBranch uData

/-- One spoke together with its graph-theoretic proof. -/
structure Decoration (object : FiniteObject.{u})
    (hub rim : object.Vertex) where
  walk : object.graph.Walk hub rim
  isPath : walk.IsPath
  nontrivial : 0 < walk.length

/-- A fan whose decorations are literal paths in the supplied graph.  The rim
is a support, not an externally numbered list. -/
structure Certificate (object : FiniteObject.{u}) where
  hub : object.Vertex
  rim : Finset object.Vertex
  hub_not_mem_rim : hub ∉ rim
  decoration : ∀ rimVertex, rimVertex ∈ rim →
    Decoration object hub rimVertex
  internallyDisjoint : ∀ ⦃left right⦄
    (left_mem : left ∈ rim) (right_mem : right ∈ rim),
    left ≠ right →
    ((decoration left left_mem).walk.support.tail).Disjoint
      ((decoration right right_mem).walk.support.tail)

namespace Certificate

variable {object : FiniteObject.{u}} (fan : Certificate object)

/-- Canonical rim order inherited from the graph's declared vertex order. -/
def schedule : List object.Vertex :=
  let _ : DecidableEq object.Vertex := object.vertices.decEq
  object.orderedVertices.filter fun vertex => decide (vertex ∈ fan.rim)

@[simp]
theorem mem_schedule_iff (vertex : object.Vertex) :
    vertex ∈ fan.schedule ↔ vertex ∈ fan.rim := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [schedule]

theorem schedule_nodup : fan.schedule.Nodup :=
  List.Nodup.filter _ object.orderedVertices_nodup

@[simp]
theorem schedule_length :
    fan.schedule.length = fan.rim.card := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [← List.toFinset_card_of_nodup fan.schedule_nodup]
  congr
  ext vertex
  simp

/-- The schedule bound is computed solely from the ambient finite graph. -/
theorem schedule_length_le_vertexCount :
    fan.schedule.length ≤ object.vertexCount := by
  rw [fan.schedule_length, ← object.card_vertexFinset]
  exact Finset.card_le_card (fun _ _ => object.mem_vertexFinset _)

/-- A nonempty decorated fan has a canonical first rim vertex and its verified
decoration; no path ordering is supplied by an application. -/
def firstDecoration (nonempty : fan.rim.Nonempty) :
    Σ rimVertex, Decoration object fan.hub rimVertex := by
  have scheduleNonempty : fan.schedule ≠ [] := by
    intro empty
    obtain ⟨vertex, member⟩ := nonempty
    have : vertex ∈ fan.schedule := (fan.mem_schedule_iff vertex).2 member
    simp [empty] at this
  let vertex := fan.schedule.head scheduleNonempty
  exact ⟨vertex, fan.decoration vertex
    ((fan.mem_schedule_iff vertex).1
      (List.head_mem scheduleNonempty))⟩

/-- Prefixes used by finite fan executors are taken from the derived schedule. -/
def initialSegment (count : Nat) : List object.Vertex :=
  fan.schedule.take count

theorem initialSegment_nodup (count : Nat) :
    (fan.initialSegment count).Nodup :=
  fan.schedule_nodup.take

theorem initialSegment_length_le (count : Nat) :
    (fan.initialSegment count).length ≤ object.vertexCount := by
  calc
    (fan.initialSegment count).length ≤ fan.schedule.length := by
      simp [initialSegment]
    _ ≤ object.vertexCount := fan.schedule_length_le_vertexCount

end Certificate

/-- Inject a proof-carrying decorated fan directly into the receiver handoff
exit.  The downstream handoff receives the concrete graph object unchanged. -/
def toReceiverHandoff
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {CycleLengthOK : Nat → Prop}
    {interface : ReceiverExhaustion.TargetInterface P T CycleLengthOK}
    {Step Residual : Core.Strategy.ProblemInput P → Type uData}
    {input : Core.Strategy.ProblemInput P}
    {object : FiniteObject.{uData}}
    (fan : Certificate object) :
    ReceiverExhaustion.Exit interface Step
      (fun _ => Certificate object) Residual input :=
  .handoff fan

end Hypostructure.Graph.DecoratedFan
