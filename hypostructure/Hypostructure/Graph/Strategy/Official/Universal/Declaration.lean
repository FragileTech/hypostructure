import Hypostructure.Core.Strategy.Official.Syntax
import Hypostructure.Core.Strategy.Official.Schema
import Hypostructure.Graph.Strategy.Official.Kernel
import Hypostructure.Graph.Strategy.Official.Target
import Hypostructure.Graph.Strategy.Official.Semantics.Terminal
import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.Replacement
import Hypostructure.Graph.External.HegdeSandeepShashank
import Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger

/-!
# Universal official graph declarations

One declaration applies the same closed `Program` to every finite graph.
Applications provide only mathematical problem data and the program.  All
finite schedules and observables are reconstructed by Graph from the current
`FiniteObject`; there is no per-object schema, result table, classifier, or
executor field.
-/

namespace Hypostructure.Graph.Strategy.Official.Universal

open Hypostructure.Core.Strategy.Official
open Hypostructure.Core.Strategy.OfficialRegistry
open Hypostructure.Graph

universe u

/-- Closed graph-baseline language.  A declaration supplies only parameters;
Graph owns the predicate and every structural preservation theorem attached to
it.  New baseline families must be added here together with their Graph
semantics, rather than supplied as executable application callbacks. -/
inductive BaselineSpec where
  | minimumDegreeAtLeast (threshold : Nat)
  deriving DecidableEq, Repr

namespace BaselineSpec

/-- Framework interpretation of a closed baseline description. -/
def Holds : BaselineSpec → FiniteObject.{u} → Prop
  | .minimumDegreeAtLeast threshold => MinimumDegreeAtLeast threshold

structure MinimumDegreeThreeConsequence (spec : BaselineSpec) :
    Type (u + 1) where
  apply : ∀ object : FiniteObject.{u}, spec.Holds object →
    3 ≤ object.minDegree

/-- The deletion-criticality profile is reconstructed from baseline data. -/
def deletionProfile (spec : BaselineSpec) :
    DeletionCriticalityProfile spec.Holds :=
  match spec with
  | .minimumDegreeAtLeast threshold =>
      minimumDegreeDeletionCriticalityProfile threshold

/-- Closed minimum-degree baselines are recovered from the threshold carried
by their deletion profile.  This is the framework-owned adapter used by
suppression and contraction strategies after they prove the exact threshold
inequality on a derived graph. -/
theorem holds_of_deletionProfile_threshold
    (spec : BaselineSpec) (object : FiniteObject.{u})
    (lower : spec.deletionProfile.threshold ≤ object.minDegree) :
    spec.Holds object := by
  cases spec with
  | minimumDegreeAtLeast threshold =>
      exact lower

/-- Isomorphism invariance is reconstructed from the closed baseline family. -/
def isomorphismInvariant (spec : BaselineSpec) :
    FiniteObject.IsomorphismInvariant spec.Holds := by
  cases spec with
  | minimumDegreeAtLeast threshold =>
      exact {
        iff_of_iso := by
          intro left right equivalent
          simp only [Holds, MinimumDegreeAtLeast]
          rw [FiniteObject.minDegree_eq_of_isomorphic equivalent]
      }

/-- Normalized local replacement preservation for the closed baseline. -/
def normalizedReplacementProfile (spec : BaselineSpec) :
    NormalizedAtomReplacementProfile spec.Holds := by
  cases spec with
  | minimumDegreeAtLeast threshold =>
      exact {
        LocalBaseline := BoundaryPiece.InternalThresholdBaseline threshold
        baselinePreserved := by
          intro boundary source replacement boundaryNonempty outside
            noBoundaryEdges localDegrees replacementInternal sourceBaseline
          exact
            glue_minDegree_ge_of_local_boundary_eq_of_context_noBoundaryEdges
              threshold outside boundaryNonempty noBoundaryEdges localDegrees
              replacementInternal sourceBaseline
      }

/-- Graph-owned degree-surplus baseline reconstructed from the closed
baseline and its proof on the current object. -/
def degreeSurplusBaseline (spec : BaselineSpec)
    (object : FiniteObject.{u}) (baseline : spec.Holds object) :
    Features.DegreeSurplusLedger.MinimumDegreeBaseline object :=
  match spec with
  | .minimumDegreeAtLeast threshold =>
      {
        degree := threshold
        lower := fun vertex =>
          baseline.trans (object.minDegree_le_degree vertex)
      }

/-- A minimum-degree-three consequence, when it follows from the closed
baseline parameter. -/
noncomputable def minimumDegreeThree?
    (spec : BaselineSpec) :
    Option (MinimumDegreeThreeConsequence.{u} spec) :=
  match spec with
  | .minimumDegreeAtLeast threshold =>
      if enough : 3 ≤ threshold then
        some ⟨fun _ baseline => enough.trans baseline⟩
      else none

end BaselineSpec

/-- The safe author-facing boundary for a graph theorem.  The two functions
are precisely the mathematical target predicate and the closed program.
Neither can produce a strategy result or influence program routing. -/
structure Declaration where
  baseline : BaselineSpec
  targetSpec : CycleTargetSpec
  schema : ProblemSchema := {}
  program : Program

namespace Declaration

variable (declaration : Declaration)

/-- The target interface is interpreted by Graph from closed data. -/
noncomputable abbrev target : CycleTargetInterface :=
  declaration.targetSpec.interface

structure InducedPathFreeTargetClosure : Type (u + 1) where
  apply : ∀ object : FiniteObject.{u},
    3 ≤ object.minDegree →
    InducedPathFree object
      External.HegdeSandeepShashank.inducedPathOrder →
    HasCycleWithLength declaration.target.CycleLengthOK object

/-- Registered induced-path-free target closure, available exactly for the
closed target family covered by the framework theorem. -/
noncomputable def inducedPathFreeTarget? :
    Option (InducedPathFreeTargetClosure.{u} declaration) :=
  match targetSpecEq : declaration.targetSpec with
  | .powersOfTwoFromExponentTwo =>
      some ⟨by
        intro object minimumDegree free
        have predicateEq :
            declaration.target.CycleLengthOK =
              (fun length =>
                ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) := by
          funext length
          apply propext
          simp [target, targetSpecEq, CycleTargetSpec.interface,
            CycleTargetSpec.CycleLengthOK]
        rw [predicateEq]
        exact
          External.HegdeSandeepShashank.finiteObject_p13Free_hasPowerOfTwoCycle
            object minimumDegree free⟩
  | .finiteLengths _ => none

/-- The baseline predicate is interpreted by Graph from closed data. -/
abbrev Baseline : FiniteObject.{u} → Prop :=
  declaration.baseline.Holds

/-- The corresponding Core problem contains no presentation or execution
extension point. -/
def problem : Core.Problem.{u + 1, 0} :=
  Graph.problem declaration.Baseline (fun _ => Unit)

/-- Graph presentation generated afresh from the current object. -/
noncomputable def presentation (object : FiniteObject.{u}) :
    Official.Presentation.{u} where
  object := object
  target := declaration.target

end Declaration

/-- Every induced-path embedding of every order bounded by the object size.
This is a dependent, graph-derived candidate type rather than an authored
path table. -/
abbrev PathCandidate (object : FiniteObject.{u}) :=
  Σ order : Nat, InducedPathMaximalPacking.Window object order

/-- Complete canonical enumeration of the graph-derived path candidates. -/
noncomputable def pathCandidates (object : FiniteObject.{u}) :
    List (PathCandidate object) :=
  (List.range (object.vertexCount + 1)).flatMap fun order =>
    (InducedPathMaximalPacking.windowSchedule object order).values.map
      fun window => ⟨order, window⟩

theorem mem_pathCandidates_of_le (object : FiniteObject.{u})
    (candidate : PathCandidate object)
    (bounded : candidate.1 ≤ object.vertexCount) :
    candidate ∈ pathCandidates object := by
  classical
  rw [pathCandidates, List.mem_flatMap]
  refine ⟨candidate.1, List.mem_range.mpr (Nat.lt_succ_iff.mpr bounded), ?_⟩
  rw [List.mem_map]
  refine ⟨candidate.2, ?_, rfl⟩
  simp [InducedPathMaximalPacking.windowSchedule]

/-- Exact object-derived inputs available to official graph semantics. -/
structure DerivedView (object : FiniteObject.{u}) where
  vertices : List object.Vertex
  darts : List object.graph.Dart
  edges : List object.graph.edgeSet
  adjacency : List ((object.Vertex × object.Vertex) × Bool)
  degrees : List (object.Vertex × Nat)
  support : List (object.Vertex × object.Vertex)
  paths : List (PathCandidate object)

/-- Graph owns every field of this construction. -/
noncomputable def derive (declaration : Declaration)
    (object : FiniteObject.{u}) : DerivedView object :=
  let presentation := declaration.presentation object
  {
    vertices := object.orderedVertices
    darts := object.orderedDarts
    edges := object.orderedEdges
    adjacency := presentation.adjacencyResponses
    degrees := presentation.degreeCapacities
    support := presentation.adjacencySupport
    paths := pathCandidates object
  }

/-- Why a selected official reference is not executable at this universal
boundary.  These constructors are closed framework facts, not authored
failure messages. -/
inductive Unavailable where
  | coreOwned
  | pdeOwned
  | semanticInputNotYetDerived
  deriving DecidableEq, Repr

/-- Closed availability result.  Only operations whose current Graph
semantic interpreter returns a genuine terminal are marked executable. -/
inductive Availability where
  | executableRootedReturn
  | unavailable (reason : Unavailable)
  deriving DecidableEq, Repr

/-- Total closed classification of the official registry.  In particular,
selecting an identifier in a `Program` cannot make an unsupported operation
executable. -/
def availability (ref : Ref) : Availability :=
  if ref.id = .rootedReturn then
    .executableRootedReturn
  else
    match (describe ref.id).owner with
    | .core => .unavailable .coreOwned
    | .pde => .unavailable .pdeOwned
    | .graph => .unavailable .semanticInputNotYetDerived

/-- Availability of every invocation in the reusable program. -/
def programAvailability (program : Program) : List (Ref × Availability) :=
  program.references.map fun ref => (ref, availability ref)

/-- Universal per-object preparation.  It evaluates no application callback:
the baseline proof is consumed only as theorem scope, while all operational
data comes from `derive` and closed program inspection. -/
structure Prepared (declaration : Declaration)
    (object : FiniteObject.{u}) where
  view : DerivedView object
  operations : List (Ref × Availability)

noncomputable def prepare (declaration : Declaration)
    (object : FiniteObject.{u}) : Prepared declaration object where
  view := derive declaration object
  operations := programAvailability declaration.program

/-- Execute the one graph operation currently supported by the closed
semantic terminal layer. -/
noncomputable def executeRootedReturn (declaration : Declaration)
    (object : FiniteObject.{u}) :
    Semantics.Result (declaration.presentation object)
      .rootedReturn :=
  Semantics.interpret (declaration.presentation object) .rootedReturn

end Hypostructure.Graph.Strategy.Official.Universal
