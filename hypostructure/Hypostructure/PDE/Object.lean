import Mathlib
import Hypostructure.Core.Problem

/-!
# Local PDE objects

The exact mirror of `Hypostructure/Graph/Object.lean`.  The graph layer owns
`Graph.FiniteObject` and hands applications `Graph.problem` /
`Graph.problemWithPresentation`; an application never defines its own ambient
graph, and is never asked to prove that a graph has vertices.

This module does the same for PDEs.  `PDE.FieldObject` is the ambient object of
a local regularity problem --- a domain, a field on it, a potential, and a
source --- and `PDE.problem` / `PDE.problemWithPresentation` register it.  An
application supplies its baseline and branch state and nothing else; in
particular it defines no ambient type and states no equation of its own.

The only difference from the graph layer is what the objects are and what the
minimal counterexample means: for graphs it is a smallest graph avoiding the
cycle target, and for PDEs it is the **singularity profile** of a field that
fails to be regular (`PDE/Singularity.lean`).
-/

namespace Hypostructure.PDE

open TopologicalSpace

universe u v w

/-- The space-time a `dimension`-dimensional local PDE problem lives on: one
time coordinate and `dimension` spatial ones, Euclidean so the regularity
theory has its inner product. -/
abbrev Place (dimension : ℕ) : Type := EuclideanSpace ℝ (Fin (dimension + 1))

/--
**The ambient object of a local PDE problem.**

A domain, the field whose regularity is at issue, the potential the balance
leaves a gradient of, and the source.  This is the analogue of
`Graph.FiniteObject`: framework-owned, so an application never declares it.

The potential is distribution-valued from the outset --- no representative and
no gauge is selected as part of the object --- which is what keeps a
normalization a *strategy* rather than a hypothesis.
-/
structure FieldObject (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] where
  /-- Where the object lives. -/
  domain : Opens (Place dimension)
  /-- The field whose interior regularity the target asserts, as a function. -/
  field : Place dimension → Value
  /-- The source, as a function. -/
  source : Place dimension → Value
  /-- The field, as a distribution on the domain. -/
  fieldState : Distribution domain Value ⊤
  /-- The source, as a distribution. -/
  sourceState : Distribution domain Value ⊤
  /-- The potential whose gradient the balance leaves over. -/
  potential : Distribution domain ℝ ⊤

namespace FieldObject

variable {dimension : ℕ} {Value : Type w}
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]


/-- Where the object lives, as the localization datum every derived window,
admissibility and cover is built from.  This is the *entire* localization
input, exactly as `FiniteObject.vertices` is for graphs. -/
abbrev domainOf (object : FieldObject dimension Value) :
    Opens (Place dimension) := object.domain

end FieldObject

/-- Register a local PDE problem without coupling its target to the ambient
data.  Mirrors `Graph.problem`. -/
def problem (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Baseline : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v) :
    Core.Problem.{w, v} where
  Ambient := FieldObject dimension Value
  Baseline := Baseline
  BranchState := BranchState

/-- Register a local PDE problem together with typed, problem-owned
presentation data.  The presentation is not interpreted by the PDE kernel; it
is exposed to reusable strategies as application input.  Mirrors
`Graph.problemWithPresentation`. -/
def problemWithPresentation (dimension : ℕ) (Value : Type w)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (Baseline : FieldObject dimension Value → Prop)
    (BranchState : FieldObject dimension Value → Type v)
    (Presentation : Type) (presentation : Presentation) :
    Core.Problem.{w, v} where
  Ambient := FieldObject dimension Value
  Baseline := Baseline
  BranchState := BranchState
  Presentation := Presentation
  presentation := some presentation

end Hypostructure.PDE
