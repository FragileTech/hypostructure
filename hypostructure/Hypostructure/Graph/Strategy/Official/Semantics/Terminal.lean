import Hypostructure.Graph.Strategy.Official.Kernel
import Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence
import Hypostructure.Graph.InducedPathMaximalPacking

/-!
# Closed semantic terminals for graph-owned official operations

This layer interprets only literal `Presentation` data.  Its equations are
closed in Graph: an application can select an operation, but cannot supply an
executor, classifier, route, or claimed result.

Two operations have all indispensable inputs in the current presentation:
rooted returns use the finite graph and generated accepted-return table, and
target-defective peeling uses the graph-derived defect schedule.  Every other
graph-owned operation used by the structural program is rejected with the
exact inert datum (or predecessor certificate) that must be added before a
semantic terminal can be constructed.
-/

namespace Hypostructure.Graph.Strategy.Official.Semantics

open Hypostructure.Graph
open Hypostructure.Core.Strategy.OfficialRegistry

universe u

/-- The closed graph-owned operation vocabulary used by the official
structural program. -/
inductive Operation where
  | rootedReturn
  | targetDefectivePeel
  | decoratedFan
  | deletionCriticality
  | highCenterFanIncidence
  | receiverExhaustion
  | inducedPathPacking
  deriving DecidableEq, Repr

def Operation.id : Operation → Id
  | .rootedReturn => .rootedReturn
  | .targetDefectivePeel => .targetDefectivePeel
  | .decoratedFan => .decoratedFan
  | .deletionCriticality => .deletionCriticality
  | .highCenterFanIncidence => .highCenterFanIncidence
  | .receiverExhaustion => .receiverExhaustion
  | .inducedPathPacking => .inducedPathPacking

/-- Exact missing inert inputs.  These are data requirements, not fallback
terminals.  In particular, predecessor-owned certificates cannot be replaced
by presentation rows.

* `decoratedFanPresentation`: a finite core, labels, declared arm paths, and
  the five literal pair-safety relations.
* `deletionCriticalityPresentation`: a baseline class, threshold profile,
  and minimal-counterexample context.
* `deletionCriticalityPredecessor`: the exact deletion-criticality
  certificate produced at the preceding ledger row.
* `receiverPresentation`: finite loads, receivers, load incidences, response
  labels, and their literal support.
* `inducedPathOrder`: the requested path order from the generated problem
  table.
-/
inductive MissingInput : Operation → Type where
  | decoratedFanPresentation :
      MissingInput .decoratedFan
  | targetDefectiveQuotientPresentation :
      MissingInput .targetDefectivePeel
  | deletionCriticalityPresentation :
      MissingInput .deletionCriticality
  | deletionCriticalityPredecessor :
      MissingInput .highCenterFanIncidence
  | receiverPresentation :
      MissingInput .receiverExhaustion
  | inducedPathOrder :
      MissingInput .inducedPathPacking

/-- Exact avoidance of every return length listed in the generated table. -/
structure ReturnAvoidance (data : Presentation.{u}) : Prop where
  disjoint : ∀ dart : data.object.graph.Dart,
    Disjoint (returnLengthSet data.object dart)
      {length | data.target.ReturnLengthOK length}

/-- Exhaustive rooted-return terminal.  The hit is a real deleted-edge path;
the other terminal is literal disjointness from the accepted table. -/
inductive ReturnTerminal (data : Presentation.{u}) where
  | found :
      EdgeRootedReturn data.object
        data.target.ReturnLengthOK →
      ReturnTerminal data
  | avoided : ReturnAvoidance data → ReturnTerminal data

/-- Operation-indexed semantic outputs.  Constructors exist only where the
current inert presentation is mathematically sufficient. -/
inductive Terminal (data : Presentation.{u}) : Operation → Type (u + 1)
  | rootedReturn : ReturnTerminal data → Terminal data .rootedReturn

/-- Closed result of Graph interpretation.  `missing` is explicit rejection,
not a successful terminal and not a route selected by the application. -/
inductive Result (data : Presentation.{u}) (operation : Operation) :
    Type (u + 1) where
  | terminal : Terminal data operation → Result data operation
  | missing : MissingInput operation → Result data operation

noncomputable def decideReturn (data : Presentation.{u}) :
    ReturnTerminal data := by
  classical
  by_cases existsReturn :
      HasEdgeRootedReturn data.object
        data.target.ReturnLengthOK
  · exact ReturnTerminal.found existsReturn.some
  · exact ReturnTerminal.avoided {
      disjoint := by
        intro dart
        rw [Set.disjoint_left]
        intro length inSet accepted
        exact existsReturn ⟨{
          dart := dart
          path := Classical.choose inSet
          isPath := (Classical.choose_spec inSet).1
          length_ok := by
            rw [(Classical.choose_spec inSet).2]
            exact accepted
        }⟩
    }

/-- The only dispatcher equation.  Unsupported operations are rejected for
their precise absent data; no generic fallback exists. -/
noncomputable def interpret (data : Presentation.{u})
    (operation : Operation) : Result data operation :=
  match operation with
  | .rootedReturn => .terminal (.rootedReturn (decideReturn data))
  | .targetDefectivePeel => .missing .targetDefectiveQuotientPresentation
  | .decoratedFan => .missing .decoratedFanPresentation
  | .deletionCriticality => .missing .deletionCriticalityPresentation
  | .highCenterFanIncidence => .missing .deletionCriticalityPredecessor
  | .receiverExhaustion => .missing .receiverPresentation
  | .inducedPathPacking => .missing .inducedPathOrder

end Hypostructure.Graph.Strategy.Official.Semantics
