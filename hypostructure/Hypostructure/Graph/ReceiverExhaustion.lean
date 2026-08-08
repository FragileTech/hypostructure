import Hypostructure.Core.Strategy.ProblemInput
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.ReceiverLoad

/-!
# Receiver-exit semantics

This module contains only the proof-carrying rooted-return, two-path, closed,
handoff, and residual exits used by registered graph strategies.
-/

namespace Hypostructure.Graph.ReceiverExhaustion

open Hypostructure

universe uAmbient uBranch uData uVertex

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}

/-- Graph interpretation of a problem input and its target. -/
structure TargetInterface
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (CycleLengthOK : Nat → Prop) where
  object : Core.Strategy.ProblemInput P -> Graph.FiniteObject.{uVertex}
  target_iff_cycle : forall input,
    T.Predicate input.object ↔
      Graph.HasCycleWithLength CycleLengthOK (object input)
  rootedReturn : Graph.RootedReturnTargetAlgebra CycleLengthOK

/-- The semantic exits of a receiver search.  Names and numbering belong to
the manuscript; the reusable constructors are target certificates, a
target-defect peel, a typed handoff, and an exact residual. -/
inductive Exit
    (interface : TargetInterface P T CycleLengthOK)
    (Step Handoff Residual : Core.Strategy.ProblemInput P -> Type uData)
    (input : Core.Strategy.ProblemInput P) where
  | rootedReturn :
      interface.rootedReturn.RootedReturn (interface.object input) ->
      Exit interface Step Handoff Residual input
  | twoPath :
      (pair : Graph.CommonEndpointsCycle (interface.object input)) ->
      CycleLengthOK (pair.forward.length + pair.backward.length) ->
      Exit interface Step Handoff Residual input
  | closed :
      T.Predicate input.object ->
      Exit interface Step Handoff Residual input
  | peel : Step input -> Exit interface Step Handoff Residual input
  | handoff : Handoff input -> Exit interface Step Handoff Residual input
  | residual : Residual input -> Exit interface Step Handoff Residual input

end Hypostructure.Graph.ReceiverExhaustion
