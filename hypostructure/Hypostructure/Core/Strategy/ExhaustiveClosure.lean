import Hypostructure.CTAdapters

/-!
# Exhaustive closure

This is the domain-neutral strategy shape for a finite exhaustion argument.  A
preceding CT pipeline produces a literal ledger; an application then
interprets that output into four exhaustive alternatives:

* a target certificate;
* a compression certificate, with a supplied target bridge;
* a typed handoff to another strategy; or
* a typed residual for the next well-founded argument.

Core owns the dependent execution and the exhaustive routing.  Graph and PDE
applications supply only the interpretation and the semantic bridge for a
compression certificate.  In particular, this type does not name receiver,
vertex, edge, pressure, or any other domain-specific object.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core

universe uAmbient uBranch uPipeline uTarget uCompression uHandoff uResidual

structure ExhaustiveClosure
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (pipeline : CTExecution (ProblemInput P)) where
  Compression : ProblemInput P -> Type uCompression
  Handoff : ProblemInput P -> Type uHandoff
  Residual : ProblemInput P -> Type uResidual
  /-- Exhaustive interpretation of the completed ledger. -/
  interpret : (input : ProblemInput P) -> pipeline.Output input ->
    Sum (PLift (T.Predicate input.object))
      (Sum (Compression input)
        (Sum (Handoff input) (Residual input)))
  /-- Semantic target bridge for the compression alternative. -/
  compressionTarget : (input : ProblemInput P) ->
    Compression input -> T.Predicate input.object
  metadata : Documentation := {}
  components : List Documentation := []
  targetMetadata : Documentation := {}
  compressionMetadata : Documentation := {}
  handoffMetadata : Documentation := {}
  residualMetadata : Documentation := {}

abbrev ExhaustiveClosure.LeftPayload
    (strategy : ExhaustiveClosure P T pipeline)
    (input : ProblemInput P) :=
  Sum (PLift (T.Predicate input.object)) (strategy.Compression input)

abbrev ExhaustiveClosure.RightPayload
    (strategy : ExhaustiveClosure P T pipeline)
    (input : ProblemInput P) :=
  Sum (strategy.Handoff input) (strategy.Residual input)

/-- Register the alternatives as one exhaustive Core dichotomy.
The target and compression alternatives close through their supplied
certificates; handoff and residual alternatives remain literal continuation
payloads for the next blueprint vertices.
-/
noncomputable def ExhaustiveClosure.toDichotomy
    (strategy : ExhaustiveClosure P T pipeline) :
    Core.DichotomyData P T where
  LeftPayload := strategy.LeftPayload
  RightPayload := strategy.RightPayload
  classify := fun input =>
    match strategy.interpret input (pipeline.run input) with
    | .inl target => .inl (.inl target)
    | .inr (.inl compression) => .inl (.inr compression)
    | .inr (.inr (.inl handoff)) => .inr (.inl handoff)
    | .inr (.inr (.inr residual)) => .inr (.inr residual)
  closeLeft := some ⟨fun input witness =>
    match witness with
    | .inl target => target.down
    | .inr compression => strategy.compressionTarget input compression⟩
  metadata := strategy.metadata
  components := strategy.components
  leftMetadata := strategy.compressionMetadata
  rightMetadata := strategy.handoffMetadata

end Hypostructure.Core.Strategy
