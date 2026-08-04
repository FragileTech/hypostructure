import Hypostructure.Core.Strategy.Data

/-!
# Domain-neutral well-founded compression strategy

This module abstracts a recurring multi-CT proof pattern: one or more domain
CTs search a finite/localized residual and return a certified replacement;
minimality transports the target from that replacement back to the current
residual.  Core owns the option split, recursion, termination measure, and
branch closures.  Graph and PDE adapters only construct `CompressionStep`
certificates from their own CT pipelines.

The certificate deliberately has no graph or PDE fields.  A graph deletion,
a PDE localization, or a composite result produced by several CTs are all
equally valid replacements when they provide the six fields below.
-/

namespace Hypostructure.Core.Strategy

universe uAmbient uBranch

open Hypostructure.Core

structure CompressionStep
    (P : Core.Problem.{uAmbient, uBranch}) where
  Certificate : ProblemInput P -> Type
  /-- The preceding CT pipeline's exhaustive result, if it found a
  compressing certificate. -/
  search : (input : ProblemInput P) -> Option (Certificate input)
  /-- The smaller/simpler residual represented by the certificate. -/
  replacement : (input : ProblemInput P) -> Certificate input -> ProblemInput P
  measure : ProblemInput P -> Nat
  measureDecreases : (input : ProblemInput P) -> (certificate : Certificate input) ->
    measure (replacement input certificate) < measure input

structure CompressionClosure
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) where
  step : CompressionStep P
  /-- The paper/application's genuine no-compression base case. -/
  baseCase : (input : ProblemInput P) ->
    step.search input = none -> T.Predicate input.object
  /-- Transport a target certificate across one certified replacement. -/
  transport : (input : ProblemInput P) ->
    (certificate : step.Certificate input) ->
    T.Predicate (step.replacement input certificate).object ->
    T.Predicate input.object

/-- The total target consumer for a well-founded compression closure. -/
noncomputable def CompressionClosure.close
    (closure : CompressionClosure P T) :
    (input : ProblemInput P) -> T.Predicate input.object
  | input =>
    match h : closure.step.search input with
    | none => closure.baseCase input h
    | some certificate =>
        closure.transport input certificate
          (closure.close (closure.step.replacement input certificate))
termination_by input => closure.step.measure input
decreasing_by
  exact closure.step.measureDecreases input certificate

/-- Expose the compression closure as an exhaustive registered dichotomy.
The left payload records the exact CT-produced certificate and the right
payload records the exact no-certificate result; neither side is a generic
placeholder.  If `baseCase` and `transport` are supplied, Core closes both
branches and the result can be consumed directly by the DAG runner. -/
noncomputable def CompressionClosure.toDichotomy
    (closure : CompressionClosure P T) : Core.DichotomyData P T where
  LeftPayload := fun input => PLift (∃ certificate,
    closure.step.search input = some certificate)
  RightPayload := fun input => PLift (closure.step.search input = none)
  classify := fun input =>
    match h : closure.step.search input with
    | some certificate => Sum.inl ⟨certificate, rfl⟩
    | none => Sum.inr ⟨rfl⟩
  closeLeft := some ⟨fun input witness => by
    exact closure.close input⟩
  closeRight := some ⟨fun input witness => closure.baseCase input witness.down⟩

end Hypostructure.Core.Strategy
