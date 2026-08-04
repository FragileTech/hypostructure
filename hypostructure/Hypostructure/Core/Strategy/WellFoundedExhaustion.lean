import Hypostructure.Core.Strategy.Dag

/-!
# Well-founded finite exhaustion

This is the domain-neutral Core shape for a finite proof search with a
well-founded feedback outcome.  A search either produces one strictly smaller
predecessor, or reaches one of three terminal classes: a target certificate,
a handoff, or a residual.  Core executes the feedback internally and exposes
only the terminal result to the DAG.

The construction is useful for graph receiver peeling, PDE defect peeling,
and any other proof in which a local certificate is removed and the same
finite exhaustion is rerun.  Domain adapters supply the search, the strict
measure law, and the transport laws; Core owns recursion, terminal
exhaustiveness, and the public dichotomy.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core

universe uAmbient uBranch uStep uHandoff uResidual

structure WellFoundedExhaustion
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) where
  Step : ProblemInput P -> Type uStep
  Handoff : ProblemInput P -> Type uHandoff
  Residual : ProblemInput P -> Type uResidual
  measure : ProblemInput P -> Nat
  /-- A local feedback step or an exhaustive terminal outcome. -/
  search : (input : ProblemInput P) ->
    Sum (Step input)
      (Sum (PLift (T.Predicate input.object))
        (Sum (Handoff input) (Residual input)))
  replace : (input : ProblemInput P) -> Step input -> ProblemInput P
  measureDecreases : ∀ (input : ProblemInput P) (step : Step input),
    measure (replace input step) < measure input
  /-- Transport a target certificate through one feedback replacement. -/
  transportTarget : ∀ (input : ProblemInput P) (step : Step input),
    T.Predicate (replace input step).object -> T.Predicate input.object
  /-- Handoffs and residuals remain owned by the original predecessor after
  the feedback loop has finished. -/
  transportHandoff : ∀ (input : ProblemInput P) (step : Step input),
    Handoff (replace input step) -> Handoff input
  transportResidual : ∀ (input : ProblemInput P) (step : Step input),
    Residual (replace input step) -> Residual input
  metadata : Documentation := {}
  components : List Documentation := []
  targetMetadata : Documentation := {}
  handoffMetadata : Documentation := {}
  residualMetadata : Documentation := {}

inductive ExhaustionTerminal
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (strategy : WellFoundedExhaustion P T)
    (input : ProblemInput P) where
  | target : T.Predicate input.object -> ExhaustionTerminal strategy input
  | handoff : strategy.Handoff input -> ExhaustionTerminal strategy input
  | residual : strategy.Residual input -> ExhaustionTerminal strategy input

structure ExhaustionRun
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (strategy : WellFoundedExhaustion P T)
    (input : ProblemInput P) where
  terminal : ExhaustionTerminal strategy input
  feedbackSteps : Nat

noncomputable def WellFoundedExhaustion.run
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (strategy : WellFoundedExhaustion P T)
    (input : ProblemInput P) : ExhaustionRun strategy input :=
  match strategy.search input with
  | .inl step =>
      let next := WellFoundedExhaustion.run strategy (strategy.replace input step)
      { terminal := match next.terminal with
        | .target proof => .target (strategy.transportTarget input step proof)
        | .handoff handoff =>
            .handoff (strategy.transportHandoff input step handoff)
        | .residual residual =>
            .residual (strategy.transportResidual input step residual)
        feedbackSteps := next.feedbackSteps + 1 }
  | .inr (.inl target) =>
      { terminal := .target target.down, feedbackSteps := 0 }
  | .inr (.inr (.inl handoff)) =>
      { terminal := .handoff handoff, feedbackSteps := 0 }
  | .inr (.inr (.inr residual)) =>
      { terminal := .residual residual, feedbackSteps := 0 }
termination_by strategy.measure input
decreasing_by
  exact strategy.measureDecreases input step

abbrev WellFoundedExhaustion.LeftPayload
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (_strategy : WellFoundedExhaustion P T) (input : ProblemInput P) :=
  PLift (T.Predicate input.object)

abbrev WellFoundedExhaustion.RightPayload
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (strategy : WellFoundedExhaustion P T) (input : ProblemInput P) :=
  Sum (strategy.Handoff input) (strategy.Residual input)

/-- Expose the fully exhausted terminal as one Core dichotomy.  The feedback
loop is not a DAG edge: its strict measure and complete trace are consumed by
this executable Core vertex before either branch is returned.
-/
noncomputable def WellFoundedExhaustion.toDichotomy
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (strategy : WellFoundedExhaustion P T) : Core.DichotomyData P T where
  LeftPayload := strategy.LeftPayload
  RightPayload := strategy.RightPayload
  classify := fun input =>
    match (strategy.run input).terminal with
    | .target target => .inl ⟨target⟩
    | .handoff handoff => .inr (.inl handoff)
    | .residual residual => .inr (.inr residual)
  closeLeft := some ⟨fun _input witness => witness.down⟩
  metadata := strategy.metadata
  components := strategy.components
  leftMetadata := strategy.targetMetadata
  rightMetadata := strategy.handoffMetadata

end Hypostructure.Core.Strategy
