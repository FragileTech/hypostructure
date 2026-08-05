import Hypostructure.Graph.Minimality
import Hypostructure.Core.MinimalityFocus

/-!
# Graph minimality: the legacy focused execution

**Legacy.**  `Graph/Minimality.lean` holds `lem:no-proper-core` in graph
coordinates -- the no-proper-baseline certificate the spine's node `[8]`
proves.  This file holds the focused-stage execution that used to drive it,
which reaches `Core.Residual.Focus` and through it the legacy
`Core.Residual.Ledger`.
-/

namespace Hypostructure.Graph

universe u v w

/-! ## Focused accumulated execution -/

/-- The graph-owned payload produced on one active minimal-context branch. -/
abbrev FocusedNoProperBaselineOutput
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) (active : focus.Active previous) :=
  NoProperBaselineCertificate (context previous active)

/-- Exact accumulated stage after focused proper-subgraph closure. -/
abbrev FocusedNoProperBaselineStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  Core.Residual.Focus.Stage focus
    (FocusedNoProperBaselineOutput focus context)

/-- Counted execution of generic proper-subgraph minimality on the active
branch. The derived certificate is proof-only, so the exact work is the
framework-owned focus selection. -/
def executeFocusedNoProperBaselineCounted
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
  Core.Counted (FocusedNoProperBaselineStage focus context) :=
  Core.Residual.Focus.runCounted focus
    (Output := FocusedNoProperBaselineOutput focus context)
    previous
    (fun active _checks _exact =>
      deriveNoProperBaseline profile (context previous active))

/-- Public stage projection of counted proper-subgraph minimality. -/
def executeFocusedNoProperBaseline
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    FocusedNoProperBaselineStage focus context :=
  (executeFocusedNoProperBaselineCounted focus profile context previous).value

@[simp] theorem executeFocusedNoProperBaselineCounted_checks
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    (executeFocusedNoProperBaselineCounted focus profile context previous).checks =
      focus.selectionBudget.checks previous := by
  simp [executeFocusedNoProperBaselineCounted]

theorem executeFocusedNoProperBaselineCounted_checks_bounded
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    (executeFocusedNoProperBaselineCounted focus profile context previous).checks <=
      focus.selectionBudget.coefficient *
        (focus.selectionBudget.size previous + 1) ^
          focus.selectionBudget.degree := by
  rw [executeFocusedNoProperBaselineCounted_checks]
  exact focus.selectionBudget.bounded previous

/-- Predicate-form work theorem for focused proper-subgraph minimality. -/
theorem executeFocusedNoProperBaselineCounted_work_within
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (profile : ProperSubgraphMinimalityProfile Baseline BranchState Target)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState))
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeFocusedNoProperBaselineCounted focus profile context previous).checks :=
  by
    rw [executeFocusedNoProperBaselineCounted_checks focus profile context previous]
    exact focus.selectionBudget.bounded previous

/-- Focus inherited after the Graph minimality executor. -/
abbrev FocusedNoProperBaselineProfile
    {Previous : Type uPrevious}
  (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
  (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  Core.Residual.Focus.successor focus
    (FocusedNoProperBaselineOutput focus context)

/-- Query the exact graph-owned no-proper-baseline certificate. -/
def focusedNoProperBaselineQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject -> Prop}
    {BranchState : FiniteObject -> Type v}
    {Target : FiniteObject -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :
  Core.Residual.Focus.ActiveQuery
      (FocusedNoProperBaselineProfile focus context)
      (fun stage active =>
        FocusedNoProperBaselineOutput focus context
          stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

end Hypostructure.Graph
