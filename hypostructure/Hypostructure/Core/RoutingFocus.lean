import Hypostructure.Core.Routing
import Hypostructure.Core.Residual.Focus

/-!
# Routing profiles built from a focused branch

**Legacy.**  `Core/Routing.lean` holds the routing profile and its discovery
semantics.  This file holds the constructor that builds one from a
`Core.Residual.Focus` branch, which reaches the legacy `Core.Residual.Ledger`.

Separated so that `Core.Closure` -- and through it `Core.Minimality`, the graph
minimality layer, and the entry spine's nodes `[1]`--`[10]` -- can route without
importing the legacy stage stack.
-/

namespace Hypostructure.Core.Routing

namespace Profile

open Hypostructure.Core.Residual

/-- Disabled discovery payload for focus-derived routes. -/
structure FocusBlocked {Source : Type uSource}
    (focus : Focus.Profile Source) (source : Source) : Type where
  inactive : Not (focus.Active source)

/-- Build a route profile from a focused branch.  Core owns the handoff:
semantic discovery is enabled exactly when the source lies in the supplied
focus, and disabled otherwise.  The caller supplies only the active-branch
seed constructor and target-input map; it never supplies a routed result. -/
def ofFocus {Source : Type uSource}
    (focus : Focus.Profile Source)
    (target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source)
    (executor : Execution.Capability target)
    (Seed : Source -> Type uSeed)
    (seed : (source : Source) -> (active : focus.Active source) ->
      Seed source)
    (targetInput :
      (source : Source) -> Seed source -> target.Input source) :
    Profile.{uSource, uInput, uOutcome, uTrace, uSeed, 0} Source where
  Target := target
  executor := executor
  Seed := Seed
  Blocked := FocusBlocked focus
  discover := fun source =>
    match (focus.select source).value with
    | .isTrue active => .enabled (seed source active)
    | .isFalse inactive => .disabled ⟨inactive⟩
  targetInput := fun source packed =>
    targetInput source packed

@[simp] theorem ofFocus_discover_active {Source : Type uSource}
    (focus : Focus.Profile Source)
    (target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source)
    (executor : Execution.Capability target)
    (Seed : Source -> Type uSeed)
    (seed : (source : Source) -> (active : focus.Active source) ->
      Seed source)
    (targetInput :
      (source : Source) -> Seed source -> target.Input source)
    (source : Source) (active : focus.Active source) :
    ((ofFocus focus target executor Seed seed targetInput).discover source) =
      .enabled (seed source active) := by
  cases selected : (focus.select source).value with
  | isTrue selectedActive =>
      have equal : selectedActive = active := Subsingleton.elim _ _
      cases equal
      simp [ofFocus, selected]
  | isFalse inactive => exact (inactive active).elim

@[simp] theorem ofFocus_discover_inactive {Source : Type uSource}
    (focus : Focus.Profile Source)
    (target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source)
    (executor : Execution.Capability target)
    (Seed : Source -> Type uSeed)
    (seed : (source : Source) -> (active : focus.Active source) ->
      Seed source)
    (targetInput :
      (source : Source) -> Seed source -> target.Input source)
    (source : Source) (inactive : Not (focus.Active source)) :
    ((ofFocus focus target executor Seed seed targetInput).discover source) =
      .disabled ⟨inactive⟩ := by
  cases selected : (focus.select source).value with
  | isTrue active => exact (inactive active).elim
  | isFalse selectedInactive =>
      have equal : selectedInactive = inactive := Subsingleton.elim _ _
      cases equal
      simp [ofFocus, selected]

end Profile

end Hypostructure.Core.Routing
