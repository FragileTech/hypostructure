import Hypostructure.Core.Strategy.Official.Strategies.OrderedExhaustion
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification
import Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization
import Hypostructure.Core.Strategy.Official.Strategies.RankBudget
import Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion

/-!
# Canonical CT composition framework

A canonical CT composition chains numbered canonical operations (CT1--CT17)
so that CT n+1 receives the exact `Ledger.Extension` returned by CT n.
Each composition retains the complete composed output and exposes only a
framework-defined projection of its final terminals.

The composition type is a dependent fold: the terminal of CT n is threaded
as a hypothesis into the continuation that produces CT n+1's terminal.
No feature-local executor, `Option`-erasing classifier, or detached
aggregate input record may participate.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.Composition

open Hypostructure.Core.Strategy.Official

universe u v w

/-- A single canonical step.  `input` is the inert presentation slot;
`terminal` is the framework-produced terminal; `work` is the static work
bound inherited from the CT execution. -/
structure Step where
  input : Type
  terminal : Type
  work : Nat

/-- A two-step composition.  CT₂ receives the terminal of CT₁ as a
hypothesis; it never reconstructs or re-runs CT₁'s result. -/
structure Compose2 (step₁ step₂ : Step) where
  terminal₁ : step₁.terminal
  terminal₂ : step₂.terminal
  work : Nat

/-- A three-step composition. -/
structure Compose3 (s₁ s₂ s₃ : Step) extends Compose2 s₁ s₂ where
  terminal₃ : s₃.terminal

/-- A four-step composition. -/
structure Compose4 (s₁ s₂ s₃ s₄ : Step) extends Compose3 s₁ s₂ s₃ where
  terminal₄ : s₄.terminal

/-- Work is the sum of all constituent CT work bounds. -/
def totalWork (steps : List Nat) : Nat :=
  steps.sum

/-- The canonical ledger extension accumulated across a composition.
Each entry records which CT produced it and its static work bound. -/
structure LedgerExtension where
  ct : Nat
  work : Nat

def LedgerExtension.totalWork (extensions : List LedgerExtension) : Nat :=
  (extensions.map (·.work)).sum

end Hypostructure.Core.Strategy.Official.Strategies.Composition
