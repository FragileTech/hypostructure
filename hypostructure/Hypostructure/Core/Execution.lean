import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Provision

/-!
# Generic executable substrate

A CT-specific module supplies a deterministic reference machine and proofs
about that machine.  Core alone packages its value as a public typed result
and installs it in the accumulated predecessor ledger.
-/

namespace Hypostructure.Core.Execution

universe uPrevious uInput uOutcome uTrace uResidual

/-- Domain-neutral shape of one executable CT entry. -/
structure Spec (Previous : Type uPrevious) where
  Input : Previous -> Type uInput
  Outcome : (previous : Previous) -> Input previous -> Type uOutcome
  Trace : (previous : Previous) -> (input : Input previous) ->
    Outcome previous input -> Type uTrace
  Sound : (previous : Previous) -> (input : Input previous) ->
    (outcome : Outcome previous input) -> Trace previous input outcome -> Prop
  Exhaustive : (previous : Previous) -> (input : Input previous) ->
    Outcome previous input -> Prop

/-- The exact dependent input used by work-budget accounting. -/
abbrev PackedInput {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous) :=
  Sigma spec.Input

/-- Raw value returned by a registered deterministic reference machine. -/
structure ReferenceResult {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous)
    (previous : Previous) (input : spec.Input previous) where
  outcome : spec.Outcome previous input
  trace : spec.Trace previous input outcome

/-- Complete reusable implementation contract for one `Spec`.

CT modules construct this from their primitive capabilities.  The application
does not provide a completed `ReferenceResult`; it provides the primitive
mathematics from which the CT module defines `reference`. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous) where
  reference : (previous : Previous) -> (input : spec.Input previous) ->
    Counted (ReferenceResult spec previous input)
  sound : (previous : Previous) -> (input : spec.Input previous) ->
    spec.Sound previous input
      (reference previous input).value.outcome
      (reference previous input).value.trace
  exhaustive : (previous : Previous) -> (input : spec.Input previous) ->
    spec.Exhaustive previous input (reference previous input).value.outcome
  work : PolynomialCheckBudget (PackedInput spec)
  checks_eq : (previous : Previous) -> (input : spec.Input previous) ->
    (reference previous input).checks = work.checks ⟨previous, input⟩

/-- Public framework-generated result.  Its private constructor prevents a
caller from manufacturing a selected outcome, trace, or verification proof. -/
structure Result {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous)
    (previous : Previous) (input : spec.Input previous) where
  private mk ::
  outcome : spec.Outcome previous input
  trace : spec.Trace previous input outcome
  sound : spec.Sound previous input outcome trace
  exhaustive : spec.Exhaustive previous input outcome
  checks : Nat

/-- The sole value added by an execution.  It retains the exact input and the
typed generated result indexed by that input. -/
structure Output {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uInput, uOutcome, uTrace} Previous)
    (previous : Previous) where
  private mk ::
  input : spec.Input previous
  result : Result spec previous input

end Hypostructure.Core.Execution
