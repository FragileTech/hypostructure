import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.Focus

/-!
# Boundaried atoms: the legacy focused execution

**Legacy.**  `Graph/BoundariedAtom.lean` holds the boundaried-gluing and atom
mathematics that `lem:replacement` is stated against.  This file holds the
focused accumulated execution that used to drive it, which reaches
`Core.Residual.Focus` and `Core.Metadata` and through them the legacy
`Core.Residual.Ledger`.

Separated so that row `[11]`--`[14]` can consume the atom mathematics without
importing the legacy stage stack.  Nothing in the ported spine reaches this
file.
-/

namespace Hypostructure.Graph

universe u v uPrevious

/-! ## Focused accumulated execution -/

/-- Private Graph-owned execution certificate. The registration and exact
focus-selection count are produced together by one counted Core execution. -/
structure FocusedBoundariedAtomCertificate
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) (active : focus.Active previous) where
  private mk ::
  registration : BoundariedAtomRegistration (context previous active)
  checks : Nat
  checks_eq_budget : checks = focus.selectionBudget.checks previous

namespace FocusedBoundariedAtomCertificate

theorem work_bounded
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))}
    {previous : Previous} {active : focus.Active previous}
    (certificate : FocusedBoundariedAtomCertificate
      focus context previous active) :
    certificate.checks <=
      focus.selectionBudget.coefficient *
        (focus.selectionBudget.size previous + 1) ^
          focus.selectionBudget.degree := by
  rw [certificate.checks_eq_budget]
  exact focus.selectionBudget.bounded previous

/-- Predicate-form work theorem for an active boundaried-atom certificate. -/
theorem work_within
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))}
    {previous : Previous} {active : focus.Active previous}
    (certificate : FocusedBoundariedAtomCertificate
      focus context previous active) :
    focus.selectionBudget.Within previous certificate.checks :=
  certificate.work_bounded

end FocusedBoundariedAtomCertificate

/-- Complete Graph-owned certificate generated on one active
minimal-context branch. -/
abbrev FocusedBoundariedAtomOutput
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) (active : focus.Active previous) :=
  FocusedBoundariedAtomCertificate focus context previous active

/-- Exact accumulated successor carrying the generated atom family. -/
abbrev FocusedBoundariedAtomStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.Stage focus
    (FocusedBoundariedAtomOutput focus context)

/-- Execute the complete boundaried-atom registration and branch selection as
one counted computation. -/
def executeFocusedBoundariedAtomRegistrationCounted
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) :
    Core.Counted (FocusedBoundariedAtomStage focus context) :=
  Core.Residual.Focus.runCounted focus previous fun active checks exact =>
    .mk (deriveBoundariedAtomRegistration (context previous active))
      checks exact

/-- Public focused successor; exact work remains stored in its private latest
certificate and coupled to the counted execution that produced the stage. -/
def executeFocusedBoundariedAtomRegistration
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) :
    FocusedBoundariedAtomStage focus context :=
  (executeFocusedBoundariedAtomRegistrationCounted
    focus context previous).value

@[simp] theorem executeFocusedBoundariedAtomRegistrationCounted_checks
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) :
    (executeFocusedBoundariedAtomRegistrationCounted
      focus context previous).checks =
        focus.selectionBudget.checks previous :=
  Core.Residual.Focus.runCounted_checks focus previous _

/-- The complete counted registration, including inactive outcomes, satisfies
the inherited focus-selection envelope. -/
theorem executeFocusedBoundariedAtomRegistrationCounted_checks_bounded
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) :
    (executeFocusedBoundariedAtomRegistrationCounted
      focus context previous).checks <=
        focus.selectionBudget.coefficient *
          (focus.selectionBudget.size previous + 1) ^
            focus.selectionBudget.degree := by
  rw [executeFocusedBoundariedAtomRegistrationCounted_checks]
  exact focus.selectionBudget.bounded previous

/-- Predicate-form work theorem for focused boundaried-atom registration. -/
theorem executeFocusedBoundariedAtomRegistrationCounted_work_within
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeFocusedBoundariedAtomRegistrationCounted focus context
        previous).checks :=
  executeFocusedBoundariedAtomRegistrationCounted_checks_bounded focus context
    previous

/-- Active branch inherited after the atom-family registration. -/
abbrev FocusedBoundariedAtomProfile
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.successor focus
    (FocusedBoundariedAtomOutput focus context)

/-- Query the private Graph execution certificate from the newest extension. -/
def focusedBoundariedAtomCertificateQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedBoundariedAtomProfile focus context)
      (fun stage active =>
        FocusedBoundariedAtomOutput focus context stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

/-- Project only the Graph-generated atom registration from the exact latest
execution certificate. -/
def focusedBoundariedAtomRegistrationQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedBoundariedAtomProfile focus context)
      (fun stage active =>
        BoundariedAtomRegistration (context stage.previous active)) :=
  (focusedBoundariedAtomCertificateQuery focus context).map
    fun _stage _active certificate => certificate.registration

/-! ## Proof-relevant declaration metadata -/

/-- Canonical audit record for the focused boundaried-atom executor.  It
stores the actual active context query and the exact work budget rather than
describing either one only in prose. -/
def focusedBoundariedAtomMetadata
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Metadata.DeclarationMetadata Previous Previous where
  declaration :=
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "executeFocusedBoundariedAtomRegistration"⟩
  primitiveInputs := [
    ⟨⟨"Hypostructure.Graph.BoundariedAtom", "ProperBoundariedAtom"⟩,
      .localCertificate⟩
  ]
  inferredDependencies := [
    ⟨⟨"Hypostructure.Core.Residual.Focus", "ActiveQuery"⟩,
      .predecessorProjection⟩,
    ⟨⟨"Hypostructure.Graph.BoundariedAtom",
      "deriveBoundariedAtomRegistration"⟩, .registeredProfile⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"Hypostructure.Core.Residual.Focus", "ActiveQuery"⟩
    profile := focus
    Result := fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)
    query := context
  }]
  frameworkSearch := []
  generatedOutputs := [
    ⟨⟨"Hypostructure.Graph.BoundariedAtom",
      "deriveBoundariedAtomRegistration"⟩, .auditRecord⟩,
    ⟨⟨"Hypostructure.Core.Residual.Focus", "runCounted"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "OwnedDecomposition.piece_lexicographicallySmaller"⟩,
    ⟨"Hypostructure.Graph.Response",
      "profile_ne_not_targetComplete"⟩,
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "FocusedBoundariedAtomCertificate.work_bounded"⟩
  ]
  workBound := focus.selectionBudget
  manualObligations := []

/-- The canonical executor metadata has no unresolved manual obligation. -/
def focusedBoundariedAtomMetadataComplete
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Metadata.Complete
      (focusedBoundariedAtomMetadata focus context) :=
  ⟨rfl⟩

end Hypostructure.Graph
