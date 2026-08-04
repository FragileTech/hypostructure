import Hypostructure.Core.Finite.Enumeration

/-!
# Canonical pair-response accounting semantics

This registration contains only residual-indexed finite mathematics.  Pair
dependence and canonical roles are primitive observations; CT15 and CT9 own
all finite scans, outcomes, routing, and ledger extensions.
-/

namespace Hypostructure.Core.Strategy.CanonicalPairResponseAccounting

universe uResidual uPair uBlocker

/-- The pre-retokenization role alphabet is exactly the blocker-kind alphabet
plus one distinct free-anchor role. -/
abbrev Role (BlockerKind : Type uBlocker) :=
  Sum BlockerKind Unit

namespace Role

/-- The role of a blocker-free pair. -/
def freeAnchor {BlockerKind : Type uBlocker} : Role BlockerKind :=
  Sum.inr ()

/-- The role carrying one exact canonical blocker kind. -/
def blocked {BlockerKind : Type uBlocker}
    (kind : BlockerKind) : Role BlockerKind :=
  Sum.inl kind

end Role

/-- Inert residual-owned semantics for the CT15 -> CT9 composition. -/
structure Registration (Residual : Type uResidual) where
  Pair : Residual → Type uPair
  pairSchedule :
    (residual : Residual) → Core.Finite.Enumeration (Pair residual)
  IntendedPair : (residual : Residual) → Pair residual → Prop
  pairSchedule_exact : ∀ residual pair,
    pair ∈ (pairSchedule residual).values ↔ IntendedPair residual pair
  Dependent : (residual : Residual) → Pair residual → Prop
  AdmittedDependent : (residual : Residual) → Pair residual → Prop
  dependent_exact : ∀ residual pair,
    Dependent residual pair ↔ AdmittedDependent residual pair
  dependentDecidable :
    (residual : Residual) → (pair : Pair residual) →
      Decidable (Dependent residual pair)
  pairCharge : (residual : Residual) → Pair residual → Nat
  pairCapacity : Residual → Nat
  BlockerKind : Residual → Type uBlocker
  completeBlockerKinds :
    (residual : Residual) →
      Core.Finite.CompleteEnumeration (BlockerKind residual)
  CanonicalBlocker :
    (residual : Residual) → Pair residual → BlockerKind residual → Prop
  blocker_exact : ∀ residual pair,
    AdmittedDependent residual pair ↔
      ∃ kind, CanonicalBlocker residual pair kind
  roleOf :
    (residual : Residual) → Pair residual → Role (BlockerKind residual)
  role_freeAnchor_exact : ∀ residual pair,
    roleOf residual pair = Role.freeAnchor ↔
      ¬ AdmittedDependent residual pair
  role_blocked_exact : ∀ residual pair kind,
    roleOf residual pair = Role.blocked kind ↔
      CanonicalBlocker residual pair kind
  roleCapacity :
    (residual : Residual) → Role (BlockerKind residual) → Nat

namespace Registration

/-- The exact CT9 role schedule, derived solely from the complete blocker-kind
schedule and the two sum constructors. -/
def completeRoles
    (registration :
      Registration.{uResidual, uPair, uBlocker} Residual)
    (residual : Residual) :
    Core.Finite.CompleteEnumeration
      (Role (registration.BlockerKind residual)) := by
  let blockers := registration.completeBlockerKinds residual
  let values :=
    blockers.values.map (fun kind => Role.blocked kind) ++
      [Role.freeAnchor]
  letI : DecidableEq (registration.BlockerKind residual) :=
    blockers.decEq
  exact
    { toEnumeration :=
        { values := values
          nodup := by
            have blockedNodup :
                (blockers.values.map
                  (fun kind => Role.blocked kind)).Nodup :=
              blockers.nodup.map Sum.inl_injective
            apply blockedNodup.append (by simp)
            rw [List.disjoint_left]
            intro role blockedMember anchorMember
            rcases List.mem_map.mp blockedMember with
              ⟨kind, _, rfl⟩
            simp [Role.blocked, Role.freeAnchor] at anchorMember
          decEq := inferInstance }
      complete := by
        intro role
        cases role with
        | inl kind =>
            exact List.mem_append_left _
              (List.mem_map.mpr
                ⟨kind, blockers.complete kind, rfl⟩)
        | inr anchor =>
            cases anchor
            exact List.mem_append_right _ (by
              simp [Role.freeAnchor]) }

end Registration

end Hypostructure.Core.Strategy.CanonicalPairResponseAccounting
