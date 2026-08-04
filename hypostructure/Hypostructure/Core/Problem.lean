import Hypostructure.Core.Prelude

/-!
# Problem kernel

The universal problem data contains only an ambient type, its baseline
predicate, and the branch state indexed by the current ambient object. Targets
and optional capabilities are supplied separately.
-/

namespace Hypostructure.Core

universe uAmbient uBranch

/-- Irreducible data shared by every tactic in one proof program. -/
structure Problem where
  Ambient : Type uAmbient
  Baseline : Ambient -> Prop
  BranchState : Ambient -> Type uBranch
  /-- Type of optional, typed presentation data shared by its strategies. -/
  Presentation : Type := PUnit
  /-- Problem-owned metadata and parameters.  `none` keeps existing problem
  declarations source-compatible; declarations that need typed presentation
  data install it with `some`. -/
  presentation : Option Presentation := none

/-! ## Target boundary

Targets are kept separate from `Problem` so the same problem registration can
be reused by different theorem statements or terminal predicates.  The two
bridge fields are formulation laws, not a proof of the statement itself.
-/

structure Target (P : Problem) where
  Predicate : P.Ambient -> Prop
  Statement : Prop
  statement_to_target :
    Statement -> forall object, P.Baseline object -> Predicate object
  target_to_statement :
    (forall object, P.Baseline object -> Predicate object) -> Statement

/-- The target whose public statement is exactly its own closure: every
baseline object satisfies the registered predicate.  Both bridge fields are
the identity, so a problem whose theorem *is* the closure of a predicate
registers this and supplies no formulation law. -/
def Target.ofPredicate (P : Problem) (Predicate : P.Ambient -> Prop) :
    Target P where
  Predicate := Predicate
  Statement := forall object, P.Baseline object -> Predicate object
  statement_to_target := fun statement => statement
  target_to_statement := fun closure => closure

end Hypostructure.Core
