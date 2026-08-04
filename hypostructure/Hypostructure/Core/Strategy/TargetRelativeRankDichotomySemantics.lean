import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics

/-!
# Residual-indexed target-relative rank semantics

Inert presentation data for the CT10 → CT15 → CT16 composition implemented in
`TargetRelativeRankDichotomy.lean`.  The record supplies the response
presentation, the finite observation and class schedules, the coordinate
family with its target-relative charge and capacity. Core owns classification,
rank comparison, the exact-code projection from CT10's retained result, both
ledger extensions, and the branch transport.
-/

namespace Hypostructure.Core.Strategy.TargetRelativeRankDichotomy

universe uResidual uAmbient uResponse uDatum uClass uPromotion uCoordinate

open Hypostructure.Core.Strategy

/-- Residual-owned response, classification, and rank presentation. Rank-side
capacity is additionally indexed by the exact local-supply ledger published
by a completed `LocalSupplyLowerBound`; closed-code routing is derived by Core
from CT10's exact retained terminal and is not an application field. -/
structure BaseRegistration (Residual : Type uResidual)
    (AmbientItem : Residual → Type uAmbient)
    (Coordinate : Residual → Type uCoordinate) where
  Response : Residual → Type uResponse
  response : (residual : Residual) → Response residual
  Datum : Residual → Type uDatum
  Class : Residual → Type uClass
  Promotion : Residual → Type uPromotion
  observationData : (residual : Residual) →
    Core.Finite.Enumeration (Datum residual)
  completeClasses : (residual : Residual) →
    Core.Finite.CompleteEnumeration (Class residual)
  classOf : (residual : Residual) → Response residual →
    Datum residual → Class residual
  Direct : (residual : Residual) → Response residual →
    Class residual → Prop
  promote : (residual : Residual) → Response residual →
    Class residual → Promotion residual
  directDecidable : (residual : Residual) →
    (response : Response residual) → (cls : Class residual) →
      Decidable (Direct residual response cls)
  coordinates : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) →
      Core.Finite.Enumeration (Coordinate residual)
  charge : (residual : Residual) →
    Response residual → Coordinate residual → Nat
  /-- Every scheduled coordinate is charged at all.

  CT15 measures the target-relative rank as the *cardinality* of the
  coordinate schedule and, separately, tallies the registered charge of that
  same schedule against the supply budget.  Without this law the two
  quantities are unrelated and the published rank carries no budget
  information whatever; with it, the rank is dominated by the charge total
  the full-rank terminal already certifies, entry by entry.  It is a law of
  exactly the same kind as `LocalSupplyLowerBound`'s `pointwise`: a statement
  about the registration's own numeric observation, with no ledger, stage, or
  terminal in sight. -/
  charge_pos : ∀ (residual : Residual) (response : Response residual)
      (coordinate : Coordinate residual),
    0 < charge residual response coordinate
  /-- Residual-owned allowance added to the charge total of the registration's
  own coordinate schedule before CT15's capacity gate reads it.  The gate is
  `chargeTotal ≤ capacity` and `Profile.ofRegistrationAt` installs
  `capacity := chargeTotal + capacitySlack`, so the slack is headroom above the
  schedule's own charge, never a subtraction from an inherited budget: a
  subtractive reading would make CT15's overload terminal fire for every
  positive slack. -/
  capacitySlack : (residual : Residual) → Response residual → Nat
  /-- Optional registered closure of the rank-drop output: the residual-owned
  half of the fact that the CT10 → CT15 → CT16 composition has no rank-drop
  alternative at all.

  This is not a routing decision and not an asserted terminal.  Both conjuncts
  are statements about data the registration already carries, read in the
  contrapositive, and they are literally `ClassificationExhaustive` --

  * no class satisfies the registered `Direct` predicate, so CT10's direct
    search cannot hit;
  * every class is realized by the registered observation schedule through the
    registered classifier, so CT10's first-missing search cannot hit,

  which is exactly what excludes the composed CT16 closed-code mismatch
  alternative (`Profile.ofRegistrationAt_mismatch_impossible`).  The other
  three rank-drop alternatives are not registration statements and are not
  restated here.  Two of them cost nothing at all: the CT16 proper-support
  alternative is unreachable for every registration-built composition
  (`Profile.ofRegistrationAt_properSupport_impossible`), and so is the CT15
  capacity alternative, because the capacity `ofRegistrationAt` installs is the
  charge total of the very schedule CT15 tallies plus `capacitySlack`
  (`Profile.ofRegistrationAt_capacity_impossible`).  The third, the CT15
  dependence alternative, is refuted by Core from the minimal-counterexample
  closure retained in the ledger, which no registration can see and which it is
  therefore not asked to restate.

  Supplying this field lets Core eliminate the rank-drop output as vacuous
  instead of retaining it as an open branch endpoint.  Registrations whose
  rank-drop alternative is genuinely inhabited leave this `none`, and that
  output stays live exactly as before. -/
  rankDropImpossible :
    Option (PLift
      ((∀ (residual : Residual) (cls : Class residual),
          ¬ Direct residual (response residual) cls) ∧
        (∀ (residual : Residual) (cls : Class residual),
          ∃ datum, datum ∈ (observationData residual).values ∧
            classOf residual (response residual) datum = cls))) := none

/-- Exhaustiveness of the registered classification, stated against the
registration's own fields and nothing else.

Core composes CT10 → CT15 → CT16 so that CT16's closed code *is* CT10's
retained terminal and its target code is `CT10.Terminal.exhaustive`.  The two
conjuncts below are exactly the contrapositives of CT10's two non-exhaustive
terminals:

* no class satisfies the registered `Direct` predicate, so CT10's direct
  search cannot hit;
* every class is realized by the registered observation schedule through the
  registered classifier, so CT10's first-missing search cannot hit.

A registration that supplies both leaves CT10 with the exhaustive terminal
alone, hence leaves the composed closed-code test with no mismatch.  This is
the statement `BaseRegistration.rankDropImpossible` carries. -/
def BaseRegistration.ClassificationExhaustive
    {Residual : Type uResidual}
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration : BaseRegistration Residual AmbientItem Coordinate) : Prop :=
  (∀ (residual : Residual) (cls : registration.Class residual),
      ¬ registration.Direct residual (registration.response residual) cls) ∧
    (∀ (residual : Residual) (cls : registration.Class residual),
      ∃ datum, datum ∈ (registration.observationData residual).values ∧
        registration.classOf residual (registration.response residual)
          datum = cls)

/-- Ordinary target-relative rank registration.  The structural presentation
is separated from its target-dependence predicate so typed compiler linkages
can fix that predicate by construction rather than carrying an equality or a
proof callback. -/
structure Registration (Residual : Type uResidual)
    (AmbientItem : Residual → Type uAmbient)
    (Coordinate : Residual → Type uCoordinate)
    extends BaseRegistration Residual AmbientItem Coordinate where
  TargetDependent : (residual : Residual) →
    Response residual → Coordinate residual → Prop
  targetDependentDecidable : (residual : Residual) →
    (response : Response residual) → (coordinate : Coordinate residual) →
      Decidable (TargetDependent residual response coordinate)

/-- The registered rank-drop closure, read back as the classification
exhaustiveness statement Core consumes.  The two presentations are the same
statement; this projection only names it.

It lives on the base presentation, so both the ordinary registration and the
compiler-facing `FixedRegistration` linkage publish the same closure without
either of them restating it. -/
def BaseRegistration.rankDropClosure
    {Residual : Type uResidual}
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration : BaseRegistration Residual AmbientItem Coordinate) :
    Option (PLift registration.ClassificationExhaustive) :=
  registration.rankDropImpossible

/-- Registration whose target-dependence predicate is fixed in its type.
This is the compiler-facing form used by a linked minimal-context producer;
`toRegistration` merely restores the ordinary public presentation. -/
structure FixedRegistration
    {Residual : Type uResidual}
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (base : BaseRegistration Residual AmbientItem Coordinate)
    (TargetDependent : (residual : Residual) →
      base.Response residual → Coordinate residual → Prop) where
  targetDependentDecidable : (residual : Residual) →
    (response : base.Response residual) → (coordinate : Coordinate residual) →
      Decidable (TargetDependent residual response coordinate)

def FixedRegistration.toRegistration
    {Residual : Type uResidual}
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (base : BaseRegistration Residual AmbientItem Coordinate)
    (TargetDependent : (residual : Residual) →
      base.Response residual → Coordinate residual → Prop)
    (fixed : FixedRegistration base TargetDependent) :
    Registration Residual AmbientItem Coordinate where
  toBaseRegistration := base
  TargetDependent := TargetDependent
  targetDependentDecidable := fixed.targetDependentDecidable

end Hypostructure.Core.Strategy.TargetRelativeRankDichotomy
