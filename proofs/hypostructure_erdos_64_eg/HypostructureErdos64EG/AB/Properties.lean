import Hypostructure.Graph.TypeABCertificate
import Hypostructure.Graph.External.HegdeSandeepShashank
import HypostructureErdos64EG.Presentation

/-!
# Type-A / Type-B target registration

The global structural alternative itself -- `def:admissible`,
`def:net-charge`, the Type-A node and the Type-B node, together with every
proposition and every transport law they need -- is owned by
`Hypostructure.Graph.TypeABCertificate`.

This module registers only the presentation those declarations read: the
baseline degree and induced-path order the problem already registered, the
registered official target, and its accepted cycle lengths.  No numeral
appears anywhere in this file.
-/

namespace HypostructureErdos64EG.AB

open Hypostructure

universe u

abbrev problem := HypostructureErdos64EG.problem
abbrev Baseline := HypostructureErdos64EG.Baseline

/-- The registered baseline degree.  The manuscript's `3` is this value. -/
abbrev baselineDegree : Nat := HypostructureErdos64EG.baselineDegree

/-- The registered induced-path order.  The manuscript's `P₁₃` is this value. -/
abbrev inducedPathOrder : Nat := HypostructureErdos64EG.inducedPathOrder

/-- The registered discharge scale `1/α`.  The manuscript's `α = 1/4` of
`lem:typeA-unsaturated-discharge` is the reciprocal of this value, which is the
registered profile's own `loadMultiplier`. -/
abbrev dischargeScale : Nat := HypostructureErdos64EG.dischargeScale

/-- The presentation the Type-A/Type-B propositions read.  Declared once in
`HypostructureErdos64EG.Presentation`, above both registries. -/
abbrev presentation : Graph.TypeAB.Presentation.{u} :=
  HypostructureErdos64EG.presentation.{u}

/-- The ambient graph contains the complete paper Type-A certificate. -/
abbrev GlobalTypeA (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.TypeAB.GlobalTypeA presentation object

namespace GlobalTypeA

export Hypostructure.Graph.TypeAB.GlobalTypeA (ofCurrent mapProper iff_of_iso)

end GlobalTypeA

/-- The ambient graph contains the complete paper Type-B certificate. -/
abbrev GlobalTypeB (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.TypeAB.GlobalTypeB presentation object

namespace GlobalTypeB

export Hypostructure.Graph.TypeAB.GlobalTypeB (ofCurrent mapProper iff_of_iso)

end GlobalTypeB

/-- The non-circular sanity target: the official target or a complete global
Type-A/Type-B certificate. -/
def abPredicate (object : Graph.FiniteObject.{u}) : Prop :=
  HypostructureErdos64EG.Target object ∨
    GlobalTypeA object ∨ GlobalTypeB object

/-- The registered A/B target.  Its statement is its own closure: every
baseline object satisfies the disjunctive predicate. -/
def abTarget : Core.Target problem.{0} :=
  Core.Target.ofPredicate problem.{0} abPredicate.{0}

end HypostructureErdos64EG.AB
