import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Function

/-!
# Target rank of a coordinate family under an admissible quotient system

This module is the domain-generic form of the manuscript's rank apparatus:
`def:exact-response-profile`, `def:admissible-rank-quotient`,
`def:functional-rank-quotient`, `def:curvature-target-rank`,
`def:curvature-target-dependence`, `lem:target-rank-circuit`, and
`lem:curvature-dependence-routing`.

Nothing here knows what a coordinate is.  A *coordinate family* is a finite
type-indexed family; a *quotient* is a relabelling of coordinates together
with the realizations its quotient data is evaluated on; the *target rank* is
the largest subfamily no quotient of the system collapses.  The manuscript's
curvature target-rank `r_Ω(C)` is this construction at the raw internal
length-two wedges of an atom, and that instantiation lives at the node that
uses it, not here.

What this module does *not* do is decide which quotients a system contains.
That is a question about supports, contexts, and representatives -- the
manuscript's `def:admissible-rank-quotient` -- and it is answered where the
objects live: the graph layer builds the manuscript's system and hands it here
as a `QuotientSystem`.  Everything below is the rank calculus on top of it, and
the one property of a member it ever uses is that the member is functional on
the family, which is `def:functional-rank-quotient`'s closing sentence.
-/

namespace Hypostructure.Core.TargetRank

universe u v

/-- **`def:exact-response-profile`, as the rank argument uses it.**

A quotient `q : ρ_T^ex(X) → Q` of an exact response profile does two things to
the rank argument: it relabels the declared coordinates (`label`), and each
realization of the profile under `q` assigns a target-response value to each
quotient label (`value`).  Exactness of the profile is the statement that
`label` is injective *unless* the quotient identifies two coordinates, which is
what `LabelInjectiveOn` below measures.

The quotient's data universe is separate from the coordinates': a realization
is a boundaried support, which in the graph layer lives one universe above its
vertices. -/
structure RankQuotient (Coordinate : Type u) : Type (max u (v + 1)) where
  /-- The labelled coordinates of the quotient datum `Q`. -/
  Label : Type v
  /-- Target-response values. -/
  Value : Type v
  /-- The realizations of the exact response profile under this quotient. -/
  Realization : Type v
  /-- The quotient map on declared coordinate labels. -/
  label : Coordinate → Label
  /-- The target response read off a realization at a quotient label. -/
  value : Realization → Label → Value

namespace RankQuotient

variable {Coordinate : Type u}

/-- The target-response value of a declared coordinate in one realization. -/
def response (quotient : RankQuotient Coordinate)
    (realization : quotient.Realization) (coordinate : Coordinate) :
    quotient.Value :=
  quotient.value realization (quotient.label coordinate)

/-- **Label-injective on a subfamily** (`def:exact-response-profile`): every
coordinate of the subfamily is retained by the quotient, and no two distinct
coordinates of it are identified. -/
def LabelInjectiveOn (quotient : RankQuotient Coordinate)
    (family : Set Coordinate) : Prop :=
  Set.InjOn quotient.label family

/-- **Rank-reducing on a subfamily**: the manuscript's own definition, the
negation of label-injectivity. -/
def RankReducingOn (quotient : RankQuotient Coordinate)
    (family : Set Coordinate) : Prop :=
  ¬ quotient.LabelInjectiveOn family

theorem LabelInjectiveOn.mono {quotient : RankQuotient Coordinate}
    {smaller larger : Set Coordinate} (subset : smaller ⊆ larger)
    (injective : quotient.LabelInjectiveOn larger) :
    quotient.LabelInjectiveOn smaller :=
  Set.InjOn.mono subset injective

theorem RankReducingOn.mono {quotient : RankQuotient Coordinate}
    {smaller larger : Set Coordinate} (subset : smaller ⊆ larger)
    (reducing : quotient.RankReducingOn smaller) :
    quotient.RankReducingOn larger :=
  fun injective => reducing (injective.mono subset)

/-- **The determination clause of `def:curvature-target-dependence`.**

Clause (c) of a determination certificate: for any two realizations with the
same `q`-image on the coordinates of `determiners`, the `q`-image of
`coordinate` is the same -- equivalently, the `q`-value of `coordinate` is a
function of the `q`-value vector on `determiners`.  The equivalence is why the
existential form below is the definition: `φ` *is* that function. -/
def Determines (quotient : RankQuotient Coordinate) (coordinate : Coordinate)
    (determiners : Set Coordinate) : Prop :=
  ∃ evaluation : (determiners → quotient.Value) → quotient.Value,
    ∀ realization : quotient.Realization,
      quotient.response realization coordinate =
        evaluation fun determiner => quotient.response realization determiner.1

/-- **`def:functional-rank-quotient`'s rank axiom.**

Whenever the quotient is label-injective on a subfamily `independent` of the
family but not on `independent` together with one further coordinate, that
coordinate's quotient value is a function of the quotient values on a finite
subfamily of `independent`.

The manuscript's two named instances are the extremes of this clause and are
not extra requirements: a coordinate sent to a single quotient value takes
`determiners = ∅`, and a coordinate identified with `b ∈ independent` takes
`determiners = {b}` with `φ` the identity. -/
def FunctionalOn (quotient : RankQuotient Coordinate)
    (family : Set Coordinate) : Prop :=
  ∀ ⦃independent : Set Coordinate⦄, independent ⊆ family →
    ∀ ⦃coordinate : Coordinate⦄, coordinate ∈ family →
      coordinate ∉ independent →
      quotient.LabelInjectiveOn independent →
      ¬ quotient.LabelInjectiveOn (insert coordinate independent) →
      ∃ determiners ⊆ independent, quotient.Determines coordinate determiners

end RankQuotient

/-- **The admissible quotient system used to compute target rank.**

`def:functional-rank-quotient`'s closing sentence: the system "consists only of
admissible rank quotients that are functional on the coordinate family under
discussion".  Membership is left abstract -- which relabellings of the declared
signature are admissible is a question about the support, not about rank -- so
every theorem below holds for *every* such system. -/
structure QuotientSystem (Coordinate : Type u) (family : Finset Coordinate) :
    Type (max u (v + 2)) where
  /-- The quotients the system contains. -/
  Member : RankQuotient.{u, v} Coordinate → Prop
  /-- Each of them is functional on the family under discussion. -/
  functional : ∀ {quotient : RankQuotient.{u, v} Coordinate}, Member quotient →
    quotient.FunctionalOn ↑family
  /-- The canonical target-complete states from which the declared coordinate
  responses are read. -/
  State : Type v
  /-- The states retained by the target-complete response algebra. -/
  targetComplete : State → Prop
  /-- Every coordinate has its canonical Boolean obstructing/non-obstructing
  response in each target-complete state. -/
  response : State → Coordinate → Bool
  /-- The empty Boolean assignment is realized. -/
  existsTargetComplete : ∃ state, targetComplete state

namespace QuotientSystem

variable {Coordinate : Type u} {family : Finset Coordinate}

/-- **Independent target-testability** (`def:target-rank`).

A subfamily survives precisely when every Boolean assignment on its declared
coordinates is realized by a target-complete state.  This is the manuscript's
definition: a `k`-coordinate surviving family realizes all `2^k` response
states. -/
def Survives (system : QuotientSystem.{u, v} Coordinate family)
    (subfamily : Set Coordinate) : Prop :=
  ∀ assignment : subfamily → Bool,
    ∃ state, system.targetComplete state ∧
      ∀ coordinate : subfamily,
        system.response state coordinate.1 = assignment coordinate

theorem Survives.mono {system : QuotientSystem Coordinate family}
    {smaller larger : Set Coordinate} (subset : smaller ⊆ larger)
    (survives : system.Survives larger) : system.Survives smaller :=
  fun assignment => by
    classical
    let extended : larger → Bool := fun coordinate =>
      if membership : coordinate.1 ∈ smaller then
        assignment ⟨coordinate.1, membership⟩
      else false
    obtain ⟨state, complete, realizes⟩ := survives extended
    refine ⟨state, complete, ?_⟩
    intro coordinate
    have membership : coordinate.1 ∈ larger := subset coordinate.2
    simpa [extended, coordinate.2] using realizes ⟨coordinate.1, membership⟩

theorem survives_empty (system : QuotientSystem Coordinate family) :
    system.Survives (∅ : Set Coordinate) :=
  fun _assignment => by
    obtain ⟨state, complete⟩ := system.existsTargetComplete
    exact ⟨state, complete, fun coordinate => coordinate.2.elim⟩

end QuotientSystem

section Rank

variable {Coordinate : Type u} {family : Finset Coordinate}

/-- The subfamilies of the family that survive the whole system. -/
noncomputable def survivingSubfamilies
    (system : QuotientSystem Coordinate family) : Finset (Finset Coordinate) := by
  classical
  exact family.powerset.filter fun subfamily => system.Survives ↑subfamily

theorem mem_survivingSubfamilies {system : QuotientSystem Coordinate family}
    {subfamily : Finset Coordinate} :
    subfamily ∈ survivingSubfamilies system ↔
      subfamily ⊆ family ∧ system.Survives ↑subfamily := by
  classical
  simp [survivingSubfamilies, Finset.mem_filter, Finset.mem_powerset]

/-- **`def:curvature-target-rank`.**  The target rank of the family under the
system is the maximum size of a subfamily that survives every functional
admissible rank quotient of the system. -/
noncomputable def targetRank (system : QuotientSystem Coordinate family) : Nat :=
  (survivingSubfamilies system).sup Finset.card

theorem card_le_targetRank {system : QuotientSystem Coordinate family}
    {subfamily : Finset Coordinate} (subset : subfamily ⊆ family)
    (survives : system.Survives ↑subfamily) :
    subfamily.card ≤ targetRank system :=
  Finset.le_sup (f := Finset.card) (mem_survivingSubfamilies.mpr ⟨subset, survives⟩)

theorem targetRank_le_card (system : QuotientSystem Coordinate family) :
    targetRank system ≤ family.card := by
  refine Finset.sup_le fun subfamily member => ?_
  exact Finset.card_le_card (mem_survivingSubfamilies.mp member).1

/-- The rank is attained: some surviving subfamily has exactly that many
coordinates.  The empty subfamily always survives, so the maximum is taken over
a nonempty collection. -/
theorem exists_attaining (system : QuotientSystem Coordinate family) :
    ∃ independent ⊆ family, system.Survives ↑independent ∧
      independent.card = targetRank system := by
  have nonempty : (survivingSubfamilies system).Nonempty :=
    ⟨∅, mem_survivingSubfamilies.mpr
      ⟨Finset.empty_subset _, by
        simpa using system.survives_empty⟩⟩
  obtain ⟨independent, member, equality⟩ :=
    Finset.exists_mem_eq_sup (survivingSubfamilies system) nonempty Finset.card
  obtain ⟨subset, survives⟩ := mem_survivingSubfamilies.mp member
  exact ⟨independent, subset, survives, equality.symm⟩

/-- Full rank is exactly survival of the whole family. -/
theorem targetRank_eq_card_iff_survives
    (system : QuotientSystem Coordinate family) :
    targetRank system = family.card ↔ system.Survives ↑family := by
  constructor
  · intro full
    obtain ⟨independent, subset, survives, attains⟩ := exists_attaining system
    have : independent = family :=
      Finset.eq_of_subset_of_card_le subset (by omega)
    exact this ▸ survives
  · intro survives
    exact Nat.le_antisymm (targetRank_le_card system)
      (card_le_targetRank (subset_refl family) survives)

end Rank

section Circuit

variable {Coordinate : Type u} {family : Finset Coordinate}

/-- **`def:curvature-target-dependence`.**

A target-dependence in the family: a coordinate whose target response a
functional admissible rank quotient of the system determines from the target
responses on a subfamily of the others.

`proper` is the manuscript's properness clause.  "Exact coordinate labels keep
distinct declared raw coordinates distinct", so a determination of a coordinate
by a family it does not belong to is never the tautological equality of a
coordinate with itself. -/
structure Dependence (system : QuotientSystem Coordinate family)
    (coordinate : Coordinate) (determiners : Set Coordinate) : Prop where
  /-- The determined coordinate belongs to the family under discussion. -/
  determined : coordinate ∈ family
  /-- So do the determiners. -/
  supported : determiners ⊆ ↑family
  /-- The dependence is proper, not a tautological self-identification. -/
  proper : coordinate ∉ determiners
  /-- A functional admissible rank quotient of the system realizes it, and it
  is the quotient that loses rank on the family. -/
  witness : ∃ quotient, system.Member quotient ∧
    quotient.RankReducingOn ↑family ∧
      quotient.Determines coordinate determiners

end Circuit

end Hypostructure.Core.TargetRank
