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

namespace QuotientSystem

variable {Coordinate : Type u} {family : Finset Coordinate}

/-- **Survival** (`def:curvature-target-rank`): a subfamily survives the system
when it survives every one of its functional admissible rank quotients. -/
def Survives (system : QuotientSystem.{u, v} Coordinate family)
    (subfamily : Set Coordinate) : Prop :=
  ∀ quotient : RankQuotient.{u, v} Coordinate, system.Member quotient →
    quotient.LabelInjectiveOn subfamily

theorem Survives.mono {system : QuotientSystem Coordinate family}
    {smaller larger : Set Coordinate} (subset : smaller ⊆ larger)
    (survives : system.Survives larger) : system.Survives smaller :=
  fun quotient member => (survives quotient member).mono subset

theorem survives_empty (system : QuotientSystem Coordinate family) :
    system.Survives (∅ : Set Coordinate) :=
  fun _quotient _member => Set.injOn_empty _

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

/-- **Enlarging a system can only lower the rank.**  A subfamily that survives
the larger system survives the smaller one, so it is counted there too.

This is why a rank statement made at *every* system is a statement about the
one the manuscript defines `r_Ω` by: a system contained in it ranks no lower,
so a rank drop under it is a rank drop under some system, and a rank bound at
every system is a rank bound at it. -/
theorem targetRank_le_of_member_subset
    {small large : QuotientSystem Coordinate family}
    (contains : ∀ quotient, small.Member quotient → large.Member quotient) :
    targetRank large ≤ targetRank small := by
  refine Finset.sup_le fun subfamily member => ?_
  obtain ⟨subset, survives⟩ := mem_survivingSubfamilies.mp member
  exact card_le_targetRank subset
    fun quotient memberOf => survives quotient (contains quotient memberOf)

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

/-- **`lem:target-rank-circuit`.**

If `independent` is maximal among subfamilies of the family that survive every
functional admissible rank quotient, and `coordinate` lies outside it, then
some subfamily of `independent` target-determines `coordinate`.

The manuscript's proof, verbatim: maximality means `independent ∪ {coordinate}`
fails to survive some member `q`; `independent` survives `q`, so the failure of
label-injectivity involves `coordinate`; `q` is functional on the family, so a
finite subfamily of `independent` determines `coordinate`'s quotient value. -/
theorem exists_dependence_of_maximal (system : QuotientSystem Coordinate family)
    {independent : Finset Coordinate} (subset : independent ⊆ family)
    (survives : system.Survives ↑independent)
    (maximal : ∀ outside ∈ family, outside ∉ independent →
      ¬ system.Survives (insert outside ↑independent))
    {coordinate : Coordinate} (member : coordinate ∈ family)
    (fresh : coordinate ∉ independent) :
    ∃ determiners ⊆ (↑independent : Set Coordinate),
      Dependence system coordinate determiners := by
  classical
  obtain ⟨quotient, memberOf, failure⟩ :
      ∃ quotient, system.Member quotient ∧
        ¬ quotient.LabelInjectiveOn (insert coordinate ↑independent) := by
    by_contra absent
    exact maximal coordinate member fresh fun quotient memberOf =>
      not_not.mp fun failure => absent ⟨quotient, memberOf, failure⟩
  have contains : (↑independent : Set Coordinate) ⊆ ↑family := by
    exact_mod_cast subset
  have inside : insert coordinate (↑independent : Set Coordinate) ⊆ ↑family := by
    intro vertex membership
    rcases membership with rfl | inner
    · exact_mod_cast member
    · exact contains inner
  obtain ⟨determiners, contained, determines⟩ :=
    system.functional memberOf contains (by exact_mod_cast member)
      (by exact_mod_cast fresh) (survives quotient memberOf) failure
  refine ⟨determiners, contained, ?_⟩
  refine ⟨member, contained.trans contains, fun absurdity => ?_,
    ⟨quotient, memberOf, RankQuotient.RankReducingOn.mono inside failure, determines⟩⟩
  exact fresh (by exact_mod_cast contained absurdity)

/-- The rank is attained by a subfamily on which every excluded coordinate is
target-dependent: `def:curvature-target-rank` together with
`lem:target-rank-circuit`, in the single form a node commits. -/
theorem exists_independent_attaining (system : QuotientSystem Coordinate family) :
    ∃ independent ⊆ family, system.Survives ↑independent ∧
      independent.card = targetRank system ∧
      ∀ coordinate ∈ family, coordinate ∉ independent →
        ∃ determiners ⊆ (↑independent : Set Coordinate),
          Dependence system coordinate determiners := by
  classical
  obtain ⟨independent, subset, survives, attains⟩ := exists_attaining system
  refine ⟨independent, subset, survives, attains, fun coordinate member fresh => ?_⟩
  refine exists_dependence_of_maximal system subset survives ?_ member fresh
  intro outside outsideMem outsideFresh larger
  have contained : insert outside independent ⊆ family :=
    Finset.insert_subset outsideMem subset
  have bound : (insert outside independent).card ≤ targetRank system :=
    card_le_targetRank contained (by
      simpa [Finset.coe_insert] using larger)
  rw [Finset.card_insert_of_notMem outsideFresh, attains] at bound
  omega

/-- A rank drop produces a proper target-dependence.  This is the reading of
`lem:target-rank-circuit` the branch test uses: the hypothesis is the drop, and
the conclusion is the dependence Branch D is entered with.

The maximal surviving subfamily is supplied by the caller -- at a node it is
read from the ledger fact that node `[31]` committed, rather than recomputed. -/
theorem exists_dependence_of_attaining {system : QuotientSystem Coordinate family}
    {independent : Finset Coordinate} (subset : independent ⊆ family)
    (attains : independent.card = targetRank system)
    (dependent : ∀ coordinate ∈ family, coordinate ∉ independent →
      ∃ determiners ⊆ (↑independent : Set Coordinate),
        Dependence system coordinate determiners)
    (drop : targetRank system < family.card) :
    ∃ coordinate determiners, Dependence system coordinate determiners := by
  have distinct : independent ≠ family := by
    intro same
    subst same
    omega
  obtain ⟨coordinate, member, fresh⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨subset, distinct⟩)
  obtain ⟨determiners, _contained, dependence⟩ := dependent coordinate member fresh
  exact ⟨coordinate, determiners, dependence⟩

/-- **The rank-drop interface.**  A family whose rank falls short of its size
carries a proper target-dependence.  This is `lem:target-rank-circuit` in the
form the branch test at a rank comparison uses. -/
theorem exists_dependence_of_targetRank_lt (system : QuotientSystem Coordinate family)
    (drop : targetRank system < family.card) :
    ∃ coordinate determiners, Dependence system coordinate determiners := by
  obtain ⟨independent, subset, _survives, attains, dependent⟩ :=
    exists_independent_attaining system
  exact exists_dependence_of_attaining subset attains dependent drop

/-- `lem:target-rank-circuit`'s closing assertion: if no proper target-dependence
exists in the family, the whole family survives every functional admissible rank
quotient, so it is independently target-testable and the rank is its size. -/
theorem targetRank_eq_card_of_no_dependence
    (system : QuotientSystem Coordinate family)
    (independence : ∀ coordinate determiners,
      ¬ Dependence system coordinate determiners) :
    targetRank system = family.card := by
  obtain ⟨independent, subset, survives, attains, dependent⟩ :=
    exists_independent_attaining system
  by_contra drop
  obtain ⟨coordinate, determiners, dependence⟩ :=
    exists_dependence_of_attaining subset attains dependent
      (lt_of_le_of_ne (targetRank_le_card system) drop)
  exact independence coordinate determiners dependence

end Circuit

end Hypostructure.Core.TargetRank
