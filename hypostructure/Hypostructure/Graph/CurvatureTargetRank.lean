import Hypostructure.Graph.InternalWedgeFamily
import Hypostructure.Graph.DeclaredRankQuotient

/-!
# The curvature target-rank of a region

`def:curvature-target-rank` computes `r_Ω` over the raw internal length-two
curvature tests of an atom.  A subfamily survives when every admissible quotient
that is functional on the declared family remains label-injective on it; `r_Ω`
is the maximum cardinality among those finitely many surviving subfamilies.

Every clause is the manuscript's, at the framework object the manuscript names.

* A quotient lives on a connected **determination support** `Z` that carries
  the coordinates under discussion, and its realizations are the boundaried
  graphs that can occupy `Z`'s place — `BoundaryPiece` at the support's own cut
  interface, which is what `def:curvature-target-dependence` means by "a
  realization is a `T`-boundaried support whose exact response profile maps to
  the same quotient data `Q` under `q`".
* `def:target-complete-quotient`: every identification the quotient makes
  preserves (a) the boundary degree profile and (b) the target predicate after
  gluing to every `T`-boundaried context.  Both are stated at
  `BoundaryPiece.boundaryDegreeProfile` and at `glue` against every
  `OutsideContext`, the framework's own gluing.
* `def:admissible-rank-quotient`, proper clause: at `Z ⊊ G` a rank-reducing
  quotient supplies a strictly smaller proper representative.  The manuscript
  says of it that "the five defining properties of a proper representative are
  exactly the five hypotheses of the replacement lemma `lem:replacement` for
  the support `Z`", so the clause *is*
  `InterfaceReplacement.ReplacementSupport`, which is the hypothesis
  `InterfaceReplacement.not_replacementSupport` refutes at a minimal
  counterexample.
* `def:admissible-rank-quotient`, closed clause: at `Z = G` a rank-reducing
  quotient supplies a strictly smaller admissible closed representative `H` —
  finite, simple, meeting the baseline, with
  `profile_∅(H) ⊆ profile_∅(G)`.  With an empty boundary the only context is
  the empty one, so that inclusion is `Target H → Target G`, which is the
  manuscript's own reading of it ("a dyadic cycle in `H` would add the
  corresponding empty-context target event to `profile_∅(H)`, impossible
  because `profile_∅(G)` contains no such event").

Nothing here is specialized to one manuscript: the baseline and the target are
parameters, and the module never mentions a window, a packing, or a numeral.
-/

namespace Hypostructure.Graph

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

namespace FiniteObject

/-- The declared support of a raw internal curvature test: the wedge's centre
together with the two neighbours it joins (`def:declared-coordinate-signature`,
clause (D4) — a raw curvature coordinate is indexed by its internal length-two
wedge, and its support is that wedge). -/
noncomputable def internalWedgeSupport {object : FiniteObject.{u}}
    {region : Finset object.Vertex} (test : object.InternalWedge region) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact insert test.1 test.2.1

end FiniteObject

/-- **`def:admissible-rank-quotient` on the raw curvature tests of a region.**

`r_Ω`'s quotients are the declared-family quotients of
`Graph.DeclaredQuotient` at one particular family: the raw internal length-two
wedges of the region, each carried on its own wedge as clause (D4) of
`def:declared-coordinate-signature` declares.  There is no second structure:
this abbreviation is that instance, so every field, every completeness clause
and the routing `localize` are the ones proved once in
`Graph/DeclaredRankQuotient`. -/
abbrev CurvatureQuotient (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (region : Finset object.Vertex) : Type (u + 2) :=
  DeclaredQuotient Baseline Target object (object.internalWedgeFamily region)
    (FiniteObject.internalWedgeSupport (region := region))

namespace FiniteObject

/-- **`r_Ω(X)`**: the curvature target-rank of a region — the maximum size of a
subfamily of its raw internal curvature tests that survives every functional
admissible rank quotient. -/
noncomputable def curvatureTargetRank
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (region : Finset object.Vertex) : Nat := by
  classical
  let family := object.internalWedgeFamily region
  let survives := fun subfamily : Finset (object.InternalWedge region) =>
    ∀ quotient : Core.TargetRank.RankQuotient.{u, u + 1}
        (object.InternalWedge region),
      ((∃ declared : CurvatureQuotient Baseline Target object region,
          declared.toRankQuotient = quotient) ∧
        quotient.FunctionalOn ↑family) →
      quotient.LabelInjectiveOn ↑subfamily
  exact (family.powerset.filter survives).sup Finset.card

/-- **Survival of the admissible quotient system** (`def:curvature-target-rank`):
a subfamily of the raw curvature tests of a region survives when every
admissible rank quotient that is functional on the declared family remains
label-injective on it. -/
def SurvivesCurvatureSystem
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (region : Finset object.Vertex)
    (subfamily : Finset (object.InternalWedge region)) : Prop :=
  ∀ quotient : CurvatureQuotient Baseline Target object region,
    quotient.toRankQuotient.FunctionalOn ↑(object.internalWedgeFamily region) →
      quotient.toRankQuotient.LabelInjectiveOn ↑subfamily

section RankFacts

variable (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
variable (region : Finset object.Vertex)

/-- The surviving subfamilies, as `curvatureTargetRank` filters them. -/
noncomputable def survivingCurvatureSubfamilies :
    Finset (Finset (object.InternalWedge region)) := by
  classical
  exact (object.internalWedgeFamily region).powerset.filter
    (SurvivesCurvatureSystem Baseline Target object region)

theorem mem_survivingCurvatureSubfamilies
    (subfamily : Finset (object.InternalWedge region)) :
    subfamily ∈ survivingCurvatureSubfamilies Baseline Target object region ↔
      subfamily ⊆ object.internalWedgeFamily region ∧
        SurvivesCurvatureSystem Baseline Target object region subfamily := by
  classical
  simp [survivingCurvatureSubfamilies, Finset.mem_filter, Finset.mem_powerset]

theorem curvatureTargetRank_eq_sup :
    object.curvatureTargetRank Baseline Target region =
      (survivingCurvatureSubfamilies Baseline Target object region).sup Finset.card := by
  classical
  unfold curvatureTargetRank survivingCurvatureSubfamilies
  refine congrArg (fun s : Finset (Finset (object.InternalWedge region)) =>
    s.sup Finset.card) ?_
  ext subfamily
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨subset, survives⟩
    refine ⟨subset, fun quotient functional => ?_⟩
    exact survives quotient.toRankQuotient ⟨⟨quotient, rfl⟩, functional⟩
  · rintro ⟨subset, survives⟩
    refine ⟨subset, fun quotient ⟨⟨declared, equal⟩, functional⟩ => ?_⟩
    subst equal
    exact survives declared functional

/-- The empty subfamily survives every quotient. -/
theorem survivesCurvatureSystem_empty :
    SurvivesCurvatureSystem Baseline Target object region ∅ :=
  fun _quotient _functional => by
    simp [Core.TargetRank.RankQuotient.LabelInjectiveOn]

/-- **`r_Ω` is attained**: some surviving subfamily has exactly `r_Ω` members. -/
theorem exists_attaining_curvatureTargetRank :
    ∃ independent ⊆ object.internalWedgeFamily region,
      SurvivesCurvatureSystem Baseline Target object region independent ∧
        independent.card = object.curvatureTargetRank Baseline Target region := by
  classical
  have nonempty : (survivingCurvatureSubfamilies Baseline Target object region).Nonempty :=
    ⟨∅, (mem_survivingCurvatureSubfamilies Baseline Target object region ∅).2
      ⟨Finset.empty_subset _, survivesCurvatureSystem_empty Baseline Target object region⟩⟩
  obtain ⟨independent, member, equality⟩ :=
    Finset.exists_mem_eq_sup _ nonempty Finset.card
  obtain ⟨subset, survives⟩ :=
    (mem_survivingCurvatureSubfamilies Baseline Target object region independent).1 member
  refine ⟨independent, subset, survives, ?_⟩
  rw [curvatureTargetRank_eq_sup]
  exact equality.symm

/-- **`r_Ω` is the maximum**: every surviving subfamily has at most `r_Ω`
members. -/
theorem card_le_curvatureTargetRank
    {subfamily : Finset (object.InternalWedge region)}
    (subset : subfamily ⊆ object.internalWedgeFamily region)
    (survives : SurvivesCurvatureSystem Baseline Target object region subfamily) :
    subfamily.card ≤ object.curvatureTargetRank Baseline Target region := by
  classical
  rw [curvatureTargetRank_eq_sup]
  exact Finset.le_sup (f := Finset.card)
    ((mem_survivingCurvatureSubfamilies Baseline Target object region subfamily).2
      ⟨subset, survives⟩)

/-- `r_Ω(X) ≤ |𝒲₂(X)|`. -/
theorem curvatureTargetRank_le_card :
    object.curvatureTargetRank Baseline Target region ≤
      (object.internalWedgeFamily region).card := by
  classical
  rw [curvatureTargetRank_eq_sup]
  refine Finset.sup_le fun subfamily member => ?_
  exact Finset.card_le_card
    ((mem_survivingCurvatureSubfamilies Baseline Target object region subfamily).1 member).1

/-- **`lem:target-rank-circuit`, extraction step.**  If `independent` is a
surviving subfamily of maximum size and `test` is a raw curvature test outside
it, then some functional admissible rank quotient is label-injective on
`independent` but not on `independent ∪ {test}`, and its functional clause
supplies a finite subfamily of `independent` determining `test`. -/
theorem exists_dependence_of_not_mem
    {independent : Finset (object.InternalWedge region)}
    (subset : independent ⊆ object.internalWedgeFamily region)
    (survives : SurvivesCurvatureSystem Baseline Target object region independent)
    (maximum : independent.card = object.curvatureTargetRank Baseline Target region)
    {test : object.InternalWedge region}
    (testMem : test ∈ object.internalWedgeFamily region)
    (outside : test ∉ independent) :
    ∃ determiners : Set (object.InternalWedge region),
      determiners ⊆ ↑independent ∧ determiners.Finite ∧ test ∉ determiners ∧
        ∃ quotient : CurvatureQuotient Baseline Target object region,
          quotient.toRankQuotient.FunctionalOn ↑(object.internalWedgeFamily region) ∧
            quotient.toRankQuotient.RankReducingOn
              ↑(object.internalWedgeFamily region) ∧
            quotient.toRankQuotient.Determines test determiners := by
  classical
  have notSurvive : ¬ SurvivesCurvatureSystem Baseline Target object region
      (insert test independent) := by
    intro survivesInsert
    have le := card_le_curvatureTargetRank Baseline Target object region
      (Finset.insert_subset testMem subset) survivesInsert
    rw [Finset.card_insert_of_notMem outside] at le
    omega
  simp only [SurvivesCurvatureSystem, not_forall] at notSurvive
  obtain ⟨quotient, functional, notInjective⟩ := notSurvive
  have injective := survives quotient functional
  have insertCoe : (↑(insert test independent) : Set (object.InternalWedge region)) =
      insert test ↑independent := by
    simp
  rw [Core.TargetRank.RankQuotient.LabelInjectiveOn, insertCoe] at notInjective
  obtain ⟨determiners, finite, determinersSubset, determines⟩ :=
    functional (Finset.coe_subset.2 subset) testMem
      (by simpa using outside) injective notInjective
  refine ⟨determiners, determinersSubset, finite, fun mem => outside (determinersSubset mem),
    quotient, functional, ?_, determines⟩
  intro injectiveFamily
  exact notInjective (injectiveFamily.mono (by
    rw [← insertCoe]
    exact Finset.coe_subset.2 (Finset.insert_subset testMem subset)))

/-- **`lem:target-rank-circuit`, "in particular"**: if no proper target-dependence
exists among the raw curvature tests, the whole family survives every
functional admissible rank quotient. -/
theorem survives_of_no_dependence
    (noDependence : ¬ ∃ test ∈ object.internalWedgeFamily region,
      ∃ determiners : Set (object.InternalWedge region),
        determiners ⊆ ↑(object.internalWedgeFamily region) ∧ determiners.Finite ∧
          test ∉ determiners ∧
          ∃ quotient : CurvatureQuotient Baseline Target object region,
            quotient.toRankQuotient.FunctionalOn ↑(object.internalWedgeFamily region) ∧
              quotient.toRankQuotient.RankReducingOn
                ↑(object.internalWedgeFamily region) ∧
              quotient.toRankQuotient.Determines test determiners) :
    SurvivesCurvatureSystem Baseline Target object region
      (object.internalWedgeFamily region) := by
  classical
  by_contra notAll
  obtain ⟨independent, subset, survives, maximum⟩ :=
    exists_attaining_curvatureTargetRank Baseline Target object region
  have proper : independent ≠ object.internalWedgeFamily region := by
    rintro rfl
    exact notAll survives
  obtain ⟨test, testMem, outside⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨subset, proper⟩)
  obtain ⟨determiners, determinersSubset, finite, notMem, quotient, functional, reducing,
    determines⟩ := exists_dependence_of_not_mem Baseline Target object region subset survives
      maximum testMem outside
  exact noDependence ⟨test, testMem, determiners,
    determinersSubset.trans (Finset.coe_subset.2 subset), finite, notMem, quotient,
    functional, reducing, determines⟩

end RankFacts

end FiniteObject

end Hypostructure.Graph
