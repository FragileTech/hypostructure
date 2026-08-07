import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePairResponse

/-!
# The sparse pair dependence dichotomy and the entropy sandwich

`lem:sparse-pair-dependence-exit`, `lem:mixed-sparse-spine-dependence`,
`prop:sparse-pair-independence-dichotomy`, `cor:sparse-pair-entropy-saturation`,
`prop:sparse-entropy-sandwich` and `prop:sparse-entropy-sandwich-with-blockers`.

The six statements are two theorems and their readings.

**The dichotomy.**  All three dependence statements run the same case analysis
over an inclusion-minimal determination certificate, and that analysis is
`AttemptedQuotient.route`.  At an object that survives the sparse surplus exits
and admits no proper-support replacement, the two exit alternatives are
discharged — a smaller closed representative is the delocalization exit, and a
replacement is `lem:replacement` — so what remains is exactly the manuscript's
blocker alternative: two realizations the attempted determination identifies
which are separated, either by their boundary degree profiles, which is the
blocker of type (d), or by a boundaried context, which is the blocker of type
(e).  That is `blockerSeparation_of_reducing`, and it is
`lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence` at
once: neither proof inspects which coordinates the family holds, which is why
the manuscript gives them the same four cases.

`survives_of_exitFree` is `prop:sparse-pair-independence-dichotomy`: an
*admissible* quotient carries no such separation — that is what its two
completeness clauses say — so at a survivor with no blocker no admissible
quotient reduces the family, and the family is independently target-testable in
the sense of `def:target-rank`.

**The sandwich.**  `prop:sparse-entropy-sandwich-with-blockers` writes

  `|Π_free| ≤ E_spine(n) + (½σ(G) + 1) log₂ n`,

and its proof is three inequalities: the entropy count on the mixed family
`ℐ_spine ∪ {r_π : π ∈ Π_free}`, the baseline demand `|ℐ_spine| ≥ B₀(n) −
E_spine(n)`, and `lem:incremental-skeleton-room`.  `entropySandwich` below is
that composition with the logarithms cleared, in the same discipline
`def:baseline-spine-demand` is already stated in:

  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)`,  `C(N,m₀) ≤ 2^{|ℐ_spine| + E}`
  ⟹ `2^{|Π_free|} ≤ 2^{E} · n^{m − m₀}`,

whose logarithm is the manuscript's display, because `m − m₀ ≤ ½σ(G) + 1` is
`lem:sparse-slack-surplus` at the branch.  `prop:sparse-entropy-sandwich` is the
same statement at the *full* pair schedule, and
`cor:sparse-pair-entropy-saturation` is its `ℐ_spine = ∅` reading,
`2^{C(|𝒜₀|,2)} ≤ C(N,m)`.

The theorem below is the reusable cancellation step, so its two inputs are the
two inequalities it cancels.  The strategy does not publish those inputs as an
obligation: `WindowTargetPackage.mixedSpinePairDemand` constructs the tagged
mixed family, proves its full rank, obtains its exact entropy count, and applies
this theorem before node `[131]` is committed.  The framework owns the count
(`Core.FiniteEntropy.two_pow_le_card_ambient_of_realizes` and
`Graph.LabelledOn.two_pow_le_card_of_realized`), and `Graph.skeletonBudget` is
`lem:skeleton-dominates`' own `C(N,m)`.

The asymptotic tail of `prop:sparse-entropy-sandwich` — *"consequently, if
`E_spine(n) = O(n)` and `|𝒜₀| ≥ c₁σ(G)`, then `σ(G) = O(√n)`"* — is not stated
here.  It is a consequence of the displayed inequality at a branch that supplies
the two rate hypotheses, and it belongs to the node that supplies them.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

/-! ## The dependence dichotomy -/

/-- **`lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence`,
at a survivor.**

> Suppose the coordinate family `ℛ_Π` does not survive every admissible rank
> quotient.  Then either `G` has a sparse surplus exit, or some `π ∈ Π` has a
> sparse surplus blocker of type (d) or (e).

The two exit alternatives the manuscript's proof produces are discharged by the
survivor's own hypotheses — the whole-graph case is the delocalization exit, and
the proper-support case is `lem:replacement` — so what a rank-reducing attempted
determination leaves is precisely the blocker: two realizations it identifies
which are separated by their boundary degree profiles (type (d)) or by a
boundaried context (type (e)).

Both witnesses are the concrete finite objects `def:surplus-blockers` names,
which is what `DemandActivation.blocks_boundaryProfile` and
`blocks_targetResponse` record on the ledger. -/
theorem blockerSeparation_of_reducing
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (survives : SurvivesSparseExits Baseline
      (Graph.HasCycleWithLength LengthOK) LengthOK object)
    (noReplacement : ∀ support : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
        support)
    (attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object family coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family) :
    (∃ left right, attempt.Identifies left right ∧
        left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
      (∃ left right, attempt.Identifies left right ∧
        Response.TargetDefect (Graph.HasCycleWithLength LengthOK) left right) := by
  rcases attempt.route reducing with profiles | defect | replacement |
    ⟨representative, smaller, baseline, transfer⟩
  · exact Or.inl profiles
  · exact Or.inr defect
  · exact absurd replacement (noReplacement _)
  · exact absurd (SparseSurplusExit.delocalization representative smaller baseline
      transfer) survives

/-- **`prop:sparse-pair-independence-dichotomy`.**

> If `G` survives the sparse surplus exits and no pair in `C(𝒜₀,2)` has a sparse
> surplus blocker, then the full family `{r_π}` is independently
> target-testable.

An admissible rank quotient carries no blocker separation: its two completeness
clauses are exactly the statement that identified realizations share a boundary
degree profile and are context-equivalent.  So at a survivor with no blocker the
first two alternatives of `blockerSeparation_of_reducing` are unavailable and
the remaining two are refuted, whence no member of the system reduces the
family — which is independent target-testability in the sense of
`def:target-rank`. -/
theorem survives_of_exitFree
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (survives : SurvivesSparseExits Baseline
      (Graph.HasCycleWithLength LengthOK) LengthOK object)
    (noReplacement : ∀ support : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
        support) :
    (FiniteObject.declaredQuotientSystem Baseline
      (Graph.HasCycleWithLength LengthOK) object family
      coordinateSupport).Survives ↑family := by
  rintro quotient ⟨⟨admissible, rfl⟩, _functional⟩
  by_contra reducing
  rcases admissible.localize reducing with replacement |
    ⟨representative, smaller, baseline, transfer⟩
  · exact noReplacement _ replacement
  · exact survives (SparseSurplusExit.delocalization representative smaller
      baseline transfer)

/-- The independently target-testable family attains full target rank: the
dichotomy read through `Core.TargetRank`'s own rank apparatus, which is the form
`def:baseline-spine-demand` consumes. -/
theorem targetRank_eq_card_of_exitFree
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (survives : SurvivesSparseExits Baseline
      (Graph.HasCycleWithLength LengthOK) LengthOK object)
    (noReplacement : ∀ support : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
        support) :
    Core.TargetRank.targetRank
        (FiniteObject.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK) object family coordinateSupport) =
      family.card :=
  (Core.TargetRank.targetRank_eq_card_iff_survives _).mpr
    (survives_of_exitFree survives noReplacement)

/-! ## The entropy sandwich -/

/-- **`prop:sparse-entropy-sandwich-with-blockers`, with the logarithms
cleared.**

  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)`  and  `C(N,m₀) ≤ 2^{|ℐ_spine| + E}`
  ⟹ `2^{|Π_free|} ≤ 2^{E} · n^{m − m₀}`.

Taking `log₂` gives the manuscript's

  `|Π_free| ≤ E_spine(n) + (m − m₀)·log₂ n`,

and `m − m₀ ≤ ½σ(G) + 1` is the branch's own slack identity, which is why the
display carries `(½σ(G) + 1) log₂ n`.

The proof is the manuscript's three steps and nothing else: the entropy count on
the mixed family, `lem:incremental-skeleton-room` at the object's own edge count,
and the baseline demand.  The spine count cancels because it appears on both
sides, which is the sense in which the sandwich charges only the *free* pairs. -/
theorem entropySandwich (object : FiniteObject.{u})
    {baselineDegree spineCount freeCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + freeCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    2 ^ freeCount ≤
      2 ^ deficit *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) := by
  have room := skeletonBudget_le_cubicBaselineBudget_mul_pow object baseline above
  have chain :
      2 ^ spineCount * 2 ^ freeCount ≤
        2 ^ spineCount *
          (2 ^ deficit *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree)) := by
    calc 2 ^ spineCount * 2 ^ freeCount
        = 2 ^ (spineCount + freeCount) := by rw [pow_add]
      _ ≤ skeletonBudget object := entropy
      _ ≤ cubicBaselineBudget object.vertexCount baselineDegree *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree) := room
      _ ≤ 2 ^ (spineCount + deficit) *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree) :=
          Nat.mul_le_mul_right _ demand
      _ = 2 ^ spineCount *
            (2 ^ deficit *
              object.vertexCount ^
                (object.edgeCount -
                  cubicBaselineEdgeCount object.vertexCount baselineDegree)) := by
          rw [pow_add, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left chain (Nat.two_pow_pos spineCount)

/-- **`prop:sparse-entropy-sandwich`**: the same bound at the *full* pair
schedule.

The manuscript states it for `C(|𝒜₀|,2)` rather than for `|Π_free|`, under the
stronger hypothesis that *no* pair has a blocker — in which case `Π_free` is the
whole schedule.  So it is `entropySandwich` read at `freeCount = C(|𝒜₀|,2)`, and
nothing is proved twice. -/
theorem entropySandwich_of_unblocked (object : FiniteObject.{u})
    {baselineDegree spineCount pairCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + pairCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    2 ^ pairCount ≤
      2 ^ deficit *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) :=
  entropySandwich object baseline above entropy demand

/-- **`cor:sparse-pair-entropy-saturation`, with the logarithm cleared.**

> If `G` survives the sparse surplus exits and no pair in `C(𝒜₀,2)` has a sparse
> surplus blocker, then `C(|𝒜₀|,2) ≤ log₂ C(C(n,2), m)`.

This is the entropy count at `ℐ_spine = ∅`: `2^{C(|𝒜₀|,2)} ≤ C(N,m)`, which is
`Graph.skeletonBudget` at the object's own order and edge count.  The manuscript
derives it from `prop:sparse-pair-independence-dichotomy` together with
`lem:independent-target-entropy` and `lem:skeleton-dominates`, and that is
exactly the composition the `entropy` hypothesis names. -/
theorem entropySaturation_of_unblocked (object : FiniteObject.{u})
    {pairCount : Nat}
    (entropy : 2 ^ (0 + pairCount) ≤ skeletonBudget object) :
    2 ^ pairCount ≤ skeletonBudget object := by
  simpa using entropy

end Hypostructure.Graph
