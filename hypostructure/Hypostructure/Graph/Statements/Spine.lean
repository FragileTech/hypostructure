import Hypostructure.Graph.Statements.Parameters

/-!
# Statements: Spine

Proof-agnostic statement definitions of the minimum-degree cycle spine:
entry, spine, net-charge, entropy, cold-corridor, absorbed-germ and dense/near-cubic survivor statements.
Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- The problem this spine argues about: a minimum-degree baseline at the
registered threshold, with the problem's own presentation attached. -/
abbrev problem (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters) :
    Core.Problem.{u + 1, v} :=
  Graph.problemWithPresentation (Graph.MinimumDegreeAtLeast data.threshold)
    BranchState Presentation presentation

/-- The registered progress order: vertex count, then edge count. -/
abbrev progress (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters) :
    Core.Progress.{u + 1, v, 0}
      (problem BranchState Presentation presentation data) :=
  (Graph.CanonicalProgress.progress
    (P := problem BranchState Presentation presentation data))

/-- The paper's refinement of node `[4]`: after vertex and edge count, compare
the fixed canonical labelled decomposition code.  The code is represented by
the labelled graph from which the canonical boundaried decomposition is read;
the order itself is fixed once and for all by `WellOrderingRel`. -/
abbrev CanonicalDecompositionCode :=
  Σ n : Nat, Graph.LabelledOn n

/-- The canonical labelled code of a finite object. -/
noncomputable def canonicalDecompositionCode
    (object : Graph.FiniteObject.{u}) : CanonicalDecompositionCode :=
  ⟨object.vertexCount, Graph.BlockedClass.objectSkeleton object⟩

/-- Strict lexicographic decrease in the paper's refined
`(|V|,|E|,Φ)` order. -/
noncomputable def RefinedLexicographicallySmaller
    (smaller larger : Graph.FiniteObject.{u}) : Prop :=
  Prod.Lex (Prod.Lex (· < ·) (· < ·)) WellOrderingRel
    (smaller.lexicographicSize, canonicalDecompositionCode smaller)
    (larger.lexicographicSize, canonicalDecompositionCode larger)

/-- Node `[4]`'s literal `(|V|,|E|,Φ)` progress profile. -/
noncomputable def refinedProgress
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters) :
    Core.Progress.{u + 1, v, 0}
      (problem BranchState Presentation presentation data) where
  Measure := Graph.LexicographicSize × CanonicalDecompositionCode
  lt := Prod.Lex (Prod.Lex (· < ·) (· < ·)) WellOrderingRel
  wellFounded :=
    (wellFounded_lt.prod_lex wellFounded_lt).prod_lex
      WellOrderingRel.isWellOrder.wf
  measure := fun object =>
    (object.lexicographicSize, canonicalDecompositionCode object)

theorem refinedProgress_smaller_iff
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    {smaller larger : Graph.FiniteObject.{u}} :
    (refinedProgress BranchState Presentation presentation data).Smaller
        smaller larger ↔
      RefinedLexicographicallySmaller smaller larger :=
  Iff.rfl

/-- Every strict vertex/edge reduction remains strict after adding the paper's
third coordinate.  Earlier nodes use this bridge and do not inspect `Φ`. -/
theorem refinedProgress_smaller_of_size_smaller
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    {smaller larger : Graph.FiniteObject.{u}}
    (sizeSmaller :
      (progress BranchState Presentation presentation data).Smaller
        smaller larger) :
    (refinedProgress BranchState Presentation presentation data).Smaller
      smaller larger :=
  Prod.Lex.left _ _ sizeSmaller

/-- The two minimality interfaces published by node `[4]`.  `sizeMinimal` is
the old `(|V|,|E|)` consequence used by all earlier nodes; `refinedMinimal` is
the paper's third-coordinate tie-break consumed at `[166]`. -/
structure SelectionMinimality
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop where
  sizeMinimal : ∀ smaller : Graph.FiniteObject.{u},
    (progress BranchState Presentation presentation data).Smaller smaller object →
    Graph.MinimumDegreeAtLeast data.threshold smaller →
    Graph.HasCycleWithLength data.LengthOK smaller
  refinedMinimal : ∀ smaller : Graph.FiniteObject.{u},
    (refinedProgress BranchState Presentation presentation data).Smaller
      smaller object →
    Graph.MinimumDegreeAtLeast data.threshold smaller →
    Graph.HasCycleWithLength data.LengthOK smaller

instance selectionMinimalityCoeFun
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    CoeFun (SelectionMinimality BranchState Presentation presentation data object)
      (fun _ => ∀ smaller : Graph.FiniteObject.{u},
        (progress BranchState Presentation presentation data).Smaller smaller object →
        Graph.MinimumDegreeAtLeast data.threshold smaller →
        Graph.HasCycleWithLength data.LengthOK smaller) :=
  ⟨SelectionMinimality.sizeMinimal⟩

/-- **`𝒲₂(R)`**: the raw internal length-two curvature tests carried by the
remainder a packing leaves.  This is the family whose rank
`def:curvature-target-rank` takes, and `internalWedgeFamily_card` says it has
exactly `W₂(R)` members. -/
noncomputable abbrev remainderCurvatureTests (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    Finset (object.InternalWedge (object.remainderSupport packing)) :=
  object.internalWedgeFamily (object.remainderSupport packing)

/-- **`r_Ω(R)`**: the curvature target-rank of the remainder. -/
noncomputable abbrev remainderCurvatureTargetRank (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  object.curvatureTargetRank (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) (object.remainderSupport packing)

/-- The manuscript's boundaried-piece part of the remainder: vertices whose
ambient degree is at the registered cubic baseline.  Near-cubic surplus bounds
the omitted high-degree vertices, while this support is exactly the one on
which the rooted-ball count is subcubic. -/
noncomputable def remainderSubcubicSupport (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Finset object.Vertex := by
  classical
  exact (object.remainderSupport packing).filter fun vertex =>
    object.degree vertex ≤ data.threshold

/-- The exact finite coordinate tested by `prop:two-budget` (b)/(c).  Its code
is the radius-two rooted type on the literal subcubic remainder support, and
the registered near-cubic threshold is the finite `o(n)` tolerance. -/
noncomputable def RemainderTypeCoordinateRepetitive (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop := by
  classical
  let support := remainderSubcubicSupport data object packing
  exact Graph.RootedLocalType.StructurallyRepetitive
    (object.rootedLocalTypeCode support 2)
    (data.surplusThreshold object.vertexCount)

/-- Unfolding bridge for the literal remainder coordinate.  Rows use this
named equality instead of asking the simplifier to unfold the complete
strategy vocabulary. -/
theorem remainderTypeCoordinateRepetitive_iff (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    RemainderTypeCoordinateRepetitive data object packing ↔
      (by
        classical
        exact Graph.RootedLocalType.StructurallyRepetitive
          (object.rootedLocalTypeCode
            (remainderSubcubicSupport data object packing) 2)
          (data.surplusThreshold object.vertexCount)) := by
  classical
  rfl

/-- The common dominant-rooted-type payload.  `RootClause` distinguishes the
plain conclusion of `lem:dominant-type`, its root-wedge arm, and its wedge-free
arm without allowing any branch to choose different packing/dominant/root
witnesses. -/
noncomputable def DominantRootedTypeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (RootClause : Finset object.Vertex → object.Vertex → Prop) : Prop := by
  classical
  exact ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      remainderCurvatureTargetRank data object packing =
        object.internalWedgeCount (object.remainderSupport packing) ∧
      let support := object.remainderSupport packing
      let subcubic := remainderSubcubicSupport data object packing
      ∃ dominant : Finset object.Vertex, ∃ root : object.Vertex,
        ∃ dominantSubset : dominant ⊆ subcubic,
          ∃ rootMem : root ∈ dominant,
            support.card ≤ dominant.card +
              2 * data.surplusThreshold object.vertexCount ∧
            (∀ vertex, ∀ vertexMem : vertex ∈ dominant,
              object.rootedLocalTypeCode subcubic 2
                ⟨root, dominantSubset rootMem⟩ =
              object.rootedLocalTypeCode subcubic 2
                ⟨vertex, dominantSubset vertexMem⟩) ∧
            RootClause subcubic root

/-- The root of the selected dominant type contains the internal length-two
wedge tested by `prop:two-budget` (b). -/
noncomputable def DominantRootWedgeClause (object : Graph.FiniteObject.{u})
    (subcubic : Finset object.Vertex) (root : object.Vertex) : Prop :=
  object.RootedInternalWedgeClause subcubic root

/-- **An admissible rank quotient of the remainder**, in the manuscript's own
sense: `Graph.CurvatureQuotient` is `def:admissible-rank-quotient` at the raw
curvature tests, carrying its connected determination support, the
target-completeness clauses of `def:target-complete-quotient`, and the two
representative clauses its scope requires.  A determination certificate of
`def:curvature-target-dependence` is one of these together with the
rank-reduction it performs. -/
abbrev remainderQuotient (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Type (u + 2) :=
  Graph.CurvatureQuotient (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) object
    (object.remainderSupport packing)

/-- **A determination certificate of `def:curvature-target-dependence`**, at the
remainder a packing leaves.

The definition's tuple is `𝔠 = (X, T, q, 𝒫)`, and each clause is here:

* (a) `X` is a connected `T`-boundaried support carrying the coordinates.  That
  is the quotient's own `support`, `connected` and `carries`, and `T` is the
  support's own cut interface, which is why no boundary is a parameter.
* (b) `q` is a functional admissible rank quotient of the exact response profile
  of `X`.  That is `remainderQuotient`, a member of the manuscript's own system.
* (c) the `q`-value of `a` is a function of the `q`-value vector on `ℬ`.  That
  is `Determines`, together with the properness clause `a ∉ ℬ`.
* (d) `𝒫`, the finite declared support data, is carried by `carries`: the
  support already contains the declared support of every coordinate under
  discussion, which is what the certificate records `𝒫` for.

The rank reduction is the drop Branch D was entered on: the certificate is the
quotient that loses label-injectivity on `𝒲₂(R)`. -/
def DeterminationCertificate (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (test : object.InternalWedge (object.remainderSupport packing))
    (determiners : Set
      (object.InternalWedge (object.remainderSupport packing)))
    (quotient : remainderQuotient data object packing)
    (supportData : Finset
      (object.InternalWedge (object.remainderSupport packing))) : Prop := by
  classical
  exact
    let family := remainderCurvatureTests object packing
    test ∈ family ∧ determiners ⊆ (↑family : Set _) ∧ determiners.Finite ∧
      test ∉ determiners ∧ quotient.toRankQuotient.FunctionalOn ↑family ∧
        quotient.toRankQuotient.RankReducingOn ↑family ∧
          quotient.toRankQuotient.Determines test determiners ∧
            supportData = family ∧
              ∀ coordinate ∈ supportData,
                Graph.FiniteObject.internalWedgeSupport
                    (region := object.remainderSupport packing) coordinate ⊆
                  quotient.support

/-- **The bookkeeping enlargement `C ∪ Z`.**

The paper's connected determination support `Z` is `quotient.support`.  This
union is used only at node `[40]` to retain the already-recorded piece `C`
while witnessing that the certificate reaches outside it.  In particular, it
is not the support classified by node `[41]` and it is not the domain of the
closed exact profile at node `[43]`. -/
noncomputable def delocalizationSupport (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (quotient : remainderQuotient data object packing) :
    Finset object.Vertex := by
  classical
  exact quotient.support ∪ object.remainderSupport packing

theorem remainderSupport_subset_delocalizationSupport (data : Parameters)
    {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing) :
    object.remainderSupport packing ⊆
      delocalizationSupport data object packing quotient := by
  classical
  intro vertex member
  simp [delocalizationSupport, member]

/-- **`C ∪ Z ⊋ C` when the certificate reaches outside `C`**, the bookkeeping
witness retained by node `[40]`. -/
theorem remainderSupport_ssubset_delocalizationSupport (data : Parameters)
    {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing)
    (outside : ¬ quotient.support ⊆ object.remainderSupport packing) :
    object.remainderSupport packing ⊂
      delocalizationSupport data object packing quotient := by
  classical
  refine ⟨remainderSupport_subset_delocalizationSupport data quotient,
    fun contained => outside fun vertex member => ?_⟩
  exact contained (by simp [delocalizationSupport, member])

/-- **The realizations a quotient identifies.**  `def:target-complete-quotient`
governs exactly the pairs of `T`-boundaried states that carry the same quotient
datum, which here is the same value at every declared raw curvature test. -/
def Identified {data : Parameters} {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
        quotient.support)) : Prop :=
  ∀ test ∈ remainderCurvatureTests object packing,
    quotient.value left (quotient.label test) =
      quotient.value right (quotient.label test)

/-- **The determination a quotient certifies is target-complete.**

Both clauses of `def:target-complete-quotient` at the quotient's own boundaried
states: identified states lie in one boundary-degree fibre
(`lem:degree-profile-fibres`) and no outside context separates them
(`lem:context-universality`).  Node `[36]`'s yes arm commits this of every
quotient on the remainder; nodes `[38]`, `[41]` and `[43]` carry it on the
certificate they route, because the manuscript's cases (ii) and (iii) are about
a *target-complete* rank-reducing quotient and not merely a rank-reducing
one. -/
def TargetCompleteAt (data : Parameters) {object : Graph.FiniteObject.{u}}
    {packing : Finset (Finset object.Vertex)}
    (quotient : remainderQuotient data object packing) : Prop :=
  ∀ left right, Identified quotient left right →
    left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
      Graph.Response.ContextEquivalent
        (Graph.HasCycleWithLength data.LengthOK) left right

/-- **`W₂(R)`**, and the allowance node `[32]` subtracts from it. -/
noncomputable abbrev remainderWedgeSupply (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  object.internalWedgeCount (object.remainderSupport packing)

/-- **`|𝒢(R)|`** of `def:remainder-entropy`, at the remainder a packing leaves:
the labelled simple graphs on `V(R)` carrying the constraints node `[27]` has
already imposed on the branch — window-freeness at the registered order, and no
subregion meeting the registered baseline.  It is the *only* thing the entropy
definition consumes; no enumeration is prescribed. -/
noncomputable abbrev remainderStates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Nat :=
  Graph.remainderStateCount data.windowOrder data.threshold
    (object.positiveDeficiency (object.remainderSupport packing) data.threshold)
    (object.internalEdgeCount (object.remainderSupport packing))
    (object.remainderSupport packing).card

/-- `lem:curv-enum` at node `[21]`: the three exact certified counts and their
flatness entropy cost.

The witnesses are read from the registered `(1,1)` row itself.  Its semantic
certificate proves that they are exactly the finite safe, curvature-positive,
and flat enumerations.  Thus the EG presentation reduces these witnesses to
the manuscript's displayed values without copying any numeral into the
strategy row. -/
def BarrierEnumerationStatement (data : Parameters) : Prop :=
  let presentation := data.windowBarrier
  letI := presentation.indexFintype
  let row := data.curvatureBarrierRow
  let left := presentation.table.counts.leftLength row
  let right := presentation.table.counts.rightLength row
  ∃ safe curvaturePositive flat : Nat,
    safe = presentation.table.counts.storedSafe row ∧
    curvaturePositive = safe - flat ∧
    flat = presentation.table.counts.storedFlat row ∧
    safe = presentation.profile.safeCount left right ∧
    curvaturePositive = presentation.profile.obstructedCount left right ∧
    flat = presentation.profile.flatCount left right ∧
    Real.logb 2 ((safe : ℝ) / flat) =
      Real.logb 2
        ((presentation.table.counts.storedSafe row : ℝ) /
          presentation.table.counts.storedFlat row)

/-- The per-window width of the separated multi-scale package of
`lem:p13-window-package`: the certified table's aggregate safe/flat ratio,
compounded across the selected dyadic scales and only then floored — the
manuscript's `(c₁₃ − o(1)) log₂ n` bits per packed window. -/
noncomputable def windowPackageBits (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat := by
  classical
  letI := data.windowBarrier.indexFintype
  exact Nat.log2
    ((Core.Finite.CertifiedTableAggregation.safeProduct data.windowBarrier.table ^
        data.separatedScaleCount object.vertexCount - 1) /
      Core.Finite.CertifiedTableAggregation.flatProduct data.windowBarrier.table ^
        data.separatedScaleCount object.vertexCount)

/-- The manuscript fixes one maximal packing before splitting it.  This is the
canonical finite choice of that packing, hence every later key names the same
family without transporting a witness outside the ledger. -/
noncomputable def canonicalWindowPacking (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) :=
  Classical.choose (object.exists_windowPacking_card_eq data.windowOrder)

/-- **The code of the canonical entropy comparison retained by a window
family** (`def:cold-window-ledger`, `def:remainder-entropy`,
`def:curvature-target-rank`): the full canonical package of every window of the
family (`windowPackageBits` per window, `lem:p13-window-package`), the
remainder states of the fixed maximal packing's remainder, and the exact code of
its raw curvature tests (`c_Ω` bits per test of `r_Ω(R)`), multiplied — the
number of target-complete states the comparison has to distinguish for that
family. -/
noncomputable def retainedCode (data : Parameters) (object : Graph.FiniteObject.{u})
    (family : Finset (Finset object.Vertex)) : Nat :=
  2 ^ (windowPackageBits data object * family.card) *
      remainderStates data object (canonicalWindowPacking data object) *
    2 ^ (data.curvatureCost *
      remainderCurvatureTargetRank data object (canonicalWindowPacking data object))

/-! The realization test of node `[158]` and the retained-code predicate of
node `[22]` are separate.  The first is exactly the single
window-package inequality displayed in `def:window-realization-test`; the
latter additionally retains the remainder and curvature code. -/
/-- **`def:window-realization-test`, nodes `[158]`--`[159]`.**  The canonical
window-package states of a family are realized by labelled skeletons.  This is
only the paper's package-count clause; the stronger retained-code clause is
`WindowFamilyRealized` below and belongs to the hot/cold ledger. -/
def WindowPackageRealized (data : Parameters) (object : Graph.FiniteObject.{u})
    (family : Finset (Finset object.Vertex)) : Prop :=
  ∃ (State : Type u)
    (stateOf : Graph.PackedWindowRealization.Skeleton
      object.vertexCount object.edgeCount → State),
    2 ^ (windowPackageBits data object * family.card) ≤
      Nat.card (Set.range stateOf)

/-- **`def:cold-window-ledger` / `def:curvature-target-rank`: a window family
retained in the canonical entropy comparison.**  The comparison's code for the
family — its full canonical window packages together with the remainder states
and the exact curvature code of the fixed packing (`retainedCode`) — is
realized canonically by the labelled skeletons of the current object's own
class `𝒢_{n,m}`: an assignment of target-complete states to skeletons whose
range has at least the family's window package states (`lem:p13-window-package`,
the live-hot comparison of nodes `[22]`--`[23]`) and at least the retained
code.  This is `lem:independent-target-entropy`'s "independently
target-testable family … arising canonically from graphs in a labelled graph
class", the
exact-code equality `def:curvature-target-rank` says is retained on the surviving
hot residual, and precisely the premise `lem:independent-target-entropy`
consumes; its failure is what makes a window cold. -/
def WindowFamilyRealized (data : Parameters) (object : Graph.FiniteObject.{u})
    (family : Finset (Finset object.Vertex)) : Prop :=
  ∃ (State : Type u)
    (stateOf : Graph.PackedWindowRealization.Skeleton
      object.vertexCount object.edgeCount → State),
    2 ^ (windowPackageBits data object * family.card) ≤ Nat.card (Set.range stateOf) ∧
      retainedCode data object family ≤ Nat.card (Set.range stateOf)

/-- Retention is monotone: a subfamily of a retained family is retained (its
package code and its retained code are both no larger). -/
theorem WindowFamilyRealized.mono {data : Parameters} {object : Graph.FiniteObject.{u}}
    {smaller larger : Finset (Finset object.Vertex)} (subset : smaller ⊆ larger)
    (realized : WindowFamilyRealized data object larger) :
    WindowFamilyRealized data object smaller := by
  obtain ⟨State, stateOf, packageLe, codeLe⟩ := realized
  have cardLe := Finset.card_le_card subset
  refine ⟨State, stateOf, ?_, ?_⟩
  · exact le_trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ cardLe)) packageLe
  · refine le_trans ?_ codeLe
    unfold retainedCode
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ cardLe)))

/-- The manuscript's canonical entropy comparison retains a canonical maximal
retained subfamily of the fixed maximal packing; the choice function below is
that lexicographic tie-break.  When the comparison realizes no family's code —
not even the empty family's remainder-and-curvature code — every packed window is
cold: `def:curvature-target-rank`'s "its failure is the complementary cold
residual". -/
theorem exists_maximal_windowFamilyRealized (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    ∃ hot : Finset (Finset object.Vertex),
      hot ⊆ canonicalWindowPacking data object ∧
        (WindowFamilyRealized data object hot ∨
          (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
        ∀ other : Finset (Finset object.Vertex),
          other ⊆ canonicalWindowPacking data object →
            WindowFamilyRealized data object other → other.card ≤ hot.card := by
  classical
  by_cases emptyRealized : WindowFamilyRealized data object ∅
  · obtain ⟨hot, memHot, maximal⟩ := Finset.exists_max_image
      ((canonicalWindowPacking data object).powerset.filter
        (WindowFamilyRealized data object)) Finset.card
      ⟨∅, by simp [Finset.mem_filter, emptyRealized]⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at memHot
    refine ⟨hot, memHot.1, Or.inl memHot.2, fun other subset realized => ?_⟩
    exact maximal other (by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨subset, realized⟩)
  · refine ⟨∅, Finset.empty_subset _, Or.inr ⟨rfl, emptyRealized⟩,
      fun other _subset realized => ?_⟩
    -- A realized family's code dominates the empty family's code, so the empty
    -- family would be realized too.
    exfalso
    obtain ⟨State, stateOf, packageLe, codeLe⟩ := realized
    refine emptyRealized ⟨State, stateOf, ?_, le_trans ?_ codeLe⟩
    · simp only [Finset.card_empty, Nat.mul_zero, pow_zero]
      exact le_trans Nat.one_le_two_pow packageLe
    · simp only [retainedCode, Finset.card_empty, Nat.mul_zero, pow_zero, Nat.one_mul]
      refine Nat.mul_le_mul_right _ ?_
      calc remainderStates data object (canonicalWindowPacking data object)
          = 1 * remainderStates data object (canonicalWindowPacking data object) := by
            rw [Nat.one_mul]
        _ ≤ 2 ^ (windowPackageBits data object * other.card) *
              remainderStates data object (canonicalWindowPacking data object) :=
            Nat.mul_le_mul_right _ Nat.one_le_two_pow

/-- `𝒫_hot`: the canonical maximal subfamily of the fixed packing retained in
the canonical entropy comparison. -/
noncomputable def canonicalHotWindows (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) :=
  Classical.choose (exists_maximal_windowFamilyRealized data object)

/-- `𝒫_cold`: the packed windows not retained in the comparison. -/
noncomputable def canonicalColdWindows (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) := by
  classical
  exact canonicalWindowPacking data object \ canonicalHotWindows data object

/-- **The joint package demand of nodes `[52]`--`[53]`.**  The window
coordinates of `lem:p13-window-package` retained in the comparison — the hot
windows, at the registered rate — and the remainder states of
`def:remainder-entropy`, multiplied, at the fixed maximal packing: the number of
target-complete states the branch has to distinguish (`prop:two-budget` (a),
`eq:feasibility`, the window-plus-remainder accounting of `prop:p13-density`).
The forced curvature cost of `cor:forced-curvature-cost` is the sharpening of
`def:Theta` that `rem:closure-robust` says the closure does not need: the
curvature patterns are realized by remainder graphs, i.e. by members of the
remainder class already counted, so it is not a further independent factor of
the demand; it stays on the ledger as `K .forcedCurvatureCost`.  `[53]` compares
exactly this demand against the labelled skeleton budget. -/
noncomputable def jointPackageDemand (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        (canonicalHotWindows data object).card) *
    remainderStates data object (canonicalWindowPacking data object)

/-- The hot/cold partition created at node `[22]`, `def:cold-window-ledger`:
`hot` is a maximal retained subfamily of the fixed maximal packing and `cold`
is its complement.  The equivalences prevent a consumer from substituting an
arbitrary partition. -/
def IsHotColdWindowPartition (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing hot cold : Finset (Finset object.Vertex)) : Prop :=
    object.IsWindowPacking data.windowOrder packing ∧
    packing.card = object.windowPackingNumber data.windowOrder ∧
    (∀ support : Finset object.Vertex,
      object.InducesWindow data.windowOrder support →
        ∃ member ∈ packing, ¬ Disjoint support member) ∧
    (hot ⊆ packing ∧
      (WindowFamilyRealized data object hot ∨
        (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
      ∀ other : Finset (Finset object.Vertex), other ⊆ packing →
        WindowFamilyRealized data object other → other.card ≤ hot.card) ∧
    (∀ window, window ∈ cold ↔ window ∈ packing ∧ window ∉ hot) ∧
    Disjoint hot cold ∧
    ∀ window, window ∈ packing ↔ window ∈ hot ∨ window ∈ cold

def HotColdWindowStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  IsHotColdWindowPartition data object
    (canonicalWindowPacking data object)
    (canonicalHotWindows data object)
    (canonicalColdWindows data object)

def BarrierCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        (canonicalHotWindows data object).card) ≤
      Graph.skeletonBudget object

def BarrierOverflowStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.skeletonBudget object <
    2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
      (canonicalHotWindows data object).card)

/-! ## Nodes `[170]`--`[172]`: the barrier states of the blocked class

`lem:scale-additivity` reads the `(a,b)`-barrier state of a packed window at a
separated dyadic scale as a function of the labelled skeleton
(`Graph/BarrierOverlapSystem.lean`), and `lem:blocked-graphs-compress` encodes a
member of `𝓑(𝒫)` as its outside edges together with all those states.  The
a-priori range `W_{a,b}` and the surviving set `F_{a,b}` are the two columns of
the *registered* certified barrier table (`data.windowBarrier`), and the
aggregate saving `c₁₃ = Σ_{a,b} γ_{a,b}` is that table's registered
`binaryRateFloor` (`data.windowRate`); no constant is written here. -/
/-- The packed windows at their labelled positions. -/
noncomputable def blockedWindowLabels (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Finset (Fin object.vertexCount)) :=
  Graph.BlockedClass.windowLabels object (canonicalWindowPacking data object)

/-- `𝓑(𝒫)` at the object, the class `def:blocked-class` fixes. -/
@[reducible] noncomputable def blockedClassAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type :=
  Graph.BlockedClass.Blocked object.vertexCount object.edgeCount data.threshold
    data.windowOrder data.LengthOK (blockedWindowLabels data object)

/-- The paper's a-priori graph class at node `[170]`: labelled skeletons with
the fixed order, edge count, and minimum-degree threshold, before imposing the
successive blocked barrier tests. -/
@[reducible] noncomputable def blockedAprioriClassAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type :=
  Graph.BlockedClass.NearCubicSkeleton object.vertexCount object.edgeCount
    data.threshold

/-- The exposure coordinates of `lem:blocked-graphs-compress`: one per packed
window, separated dyadic scale, and registered barrier `(a,b)`.  Keeping the
barrier row in the coordinate is essential: node `[172]` must retain the first
specific barrier whose conditional fibre fails. -/
@[reducible] noncomputable def blockedCoordinate (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type :=
  Graph.BarrierSystem.Coordinate (blockedWindowLabels data object)
      (data.separatedScaleCount object.vertexCount) ×
    data.windowBarrier.Index

/-- The registered barrier table's own leg pair `(a,b)` of a row. -/
noncomputable def barrierLegs (data : Parameters) :
    data.windowBarrier.Index -> Nat × Nat :=
  fun row =>
    (data.windowBarrier.table.counts.leftLength row,
      data.windowBarrier.table.counts.rightLength row)

/-- The canonical barrier code on the a-priori near-cubic class.  The blocked
class embeds in this class by forgetting only its blockedness proof. -/
noncomputable def blockedAprioriBarrierCode (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    blockedAprioriClassAt data object ->
      Finset (Sym2 (Fin object.vertexCount)) ×
        (blockedCoordinate data object ->
          Option (Graph.WindowCurvature.Label data.windowOrder ×
            Graph.WindowCurvature.Label data.windowOrder ×
              Graph.WindowCurvature.Label data.windowOrder)) :=
  fun member => by
    let encoded := Graph.BarrierSystem.code data.windowOrder
      (blockedWindowLabels data object)
      (data.separatedScaleCount object.vertexCount) (barrierLegs data)
      member.1.1
    exact (encoded.1, fun coordinate => encoded.2 coordinate.1 coordinate.2)

/-- `lem:blocked-graphs-compress`'s encoding map restricted to the blocked
class. -/
noncomputable def blockedBarrierCode (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    blockedClassAt data object ->
      Finset (Sym2 (Fin object.vertexCount)) ×
        (blockedCoordinate data object ->
          Option (Graph.WindowCurvature.Label data.windowOrder ×
            Graph.WindowCurvature.Label data.windowOrder ×
              Graph.WindowCurvature.Label data.windowOrder)) :=
  fun member => blockedAprioriBarrierCode data object member.1

/-- The honest local state carrier at a registered row.  `none` is the one
absent-completion state; a present state consists of three legal curvature
labels satisfying the two arm tests and their composed test. -/
def IsBlockedSurvivingState (data : Parameters)
    (row : data.windowBarrier.Index) :
    Option (Graph.WindowCurvature.Label data.windowOrder ×
      Graph.WindowCurvature.Label data.windowOrder ×
        Graph.WindowCurvature.Label data.windowOrder) → Prop
  | none => True
  | some (source, middle, target) =>
      source ∈ Graph.WindowCurvature.Labels data.windowOrder ∧
      middle ∈ Graph.WindowCurvature.Labels data.windowOrder ∧
      target ∈ Graph.WindowCurvature.Labels data.windowOrder ∧
      Graph.WindowCurvature.Safe
        (data.windowBarrier.table.counts.leftLength row) source middle ∧
      Graph.WindowCurvature.Safe
        (data.windowBarrier.table.counts.rightLength row) middle target ∧
      Graph.WindowCurvature.Safe
        (data.windowBarrier.table.counts.leftLength row +
          data.windowBarrier.table.counts.rightLength row) source target

/-- The manuscript's surviving count `F_{a,b}` at one registered barrier row.
An absent completion is not charged as a successful barrier state: if its
graph fibre prevents this ratio, node `[170]` routes that first failure to
`[172]`. -/
def blockedSurvivingCountAt (data : Parameters)
    (row : data.windowBarrier.Index) : Nat :=
  data.windowBarrier.table.counts.storedFlat row

/-- The manuscript's a-priori count `W_{a,b}` at one registered barrier row. -/
def blockedAprioriCountAt (data : Parameters)
    (row : data.windowBarrier.Index) : Nat :=
  data.windowBarrier.table.counts.storedSafe row

/-- The product of the registered per-row surviving carriers. -/
noncomputable def blockedSurvivingCount (data : Parameters) : Nat := by
  letI := data.windowBarrier.indexFintype
  exact ∏ row, blockedSurvivingCountAt data row

/-- The product of the registered a-priori carriers. -/
noncomputable def blockedAprioriCount (data : Parameters) : Nat := by
  letI := data.windowBarrier.indexFintype
  exact ∏ row, blockedAprioriCountAt data row

/-- **The canonical encoding order of `lem:blocked-graphs-compress`**: scale by
scale from `2^{j₁}` to `2^{j_L}`, window by window, and barrier row by barrier
row.  The scale is the major key and the registered barrier row is the minor
key.  This is the order
`def:barrier-overlap-system` conditions on. -/
noncomputable def blockedEncodingRank (data : Parameters)
    (object : Graph.FiniteObject.{u}) : blockedCoordinate data object -> Nat := by
  letI := data.windowBarrier.indexFintype
  exact fun coordinate =>
    (Fintype.equivFin _ coordinate.2).1 +
      ((Fintype.equivFin _ coordinate.1.1).1 +
        coordinate.1.2.1 *
          Fintype.card {window // window ∈ blockedWindowLabels data object}) *
        Fintype.card data.windowBarrier.Index

theorem blockedEncodingRank_injective (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Function.Injective (blockedEncodingRank data object) := by
  classical
  letI := data.windowBarrier.indexFintype
  rintro ⟨⟨leftWindow, leftScale⟩, leftRow⟩
    ⟨⟨rightWindow, rightScale⟩, rightRow⟩ same
  simp only [blockedEncodingRank] at same
  have leftRowLt : (Fintype.equivFin _ leftRow).1 <
      Fintype.card data.windowBarrier.Index := (Fintype.equivFin _ leftRow).2
  have rightRowLt : (Fintype.equivFin _ rightRow).1 <
      Fintype.card data.windowBarrier.Index := (Fintype.equivFin _ rightRow).2
  have rowPositive : 0 < Fintype.card data.windowBarrier.Index :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) leftRowLt
  have rowModEq := congrArg (· % Fintype.card data.windowBarrier.Index) same
  have restEq := congrArg (· / Fintype.card data.windowBarrier.Index) same
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt leftRowLt,
    Nat.mod_eq_of_lt rightRowLt] at rowModEq
  simp only [Nat.add_mul_div_right _ _ rowPositive,
    Nat.div_eq_of_lt leftRowLt, Nat.div_eq_of_lt rightRowLt,
    Nat.zero_add] at restEq
  have rowEq : leftRow = rightRow :=
    (Fintype.equivFin _).injective (Fin.ext rowModEq)
  have leftWindowLt : (Fintype.equivFin _ leftWindow).1 <
      Fintype.card {window // window ∈ blockedWindowLabels data object} :=
    (Fintype.equivFin _ leftWindow).2
  have rightWindowLt : (Fintype.equivFin _ rightWindow).1 <
      Fintype.card {window // window ∈ blockedWindowLabels data object} :=
    (Fintype.equivFin _ rightWindow).2
  have windowPositive :
      0 < Fintype.card {window // window ∈ blockedWindowLabels data object} :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) leftWindowLt
  have windowModEq := congrArg
    (· % Fintype.card {window // window ∈ blockedWindowLabels data object}) restEq
  have scaleEqRaw := congrArg
    (· / Fintype.card {window // window ∈ blockedWindowLabels data object}) restEq
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt leftWindowLt,
    Nat.mod_eq_of_lt rightWindowLt] at windowModEq
  simp only [Nat.add_mul_div_right _ _ windowPositive,
    Nat.div_eq_of_lt leftWindowLt, Nat.div_eq_of_lt rightWindowLt,
    Nat.zero_add] at scaleEqRaw
  have windowEq : leftWindow = rightWindow :=
    (Fintype.equivFin _).injective (Fin.ext windowModEq)
  have scaleEq : leftScale = rightScale := Fin.ext scaleEqRaw
  rw [windowEq, scaleEq, rowEq]

/-- The a-priori graph fibre at an exposure coordinate: the outside record and
every earlier barrier state are fixed to those of the selected blocked member,
but the current barrier test has not yet been imposed. -/
def BlockedAprioriConditionalFibre (data : Parameters)
    (object : Graph.FiniteObject.{u}) (member₀ : blockedClassAt data object)
    (coordinate : blockedCoordinate data object) :
    Set (blockedAprioriClassAt data object) :=
  {member |
    (blockedAprioriBarrierCode data object member).1 =
        (blockedBarrierCode data object member₀).1 ∧
      ∀ other : blockedCoordinate data object,
        blockedEncodingRank data object other <
            blockedEncodingRank data object coordinate →
          (blockedAprioriBarrierCode data object member).2 other =
            (blockedBarrierCode data object member₀).2 other}

/-- The numerator of the paper's relative conditional-fibre estimate: the same
a-priori graph fibre after imposing the registered surviving test at the
current coordinate. -/
def BlockedSurvivingConditionalFibre (data : Parameters)
    (object : Graph.FiniteObject.{u}) (member₀ : blockedClassAt data object)
    (coordinate : blockedCoordinate data object) :
    Set (blockedAprioriClassAt data object) :=
  {member | member ∈ BlockedAprioriConditionalFibre data object member₀ coordinate ∧
    IsBlockedSurvivingState data coordinate.2
      ((blockedAprioriBarrierCode data object member).2 coordinate)}

/-- The denominator-cleared `F_{a,b}/W_{a,b}` estimate at one exposure
coordinate, uniformly over every outside record and earlier prefix reached by a
blocked member. -/
def BlockedRelativeFibreBoundAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (coordinate : blockedCoordinate data object) : Prop :=
  ∀ member₀ : blockedClassAt data object,
    blockedAprioriCountAt data coordinate.2 *
        Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ≤
      blockedSurvivingCountAt data coordinate.2 *
        Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate)

/-- The unconditional conditional-state-fibre bound supplied by the certified
flat-state carrier.  The extra `1` is the distinguished `none` state recording
absence of a completion; `F_{a,b}` itself counts only successful flat states.
This strengthens the ledger without replacing the paper's separate `F/W`
graph-fibre dichotomy. -/
def BlockedStateFibreBoundAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (coordinate : blockedCoordinate data object) : Prop :=
  ∀ member₀ : blockedClassAt data object,
    Nat.card (Graph.BarrierSystem.ConditionalFibre
      (blockedBarrierCode data object) (blockedEncodingRank data object)
      member₀ coordinate) ≤ blockedSurvivingCountAt data coordinate.2 + 1

/-- Imposing the current surviving-state test only shrinks the corresponding
a-priori graph fibre. -/
def BlockedGraphFibreMonotonicityAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (coordinate : blockedCoordinate data object) : Prop :=
  ∀ member₀ : blockedClassAt data object,
    Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate) ≤
      Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate)

/-- **`lem:scale-additivity`, node `[170]`.**  Blockedness makes the selected
member's state a surviving state, and at every exposure coordinate the
surviving a-priori graph fibre has relative size at most
`F_{a,b}/W_{a,b}`.  The ratio is cleared of division, so both graph
multiplicities and the `W_{a,b}` denominator are retained. -/
def BlockedScaleAdditivityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∀ (member : blockedClassAt data object)
  (coordinate : blockedCoordinate data object),
    IsBlockedSurvivingState data coordinate.2
      ((blockedBarrierCode data object member).2 coordinate)) ∧
  ∀ coordinate : blockedCoordinate data object,
    BlockedStateFibreBoundAt data object coordinate ∧
      BlockedGraphFibreMonotonicityAt data object coordinate ∧
        BlockedRelativeFibreBoundAt data object coordinate

/-- The literal negative arm of node `[170]`: the first exposure coordinate at
which some fixed outside record and earlier prefix violates the cleared
`F_{a,b}/W_{a,b}` bound, together with the two unconditional local fibre facts
also retained by the positive arm. -/
def BlockedBarrierFailureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∀ coordinate : blockedCoordinate data object,
    BlockedStateFibreBoundAt data object coordinate ∧
      BlockedGraphFibreMonotonicityAt data object coordinate) ∧
  ∃ coordinate : blockedCoordinate data object,
    (∀ other : blockedCoordinate data object,
      blockedEncodingRank data object other <
          blockedEncodingRank data object coordinate →
        BlockedRelativeFibreBoundAt data object other) ∧
    ∃ member₀ : blockedClassAt data object,
      blockedSurvivingCountAt data coordinate.2 *
          Nat.card (BlockedAprioriConditionalFibre data object member₀ coordinate) <
        blockedAprioriCountAt data coordinate.2 *
          Nat.card (BlockedSurvivingConditionalFibre data object member₀ coordinate)

/-- The external-stub count of an ambient baseline-degree window.  For the
Erdős presentation this evaluates to `15`; no numerical value is written into
the strategy. -/
def coldExternalStubCount (data : Parameters) : Nat :=
  data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)

/-- The manuscript's restricted branch-excess of one ambient-cubic window:
the `windowOrder - 2` interior stubs after the two absorbed corridor ends are
removed.  At the registered presentation this evaluates to `9`; no numerical
value is written into the strategy. -/
def coldInteriorBranchExcess (data : Parameters) : Nat :=
  Graph.ColdCorridor.branchExcessOf (data.windowOrder - 2)

/-- The exact finite bit rate used by the near-cubic density comparison. -/
def coldWindowBitRate (data : Parameters) (object : Graph.FiniteObject.{u}) : Nat :=
  2 * (data.windowRate * data.separatedScaleCount object.vertexCount)

/-- The exact finite skeleton allowance; its two summands are the baseline
degree mass and the registered sublinear surplus threshold. -/
def coldSkeletonAllowance (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  (Graph.dyadicScaleCount object + 1) *
    (data.threshold * object.vertexCount +
      data.surplusThreshold object.vertexCount)

/-- **`prop:negative-net-charge`'s large-budget net-deficiency comparison, exact,
at the fixed maximal packing.**  With `p = |𝒫|` and `|R| = n − order·p`, this is
`discharge·(δ·order·p + T(n)) < discharge·2(order−1)·p + |R|`, the strict cap node
`[56]` hands to `[57]`--`[62]`; at the manuscript's values it reads
`4·def⁺(R) < |R|` up to the exact `T(n)` allowance, i.e. `τ(θ) < 1/4`. -/
def DenseDeficiencyBelowStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  data.dischargeScale *
      (data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) +
        data.spineScale * Core.ceilSqrt object.vertexCount) <
    data.dischargeScale *
        (2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card) +
      (object.vertexCount - data.windowOrder * (canonicalWindowPacking data object).card)

/-- **Node `[146]`, `θ < 1/78`, in the exact form the route-8 carrier collision
consumes.**  `def:cold-window-ledger`'s `τ(θ) < 3/13` is the private-carrier
rate of `rem:route8-carrier-margin` read on the near-cubic spine with its
`o(|R|)` allowances made explicit: with `stubs = δ·order − 2(order−1)` external
stubs per packed window, `|∂R| ≤ stubs·p + σ_W ≤ stubs·p + T(n)`, `|R| = n −
order·p`, and the Type B bridge mass `F·s·T(n)` of `prop:typeB-bridge-sublinear`
on the ambient side,
`(δ·s + 1)·(stubs·p + T(n)) + δ·F·s·T(n) < δ·(n − order·p)`;
at the manuscript's `δ = 3`, `s = 4`, `order = 13` this is `13·(15p + o(n)) <
3·|R| − o(n)`, i.e. `θ < 1/78` up to the `o(1)`. -/
def ColdRoute8BelowStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (data.threshold * data.dischargeScale + 1) *
      (coldExternalStubCount data * (canonicalWindowPacking data object).card +
        data.surplusThreshold object.vertexCount) +
    data.threshold * (data.bridgeMassFactor * data.dischargeScale *
      data.surplusThreshold object.vertexCount) <
  data.threshold *
    (object.vertexCount - data.windowOrder * (canonicalWindowPacking data object).card)

def ColdRoute8AtOrAboveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ ColdRoute8BelowStatement data object

def ColdHotEntropyOverflowStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  coldSkeletonAllowance data object <
    coldWindowBitRate data object * (canonicalHotWindows data object).card

def ColdHotEntropyCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  coldWindowBitRate data object * (canonicalHotWindows data object).card ≤
    coldSkeletonAllowance data object

/-- `lem:hot-failure-cold-mass`, with logarithms and division cleared. -/
def ColdMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  coldWindowBitRate data object * (canonicalWindowPacking data object).card ≤
    coldWindowBitRate data object * (canonicalColdWindows data object).card +
      coldSkeletonAllowance data object

/-- A cold window is ambient-baseline exactly when every one of its vertices
has the registered baseline degree. -/
def AmbientCubicWindow (data : Parameters) (object : Graph.FiniteObject.{u})
    (window : Finset object.Vertex) : Prop :=
  ∀ vertex ∈ window, object.degree vertex = data.threshold

/-- `X_cold`: the union of the ambient-cubic cold windows of the fixed
packing, "with their internal path edges retained". -/
noncomputable def coldAmbientCubicSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex := by
  classical
  exact ((canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)).biUnion id

/-- The deleted support used by the paper's return corridors in the dense
pass.  It is the union of the fixed maximal packing, so its outside graph is
literally the normalized remainder `R = G - W`.  The selected entries are
still the branch-excess half-edges of the ambient-cubic cold subfamily. -/
noncomputable def coldCorridorWindows (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex :=
  Graph.ColdCorridor.windowsOf object (canonicalWindowPacking data object)

/-- `def:surviving-cold-branch`'s `o(n)` assertion in exact finite form: the
non-ambient-cubic loss is charged injectively to degree surplus. -/
noncomputable def ColdAmbientCubicStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  exact cold.card ≤ cubic.card + object.degreeSurplus data.threshold ∧
    object.degreeSurplus data.threshold ≤
      data.surplusThreshold object.vertexCount

/-- `lem:cold-window-stub-excess`, subtraction-free and specialized to the
canonical cold family. -/
noncomputable def ColdStubExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let perWindow := coldInteriorBranchExcess data
  exact perWindow * cold.card ≤
    perWindow * cubic.card + perWindow * object.degreeSurplus data.threshold

/-- Node `[153]`, the exact finite dichotomy behind `lem:cold-germ-extraction`'s
"positive for all sufficiently large `n`": the selected branch-excess mass of the
cold family exceeds the two `o(n)` slacks: `perWindow·σ(G)` for the
non-ambient-cubic windows and `(threshold+1)·B_cold·σ(G)` for candidate
incidences charged to an oriented high-to-subcubic edge. -/
noncomputable def ColdMassLinearStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let perWindow := coldInteriorBranchExcess data
  exact (perWindow + (data.threshold + 1) *
      Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
        object.degreeSurplus data.threshold < perWindow * cold.card

/-- The complementary arm of node `[153]`: the cold mass is within the two
slacks, `C ≤ 2σ(G)` after cancelling the positive per-window excess. -/
noncomputable def ColdMassBoundedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cold := canonicalColdWindows data object
  let perWindow := coldInteriorBranchExcess data
  exact perWindow * cold.card ≤
    (perWindow + (data.threshold + 1) *
      Graph.ColdCorridor.overlapBound data.threshold data.coldSignature) *
        object.degreeSurplus data.threshold

/-- Every selected branch-excess half-edge of the ambient-cubic cold family.
This is the paper's counting index `𝒜_br`; it includes both stubs entering
the outside graph and direct cross-window stubs. -/
noncomputable def ColdSelectedHalfEdge (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type u := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  exact {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic}

noncomputable instance coldSelectedHalfEdgeFintype (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Fintype (ColdSelectedHalfEdge data object) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  unfold ColdSelectedHalfEdge
  infer_instance

/-- The selected branch-excess half-edge occurrences that enter the outside
graph and therefore own a literal return corridor. -/
noncomputable def ColdEligibleHalfEdge (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type u := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  let windows := coldCorridorWindows data object
  exact {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∉ windows}

/-- The paper's selected-half-edge occurrence set is finite because it is a
subtype of the finite ordered-pair set of the current finite object.  Exposing
this instance does not add data to the proof: it only lets `Finset.univ` range
over the literal occurrence index above. -/
noncomputable instance coldEligibleHalfEdgeFintype (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Fintype (ColdEligibleHalfEdge data object) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  unfold ColdEligibleHalfEdge
  infer_instance

/-- A selected repaired branch-excess incidence whose other endpoint is
already in the packed-window union.  In the contracted cold skeleton this is
the immediate terminal-corridor case. -/
noncomputable def ColdCrossWindowHalfEdge (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type u := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  let windows := coldCorridorWindows data object
  exact {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic ∧
      stub.2 ∈ windows}

noncomputable instance coldCrossWindowHalfEdgeFintype (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Fintype (ColdCrossWindowHalfEdge data object) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  unfold ColdCrossWindowHalfEdge
  infer_instance

/-- The complete occurrence index of the repaired cold extraction: an actual
outside return corridor, or an immediate cross-window terminal exchange. -/
abbrev ColdGermOccurrence (data : Parameters)
    (object : Graph.FiniteObject.{u}) :=
  ColdEligibleHalfEdge data object ⊕ ColdCrossWindowHalfEdge data object

noncomputable def ColdGermOccurrence.stub {data : Parameters}
    {object : Graph.FiniteObject.{u}} :
    ColdGermOccurrence data object → object.Vertex × object.Vertex
  | .inl epsilon => epsilon.1
  | .inr epsilon => epsilon.1

/-- The literal retained datum of `def:cold-corridor-first-failure`.

For every selected branch-excess half-edge that actually enters the outside
graph, the proposition retains the paper's actual outside component, return
corridor, declared presentation, and its canonical terminal-or-first-repeat
`(F5)` configuration.  The mathematical payload is the framework theorem
`Corridor.FirstFailureGermWitness`: in particular the repeated arm retains
`right ≤ Q_cold`, the first repeated state, the exact interval support, the
canonical cut-state representative, equality of every supported generated
reading, and the complete record read at both equal-state endpoints.

Graph realization of the second representative is deliberately not required
here.  The manuscript first separates canonical replacement pieces from
genuine second strands at node `[163]`; demanding realization at `[153]` would
silently discard that canonical-replacement arm. -/
noncomputable def ColdCorridorStateStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let packing := canonicalWindowPacking data object
  let windows := coldCorridorWindows data object
  let Eligible := ColdEligibleHalfEdge data object
  exact ∃ incidence : Eligible →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object,
    ∃ componentAt : Eligible → Finset object.Vertex,
      ∃ corridorAt : (epsilon : Eligible) →
          Graph.ColdCorridor.Corridor object windows (componentAt epsilon),
        ∃ presentationAt : Eligible →
            Graph.ColdCorridor.Presentation data.coldSignature object,
          ∃ indexAt : (epsilon : Eligible) →
              (corridorAt epsilon).Segment → (presentationAt epsilon).Segment,
    (∀ epsilon : Eligible,
      let germ := incidence epsilon
      let component := componentAt epsilon
      let corridor := corridorAt epsilon
      let presentation := presentationAt epsilon
      let index := indexAt epsilon
      Graph.ColdCorridor.IsOutsideComponent object windows component ∧
          corridor.entryStub = (epsilon.1.2, epsilon.1.1) ∧
          Function.Injective index ∧
          corridor.FirstFailureGermWitness
            (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
            (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
            presentation index germ) ∧
    (∀ epsilon : Eligible, ∀ segment : (corridorAt epsilon).Segment,
      ((presentationAt epsilon).activeInterface (indexAt epsilon segment)).card ≤
        Graph.ColdCorridor.interfaceWidth data.windowOrder) ∧
    (∀ epsilon : ColdSelectedHalfEdge data object, epsilon.1.2 ∈ windows →
      ∃ sourceWindow ∈ cubic, ∃ targetWindow ∈ packing,
        epsilon.1.1 ∈ sourceWindow ∧ epsilon.1.2 ∈ targetWindow ∧
          object.graph.Adj epsilon.1.1 epsilon.1.2) ∧
    (∀ epsilon : Eligible,
      componentAt epsilon ⊆
        object.remainderSupport (canonicalWindowPacking data object)) ∧
    (∀ epsilon : Eligible, ∀ vertex,
      vertex ∈ (corridorAt epsilon).inside.1.support.map (fun inner => inner.1) →
        vertex ∈ object.remainderSupport (canonicalWindowPacking data object)) ∧
    ∃ crossIncidence : ColdCrossWindowHalfEdge data object →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object,
      ∀ epsilon : ColdCrossWindowHalfEdge data object,
        (crossIncidence epsilon).support = {epsilon.1.1, epsilon.1.2}

/-- The exact F4 support predicate named upstream of the cold first-failure
owner: declared decorated Type-B envelope cores or route-8 response supports
of the current object. -/
noncomputable def ColdDeclaredHandoffSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  exact
    (∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
        (fun vertex => data.threshold < object.degree vertex)
        (fun _centre _first _second =>
          Graph.WindowLabelCollision.LabelCollision object
            data.windowOrder data.LengthOK packing),
      envelope.core = support ∧ envelope.decorations.Nonempty) ∨
    ∃ component ∈ object.canonicalPieces remainder,
      object.pieceSupport remainder component = support ∧
        object.NegativeNetCharge support data.threshold data.dischargeScale ∧
        object.ambientSurplus support data.threshold = 0 ∧
        Graph.Route8Deficit.SilentFirst object support data.threshold
          data.dischargeScale ∧
        ∀ receiver : object.Vertex,
          receiver ∈ Graph.VisibleEntry.saturatedReceivers object support
              data.threshold data.dischargeScale →
            ∀ load ∈ Graph.VisibleEntry.silentExcess object support
                data.threshold data.dischargeScale receiver,
              Graph.Route8.TraceBasin.Route8Entry object support data.threshold
                  data.LengthOK receiver load ∧
                ¬ ∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) support
                    data.threshold data.dischargeScale receiver ∅,
                  witness.load = load

/-- The surviving cold residual's F4 registry.  Every Type-B or route-8
handoff has already left this residual along its paper-prescribed ledger edge,
so the registry read by the first-failure row is exactly empty. -/
noncomputable def ColdDeclaredHandoffLedgerStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ Handoff : Finset object.Vertex → Prop,
    ∀ support, ¬ Handoff support

set_option maxHeartbeats 800000 in
/-- Clause (F1) at one segment of the retained cold corridor. -/
noncomputable def ColdFirstFailureCycleAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (segment : corridor.Segment) : Prop :=
  ∃ windowSupport ∈ canonicalWindowPacking data object,
    ∃ window : Graph.ColdCorridor.Window object data.windowOrder,
      (∀ vertex, vertex ∈ windowSupport ↔
        ∃ position, window.place position = vertex) ∧
      corridor.FirstFailureCycle window data.LengthOK segment

/-- Clause (F2) at one segment of the retained cold corridor. -/
noncomputable def ColdFirstFailureDefectAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (segment : corridor.Segment) : Prop :=
  ∃ left : corridor.Segment,
    left.1 < segment.1 ∧
      Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation
        index (Graph.HasCycleWithLength data.LengthOK)
        (fun stage => corridor.prefixSupport stage.1) left segment

/-- Clause (F3) at one segment of the retained cold corridor. -/
noncomputable def ColdFirstFailureCompressionAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (segment : corridor.Segment) : Prop :=
  ∃ failure : Graph.ColdCorridor.Corridor.FirstFailureCompression corridor
      presentation index (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK)
      (fun stage => corridor.prefixSupport stage.1),
    failure.stage = segment

/-- Clause (F4) at one segment, against the exact predicate registered by the
incoming handoff ledger. -/
def ColdFirstFailureHandoffAt (object : Graph.FiniteObject.{u})
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (Handoff : Finset object.Vertex → Prop) (segment : corridor.Segment) : Prop :=
  Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff segment

/-- Clause (F5) at one segment of the retained cold corridor. -/
noncomputable def ColdFirstFailureGermAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (segment : corridor.Segment) : Prop :=
  (corridor.TerminalCorridor data.coldSignature ∧
      germ.support = corridor.prefixSupport corridor.statesRead ∧
      (let terminal : corridor.Segment :=
        ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
       germ.record = corridor.recordAt presentation index terminal) ∧
      segment.1 = corridor.inside.1.length) ∨
    ∃ left right : corridor.Segment,
      right.1 ≤ Graph.ColdCorridor.stateBound data.coldSignature ∧
      left.1 < right.1 ∧
      presentation.state (index left) = presentation.state (index right) ∧
      (∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
        presentation.support (index left) coordinate ⊆
            ↑(presentation.activeInterface (index left)) →
          presentation.reading (index left) coordinate =
            presentation.reading (index right) coordinate) ∧
      (∀ earlierLeft earlierRight : corridor.Segment,
        earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
          presentation.state (index earlierLeft) ≠
            presentation.state (index earlierRight)) ∧
      germ.support = corridor.intervalSupport left right ∧
      germ.record = corridor.recordAt presentation index left ∧
      germ.record = corridor.recordAt presentation index right ∧
      segment = right

/-- The literal alternatives (F1)--(F5), in manuscript order, at one retained
corridor segment. -/
inductive ColdFirstFailureEvent (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (Handoff : Finset object.Vertex → Prop) (segment : corridor.Segment) : Prop where
  | cycle (witness : ColdFirstFailureCycleAt data object corridor segment)
  | defect (witness : ColdFirstFailureDefectAt data object corridor presentation
      index segment)
  | compression (witness : ColdFirstFailureCompressionAt data object corridor
      presentation index segment)
  | handoff (witness : ColdFirstFailureHandoffAt object corridor Handoff segment)
  | germ (witness : ColdFirstFailureGermAt data object corridor presentation
      index germ segment)

/-- `def:cold-corridor-first-failure`'s literal occurrence-level minimum.

The retained state supplies the actual corridor, presentation, and structural
F5 germ.  At each corridor segment the five predicates below are exactly the
paper's F1--F5 alternatives: a completion through a placed packed window, a
same-state target-response defect, a proper target-complete compression, entry
into a declared Type B or route-8 support, or the terminal/least-repeat germ
endpoint.  The published segment satisfies one alternative and no strictly
earlier segment satisfies any alternative. -/
structure ColdFirstFailureOccurrenceData (data : Parameters)
    (object : Graph.FiniteObject.{u}) where
  Handoff : Finset object.Vertex → Prop
  handoffAbsent : ∀ support, ¬ Handoff support
  state : ColdCorridorStateStatement data object
  occurs :
    letI : FinEnum object.Vertex := object.vertices
    let Eligible := ColdEligibleHalfEdge data object
    let incidence : Eligible →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object :=
      Classical.choose state
    let stateOne := Classical.choose_spec state
    let componentAt := Classical.choose stateOne
    let stateTwo := Classical.choose_spec stateOne
    let corridorAt := Classical.choose stateTwo
    let stateTail := Classical.choose_spec stateTwo
    let presentationAt := Classical.choose stateTail
    let indexAt := Classical.choose (Classical.choose_spec stateTail)
    ∀ epsilon : Eligible,
      let germ := incidence epsilon
      let corridor := corridorAt epsilon
      let presentation := presentationAt epsilon
      let index := indexAt epsilon
      ∃ first : corridor.Segment,
        ColdFirstFailureEvent data object corridor presentation index germ Handoff
            first ∧
          ∀ earlier : corridor.Segment, earlier.1 < first.1 →
            ¬ ColdFirstFailureEvent data object corridor presentation index germ
              Handoff earlier

/-- The retained occurrence payload is inhabited.  `Nonempty` keeps the ledger
value proof-irrelevant while the sealed owner may still store the exact
registered handoff predicate and selected minimum. -/
def ColdFirstFailureOccurrenceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Nonempty (ColdFirstFailureOccurrenceData data object)

/-! The following projections give the retained occurrence one stable semantic
shape.  They are definitions of the ledger value, not additional facts: every
projection is obtained from `occurrence.state`.  Naming them prevents consumers
from repeatedly normalizing the same nested chain of `Classical.choose` terms. -/
noncomputable def coldOccurrenceIncidence (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object) :=
  Classical.choose occurrence.state

noncomputable def coldOccurrenceComponentAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object) :=
  Classical.choose (Classical.choose_spec occurrence.state)

noncomputable def coldOccurrenceCorridorAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object) :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec occurrence.state))

noncomputable def coldOccurrencePresentationAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object) :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec occurrence.state)))

noncomputable def coldOccurrenceIndexAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object) :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec occurrence.state))))

noncomputable def coldOccurrenceStateFacts (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec occurrence.state))))).1

structure ColdFirstFailureGermOccurrence (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object) : Prop where
  holds :
    let germ := coldOccurrenceIncidence data object occurrence epsilon
    let corridor := coldOccurrenceCorridorAt data object occurrence epsilon
    let presentation := coldOccurrencePresentationAt data object occurrence epsilon
    let index := coldOccurrenceIndexAt data object occurrence epsilon
    ∃ first : corridor.Segment,
    ColdFirstFailureGermAt data object corridor presentation index germ first ∧
      ∀ earlier : corridor.Segment, earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object corridor presentation index germ
          occurrence.Handoff earlier

noncomputable def ColdFirstFailureHandoffOccurrence (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object) : Prop := by
  let germ := coldOccurrenceIncidence data object occurrence epsilon
  let corridor := coldOccurrenceCorridorAt data object occurrence epsilon
  let presentation := coldOccurrencePresentationAt data object occurrence epsilon
  let index := coldOccurrenceIndexAt data object occurrence epsilon
  exact ∃ first : corridor.Segment,
    ColdFirstFailureHandoffAt object corridor occurrence.Handoff first ∧
      ∀ earlier : corridor.Segment, earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object corridor presentation index germ
          occurrence.Handoff earlier

/-- The exact corridor consequence produced at node `[162]`: the retained
corridor state from the incoming ledger, together with terminality of every
corridor in that state. -/
noncomputable def DenseColdCorridorsTerminalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Eligible := ColdEligibleHalfEdge data object
  exact ∃ state : ColdCorridorStateStatement data object,
    let stateOne := Classical.choose_spec state
    let componentAt := Classical.choose stateOne
    let stateTwo := Classical.choose_spec stateOne
    let corridorAt := Classical.choose stateTwo
    ∀ epsilon : Eligible,
      Graph.ColdCorridor.Corridor.TerminalCorridor
        (corridorAt epsilon) data.coldSignature

/-- `def:cold-corridor-first-failure`, at every selected half-edge owned by the
current cold family.

The first conjunct retains the componentwise corridor theorem.  The second is
the exact selected-stub partition that must precede first-failure routing.  A
selected stub either has its foot in the outside graph, in which case the fact
retains its canonical outside component and unique lexicographically selected
return corridor, or its foot lies in another ambient-cubic cold window.  The
latter is the paper's cross-window incidence and is retained explicitly; it is
not silently removed by restricting the domain of the incidence map. -/
noncomputable def ColdReturnCorridorsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  let windows := coldCorridorWindows data object
  let Selected := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic}
  let selected := Graph.ColdCorridor.allSelectedStubs object cubic
  exact
    (∀ component : Finset object.Vertex,
      Graph.ColdCorridor.IsOutsideComponent object windows component →
      ∀ entry : Fin (Graph.ColdCorridor.boundaryStubs object windows
          component).length,
        ∃ corridor : Graph.ColdCorridor.Corridor object windows component,
          corridor.entry = entry) ∧
    (∀ epsilon : Selected,
      (∃ (outsideFoot : epsilon.1.2 ∉ windows)
          (component : Finset object.Vertex)
          (corridor : Graph.ColdCorridor.Corridor object windows component),
          Graph.ColdCorridor.IsOutsideComponent object windows component ∧
            corridor.entryStub = (epsilon.1.2, epsilon.1.1)) ∨
        epsilon.1.2 ∈ windows) ∧
    selected.card =
      (selected.filter fun stub => stub.2 ∉ windows).card +
        (selected.filter fun stub => stub.2 ∈ windows).card

/-- The manuscript's surviving first-failure classification.  F1--F3 are
excluded by their ledger facts and every F4 support has already left along its
handoff edge, so every occurrence remaining on this residual is the actual
terminal/least-repeat F5 germ. -/
structure ColdSurvivingFirstFailureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop where
  holds : ∃ occurrence : ColdFirstFailureOccurrenceData data object,
    ∀ epsilon : ColdEligibleHalfEdge data object,
      ColdFirstFailureGermOccurrence data object occurrence epsilon

/-- `lem:cold-corridor-first-failure` on the current surviving residual.

The retained state and its literal least F1--F5 occurrence are paired with the
incoming global sparse-exit exclusion and the proved (F4)-or-(F5)
classification.  Consumers therefore use exact ledger facts instead of
reopening or recreating the corridor presentation. -/
structure ColdFailureRoutingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop where
  sparseSurvivor :
    Graph.SurvivesSparseExits
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
  surviving : ColdSurvivingFirstFailureStatement data object

/-- Canonical classified first-failure data projected from the retained routing
fact.  This is a read-only projection of the ExactLedger payload. -/
@[reducible] noncomputable def coldRoutedClassified (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    ColdFirstFailureOccurrenceData data object :=
  Classical.choose routing.surviving.holds

/-- Canonical repeated-state trace endpoint projected from the retained routing
fact. -/
@[reducible] noncomputable def coldRoutedTraceEnd (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object) : Nat := by
  let classified := coldRoutedClassified data object routing
  let outsideIncidence := coldOccurrenceIncidence data object classified
  let corridorAt := coldOccurrenceCorridorAt data object classified
  let presentationAt := coldOccurrencePresentationAt data object classified
  let indexAt := coldOccurrenceIndexAt data object classified
  let stateFacts := coldOccurrenceStateFacts data object classified
  exact Classical.choose
    (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      (corridorAt epsilon) (presentationAt epsilon) (indexAt epsilon)
      (outsideIncidence epsilon) (stateFacts epsilon).2.2.2)

/-- Canonical immediate exchange germs for selected stubs whose target remains
inside the cold-window union. -/
@[reducible] noncomputable def coldRoutedCrossIncidence (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    ColdCrossWindowHalfEdge data object →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object := by
  let classified := coldRoutedClassified data object routing
  let state := classified.state
  let stateOne := Classical.choose_spec state
  let stateTwo := Classical.choose_spec (Classical.choose_spec stateOne)
  let stateBundle := Classical.choose_spec (Classical.choose_spec stateTwo)
  exact Classical.choose stateBundle.2.2.2.2.2

/-- The canonical occurrence-to-germ map read from the retained routing fact. -/
@[reducible] noncomputable def coldRoutedOccurrenceIncidence (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    ColdGermOccurrence data object →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
  | .inl epsilon =>
      coldOccurrenceIncidence data object
        (coldRoutedClassified data object routing) epsilon
  | .inr epsilon => coldRoutedCrossIncidence data object routing epsilon

/-- The literal candidate set determined by the retained first-failure routing
fact. -/
@[reducible] noncomputable def coldRoutedCandidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    Finset (ColdGermOccurrence data object) := by
  classical
  let classified := coldRoutedClassified data object routing
  let corridorAt := coldOccurrenceCorridorAt data object classified
  exact (Finset.univ : Finset (ColdGermOccurrence data object)).filter
    fun occurrence =>
      match occurrence with
      | .inl epsilon =>
          ColdFirstFailureGermOccurrence data object classified epsilon ∧
            ∀ vertex ∈ (corridorAt epsilon).prefixSupport
                (coldRoutedTraceEnd data object routing epsilon),
              object.degree vertex ≤ data.threshold
      | .inr epsilon =>
          ∀ vertex ∈ (coldRoutedCrossIncidence data object routing epsilon).support,
            object.degree vertex ≤ data.threshold

/-- Node `[175]`, `lem:absorbed-germ-fan-data`, on the literal occurrence
family retained by node `[153]`.  An outside occurrence is either already in
that exact candidate set, or its bounded first-failure prefix has the least
high vertex used by node `[177]`. -/
noncomputable def AbsorbedGermSplitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Eligible := ColdEligibleHalfEdge data object
  exact ∃ routing : ColdFailureRoutingStatement data object,
  let classified := coldRoutedClassified data object routing
  let corridorAt := coldOccurrenceCorridorAt data object classified
  let traceEnd := coldRoutedTraceEnd data object routing
  let candidates := coldRoutedCandidates data object routing
  ∀ epsilon : Eligible,
    (Sum.inl epsilon ∈ candidates) ∨
      ∃ first : (corridorAt epsilon).Segment,
        first.1 ≤ traceEnd epsilon ∧
          data.threshold < object.degree ((corridorAt epsilon).head first) ∧
          (∀ earlier : (corridorAt epsilon).Segment, earlier.1 < first.1 →
            object.degree ((corridorAt epsilon).head earlier) ≤ data.threshold) ∧
          ∀ neighbour : object.Vertex,
            object.graph.Adj ((corridorAt epsilon).head first) neighbour →
              object.degree neighbour = data.threshold

/-- Node `[175]`, the nonempty case-(i) class.  This is the exact candidate
set already owned by node `[153]`; `[175]` only decides its positivity. -/
noncomputable def ColdPositiveGermStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact ∃ routing : ColdFailureRoutingStatement data object,
    0 < (coldRoutedCandidates data object routing).card

/-- The literal occurrence accounting available at node `[153]`: actual F5
outside-corridor candidates together with immediate terminal exchanges for
cross-window incidences, their disjoint extracted subfamily, and every omitted
occurrence charged at its first high-to-subcubic edge. -/
noncomputable def ColdGermFamilyWitness (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (incidence : ColdGermOccurrence data object →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
    (candidates disjointFamily : Finset (ColdGermOccurrence data object))
    (corridorLoss : Nat) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let Occurrence := ColdGermOccurrence data object
  exact
    let occurrenceIncidence := coldRoutedOccurrenceIncidence data object routing
    let routedCandidates := coldRoutedCandidates data object routing
    incidence = occurrenceIncidence ∧
      candidates = routedCandidates ∧
      Graph.ColdCorridor.CandidateGermOccurrenceFamily data.coldSignature
          data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object incidence candidates ∧
        Graph.ColdCorridor.ExtractedGermOccurrenceFamily data.coldSignature
          data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object incidence candidates
          disjointFamily ∧
        (∀ occurrence : Occurrence, occurrence ∉ candidates →
          ∃ charged root : object.Vertex,
            data.threshold < object.degree charged ∧
              object.graph.Adj charged root ∧
              object.degree root ≤ data.threshold ∧
              (ColdGermOccurrence.stub occurrence).1 ∈
                @Graph.SubcubicReach.reach object.Vertex
                  (@FinEnum.instFintype _ object.vertices) object.graph
                  (object.vertexFinset.filter fun current =>
                    object.degree current ≤ data.threshold)
                  root
                  (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                  root) ∧
        (Finset.univ : Finset Occurrence).card =
          candidates.card + corridorLoss ∧
        (Graph.ColdCorridor.allSelectedStubs object cubic).card =
          candidates.card + corridorLoss ∧
        corridorLoss ≤
          (data.threshold + 1) *
            Graph.ColdCorridor.overlapBound data.threshold data.coldSignature *
              object.degreeSurplus data.threshold ∧
        (Graph.ColdCorridor.allSelectedStubs object cubic).card ≤
          disjointFamily.card *
              Graph.ColdCorridor.extractionDenominator data.threshold
                data.coldSignature +
            corridorLoss

/-- `lem:cold-germ-extraction` on the current residual.  The fact retains the
actual F5/immediate-terminal occurrence family, its greedy disjoint extraction,
and the exact first-high loss bound. -/
noncomputable def ColdGermCandidatesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Occurrence := ColdGermOccurrence data object
  exact ∃ (routing : ColdFailureRoutingStatement data object)
      (incidence : Occurrence →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
      (candidates disjointFamily : Finset Occurrence)
      (corridorLoss : Nat),
    ColdGermFamilyWitness data object routing incidence candidates disjointFamily
      corridorLoss

/-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii), with the paper's complete
accounting package.  The retained node-`[153]` witness supplies the exact
candidate/loss identity and the bound
`corridorLoss ≤ (threshold+1)·B_cold·σ(G)`.  Every selected occurrence outside
that same candidate set carries its least high vertex and the node-`[10]`
neighbour-degree conclusion.  Hence mixed families retain both the genuine
case-(i) subfamily and the entire charged case-(ii) complement in one ledger
fact. -/
noncomputable def AbsorbedGermFanDataStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Eligible := ColdEligibleHalfEdge data object
  let Occurrence := ColdGermOccurrence data object
  exact ∃ (routing : ColdFailureRoutingStatement data object)
      (incidence : Occurrence →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
      (candidates disjointFamily : Finset Occurrence)
      (corridorLoss : Nat),
    ColdGermFamilyWitness data object routing incidence candidates disjointFamily
        corridorLoss ∧
    let classified := coldRoutedClassified data object routing
    let corridorAt := coldOccurrenceCorridorAt data object classified
    let traceEnd := coldRoutedTraceEnd data object routing
    ∀ epsilon : Eligible,
      Sum.inl epsilon ∉ coldRoutedCandidates data object routing →
      ∃ first : (corridorAt epsilon).Segment,
        first.1 ≤ traceEnd epsilon ∧
          data.threshold < object.degree ((corridorAt epsilon).head first) ∧
          (∀ earlier : (corridorAt epsilon).Segment, earlier.1 < first.1 →
            object.degree ((corridorAt epsilon).head earlier) ≤ data.threshold) ∧
          ∀ neighbour : object.Vertex,
            object.graph.Adj ((corridorAt epsilon).head first) neighbour →
              object.degree neighbour = data.threshold

/-- The terminal output required from node `[153]` on its linear arm: the exact
disjoint family already published by `ColdGermCandidatesStatement` is
nonempty. -/
noncomputable def ColdGermFamilyPositiveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Occurrence := ColdGermOccurrence data object
  exact ∃ (routing : ColdFailureRoutingStatement data object)
      (incidence : Occurrence →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
      (candidates disjointFamily : Finset Occurrence)
      (corridorLoss : Nat),
    ColdGermFamilyWitness data object routing incidence candidates disjointFamily
        corridorLoss ∧
      0 < disjointFamily.card

/-- One germ occurrence of the literal disjoint family retained by the
incoming `K .coldGermCandidates` fact.  It becomes inhabited only on the later
linear arm.  Downstream cold nodes use this predicate so a neutral or symmetric
germ cannot be fabricated outside the extracted family. -/
noncomputable def ActiveColdGermAtSelectedStubStatement (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (epsilon : ColdGermOccurrence data object) : Prop :=
  by
    classical
    letI : FinEnum object.Vertex := object.vertices
    let Occurrence := ColdGermOccurrence data object
    exact ∃ (routing : ColdFailureRoutingStatement data object)
        (incidence : Occurrence →
          Graph.ColdCorridor.BoundedGerm data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object)
        (candidates disjointFamily : Finset Occurrence)
        (corridorLoss : Nat),
      ColdGermFamilyWitness data object routing incidence candidates disjointFamily
          corridorLoss ∧
        epsilon ∈ disjointFamily ∧ incidence epsilon = germ

noncomputable def ActiveColdGermStatement (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object) : Prop :=
  by
    classical
    letI : FinEnum object.Vertex := object.vertices
    let Occurrence := ColdGermOccurrence data object
    exact ∃ (routing : ColdFailureRoutingStatement data object)
        (incidence : Occurrence →
          Graph.ColdCorridor.BoundedGerm data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object)
        (candidates disjointFamily : Finset Occurrence)
        (corridorLoss : Nat),
      ColdGermFamilyWitness data object routing incidence candidates disjointFamily
          corridorLoss ∧
        ∃ epsilon ∈ disjointFamily, incidence epsilon = germ

/-- `def:cold-skeleton-excess` on the canonical cold family.  The first
conjunct is the paper's exact restricted `9C` interior mass; the second
is the statement that
one selected half-edge is charged at most once at its cold-window endpoint. -/
noncomputable def ColdSelectedBranchExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  let selected := Graph.ColdCorridor.allSelectedStubs object cubic
  exact selected.card = coldInteriorBranchExcess data * cubic.card ∧
    ∀ stub ∈ selected, ∃! window : Finset object.Vertex,
      window ∈ cubic ∧ stub ∈ Graph.ColdCorridor.selectedStubs object window

/-- The exact per-window computation in `lem:cold-window-stub-excess`: every
ambient-baseline member of the canonical cold family has precisely the
presentation-derived external-stub count. -/
noncomputable def ColdAmbientCubicStubExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  exact ∀ window ∈ cubic,
    (Graph.ColdCorridor.externalStubList object window).length =
      coldExternalStubCount data

/-- The exact exclusion of clause F1 on the selected current object. -/
noncomputable def ColdFailureCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (windows component : Finset object.Vertex)
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (order : Nat) (window : Graph.ColdCorridor.Window object order)
    (segment : corridor.Segment),
    ¬ corridor.FirstFailureCycle window data.LengthOK segment

/-- The concrete sparse-exit consequence of clause F2. -/
noncomputable def ColdFailureDefectRoutesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (windows component : Finset object.Vertex)
      (corridor : Graph.ColdCorridor.Corridor object windows component)
      (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
      (index : corridor.Segment → presentation.Segment)
      (left right : corridor.Segment),
    Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation index
        (Graph.HasCycleWithLength data.LengthOK)
        (fun stage => corridor.prefixSupport stage.1) left right →
      Graph.SparseSurplusExit
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object

/-- The context-universality consequence when clause F2 is excluded. -/
noncomputable def ColdFailureDefectEquivalentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (windows component : Finset object.Vertex)
      (corridor : Graph.ColdCorridor.Corridor object windows component)
      (presentation : Graph.ColdCorridor.Presentation data.coldSignature object)
      (index : corridor.Segment → presentation.Segment)
      (left right : corridor.Segment),
    ¬ Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation index
        (Graph.HasCycleWithLength data.LengthOK)
        (fun stage => corridor.prefixSupport stage.1) left right →
      presentation.state (index left) = presentation.state (index right) →
        Graph.Response.ContextEquivalent
          (Graph.HasCycleWithLength data.LengthOK)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
            (corridor.prefixSupport right.1) (corridor.prefixSupport left.1))
          (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
            (corridor.prefixSupport right.1))

/-- The two exact consequences of clause F2 on the current object.  Their
quantified contracts are named separately so the exact-ledger producer can
cache them without repeatedly normalizing either proposition. -/
structure ColdFailureDefectStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop where
  routes : ColdFailureDefectRoutesStatement data object
  equivalent : ColdFailureDefectEquivalentStatement data object

/-- The exact exclusion of clause F3 by uncompressibility. -/
noncomputable def ColdFailureCompressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (windows component : Finset object.Vertex)
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (presentation :
      Graph.ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (support : corridor.Segment → Finset object.Vertex),
    ¬ Graph.ColdCorridor.Corridor.FirstFailureCompression.Occurs corridor
      presentation index (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) support

/-- The concrete first-high subcase of (F4), on the exact corridor state
retained by node `[153]`.  If the bounded prefix is not subcubic, the fact
publishes the least corridor segment whose head is above the registered
baseline and proves that every earlier head is still at the baseline.  This is
the paper's high-degree handoff; it is not an auxiliary envelope or a second
incidence carrier. -/
noncomputable def ColdFirstHighHandoffStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  let windows := Graph.ColdCorridor.windowsOf object cubic
  let Eligible := ColdEligibleHalfEdge data object
  exact ∀ state : ColdCorridorStateStatement data object,
    let incidence : Eligible →
        Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object :=
      Classical.choose state
    let stateOne := Classical.choose_spec state
    let componentAt := Classical.choose stateOne
    let stateTwo := Classical.choose_spec stateOne
    let corridorAt := Classical.choose stateTwo
    let stateTail := Classical.choose_spec stateTwo
    let presentationAt := Classical.choose stateTail
    let indexAt := Classical.choose (Classical.choose_spec stateTail)
    let stateFacts := (Classical.choose_spec
      (Classical.choose_spec stateTail)).1
    let traceEnd := fun epsilon : Eligible => Classical.choose
      (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
        (corridorAt epsilon) (presentationAt epsilon) (indexAt epsilon)
        (incidence epsilon) (stateFacts epsilon).2.2.2)
    ∀ epsilon : Eligible,
      (∀ vertex ∈ (corridorAt epsilon).prefixSupport (traceEnd epsilon),
        object.degree vertex ≤ data.threshold) ∨
      ∃ first : (corridorAt epsilon).Segment,
        first.1 ≤ traceEnd epsilon ∧
          data.threshold < object.degree ((corridorAt epsilon).head first) ∧
          (∀ earlier : (corridorAt epsilon).Segment, earlier.1 < first.1 →
            object.degree ((corridorAt epsilon).head earlier) ≤ data.threshold) ∧
          ∃ root : object.Vertex,
            object.graph.Adj ((corridorAt epsilon).head first) root ∧
              object.degree root ≤ data.threshold ∧
              epsilon.1.1 ∈
                @Graph.SubcubicReach.reach object.Vertex
                  (@FinEnum.instFintype _ object.vertices) object.graph
                  (object.vertexFinset.filter fun current =>
                    object.degree current ≤ data.threshold)
                  root
                  (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                  root

/-- The exchange bound for the same current-residual first-failure routing. -/
def ColdExchangeBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ColdFailureRoutingStatement data object ∧
  ∀ (windows component : Finset object.Vertex)
    (corridor : Graph.ColdCorridor.Corridor object windows component),
    Graph.ColdCorridor.Corridor.TerminalCorridor corridor data.coldSignature →
      corridor.statesRead + Graph.ColdCorridor.interfaceBudget data.coldSignature ≤
        Graph.ColdCorridor.exchangeBound data.coldSignature

attribute [instance] Parameters.boundaryProfileFintype

/-! ## The exit-`(7)` handoff envelope, at the spine's registered data

The three parameters `def:decorated-fan-envelope` is quantified over are fixed
here once, so the node's two arms, its row and its fixture all read the same
predicate.

*The high-degree predicate* is `lem:typeA-cubic-switch-absorption`'s own
conclusion `d_G(z) ≥ 4` at a surviving first separator.  It is recorded through
the registered threshold as `data.threshold < d_G(z)`; the cubic-baseline
identity makes this exactly the manuscript's inequality, rather than a second
hard-coded degree convention.

*The absorbing predicate* is `def:typeB-fan-safe` clause (ii), the label
collision of `lem:labels`: exit `(3)`, which the branch reaching node `[107]`
has already denied and which the row therefore reads rather than restates.

*The two admissibility predicates* are node `[14]`'s hereditary
target-uncompressibility and the `P₁₃`-freeness of the counted core. -/
/-- The registered high-degree set at a surviving first separator:
`lem:typeA-cubic-switch-absorption`. -/
abbrev handoffHighDegree (data : Parameters) (object : Graph.FiniteObject.{u}) :
    object.Vertex → Prop :=
  fun vertex => data.threshold < object.degree vertex

/-- **`def:typeB-fan-safe` clauses (ii)--(v)**, at the registered data.
`lem:typeA-high-degree-handoff` reads them off the exit list: *"Failures of the
other four fan-safe conditions are exactly the label, target-defect,
target-compression, and support-dependence exits already removed before exit (7)"*.
The exit `(3)` label clause is the only local fan predicate.  The denials of
exits `(4)`, `(5)`, and `(6)` are ledger facts in `SelectedNoExitSixWith`, not
secondary route-8 objects smuggled through this predicate. -/
abbrev handoffAbsorbing (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :
    object.Vertex → object.Vertex → object.Vertex → Prop :=
  fun _centre _first _second =>
    Graph.WindowLabelCollision.LabelCollision object data.windowOrder
      data.LengthOK packing

/-- **A decorated handoff fan envelope is produced at a support.**  The test
node `[107]` splits on: `def:decorated-fan-envelope`'s data, with the Type A
support as the counted core and at least one high-degree decoration. -/
def HandoffProduced (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty

/-- Residual C, node `[55]`: `prop:two-budget`'s "in every case the surviving
residual is subsequently passed to the large-budget net-charge analysis" — the
`[53]`-no arm (the joint package fits the skeleton budget) and the low-entropy
arm; the `[53]`-yes arm is the terminal `[54]` on every residual. -/
abbrev LargeBudgetResidual (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (jointPackageDemand data object ≤ Graph.skeletonBudget object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
          data.windowOrder data.threshold
          (object.positiveDeficiency (object.remainderSupport packing)
            data.threshold)
          (object.internalEdgeCount (object.remainderSupport packing))
          (object.remainderSupport packing).card)

/-- A failed extension of an actually realized baseline code has a nonempty
extension side. -/
theorem freeSide_nonempty_of_baseline_realized
    {object : Graph.FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {free : Finset (Finset (object.Vertex × object.Vertex))}
    (realization : Graph.BaselineCodeRealization object family)
    (failure : ¬ 2 ^ (family.card + free.card) ≤
      Graph.skeletonBudget object) :
    free.Nonempty := by
  by_contra empty
  have freeEmpty : free = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
  apply failure
  simpa [freeEmpty] using realization.two_pow_le_skeletonBudget

/-- One exact graph-derived value of a sparse pair-response coordinate.  The
graph layer owns this state because both the dependence lemma and node `[178]`
read the same all-context response; Strategy does not duplicate it. -/
abbrev PairResponseState (data : Parameters) :=
  Graph.SparsePairSkeletonResponse data.LengthOK

/-- **The canonical representative of a germ's corridor piece**
(`def:cold-corridor-first-failure`: "the canonical representative determined by
the repeated cold corridor state"; `def:proper-quotient-representative`): the
`Precedes`-least canonical piece with the corridor piece's boundary-degree
profile, its target response against every outside context, and its
completions' baseline (`Graph/CanonicalRealization`). -/
noncomputable def germCanonicalRepresentative (data : Parameters)
    {object : Graph.FiniteObject.{u}}
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object) :
    Graph.CanonicalPiece germ.atom.interface :=
  Graph.CanonicalPiece.cutStateRepresentative
    (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
    (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant germ.piece

/-- The pointwise content of the paper's neutral equal-length terminal
configuration at node `[163]`.  The marked representative is canonical among
the pieces that preserve the entire retained cut-state *and* the local edge
count.  Equal internal size is recorded separately, so exchanging the two
pieces preserves both coordinates of node `[4]`'s graph-size order. -/
noncomputable def NeutralEqualLengthTerminalConfigurationAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (representative : Graph.CanonicalPiece germ.atom.interface) : Prop := by
  let Reading : Graph.CanonicalPiece germ.atom.interface → Prop :=
    fun candidate =>
      Graph.CanonicalPiece.CutStateReading
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) germ.piece candidate ∧
        (Graph.glue candidate.toPiece germ.atom.outside).edgeCount =
          (Graph.glue germ.piece germ.atom.outside).edgeCount
  exact ActiveColdGermStatement data object germ ∧
    Reading representative ∧
    representative.size = germ.piece.internalVertexCount ∧
    (representative = germ.piece.toCanonical ∨
      (Graph.CanonicalPiece.Precedes representative germ.piece.toCanonical ∧
        RefinedLexicographicallySmaller
          (Graph.glue representative.toPiece germ.atom.outside) object)) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue germ.piece germ.atom.outside)

/-- `def:neutral-equal-length-germ` in ledger form.  Terminality is the exact
incoming F5 fact from `[162]`; the existential retains the marked corridor
occurrence and its marked canonical exchange representative for the decision
at `[163]`. -/
noncomputable def NeutralEqualLengthTerminalConfigurationStatement
    (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  DenseColdCorridorsTerminalStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
      (representative : Graph.CanonicalPiece germ.atom.interface),
      NeutralEqualLengthTerminalConfigurationAt data object germ representative

/-- The finite range used by the manuscript's two-strand kernel census.  At
the registered `P₁₃` window this is `3·13 + 1 = 40`, so the semantic node
invokes exactly `survivors 13 40` without installing an application-owned
numeric field. -/
def twoStrandEnumerationBound (data : Parameters) : Nat :=
  3 * data.windowOrder + 1

/-- The literal graph-realized symmetric-strand witness of nodes
`[163]`--`[168]`, stated over one germ of the incoming extracted family.

`Q` and `E` are neutral and equal-length; `E` is embedded in the ambient graph
as the second internally-disjoint representative.  Its two cut coordinates
attach to one ambient-cubic cold window and each attachment has two distinct
outside stubs.  The retained strand and window paths construct the pair cycle
and both strand/segment cycles used by `Graph.TwoStrand`.  No witness is stored
beside the ledger: the proof-irrelevant configuration is the semantic
proposition of its key. -/
structure GenuineSecondStrandWitness (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (representative : Graph.CanonicalPiece germ.atom.interface)
    (config : Graph.TwoStrand.Configuration) where
  interface_two : germ.atom.interface.vertexCount = 2
  embedding :
    (germ.atom.interface.Vertex ⊕ representative.toPiece.Internal) ↪
      object.Vertex
  boundary_agrees : ∀ boundary : germ.atom.interface.Vertex,
    embedding (.inl boundary) = germ.atom.pieceIntoAmbient (.inl boundary)
  representative_maps : representative.toPiece.graph.map embedding ≤ object.graph
  representative_internal_outside : ∀ internal : representative.toPiece.Internal,
    embedding (.inr internal) ∉ germ.support
  length_eq : config.length = representative.size + 1
  length_le : config.length ≤ twoStrandEnumerationBound data
  gap_eq :
    config.gap = Nat.dist (germ.record.offsets 0).1 (germ.record.offsets 1).1
  gap_lt : config.gap < data.windowOrder
  window : Finset object.Vertex
  window_mem : window ∈ canonicalColdWindows data object
  window_cubic : AmbientCubicWindow data object window
  left : object.Vertex
  right : object.Vertex
  left_mem : left ∈ window
  right_mem : right ∈ window
  attachments_distinct : left ≠ right
  interface_attachments : ∃ x y : germ.atom.interface.Vertex,
    x ≠ y ∧
      germ.atom.pieceIntoAmbient (.inl x) = left ∧
      germ.atom.pieceIntoAmbient (.inl y) = right
  leftFirst : object.Vertex
  leftSecond : object.Vertex
  leftFirst_mem : leftFirst ∈ object.externalNeighbours window left
  leftSecond_mem : leftSecond ∈ object.externalNeighbours window left
  leftStubs_distinct : leftFirst ≠ leftSecond
  rightFirst : object.Vertex
  rightSecond : object.Vertex
  rightFirst_mem : rightFirst ∈ object.externalNeighbours window right
  rightSecond_mem : rightSecond ∈ object.externalNeighbours window right
  rightStubs_distinct : rightFirst ≠ rightSecond
  origin : ColdGermOccurrence data object
  origin_active :
    ActiveColdGermAtSelectedStubStatement data object germ origin
  origin_mem_window :
    (ColdGermOccurrence.stub origin) ∈
      Graph.ColdCorridor.selectedStubs object window
  origin_is_pair_stub :
    ColdGermOccurrence.stub origin = (left, leftFirst) ∨
      ColdGermOccurrence.stub origin = (left, leftSecond) ∨
      ColdGermOccurrence.stub origin = (right, rightFirst) ∨
      ColdGermOccurrence.stub origin = (right, rightSecond)
  firstStrand : object.graph.Walk left right
  secondStrand : object.graph.Walk left right
  windowSegment : object.graph.Walk left right
  firstStrand_isPath : firstStrand.IsPath
  secondStrand_isPath : secondStrand.IsPath
  windowSegment_isPath : windowSegment.IsPath
  strands_internallyDisjoint :
    firstStrand.support.tail.Disjoint secondStrand.reverse.support.tail
  firstSegment_internallyDisjoint :
    firstStrand.support.tail.Disjoint windowSegment.reverse.support.tail
  secondSegment_internallyDisjoint :
    secondStrand.support.tail.Disjoint windowSegment.reverse.support.tail
  pair_nondegenerate : 1 < firstStrand.length ∨ 1 < secondStrand.length
  firstSegment_nondegenerate : 1 < firstStrand.length ∨ 1 < windowSegment.length
  secondSegment_nondegenerate : 1 < secondStrand.length ∨ 1 < windowSegment.length
  firstStrand_length : firstStrand.length = config.length
  secondStrand_length : secondStrand.length = config.length
  windowSegment_length : windowSegment.length = config.gap

/-- Proof-irrelevant ledger proposition containing the literal ambient paths
of a genuine symmetric pair. -/
def GenuineSecondStrandConfiguration (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (representative : Graph.CanonicalPiece germ.atom.interface)
    (config : Graph.TwoStrand.Configuration) : Prop :=
  Nonempty (GenuineSecondStrandWitness data object germ representative config)

/-- Node `[163]`, yes-arm: the marked neutral equal-length terminal
configuration has its marked representative graph-realized as the second
internally-disjoint strand and retains the raw paths, attachment stubs, and
finite configuration consumed by `[167]`--`[168]`. -/
noncomputable def GenuineSecondStrandStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
      (representative : Graph.CanonicalPiece germ.atom.interface)
      (config : Graph.TwoStrand.Configuration),
    NeutralEqualLengthTerminalConfigurationAt data object germ representative ∧
      GenuineSecondStrandConfiguration data object germ representative config

/-- Node `[163]`, no-arm: the same marked neutral equal-length terminal
configuration has no genuine symmetric-pair realization with the retained
attachments, paths, and finite bound, so it enters the canonical-replacement
analysis of `[165]`--`[166]`. -/
noncomputable def CanonicalNeutralConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
      (representative : Graph.CanonicalPiece germ.atom.interface),
    NeutralEqualLengthTerminalConfigurationAt data object germ representative ∧
      ¬ ∃ config : Graph.TwoStrand.Configuration,
        GenuineSecondStrandConfiguration data object germ representative config

/-- Node `[167]`, survivor arm of the literal finite two-strand check. -/
noncomputable def TwoStrandSurvivorStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
      (representative : Graph.CanonicalPiece germ.atom.interface)
      (config : Graph.TwoStrand.Configuration),
    NeutralEqualLengthTerminalConfigurationAt data object germ representative ∧
      GenuineSecondStrandConfiguration data object germ representative config ∧
      config ∈ Graph.TwoStrand.survivors data.windowOrder
        (twoStrandEnumerationBound data)

/-- Node `[165]`, the exact canonical-replacement exchange.  Every neutral
configuration records the cut-state, equal internal size, and inherited edge
count.  Thus every nontrivial representative produces the paper's
same-`(|V|,|E|)` counterexample and replaces one canonical piece by a strict
predecessor.  Node `[166]` is the separate consumer that combines this fact
with refined minimality. -/
noncomputable def CanonicalReplacementSwapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
      (representative : Graph.CanonicalPiece germ.atom.interface),
    NeutralEqualLengthTerminalConfigurationAt data object germ representative →
      representative ≠ germ.piece.toCanonical →
      let swapped := Graph.glue representative.toPiece germ.atom.outside
      Graph.MinimumDegreeAtLeast data.threshold swapped ∧
        ¬ Graph.HasCycleWithLength data.LengthOK swapped ∧
        swapped.vertexCount = object.vertexCount ∧
        swapped.edgeCount = object.edgeCount ∧
        Graph.CanonicalPiece.Precedes representative germ.piece.toCanonical ∧
        RefinedLexicographicallySmaller swapped object

/-- Node `[166]`: every neutral configuration has trivial canonical
replacement.  This is the universal `Q = E` fact used both by the
blocked-class continuation `[169]` and by later neutral-piece
identifications. -/
noncomputable def CanonicalReplacementTrivialStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
      (representative : Graph.CanonicalPiece germ.atom.interface),
    NeutralEqualLengthTerminalConfigurationAt data object germ representative →
      representative = germ.piece.toCanonical

/-! ## Key statements

The statement each vocabulary key of this family publishes, stated over the
registered parameters and the selected object. -/

/-- Nodes `[1]`--`[4]`: the selected object avoids the target and every
strictly smaller baseline object does not. -/
noncomputable abbrev SelectionStatement
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (¬ Graph.HasCycleWithLength data.LengthOK object ∧
    SelectionMinimality BranchState Presentation presentation data object)

/-- The registered problem presentation identifies the spine threshold with
the paper's cubic baseline. -/
noncomputable abbrev CubicBaselineStatement (data : Parameters) : Prop :=
  data.threshold = 3 ∧ data.dischargeScale = 4

/-- A two-terminal closure lemma with every piece condition bound internally.
The manuscript has no such lemma and no label for it. -/
noncomputable abbrev GadgetClosureStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  let avoids (piece : Graph.FiniteObject.{u}) :=
    ¬ Graph.HasCycleWithLength data.LengthOK piece
  let cubicPiece (piece : Graph.FiniteObject.{u}) (x y : piece.Vertex) :=
    x ≠ y ∧ piece.degree x = 2 ∧ piece.degree y = 2 ∧
      ∀ vertex, vertex ≠ x → vertex ≠ y → piece.degree vertex = 3
  (∀ (left right : Graph.FiniteObject.{u})
      (a b : left.Vertex) (c d : right.Vertex),
    cubicPiece left a b → cubicPiece right c d →
    avoids left → avoids right →
    left.vertexCount + right.vertexCount < object.vertexCount →
    3 ≤ (Graph.TwoTerminalClosure.close left right a b c d).minDegree →
    ∃ leftPath : left.graph.Walk a b, ∃ rightPath : right.graph.Walk c d,
      leftPath.IsPath ∧ rightPath.IsPath ∧
      Core.DyadicLength.PowerOfTwoLength
        (leftPath.length + rightPath.length + 2)) ∧
  (∀ (piece : Graph.FiniteObject.{u}) (a b : piece.Vertex),
    piece.vertexCount < object.vertexCount → cubicPiece piece a b →
    avoids piece → 3 ≤ (piece.addEdge a b).minDegree →
    ∃ path : piece.graph.Walk a b, ∃ exponent : Nat,
      path.IsPath ∧ 1 ≤ exponent ∧ path.length = 2 ^ exponent - 1) ∧
  (∀ (piece : Graph.FiniteObject.{u}) (a b : piece.Vertex),
    2 * piece.vertexCount < object.vertexCount → cubicPiece piece a b →
    avoids piece →
    3 ≤ (Graph.TwoTerminalClosure.close piece piece a b a b).minDegree →
    ∃ first second : piece.graph.Walk a b, ∃ exponent : Nat,
      first.IsPath ∧ second.IsPath ∧
        first.length + second.length = 2 ^ exponent - 2) ∧
  (∀ (support complementSupport : Finset object.Vertex),
    let piece := object.induce support
    let complement := object.induce complementSupport
    ∀ (t1 t2 : piece.Vertex) (u1 u2 : complement.Vertex),
      (∀ vertex, vertex ∈ complementSupport ↔ vertex ∉ support) →
      cubicPiece piece t1 t2 → avoids piece → avoids complement →
      u1 ≠ u2 → ¬ complement.graph.Adj u1 u2 →
      (∀ z : piece.Vertex, ∀ u : complement.Vertex,
        object.graph.Adj z.1 u.1 ↔
          (z = t1 ∧ u = u1) ∨ (z = t2 ∧ u = u2)) →
      (complement.addEdge u1 u2).LexicographicallySmaller object →
      3 ≤ (complement.addEdge u1 u2).minDegree →
      ∃ path : complement.graph.Walk u1 u2, ∃ exponent : Nat,
        path.IsPath ∧ 1 ≤ exponent ∧ path.length = 2 ^ exponent - 1)

/-- Contracting an edge with no common cubic neighbour exposes a
power-of-two return through that edge.  The manuscript has no such lemma and
no label for it. -/
noncomputable abbrev ContractionCriticalStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ contraction : Graph.EdgeContraction object,
    (∀ common : object.Vertex,
      object.graph.Adj contraction.tail common →
      object.graph.Adj contraction.head common →
      object.degree common ≠ data.threshold) →
    ∃ path : contraction.severed.Path contraction.tail contraction.head,
      ∃ exponent : Nat,
        2 ≤ exponent ∧ path.1.length = 2 ^ exponent

/-- Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted
accepted set at every oriented edge.  This is the return-set form of target
avoidance, the standing invariant the rest of the spine consumes. -/
noncomputable abbrev ReturnAvoidanceStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ dart : object.graph.Dart,
    Disjoint (Graph.returnLengthSet object dart)
      (Graph.shiftedAcceptedSet data.LengthOK))

/-- Node `[6]`, yes arm: some oriented edge carries a Mersenne return, i.e.
its return-length set meets the shifted accepted set.  This is the exact
complement of `returnAvoidance` on the same object. -/
noncomputable abbrev MersenneReturnStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ dart : object.graph.Dart,
    ¬ Disjoint (Graph.returnLengthSet object dart)
      (Graph.shiftedAcceptedSet data.LengthOK))

/-- Node `[8]`: no proper subgraph satisfies the baseline. -/
noncomputable abbrev NoProperBaselineStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ subgraph : Graph.ProperSubgraph object,
    ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value) ∧
  object.graph.Connected

/-- Node `[9]`: every oriented edge has an endpoint exactly at the
threshold. -/
noncomputable abbrev TightEndpointStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ dart : object.graph.Dart,
    object.degree dart.fst = data.threshold ∨
      object.degree dart.snd = data.threshold)

/-- Node `[10]`: vertices strictly above the threshold are pairwise
nonadjacent. -/
noncomputable abbrev SlackIndependentStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ left right : object.Vertex,
    data.threshold < object.degree left →
    data.threshold < object.degree right →
    ¬ object.graph.Adj left right)

/-- `lem:cycle-rank`: for the selected graph,
`β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.  This is the manuscript's
division-free form of `β(G) ≥ n/2 + 1`. -/
noncomputable abbrev CycleRankConstraintStatement (object : Graph.FiniteObject.{u}) : Prop :=
  object.vertexCount + 2 ≤
    2 * (object.edgeCount + 1 - object.vertexCount)

/-- Node `[11]`, `lem:degree-profile-fibres`: every target-complete
identification of two boundaried pieces stays inside one boundary-degree
fibre. -/
noncomputable abbrev DegreeProfileFibresStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ (support : Finset object.Vertex)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
        support)),
    Graph.Response.TargetComplete
        Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK) left right →
      left.boundaryDegreeProfile = right.boundaryDegreeProfile

/-- Node `[12]`, `lem:context-universality`: every target-complete
identification has the same target response in every outside context. -/
noncomputable abbrev TargetCompleteContextUniversalityStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ (support : Finset object.Vertex)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
        support)),
    Graph.Response.TargetComplete
        Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK) left right →
      Graph.Response.ContextEquivalent
        (Graph.HasCycleWithLength data.LengthOK) left right

/-- Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller
boundary-signature-preserving replacement with one-way obstruction
inclusion. -/
noncomputable abbrev ReplacementExclusionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ support : Finset object.Vertex,
    ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)

/-- Node `[14]`: no proper atom admits a nontrivial target-complete
compression (`cor:uncompressible`). -/
noncomputable abbrev UncompressibleStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ support : Finset object.Vertex,
    ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)

/-- Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family
of induced windows, and the family is nonempty. -/
noncomputable abbrev MaximalPackingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (0 < object.windowPackingNumber data.windowOrder ∧
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∀ support : Finset object.Vertex,
          object.InducesWindow data.windowOrder support →
          ∃ member ∈ packing, ¬ Disjoint support member)

/-- Node `[18]`: `lem:labels`'s exact legal-label census at the registered
window order.  The adjacent `C_s` and `Ω₂` displays are definitions supplied
by `WindowCurvature.Safe` and `WindowCurvature.curvatureTwo`. -/
noncomputable abbrev LocalAlgebraStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ support : Finset object.Vertex,
    object.InducesWindow data.windowOrder support →
      ((Graph.WindowCurvature.Labels data.windowOrder).card = 399 ∧
        (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
          [13, 60, 122, 122, 63, 17, 2])

/-- Node `[19]`, above arm: the degree surplus exceeds the registered scale
threshold. -/
noncomputable abbrev SurplusAboveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (data.surplusThreshold object.vertexCount <
    object.degreeSurplus data.threshold)

/-- Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite
form. -/
noncomputable abbrev SurplusAtOrBelowStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (object.degreeSurplus data.threshold ≤
    data.surplusThreshold object.vertexCount)

/-- Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing
in the object's own dyadic scale. -/
noncomputable abbrev DensityCapStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `prop:p13-density` at node `[24]`, "after closure": the live-hot cap
  -- `2·rate·scaleCount·|𝒫_hot| ≤ (scaleCount + 1)(δn + T(n))` plus the
  -- cold-mass identity `|𝒫| = |𝒫_hot| + C` on the arm where the cold
  -- branch does not force a germ, `C ≤ 2σ(G) ≤ 2T(n)`.  Its asymptotic
  -- form is exactly `θ ≤ (δ/2)/rate + o(1)`, the manuscript's
  -- `θ_win = 1.5/118.108581006…`; the `o(1)` is the
  -- `(scaleCount + 1)/scaleCount` factor, the `T(n)` term, and the cold
  -- slack `4·rate·scaleCount·T(n)`, all exact here.
  (2 * (data.windowRate * data.separatedScaleCount object.vertexCount *
      object.windowPackingNumber data.windowOrder) ≤
    (Graph.dyadicScaleCount object + 1) *
      (data.threshold * object.vertexCount +
        data.surplusThreshold object.vertexCount) +
    data.densitySlack * (data.windowRate * data.separatedScaleCount object.vertexCount) *
      data.surplusThreshold object.vertexCount)

/-- Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no
window and no subgraph meeting the baseline (`sec:remainder`). -/
noncomputable abbrev RemainderNormalizedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Quantified over every maximal packing, so no family has to travel from
  -- the row that produced one: the statement is about all of them.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    ∀ support : Finset object.Vertex,
      support ⊆ object.remainderSupport packing →
      ¬ object.InducesWindow data.windowOrder support ∧
        ¬ Graph.MinimumDegreeAtLeast data.threshold
          (object.induce support))

/-- Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by
its boundary incidences (`lem:surplus-aware-window-stub`). -/
noncomputable abbrev BoundaryDemandStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:surplus-aware-window-stub`, the manuscript's chain
  --   `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`,
  -- both links kept: the first is invariant 24's demand, the second is
  -- invariant 23's window stub capacity, which is about the cut alone.  At
  -- the registered presentation the second reads `e(R,W) ≤ 15p₁₃ + σ_W`.
  -- No near-cubic hypothesis, and the statement holds at every packing, so
  -- none travels.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    object.positiveDeficiency (object.remainderSupport packing)
          data.threshold ≤
        object.boundaryIncidence (object.remainderSupport packing) ∧
      object.boundaryIncidence (object.remainderSupport packing) +
          2 * (data.windowOrder - 1) * packing.card ≤
        data.threshold * (data.windowOrder * packing.card) +
          object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
            data.threshold)

/-- Node `[29]` proper: `lem:stub-positive`'s ceiling, the same chain with the
object's own surplus and the registered near-cubic threshold spent against it.
This is the manuscript's *supply ceiling* of the final collision. -/
noncomputable abbrev StubSupplyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:stub-positive`, exactly: the same chain with the object's own
  -- surplus in place of the windows', `def⁺(R) ≤ 15p₁₃ + σ(G)`, and then
  -- the registered near-cubic ceiling `σ(G) ≤ T(n)` spent against it.  The
  -- manuscript spends `σ(G) = O(√n) = o(n)` here and writes
  -- `def⁺(R) ≤ 15p₁₃ + o(n)`; `T` is the spine's exact `o(n)`.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    object.positiveDeficiency (object.remainderSupport packing)
          data.threshold +
        2 * (data.windowOrder - 1) * packing.card ≤
      data.threshold * (data.windowOrder * packing.card) +
        data.surplusThreshold object.vertexCount)

/-- Node `[30]`, the lemma proper: every region of the remainder meets the
baseline out of its own internal wedge supply and twice its own positive
deficiency (`lem:wedge-lower`). -/
noncomputable abbrev WedgeSupplyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:wedge-lower`, subtraction-free: `δ·|X| ≤ W₂(X) + 2·def⁺(X)`.
  -- Stated at every region of the remainder, which is both of the lemma's
  -- displayed inequalities at once: the componentwise bound at a component
  -- of `R`, and its sum over the components at `R` itself.  Quantified over
  -- every maximal packing, so none has to travel.
  (∀ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing →
      ∀ support : Finset object.Vertex,
        support ⊆ object.remainderSupport packing →
        data.threshold * support.card ≤
          object.internalWedgeCount support +
            2 * object.positiveDeficiency support data.threshold) ∧
    (∀ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing →
      data.threshold * (object.remainderSupport packing).card +
            2 * (2 * (data.windowOrder - 1) * packing.card) ≤
          object.internalWedgeCount (object.remainderSupport packing) +
            2 * (data.threshold * (data.windowOrder * packing.card) +
              data.surplusThreshold object.vertexCount))

/-- Node `[31]`, `def:exact-response-profile` at the remainder of every
maximal packing: the declared raw curvature coordinates are exact, so their
labelled family has exactly `W₂(R)` entries. -/
noncomputable abbrev ExactResponseProfileStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:exact-response-profile` at the remainder of every maximal packing.
  -- The declared raw curvature coordinates (clause (D4)) are the internal
  -- length-two wedges of `R`; the profile is *exact*: "two distinct
  -- coordinate labels remain distinct entries even if their numerical
  -- values in the embedded graph coincide", so the declared family has
  -- exactly `W₂(R)` labelled entries.  The boundary-degree and
  -- all-context target components of `ρ_T^ex` are the ones every
  -- admissible quotient below is tested against.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    packing.card = object.windowPackingNumber data.windowOrder →
      (remainderCurvatureTests object packing).card =
        remainderWedgeSupply object packing)

/-- Node `[31]`, `def:admissible-rank-quotient` at the definition's own
generality — every declared coordinate family on every connected support that
carries it: a rank-reducing admissible rank quotient is represented by a
strictly smaller proper representative or by a strictly smaller admissible
closed representative.  The raw curvature family at the remainder of a maximal
packing, which node `[31]` reads, is one instance of it. -/
noncomputable abbrev AdmissibleRankQuotientStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:admissible-rank-quotient` at the manuscript's own generality:
  -- "let `𝒜` be a family of declared response coordinates carried by a
  -- connected support `X ⊆ G`" — every declared family, on every connected
  -- support that carries it, with the cut interface `T` derived from `X`.
  -- The connectedness and carrying clauses are the `connected` and
  -- `carries` fields of `Graph.DeclaredQuotient`, and its two
  -- target-completeness fields are the definition's admissibility premise;
  -- a rank-reducing one is represented — at a proper support by a strictly
  -- smaller proper representative (`lem:replacement`'s five hypotheses,
  -- `def:proper-quotient-representative`), at the whole graph by a strictly
  -- smaller admissible closed representative
  -- (`def:closed-quotient-representative`).
  --
  -- The raw curvature reading of node `[31]` is the instance at
  -- `object.InternalWedge (object.remainderSupport packing)`,
  -- `remainderCurvatureTests object packing` and `internalWedgeSupport`;
  -- the manuscript also applies the definition at an arbitrary boundaried
  -- piece, at a certificate support strictly containing the remainder, at
  -- the same-token routing and switch supports of `[144]`, at the cold
  -- corridors, and at the closed `X = G`, so the fact is recorded once at
  -- the generality all of those need.
  (∀ (Coordinate : Type u) (family : Finset Coordinate)
      (coordinateSupport : Coordinate → Finset object.Vertex)
      (quotient : Graph.DeclaredQuotient
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object family
        coordinateSupport),
    quotient.toRankQuotient.RankReducingOn ↑family →
      Graph.Strategy.InterfaceReplacement.ReplacementSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object quotient.support ∨
        ∃ representative : Graph.FiniteObject.{u},
          representative.LexicographicallySmaller object ∧
            Graph.MinimumDegreeAtLeast data.threshold representative ∧
            (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK object))

/-- Node `[31]`, `def:curvature-target-rank` at the remainder of every
maximal packing: `r_Ω(R)` is attained by a surviving subfamily of raw
curvature tests and bounds every surviving subfamily. -/
noncomputable abbrev CurvatureTargetRankStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:curvature-target-rank` at the remainder of every maximal packing:
  -- a subfamily of `𝒲₂(R)` survives when every functional admissible rank
  -- quotient is label-injective on it; `r_Ω(R)` is the maximum size of a
  -- surviving subfamily — attained, and an upper bound for every
  -- surviving subfamily.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    packing.card = object.windowPackingNumber data.windowOrder →
      (∃ independent ⊆ remainderCurvatureTests object packing,
        Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          (object.remainderSupport packing) independent ∧
        independent.card = remainderCurvatureTargetRank data object packing) ∧
      ∀ candidate ⊆ remainderCurvatureTests object packing,
        Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          (object.remainderSupport packing) candidate →
        candidate.card ≤ remainderCurvatureTargetRank data object packing)

/-- `lem:target-rank-circuit` at the remainder of every maximal packing:
every raw test outside a maximal surviving family carries a proper finite
target-dependence, and absence of proper dependences is full survival. -/
noncomputable abbrev TargetRankCircuitStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:target-rank-circuit` at the remainder of every maximal packing.
  -- For a maximal surviving subfamily `𝓘` and a raw test `a ∉ 𝓘`, some
  -- functional admissible rank quotient that loses rank on the family
  -- determines `a` from a finite subfamily `ℬ ⊆ 𝓘`: a proper
  -- target-dependence `(a, ℬ)` (`def:curvature-target-dependence`).  In
  -- particular, if no proper target-dependence exists among the raw tests,
  -- the whole family survives every functional admissible rank quotient.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    packing.card = object.windowPackingNumber data.windowOrder →
      let tests := remainderCurvatureTests object packing
      let ProperDependence := fun
          (test : object.InternalWedge (object.remainderSupport packing))
          (determiners : Set (object.InternalWedge (object.remainderSupport packing))) =>
        determiners.Finite ∧ test ∉ determiners ∧
          ∃ quotient : remainderQuotient data object packing,
            quotient.toRankQuotient.FunctionalOn ↑tests ∧
              quotient.toRankQuotient.RankReducingOn ↑tests ∧
                quotient.toRankQuotient.Determines test determiners
      (∀ independent ⊆ tests,
        Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          (object.remainderSupport packing) independent →
        independent.card = remainderCurvatureTargetRank data object packing →
        ∀ test ∈ tests, test ∉ independent →
          ∃ determiners, determiners ⊆ ↑independent ∧
            ProperDependence test determiners) ∧
      ((¬ ∃ test ∈ tests, ∃ determiners, determiners ⊆ ↑tests ∧
          ProperDependence test determiners) →
        Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          (object.remainderSupport packing) tests))

/-- Node `[32]`, yes arm: `r_Ω(R) < W₂(R) − o(W₂)` for some admissible
quotient system, together with the proper target-dependence the rank drop
yields.  This is node `[33]`, Branch D. -/
noncomputable abbrev CurvatureRankDropStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Any strict loss of raw curvature rank supplies the proper
  -- target-dependence routed by Branch D.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      remainderCurvatureTargetRank data object packing <
          remainderWedgeSupply object packing ∧
        let support := object.remainderSupport packing
        let family := object.internalWedgeFamily support
        ∃ test ∈ family,
          ∃ determiners : Set (object.InternalWedge support),
            determiners ⊆ ↑family ∧ determiners.Finite ∧
              test ∉ determiners ∧
                ∃ declared : Graph.DeclaredQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object family
                  (Graph.FiniteObject.internalWedgeSupport
                    (region := support)),
                  declared.toRankQuotient.FunctionalOn ↑family ∧
                    declared.toRankQuotient.RankReducingOn ↑family ∧
                      declared.toRankQuotient.Determines test determiners)

/-- Node `[32]`, no arm: `r_Ω(R) ≥ W₂(R) − o(W₂)` against every admissible
quotient system.  This is node `[34]`, Residual B. -/
noncomputable abbrev CurvatureFullRankStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- This is the equality proved in the last paragraph of `lem:full-rank`.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
        remainderCurvatureTargetRank data object packing =
          remainderWedgeSupply object packing)

/-- Nodes `[33]` and `[35]`: Branch D, entered with the determination
certificate.  `lem:target-rank-circuit` turns the rank drop into a proper
target-dependence, and `lem:curvature-dependence-routing` opens its proof by
choosing a certificate for that dependence: an admissible rank quotient on a
connected determination support, rank-reducing on the raw curvature tests.
That certificate is the object nodes `[36]`, `[38]` and `[40]` route. -/
noncomputable abbrev BranchDependenceStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Nodes `[33]`/`[35]`: choose the paper's determination certificate with
  -- inclusion-minimal connected support.  The determined coordinate is
  -- fixed during minimization, while its finite determining subfamily may
  -- vary.  A `remainderQuotient` is already a declared admissible quotient;
  -- its support/carries fields are the connected declared support data.
  by
    classical
    exact ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        remainderCurvatureTargetRank data object packing <
            remainderWedgeSupply object packing ∧
          ∃ test,
          let Supports := object.vertexFinset.powerset.filter
            fun candidateSupport =>
              ∃ determiners quotient,
                quotient.support = candidateSupport ∧
                  ∃ supportData,
                    DeterminationCertificate data object packing test
                      determiners quotient supportData
          ∃ determiners quotient supportData,
            DeterminationCertificate data object packing test determiners
                quotient supportData ∧
              ∀ smaller : Finset object.Vertex,
                smaller ⊂ quotient.support →
                  ∀ narrower : remainderQuotient data object packing,
                    narrower.support = smaller →
                      ∀ narrowerDeterminers narrowerSupportData,
                        ¬ DeterminationCertificate data object packing test
                          narrowerDeterminers narrower narrowerSupportData

/-- Node `[35]`, `lem:separated-testers`: corresponding internal wedges in
vertex-disjoint isomorphic rooted balls can be tested only by the outside
side of their boundaried decomposition; any quotient identifying the two
wedge labels is context-universal or has a concrete target-defect witness. -/
noncomputable abbrev SeparatedTestersStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:separated-testers`, with each manuscript object represented
  -- literally.  `closedBall` is the rooted radius-`r` neighbourhood.  The
  -- rooted graph isomorphism maps the two wedge centres and their two
  -- neighbours.  An ambient target tester is the outside side of an exact
  -- owned decomposition whose piece side is the union of the two balls;
  -- its internal support is therefore in their complement.  Finally an
  -- attempted rank quotient identifying the wedge labels is either valid
  -- against every outside context or exhibits an identified pair with a
  -- concrete target-defect context.
  (∀ (packing : Finset (Finset object.Vertex)),
    object.IsWindowPacking data.windowOrder packing →
    packing.card = object.windowPackingNumber data.windowOrder →
    ∀ (radius : Nat) (u v : object.Vertex),
      u ∈ object.remainderSupport packing →
      v ∈ object.remainderSupport packing →
      let closedBall := fun root : object.Vertex =>
        object.vertexFinset.filter fun vertex =>
          object.graph.edist vertex root ≤ radius
      ∀ (leftWedge rightWedge :
          object.InternalWedge (object.remainderSupport packing)),
        leftWedge ∈ remainderCurvatureTests object packing →
        rightWedge ∈ remainderCurvatureTests object packing →
        leftWedge.1 = u → rightWedge.1 = v →
        (∃ iso : (object.induce (closedBall u)).graph ≃g
              (object.induce (closedBall v)).graph,
          (∀ hu : u ∈ closedBall u, (iso ⟨u, hu⟩).1 = v) ∧
          (∀ hv : v ∈ closedBall v, (iso.symm ⟨v, hv⟩).1 = u) ∧
          (∀ x, x ∈ leftWedge.2.1 →
            ∃ hx : x ∈ closedBall u,
              (iso ⟨x, hx⟩).1 ∈ rightWedge.2.1) ∧
          (∀ y, y ∈ rightWedge.2.1 →
            ∃ hy : y ∈ closedBall v,
              (iso.symm ⟨y, hy⟩).1 ∈ leftWedge.2.1)) →
        Disjoint (closedBall u) (closedBall v) →
        (∀ (decomposition : Graph.OwnedDecomposition object),
          (∀ vertex, (vertex ∈ closedBall u ∨ vertex ∈ closedBall v) ↔
            ∃ inside, decomposition.pieceIntoAmbient inside = vertex) →
          ∀ (represented :
              object.InternalWedge (object.remainderSupport packing) →
                Graph.BoundaryPiece decomposition.interface),
            ¬ (Graph.HasCycleWithLength data.LengthOK
                  (Graph.glue (represented leftWedge) decomposition.outside) ↔
                Graph.HasCycleWithLength data.LengthOK
                  (Graph.glue (represented rightWedge) decomposition.outside)) →
            ∀ internal : decomposition.outside.Internal,
              decomposition.vertexEquiv
                  (Graph.contextEmbedding decomposition.piece
                    decomposition.outside (.inr internal)) ∉ closedBall u ∧
              decomposition.vertexEquiv
                  (Graph.contextEmbedding decomposition.piece
                    decomposition.outside (.inr internal)) ∉ closedBall v) ∧
        (∀ (attempt : Graph.AttemptedQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object
              (remainderCurvatureTests object packing)
              (Graph.FiniteObject.internalWedgeSupport
                (region := object.remainderSupport packing))),
          attempt.label leftWedge = attempt.label rightWedge →
          ((∀ left right : Graph.BoundaryPiece
                (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
                  object attempt.support),
              attempt.Identifies left right →
                Graph.Response.ContextEquivalent
                  (Graph.HasCycleWithLength data.LengthOK) left right) ∨
            ∃ left right : Graph.BoundaryPiece
                (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
                  object attempt.support),
              attempt.Identifies left right ∧
                Graph.Response.TargetDefect
                  (Graph.HasCycleWithLength data.LengthOK) left right)))

/-- Node `[36]`, yes arm: the determination the certificate makes is valid
against every outside context, and the states it identifies lie in one
boundary-degree fibre (`lem:context-universality`,
`lem:degree-profile-fibres`).  This is the residual node `[38]` consumes. -/
noncomputable abbrev ContextUniversalStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[36]`, yes: the single certificate chosen at `[33]` remains
  -- valid against every outside context.  The certificate and its
  -- same-coordinate inclusion-minimality identify exactly which quotient
  -- this branch fact concerns; the earlier strict-drop fact remains in the
  -- ExactLedger and is not copied here.
  by
    classical
    exact ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ test determiners quotient supportData,
          DeterminationCertificate data object packing test determiners
              quotient supportData ∧
          (∀ smaller : Finset object.Vertex,
            smaller ⊂ quotient.support →
              ∀ narrower : remainderQuotient data object packing,
                narrower.support = smaller →
                  ∀ narrowerDeterminers narrowerSupportData,
                    ¬ DeterminationCertificate data object packing test
                      narrowerDeterminers narrower narrowerSupportData) ∧
          ∀ left right, Identified quotient left right →
            Graph.Response.ContextEquivalent
              (Graph.HasCycleWithLength data.LengthOK) left right

/-- Node `[36]`, no arm — the terminal `[37]`: some pair of states the
certificate identifies is separated by a concrete outside context.  This is
case (i) of `lem:curvature-dependence-routing`, a target-defective quotient.
Boundary-profile preservation is already part of quotient admissibility. -/
noncomputable abbrev ContextDefectStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[36]`, no: the same selected certificate has a concrete pair of
  -- identified realizations separated by an outside context, exactly the
  -- paper's target-defective alternative.  Boundary-fibre preservation is
  -- part of admissibility and is not reproved or branched on here.
  by
    classical
    exact ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ test determiners quotient supportData,
          DeterminationCertificate data object packing test determiners
              quotient supportData ∧
          (∀ smaller : Finset object.Vertex,
            smaller ⊂ quotient.support →
              ∀ narrower : remainderQuotient data object packing,
                narrower.support = smaller →
                  ∀ narrowerDeterminers narrowerSupportData,
                    ¬ DeterminationCertificate data object packing test
                      narrowerDeterminers narrower narrowerSupportData) ∧
          ∃ left right, Identified quotient left right ∧
            Graph.Response.TargetDefect
              (Graph.HasCycleWithLength data.LengthOK) left right

/-- Node `[38]`, yes arm — the terminal `[39]`: the context-universal
determination is already certified inside the proper atom `C`, so the
quotient is a target-complete rank-reducing quotient of `C` and
`def:admissible-rank-quotient` supplies a strictly smaller proper
representative.  This is case (ii), proper atom compression. -/
noncomputable abbrev AtomCompressionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[38]` yes, the terminal `[39]`: the determination is certified
  -- without leaving `C`, which is case (ii) -- "it holds for every outside
  -- context already with support `C`".
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      ∃ quotient : remainderQuotient data object packing,
        (∃ test determiners supportData,
          DeterminationCertificate data object packing test determiners
            quotient supportData) ∧
          TargetCompleteAt data quotient ∧
            quotient.support ⊆ object.remainderSupport packing ∧
              Graph.Strategy.InterfaceReplacement.ReplacementSupport
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object
                quotient.support)

/-- Node `[40]`: the determination is certified only after adjoining
structure outside `C`, so the connected support it needs strictly contains
`C`.  This is case (iii)'s entry. -/
noncomputable abbrev DelocalizedSupportStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[40]`: case (iii)'s entry.  The certificate reaches outside `C`,
  -- so the connected support the determination needs strictly contains it.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      ∃ quotient : remainderQuotient data object packing,
        (∃ test determiners supportData,
          DeterminationCertificate data object packing test determiners
            quotient supportData) ∧
          TargetCompleteAt data quotient ∧
            ¬ quotient.support ⊆ object.remainderSupport packing ∧
              object.remainderSupport packing ⊂
                delocalizationSupport data object packing quotient)

/-- Node `[41]`, yes arm — the terminal `[42]`: the enlarged support is still
proper in `G`.  `lem:proper-smearing`: a proper boundaried support carrying
the dependence is a target defect or a target-complete compression, and both
are excluded at a minimal counterexample. -/
noncomputable abbrev ProperDelocalizationStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[41]` yes, the terminal `[42]`: `Z ⊊ G`.  `lem:proper-smearing`
  -- is stated exactly under this hypothesis.  The paper's `Z` is the
  -- connected determination support carried by the quotient itself.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      ∃ quotient : remainderQuotient data object packing,
        (∃ test determiners supportData,
          DeterminationCertificate data object packing test determiners
            quotient supportData) ∧
          TargetCompleteAt data quotient ∧
            ¬ quotient.support ⊆ object.remainderSupport packing ∧
              ∃ vertex,
                vertex ∉ quotient.support ∧
              Graph.Strategy.InterfaceReplacement.ReplacementSupport
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object
                quotient.support)

/-- Node `[43]`: the enlarged support is the whole graph, so the dependence
delocalizes globally and the quotient is a closed exact-profile quotient. -/
noncomputable abbrev GlobalDelocalizationStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[43]`: `Z = G`.  The quotient is then a closed exact-profile
  -- quotient, which is the hypothesis of `lem:no-silent-global-smearing`.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      ∃ quotient : remainderQuotient data object packing,
        (∃ test determiners supportData,
          DeterminationCertificate data object packing test determiners
            quotient supportData) ∧
          TargetCompleteAt data quotient ∧
            ¬ quotient.support ⊆ object.remainderSupport packing ∧
              ∀ vertex,
                vertex ∈ quotient.support)

/-- Node `[44]`: `lem:smearing-support-repair`'s identity
`s = p − 2 + 2β − σ` for a delayed compensation component of the
delocalization support, at every `1`--`3` repair network up to surplus. -/
noncomputable abbrev RepairIdentityStatement (object : Graph.FiniteObject.{u}) : Prop :=
  -- Node `[44]`, `lem:smearing-support-repair`: for each stipulated
  -- `1`--`3` repair component on the active support `Z = G`, the paper
  -- records only the handshake identity below.  The raw embedding and
  -- graph inclusion express that the repair network lies in the active
  -- graph; node `[43]`'s whole-support witness remains in its own earlier
  -- ledger entry instead of being copied into this value.
  ∀ component : Graph.OneThreeRepair.Component.{u},
    (∃ embedding : component.object.Vertex ↪ object.Vertex,
      component.object.graph.map embedding ≤ object.graph) →
    (component.internal.card : Int) =
      component.boundary.card - 2 +
        2 * component.cycleRank - component.surplus

/-- Node `[45]`: the global profile barrier `lem:no-silent-global-smearing`
raises against a whole-graph dependence — the closed clause of
`def:admissible-rank-quotient` yields either a proper-support replacement or
a strictly smaller admissible closed representative. -/
noncomputable abbrev GlobalBarrierStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[45]`, `lem:no-silent-global-smearing`: node `[43]` has already
  -- established that the target-complete rank-reducing quotient has
  -- support `Z = G`.  The closed admissibility clause therefore supplies
  -- exactly the strictly smaller admissible closed representative below;
  -- the earlier quotient and coverage data remain in their own ledger
  -- entry and are not republished here.
  ∃ representative : Graph.FiniteObject.{u},
    representative.LexicographicallySmaller object ∧
      Graph.MinimumDegreeAtLeast data.threshold representative ∧
        (Graph.HasCycleWithLength data.LengthOK representative →
          Graph.HasCycleWithLength data.LengthOK object)

/-- The statement published under the `coldSameInterfaceTable` key. -/
noncomputable abbrev ColdSameInterfaceTableStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:cold-same-interface-table` and `lem:cold-short-self-return-filter`.
  --
  -- The first clause closes every row of `def:cold-same-interface-table`:
  -- no row is realizing, and every row is either handed off to an already
  -- closed ledger or distinguishing.  It is quantified over every handoff
  -- support predicate supplied by the incoming ledger, so a row cannot
  -- escape by naming its own; a row that is not handed off and not distinguishing is a
  -- target-complete compression of its own proper support, which node
  -- `[14]` has already excluded.
  --
  -- The second is the short self-return filter: a cold-window outside
  -- self-return whose smear interval `[ℓ, ℓ+order−1]` meets an accepted
  -- length realizes it.  The surviving lengths are the rows of the table,
  -- and the first clause closes them with the germs.
  --
  -- The table has two row families, and both are closed here.  The first
  -- clause is the equal-length cold bounded germs; the second is the short
  -- self-return exceptions, whose lengths are *proved* to be
  -- `lem:cold-short-self-return-filter`'s surviving ones -- an accepted
  -- length in a self-return's smear interval would be realized through its
  -- cold-window offset, and the selected object realizes none.
  ColdGermCandidatesStatement data object ∧
    ((∀ Handoff : Finset object.Vertex → Prop,
      ∀ row : Graph.ColdCorridor.TableRow data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object Handoff,
        ¬ row.Realizing ∧ (Handoff row.support ∨ row.Distinguishing)) ∧
      (∀ Handoff : Finset object.Vertex → Prop,
        ∀ self : Graph.ColdCorridor.SelfReturn data.coldSignature data.LengthOK
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object Handoff,
          Graph.ColdCorridor.SurvivesSmear data.LengthOK
              (data.coldSignature.windowOrder - 1) self.outsideLength ∧
            ¬ self.row.Realizing ∧
              (Handoff self.row.support ∨ self.row.Distinguishing)) ∧
      (∀ length : Nat,
        ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
            (data.windowOrder - 1) length →
          ∃ tested, length ≤ tested ∧ tested ≤ length + (data.windowOrder - 1) ∧
            data.LengthOK tested) ∧
      -- `def:cold-same-interface-table`'s own finiteness claim -- "the table
      -- is finite because the support size, boundary size, window labels, and
      -- declared coordinate labels are bounded" -- and the equal-length
      -- condition `δ = 0` that makes a row a row.
      (Graph.ColdCorridor.tableBound data.coldSignature =
        Fintype.card (Graph.ColdCorridor.Record data.coldSignature)) ∧
      ∀ Handoff : Finset object.Vertex → Prop,
        ∀ row : Graph.ColdCorridor.TableRow data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object Handoff,
          row.increment = 0)

/-- The statement published under the `coldGermRealized` key. -/
noncomputable abbrev ColdGermRealizedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:cold-bounded-germ-trichotomy`, G1 and the exhaustiveness of the
  -- three cases.
  --
  -- G1 is "some compatible live completion and window offset close a dyadic
  -- cycle.  This contradicts the counterexample condition": a germ's own
  -- compatible completion *is* the selected object, up to the
  -- decomposition's reconstruction isomorphism, so a realizing germ would
  -- hand it the target node `[1]` says it avoids.  No germ realizes.
  --
  -- The second clause is the manuscript's own reading of the split -- "by
  -- whether a compatible completion realizes a dyadic hit, distinguishes
  -- dyadic truth without realization in `G`, or never distinguishes the two
  -- representatives" -- and it is what makes the routing of the remaining
  -- two arms exhaustive rather than partial.  It is also the case
  -- distinction `lem:cold-increment-arithmetic` (c) appeals to when it
  -- sends a target-visible periodic carrier to G2 and a target-invisible one
  -- to G3.
  ColdGermCandidatesStatement data object ∧
    ((∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object,
        ¬ germ.Realizing) ∧
      ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object,
        germ.Realizing ∨ germ.Distinguishing ∨ germ.Neutral)

/-- The statement published under the `coldGermDistinguished` key. -/
noncomputable abbrev ColdGermDistinguishedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:cold-bounded-germ-trichotomy`, G2, through
  -- `lem:context-universality`: "the two local responses agree in the actual
  -- quotient but disagree in a compatible context.  By
  -- `lem:context-universality`, such an identification is not
  -- target-complete; equivalently it is a target-defective quotient."
  --
  -- The conclusion is drawn in *every* immutable profile fibre, which is
  -- what makes it a statement about the quotient rather than about one
  -- chosen profile, and it is the same shape node `[156]` already commits
  -- for the (F2) discrepancy.  No cycle is claimed: the manuscript is
  -- explicit that G2 distinguishes "without already realizing the cycle in
  -- the current graph", and what the germ is routed to is the defect exit.
  ColdGermCandidatesStatement data object ∧
    ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
      ∀ (Profile : Type)
        (profile : Graph.BoundaryPiece germ.atom.interface → Profile),
        germ.Distinguishing →
          ¬ Graph.Response.TargetComplete profile
            (Graph.HasCycleWithLength data.LengthOK) germ.piece germ.canonical

/-- The statement published under the `coldGermSilent` key. -/
noncomputable abbrev ColdGermSilentStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:cold-bounded-germ-trichotomy`, G3, with
  -- `lem:cold-increment-arithmetic`.
  --
  -- First clause, G3: "replacing the longer representative by the shorter
  -- one preserves the boundary degree profile and the target response
  -- against every context, creates no dyadic cycle, and strictly decreases
  -- the support.  This is a nontrivial target-complete compression of a
  -- proper support", forbidden by `cor:uncompressible`.  The germ is
  -- oriented as the manuscript orients it: its support carries the longer
  -- representative, so `δ < 0` and the replacement is the shorter one.  No
  -- silent length-changing germ survives.
  --
  -- The remaining clauses are `lem:cold-increment-arithmetic`, which decides
  -- which arm a length-changing germ falls into.  Everything is stated at
  -- the smear `order − 1` of `lem:cold-short-self-return-filter`, so the
  -- manuscript's `12` and `13` are the registered window order and no
  -- numeral is written.
  --
  -- (a) `1 ≤ δ ≤ 12`: "the achievable length blocks `[L+jδ, L+jδ+12]`
  -- overlap … Hence their union is an interval.  An interval containing a
  -- power of two gives G1."  An accepted length in the covered interval
  -- makes one block fail the smear filter, which is the offset that closes
  -- the cycle.
  --
  -- (b) `δ ≥ 13` with the doubling orbit hitting a smear residue: "a
  -- congruence `2^k ≡ L + r (mod δ)` with `0 ≤ r ≤ 12` means that, after
  -- adding the appropriate number of homogeneous copies, one attainable
  -- length is `2^k`.  This is exactly a hit-realized germ."
  --
  -- The order criterion: "for odd `δ`, `ord_δ(2) > δ − 13` forces case
  -- (b)", the pigeonhole between the doubling orbit and the complement of
  -- the thirteen smear residues.
  --
  -- The even transient: "for `δ = 2^a u`, the initial powers with `k < a`
  -- form a bounded transient, and for `k ≥ a` the congruence reduces to the
  -- odd modulus `u`."
  --
  -- (d) `δ = 0`: "the equal-length switch belongs to the finite
  -- same-interface cold table", which is `def:cold-same-interface-table`'s
  -- own defining clause and routes the germ to node `[157]`'s table.
  ((∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
      germ.increment < 0 → ¬ germ.Neutral) ∧
    (∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
      ¬ germ.LengthChanging ↔
        germ.canonical.internalVertexCount =
          germ.piece.internalVertexCount) ∧
    (∀ increment base copies length : Nat,
      0 < increment →
      increment ≤ (data.coldSignature.windowOrder - 1) + 1 →
      base ≤ length →
      length ≤ base + copies * increment +
        (data.coldSignature.windowOrder - 1) →
      data.LengthOK length →
        ∃ j ≤ copies, ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
          (data.coldSignature.windowOrder - 1) (base + j * increment)) ∧
    (∀ increment base exponent residue : Nat,
      0 < increment →
      residue ≤ (data.coldSignature.windowOrder - 1) →
      base + residue ≤ 2 ^ exponent →
      2 ^ exponent % increment = (base + residue) % increment →
      data.LengthOK (2 ^ exponent) →
        ∃ j, ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
          (data.coldSignature.windowOrder - 1) (base + j * increment)) ∧
    (∀ (increment base : Nat) (_ : NeZero increment),
      (data.coldSignature.windowOrder - 1) + 1 ≤ increment →
      increment - ((data.coldSignature.windowOrder - 1) + 1) <
          orderOf (2 : ZMod increment) →
        ∃ k < orderOf (2 : ZMod increment),
          ∃ residue ≤ (data.coldSignature.windowOrder - 1),
            2 ^ k % increment = (base + residue) % increment) ∧
    ∀ transient exponent odd : Nat, transient ≤ exponent →
      2 ^ exponent % (2 ^ transient * odd) =
        2 ^ transient * (2 ^ (exponent - transient) % odd))

/-- The statement published under the `coldFailureHandoff` key. -/
noncomputable abbrev ColdFailureHandoffStatement (object : Graph.FiniteObject.{u}) : Prop :=
  -- `lem:cold-corridor-first-failure` (iv).  A corridor that first enters
  -- a support already recorded in the incoming ledger transfers there.
  -- The cold row records only the local membership; it constructs no
  -- envelope object.
  (∀ (windows component : Finset object.Vertex)
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (Handoff : Finset object.Vertex → Prop)
    (segment : corridor.Segment),
    Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff segment →
      ∃ support, Handoff support ∧ corridor.head segment ∈ support)

/-- `lem:bridgeless`: the selected minimal counterexample has no bridge —
every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`. -/
noncomputable abbrev BridgelessStatement (object : Graph.FiniteObject.{u}) : Prop :=
  -- `lem:bridgeless`: "every edge of `G` lies on a cycle; equivalently
  -- `R_e(G) ≠ ∅` for every oriented edge".  `HasReturn` is a simple path
  -- from the tail back to the head after the edge is deleted.
  (∀ contraction : Graph.EdgeContraction object, contraction.HasReturn)

/-- Node `[21]`, `lem:p13-window-package` with `def:target-rank` and
the realization sentence used in `lem:p13-window-package` and `prop:p13-density`,
"all target-complete window states are realized by labelled near-cubic
skeletons": the canonical
multi-scale package of the fixed maximal packing is a family of independently
target-testable coordinates, i.e. its full package code is realized canonically
by the labelled skeletons of the current object's class `𝒢_{n,m}`. -/
noncomputable abbrev WindowPackageRealizedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  WindowPackageRealized data object (canonicalWindowPacking data object)

/-- The complementary arm of the `[21]` realization decision: the fixed
maximal packing's full package code is *not* realized canonically by the
labelled skeletons of the current object's class — the residual on which the
manuscript's `[21]` sentence fails, carried as a branch of its own. -/
noncomputable abbrev WindowPackageUnrealizedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ WindowPackageRealized data object (canonicalWindowPacking data object)

/-- Node `[159]`: the no-arm of `[158]`, after comparison with the labelled
skeleton class: the canonical window-package demand strictly exceeds the
exact skeleton budget. -/
noncomputable abbrev DensePackingOverflowStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.skeletonBudget object <
    2 ^ (windowPackageBits data object *
      (canonicalWindowPacking data object).card)

/-- Its exact complement: the dense residual, `τ(θ) ≥ 1/4` up to the exact
allowance, on which the net-charge collision does not fire. -/
noncomputable abbrev DenseDeficiencyAtOrAboveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ DenseDeficiencyBelowStatement data object

/-- Node `[168]`, the stub structure of the ambient-cubic cold windows: at
exactly two endpoints carry `δ − 1` external stubs and every other window vertex
carries `δ − 2`; a genuine symmetric strand pair needs two stubs at each
attachment vertex, so it can attach only at the endpoints, and at least
`(order − 2)(δ − 2)` stubs are single-stub interior attachments. -/
noncomputable abbrev ColdWindowStubStructureStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop := by
  -- `lem:cold-window-stub-excess` read vertex by vertex at every ambient-cubic
  -- cold window of the fixed packing (`Graph/WindowStubStructure.lean`).
  classical
  exact (∀ window ∈ (canonicalColdWindows data object).filter (AmbientCubicWindow data object),
    ∃ ends : Finset object.Vertex, ends ⊆ window ∧ ends.card = 2 ∧
      (∀ vertex ∈ window, vertex ∉ ends →
        (object.externalNeighbours window vertex).card = data.threshold - 2) ∧
      (∀ vertex ∈ ends,
        (object.externalNeighbours window vertex).card = data.threshold - 1) ∧
      (data.windowOrder - 2) * (data.threshold - 2) ≤
        ∑ vertex ∈ window.filter (fun vertex =>
          (object.externalNeighbours window vertex).card = data.threshold - 2),
          (object.externalNeighbours window vertex).card)

/-- Node `[168]`: the endpoint/interior stub count excludes every surviving
genuine pair whose retained origin is one of the selected interior
half-edges. -/
noncomputable abbrev ColdSymmetricPairExcludedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ TwoStrandSurvivorStatement data object

/-- `lem:refined-minimality-swap`, size-reducing case (node `[165]`): some
neutral germ's corridor piece has a canonical representative with strictly
fewer internal vertices, so the exchange is a strictly smaller counterexample. -/
noncomputable abbrev ColdCanonicalSwapSmallerStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    germ.Neutral ∧
      (germCanonicalRepresentative data germ).size < germ.piece.internalVertexCount

/-- The exact complement: every neutral germ's canonical representative has
the same internal size as its corridor piece — the same-size tie-break of node
`[166]`. -/
noncomputable abbrev ColdCanonicalSwapSameSizeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    germ.Neutral →
      ¬ (germCanonicalRepresentative data germ).size < germ.piece.internalVertexCount

/-- Node `[169]`, `def:blocked-class`: on the trivial neutral-configuration residual the
object's own labelled skeleton lies in the blocked class `𝓑(𝒫)` of the fixed
maximal packing (near-cubic, windows present, no accepted cycle through a
window), and `card 𝓑(𝒫) ≤ skeletonBudget`. -/
noncomputable abbrev BlockedClassMemberStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:blocked-class`, last sentence, at the fixed maximal packing: the
  -- object's skeleton has the baseline minimum degree, contains every packed
  -- window at its labelled position, and no accepted cycle passes through a
  -- window; and the class is dominated by the skeleton budget
  -- (`lem:skeleton-dominates`).  Read at `objectSkeleton`, the graph
  -- transported to `Fin n` by the object's own labelling.
  Graph.BlockedClass.MinDegreeAtLeast data.threshold
      (Graph.BlockedClass.objectSkeleton object) ∧
    Graph.BlockedClass.IsBlocked data.windowOrder data.LengthOK
      (Graph.BlockedClass.windowLabels object (canonicalWindowPacking data object))
      (Graph.BlockedClass.objectSkeleton object) ∧
    Nat.card (Graph.BlockedClass.Blocked object.vertexCount object.edgeCount
        data.threshold data.windowOrder data.LengthOK
        (Graph.BlockedClass.windowLabels object (canonicalWindowPacking data object))) ≤
      Graph.skeletonBudget object

/-- Node `[171]`, `lem:blocked-graphs-compress`: the denominator-cleared
finite-exposure inequality for the blocked class against the exact
near-cubic a-priori class. -/
noncomputable abbrev BlockedCompressionBoundStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Nat.card (blockedClassAt data object) *
      2 ^ (windowPackageBits data object *
        (canonicalWindowPacking data object).card) ≤
    Nat.card (blockedAprioriClassAt data object)

/-- Node `[171]`, terminal consequence: the registered package saving is at
most the exact labelled-skeleton budget. -/
noncomputable abbrev BlockedCompressionCapStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  2 ^ (windowPackageBits data object *
      (canonicalWindowPacking data object).card) ≤
    Graph.skeletonBudget object

/-- The route-8 rate-failure residual, `rem:route8-carrier-margin` read
exactly: the cold family of the fixed packing is nonempty, so the failure of
the private-carrier rate is carried by absorbed cold germs (`[174]`--`[177]`). -/
noncomputable abbrev ColdFamilyPositiveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  0 < (canonicalColdWindows data object).card

/-- The complementary arm: the cold family is empty — every packed window is
hot at the exact skeleton budget, and the private-carrier rate still fails:
the exact budget-edge corner of `rem:route8-carrier-margin`. -/
noncomputable abbrev ColdFamilyEmptyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (canonicalColdWindows data object).card = 0

/-- Nodes `[21]`--`[22]`: `lem:p13-window-package`.  The selected coordinates of
the multi-scale window package are separated, and each carries the audited
per-window rate.  This is the arm on which `lem:independent-target-entropy`
applies; the arm where the coordinates collide is the `O(1)` the manuscript's
scale count discards. -/
noncomputable abbrev WindowPackageSeparatedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop := by
  classical
  let scales := data.separatedScaleCount object.vertexCount
  let bits := windowPackageBits data object
  exact ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        (∀ support : Finset object.Vertex,
          object.InducesWindow data.windowOrder support →
            ∃ member ∈ packing, ¬ Disjoint support member) ∧
        let Coordinate := Graph.DeclaredSignature.Coordinate
          object.Vertex (Fin bits × Finset object.Vertex)
        let package : Finset object.Vertex → Finset Coordinate := fun window =>
          Finset.univ.image fun bit =>
            Graph.DeclaredSignature.Coordinate.base
              .windowLabel (bit, window) window
        let family := packing.biUnion package
        (∀ window ∈ packing, (package window).card = bits) ∧
          (∀ left ∈ packing, ∀ right ∈ packing, left ≠ right →
            Disjoint (package left) (package right)) ∧
          family.card = bits * packing.card ∧
          data.windowRate * scales ≤ bits ∧
          (∀ declared : Graph.DeclaredQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object family
              Graph.DeclaredSignature.Coordinate.support,
            declared.toRankQuotient.FunctionalOn ↑family →
              declared.toRankQuotient.LabelInjectiveOn ↑family) ∧
          (∀ (BaselineCoordinate : Type u)
              (baseline : Finset BaselineCoordinate)
              (baselineSupport : BaselineCoordinate → Finset object.Vertex),
            (∀ declared : Graph.DeclaredQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object baseline
                baselineSupport,
              declared.toRankQuotient.FunctionalOn ↑baseline →
                declared.toRankQuotient.LabelInjectiveOn ↑baseline) →
            let combined := family.image Sum.inl ∪ baseline.image Sum.inr
            let combinedSupport : Sum Coordinate BaselineCoordinate →
                Finset object.Vertex :=
              Sum.elim Graph.DeclaredSignature.Coordinate.support
                baselineSupport
            ∀ declared : Graph.DeclaredQuotient
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object combined
                combinedSupport,
              declared.toRankQuotient.FunctionalOn ↑combined →
                declared.toRankQuotient.LabelInjectiveOn ↑combined)

/-- The statement published under the `coldGermExtraction` key. -/
noncomputable abbrev ColdGermExtractionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:cold-germ-extraction`, in ledger form on the current object.  The
  -- candidate family consists of actual bounded germs of this residual, so
  -- the overlap graph is the one on their literal supports.  No arbitrary
  -- `Germ` type, support-realization premise, disjoint-family carrier, or
  -- theorem bundle is exported.
  ColdExchangeBoundStatement data object ∧
    Graph.ColdCorridor.ColdGermOccurrenceExtractionLocal data.coldSignature
      data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object

/-- The statement published under the `coldGermRouted` key. -/
noncomputable abbrev ColdGermRoutedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The length-changing germ conclusion obtained by eliminating G1 and G3
  -- and then reading the G2 route from the ledger.  The fact therefore
  -- carries the actual target-defect route, not just the intermediate
  -- `Distinguishing` predicate.
  ColdGermCandidatesStatement data object ∧
    ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object,
      germ.increment < 0 →
        germ.Distinguishing ∧
          (∀ (Profile : Type)
            (profile : Graph.BoundaryPiece germ.atom.interface → Profile),
            ¬ Graph.Response.TargetComplete profile
              (Graph.HasCycleWithLength data.LengthOK)
              germ.piece germ.canonical) ∧
          (germ.Distinguishing ∨
            HandoffProduced data object (canonicalWindowPacking data object)
              germ.support)

/-- Node `[154]`, first binary test of `lem:cold-bounded-germ-trichotomy`
(G1): some configuration of the extracted active family is hit-realized. -/
noncomputable abbrev ColdGermSomeRealizingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:cold-bounded-germ-trichotomy`, G1 read as the `[154]` test on the
  -- node-`[153]` active family: some configuration is hit-realized.
  ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    ActiveColdGermStatement data object germ ∧ germ.Realizing

/-- Node `[154]`, the exact complement of `coldGermSomeRealizing`. -/
noncomputable abbrev ColdGermNoneRealizingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    ActiveColdGermStatement data object germ ∧ germ.Realizing

/-- Node `[154]`, second binary test on the no-G1 arm (G2): some configuration
of the extracted active family is hit-distinguished. -/
noncomputable abbrev ColdGermSomeDistinguishingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- G2 read as the second `[154]` test: some active configuration is
  -- hit-distinguished.
  ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    ActiveColdGermStatement data object germ ∧ germ.Distinguishing

/-- Node `[154]`, the exact complement of `coldGermSomeDistinguishing`: every
active configuration is silent (G3 or the equal-length table). -/
noncomputable abbrev ColdGermNoneDistinguishingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    ActiveColdGermStatement data object germ ∧ germ.Distinguishing

/-- The statement published under the `coldBranchClosed` key. -/
noncomputable abbrev ColdBranchClosedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `thm:cold-branch-quantitative-closure`, in the form consumed by the
  -- cold oval: after the current residual's length-changing germs and
  -- same-interface table rows have been routed, no local terminal cold
  -- pattern remains on this residual.
  Graph.ColdCorridor.NoTerminalColdResidual data.coldSignature data.threshold
    data.LengthOK (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) object

/-- Nodes `[47]`--`[48]`: `cor:forced-curvature-cost`.  The full-rank residual
pays `c_Ω·r_Ω(R) ≥ K_win|R| − o(|R|)`, which is the wedge demand floor of node
`[30]` with node `[34]`'s rank substituted for its wedge supply and the
registered cost applied to both sides. -/
noncomputable abbrev ForcedCurvatureCostStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `cor:forced-curvature-cost`, "from `lem:full-rank` and `lem:wedge-lower`":
  -- the exact equality `r_Ω(R) = W₂(R)` of node `[34]` substituted into
  -- node `[30]`'s demand floor (`K .wedgeSupply`'s "in particular"), both
  -- sides multiplied by the registered cost `c_Ω`:
  --   `c_Ω·(δ|R| + 2·2(order−1)p) ≤ c_Ω·r_Ω(R) + c_Ω·2(δ·order·p + T(n))`,
  -- the manuscript's `c_Ω r_Ω(R) ≥ K_win|R| − o(|R|)`, at the packing of
  -- the full-rank fact.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
    packing.card = object.windowPackingNumber data.windowOrder ∧
    data.curvatureCost *
          (data.threshold * (object.remainderSupport packing).card +
            2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
        data.curvatureCost *
            remainderCurvatureTargetRank data object packing +
          data.curvatureCost *
            (2 * (data.threshold * (data.windowOrder * packing.card) +
              data.surplusThreshold object.vertexCount)))

/-- Node `[50]`, yes arm — node `[51]`, the high-entropy remainder branch:
`η(R) ≥ (1/d)·log₂ n`, i.e. the remainder's realized target-complete states
number at least `n^{|R|/d}` (`prop:two-budget` (a)). -/
noncomputable abbrev RemainderEntropyHighStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[50]`, yes -- node `[51]`.  `η(R) ≥ (1/d)·log₂ n`, exponentiated
  -- by `d·|R|`: the remainder's realized states number at least
  -- `n^{|R|/d}`, which is `prop:two-budget` (a)'s own display.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    Graph.AtLeastEntropyRate object.vertexCount data.entropyDenominator
      data.windowOrder data.threshold
      (object.positiveDeficiency (object.remainderSupport packing)
        data.threshold)
      (object.internalEdgeCount (object.remainderSupport packing))
      (object.remainderSupport packing).card)

/-- Node `[50]`, no arm: `η(R) < (1/d)·log₂ n`, the low-entropy branch
`prop:two-budget` (b) and (c) share. -/
noncomputable abbrev RemainderEntropyLowStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[50]`, no.  The exact negation, with the witness exhibited.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      Graph.BelowEntropyRate object.vertexCount data.entropyDenominator
        data.windowOrder data.threshold
        (object.positiveDeficiency (object.remainderSupport packing)
          data.threshold)
        (object.internalEdgeCount (object.remainderSupport packing))
        (object.remainderSupport packing).card)

/-- `prop:two-budget` (b): on the low-entropy residual, the radius-two
rooted-type coordinate lies below the exact finite relabelling threshold. -/
noncomputable abbrev LocalTypeCoordinateRepetitiveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The literal maximum-packing coordinate selected from the full-rank
  -- residual lies below the finite relabelling threshold.
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      remainderCurvatureTargetRank data object packing =
        remainderWedgeSupply object packing ∧
      RemainderTypeCoordinateRepetitive data object packing

/-- `prop:two-budget` (c): the same literal coordinate is not structurally
repetitive.  This arm passes unchanged to the large-budget analysis. -/
noncomputable abbrev LocalTypeCoordinateNonrepetitiveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Exact complementary arm of the same coordinate decision.
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      remainderCurvatureTargetRank data object packing =
        remainderWedgeSupply object packing ∧
      ¬ RemainderTypeCoordinateRepetitive data object packing

/-- `lem:dominant-type`: the repetitive coordinate has a single rooted
radius-two type outside only the registered finite `o(n)` allowance. -/
noncomputable abbrev DominantRootedTypeSchema
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  DominantRootedTypeStatement data object fun _subcubic _root => True

/-- The wedge-free subarm after `lem:dominant-type`; the manuscript makes no
translate-rank claim and passes this arm to the large-budget analysis. -/
noncomputable abbrev DominantRootedTypeWedgeFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  DominantRootedTypeStatement data object fun subcubic root =>
    ¬ DominantRootWedgeClause object subcubic root

/-- The literal incoming wedge subarm of `lem:translates-independent`: the
preceding executor proved the dominant rooted type and the decision found an
internal root wedge in that same type. -/
noncomputable abbrev DominantRootedWedgeTypeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  DominantRootedTypeStatement data object
    (DominantRootWedgeClause object)

/-- Nodes `[51]`--`[52]`, `lem:translates-independent`: a dominant rooted
radius-`r` type with an internal root wedge admits a maximal `2r`-separated
family of translates.  Its radius-`r` balls are disjoint, the radius-`2r`
balls cover the dominant centres, and full obstruction rank gives the exact
finite inequality whose asymptotic form is
`r_Ω(R) ≥ c_r|R| - o(|R|)`. -/
noncomputable abbrev IndependentObstructionTranslatesStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:translates-independent`, in the unconditional finite form stored
  -- on the node `[51]` output ledger.  The registered surplus threshold is
  -- the branch's explicit `o(|R|)` allowance, and the multiplier is the
  -- presentation-parametric form of the manuscript's
  -- `1 + 3(2^(2r)-1)` (the presentation proves `threshold = 3`).
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ radius : Nat, 2 ≤ radius ∧
        (object.remainderSupport packing).card ≤
          (1 + data.threshold *
              ((data.threshold - 1) ^ (2 * radius) - 1)) *
            remainderCurvatureTargetRank data object packing +
              2 * data.surplusThreshold object.vertexCount

/-- Node `[52]`: the window package and the remainder accounting, joined.
`eq:feasibility`'s left-hand side in exact integer form — the joint
window/remainder/curvature coordinate family realizes at least
`2^{rate·p}·n^{|R|/d}·2^{c_Ω·r_Ω(R)}` states. -/
noncomputable abbrev EntropyPackageDemandStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[52]`: `eq:feasibility`'s left-hand side.  Raising the joint
  -- demand to the `d`-th power clears the `1/d` the entropy split carries,
  -- and the high-entropy arm's `n^{|R|} ≤ |𝒢(R)|^d` is substituted for the
  -- remainder factor.  What the inequality says is that the window and
  -- remainder coordinates together realize at least `2^{rate·p}·n^{|R|/d}`
  -- states (`prop:two-budget` (a)).
  ((2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
          (canonicalHotWindows data object).card)) ^ data.entropyDenominator *
      object.vertexCount ^
        (object.remainderSupport (canonicalWindowPacking data object)).card ≤
    jointPackageDemand data object ^ data.entropyDenominator)

/-- Node `[53]`, yes arm — the terminal `[54]`: the remaining non-curvature
budget is strictly smaller than the forced curvature cost, so the joint
package overflows the labelled skeleton budget (`eq:entropy-cap`,
`prop:entropy-high-theta`). -/
noncomputable abbrev EntropyCapActiveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[53]`, yes -- the terminal `[54]`.  `eq:entropy-cap`: the
  -- remaining non-curvature budget is strictly smaller than the forced
  -- curvature cost, i.e. the joint package strictly overflows the labelled
  -- skeleton budget of `lem:near-cubic-budget`.
  Graph.skeletonBudget object < jointPackageDemand data object

/-- Node `[54]`: the independently realized window/remainder code fits in
the labelled skeleton class.  This is the exact bound contradicted by the
active arm of `eq:entropy-cap`. -/
noncomputable abbrev EntropyCapBoundStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[54]`: `lem:independent-target-entropy` and
  -- `lem:skeleton-dominates` bound the exact joint code by the labelled
  -- skeleton budget.  `K .entropyCapActive` is its strict negation.
  jointPackageDemand data object ≤ Graph.skeletonBudget object

/-- Node `[56]`: exact cleared finite form of the large-budget
net-deficiency cap. -/
noncomputable abbrev NetDeficiencyCapStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    packing.card = object.windowPackingNumber data.windowOrder →
    Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate
        data.spineScale data.densitySlack object.vertexCount →
      data.dischargeScale *
          (data.threshold * (data.windowOrder * packing.card) +
            data.spineScale * Core.ceilSqrt object.vertexCount) <
        data.dischargeScale *
            (2 * (data.windowOrder - 1) * packing.card) +
          (object.remainderSupport packing).card)

/-- Nodes `[57]`--`[58]`: `def:net-charge` and `lem:netcharge-superadd`.  The
canonical support decomposition is exact on all three of the charge's terms,
so a remainder of negative net charge has a *connected* admissible support of
negative net charge. -/
noncomputable abbrev NetChargeLocalizationStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Nodes `[57]`--`[58]`.  `lem:netcharge-superadd`'s only consumed
  -- consequence, at the registered discharge scale: the canonical
  -- decomposition is exact on the vertex count, the positive deficiency and
  -- the assigned surplus, so a remainder whose own charge is negative has a
  -- connected piece whose charge is negative.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    object.NegativeNetCharge (object.remainderSupport packing)
        data.threshold data.dischargeScale →
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        object.NegativeNetCharge
          (object.pieceSupport (object.remainderSupport packing) component)
          data.threshold data.dischargeScale)

/-- Node `[59]`, yes arm: `N₀(R) ≥ 0` for the fixed maximum packing
whose complement is the manuscript's remainder `R`. -/
noncomputable abbrev NetChargeNonNegativeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[59]`, yes: the selected maximum packing and the exact assertion
  -- `N₀(R) ≥ 0` for its remainder.  Carrying the packing in the fact keeps
  -- this a test of the paper's fixed `R`, rather than a statement about all
  -- possible maximal packings.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      object.NonNegativeNetCharge (object.remainderSupport packing)
        data.threshold data.dischargeScale)

/-- Node `[59]`, no arm: `N₀(R) < 0` for that same selected packing. -/
noncomputable abbrev NetChargeNegativeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[59]`, no: the same selected maximum packing and `N₀(R) < 0`.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      object.NegativeNetCharge (object.remainderSupport packing)
        data.threshold data.dischargeScale)

/-- Node `[173]`, `lem:exact-collision-test`, no arm: node `[56]`'s
collision, decided exactly on the current object, fails at some maximal
packing — the absorbed-germ residual `[174]`. -/
noncomputable abbrev ExactCollisionFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The exact complement of `K .netChargeCap` (`lem:exact-collision-test`):
  -- some maximal packing's remainder has nonnegative net charge.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
        object.NonNegativeNetCharge (object.remainderSupport packing)
          data.threshold data.dischargeScale)

/-- Node `[174]`, `lem:exact-collision-test`, the consequence of the failed
collision: the failure witness packing `P` of `[173]` satisfies
`n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`, `A = netChargeCoefficient`,
the manuscript's `C ≥ (n − 73|𝒫_hot| − 4(σ_W − σ_R))/73` without subtraction:
the residual carries linearly many cold windows. -/
noncomputable abbrev AbsorbedConfigurationResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[174]`, `lem:exact-collision-test`: at the failure witness
  -- packing, `|R| + s·σ_R ≤ s·def⁺(R)` combined with the exact stub supply
  -- `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W` and
  -- `|R| + order·p = n`, `p = |𝒫_hot| + |𝒫_cold|`, gives the manuscript's
  -- `C ≥ (n − A|𝒫_hot| − s(σ_W − σ_R))/A` with `A = s·(δ·order − 2(order−1)) + order`.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
        object.NonNegativeNetCharge (object.remainderSupport packing)
          data.threshold data.dischargeScale ∧
        object.vertexCount +
            data.dischargeScale *
              object.ambientSurplus (object.remainderSupport packing)
                data.threshold ≤
          data.netChargeCoefficient *
              ((canonicalHotWindows data object).card +
                (canonicalColdWindows data object).card) +
            data.dischargeScale *
              object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
                data.threshold)

/-- Node `[60]`: the large-budget remainder has negative total net charge
once the paper's explicit sufficiently-large predicate holds. -/
noncomputable abbrev NetChargeCapStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
      packing.card = object.windowPackingNumber data.windowOrder →
        object.NegativeNetCharge (object.remainderSupport packing)
          data.threshold data.dischargeScale)

/-- Node `[61]`: `prop:negative-net-charge`.  A connected admissible support
of the remainder carries negative net charge. -/
noncomputable abbrev NegativeSupportStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[61]`, `prop:negative-net-charge`.  The support is data, so what
  -- the ledger records is its existence, with the two clauses of
  -- `def:admissible` the decomposition supplies: it is a connected piece of
  -- the remainder, and its net charge is negative.  The packing is carried
  -- with its maximality, which is what lets node `[27]` be read on the
  -- piece: `def:admissible`'s remaining inherited clauses are statements
  -- about the remainder of a *maximal* packing.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        object.NegativeNetCharge
          (object.pieceSupport (object.remainderSupport packing) component)
          data.threshold data.dischargeScale)

/-- Exact finite orbit lower bound for every normalized remainder support. -/
noncomputable abbrev RemainderRelabelingEntropyStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    ∀ support : Finset object.Vertex,
      support ⊆ object.remainderSupport packing →
      Nat.factorial support.card ≤
        Graph.remainderStateCount data.windowOrder data.threshold
            (object.positiveDeficiency support data.threshold)
            (object.internalEdgeCount support) support.card *
          Nat.card (MulAction.stabilizer
            (Equiv.Perm (Fin support.card))
            (object.labelledInduce support))

/-- Exact finite invariant-state cap under relabellings fixing packed windows. -/
noncomputable abbrev RelabelingDensityCapStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    ∀ labels : object.Vertex ≃ Fin object.vertexCount,
      let window : Finset (Fin object.vertexCount) :=
        (object.windowSupport packing).map labels.toEmbedding
      let remainder : Finset (Fin object.vertexCount) := Finset.univ \ window
      ∀ (State : Type u) (_stateDecidable : DecidableEq State)
          (skeletons : Finset (Graph.LabelledOn object.vertexCount))
          (state : Graph.LabelledOn object.vertexCount → State)
          (stabilizerBound : Nat),
        (∀ permutation : Graph.LabelledRelabeling.FixedSupportPermutations window,
          ∀ graph ∈ skeletons, permutation • graph ∈ skeletons) →
        (∀ permutation : Graph.LabelledRelabeling.FixedSupportPermutations window,
          ∀ graph ∈ skeletons,
            state (permutation • graph) = state graph) →
        (∀ graph ∈ skeletons,
          Nat.card (MulAction.stabilizer
            (Graph.LabelledRelabeling.FixedSupportPermutations window) graph) ≤
              stabilizerBound) →
        (by
          letI : DecidableEq State := _stateDecidable
          exact (skeletons.image state).card * Nat.factorial remainder.card ≤
            skeletons.card * stabilizerBound)

end Hypostructure.Graph.Strategy.Spine
