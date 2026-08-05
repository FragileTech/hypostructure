import Hypostructure.Graph.ColdFirstFailure

/-!
# The cold branch closes

Three manuscript statements, in the order the branch spends them.

`lem:hot-failure-cold-mass`: on `def:surviving-cold-branch`, if the live-hot
entropy comparison does not close then `C ≥ (θ − θ_win)n − o(n)`, because the
hot windows' own package would otherwise exceed the near-cubic skeleton budget.

`lem:cold-germ-extraction`: the cold skeleton's branch excess `b` yields a
family of *pairwise vertex-disjoint* candidate cold bounded germs of size
`N_germ ≥ b/D_cold − o(n)`.  The extraction is greedy independence in the
intersection graph of the candidate supports, whose maximum degree is
`M_cold·B_cold`; that greedy bound is the mathematical content and is proved
here for an arbitrary finite family and overlap relation.

`thm:cold-branch-quantitative-closure`: "no terminal cold branch survives after
the near-cubic spine estimate has been supplied".  Every alternative the germ is
routed to is excluded on the surviving cold branch, so a branch that reaches a
germ has no residual left.

Nothing here is specialized to one manuscript: the greedy bound is about a
`Finset` and a symmetric relation, the mass bound is subtraction-free `Nat`
arithmetic, and the closure is stated against the routing theorems of
`ColdFirstFailure` and `ColdCorridor`.
-/

namespace Hypostructure.Graph.ColdCorridor

open Hypostructure

universe u v

/-! ## Greedy independence

> A greedy maximal independent set in a graph of maximum degree `Δ` has size at
> least the number of vertices divided by `Δ+1`.  With `Δ = M_cold·B_cold`, this
> gives a vertex-disjoint candidate germ family of size
> `N_germ ≥ |𝒢_cand|/(M_cold·B_cold + 1) ≥ b/D_cold − o(n)`.

The bound is stated multiplicatively -- `|family| ≤ |independent| · (Δ+1)` --
so that no division or rounding occurs, and it is proved by the manuscript's own
greedy argument: take a member, discard it and everything it overlaps, recurse.
-/

section Greedy

variable {α : Type u} [DecidableEq α]

/-- A subfamily is *independent* for an overlap relation when no two distinct
members overlap.  For `lem:cold-germ-extraction` the members are candidate germ
supports and overlapping is sharing a vertex, so independence is the pairwise
vertex-disjointness the lemma asks for. -/
def IndependentFor (Overlaps : α → α → Prop) (independent : Finset α) : Prop :=
  ∀ left ∈ independent, ∀ right ∈ independent, left ≠ right →
    ¬ Overlaps left right

/-- **Greedy independence.**

A finite family whose overlap relation is symmetric and has every member
overlapping at most `degree` members contains an independent subfamily whose
size, multiplied by `degree + 1`, covers the whole family.

This is the manuscript's "a greedy maximal independent set in a graph of maximum
degree `Δ` has size at least the number of vertices divided by `Δ+1`", with the
division cleared. -/
theorem exists_independent_card_le_mul (Overlaps : α → α → Prop)
    [DecidableRel Overlaps] (symmetric : ∀ left right, Overlaps left right →
      Overlaps right left) (degree : Nat) :
    ∀ family : Finset α,
      (∀ member ∈ family,
        (family.filter fun other => Overlaps member other).card ≤ degree) →
      ∃ independent ⊆ family, IndependentFor Overlaps independent ∧
        family.card ≤ independent.card * (degree + 1) := by
  classical
  intro family
  induction family using Finset.strongInduction with
  | _ family recurse =>
    intro bounded
    rcases Finset.eq_empty_or_nonempty family with rfl | ⟨chosen, member⟩
    · exact ⟨∅, Finset.Subset.refl _, by simp [IndependentFor], by simp⟩
    -- Discard the chosen member together with everything it overlaps.
    · set blocked : Finset α :=
        family.filter fun other => other = chosen ∨ Overlaps chosen other
        with blockedDef
      have chosenBlocked : chosen ∈ blocked := by
        simp [blockedDef, member]
      have blockedSubset : blocked ⊆ family := Finset.filter_subset _ _
      have blockedCard : blocked.card ≤ degree + 1 := by
        have split : blocked ⊆
            insert chosen (family.filter fun other => Overlaps chosen other) := by
          intro other otherMember
          simp only [blockedDef, Finset.mem_filter] at otherMember
          rcases otherMember.2 with rfl | overlap
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem
              (Finset.mem_filter.2 ⟨otherMember.1, overlap⟩)
        refine le_trans (Finset.card_le_card split) ?_
        refine le_trans (Finset.card_insert_le _ _) ?_
        exact Nat.succ_le_succ (bounded chosen member)
      set rest : Finset α := family \ blocked with restDef
      have restSubset : rest ⊆ family := Finset.sdiff_subset
      have restSmaller : rest ⊂ family := by
        refine Finset.ssubset_iff_of_subset restSubset |>.2 ⟨chosen, member, ?_⟩
        simp [restDef, chosenBlocked]
      obtain ⟨independent, independentSubset, independentFor, cover⟩ :=
        recurse rest restSmaller (fun other otherMember =>
          le_trans (Finset.card_le_card (Finset.filter_subset_filter _ restSubset))
            (bounded other (restSubset otherMember)))
      -- The chosen member overlaps nothing left in `rest`.
      have chosenFree : ∀ other ∈ rest, ¬ Overlaps chosen other := by
        intro other otherMember overlap
        have : other ∈ blocked := by
          simp only [blockedDef, Finset.mem_filter]
          exact ⟨restSubset otherMember, Or.inr overlap⟩
        simp only [restDef, Finset.mem_sdiff] at otherMember
        exact otherMember.2 this
      have chosenNotMem : chosen ∉ independent := by
        intro chosenMember
        have : chosen ∈ rest := independentSubset chosenMember
        simp only [restDef, Finset.mem_sdiff] at this
        exact this.2 chosenBlocked
      refine ⟨insert chosen independent, ?_, ?_, ?_⟩
      · exact Finset.insert_subset member
          (Finset.Subset.trans independentSubset restSubset)
      · intro left leftMember right rightMember different
        simp only [Finset.mem_insert] at leftMember rightMember
        rcases leftMember with leftEq | leftMember
        · rcases rightMember with rightEq | rightMember
          · exact absurd (leftEq.trans rightEq.symm) different
          · subst leftEq
            exact chosenFree right (independentSubset rightMember)
        · rcases rightMember with rightEq | rightMember
          · subst rightEq
            exact fun overlap =>
              chosenFree left (independentSubset leftMember) (symmetric _ _ overlap)
          · exact independentFor left leftMember right rightMember different
      · have decompose : family.card = blocked.card + rest.card := by
          have total := Finset.card_sdiff_add_card_eq_card blockedSubset
          rw [restDef]
          omega
        rw [Finset.card_insert_of_notMem chosenNotMem]
        calc family.card = blocked.card + rest.card := decompose
          _ ≤ (degree + 1) + independent.card * (degree + 1) := by
              exact Nat.add_le_add blockedCard cover
          _ = (independent.card + 1) * (degree + 1) := by ring

end Greedy

/-! ## `lem:hot-failure-cold-mass`

> The hot windows contribute at least `(c_hot − o(1))|𝒫_hot| log₂ n`
> independently target-testable coordinates.  If these coordinates alone exceed
> the near-cubic skeleton budget `(3/2)n log₂ n + o(n log n)`, then the branch
> closes.  Therefore, on a branch where the hot comparison has not closed,
> `c_hot |𝒫_hot| log₂ n ≤ (3/2) n log₂ n + o(n log n)`, so
> `|𝒫_hot| ≤ θ_win n + o(n)` and `C = |𝒫| − |𝒫_hot| ≥ (θ − θ_win) n − o(n)`.

Every `log₂ n` cancels, so the content is one subtraction-free inequality: the
hot bound the unclosed comparison gives, transported across the partition
`𝒫 = 𝒫_hot ⊔ 𝒫_cold`.  No rational and no rounding appears.
-/

/-- **`lem:hot-failure-cold-mass`, cleared of logarithms and division.**

`hotRate` is `c_hot`, `skeletonRate·order + slack` is the near-cubic skeleton
budget with its `o(n log n)`, and `hotBound` is the comparison that has *not*
closed.  The conclusion is `C ≥ (θ − θ_win)n − o(n)` in the form
`hotRate·|𝒫| ≤ hotRate·C + (skeletonRate·n + slack)`: the cold count carries
everything the hot budget could not. -/
theorem hotFailure_coldMass (hotRate skeletonRate order slack : Nat)
    (hotCount coldCount packing : Nat)
    (partition : packing = hotCount + coldCount)
    (hotBound : hotRate * hotCount ≤ skeletonRate * order + slack) :
    hotRate * packing ≤ hotRate * coldCount + (skeletonRate * order + slack) := by
  subst partition
  calc hotRate * (hotCount + coldCount)
      = hotRate * hotCount + hotRate * coldCount := by ring
    _ ≤ (skeletonRate * order + slack) + hotRate * coldCount :=
        Nat.add_le_add_right hotBound _
    _ = hotRate * coldCount + (skeletonRate * order + slack) := by ring

/-! ## `lem:cold-germ-extraction`

> If the cold skeleton has branch excess `b = b(𝔖_cold)`, then it contains a
> family of pairwise vertex-disjoint candidate cold bounded germs of size
> `N_germ ≥ b/D_cold − o(n)`.

The candidate family has `b − o(n)` members by
`lem:cold-corridor-first-failure` — each surviving selected branch-excess
half-edge supplies one canonical first-failure germ — and its intersection graph
has maximum degree at most `M_cold·B_cold`, so greedy independence extracts
`b/D_cold − o(n)` of them with `D_cold = M_cold·B_cold + 1`.
-/

/-- **`lem:cold-germ-extraction`.**

`candidates` is `𝒢_cand`, `Overlaps` is "the two candidate supports share a
vertex", and `boundedOverlap` is the manuscript's degree bound: a candidate
support has at most `M_cold` vertices and a fixed vertex belongs to at most
`B_cold` candidate supports, so a candidate meets at most `M_cold·B_cold`
others.  The conclusion is the extraction, multiplicatively: the candidate
family is covered by the disjoint subfamily times `D_cold`. -/
theorem coldGermExtraction {Germ : Type u} [DecidableEq Germ]
    (Overlaps : Germ → Germ → Prop) [DecidableRel Overlaps]
    (symmetric : ∀ left right, Overlaps left right → Overlaps right left)
    (exchangeBound overlapBound : Nat) (candidates : Finset Germ)
    (boundedOverlap : ∀ candidate ∈ candidates,
      (candidates.filter fun other => Overlaps candidate other).card ≤
        exchangeBound * overlapBound) :
    ∃ disjointFamily ⊆ candidates,
      IndependentFor Overlaps disjointFamily ∧
        candidates.card ≤
          disjointFamily.card * (exchangeBound * overlapBound + 1) :=
  exists_independent_card_le_mul Overlaps symmetric (exchangeBound * overlapBound)
    candidates boundedOverlap

/-- **The extracted family is nonempty as soon as the candidate family is.**

*"Since `D_cold` is a fixed constant and `θ_win < 1/78`, the displayed lower
bound is positive for all sufficiently large `n`; hence at least one bounded
candidate germ is present on every remaining branch."*  This is that step: a
positive candidate count forces a positive disjoint count, so the (F5) partition
cannot be empty. -/
theorem coldGerm_nonempty {Germ : Type u} [DecidableEq Germ]
    {candidates disjointFamily : Finset Germ}
    {denominator : Nat}
    (cover : candidates.card ≤ disjointFamily.card * denominator)
    (positive : 0 < candidates.card) : 0 < disjointFamily.card := by
  by_contra empty
  have : disjointFamily.card = 0 := by omega
  rw [this] at cover
  omega


/-- **The quantitative chain, assembled: at least one bounded candidate germ is
present on every remaining branch.**

> `C ≥ (θ − θ_win)n − o(n)` … The route-8 threshold already gives
> `C ≥ 0.000120334838333602 n − o(n)`, so `C` is linear on every remaining
> branch.  By `lem:cold-window-stub-excess`, `b(𝔖_cold) ≥ 13C − o(n)`, and by
> `lem:cold-germ-extraction`, `N_germ ≥ 13C/D_cold − o(n)`.  … Since `D_cold` is
> a fixed constant and `θ_win < 1/78`, the displayed lower bound is positive for
> all sufficiently large `n`; hence at least one bounded candidate germ is
> present on every remaining branch.

That last sentence is what this theorem proves, and it is what makes the
routing non-vacuous: without it every closure below would be "given a germ,
contradiction", with nothing supplying the germ.

The manuscript's three `o(n)` losses are one registered `slack`, and its "for
all sufficiently large `n`" is `linear`: the cold mass, multiplied by the
per-window branch excess, exceeds twice the accumulated loss.  Every step is
`Nat` and subtraction-free. -/
theorem coldGerm_positive {Germ : Type u} [DecidableEq Germ]
    {candidates disjointFamily : Finset Germ}
    (perWindow coldCount branchExcess denominator slack : Nat)
    -- `lem:cold-window-stub-excess`: `b(𝔖_cold) ≥ 13C − o(n)`.
    (stubExcess : perWindow * coldCount ≤ branchExcess + slack)
    -- `lem:cold-corridor-first-failure`: each surviving selected half-edge
    -- supplies one candidate germ, so `|𝒢_cand| ≥ b − o(n)`.
    (candidateLoss : branchExcess ≤ candidates.card + slack)
    -- `lem:cold-germ-extraction`, the greedy cover.
    (cover : candidates.card ≤ disjointFamily.card * denominator)
    -- "positive for all sufficiently large `n`".
    (linear : 2 * slack < perWindow * coldCount) :
    0 < disjointFamily.card := by
  refine coldGerm_nonempty cover ?_
  omega

/-! ## `thm:cold-branch-quantitative-closure`

> No terminal cold branch survives after the near-cubic spine estimate has been
> supplied.  More precisely, on `def:surviving-cold-branch`, either the route-8
> carrier inequality closes `θ < 1/78`, or the live-hot entropy comparison
> closes, or the hot failure produces a cold family whose branch excess yields a
> bounded germ; that germ is routed by `lem:cold-corridor-first-failure`,
> `lem:cold-bounded-germ-trichotomy`, `lem:cold-same-interface-table` and
> `lem:cold-increment-arithmetic` to a dyadic cycle, a target-defective
> quotient or exit-(4) route, a Type B handoff already in its ledger, a route-8
> closure, or a target-complete compression.  All these outcomes are excluded on
> the surviving cold branch.

The theorem below is the last step: *given* a germ, every branch of the
trichotomy is closed by a clause the branch already carries, so no germ
survives.  With `coldGerm_nonempty` above — which turns a positive candidate
count into a positive disjoint count — that is "the germ trichotomy has no
terminal residual". -/

section Closure

variable {S : DeclaredSignature} {Baseline Target : Graph.FiniteObject.{u} → Prop}
variable {object : Graph.FiniteObject.{u}}

/-- **A length-changing bounded germ cannot survive the branch.**

`lem:cold-bounded-germ-trichotomy`: G1 realizes the target, G2 is a
target-defective quotient, G3 is a target-complete compression of a proper
support.  The G1 and G3 exclusions are *read from the ledger* -- rows 52 and 54
committed them at nodes `[155]` and `[157]` -- rather than re-derived from the
selection and `cor:uncompressible` here, which would prove the trichotomy a
second time.  What is left is G2. -/
theorem boundedGerm_not_survives
    (notRealizing : ∀ germ : BoundedGerm S Baseline Target object,
      ¬ germ.Realizing)
    (notSilent : ∀ germ : BoundedGerm S Baseline Target object,
      germ.increment < 0 → ¬ germ.Neutral)
    (germ : BoundedGerm S Baseline Target object)
    (shorter : germ.increment < 0) :
    germ.Distinguishing := by
  rcases germ.trichotomy with realizing | distinguishing | neutral
  · exact absurd realizing (notRealizing germ)
  · exact distinguishing
  · exact absurd neutral (notSilent germ shorter)

/-- **`thm:cold-branch-quantitative-closure`: the cold branch has no terminal
survivor.**

Every length-changing germ the extraction produces is distinguishing -- the only
branch of the trichotomy the earlier rows have not already closed -- and a
distinguishing germ's identification is a target-defective quotient, which
`def:surviving-cold-branch` (ii) says the branch does not carry.  So a branch
that reaches a germ contradicts its own clause (ii): there is no terminal cold
residual.

This is the statement Row 61 needs, and it is total: no `Option`, no arm
returning "no target". -/
theorem coldBranch_no_terminal_survivor
    (notRealizing : ∀ germ : BoundedGerm S Baseline Target object,
      ¬ germ.Realizing)
    (notSilent : ∀ germ : BoundedGerm S Baseline Target object,
      germ.increment < 0 → ¬ germ.Neutral)
    (branch : SurvivingColdBranch S Baseline Target object)
    (germ : BoundedGerm S Baseline Target object)
    (shorter : germ.increment < 0) :
    False :=
  branch.noGermDefect germ
    (boundedGerm_not_survives notRealizing notSilent germ shorter)

/-! ### The manuscript's orientation

`def:cold-bounded-germ` gives a germ *two* same-interface representatives:
"in a terminal corridor these representatives are the two bounded completion
strands between the same interfaces; in a repeated-state corridor one
representative is the actual corridor segment and the other is the canonical
representative determined by the repeated cold corridor state."  Both are
strands between the same two interfaces of `G`, so each occurs at a support of
the object.

`BoundedGerm` records one occurrence — its `support` — and the other
representative abstractly, as `canonical`.  That is enough for G1 and G2, which
do not care which is which, but G3 replaces "the longer representative by the
shorter one", and a replacement only shrinks the object where the *longer* one
occurs.  So `lem:cold-increment-arithmetic`'s "oriented so `δ ≥ 0`" needs both
occurrences to be nameable, and `OrientedGerm` records them.

With it the orientation is what the manuscript says it is — a naming
convention — and no length-changing germ escapes on a sign. -/

/-- **A cold bounded germ with both of its representatives realized.** -/
structure OrientedGerm (S : DeclaredSignature)
    (Baseline Target : Graph.FiniteObject.{u} → Prop)
    (object : Graph.FiniteObject.{u}) where
  /-- The germ as read at the occurrence of the first representative. -/
  forward : BoundedGerm S Baseline Target object
  /-- The same pair read at the occurrence of the second: the roles of
  `Q[x,y]` and `E` are exchanged. -/
  backward : BoundedGerm S Baseline Target object
  /-- The second reading's *occurrence* has the size of the first reading's
  other representative, and conversely: the roles of `Q[x,y]` and `E` are
  exchanged.  `def:cold-bounded-germ` provides this, because both
  representatives are strands between the same two interfaces of `G` and either
  may be named `E`.

  What is pinned here is the *size* correspondence, which is what the increment
  argument consumes; the two readings sit at different interfaces, so a
  piece-level identity would need an interface correspondence and is not
  asserted.  The closure does not depend on more: `backward` is a genuine germ
  of the object in its own right, so `not_survives` is sound whatever else
  relates the two readings. -/
  exchangedPiece :
    backward.piece.internalVertexCount = forward.canonical.internalVertexCount
  /-- The other half of the exchange. -/
  exchangedCanonical :
    backward.canonical.internalVertexCount = forward.piece.internalVertexCount

namespace OrientedGerm

variable {S : DeclaredSignature} {Baseline Target : Graph.FiniteObject.{u} → Prop}
variable {object : Graph.FiniteObject.{u}}

/-- **Exchanging the two representatives negates the increment.**

`δ := |E| − |Q[x,y]|`, so reading the germ the other way round replaces `δ` by
`−δ`.  This is *derived* from the exchange, not assumed.  Assuming it directly
would have been strictly weaker: `backward.increment = −forward.increment` only
constrains the two increments jointly, while the exchange pins each side's size
against the other's. -/
theorem swapped (germ : OrientedGerm S Baseline Target object) :
    germ.backward.increment = - germ.forward.increment := by
  unfold BoundedGerm.increment
  rw [germ.exchangedPiece, germ.exchangedCanonical]
  omega

/-- **No length-changing cold bounded germ survives — in either orientation.**

`lem:cold-bounded-germ-trichotomy` in full: "No length-changing cold bounded
germ survives on `def:surviving-cold-branch`."  Whichever of the two
representatives is the longer, the germ can be read with that one as the
occurrence being replaced, and the closure applies to that reading.  So the
manuscript's `δ ≥ 0` is a choice of name, not a hypothesis, and `δ ≠ 0` is all
that is required. -/
theorem not_survives
    (notRealizing : ∀ germ : BoundedGerm S Baseline Target object,
      ¬ germ.Realizing)
    (notSilent : ∀ germ : BoundedGerm S Baseline Target object,
      germ.increment < 0 → ¬ germ.Neutral)
    (branch : SurvivingColdBranch S Baseline Target object)
    (germ : OrientedGerm S Baseline Target object)
    (lengthChanging : germ.forward.increment ≠ 0) :
    False := by
  rcases lt_trichotomy germ.forward.increment 0 with shorter | zero | longer
  · -- The first reading already has the shorter representative as the
    -- replacement.
    exact coldBranch_no_terminal_survivor notRealizing notSilent branch
      germ.forward shorter
  · exact lengthChanging zero
  · -- Otherwise read the germ the other way round; `swapped` makes its
    -- increment negative, which is the manuscript's own orientation.
    refine coldBranch_no_terminal_survivor notRealizing notSilent branch
      germ.backward ?_
    rw [germ.swapped]
    omega

end OrientedGerm

/-- **The whole cold branch closes, as `thm:cold-branch-quantitative-closure`
prescribes.**

The manuscript's germ families are three, and all three are impossible on the
surviving cold branch.

*Length-changing germs*, in either orientation: `OrientedGerm.not_survives`.
The trichotomy leaves only G2, and clause (ii) excludes G2; the manuscript's
"oriented so `δ ≥ 0`" is a choice of which representative to name `E`, and
`OrientedGerm` records both occurrences so that choice is always available.

*Equal-length germs* — the rows of `def:cold-same-interface-table` — and *short
self-return exceptions*: `TableRow.row_closed` and `selfReturn_closed` leave
each of them handed off or distinguishing, and a distinguishing row's underlying
germ is excluded by clause (ii) exactly as above.  So such a row is *handed
off*: its charge is in the recorded ledger and nothing is retained at the
corridor.

Together: no bounded germ survives in any family, so the cold branch has no
terminal residual. -/
theorem coldBranch_closed
    {Handoff : Finset object.Vertex → Prop}
    (targetInvariant : Graph.FiniteObject.IsomorphismInvariant Target)
    (notRealizing : ∀ germ : BoundedGerm S Baseline Target object,
      ¬ germ.Realizing)
    (notSilent : ∀ germ : BoundedGerm S Baseline Target object,
      germ.increment < 0 → ¬ germ.Neutral)
    (branch : SurvivingColdBranch S Baseline Target object)
    (avoids : ¬ Target object)
    (uncompressible : ∀ region : Finset object.Vertex,
      ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline Target
        object region) :
    -- No length-changing germ, in *either* orientation: whichever
    -- representative is longer, the germ reads with that one as the occurrence
    -- being replaced.  `lem:cold-bounded-germ-trichotomy` in full.
    (∀ germ : OrientedGerm S Baseline Target object,
      germ.forward.increment ≠ 0 → False) ∧
      -- Every table row is handed off: it cannot be realizing, and it cannot be
      -- distinguishing either, because clause (ii) forbids that.
      (∀ row : TableRow S Baseline Target object Handoff,
        Handoff row.support) := by
  refine ⟨fun germ lengthChanging =>
      OrientedGerm.not_survives notRealizing notSilent branch germ lengthChanging,
    fun row => ?_⟩
  rcases (row_closed targetInvariant avoids uncompressible row).2 with
    handoff | distinguishing
  · exact handoff
  · exact absurd distinguishing (branch.noGermDefect row.toBoundedGerm)

end Closure

end Hypostructure.Graph.ColdCorridor
