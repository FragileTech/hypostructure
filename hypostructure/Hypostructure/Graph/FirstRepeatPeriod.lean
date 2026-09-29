import Hypostructure.Graph.SpliceLift
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Core.DyadicLength

/-!
# F08: the period and the length shift of the first repetition

The ledger certifies that a first repetition of cut states exists along G's
corridors and paths (the cold corridor germ `[153]`/`[187]`, and the repeated
arms of `[162]`, the pair-conditional factorization, route 8 and `[172a]`), but
it never publishes *where* the repetition sits: its period `P` and the length
shift `Δ` of the excision it licenses.  This module publishes both, at G,
vocabulary-free.

1. **The canonical first repetition** (`firstRight`, `firstLeft`, `period`)
   of a state sequence `s : ℕ → α`: least `j`, then least `i`.  In a finite
   state type of size `N`: `j ≤ N`, `1 ≤ P = j − i ≤ N`
   (`firstRight_le_card`, `period_le_card`), the states before `j` are
   pairwise distinct, `i` is the only earlier copy of `s j`, and every pair
   satisfying the ledger's "no earlier repeat" clause *is* the canonical one
   (`eq_first_of_minimal`, `fin_eq_first`).  On the cold germ `[153]`/`[187]`
   this pins the repeated arm's `left`/`right` to the canonical pair with
   `P ≤ Q_cold` (`FirstFailureGermWitness.repeated_period`).

2. **The excision of a path segment** of G (`segment`, `segmentShortcut`):
   positions `i < j` of a path `p` of G, `j − i ≥ 2`, give SpliceLift's
   `Shortcut` with shift exactly `Δ = j − i − 1`; its interior is exactly the
   open position interval `(i, j)` (`mem_interior_segment_iff`).  A cycle of G
   through the segment projects to a cycle of the spliced graph of length
   `ℓ − Δ` (`splice_cycle_project`); every cycle of the excised graph lifts
   to a cycle of G of length `ℓ` or `ℓ + Δ` (SpliceLift).

3. **The periodic block** (`blockShortcuts`): `T` consecutive segments of
   period `P` starting at `i` are compatible, each has shift `P − 1`, and the
   multi-splice lift is exactly `ℓ + (P − 1)·t` with `t ≤ T`
   (`blockShortcuts_cycle_lift`); the multi-excision dichotomy with `1 ≤ t ≤ T`
   (`block_excision_dichotomy`).

4. **Dyadic arithmetic of the progression** `L, L+Δ, …, L+(T−1)Δ`: exact
   membership (`mem_progression_iff`), the doubling period
   `2^(k + ord·n) ≡ 2^k (mod Δ)` (`two_pow_add_orderOf_mul_mod`), the exact
   criterion for the infinite progression to contain a power `2^k`, `k ≥ 2`
   (odd `Δ`: iff `L mod Δ` lies in the doubling orbit,
   `exists_two_pow_in_progression_iff`), the explicit range that forces the hit
   (`two_pow_mem_progression_of_residue`), and the contradiction with `avoids`
   when the progression is realized by cycles of G
   (`false_of_realized_progression`).

5. **The size consequence**: the block excision is strictly smaller than G, and
   the dichotomy is stated with the minimality hypothesis in the shape of
   `ActualContext.not_baseline_swap_of_minimal`
   (`block_excision_dichotomy_of_minimal`).

What is *not* claimed: equality of cut states does not by itself give the
excised object the same boundary response (at G the two prefix readings of an
equal-state pair already differ in `d_∂`, `ColdEqualStates.prefix_profile_ne`);
and the progression of item 4 is a progression of cycles of G only when the
residual supplies it (`realized`).  The excision lemmas use only the path
geometry; the state equality contributes the bound `P ≤ N`.
-/

namespace Hypostructure.Graph.FirstRepeatPeriod

open SimpleGraph Hypostructure Hypostructure.Graph
open Hypostructure.Graph.SpliceLift

set_option linter.unusedSectionVars false

universe u v

/-! ## 1. The canonical first repetition -/

section FirstRepeat

variable {α : Type*}

/-- Position `j` repeats an earlier state. -/
def RepeatsAt (s : ℕ → α) (j : ℕ) : Prop := ∃ i, i < j ∧ s i = s j

/-- **The right end of the first repetition**: the least `j` repeating an
earlier state. -/
noncomputable def firstRight (s : ℕ → α) (h : ∃ j, RepeatsAt s j) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) h

theorem firstRight_spec (s : ℕ → α) (h : ∃ j, RepeatsAt s j) :
    RepeatsAt s (firstRight s h) :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) h

theorem firstRight_le (s : ℕ → α) (h : ∃ j, RepeatsAt s j) {j : ℕ}
    (hj : RepeatsAt s j) : firstRight s h ≤ j :=
  @Nat.find_min' _ (fun _ => Classical.propDecidable _) h j hj

/-- **The left end of the first repetition**: the least `i < firstRight` with
the same state. -/
noncomputable def firstLeft (s : ℕ → α) (h : ∃ j, RepeatsAt s j) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) (firstRight_spec s h)

theorem firstLeft_spec (s : ℕ → α) (h : ∃ j, RepeatsAt s j) :
    firstLeft s h < firstRight s h ∧ s (firstLeft s h) = s (firstRight s h) :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) (firstRight_spec s h)

/-- **The period `P` of the first repetition.** -/
noncomputable def period (s : ℕ → α) (h : ∃ j, RepeatsAt s j) : ℕ :=
  firstRight s h - firstLeft s h

theorem one_le_period (s : ℕ → α) (h : ∃ j, RepeatsAt s j) : 1 ≤ period s h := by
  have := (firstLeft_spec s h).1
  unfold period; omega

theorem period_add_firstLeft (s : ℕ → α) (h : ∃ j, RepeatsAt s j) :
    firstLeft s h + period s h = firstRight s h := by
  have := (firstLeft_spec s h).1
  unfold period; omega

/-- **Before the first repetition every state is new.** -/
theorem distinct_before (s : ℕ → α) (h : ∃ j, RepeatsAt s j) {i j : ℕ}
    (hij : i < j) (hj : j < firstRight s h) : s i ≠ s j := fun same =>
  absurd (firstRight_le s h ⟨i, hij, same⟩) (by omega)

/-- **The left end is the only earlier copy of the repeated state.** -/
theorem firstLeft_unique (s : ℕ → α) (h : ∃ j, RepeatsAt s j) {i : ℕ}
    (hi : i < firstRight s h) (same : s i = s (firstRight s h)) :
    i = firstLeft s h := by
  obtain ⟨lt, eq⟩ := firstLeft_spec s h
  rcases lt_trichotomy i (firstLeft s h) with c | c | c
  · exact absurd (same.trans eq.symm) (distinct_before s h c lt)
  · exact c
  · exact absurd (eq.trans same.symm) (distinct_before s h c hi)

/-- **The first repetition is at most the number of states.**  The states
`s 0, …, s (j−1)` are pairwise distinct. -/
theorem firstRight_le_card [Fintype α] (s : ℕ → α) (h : ∃ j, RepeatsAt s j) :
    firstRight s h ≤ Fintype.card α := by
  have inj : Function.Injective (fun k : Fin (firstRight s h) => s k.1) := by
    intro a b e
    by_contra ne
    rcases Nat.lt_or_gt_of_ne (fun q => ne (Fin.ext q)) with c | c
    · exact distinct_before s h c b.2 e
    · exact distinct_before s h c a.2 e.symm
  simpa using Fintype.card_le_of_injective _ inj

/-- **`P ≤ N`.** -/
theorem period_le_card [Fintype α] (s : ℕ → α) (h : ∃ j, RepeatsAt s j) :
    period s h ≤ Fintype.card α := by
  have := firstRight_le_card s h
  unfold period; omega

/-- **A repetition always occurs by position `N`** (pigeonhole on `N + 1`
states). -/
theorem exists_repeatsAt_le_card [Fintype α] (s : ℕ → α) :
    ∃ j ≤ Fintype.card α, RepeatsAt s j := by
  have card : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by simp
  obtain ⟨a, b, ne, e⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card α + 1) => s k.1) card
  rcases Nat.lt_or_gt_of_ne (fun q => ne (Fin.ext q)) with c | c
  · exact ⟨b.1, by omega, a.1, c, e⟩
  · exact ⟨a.1, by omega, b.1, c, e.symm⟩

theorem hasRepeat [Fintype α] (s : ℕ → α) : ∃ j, RepeatsAt s j := by
  obtain ⟨j, _, hj⟩ := exists_repeatsAt_le_card s
  exact ⟨j, hj⟩

/-- **Every pair satisfying the ledger's "no earlier repeat" clause is the
canonical first repetition.** -/
theorem eq_first_of_minimal (s : ℕ → α) {i j : ℕ} (hij : i < j) (same : s i = s j)
    (first : ∀ i' j', i' < j' → j' < j → s i' ≠ s j') :
    ∃ h : ∃ j, RepeatsAt s j, j = firstRight s h ∧ i = firstLeft s h := by
  have h : ∃ j, RepeatsAt s j := ⟨j, i, hij, same⟩
  have le : firstRight s h ≤ j := firstRight_le s h ⟨i, hij, same⟩
  have eqj : j = firstRight s h := by
    by_contra ne
    obtain ⟨lt, e⟩ := firstLeft_spec s h
    exact first _ _ lt (by omega) e
  refine ⟨h, eqj, ?_⟩
  exact firstLeft_unique s h (by omega) (eqj ▸ same)

/-- A finite state sequence `Fin (n+1) → α` (a corridor's `Segment`s), read as
a sequence on `ℕ` constant after `n`. -/
def extendFin {n : ℕ} (f : Fin (n + 1) → α) : ℕ → α :=
  fun k => f ⟨min k n, by omega⟩

theorem extendFin_apply {n : ℕ} (f : Fin (n + 1) → α) (k : Fin (n + 1)) :
    extendFin f k.1 = f k := by
  unfold extendFin
  congr 1
  ext
  simp only
  have := k.2
  omega

/-- **The Fin form of `eq_first_of_minimal`**, in the exact shape of the
repeated arm of `FirstFailureGermWitness`. -/
theorem fin_eq_first {n : ℕ} (f : Fin (n + 1) → α) (left right : Fin (n + 1))
    (lt : left.1 < right.1) (same : f left = f right)
    (first : ∀ l r : Fin (n + 1), l.1 < r.1 → r.1 < right.1 → f l ≠ f r) :
    ∃ h : ∃ j, RepeatsAt (extendFin f) j,
      right.1 = firstRight (extendFin f) h ∧ left.1 = firstLeft (extendFin f) h := by
  refine eq_first_of_minimal (extendFin f) lt ?_ ?_
  · rw [extendFin_apply, extendFin_apply]; exact same
  · intro i' j' hij hj
    have := right.2
    have e1 := extendFin_apply f ⟨i', by omega⟩
    have e2 := extendFin_apply f ⟨j', by omega⟩
    simp only at e1 e2
    rw [e1, e2]
    exact first _ _ hij hj

end FirstRepeat

/-! ### On the cold germ `[153]`/`[187]` -/

section ColdGerm

open Hypostructure.Graph.ColdCorridor

variable {object : FiniteObject.{u}} {windows component : Finset object.Vertex}

/-- **The period of the cold germ's first repeat.**  In the repeated arm of
G's (F5) germ witness, `(left, right)` is the canonical first repetition of the
corridor's cut states, its period `P = right − left` satisfies
`1 ≤ P ≤ Q_cold`, and the germ occupies at most `P + 1` vertices. -/
theorem FirstFailureGermWitness.repeated_period
    {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (germ : BoundedGerm S Baseline Target object)
    (witness : corridor.FirstFailureGermWitness baselineInvariant targetInvariant
      presentation index germ) :
    (corridor.TerminalCorridor S ∧
        germ.support = corridor.prefixSupport corridor.statesRead) ∨
      ∃ left right : corridor.Segment,
        left.1 < right.1 ∧ right.1 ≤ stateBound S ∧
          presentation.state (index left) = presentation.state (index right) ∧
          1 ≤ right.1 - left.1 ∧ right.1 - left.1 ≤ stateBound S ∧
          germ.support = corridor.intervalSupport left right ∧
          germ.support.card ≤ right.1 - left.1 + 1 ∧
          ∃ h : ∃ j, RepeatsAt (extendFin fun k => presentation.state (index k)) j,
            right.1 = firstRight (extendFin fun k => presentation.state (index k)) h ∧
            left.1 = firstLeft (extendFin fun k => presentation.state (index k)) h := by
  rcases witness.2.2 with terminal | repeated
  · exact Or.inl ⟨terminal.1, terminal.2.1⟩
  · obtain ⟨left, right, rightBound, before, same, _readings, first, supportEq,
      _leftRecord, _rightRecord⟩ := repeated
    refine Or.inr ⟨left, right, before, rightBound, same, by omega, by omega, supportEq,
      ?_, ?_⟩
    · rw [supportEq]; exact corridor.intervalSupport_card_le left right
    · exact fin_eq_first (fun k => presentation.state (index k)) left right before same
        first

end ColdGerm

/-! ## 2. Excising a path segment of G -/

section Segment

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- **The segment of `p` between positions `i ≤ j`**, the ledger's literal
`drop i; take (j − i)`, with its ends named `p.getVert i`, `p.getVert j`. -/
def segment {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl
    (by rw [Walk.drop_getVert, Nat.add_sub_cancel' hij])

theorem segment_length {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ p.length) : (segment p hij).length = j - i := by
  simp only [segment, Walk.length_copy, Walk.take_length, Walk.drop_length]
  omega

theorem segment_getVert {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i ≤ j) (k : ℕ) :
    (segment p hij).getVert k = p.getVert (i + min (j - i) k) := by
  simp only [segment, Walk.getVert_copy, Walk.take_getVert, Walk.drop_getVert]

theorem segment_isPath {x y : V} {p : G.Walk x y} (hp : p.IsPath) {i j : ℕ}
    (hij : i ≤ j) : (segment p hij).IsPath :=
  (Walk.isPath_copy _ _ _).2 ((hp.drop i).take _)

/-- The support of a segment is exactly the positions `[i, j]`. -/
theorem mem_segment_support_iff {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ p.length) (w : V) :
    w ∈ (segment p hij).support ↔ ∃ n, i ≤ n ∧ n ≤ j ∧ p.getVert n = w := by
  rw [Walk.mem_support_iff_exists_getVert, segment_length p hij hj]
  constructor
  · rintro ⟨m, hm, hle⟩
    rw [segment_getVert] at hm
    exact ⟨i + m, by omega, by omega, by rw [← hm]; congr 1; omega⟩
  · rintro ⟨n, hin, hnj, hn⟩
    refine ⟨n - i, ?_, by omega⟩
    rw [segment_getVert, ← hn]; congr 1; omega

/-- **The interior of a segment is exactly the open positions `(i, j)`.** -/
theorem mem_interior_segment_iff {x y : V} {p : G.Walk x y} (hp : p.IsPath)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) (w : V) :
    w ∈ SpliceLift.interior (segment p hij) ↔ ∃ n, i < n ∧ n < j ∧ p.getVert n = w := by
  unfold SpliceLift.interior
  simp only [Set.mem_setOf_eq, mem_segment_support_iff p hij hj]
  constructor
  · rintro ⟨⟨n, hin, hnj, rfl⟩, hi, hjn⟩
    refine ⟨n, ?_, ?_, rfl⟩
    · rcases Nat.lt_or_ge i n with c | c
      · exact c
      · exact absurd (by rw [show n = i by omega]) hi
    · rcases Nat.lt_or_ge n j with c | c
      · exact c
      · exact absurd (by rw [show n = j by omega]) hjn
  · rintro ⟨n, hin, hnj, rfl⟩
    refine ⟨⟨n, by omega, by omega, rfl⟩, fun e => ?_, fun e => ?_⟩
    · have := hp.getVert_injOn (show n ∈ {k | k ≤ p.length} by simp; omega)
        (show i ∈ {k | k ≤ p.length} by simp; omega) e
      omega
    · have := hp.getVert_injOn (show n ∈ {k | k ≤ p.length} by simp; omega)
        (show j ∈ {k | k ≤ p.length} by simp; omega) e
      omega

/-- **Separated segments do not meet**: the interior of `[i₁, j₁]` avoids the
support of `[i₂, j₂]` when the position intervals overlap at most in an end. -/
theorem disjoint_interior_segment {x y : V} {p : G.Walk x y} (hp : p.IsPath)
    {i₁ j₁ i₂ j₂ : ℕ} (h₁ : i₁ ≤ j₁) (h₂ : i₂ ≤ j₂) (hj₁ : j₁ ≤ p.length)
    (hj₂ : j₂ ≤ p.length) (sep : j₁ ≤ i₂ ∨ j₂ ≤ i₁) :
    Disjoint (SpliceLift.interior (segment p h₁)) {w | w ∈ (segment p h₂).support} := by
  rw [Set.disjoint_left]
  intro w hw hw'
  obtain ⟨n, hn1, hn2, rfl⟩ := (mem_interior_segment_iff hp h₁ hj₁ _).1 hw
  obtain ⟨m, hm1, hm2, e⟩ := (mem_segment_support_iff p h₂ hj₂ _).1 hw'
  have := hp.getVert_injOn (show m ∈ {k | k ≤ p.length} by simp; omega)
    (show n ∈ {k | k ≤ p.length} by simp; omega) e
  omega

/-- **The excision of the segment `[i, j]` of a path of G** as SpliceLift's
shortcut.  Its shift is `Δ = j − i − 1` (`segmentShortcut_shift`). -/
def segmentShortcut {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : j ≤ p.length) : Shortcut G where
  a := p.getVert i
  b := p.getVert j
  p := segment p (by omega : i ≤ j)
  isPath := segment_isPath hp _
  two_le := by rw [segment_length p (i := i) (by omega) hj]; omega

theorem segmentShortcut_shift {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : j ≤ p.length) :
    (segmentShortcut p hp hij hj).shift = j - i - 1 := by
  simp only [Shortcut.shift, segmentShortcut, segment_length p (i := i) (by omega) hj]

theorem segmentShortcut_length {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : j ≤ p.length) :
    (segmentShortcut p hp hij hj).p.length = j - i :=
  segment_length p (i := i) (by omega) hj

/-- **Projection: a cycle of G through a path segment is a cycle of the
excised graph, shorter by exactly the shift.**  If `p : a ⇝ b` is a path of
length at least `2` and `q : b ⇝ a` is a path of G avoiding the interior of `p`
and not using the edge `ab`, then the spliced graph has the cycle
`ab · q` of length `(p ++ q).length − (|p| − 1)`. -/
theorem splice_cycle_project {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (q : G.Walk b a) (hq : q.IsPath)
    (avoid : ∀ w ∈ q.support, w ∉ SpliceLift.interior p) (hab : s(a, b) ∉ q.edges) :
    ∃ c : (splice G a b (SpliceLift.interior p)).Walk a a,
      c.IsCycle ∧ c.length + (p.length - 1) = (p.append q).length := by
  have ne : a ≠ b := by
    rintro rfl
    have := Walk.length_eq_zero_iff.2 ((Walk.isPath_iff_nil).1 hp)
    omega
  have hedges : ∀ e ∈ q.edges, e ∈ (splice G a b (SpliceLift.interior p)).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      exact Or.inl ⟨q.adj_of_mem_edges he, avoid x (q.fst_mem_support_of_mem_edges he),
        avoid y (q.snd_mem_support_of_mem_edges he)⟩
  let q' := q.transfer (splice G a b (SpliceLift.interior p)) hedges
  have adj : (splice G a b (SpliceLift.interior p)).Adj a b := Or.inr ⟨rfl, ne⟩
  refine ⟨Walk.cons adj q', ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hq.transfer hedges, ?_⟩
    simpa [q', Walk.edges_transfer] using hab
  · simp only [Walk.length_cons, q', Walk.length_transfer, Walk.length_append]
    omega

end Segment

/-! ## 3. The periodic block: `T` consecutive segments of period `P` -/

section Block

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem block_step {i P k : ℕ} (hP : 2 ≤ P) : i + k * P + 2 ≤ i + (k + 1) * P := by
  rw [Nat.succ_mul]; omega

theorem block_end {i P T k : ℕ} {len : ℕ} (hk : k < T) (hlen : i + T * P ≤ len) :
    i + (k + 1) * P ≤ len := by
  have := Nat.mul_le_mul_right P (show k + 1 ≤ T by omega)
  omega

/-- **The block of `T` consecutive segments `[i + kP, i + (k+1)P]`**, `k < T`,
of a path of G, each as a SpliceLift shortcut of shift `P − 1`. -/
def blockShortcuts {x y : V} (p : G.Walk x y) (hp : p.IsPath) (i P T : ℕ) (hP : 2 ≤ P)
    (hlen : i + T * P ≤ p.length) : List (Shortcut G) :=
  List.ofFn fun k : Fin T =>
    segmentShortcut p hp (i := i + k.1 * P) (j := i + (k.1 + 1) * P) (block_step hP)
      (block_end k.2 hlen)

theorem blockShortcuts_length {x y : V} (p : G.Walk x y) (hp : p.IsPath) (i P T : ℕ)
    (hP : 2 ≤ P) (hlen : i + T * P ≤ p.length) :
    (blockShortcuts p hp i P T hP hlen).length = T := by
  simp [blockShortcuts]

theorem shift_of_mem_blockShortcuts {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (i P T : ℕ) (hP : 2 ≤ P) (hlen : i + T * P ≤ p.length) {s : Shortcut G}
    (hs : s ∈ blockShortcuts p hp i P T hP hlen) : s.shift = P - 1 := by
  simp only [blockShortcuts, List.mem_ofFn] at hs
  obtain ⟨k, rfl⟩ := hs
  rw [segmentShortcut_shift, Nat.succ_mul]
  omega

/-- **The block is compatible** (SpliceLift's `Compatible`): consecutive
segments share only an end. -/
theorem blockShortcuts_compatible {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (i P T : ℕ) (hP : 2 ≤ P) (hlen : i + T * P ≤ p.length) :
    Compatible (blockShortcuts p hp i P T hP hlen) := by
  unfold Compatible blockShortcuts
  rw [List.pairwise_ofFn]
  intro k k' hkk'
  have hk : k.1 < k'.1 := hkk'
  have sep : i + (k.1 + 1) * P ≤ i + k'.1 * P := by
    have := Nat.mul_le_mul_right P (show k.1 + 1 ≤ k'.1 by omega)
    omega
  have a1 := block_end (i := i) k.2 hlen
  have a2 := block_end (i := i) k'.2 hlen
  have s1 : i + k.1 * P ≤ i + (k.1 + 1) * P := by have := block_step (i := i) (k := k.1) hP; omega
  have s2 : i + k'.1 * P ≤ i + (k'.1 + 1) * P := by have := block_step (i := i) (k := k'.1) hP; omega
  exact ⟨disjoint_interior_segment hp s1 s2 a1 a2 (Or.inl sep),
    disjoint_interior_segment hp s2 s1 a2 a1 (Or.inr sep)⟩

theorem interior_subset_delSet {L : List (Shortcut G)} {s : Shortcut G} (hs : s ∈ L) :
    SpliceLift.interior s.p ⊆ delSet L := by
  induction L with
  | nil => simp at hs
  | cons t L ih =>
    intro w hw
    simp only [delSet, Set.mem_union]
    rcases List.mem_cons.1 hs with rfl | hs'
    · exact Or.inl hw
    · exact Or.inr (ih hs' hw)

/-- The first interior vertex of the block, `p.getVert (i + 1)`, is deleted. -/
theorem getVert_succ_mem_delSet {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (i P T : ℕ) (hP : 2 ≤ P) (hT : 1 ≤ T) (hlen : i + T * P ≤ p.length) :
    p.getVert (i + 1) ∈ delSet (blockShortcuts p hp i P T hP hlen) := by
  let k0 : Fin T := ⟨0, hT⟩
  have mem : segmentShortcut p hp (block_step (i := i) (k := 0) hP) (block_end k0.2 hlen) ∈
      blockShortcuts p hp i P T hP hlen :=
    List.mem_ofFn.2 ⟨k0, rfl⟩
  refine interior_subset_delSet mem ?_
  have e : i + (0 + 1) * P ≤ p.length := block_end k0.2 hlen
  have le : i + 0 * P ≤ i + (0 + 1) * P := by omega
  change p.getVert (i + 1) ∈ SpliceLift.interior (segment p le)
  exact (mem_interior_segment_iff hp le e _).2 ⟨i + 1, by omega, by omega, rfl⟩

theorem sum_shift_of_const {L : List (Shortcut G)} {c : ℕ}
    (h : ∀ s ∈ L, s.shift = c) : (L.map Shortcut.shift).sum = c * L.length := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h s List.mem_cons_self, ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    ring

/-- **The period/shift length identity.**  Every cycle of the block-excised
graph lifts to a cycle of G of length exactly `ℓ + (P − 1)·t`, where
`t ≤ T` counts the block segments whose shortcut edge the cycle uses. -/
theorem blockShortcuts_cycle_lift {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (i P T : ℕ) (hP : 2 ≤ P) (hlen : i + T * P ≤ p.length) {z : V}
    (c : (multiSplice G (blockShortcuts p hp i P T hP hlen)).Walk z z) (hc : c.IsCycle) :
    ∃ (t : ℕ) (w : V) (d : G.Walk w w), t ≤ T ∧ d.IsCycle ∧
      d.length = c.length + (P - 1) * t := by
  obtain ⟨S, w, d, hS, hd, hl⟩ :=
    multiSplice_cycle_lift _ (blockShortcuts_compatible p hp i P T hP hlen) c hc
  refine ⟨S.length, w, d, ?_, hd, ?_⟩
  · have := hS.length_le
    rwa [blockShortcuts_length] at this
  · rw [hl, sum_shift_of_const (c := P - 1)
      (fun s hs => shift_of_mem_blockShortcuts p hp i P T hP hlen (hS.subset hs))]

end Block

/-! ## 4. The excision dichotomy with period and shift, at G -/

section Dichotomy

open Classical

/-- **F08 for a periodic block (exact form).**  `G` avoids `LengthOK`; the
block of `T ≥ 1` consecutive segments of period `P ≥ 2` of a path of G is
excised.  Either the excised object misses the baseline, or G has a cycle of
length `L + (P − 1)·t` with `1 ≤ t ≤ T`, `L` accepted and `L + (P − 1)·t` not
accepted.  (`t = 0` is excluded by `avoids`.) -/
theorem block_excision_dichotomy (G : FiniteObject.{u}) {x y : G.Vertex}
    (p : G.graph.Walk x y) (hp : p.IsPath) (i P T : ℕ) (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hlen : i + T * P ≤ p.length)
    (LengthOK : Nat → Prop) (avoids : ¬ HasCycleWithLength LengthOK G)
    (Baseline : FiniteObject.{u} → Prop)
    (minimal : ∀ X : FiniteObject.{u}, Baseline X → X.LexicographicallySmaller G →
      HasCycleWithLength LengthOK X) :
    ¬ Baseline (multiSpliceObject G (blockShortcuts p hp i P T hP hlen)) ∨
    ∃ (t L : ℕ) (w : G.Vertex) (d : G.graph.Walk w w),
      1 ≤ t ∧ t ≤ T ∧ LengthOK L ∧ ¬ LengthOK (L + (P - 1) * t) ∧ d.IsCycle ∧
        d.length = L + (P - 1) * t := by
  by_cases hb : Baseline (multiSpliceObject G (blockShortcuts p hp i P T hP hlen))
  · right
    have small : (multiSpliceObject G (blockShortcuts p hp i P T hP hlen)).LexicographicallySmaller G :=
      FiniteObject.lexicographicallySmaller_of_vertexCount_lt
        (vertexCount_multiSpliceObject_lt G _ _ (getVert_succ_mem_delSet p hp i P T hP hT hlen))
    obtain ⟨z, c, hc, hok⟩ := cycle_of_multiSpliceObject G _ LengthOK (minimal _ hb small)
    obtain ⟨t, w, d, ht, hd, hl⟩ := blockShortcuts_cycle_lift p hp i P T hP hlen c hc
    have t1 : 1 ≤ t := by
      by_contra t0
      have : t = 0 := by omega
      subst this
      exact avoids ⟨⟨w, d, hd, by simpa using hl ▸ hok⟩⟩
    exact ⟨t, c.length, w, d, t1, ht, hok,
      fun hok' => avoids ⟨⟨w, d, hd, hl ▸ hok'⟩⟩, hd, hl⟩
  · exact Or.inl hb

/-- **The size consequence of minimality**: the block excision is strictly
smaller than G. -/
theorem vertexCount_block_lt (G : FiniteObject.{u}) {x y : G.Vertex}
    (p : G.graph.Walk x y) (hp : p.IsPath) (i P T : ℕ) (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hlen : i + T * P ≤ p.length) :
    (multiSpliceObject G (blockShortcuts p hp i P T hP hlen)).vertexCount < G.vertexCount :=
  vertexCount_multiSpliceObject_lt G _ _ (getVert_succ_mem_delSet p hp i P T hP hT hlen)

/-- **The dichotomy with G's minimality in the shape of
`ActualContext.not_baseline_swap_of_minimal`** (`∀ H, H < G → Baseline H →
target`). -/
theorem block_excision_dichotomy_of_minimal (G : FiniteObject.{u}) {x y : G.Vertex}
    (p : G.graph.Walk x y) (hp : p.IsPath) (i P T : ℕ) (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hlen : i + T * P ≤ p.length)
    {LengthOK : Nat → Prop} (avoids : ¬ HasCycleWithLength LengthOK G)
    {Baseline : FiniteObject.{u} → Prop}
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller G →
      Baseline H → HasCycleWithLength LengthOK H) :
    ¬ Baseline (multiSpliceObject G (blockShortcuts p hp i P T hP hlen)) ∨
    ∃ (t L : ℕ) (w : G.Vertex) (d : G.graph.Walk w w),
      1 ≤ t ∧ t ≤ T ∧ LengthOK L ∧ ¬ LengthOK (L + (P - 1) * t) ∧ d.IsCycle ∧
        d.length = L + (P - 1) * t :=
  block_excision_dichotomy G p hp i P T hP hT hlen LengthOK avoids Baseline
    (fun X hb hs => minimal X hs hb)

/-- **A block excision that keeps the baseline is impossible without the
shifted hit**: if the excised object keeps the baseline, G has the cycle of
length `L + (P − 1)·t`. -/
theorem block_shift_hit_of_baseline (G : FiniteObject.{u}) {x y : G.Vertex}
    (p : G.graph.Walk x y) (hp : p.IsPath) (i P T : ℕ) (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hlen : i + T * P ≤ p.length)
    {LengthOK : Nat → Prop} (avoids : ¬ HasCycleWithLength LengthOK G)
    {Baseline : FiniteObject.{u} → Prop}
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller G →
      Baseline H → HasCycleWithLength LengthOK H)
    (keeps : Baseline (multiSpliceObject G (blockShortcuts p hp i P T hP hlen))) :
    ∃ (t L : ℕ) (w : G.Vertex) (d : G.graph.Walk w w),
      1 ≤ t ∧ t ≤ T ∧ LengthOK L ∧ ¬ LengthOK (L + (P - 1) * t) ∧ d.IsCycle ∧
        d.length = L + (P - 1) * t :=
  (block_excision_dichotomy_of_minimal G p hp i P T hP hT hlen avoids minimal).resolve_left
    (fun h => h keeps)

end Dichotomy

/-! ## 5. Dyadic arithmetic of the progression `L + tΔ` -/

section Arithmetic

/-- **Exact membership in the progression `L, L+Δ, …, L+(T−1)Δ`.** -/
theorem mem_progression_iff {L Δ T n : ℕ} (hΔ : 0 < Δ) :
    (∃ t < T, L + t * Δ = n) ↔ L ≤ n ∧ (n - L) % Δ = 0 ∧ n < L + T * Δ := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨by omega, by simp, ?_⟩
    have := Nat.mul_lt_mul_of_pos_right ht hΔ
    omega
  · rintro ⟨hle, hmod, hlt⟩
    have dvd : Δ ∣ n - L := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨t, ht⟩ := dvd
    refine ⟨t, ?_, ?_⟩
    · have : t * Δ < T * Δ := by rw [Nat.mul_comm t]; omega
      exact Nat.lt_of_mul_lt_mul_right this
    · rw [Nat.mul_comm t]; omega

/-- **The doubling orbit is periodic with period `ord_Δ(2)`.** -/
theorem two_pow_add_orderOf_mul_mod (Δ k n : ℕ) :
    2 ^ (k + orderOf (2 : ZMod Δ) * n) % Δ = 2 ^ k % Δ := by
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one]

/-- For odd `Δ`, `2` has positive multiplicative order modulo `Δ`. -/
theorem orderOf_two_pos_of_odd {Δ : ℕ} (hodd : Odd Δ) : 0 < orderOf (2 : ZMod Δ) := by
  have hpos : 0 < Δ := hodd.pos
  haveI : NeZero Δ := ⟨by omega⟩
  have cop : Nat.Coprime 2 Δ := (Nat.coprime_two_left).2 hodd
  have e : ((ZMod.unitOfCoprime 2 cop : (ZMod Δ)ˣ) : ZMod Δ) = 2 := by
    rw [ZMod.coe_unitOfCoprime]; norm_num
  rw [← e, orderOf_units]
  exact orderOf_pos _

/-- **The explicit hit.**  For odd `Δ`, if `L mod Δ` lies in the doubling orbit
(`2^k₀ ≡ L`), then `k = k₀ + ord_Δ(2)·(L + 2)` satisfies `k ≥ 2`,
`2^k ≥ L` and `Δ ∣ 2^k − L`; so the progression of `T` terms contains `2^k` as
soon as `2^k < L + T·Δ`. -/
theorem two_pow_mem_progression_of_residue {L Δ k₀ T : ℕ} (hodd : Odd Δ)
    (res : 2 ^ k₀ % Δ = L % Δ)
    (range : 2 ^ (k₀ + orderOf (2 : ZMod Δ) * (L + 2)) < L + T * Δ) :
    2 ≤ k₀ + orderOf (2 : ZMod Δ) * (L + 2) ∧
      ∃ t < T, L + t * Δ = 2 ^ (k₀ + orderOf (2 : ZMod Δ) * (L + 2)) := by
  have opos := orderOf_two_pos_of_odd hodd
  set k := k₀ + orderOf (2 : ZMod Δ) * (L + 2) with hk
  have kge : L + 2 ≤ k := by
    have := Nat.le_mul_of_pos_left (L + 2) opos
    omega
  have big : L ≤ 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    omega
  refine ⟨by omega, (mem_progression_iff hodd.pos).2 ⟨big, ?_, range⟩⟩
  have hm : 2 ^ k % Δ = L % Δ := by rw [hk, two_pow_add_orderOf_mul_mod]; exact res
  exact Nat.sub_mod_eq_zero_of_mod_eq hm

/-- **The exact hit criterion for the infinite progression**, odd `Δ`: some
term `L + tΔ` is a power `2^k` with `k ≥ 2` iff `L mod Δ` is one of the
`ord_Δ(2)` residues of the doubling orbit. -/
theorem exists_two_pow_in_progression_iff {L Δ : ℕ} (hodd : Odd Δ) :
    (∃ t k, 2 ≤ k ∧ L + t * Δ = 2 ^ k) ↔
      ∃ k < orderOf (2 : ZMod Δ), 2 ^ k % Δ = L % Δ := by
  have opos := orderOf_two_pos_of_odd hodd
  constructor
  · rintro ⟨t, k, _, e⟩
    refine ⟨k % orderOf (2 : ZMod Δ), Nat.mod_lt _ opos, ?_⟩
    have split := two_pow_add_orderOf_mul_mod Δ (k % orderOf (2 : ZMod Δ))
      (k / orderOf (2 : ZMod Δ))
    rw [Nat.mod_add_div] at split
    rw [← split, ← e]
    simp
  · rintro ⟨k₀, _, res⟩
    have big := Nat.lt_two_pow_self (n := k₀ + orderOf (2 : ZMod Δ) * (L + 2))
    have hΔ := hodd.pos
    have range : 2 ^ (k₀ + orderOf (2 : ZMod Δ) * (L + 2)) <
        L + (2 ^ (k₀ + orderOf (2 : ZMod Δ) * (L + 2)) + 1) * Δ := by
      have := Nat.le_mul_of_pos_right (2 ^ (k₀ + orderOf (2 : ZMod Δ) * (L + 2)) + 1) hΔ
      omega
    obtain ⟨two, t, _, e⟩ := two_pow_mem_progression_of_residue hodd res range
    exact ⟨t, _, two, e⟩

/-- **The contradiction with `avoids`.**  If every term `L + tΔ`, `t < T`, is
the length of a cycle of G and some term is accepted, G has an accepted
cycle. -/
theorem false_of_realized_progression (G : FiniteObject.{u}) {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK G) {L Δ T : ℕ}
    (realized : ∀ t < T, ∃ (w : G.Vertex) (d : G.graph.Walk w w),
      d.IsCycle ∧ d.length = L + t * Δ)
    (hit : ∃ t < T, LengthOK (L + t * Δ)) : False := by
  obtain ⟨t, ht, hok⟩ := hit
  obtain ⟨w, d, hd, hl⟩ := realized t ht
  exact avoids ⟨⟨w, d, hd, hl ▸ hok⟩⟩

/-- **The dyadic contradiction.**  A progression of cycle lengths of G with odd
step `Δ`, whose start `L` lies in the doubling orbit modulo `Δ`, and whose `T`
terms reach past `2^(k₀ + ord_Δ(2)(L+2))`, contradicts `avoids` for dyadic
lengths. -/
theorem false_of_realized_dyadic_progression (G : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength G) {L Δ T k₀ : ℕ}
    (realized : ∀ t < T, ∃ (w : G.Vertex) (d : G.graph.Walk w w),
      d.IsCycle ∧ d.length = L + t * Δ)
    (hodd : Odd Δ) (res : 2 ^ k₀ % Δ = L % Δ)
    (range : 2 ^ (k₀ + orderOf (2 : ZMod Δ) * (L + 2)) < L + T * Δ) : False := by
  obtain ⟨two, t, ht, e⟩ := two_pow_mem_progression_of_residue hodd res range
  refine false_of_realized_progression G avoids realized ⟨t, ht, ?_⟩
  rw [e]
  exact Core.DyadicLength.powerOfTwoLength_of_exists ⟨_, two, rfl⟩

end Arithmetic

end Hypostructure.Graph.FirstRepeatPeriod
