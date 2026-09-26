import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SameTokenRoutingGerms

/-!
# Node [144]: what a target-complete identification of two coordinates yields

Scratch analysis (not part of the repository).  All statements are about the
live repository notions `ResidualTargetDefect`, `SparseSurplusExit`,
`ReplacementSupport`, `SameTokenRoutingGerms.Parallel`.
-/

namespace Math144

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u w

open scoped Classical

variable {LengthOK : Nat → Prop} {object : FiniteObject.{u}}

/-- The reading of a declared support `s` on G's own piece at `support`. -/
noncomputable abbrev reading (object : FiniteObject.{u})
    (support s : Finset object.Vertex) :
    BoundaryPiece (SupportAtom.boundary object support) :=
  SupportAtom.retainedPiece object support s

/-- (L1) On a target-avoiding object the "agree in the actual outside context"
conjunct of clause (b) is automatic: both readings glued to `G - Z` are
subgraphs of `G`. -/
theorem actual_context_agreement
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (support s₁ s₂ : Finset object.Vertex) :
    (HasCycleWithLength LengthOK
        (glue (reading object support s₁) (SupportAtom.outside object support)) ↔
      HasCycleWithLength LengthOK
        (glue (reading object support s₂) (SupportAtom.outside object support))) :=
  iff_of_false (not_target_retainedGlue avoids support s₁)
    (not_target_retainedGlue avoids support s₂)

/-- (L1') Survivor dichotomy.  If clause (b) fails for a family, then every two
distinct coordinates of the family are either profile-separated at their
canonical support or **target-complete** (context-equivalent) there.  Thus
"the identification is target-complete" is exactly the state a survivor of
clause (b) is in; it is not an additional event. -/
theorem survivor_dichotomy
    {Coordinate : Type w} {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (noDefect : ¬ ResidualTargetDefect (HasCycleWithLength LengthOK) object
      family coordinateSupport)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {first second : Coordinate} (firstMem : first ∈ family)
    (secondMem : second ∈ family) (different : first ≠ second)
    {support : Finset object.Vertex}
    (selected : CanonicalSupport.select? object
      (coordinateSupport first ∪ coordinateSupport second) = some support) :
    (reading object support (coordinateSupport first)).boundaryDegreeProfile ≠
        (reading object support (coordinateSupport second)).boundaryDegreeProfile ∨
      Response.ContextEquivalent (HasCycleWithLength LengthOK)
        (reading object support (coordinateSupport first))
        (reading object support (coordinateSupport second)) := by
  classical
  by_cases profile :
      (reading object support (coordinateSupport first)).boundaryDegreeProfile =
        (reading object support (coordinateSupport second)).boundaryDegreeProfile
  · right
    intro outside
    by_contra separated
    exact noDefect ⟨first, firstMem, second, secondMem, different, support,
      selected, profile, actual_context_agreement avoids support _ _,
      ⟨outside, separated⟩⟩
  · exact Or.inl profile

/-- (L2) Two coordinates with the same declared support have literally the same
reading, hence are target-complete.  Nothing about the graph is used. -/
theorem contextEquivalent_of_support_eq
    (Target : FiniteObject.{u} → Prop) (support s₁ s₂ : Finset object.Vertex)
    (equal : s₁ = s₂) :
    Response.ContextEquivalent Target (reading object support s₁)
      (reading object support s₂) := by
  subst equal
  intro _
  exact Iff.rfl

/-- (L3) **A target-complete identification of two coordinates adds no sparse
surplus exit.**  For a two-coordinate family whose two readings are
target-complete at their canonical support (in either order), the sparse exits
of the family are exactly the family-independent ones (the exits of the empty
family): (a) dyadic, (c) compression, (d) delocalization, (e) suppression chord.
Hence "target-complete on a proper support ⇒ exit (c)" can only hold if exit (c)
already holds for `G` independently of the two coordinates -- and in a minimal
counterexample `not_replacementSupport` refutes (c) outright. -/
theorem pairExit_iff_emptyExit
    (Baseline : FiniteObject.{u} → Prop)
    {Coordinate : Type w} [DecidableEq Coordinate]
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (a b : Coordinate)
    (targetComplete : ∀ support : Finset object.Vertex,
      CanonicalSupport.select? object
          (coordinateSupport a ∪ coordinateSupport b) = some support →
        Response.ContextEquivalent (HasCycleWithLength LengthOK)
          (reading object support (coordinateSupport a))
          (reading object support (coordinateSupport b))) :
    SparseSurplusExit Baseline (HasCycleWithLength LengthOK) LengthOK object
        ({a, b} : Finset Coordinate) coordinateSupport ↔
      SparseSurplusExit Baseline (HasCycleWithLength LengthOK) LengthOK object
        (∅ : Finset Coordinate) coordinateSupport := by
  constructor
  · intro exit
    cases exit with
    | dyadic cycle => exact .dyadic cycle
    | targetDefect defect =>
        exfalso
        obtain ⟨first, firstMem, second, secondMem, different, support,
          selected, _profile, _actual, ⟨outside, separated⟩⟩ := defect
        simp only [Finset.mem_insert, Finset.mem_singleton] at firstMem secondMem
        rcases firstMem with rfl | rfl <;> rcases secondMem with rfl | rfl
        · exact different rfl
        · exact separated (targetComplete support selected outside)
        · rw [Finset.union_comm] at selected
          exact separated (targetComplete support selected outside).symm
        · exact different rfl
    | compression support replacement => exact .compression support replacement
    | delocalization representative smaller baseline transfer =>
        exact .delocalization representative smaller baseline transfer
    | suppressionChord tvs certificate violates =>
        exact .suppressionChord tvs certificate violates
  · intro exit
    cases exit with
    | dyadic cycle => exact .dyadic cycle
    | targetDefect defect =>
        obtain ⟨first, firstMem, -⟩ := defect
        exact absurd firstMem (Finset.notMem_empty first)
    | compression support replacement => exact .compression support replacement
    | delocalization representative smaller baseline transfer =>
        exact .delocalization representative smaller baseline transfer
    | suppressionChord tvs certificate violates =>
        exact .suppressionChord tvs certificate violates

/-- (L3') The same statement specialised to the only case the [144] text can
guarantee without further geometry: equal declared supports. -/
theorem pairExit_iff_emptyExit_of_support_eq
    (Baseline : FiniteObject.{u} → Prop)
    {Coordinate : Type w} [DecidableEq Coordinate]
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (a b : Coordinate) (equal : coordinateSupport a = coordinateSupport b) :
    SparseSurplusExit Baseline (HasCycleWithLength LengthOK) LengthOK object
        ({a, b} : Finset Coordinate) coordinateSupport ↔
      SparseSurplusExit Baseline (HasCycleWithLength LengthOK) LengthOK object
        (∅ : Finset Coordinate) coordinateSupport :=
  pairExit_iff_emptyExit Baseline coordinateSupport a b fun support _ =>
    contextEquivalent_of_support_eq _ support _ _ equal

/-- (L4) The formal parallel alternative of the [144] dichotomy holds as soon
as the common root already lies in the common selected-port support
`T(p₁) ∪ T(p₂)` -- e.g. a shoulder vertex shared by two ports (blocker type
(a)/(c)).  No response data, no fibre data and no divergence information is
involved: the case is a purely positional one. -/
theorem parallel_of_root_mem {Item : Type u} [DecidableEq Item]
    {left right : List Item} {root : Item} {selected : Finset Item}
    (leftIssued : left.head? = some root) (rightIssued : right.head? = some root)
    (rootSelected : root ∈ selected) :
    SameTokenRoutingGerms.Parallel left right selected := by
  cases left with
  | nil => simp at leftIssued
  | cons l ls =>
    cases right with
    | nil => simp at rightIssued
    | cons r rs =>
      simp only [List.head?_cons, Option.some.injEq] at leftIssued rightIssued
      refine ⟨root, ?_, rootSelected⟩
      rw [leftIssued, rightIssued]
      simp [SameTokenRoutingGerms.commonPrefix,
        SameTokenRoutingGerms.commonPrefixLength]

end Math144

namespace Math144.Trie

/-! ## (P2) Sharp counting for the separator dichotomy

Configurations issued from one root are recorded as their continuations after
the root (lists).  If no common prefix has three distinct next incidences
(every first separator is a *switch*, i.e. `d(z) = 3` for a non-root separator),
the configurations are pairwise non-nested, and all have length at most `n`,
then there are at most `2 ^ n` of them.  A complete binary cubic funnel of depth
`n` attains the bound, so no bound independent of the configuration length
exists. -/

variable {α : Type*} [DecidableEq α]

/-- The next incidence of `l` after the prefix `w`. -/
def next (w l : List α) : Option α := (l.drop w.length).head?

/-- Every common prefix has at most two distinct continuations. -/
def Binary (S : Finset (List α)) : Prop :=
  ∀ w : List α,
    ((S.filter fun l => w <+: l ∧ l ≠ w).image (next w)).card ≤ 2

/-- No configuration is a proper prefix of another. -/
def Antichain (S : Finset (List α)) : Prop :=
  ∀ l₁ ∈ S, ∀ l₂ ∈ S, l₁ <+: l₂ → l₁ = l₂

theorem card_le_pow (n : Nat) :
    ∀ S : Finset (List α), (∀ l ∈ S, l.length ≤ n) → Antichain S → Binary S →
      S.card ≤ 2 ^ n := by
  induction n with
  | zero =>
    intro S short _ _
    have : S ⊆ {[]} := by
      intro l hl
      have := short l hl
      simp_all [List.length_eq_zero_iff]
    calc S.card ≤ ({[]} : Finset (List α)).card := Finset.card_le_card this
      _ = 2 ^ 0 := by simp
  | succ n ih =>
    intro S short anti binary
    by_cases nilMem : ([] : List α) ∈ S
    · have : S ⊆ {[]} := by
        intro l hl
        have := anti [] nilMem l hl (List.nil_prefix)
        simp [← this]
      calc S.card ≤ ({[]} : Finset (List α)).card := Finset.card_le_card this
        _ = 1 := by simp
        _ ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    · -- split by head
      have heads := binary []
      have filterEq : (S.filter fun l => ([] : List α) <+: l ∧ l ≠ []) = S := by
        apply Finset.filter_true_of_mem
        intro l hl
        exact ⟨List.nil_prefix, fun h => nilMem (h ▸ hl)⟩
      rw [filterEq] at heads
      -- fibres
      have fibre : ∀ h ∈ S.image (next []),
          (S.filter fun l => next [] l = h).card ≤ 2 ^ n := by
        intro h hmem
        obtain ⟨l0, l0mem, rfl⟩ := Finset.mem_image.mp hmem
        cases l0 with
        | nil => exact absurd l0mem nilMem
        | cons a t0 =>
          let F := S.filter fun l => next [] l = next [] (a :: t0)
          let T := F.image List.tail
          have consOf : ∀ l ∈ F, l = a :: l.tail := by
            intro l hl
            obtain ⟨lS, lnext⟩ := Finset.mem_filter.mp hl
            cases l with
            | nil => exact absurd lS nilMem
            | cons b u =>
              simp [next] at lnext
              simp [lnext]
          have injOn : Set.InjOn List.tail (F : Set (List α)) := by
            intro l₁ h₁ l₂ h₂ eq
            rw [consOf l₁ h₁, consOf l₂ h₂, eq]
          have memT : ∀ u, u ∈ T ↔ a :: u ∈ S := by
            intro u
            constructor
            · intro hu
              obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
              have := consOf l hl
              rw [← this]
              exact (Finset.mem_filter.mp hl).1
            · intro hu
              refine Finset.mem_image.mpr ⟨a :: u, ?_, rfl⟩
              exact Finset.mem_filter.mpr ⟨hu, by simp [next]⟩
          have cardEq : F.card = T.card := (Finset.card_image_of_injOn injOn).symm
          change F.card ≤ 2 ^ n
          rw [cardEq]
          apply ih T
          · intro u hu
            have := short _ ((memT u).mp hu)
            simp at this
            omega
          · intro u₁ h₁ u₂ h₂ pre
            have := anti _ ((memT u₁).mp h₁) _ ((memT u₂).mp h₂)
              ((List.prefix_cons_inj a).mpr pre)
            simpa using this
          · intro w
            have hb := binary (a :: w)
            refine le_trans (le_of_eq ?_) hb
            -- the continuation sets coincide under `cons a`
            congr 1
            ext o
            simp only [Finset.mem_image, Finset.mem_filter]
            constructor
            · rintro ⟨u, ⟨hu, pre, ne⟩, rfl⟩
              refine ⟨a :: u, ⟨(memT u).mp hu, (List.prefix_cons_inj a).mpr pre,
                by simpa using ne⟩, ?_⟩
              simp [next]
            · rintro ⟨l, ⟨hl, pre, ne⟩, rfl⟩
              obtain ⟨u, rfl⟩ : ∃ u, l = a :: u := by
                obtain ⟨r, hr⟩ := pre
                exact ⟨w ++ r, by simp [← hr]⟩
              refine ⟨u, ⟨(memT u).mpr hl, (List.prefix_cons_inj a).mp pre,
                by simpa using ne⟩, ?_⟩
              simp [next]
      calc S.card = ∑ h ∈ S.image (next []), (S.filter fun l => next [] l = h).card :=
            Finset.card_eq_sum_card_image (next []) S
        _ ≤ ∑ _h ∈ S.image (next []), 2 ^ n := Finset.sum_le_sum fibre
        _ = (S.image (next [])).card * 2 ^ n := by simp
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ heads
        _ = 2 ^ (n + 1) := by ring

/-- Contrapositive, the form [144] would use: more than `2 ^ n` pairwise
non-nested configurations of length `≤ n` from one root force a common prefix
with three distinct next incidences, i.e. a first separator of degree `≥ 4`
(when the separator is not the root itself). -/
theorem exists_three_way_branch (n : Nat) (S : Finset (List α))
    (short : ∀ l ∈ S, l.length ≤ n) (anti : Antichain S)
    (large : 2 ^ n < S.card) :
    ∃ w : List α,
      2 < ((S.filter fun l => w <+: l ∧ l ≠ w).image (next w)).card := by
  by_contra none
  simp only [not_exists, not_lt] at none
  exact absurd (card_le_pow n S short anti none) (by omega)

end Math144.Trie

/-! ## Axiom audit -/
#print axioms Math144.pairExit_iff_emptyExit
#print axioms Math144.pairExit_iff_emptyExit_of_support_eq
#print axioms Math144.survivor_dichotomy
#print axioms Math144.parallel_of_root_mem
#print axioms Math144.Trie.card_le_pow
#print axioms Math144.Trie.exists_three_way_branch
