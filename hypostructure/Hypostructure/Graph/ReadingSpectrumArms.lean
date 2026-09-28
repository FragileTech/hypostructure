import Hypostructure.Graph.ReadingCounts
import Hypostructure.Graph.SingleEdgeContext

/-!
# Arm (i) of the path-spectrum split, refined, and outside returns of a support

Two readings `ret_P`, `ret_N` of a support `Z` with equal boundary-degree
profiles, glued to a context `O` in which `ret_P` has an accepted cycle and
`ret_N` has none, split by the path spectrum.  On arm (i) (labels `a ≠ b`, a
reading path `π : a → b`, a context path `σ : b → a`, `|π| + |σ| = 2^k`, and no
`ret_N` path reproduces the length or the sum) the configuration is much more
rigid: the two labels are active in both readings, `π` carries a private edge
of `ret_P`, `|π| ≥ 2`; at an adjacent pair `a ~ b` also `|σ| ≥ 2`, and the
residues and outside closures are fixed; when `|σ| = 1` the single-edge context
`a — b` separates the readings.

Also: a vertex of degree exactly the baseline in a support `Z` with an outside
neighbour has an outside return to another vertex of `Z` (on a connected
bridgeless object with no proper baseline subgraph).

All results are vocabulary-free.
-/

namespace Hypostructure.Graph.ReadingSpectrumArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ReadingCounts
open Hypostructure.Graph.SingleEdgeContext

universe u

section ArmOne

variable {G : FiniteObject.{u}}

open Core.DyadicLength in
/-- **Arm (i), refined** (vocabulary-free).  Two readings of `Z` with equal
profiles; labels `a ≠ b`; a path `π : a → b` of `ret_P`; an `O`-path
`σ : b → a` with `|π| + |σ| = 2^k`; and every `a → b` path `π'` of `ret_N` has
`|π'| ≠ |π|` and `|π'| + |σ|` never a power `2^j` (`j ≥ 2`).  Then
(1) `a, b` are active: both reading counts positive, both in `P ∩ N`;
(2) `π` uses an edge of `ret_P` that is not an edge of `ret_N` (a private edge);
(3) `|π| ≥ 2`;
(4) if `a ~ b` in `G` (and `G` has return avoidance), then `|σ| ≥ 2`,
`|π| + 1` and `|σ| + 1` are not accepted. -/
theorem armOne_refined {Z P N : Finset G.Vertex}
    {O : OutsideContext (SupportAtom.boundary G Z)}
    (prof : (SupportAtom.retainedPiece G Z P).boundaryDegreeProfile =
      (SupportAtom.retainedPiece G Z N).boundaryDegreeProfile)
    {a b : (SupportAtom.boundary G Z).Vertex} (ab : a ≠ b)
    (π : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl a) (.inl b)) (hπ : π.IsPath)
    (σ : O.graph.Walk (.inl b) (.inl a)) (hσ : σ.IsPath)
    {k : Nat} (hk : 2 ≤ k) (sum : π.length + σ.length = 2 ^ k)
    (spec : ∀ π' : (SupportAtom.retainedPiece G Z N).graph.Walk (.inl a) (.inl b),
      π'.IsPath → π'.length ≠ π.length ∧ ∀ j, 2 ≤ j → π'.length + σ.length ≠ 2 ^ j) :
    (0 < readingCount Z P a ∧ 0 < readingCount Z P b ∧
      a.1 ∈ P ∧ b.1 ∈ P ∧ a.1 ∈ N ∧ b.1 ∈ N) ∧
    (∃ e ∈ π.edges, e ∉ (SupportAtom.retainedPiece G Z N).graph.edgeSet) ∧
    2 ≤ π.length ∧
    ((∀ dart : G.graph.Dart,
        Disjoint (returnLengthSet G dart) (shiftedAcceptedSet PowerOfTwoLength)) →
      G.graph.Adj a.1 b.1 →
      2 ≤ σ.length ∧ ¬ PowerOfTwoLength (π.length + 1) ∧
        ¬ PowerOfTwoLength (σ.length + 1)) := by
  classical
  -- (1) activity at a generic label from a first edge
  have firstActive : ∀ {x y : (SupportAtom.boundary G Z).Vertex}
      (p : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl x) (.inl y)), x ≠ y →
      0 < readingCount Z P x := by
    intro x y p xy
    cases p with
    | nil => exact absurd rfl xy
    | cons h _ =>
      have mem := GluedReadings.retained_adj_mem h
      unfold readingCount
      exact (Set.ncard_pos (Set.toFinite _)).2
        ⟨_, pieceDecode_mem Z _, h.1, mem.1, mem.2⟩
  have aP := firstActive π ab
  have bP := firstActive π.reverse ab.symm
  have counts := (profile_eq_iff_counts Z P N).1 prof
  have aN := readingCount_pos (show 0 < readingCount Z N a by rw [← counts a]; exact aP)
  have bN := readingCount_pos (show 0 < readingCount Z N b by rw [← counts b]; exact bP)
  have aP' := readingCount_pos aP
  have bP' := readingCount_pos bP
  -- the edge `ab` in `ret_N` when `a ~ b`
  have edgeN : G.graph.Adj a.1 b.1 →
      (SupportAtom.retainedPiece G Z N).graph.Adj (.inl a) (.inl b) := by
    intro adj
    refine ⟨adj, ?_⟩
    simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
    exact ⟨fun h => ab (Subtype.ext h), Or.inl ⟨aN.1, bN.1⟩⟩
  have lenPos : 1 ≤ π.length := by
    rcases π with _ | ⟨_, _⟩
    · exact absurd rfl ab
    · simp
  have two : 2 ≤ π.length := by
    by_contra lt
    have one : π.length = 1 := by omega
    cases π with
    | nil => exact absurd rfl ab
    | cons h r =>
      cases r with
      | cons h' r' => simp at one
      | nil =>
        have adj : G.graph.Adj a.1 b.1 := h.1
        have hp : (SimpleGraph.Walk.cons (edgeN adj) .nil :
            (SupportAtom.retainedPiece G Z N).graph.Walk (.inl a) (.inl b)).IsPath := by
          simp [SimpleGraph.Walk.cons_isPath_iff, ab]
        exact (spec _ hp).1 (by simp)
  refine ⟨⟨aP, bP, aP'.1, bP'.1, aN.1, bN.1⟩, ?_, two, ?_⟩
  · by_contra none
    push Not at none
    have edgesIn : ∀ e ∈ π.edges, e ∈ (SupportAtom.retainedPiece G Z N).graph.edgeSet :=
      fun e he => none e he
    exact (spec (π.transfer _ edgesIn) (hπ.transfer edgesIn)).1
      (SimpleGraph.Walk.length_transfer _ _)
  · intro returnAvoidance adj
    -- `|σ| + 1` is not accepted: the single edge `ab` of `ret_N`
    have hp : (SimpleGraph.Walk.cons (edgeN adj) .nil :
        (SupportAtom.retainedPiece G Z N).graph.Walk (.inl a) (.inl b)).IsPath := by
      simp [SimpleGraph.Walk.cons_isPath_iff, ab]
    have sigmaNot : ¬ PowerOfTwoLength (σ.length + 1) := by
      intro h
      obtain ⟨j, hj, eq⟩ := (powerOfTwoLength_iff _).1 h
      exact (spec _ hp).2 j hj (by simp; omega)
    -- `|π| + 1` is not accepted: `π + ab` is a cycle of `G`
    have fresh : s(.inl a, .inl b) ∉ π.edges := by
      intro mem
      obtain ⟨h, r, hr⟩ := path_first_edge π hπ mem
      have rnil : r.length = 0 := by
        have rp : r.IsPath := by
          have := hπ; rw [hr] at this
          exact ((SimpleGraph.Walk.cons_isPath_iff h r).1 this).1
        cases r with
        | nil => rfl
        | cons h' r' =>
          exfalso
          have := rp.support_nodup
          simp only [SimpleGraph.Walk.support_cons] at this
          exact (List.nodup_cons.1 this).1 (SimpleGraph.Walk.end_mem_support _)
      have := congrArg SimpleGraph.Walk.length hr
      simp [rnil] at this
      omega
    have piNot : ¬ PowerOfTwoLength (π.length + 1) :=
      no_spectrum_of_adj (L := PowerOfTwoLength) returnAvoidance adj.symm π hπ fresh
    have sigmaPos : 1 ≤ σ.length := by
      rcases σ with _ | ⟨_, _⟩
      · exact absurd rfl ab
      · simp
    refine ⟨?_, piNot, sigmaNot⟩
    by_contra lt
    have one : σ.length = 1 := by omega
    exact piNot ((powerOfTwoLength_iff _).2 ⟨k, hk, by omega⟩)


end ArmOne

open Classical in
/-- **The outside never realizes `σ`** (vocabulary-free): a path `π : a → b` of a
reading, of length `≥ 2`, and a `G`-path `τ : b → a` with interior outside `Z`
never sum to an accepted length. -/
theorem reading_outside_noSum {G : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength G)
    {Z R : Finset G.Vertex} {a b : (SupportAtom.boundary G Z).Vertex}
    (π : (SupportAtom.retainedPiece G Z R).graph.Walk (.inl a) (.inl b)) (hπ : π.IsPath)
    (two : 2 ≤ π.length) (τ : G.graph.Walk b.1 a.1) (hτ : τ.IsPath)
    (out : ∀ v ∈ τ.support, v ∉ Z ∨ v = a.1 ∨ v = b.1) :
    ¬ Core.DyadicLength.PowerOfTwoLength (π.length + τ.length) := by
  letI : FinEnum G.Vertex := G.vertices
  have hp : (π.map (readingHom Z R)).IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective (readingHom_injective Z R) hπ
  have hlen : (π.map (readingHom Z R)).length = π.length :=
    SimpleGraph.Walk.length_map _ _
  have pZ : ∀ v ∈ (π.map (readingHom Z R)).support, v ∈ Z := by
    intro v hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hv
    exact pieceDecode_mem Z x
  have := GluedReadings.no_target_two_sides G avoids Z
    (Finset.univ.filter fun v => v ∉ Z ∨ v = a.1 ∨ v = b.1)
    (fun v h1 h2 => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
      rcases h2 with h | h | h
      · exact absurd h1 h
      · exact Or.inl h
      · exact Or.inr h)
    (π.map (readingHom Z R)) hp pZ τ hτ (fun v hv => by simpa using out v hv)
    (Or.inl (by rw [hlen]; omega))
  rwa [hlen] at this

/-- **Arm (i) with `|σ| = 1` is a single-edge separation** (vocabulary-free):
then `a ≁ b`, `glue ret_P (a — b)` is positive and `glue ret_N (a — b)` is
negative. -/
theorem armOne_sigma_one {G : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength G)
    {Z P N : Finset G.Vertex} {O : OutsideContext (SupportAtom.boundary G Z)}
    {a b : (SupportAtom.boundary G Z).Vertex} (ab : a ≠ b)
    (π : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl a) (.inl b)) (hπ : π.IsPath)
    (σ : O.graph.Walk (.inl b) (.inl a))
    {k : Nat} (hk : 2 ≤ k) (sum : π.length + σ.length = 2 ^ k)
    (spec : ∀ π' : (SupportAtom.retainedPiece G Z N).graph.Walk (.inl a) (.inl b),
      π'.IsPath → π'.length ≠ π.length ∧ ∀ j, 2 ≤ j → π'.length + σ.length ≠ 2 ^ j)
    (adjClause : G.graph.Adj a.1 b.1 → 2 ≤ σ.length)
    (one : σ.length = 1) :
    ¬ G.graph.Adj a.1 b.1 ∧
      HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
        (glue (SupportAtom.retainedPiece G Z P) (edgeContext Z a b)) ∧
      ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
        (glue (SupportAtom.retainedPiece G Z N) (edgeContext Z a b)) := by
  have nadj : ¬ G.graph.Adj a.1 b.1 := fun adj => by have := adjClause adj; omega
  have freshOf : ∀ {R : Finset G.Vertex}
      (p : (SupportAtom.retainedPiece G Z R).graph.Walk (.inl a) (.inl b)),
      s(.inl a, .inl b) ∉ p.edges := by
    intro R p mem
    exact nadj (p.adj_of_mem_edges mem).1
  refine ⟨nadj, ?_, ?_⟩
  · exact edgeContext_cycle_of_path ab π hπ (freshOf π)
      ((Core.DyadicLength.powerOfTwoLength_iff _).2 ⟨k, hk, by omega⟩)
  · intro cyc
    obtain ⟨p, hp, -, hl⟩ := path_of_edgeContext_cycle avoids cyc
    obtain ⟨j, hj, eq⟩ := (Core.DyadicLength.powerOfTwoLength_iff _).1 hl
    exact (spec p hp).2 j hj (by omega)

open Core.DyadicLength in
/-- **Residue classes at an adjacent pair**: `|π|, |σ| ≥ 2`, `|π| + |σ| = 2^k`, neither
`|π| + 1` nor `|σ| + 1` accepted leaves exactly the four classes
`(|π|, |σ|) ≡ (0,0), (1,3), (2,2), (3,1) (mod 4)`. -/
theorem adj_residues {p s k : Nat} (hk : 2 ≤ k) (sum : p + s = 2 ^ k) :
    (p % 4 = 0 ∧ s % 4 = 0) ∨ (p % 4 = 1 ∧ s % 4 = 3) ∨
      (p % 4 = 2 ∧ s % 4 = 2) ∨ (p % 4 = 3 ∧ s % 4 = 1) := by
  have : (2 ^ k) % 4 = 0 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add]; simp [Nat.mul_mod_right]
  omega


open Classical in
/-- **Outside theta at an adjacent pair** (vocabulary-free): with `a ~ b` both in `Z`, every
`G`-path `τ : b → a` with interior outside `Z` and `|τ| ≥ 2` has `|τ| + 1` not
accepted (it closes with the edge `ab`). -/
theorem adj_outside {G : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength G)
    {Z : Finset G.Vertex} {a b : G.Vertex} (aZ : a ∈ Z) (bZ : b ∈ Z) (adj : G.graph.Adj a b)
    (τ : G.graph.Walk b a) (hτ : τ.IsPath) (out : ∀ v ∈ τ.support, v ∉ Z ∨ v = a ∨ v = b)
    (long : 2 ≤ τ.length) :
    ¬ Core.DyadicLength.PowerOfTwoLength (τ.length + 1) := by
  letI : FinEnum G.Vertex := G.vertices
  have e : (SimpleGraph.Walk.cons adj .nil : G.graph.Walk a b).IsPath := by
    simp [SimpleGraph.Walk.cons_isPath_iff, adj.ne]
  have := GluedReadings.no_target_two_sides G avoids Z
    (Finset.univ.filter fun v => v ∉ Z ∨ v = a ∨ v = b)
    (fun v h1 h2 => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
      rcases h2 with h | h | h
      · exact absurd h1 h
      · exact Or.inl h
      · exact Or.inr h)
    (.cons adj .nil) e (fun v hv => by
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact aZ
      · exact bZ)
    τ hτ (fun v hv => by simpa using out v hv) (Or.inr (by omega))
  simpa [Nat.add_comm] using this


/-- **Arm (i) of the spectrum split, refined** (vocabulary-free), at readings
`P`, `N` of `Z` and a context `O`: labels `a ≠ b` of `∂Z`, a path `π : a → b` of
`ret_P` and an `O`-path `σ : b → a` meeting no other label with
`|π| + |σ| = 2^k` (`k ≥ 2`), every `a → b` path `π'` of `ret_N` having
`|π'| ≠ |π|` and `|π'| + |σ|` never a power `2^j` (`j ≥ 2`); and then:
`a, b` are active in `P` and lie in `P ∩ N`; `π` uses an edge of `ret_P` that is
not an edge of `ret_N`; `|π| ≥ 2`; if `a ~ b`, then `|σ| ≥ 2`, neither
`|π| + 1` nor `|σ| + 1` is a power of two, `(|π|, |σ|) mod 4` is one of
`(0,0), (1,3), (2,2), (3,1)`, and no path `τ : b → a` with interior outside `Z`
and `|τ| ≥ 2` has `|τ| + 1` a power of two; no such outside path `τ` has
`|π| + |τ|` a power of two or `|τ| = |σ|`; and if `|σ| = 1`, then `a ≁ b` and
the single-edge context `a — b` separates the readings (`ret_P` positive,
`ret_N` negative). -/
def ArmOneRefined {G : FiniteObject.{u}} (Z P N : Finset G.Vertex)
    (O : OutsideContext (SupportAtom.boundary G Z)) : Prop :=
  ∃ a b : (SupportAtom.boundary G Z).Vertex, a ≠ b ∧
    ∃ π : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl a) (.inl b), π.IsPath ∧
    ∃ σ : O.graph.Walk (.inl b) (.inl a), σ.IsPath ∧
      (∀ d, (Sum.inl d : _ ⊕ O.Internal) ∈ σ.support → d = a ∨ d = b) ∧
      (∃ k, 2 ≤ k ∧ π.length + σ.length = 2 ^ k) ∧
      (∀ π' : (SupportAtom.retainedPiece G Z N).graph.Walk (.inl a) (.inl b),
        π'.IsPath → π'.length ≠ π.length ∧ ∀ j, 2 ≤ j → π'.length + σ.length ≠ 2 ^ j) ∧
      (0 < ReadingCounts.readingCount Z P a ∧ 0 < ReadingCounts.readingCount Z P b ∧
        a.1 ∈ P ∧ b.1 ∈ P ∧ a.1 ∈ N ∧ b.1 ∈ N) ∧
      (∃ e ∈ π.edges, e ∉ (SupportAtom.retainedPiece G Z N).graph.edgeSet) ∧
      2 ≤ π.length ∧
      (G.graph.Adj a.1 b.1 → 2 ≤ σ.length ∧
        ¬ Core.DyadicLength.PowerOfTwoLength (π.length + 1) ∧
        ¬ Core.DyadicLength.PowerOfTwoLength (σ.length + 1) ∧
        ((π.length % 4 = 0 ∧ σ.length % 4 = 0) ∨ (π.length % 4 = 1 ∧ σ.length % 4 = 3) ∨
          (π.length % 4 = 2 ∧ σ.length % 4 = 2) ∨ (π.length % 4 = 3 ∧ σ.length % 4 = 1)) ∧
        ∀ τ : G.graph.Walk b.1 a.1, τ.IsPath →
          (∀ v ∈ τ.support, v ∉ Z ∨ v = a.1 ∨ v = b.1) → 2 ≤ τ.length →
          ¬ Core.DyadicLength.PowerOfTwoLength (τ.length + 1)) ∧
      (∀ τ : G.graph.Walk b.1 a.1, τ.IsPath →
        (∀ v ∈ τ.support, v ∉ Z ∨ v = a.1 ∨ v = b.1) →
        ¬ Core.DyadicLength.PowerOfTwoLength (π.length + τ.length) ∧ τ.length ≠ σ.length) ∧
      (σ.length = 1 → ¬ G.graph.Adj a.1 b.1 ∧
        HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
          (glue (SupportAtom.retainedPiece G Z P) (SingleEdgeContext.edgeContext Z a b)) ∧
        ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
          (glue (SupportAtom.retainedPiece G Z N) (SingleEdgeContext.edgeContext Z a b)))

/-- **Arm (i) refines** (vocabulary-free): on a target-avoiding object with
return avoidance, every arm-(i) configuration of two readings with equal
profiles is an `ArmOneRefined` configuration. -/
theorem armOneRefined_of_arm {G : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength G)
    (returnAvoidance : ∀ dart : G.graph.Dart,
      Disjoint (returnLengthSet G dart)
        (shiftedAcceptedSet Core.DyadicLength.PowerOfTwoLength))
    {Z P N : Finset G.Vertex} {O : OutsideContext (SupportAtom.boundary G Z)}
    (prof : (SupportAtom.retainedPiece G Z P).boundaryDegreeProfile =
      (SupportAtom.retainedPiece G Z N).boundaryDegreeProfile)
    {a b : (SupportAtom.boundary G Z).Vertex} (ab : a ≠ b)
    (π : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl a) (.inl b)) (hπ : π.IsPath)
    (σ : O.graph.Walk (.inl b) (.inl a)) (hσ : σ.IsPath)
    (lab : ∀ d, (Sum.inl d : _ ⊕ O.Internal) ∈ σ.support → d = a ∨ d = b)
    (hk : ∃ k, 2 ≤ k ∧ π.length + σ.length = 2 ^ k)
    (spec : ∀ π' : (SupportAtom.retainedPiece G Z N).graph.Walk (.inl a) (.inl b),
      π'.IsPath → π'.length ≠ π.length ∧ ∀ j, 2 ≤ j → π'.length + σ.length ≠ 2 ^ j) :
    ArmOneRefined Z P N O := by
  obtain ⟨k, hk2, hsum⟩ := hk
  obtain ⟨act, privE, two, adjc⟩ := armOne_refined prof ab π hπ σ hσ hk2 hsum spec
  have aZ : a.1 ∈ Z := ((SupportAtom.mem_cutBoundary_iff G Z a.1).1 a.2).1
  have bZ : b.1 ∈ Z := ((SupportAtom.mem_cutBoundary_iff G Z b.1).1 b.2).1
  refine ⟨a, b, ab, π, hπ, σ, hσ, lab, ⟨k, hk2, hsum⟩, spec, act, privE, two, ?_, ?_, ?_⟩
  · intro adj
    obtain ⟨s2, pn, sn⟩ := adjc returnAvoidance adj
    refine ⟨s2, pn, sn, adj_residues hk2 hsum, ?_⟩
    intro τ hτ out long
    exact adj_outside avoids aZ bZ adj τ hτ out long
  · intro τ hτ out
    have ns := reading_outside_noSum avoids π hπ two τ hτ out
    refine ⟨ns, fun e => ns ?_⟩
    rw [e]
    exact (Core.DyadicLength.powerOfTwoLength_iff _).2 ⟨k, hk2, hsum⟩
  · intro one
    exact armOne_sigma_one avoids ab π hπ σ hk2 hsum spec
      (fun adj => (adjc returnAvoidance adj).1) one


section OutsideReturn

open Classical

/-- **A cubic vertex of a support has an outside return to another vertex of
the support** (vocabulary-free; `single_boundary_shape` applied to
`S = W ∪ {a}`, `W` the outside component of `y`).  With `δ ≥ 3`, no proper
baseline, no bridge and `G` connected: if `a ∈ Z` is cubic with an outside
neighbour `y`, and `Z ∖ {a} ≠ ∅`, then the outside component of `y` has a
neighbour `b' ∈ Z ∖ {a}`. -/
theorem cubic_outside_return {G : FiniteObject.{u}}
    (baseline : MinimumDegreeAtLeast 3 G)
    (noProper : ∀ sub : ProperSubgraph G, ¬ MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : EdgeContraction G, contraction.HasReturn)
    (connected : G.graph.Connected)
    {Z : Finset G.Vertex} {a y z : G.Vertex} (aZ : a ∈ Z) (cubic : G.degree a = 3)
    (ay : G.graph.Adj a y) (yZ : y ∉ Z) (zZ : z ∈ Z) (za : z ≠ a) :
    ∃ v b', v ∉ Z ∧ G.graph.Adj v b' ∧ b' ∈ Z ∧ b' ≠ a ∧
      ∃ p : G.graph.Walk y v, ∀ x ∈ p.support, x ∉ Z := by
  letI : FinEnum G.Vertex := G.vertices
  let W : Finset G.Vertex := Finset.univ.filter fun v => ∃ p : G.graph.Walk y v, ∀ x ∈ p.support, x ∉ Z
  have yW : y ∈ W := by
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨.nil, by simpa using yZ⟩
  have Wout : ∀ v ∈ W, v ∉ Z := by
    intro v hv
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨p, hp⟩ := hv
    exact hp v p.end_mem_support
  by_contra none
  push Not at none
  -- every `Z`-neighbour of `W` is `a`
  have onlyA : ∀ v ∈ W, ∀ x, G.graph.Adj v x → x ∈ Z → x = a := by
    intro v hv x adj xZ
    by_contra xa
    have hv' := hv
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    obtain ⟨p, hp⟩ := hv'
    obtain ⟨u, hu, uZ⟩ := none v x (Wout v hv) adj xZ xa p
    exact hp u hu uZ
  have closed : ∀ v ∈ W, ∀ x, G.graph.Adj v x → x ∉ Z → x ∈ W := by
    intro v hv x adj xZ
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨p, hp⟩ := hv
    refine ⟨p.concat adj, ?_⟩
    intro u hu
    rw [SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hp u hu
    · exact xZ
  let S : Finset G.Vertex := insert a W
  have nbrS : ∀ v ∈ W, ∀ x, G.graph.Adj v x → x ∈ S := by
    intro v hv x adj
    by_cases xZ : x ∈ Z
    · rw [onlyA v hv x adj xZ]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (closed v hv x adj xZ)
  have zS : z ∉ S := by
    intro h
    rcases Finset.mem_insert.1 h with e | h
    · exact za e
    · exact Wout z h zZ
  have single : SupportAtom.cutBoundary G S = {a} := by
    ext v
    simp only [SupportAtom.mem_cutBoundary_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨vS, x, adj, xS⟩
      rcases Finset.mem_insert.1 vS with e | vW
      · exact e
      · exact absurd (nbrS v vW x adj) xS
    · rintro rfl
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      obtain ⟨p⟩ := connected.preconnected y z
      obtain ⟨d, -, dIn, dOut⟩ := p.exists_boundary_dart (S : Set G.Vertex)
        (Finset.mem_insert_of_mem yW) zS
      rcases Finset.mem_insert.1 dIn with e | dW
      · exact ⟨d.snd, e ▸ d.adj, dOut⟩
      · exact absurd (nbrS _ dW _ d.adj) dOut
  obtain ⟨inn, out⟩ := GluedReadings.single_boundary_shape G baseline noProper bridgeless S a
    single (Finset.mem_insert_of_mem yW) (fun e => yZ (e ▸ aZ)) ⟨z, zS⟩
  have split := GluedReadings.degree_eq_inside_add_outside G S a
  omega

/-- The walk `a — y ⋯ v — b'` with outside interior bypasses to a path of
length `≥ 2` with outside interior. -/
theorem outside_path_of_walk {G : FiniteObject.{u}} {Z : Finset G.Vertex}
    {a y v b' : G.Vertex} (aZ : a ∈ Z) (bZ : b' ∈ Z) (ab : a ≠ b')
    (ay : G.graph.Adj a y) (p : G.graph.Walk y v) (hp : ∀ x ∈ p.support, x ∉ Z)
    (vb : G.graph.Adj v b') :
    ∃ τ : G.graph.Walk a b', τ.IsPath ∧ (∀ x ∈ τ.support, x ∉ Z ∨ x = a ∨ x = b') ∧
      2 ≤ τ.length := by
  let W : G.graph.Walk a b' := .cons ay (p.concat vb)
  have Wsupp : ∀ x ∈ W.support, x ∉ Z ∨ x = a ∨ x = b' := by
    intro x hx
    simp only [W, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hp x hx)
    · exact Or.inr (Or.inr rfl)
  refine ⟨W.bypass, W.bypass_isPath, fun x hx => Wsupp x (W.support_bypass_subset_support hx), ?_⟩
  by_contra lt
  have pos : 1 ≤ W.bypass.length := by
    rcases h : W.bypass with _ | ⟨_, _⟩
    · exact absurd rfl ab
    · simp
  have one : W.bypass.length = 1 := by omega
  have mem : s(a, b') ∈ W.bypass.edges := by
    rcases h : W.bypass with _ | ⟨h1, r⟩
    · exact absurd rfl ab
    · rw [h] at one
      cases r with
      | nil => simp
      | cons _ _ => simp at one
  have memW := W.edges_bypass_subset_edges mem
  simp only [W, SimpleGraph.Walk.edges_cons, List.mem_cons] at memW
  rcases memW with e | e
  · rcases Sym2.eq_iff.1 e with ⟨-, h⟩ | ⟨h, -⟩
    · exact hp y p.start_mem_support (h ▸ bZ)
    · exact hp y p.start_mem_support (h ▸ aZ)
  · have := (p.concat vb).fst_mem_support_of_mem_edges e
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at this
    rcases this with h | h
    · exact hp a h aZ
    · exact ab h

end OutsideReturn

end Hypostructure.Graph.ReadingSpectrumArms
