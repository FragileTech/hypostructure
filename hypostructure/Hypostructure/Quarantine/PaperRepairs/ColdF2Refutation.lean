import Hypostructure.Graph.GluedCycleSides
import Hypostructure.Graph.TargetDefectStructure
import Hypostructure.Core.DyadicLength
import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.CanonicalSurplus

/-!
# (F2) is not a clause-(b) exit: Lean-checked refutation

Quarantined evidence (reference only; no live module imports it) for the paper
error at node `[153]`, `lem:cold-corridor-first-failure` (ii), tex 7265-7270
(`audits/erdos-64-red-team/lean-vs-paper-discrepancies.md#paper-errors`).

* Part 1 (`not_residualTargetDefect_prefixPair_zero`): the two readings of an
  (F2) pair `(0, right)` lie in different `d_∂` fibres, so the pair is never a
  clause-(b) sparse exit; the survivor fact does not refute (F2).
* Part 2 (`coldF2_not_clauseB`, `coldFailureDefect_excluded_is_false`): the
  Lean (F2) fires at segment 1 of every corridor whose states 0 and 1 agree.
  In particular the former statement of
  `Contracts.Spine.coldFailureDefect_excluded`, quantified over all
  presentations and indices, was false (constant index).  The live statement
  is restated at G's retained occurrence (injective retained index, G's chosen
  states), where this construction does not apply.
* Part 3 (`edge_twoPath_sameFibre_targetDefect`): reading prefixes through the
  two-label cut-state interface instead would make clause (b) fire on every
  corridor of length `≥ 2`, i.e. the surviving branch vacuous.

Part 0 (below, through `targetDefect_of_size`) is the stopped `mathf2` analysis
`F2PathContext.lean`, copied verbatim (namespace renamed).  Parts 1-3 are new.
Part 4 (group F2, 2026-09-27) proves that at G the Lean (F2) at a segment is
exactly an earlier equal cut state, and that every (F2) pair is a `d_∂`
separation.

Part 0 original header: a path context between two boundary labels, and the
cycles it closes.  The one context used to separate two readings of corridor
prefixes: a path with `m ≥ 2` edges from label `x` to label `y`, whose
interior is fresh.  Every glued cycle through its interior contains the whole
path; so it either lifts to the piece, or has length in `[m+1, |glue|]`.
-/

namespace Hypostructure.Graph.ColdRepairF2

open Hypostructure.Graph

universe u

/-! ## Two generic walk facts -/

/-- A vertex of a cycle has two distinct neighbours on the cycle. -/
theorem cycle_two_neighbours {V : Type*} {G : SimpleGraph V} {u v : V}
    {c : G.Walk u u} (hc : c.IsCycle) (hv : v ∈ c.support) :
    ∃ w₁ w₂, w₁ ≠ w₂ ∧ G.Adj v w₁ ∧ G.Adj v w₂ ∧
      w₁ ∈ c.support ∧ w₂ ∈ c.support := by
  classical
  set d := c.rotate v hv
  have hd : d.IsCycle := hc.rotate hv
  have hn : ¬ d.Nil := hd.not_nil
  refine ⟨d.snd, d.penultimate, hd.snd_ne_penultimate, d.adj_snd hn,
    (d.adj_penultimate hn).symm, ?_, ?_⟩
  · exact (SimpleGraph.Walk.mem_support_rotate_iff c _ hv).mp (d.getVert_mem_support 1)
  · exact (SimpleGraph.Walk.mem_support_rotate_iff c _ hv).mp
      (d.getVert_mem_support _)

/-- Every vertex of a closed nonempty walk lies in the tail of its support. -/
theorem mem_tail_of_cycle {V : Type*} {G : SimpleGraph V} {u v : V}
    {c : G.Walk u u} (hc : c.IsCycle) (hv : v ∈ c.support) :
    v ∈ c.support.tail := by
  rw [← SimpleGraph.Walk.cons_tail_support] at hv
  rcases List.mem_cons.mp hv with rfl | tail
  · exact SimpleGraph.Walk.end_mem_tail_support hc.not_nil
  · exact tail

/-- A cycle's length is at least the number of distinct vertices it visits. -/
theorem card_le_length_of_cycle {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) (S : Finset V)
    (hS : ∀ v ∈ S, v ∈ c.support) : S.card ≤ c.length := by
  have sub : S ⊆ c.support.tail.toFinset := by
    intro v hv
    exact List.mem_toFinset.mpr (mem_tail_of_cycle hc (hS v hv))
  calc S.card ≤ c.support.tail.toFinset.card := Finset.card_le_card sub
    _ ≤ c.support.tail.length := List.toFinset_card_le _
    _ = c.length := by simp [SimpleGraph.Walk.length_support]

/-- A cycle is no longer than the number of vertices. -/
theorem length_le_card_of_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) : c.length ≤ Fintype.card V := by
  classical
  have nodup := hc.support_nodup
  have : c.support.tail.length = c.length := by
    simp [SimpleGraph.Walk.length_support]
  rw [← this, ← List.toFinset_card_of_nodup nodup]
  exact Finset.card_le_univ _

/-! ## The path context -/

variable {B : Boundary.{u}}

/-- Position of a context vertex along the path `x = 0, 1, …, m-1, m = y`. -/
noncomputable def pos (x y : B.Vertex) (m : ℕ) :
    B.Vertex ⊕ ULift.{u} (Fin (m - 1)) → Option ℕ := by
  classical
  exact fun v => match v with
    | .inl b => if b = x then some 0 else if b = y then some m else none
    | .inr i => some (i.down.val + 1)

/-- The vertex at position `p` (clamped to `y` beyond `m`). -/
noncomputable def at_ (x y : B.Vertex) (m : ℕ) (p : ℕ) :
    B.Vertex ⊕ ULift.{u} (Fin (m - 1)) :=
  if h0 : p = 0 then .inl x
  else if h : p ≤ m - 1 then .inr ⟨⟨p - 1, by omega⟩⟩
  else .inl y

theorem pos_at (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) {p : ℕ}
    (hp : p ≤ m) : pos x y m (at_ x y m p) = some p := by
  classical
  unfold at_
  by_cases h0 : p = 0
  · subst h0; simp [pos]
  · by_cases h1 : p ≤ m - 1
    · simp only [h0, h1, dif_pos, dif_neg, not_false_eq_true, pos]
      congr 1; omega
    · have hpm : p = m := by omega
      subst hpm
      simp [h0, h1, pos, hxy.symm]

theorem at_of_pos (x y : B.Vertex) (m : ℕ) (hm : 1 ≤ m)
    {v : B.Vertex ⊕ ULift.{u} (Fin (m - 1))} {p : ℕ}
    (h : pos x y m v = some p) : p ≤ m ∧ v = at_ x y m p := by
  classical
  rcases v with b | i
  · simp only [pos] at h
    by_cases hbx : b = x
    · subst hbx; simp at h; subst h; simp [at_]
    · simp only [hbx, if_false] at h
      by_cases hby : b = y
      · subst hby
        simp at h; subst h
        refine ⟨le_rfl, ?_⟩
        unfold at_
        rw [dif_neg (by omega), dif_neg (by omega)]
      · simp [hby] at h
  · simp only [pos, Option.some.injEq] at h
    subst h
    have hi := i.down.isLt
    refine ⟨by omega, ?_⟩
    unfold at_
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 1

/-- **The path context** with `m` edges from label `x` to label `y`. -/
noncomputable def pathContext (x y : B.Vertex) (m : ℕ) : OutsideContext B where
  Internal := ULift.{u} (Fin (m - 1))
  internalVertices := FinEnum.ofEquiv (Fin (m - 1)) Equiv.ulift
  graph := SimpleGraph.fromRel fun v w =>
    ∃ p, pos x y m v = some p ∧ pos x y m w = some (p + 1)
  decideAdj := Classical.decRel _

theorem pathContext_internalVertexCount (x y : B.Vertex) (m : ℕ) :
    (pathContext x y m).internalVertexCount = m - 1 := by
  simp [OutsideContext.internalVertexCount, pathContext, FinEnum.card]
  rw [List.Nodup.dedup (List.nodup_finRange _), List.length_finRange]

theorem pathContext_adj_pos {x y : B.Vertex} {m : ℕ} {v w}
    (h : (pathContext x y m).graph.Adj v w) :
    ∃ p q, pos x y m v = some p ∧ pos x y m w = some q ∧ (q = p + 1 ∨ p = q + 1) := by
  simp only [pathContext, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨p, hv, hw⟩ | ⟨p, hw, hv⟩
  · exact ⟨p, p + 1, hv, hw, Or.inl rfl⟩
  · exact ⟨p + 1, p, hv, hw, Or.inr rfl⟩

theorem pathContext_adj_at (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m)
    {p : ℕ} (hp : p + 1 ≤ m) :
    (pathContext x y m).graph.Adj (at_ x y m p) (at_ x y m (p + 1)) := by
  simp only [pathContext, SimpleGraph.fromRel_adj]
  have h1 := pos_at x y m hxy hm (p := p) (by omega)
  have h2 := pos_at x y m hxy hm (p := p + 1) hp
  refine ⟨fun e => ?_, Or.inl ⟨p, h1, h2⟩⟩
  rw [e, h2] at h1
  simp at h1

/-- The walk `at_ 0 → at_ k` along the path context. -/
noncomputable def chain (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) :
    (k : ℕ) → k ≤ m → (pathContext x y m).graph.Walk (at_ x y m 0) (at_ x y m k)
  | 0, _ => .nil
  | k + 1, hk => (chain x y m hxy hm k (by omega)).concat
      (pathContext_adj_at x y m hxy hm hk)

theorem chain_length (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) :
    ∀ k (hk : k ≤ m), (chain x y m hxy hm k hk).length = k
  | 0, _ => rfl
  | k + 1, hk => by
      simp [chain, SimpleGraph.Walk.length_concat, chain_length x y m hxy hm k]

theorem chain_support (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) :
    ∀ k (hk : k ≤ m), (chain x y m hxy hm k hk).support =
      (List.range (k + 1)).map (at_ x y m)
  | 0, _ => by simp [chain]; rfl
  | k + 1, hk => by
      rw [chain, SimpleGraph.Walk.support_concat, chain_support x y m hxy hm k,
        List.range_succ (n := k + 1), List.map_append]
      simp; rfl

theorem at_injOn (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) {p q : ℕ}
    (hp : p ≤ m) (hq : q ≤ m) (h : at_ x y m p = at_ x y m q) : p = q := by
  have a := pos_at x y m hxy hm hp
  have b := pos_at x y m hxy hm hq
  rw [h, b] at a
  exact (Option.some.inj a).symm

theorem chain_isPath (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) (k : ℕ)
    (hk : k ≤ m) : (chain x y m hxy hm k hk).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, chain_support]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro p hp q hq e
  simp only [List.mem_range] at hp hq
  exact at_injOn x y m hxy hm (by omega) (by omega) e

theorem at_zero (x y : B.Vertex) (m : ℕ) : at_ x y m 0 = .inl x := by
  simp [at_]

theorem at_top (x y : B.Vertex) (m : ℕ) (hm : 1 ≤ m) : at_ x y m m = .inl y := by
  unfold at_
  rw [dif_neg (by omega), dif_neg (by omega)]

/-- The context's own `x → y` path, of length `m`. -/
noncomputable def contextWalk (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) :
    (pathContext x y m).graph.Walk (.inl x) (.inl y) :=
  (chain x y m hxy hm m le_rfl).copy (at_zero x y m) (at_top x y m hm)

theorem contextWalk_length (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) :
    (contextWalk x y m hxy hm).length = m := by
  simp [contextWalk, chain_length]

theorem contextWalk_isPath (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m) :
    (contextWalk x y m hxy hm).IsPath := by
  simpa [contextWalk] using chain_isPath x y m hxy hm m le_rfl

theorem contextWalk_labels (x y : B.Vertex) (m : ℕ) (hxy : x ≠ y) (hm : 1 ≤ m)
    (b : B.Vertex)
    (hb : (Sum.inl b : B.Vertex ⊕ (pathContext x y m).Internal) ∈
      (contextWalk x y m hxy hm).support) : b = x ∨ b = y := by
  classical
  have hb' : (Sum.inl b : B.Vertex ⊕ ULift.{u} (Fin (m - 1))) ∈
      (List.range (m + 1)).map (at_ x y m) := by
    have := hb
    simp only [contextWalk, SimpleGraph.Walk.support_copy] at this
    rwa [chain_support] at this
  obtain ⟨p, hp, e⟩ := List.mem_map.mp hb'
  rw [List.mem_range] at hp
  have := pos_at x y m hxy hm (p := p) (by omega)
  rw [e] at this
  simp only [pos] at this
  by_cases hbx : b = x
  · exact Or.inl hbx
  · by_cases hby : b = y
    · exact Or.inr hby
    · simp [hbx, hby] at this

/-! ## Cycles through the interior of the path context -/

variable {P : BoundaryPiece B}

/-- Glued position. -/
noncomputable def gat (P : BoundaryPiece B) (x y : B.Vertex) (m : ℕ) (p : ℕ) :
    GluedVertex P (pathContext x y m) :=
  contextEmbedding P (pathContext x y m) (at_ x y m p)

/-- A glued vertex adjacent to an interior position is a neighbouring
position. -/
theorem glue_adj_interior {x y : B.Vertex} {m : ℕ} (hxy : x ≠ y) (hm : 1 ≤ m)
    {p : ℕ} (hp1 : 1 ≤ p) (hp2 : p ≤ m - 1) {w : GluedVertex P (pathContext x y m)}
    (h : (glueGraph P (pathContext x y m)).Adj (gat P x y m p) w) :
    w = gat P x y m (p - 1) ∨ w = gat P x y m (p + 1) := by
  have hat : at_ x y m p = .inr ⟨⟨p - 1, by omega⟩⟩ := by
    unfold at_; rw [dif_neg (by omega), dif_pos hp2]
  rcases (glueGraph_adj_iff _ _ _ _).mp h with owns | owns
  · exfalso
    refine GluedCycleSides.not_pieceOwns_context_internal
      (inner := (⟨⟨p - 1, by omega⟩⟩ : ULift (Fin (m - 1)))) (other := w) ?_
    have e : gat P x y m p = Sum.inr (Sum.inr ⟨⟨p - 1, by omega⟩⟩) := by
      simp [gat, hat, contextEmbedding]
    rw [← e]; exact owns
  · obtain ⟨a, b, adj, ha, hb⟩ := owns
    have ha' : a = at_ x y m p := (contextEmbedding P _).injective ha
    subst ha'
    obtain ⟨p', q, hpa, hqb, rel⟩ := pathContext_adj_pos adj
    rw [pos_at x y m hxy hm (by omega)] at hpa
    cases hpa
    obtain ⟨_, hbq⟩ := at_of_pos x y m hm hqb
    subst hbq
    rcases rel with rfl | rfl
    · exact Or.inr (by simp only [gat]; exact hb.symm)
    · exact Or.inl (by simp only [gat, Nat.add_sub_cancel]; exact hb.symm)

/-- **A glued cycle through the interior of the path context contains every
position of the path.** -/
theorem cycle_contains_path {x y : B.Vertex} {m : ℕ} (hxy : x ≠ y) (hm : 1 ≤ m)
    {base : GluedVertex P (pathContext x y m)}
    {c : (glueGraph P (pathContext x y m)).Walk base base} (hc : c.IsCycle)
    {p₀ : ℕ} (h1 : 1 ≤ p₀) (h2 : p₀ ≤ m - 1) (hmem : gat P x y m p₀ ∈ c.support) :
    ∀ p ≤ m, gat P x y m p ∈ c.support := by
  classical
  -- an interior position on the cycle forces both neighbours onto it
  have step : ∀ p, 1 ≤ p → p ≤ m - 1 → gat P x y m p ∈ c.support →
      gat P x y m (p - 1) ∈ c.support ∧ gat P x y m (p + 1) ∈ c.support := by
    intro p hp1 hp2 hp
    obtain ⟨w₁, w₂, ne, a₁, a₂, m₁, m₂⟩ := cycle_two_neighbours hc hp
    rcases glue_adj_interior (P := P) hxy hm hp1 hp2 a₁ with e₁ | e₁ <;>
      rcases glue_adj_interior (P := P) hxy hm hp1 hp2 a₂ with e₂ | e₂
    · exact absurd (e₁.trans e₂.symm) ne
    · exact ⟨e₁ ▸ m₁, e₂ ▸ m₂⟩
    · exact ⟨e₂ ▸ m₂, e₁ ▸ m₁⟩
    · exact absurd (e₁.trans e₂.symm) ne
  have down : ∀ d, d ≤ p₀ → gat P x y m (p₀ - d) ∈ c.support := by
    intro d
    induction d with
    | zero => intro _; simpa using hmem
    | succ d ih =>
        intro hd
        have := (step (p₀ - d) (by omega) (by omega) (ih (by omega))).1
        rwa [show p₀ - d - 1 = p₀ - (d + 1) by omega] at this
  have up : ∀ d, p₀ + d ≤ m → gat P x y m (p₀ + d) ∈ c.support := by
    intro d
    induction d with
    | zero => intro _; simpa using hmem
    | succ d ih =>
        intro hd
        have := (step (p₀ + d) (by omega) (by omega) (ih (by omega))).2
        rwa [show p₀ + d + 1 = p₀ + (d + 1) by omega] at this
  intro p hp
  by_cases hle : p ≤ p₀
  · have := down (p₀ - p) (by omega)
    rwa [show p₀ - (p₀ - p) = p by omega] at this
  · have := up (p - p₀) (by omega)
    rwa [show p₀ + (p - p₀) = p by omega] at this

/-- **Length window.**  A glued cycle through the interior of the path context
has length at least `m + 1` and at most the number of glued vertices. -/
theorem cycle_length_window {x y : B.Vertex} {m : ℕ} (hxy : x ≠ y) (hm : 2 ≤ m)
    {base : GluedVertex P (pathContext x y m)}
    {c : (glueGraph P (pathContext x y m)).Walk base base} (hc : c.IsCycle)
    (inner : (pathContext x y m).Internal)
    (hmem : (Sum.inr (Sum.inr inner) : GluedVertex P (pathContext x y m)) ∈
      c.support) :
    m + 1 ≤ c.length ∧ c.length ≤ (glue P (pathContext x y m)).vertexCount := by
  classical
  have hi := inner.down.isLt
  have hat : gat P x y m (inner.down.val + 1) = Sum.inr (Sum.inr inner) := by
    unfold gat at_
    rw [dif_neg (by omega), dif_pos (by omega)]
    rfl
  have all := cycle_contains_path (P := P) hxy (by omega) hc (p₀ := inner.down.val + 1)
    (by omega) (by omega) (hat ▸ hmem)
  constructor
  · have inj : Set.InjOn (gat P x y m) ↑(Finset.range (m + 1)) := by
      intro p hp q hq e
      simp only [Finset.coe_range, Set.mem_Iio] at hp hq
      exact at_injOn x y m hxy (by omega) (by omega) (by omega)
        ((contextEmbedding P _).injective e)
    have card : ((Finset.range (m + 1)).image (gat P x y m)).card = m + 1 := by
      rw [Finset.card_image_of_injOn inj, Finset.card_range]
    rw [← card]
    refine card_le_length_of_cycle hc _ ?_
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact all p (by simpa [Nat.lt_succ_iff] using hp)
  · letI : Fintype (GluedVertex P (pathContext x y m)) :=
      (glue P (pathContext x y m)).vertices.instFintype
    have := length_le_card_of_cycle (V := GluedVertex P (pathContext x y m))
      (G := glueGraph P (pathContext x y m)) hc
    simpa [FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard, glue] using this


theorem pos_inl {x y : B.Vertex} {m : ℕ} {a : B.Vertex} {p : ℕ}
    (h : pos x y m (.inl a) = some p) : p = 0 ∨ p = m := by
  classical
  simp only [pos] at h
  by_cases hax : a = x
  · simp [hax] at h; exact Or.inl h.symm
  · by_cases hay : a = y
    · subst hay
      simp only [hax, if_false, if_true, Option.some.injEq] at h
      exact Or.inr h.symm
    · simp [hax, hay] at h

/-- No power of two lies strictly between `2^b` and `2^(b+1)`. -/
theorem not_powerOfTwo_between {b ℓ : ℕ} (lo : 2 ^ b < ℓ) (hi : ℓ < 2 ^ (b + 1)) :
    ¬ Core.DyadicLength.PowerOfTwoLength ℓ := by
  rintro ⟨e, _, h⟩
  rw [h] at lo hi
  have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp lo
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hi
  omega

/-- **Separation by size.**  Two pieces on a common interface with two
distinct labels `x ≠ y`: if `R` contains an `x`–`y` path of length `b`, `L`
has at most `b` vertices and `L` itself carries no power-of-two cycle, then some
outside context separates them for the power-of-two cycle target: glued to the
path context with `2^(b+1) - b` edges, `R` closes a cycle of length
`2^(b+1)`, while every cycle of `L`'s gluing lies in `L` or has length strictly
between `2^b` and `2^(b+1)`. -/
theorem targetDefect_of_size {x y : B.Vertex} (hxy : x ≠ y)
    (L R : BoundaryPiece B)
    (Lfree : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength (BoundaryPiece.pack L))
    (Rwalk : R.graph.Walk (.inl x) (.inl y)) (Rpath : Rwalk.IsPath)
    (small : B.vertexCount + L.internalVertexCount ≤ Rwalk.length) :
    Response.TargetDefect (HasCycleWithLength Core.DyadicLength.PowerOfTwoLength) L R := by
  classical
  set b := Rwalk.length with hbdef
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · exfalso
      have := SimpleGraph.Walk.eq_of_length_eq_zero h
      exact hxy (Sum.inl_injective this)
    · exact h
  have pow_lt : b + 1 < 2 ^ (b + 1) := Nat.lt_two_pow_self
  have pow_b : b < 2 ^ b := Nat.lt_two_pow_self
  have pow_succ : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  set m := 2 ^ (b + 1) - b with hmdef
  have hm : 2 ≤ m := by omega
  refine ⟨pathContext x y m, fun equivalent => ?_⟩
  -- the positive side: `R` closes a cycle of length `2^(b+1)`
  have positive : HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
      (glue R (pathContext x y m)) := by
    refine hasCycleWithLength_glue_of_crossing R
      (pathContext x y m) Rwalk (contextWalk x y m hxy (by omega)) Rpath
      (contextWalk_isPath x y m hxy (by omega))
      (contextWalk_labels x y m hxy (by omega))
      (Or.inr (by rw [contextWalk_length]; omega)) ?_
    rw [contextWalk_length]
    refine ⟨⟨b + 1, by omega⟩, by simp; omega, by simp; omega⟩
  -- the negative side: no power-of-two cycle in `L`'s gluing
  apply (show ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
      (glue L (pathContext x y m)) from ?_) (equivalent.mpr positive)
  rintro ⟨certificate⟩
  have hc := certificate.isCycle
  rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
      (piece := L) (outside := pathContext x y m) hc with
    ⟨pb, lifted, liftedCycle, liftedLength⟩ | ⟨inner, hmem⟩ |
      ⟨a, a', ne, _, _, adj, _⟩
  · exact Lfree ⟨⟨pb, lifted, liftedCycle, liftedLength ▸ certificate.length_ok⟩⟩
  · obtain ⟨lo, hi⟩ := cycle_length_window (P := L) hxy hm hc inner hmem
    rw [glue_vertexCount, pathContext_internalVertexCount] at hi
    have lo' : m + 1 ≤ certificate.walk.length := lo
    have hi' : certificate.walk.length ≤
        B.vertexCount + L.internalVertexCount + (m - 1) := hi
    exact not_powerOfTwo_between (b := b) (by omega) (by omega) certificate.length_ok
  · obtain ⟨p, q, hp, hq, rel⟩ := pathContext_adj_pos adj
    rcases pos_inl hp with rfl | rfl <;> rcases pos_inl hq with rfl | rfl <;> omega

end Hypostructure.Graph.ColdRepairF2

/-! ## Part 1: the two prefix readings of an (F2) pair lie in different
boundary-degree fibres

Clause (b) of `def:named-surplus-exits` (`Graph.ResidualTargetDefect`) reads two
declared coordinates as G's own piece at the canonical connected support `Z`
of their union, restricted to each coordinate's support, on the one boundary
`∂Z`, and requires `d_∂` equal (tex 5835-5839, 5862: `d_∂(X) = (d_X(v_t))_t`,
the degree *in the piece*).  (F2) (`FirstFailureDefect`) compares exactly the
readings `retainedPiece J_r J_l` and `piece J_r` of two prefixes
`J_l ⊆ J_r`.  Those two readings are in different `d_∂` fibres as soon as a
cut-boundary vertex of `J_r` loses an edge. -/

namespace Hypostructure.Graph.ColdRepairF2

open Hypostructure Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe v

section Readings

variable {object : FiniteObject.{v}}

theorem pieceDecode_mem (Z : Finset object.Vertex)
    (w : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    SupportAtom.pieceDecode object Z w ∈ Z := by
  rcases w with b | i
  · exact ((SupportAtom.mem_cutBoundary_iff object Z b.1).1 b.2).1
  · exact i.2.1

/-- The piece-side vertex of a support vertex. -/
noncomputable def enc (Z : Finset object.Vertex) (w : object.Vertex) (hw : w ∈ Z) :
    (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z := by
  classical
  exact if hb : w ∈ SupportAtom.cutBoundary object Z then .inl ⟨w, hb⟩
    else .inr ⟨w, hw, hb⟩

theorem pieceDecode_enc (Z : Finset object.Vertex) (w : object.Vertex) (hw : w ∈ Z) :
    SupportAtom.pieceDecode object Z (enc Z w hw) = w := by
  unfold enc
  split <;> rfl

theorem retained_adj_iff (Z L : Finset object.Vertex)
    (a b : (SupportAtom.boundary object Z).Vertex ⊕ SupportAtom.PieceInternal object Z) :
    (SupportAtom.retainedPiece object Z L).graph.Adj a b ↔
      object.graph.Adj (SupportAtom.pieceDecode object Z a)
          (SupportAtom.pieceDecode object Z b) ∧
        SupportAtom.pieceDecode object Z a ∈ L ∧
        SupportAtom.pieceDecode object Z b ∈ L := by
  simp only [SupportAtom.retainedPiece, SimpleGraph.inf_adj, SimpleGraph.comap_adj,
    SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨adj, _, (h | h)⟩
    · exact ⟨adj, h⟩
    · exact ⟨adj, h.2, h.1⟩
  · rintro ⟨adj, ha, hb⟩
    exact ⟨adj, adj.ne, Or.inl ⟨ha, hb⟩⟩

/-- **A boundary vertex that loses an edge lowers its `d_∂` entry.**  If the
cut-boundary vertex `b` of `Z` has a `G`-neighbour `w ∈ Z` and the edge `bw`
is not retained by `L`, then `b`'s degree in `retainedPiece Z L` is strictly
below its degree in the full reading `retainedPiece Z Z`. -/
theorem retained_boundaryDegree_lt (Z L : Finset object.Vertex)
    (b : object.Vertex) (hb : b ∈ SupportAtom.cutBoundary object Z)
    (w : object.Vertex) (hw : w ∈ Z) (adj : object.graph.Adj b w)
    (lost : b ∉ L ∨ w ∉ L) :
    (SupportAtom.retainedPiece object Z L).boundaryDegree ⟨b, hb⟩ <
      (SupportAtom.retainedPiece object Z Z).boundaryDegree ⟨b, hb⟩ := by
  classical
  unfold BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet,
    FiniteObject.degree_eq_ncard_neighborSet]
  have finite : Set.Finite ((SupportAtom.retainedPiece object Z Z).pack.graph.neighborSet
      (.inl ⟨b, hb⟩)) :=
    @Set.toFinite _ _ (@Subtype.finite _
      (@Finite.of_fintype _
        (@FinEnum.instFintype _ (SupportAtom.retainedPiece object Z Z).pack.vertices)) _)
  apply Set.ncard_lt_ncard _ finite
  refine ⟨fun x hx => ?_, fun sub => ?_⟩
  · change (SupportAtom.retainedPiece object Z L).graph.Adj _ _ at hx
    change (SupportAtom.retainedPiece object Z Z).graph.Adj _ _
    rw [retained_adj_iff] at hx ⊢
    exact ⟨hx.1, pieceDecode_mem Z _, pieceDecode_mem Z _⟩
  · have inZ : enc Z w hw ∈
        (SupportAtom.retainedPiece object Z Z).pack.graph.neighborSet (.inl ⟨b, hb⟩) := by
      change (SupportAtom.retainedPiece object Z Z).graph.Adj _ _
      rw [retained_adj_iff, pieceDecode_enc]
      exact ⟨adj, pieceDecode_mem Z _, hw⟩
    have inL := sub inZ
    change (SupportAtom.retainedPiece object Z L).graph.Adj _ _ at inL
    rw [retained_adj_iff, pieceDecode_enc] at inL
    rcases lost with lost | lost
    · exact lost inL.2.1
    · exact lost inL.2.2

/-- **Profile equality forces a closed, edge-preserving boundary.**  If the
readings `retainedPiece Z L` and `retainedPiece Z Z` have the same `d_∂`, then
no cut-boundary vertex of `Z` loses an edge: every boundary vertex lies in `L`
and every edge from it into `Z` ends in `L`. -/
theorem retained_profile_eq_imp (Z L : Finset object.Vertex)
    (same : (SupportAtom.retainedPiece object Z L).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object Z Z).boundaryDegreeProfile) :
    ∀ b ∈ SupportAtom.cutBoundary object Z, ∀ w ∈ Z,
      object.graph.Adj b w → b ∈ L ∧ w ∈ L := by
  intro b hb w hw adj
  by_contra lost
  have lt := retained_boundaryDegree_lt Z L b hb w hw adj (by tauto)
  have eq := congrFun same ⟨b, hb⟩
  unfold BoundaryPiece.boundaryDegreeProfile at eq
  omega

end Readings

/-! ### The canonical support of a connected seed is the seed -/

theorem select?_self {object : FiniteObject.{v}} (S : Finset object.Vertex)
    (connected : SupportComponents.Connected.ConnectedOn object S) :
    CanonicalSupport.select? object S = some S := by
  classical
  have self : S ∈ CanonicalSupport.candidates object S :=
    CanonicalSupport.mem_candidates_iff.2 ⟨subset_rfl, connected⟩
  have single : CanonicalSupport.minimalCandidates object S = {S} := by
    ext T
    rw [Finset.mem_singleton]
    unfold CanonicalSupport.minimalCandidates
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨member, minimal⟩
      have sub := (CanonicalSupport.mem_candidates_iff.1 member).1
      exact (Finset.eq_of_subset_of_card_le sub (minimal S self)).symm
    · rintro rfl
      refine ⟨self, fun other member => ?_⟩
      exact Finset.card_le_card (CanonicalSupport.mem_candidates_iff.1 member).1
  unfold CanonicalSupport.select?
  rw [single, Finset.toList_singleton]
  rfl

/-! ### Corridor facts -/

section Corridor

variable {object : FiniteObject.{v}} {windows component : Finset object.Vertex}

theorem head_mem_prefixSupport_iff
    (corridor : ColdCorridor.Corridor object windows component)
    (s : corridor.Segment) (n : Nat) :
    corridor.head s ∈ corridor.prefixSupport n ↔ s.1 ≤ n := by
  classical
  constructor
  · intro mem
    obtain ⟨inner, innerMem, innerEq⟩ := (corridor.mem_prefixSupport n _).1 mem
    obtain ⟨i, hi, hiLe⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMem
    rw [SimpleGraph.Walk.take_getVert] at hi
    have takeLen := SimpleGraph.Walk.take_length corridor.inside.1 n
    have eq : corridor.inside.1.getVert (min n i) = corridor.inside.1.getVert s.1 := by
      apply Subtype.ext
      rw [hi]
      exact innerEq
    have inj := corridor.inside.2.getVert_injOn
      (show min n i ∈ {j | j ≤ corridor.inside.1.length} by
        simp only [Set.mem_setOf_eq]; omega)
      (show s.1 ∈ {j | j ≤ corridor.inside.1.length} by
        simp only [Set.mem_setOf_eq]; omega) eq
    omega
  · intro le
    refine (corridor.mem_prefixSupport n _).2
      ⟨(corridor.inside.1.take n).getVert s.1, ?_, ?_⟩
    · exact SimpleGraph.Walk.getVert_mem_support _ _
    · rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right le]
      rfl

/-- Every vertex of a prefix is the head of a segment inside it. -/
theorem mem_prefixSupport_iff_head
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat)
    (vertex : object.Vertex) :
    vertex ∈ corridor.prefixSupport n ↔
      ∃ s : corridor.Segment, s.1 ≤ n ∧ corridor.head s = vertex := by
  constructor
  · intro mem
    obtain ⟨inner, innerMem, innerEq⟩ := (corridor.mem_prefixSupport n _).1 mem
    obtain ⟨i, hi, hiLe⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMem
    rw [SimpleGraph.Walk.take_getVert] at hi
    have takeLen := SimpleGraph.Walk.take_length corridor.inside.1 n
    refine ⟨⟨min n i, by omega⟩, Nat.min_le_left _ _, ?_⟩
    change (corridor.inside.1.getVert (min n i)).1 = vertex
    rw [hi]
    exact innerEq
  · rintro ⟨s, le, rfl⟩
    exact (head_mem_prefixSupport_iff corridor s n).2 le

theorem prefixSupport_subset_component
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat) :
    corridor.prefixSupport n ⊆ component := by
  intro vertex mem
  obtain ⟨inner, _, rfl⟩ := (corridor.mem_prefixSupport n _).1 mem
  exact inner.2

theorem head_zero (corridor : ColdCorridor.Corridor object windows component) :
    corridor.head ⟨0, Nat.succ_pos _⟩ = corridor.entryStub.1 := by
  simp [ColdCorridor.Corridor.head, ColdCorridor.Corridor.entryStub,
    ColdCorridor.stubFoot]

theorem head_adj_succ (corridor : ColdCorridor.Corridor object windows component)
    (i : Nat) (hi : i < corridor.inside.1.length) :
    object.graph.Adj (corridor.head ⟨i, by omega⟩) (corridor.head ⟨i + 1, by omega⟩) :=
  SimpleGraph.induce_adj.mp (corridor.inside.1.adj_getVert_succ hi)

/-- The entry foot is on the cut boundary of every prefix: its window
neighbour lies outside the outside component. -/
theorem foot_mem_cutBoundary
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat) :
    corridor.entryStub.1 ∈ SupportAtom.cutBoundary object (corridor.prefixSupport n) := by
  have stub := (ColdCorridor.mem_boundaryStubs_iff object windows component _).1
    (List.get_mem _ corridor.entry)
  rw [SupportAtom.mem_cutBoundary_iff]
  refine ⟨corridor.foot_mem_prefixSupport n, corridor.entryStub.2, stub.2.2, ?_⟩
  intro inside
  exact Finset.disjoint_left.mp outside.1
    (prefixSupport_subset_component corridor n inside) stub.2.1

end Corridor

/-! ### The (F2) pair `(0, right)` is never a clause-(b) exit -/

section Pair

variable {object : FiniteObject.{v}} {windows component : Finset object.Vertex}

/-- **The `d_∂` fibres of the (F2) readings differ.**  For every corridor in an
outside component and every `right > 0`, the readings
`retainedPiece J_right J_0` and `retainedPiece J_right J_right` have different
boundary-degree profiles: the entry foot is a cut-boundary vertex of
`J_right` and loses its corridor edge to `head 1`. -/
theorem prefix_zero_profile_ne
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) (positive : 0 < right.1) :
    (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport 0)).boundaryDegreeProfile ≠
      (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport right.1)).boundaryDegreeProfile := by
  intro same
  have long : 0 < corridor.inside.1.length := by have := right.2; omega
  let one : corridor.Segment := ⟨1, by omega⟩
  have adj := head_adj_succ corridor 0 long
  rw [head_zero] at adj
  have oneIn : corridor.head one ∈ corridor.prefixSupport right.1 :=
    (head_mem_prefixSupport_iff corridor one right.1).2 (by simp [one]; omega)
  have oneOut : corridor.head one ∉ corridor.prefixSupport 0 := by
    rw [head_mem_prefixSupport_iff]; simp [one]
  have := retained_profile_eq_imp _ _ same corridor.entryStub.1
    (foot_mem_cutBoundary outside corridor right.1) (corridor.head one) oneIn adj
  exact oneOut this.2

/-- The two prefix coordinates `J_left`, `J_right`, labelled by `Bool`. -/
noncomputable def prefixPairSupport
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : Nat) : Bool → Finset object.Vertex :=
  fun side => if side then corridor.prefixSupport right else corridor.prefixSupport left

/-- **Clause (b) on the prefix pair forces equal `d_∂` of the (F2) readings.**
Any clause-(b) defect between the two prefix coordinates is read at
`Z = select?(J_l ∪ J_r) = J_r` and asserts
`d_∂(retainedPiece J_r J_l) = d_∂(retainedPiece J_r J_r)`. -/
theorem prefixPair_residualTargetDefect_profile
    (Target : FiniteObject.{v} → Prop)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : Nat) (le : left ≤ right)
    (defect : ResidualTargetDefect Target object (Finset.univ : Finset Bool)
      (prefixPairSupport corridor left right)) :
    (SupportAtom.retainedPiece object (corridor.prefixSupport right)
        (corridor.prefixSupport left)).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object (corridor.prefixSupport right)
        (corridor.prefixSupport right)).boundaryDegreeProfile := by
  classical
  unfold ResidualTargetDefect at defect
  obtain ⟨first, _, second, _, different, support, selected, profile, _, _⟩ := defect
  have mono := corridor.prefixSupport_mono le
  have selectRight := select?_self (corridor.prefixSupport right)
    (corridor.prefixSupport_connectedOn right)
  cases first <;> cases second
  · exact absurd rfl different
  · have union : prefixPairSupport corridor left right false ∪
        prefixPairSupport corridor left right true = corridor.prefixSupport right := by
      simp only [prefixPairSupport, Bool.false_eq_true, if_false, if_true]
      exact Finset.union_eq_right.2 mono
    rw [union, selectRight] at selected
    cases selected
    simpa [prefixPairSupport] using profile
  · have union : prefixPairSupport corridor left right true ∪
        prefixPairSupport corridor left right false = corridor.prefixSupport right := by
      simp only [prefixPairSupport, Bool.false_eq_true, if_false, if_true]
      exact Finset.union_eq_left.2 mono
    rw [union, selectRight] at selected
    cases selected
    simpa [prefixPairSupport] using profile.symm
  · exact absurd rfl different

/-- **(F2) ⇏ clause (b), at every corridor.**  For every corridor of G in an
outside component and every `right > 0`, the prefix coordinates
`{J_0, J_right}` carry no clause-(b) defect (any target predicate). -/
theorem not_residualTargetDefect_prefixPair_zero
    (Target : FiniteObject.{v} → Prop)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) (positive : 0 < right.1) :
    ¬ ResidualTargetDefect Target object (Finset.univ : Finset Bool)
      (prefixPairSupport corridor 0 right.1) := fun defect =>
  prefix_zero_profile_ne outside corridor right positive
    (prefixPair_residualTargetDefect_profile Target corridor 0 right.1
      (Nat.zero_le _) defect)

end Pair

/-! ## Part 2: the Lean (F2) fires at segment 1 of every corridor

`FirstFailureDefect` at `(0, 1)` needs only equal states: the two readings are
separated by the path context of length 3 between the entry foot and `head 1`
(the full reading closes a 4-cycle; the retained reading `J_0 = {foot}` is
edgeless, so its gluing is acyclic). -/

section Fires

/-- An edgeless piece glued to a path context has no cycle at all. -/
theorem no_cycle_glue_edgeless {B : Boundary.{v}} (L : BoundaryPiece B)
    (edgeless : ∀ a b, ¬ L.graph.Adj a b) {x y : B.Vertex} (hxy : x ≠ y)
    {m : ℕ} (hm : 2 ≤ m) (LengthOK : ℕ → Prop) :
    ¬ HasCycleWithLength LengthOK (glue L (pathContext x y m)) := by
  rintro ⟨certificate⟩
  have hc := certificate.isCycle
  rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
      (piece := L) (outside := pathContext x y m) hc with
    ⟨pb, lifted, liftedCycle, _⟩ | ⟨inner, hmem⟩ | ⟨a, a', ne, _, _, adj, _⟩
  · exact edgeless _ _ (lifted.adj_snd liftedCycle.not_nil)
  · have hi := inner.down.isLt
    have hat : gat L x y m (inner.down.val + 1) = Sum.inr (Sum.inr inner) := by
      unfold gat at_
      rw [dif_neg (by omega), dif_pos (by omega)]
      rfl
    have all := cycle_contains_path (P := L) hxy (by omega) hc
      (p₀ := inner.down.val + 1) (by omega) (by omega) (hat ▸ hmem)
    have zeroMem := all 0 (Nat.zero_le _)
    obtain ⟨w₁, w₂, different, a₁, a₂, _, _⟩ := cycle_two_neighbours hc zeroMem
    have only : ∀ w, (glueGraph L (pathContext x y m)).Adj (gat L x y m 0) w →
        w = gat L x y m 1 := by
      intro w h
      rcases (glueGraph_adj_iff _ _ _ _).mp h with owns | owns
      · obtain ⟨pa, pb, padj, _, _⟩ := owns
        exact (edgeless _ _ padj).elim
      · obtain ⟨ca, cb, cadj, ha, hb⟩ := owns
        have ha' : ca = at_ x y m 0 := (contextEmbedding L _).injective ha
        subst ha'
        obtain ⟨p, q, hp, hq, rel⟩ := pathContext_adj_pos cadj
        rw [pos_at x y m hxy (by omega) (Nat.zero_le _)] at hp
        cases hp
        obtain ⟨_, hbq⟩ := at_of_pos x y m (by omega) hq
        subst hbq
        rcases rel with rfl | h
        · exact hb.symm
        · omega
    exact different ((only _ a₁).trans (only _ a₂).symm)
  · obtain ⟨p, q, hp, hq, rel⟩ := pathContext_adj_pos adj
    rcases pos_inl hp with rfl | rfl <;> rcases pos_inl hq with rfl | rfl <;> omega

variable {object : FiniteObject.{v}} {windows component : Finset object.Vertex}

/-- `J_1 = {foot, head 1}`: the two members of the first prefix. -/
theorem mem_prefixSupport_one
    (corridor : ColdCorridor.Corridor object windows component)
    (long : 1 ≤ corridor.inside.1.length) (vertex : object.Vertex)
    (member : vertex ∈ corridor.prefixSupport 1) :
    vertex = corridor.entryStub.1 ∨ vertex = corridor.head ⟨1, by omega⟩ := by
  obtain ⟨s, le, rfl⟩ := (mem_prefixSupport_iff_head corridor 1 vertex).1 member
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 le with zero | one
  · left
    rw [← head_zero corridor]
    exact congrArg corridor.head (Fin.ext zero)
  · right
    exact congrArg corridor.head (Fin.ext one)

/-- **The Lean (F2) separation holds at `(0, 1)`.**  On an object of minimum
degree `≥ 2`, for every corridor of length `≥ 1` in an outside component, the
readings `retainedPiece J_1 J_0` and `piece J_1` are separated by a context
(the length-3 path from the foot to `head 1`), for any `LengthOK` accepting `4`. -/
theorem prefix_zero_one_targetDefect (LengthOK : ℕ → Prop) (four : LengthOK 4)
    (baseline : ∀ vertex : object.Vertex, 2 ≤ object.degree vertex)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (long : 1 ≤ corridor.inside.1.length) :
    Response.TargetDefect (HasCycleWithLength LengthOK)
      (SupportAtom.retainedPiece object (corridor.prefixSupport 1)
        (corridor.prefixSupport 0))
      (SupportAtom.piece object (corridor.prefixSupport 1)) := by
  classical
  let one : corridor.Segment := ⟨1, by omega⟩
  let foot := corridor.entryStub.1
  let h1 := corridor.head one
  have adj : object.graph.Adj foot h1 := by
    have := head_adj_succ corridor 0 (by omega)
    rw [head_zero] at this
    exact this
  have footB := foot_mem_cutBoundary outside corridor 1
  have h1In : h1 ∈ corridor.prefixSupport 1 :=
    (head_mem_prefixSupport_iff corridor one 1).2 le_rfl
  have h1B : h1 ∈ SupportAtom.cutBoundary object (corridor.prefixSupport 1) := by
    rw [SupportAtom.mem_cutBoundary_iff]
    refine ⟨h1In, ?_⟩
    by_contra inside
    push Not at inside
    have sub : object.graph.neighborSet h1 ⊆ {foot} := by
      intro w hw
      have mem := inside w hw
      rcases mem_prefixSupport_one corridor long w mem with rfl | rfl
      · exact Set.mem_singleton _
      · exact (hw.ne rfl).elim
    have le := Set.ncard_le_ncard sub (Set.finite_singleton _)
    rw [Set.ncard_singleton, ← FiniteObject.degree_eq_ncard_neighborSet] at le
    have := baseline h1
    omega
  let x : (SupportAtom.boundary object (corridor.prefixSupport 1)).Vertex := ⟨foot, footB⟩
  let y : (SupportAtom.boundary object (corridor.prefixSupport 1)).Vertex := ⟨h1, h1B⟩
  have hxy : x ≠ y := fun e => adj.ne (congrArg Subtype.val e)
  have pieceAdj : (SupportAtom.piece object (corridor.prefixSupport 1)).graph.Adj
      (.inl x) (.inl y) := adj
  let pieceWalk : (SupportAtom.piece object (corridor.prefixSupport 1)).graph.Walk
      (.inl x) (.inl y) := SimpleGraph.Walk.cons pieceAdj .nil
  have piecePath : pieceWalk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [pieceWalk, hxy]
  have positive : HasCycleWithLength LengthOK
      (glue (SupportAtom.piece object (corridor.prefixSupport 1)) (pathContext x y 3)) :=
    hasCycleWithLength_glue_of_crossing _ (pathContext x y 3) pieceWalk
      (contextWalk x y 3 hxy (by norm_num)) piecePath
      (contextWalk_isPath x y 3 hxy (by norm_num))
      (contextWalk_labels x y 3 hxy (by norm_num))
      (Or.inr (by rw [contextWalk_length]; norm_num))
      (by rw [contextWalk_length]; simpa [pieceWalk] using four)
  have edgeless : ∀ a b, ¬ (SupportAtom.retainedPiece object (corridor.prefixSupport 1)
      (corridor.prefixSupport 0)).graph.Adj a b := by
    intro a b h
    rw [retained_adj_iff] at h
    obtain ⟨hadj, ha, hb⟩ := h
    obtain ⟨sa, lea, ea⟩ := (mem_prefixSupport_iff_head corridor 0 _).1 ha
    obtain ⟨sb, leb, eb⟩ := (mem_prefixSupport_iff_head corridor 0 _).1 hb
    have : sa = sb := Fin.ext (by omega)
    rw [← ea, ← eb, this] at hadj
    exact hadj.ne rfl
  exact ⟨pathContext x y 3, fun equivalent =>
    no_cycle_glue_edgeless _ edgeless hxy (by norm_num) LengthOK
      (equivalent.mpr positive)⟩

open Hypostructure.Graph.Strategy.Spine in
/-- **The (F2) clause at segment 1 is exactly "states 0 and 1 agree".** -/
theorem coldFirstFailureDefectAt_one_iff (data : Parameters)
    (four : data.LengthOK 4)
    (baseline : ∀ vertex : object.Vertex, 2 ≤ object.degree vertex)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (long : 1 ≤ corridor.inside.1.length)
    (presentation : ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment) :
    ColdFirstFailureDefectAt data object corridor presentation index ⟨1, by omega⟩ ↔
      presentation.state (index ⟨0, by omega⟩) =
        presentation.state (index ⟨1, by omega⟩) := by
  constructor
  · rintro ⟨left, lt, same, _⟩
    have : left = ⟨0, by omega⟩ := Fin.ext (by simpa using lt)
    rw [this] at same
    exact same
  · intro same
    exact ⟨⟨0, by omega⟩, Nat.zero_lt_one, same,
      prefix_zero_one_targetDefect data.LengthOK four baseline outside corridor long⟩

open Hypostructure.Graph.Strategy.Spine in
/-- **The former all-presentations/all-indices form of `coldFailureDefect_excluded` is false** on
every object that has a corridor of length `≥ 1` in an outside component and a
presentation with one segment: with the constant index the states agree, so
(F2) occurs at segment 1. -/
theorem coldFailureDefect_excluded_is_false (data : Parameters)
    (four : data.LengthOK 4)
    (baseline : ∀ vertex : object.Vertex, 2 ≤ object.degree vertex)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (long : 1 ≤ corridor.inside.1.length)
    (presentation : ColdCorridor.Presentation data.coldSignature object)
    (p0 : presentation.Segment) :
    ¬ ∀ (index : corridor.Segment → presentation.Segment)
        (segment : corridor.Segment),
      ¬ ColdFirstFailureDefectAt data object corridor presentation index segment :=
  fun excluded => excluded (fun _ => p0) ⟨1, by omega⟩
    ((coldFirstFailureDefectAt_one_iff data four baseline outside corridor long
      presentation (fun _ => p0)).2 rfl)

open Hypostructure.Graph.Strategy.Spine in
/-- **(F2) ⇏ clause (b)**, in one statement: at segment 1 of every corridor the
(F2) clause holds whenever the two states agree, while the prefix coordinates
`{J_0, J_1}` carry no clause-(b) defect. -/
theorem coldF2_not_clauseB (data : Parameters)
    (four : data.LengthOK 4)
    (baseline : ∀ vertex : object.Vertex, 2 ≤ object.degree vertex)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (long : 1 ≤ corridor.inside.1.length)
    (presentation : ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (same : presentation.state (index ⟨0, by omega⟩) =
        presentation.state (index ⟨1, by omega⟩)) :
    ColdFirstFailureDefectAt data object corridor presentation index ⟨1, by omega⟩ ∧
      ¬ ResidualTargetDefect (HasCycleWithLength data.LengthOK) object
        (Finset.univ : Finset Bool) (prefixPairSupport corridor 0 1) :=
  ⟨(coldFirstFailureDefectAt_one_iff data four baseline outside corridor long
      presentation index).2 same,
    not_residualTargetDefect_prefixPair_zero _ outside corridor ⟨1, by omega⟩
      Nat.one_pos⟩

end Fires

/-! ## Part 3: the cut-state (two-label) reading makes clause (b) trivial

Reading a prefix `J` as a graph on its two cut-state interfaces
`T(J) = {foot, head}` (tex 7187-7197), the prefixes `J_1` (one edge) and `J_2`
(a two-edge path) of any corridor whose `J_2` is induced are the pieces below:
same labels, same `d_∂ = (1,1)`, and they are separated by a context.  So a
clause (b) that compared prefixes through their cut-state interface would fire
at every such corridor: `K .sparseSurplusSurvivor` would be refuted on every
counterexample with a corridor of length `≥ 2`, and the surviving branch would
be vacuous.  (Such pieces are also not pieces of G -- `G ≠ J ⊕_{T(J)} (G - J)`
once a third prefix vertex has an outside neighbour -- so "agree in G's actual
outside context" is not even defined for them.) -/

section TwoLabel

/-- The two-label interface `{x, y}` (`x = 0`, `y = 1`). -/
abbrev twoLabels : Boundary.{v} where
  Vertex := ULift.{v} (Fin 2)
  vertices := FinEnum.ofEquiv (Fin 2) Equiv.ulift

/-- `J_1` on `T(J_1)`: the single edge `x y`. -/
noncomputable abbrev edgePiece : BoundaryPiece twoLabels.{v} where
  Internal := ULift.{v} (Fin 0)
  internalVertices := FinEnum.ofEquiv (Fin 0) Equiv.ulift
  graph := SimpleGraph.fromRel fun a b =>
    a = .inl ⟨0⟩ ∧ b = .inl ⟨1⟩
  decideAdj := Classical.decRel _

/-- `J_2` on `T(J_2)`: the two-edge path `x z y`. -/
noncomputable abbrev twoPathPiece : BoundaryPiece twoLabels.{v} where
  Internal := ULift.{v} (Fin 1)
  internalVertices := FinEnum.ofEquiv (Fin 1) Equiv.ulift
  graph := SimpleGraph.fromRel fun a b =>
    (a = .inl ⟨0⟩ ∧ b = .inr ⟨0⟩) ∨ (a = .inr ⟨0⟩ ∧ b = .inl ⟨1⟩)
  decideAdj := Classical.decRel _

theorem edgePiece_profile :
    edgePiece.{v}.boundaryDegreeProfile = fun _ => 1 := by
  classical
  funext label
  unfold BoundaryPiece.boundaryDegreeProfile BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have key : ∀ i : Fin 2, edgePiece.{v}.pack.graph.neighborSet (.inl ⟨i⟩) =
      {.inl ⟨1 - i⟩} := by
    intro i
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    change (SimpleGraph.fromRel _).Adj _ _ ↔ _
    rw [SimpleGraph.fromRel_adj]
    rcases w with ⟨j⟩ | ⟨⟨k, hk⟩⟩
    · fin_cases i <;> fin_cases j <;> simp <;>
        (intro h; injection h with h; injection h with h; exact absurd h (by decide))
    · exact absurd hk (Nat.not_lt_zero _)
  rcases label with ⟨i⟩
  rw [key i, Set.ncard_singleton]

theorem twoPathPiece_profile :
    twoPathPiece.{v}.boundaryDegreeProfile = fun _ => 1 := by
  classical
  funext label
  unfold BoundaryPiece.boundaryDegreeProfile BoundaryPiece.boundaryDegree
  rw [FiniteObject.degree_eq_ncard_neighborSet]
  have key : ∀ i : Fin 2, twoPathPiece.{v}.pack.graph.neighborSet (.inl ⟨i⟩) =
      {.inr ⟨0⟩} := by
    intro i
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    change (SimpleGraph.fromRel _).Adj _ _ ↔ _
    rw [SimpleGraph.fromRel_adj]
    rcases w with ⟨j⟩ | ⟨k⟩
    · fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> fin_cases k <;> simp
  rcases label with ⟨i⟩
  rw [key i, Set.ncard_singleton]

/-- **Same `d_∂` fibre, separated by a context** (`targetDefect_of_size` with
the two-edge path of `J_2` against the edge `J_1`): in the cut-state reading
`J_1` and `J_2` are a clause-(b) identification failing the context test. -/
theorem edge_twoPath_sameFibre_targetDefect :
    edgePiece.{v}.boundaryDegreeProfile = twoPathPiece.{v}.boundaryDegreeProfile ∧
      Response.TargetDefect
        (HasCycleWithLength Core.DyadicLength.PowerOfTwoLength)
        edgePiece.{v} twoPathPiece.{v} := by
  classical
  refine ⟨by rw [edgePiece_profile, twoPathPiece_profile], ?_⟩
  have hxy : (⟨0⟩ : twoLabels.{v}.Vertex) ≠ ⟨1⟩ := by
    intro e; cases congrArg ULift.down e
  have a1 : twoPathPiece.{v}.graph.Adj (.inl ⟨0⟩) (.inr ⟨0⟩) := by
    change (SimpleGraph.fromRel _).Adj _ _
    rw [SimpleGraph.fromRel_adj]; simp
  have a2 : twoPathPiece.{v}.graph.Adj (.inr ⟨0⟩) (.inl ⟨1⟩) := by
    change (SimpleGraph.fromRel _).Adj _ _
    rw [SimpleGraph.fromRel_adj]; simp
  let walk : twoPathPiece.{v}.graph.Walk (.inl ⟨0⟩) (.inl ⟨1⟩) :=
    .cons a1 (.cons a2 .nil)
  have path : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [walk]
  have free : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength
      (BoundaryPiece.pack edgePiece.{v}) := by
    rintro ⟨certificate⟩
    letI : Fintype (BoundaryPiece.pack edgePiece.{v}).Vertex :=
      @FinEnum.instFintype _ (BoundaryPiece.pack edgePiece.{v}).vertices
    have three := certificate.isCycle.three_le_length
    have le := length_le_card_of_cycle certificate.isCycle
    have card : Nat.card (BoundaryPiece.pack edgePiece.{v}).Vertex = 2 := by
      change Nat.card (ULift.{v} (Fin 2) ⊕ ULift.{v} (Fin 0)) = 2
      simp
    rw [Fintype.card_eq_nat_card, card] at le
    omega
  have small : twoLabels.{v}.vertexCount + edgePiece.{v}.internalVertexCount ≤
      walk.length := by
    have c1 : twoLabels.{v}.vertexCount = 2 := by
      simp only [Boundary.vertexCount, FinEnum.card]
      simp [List.Nodup.dedup (List.nodup_finRange _)]
    have c2 : edgePiece.{v}.internalVertexCount = 0 := by
      simp [BoundaryPiece.internalVertexCount, FinEnum.card]
    rw [c1, c2]
    simp [walk]
  exact targetDefect_of_size hxy edgePiece twoPathPiece free walk path small

end TwoLabel

end Hypostructure.Graph.ColdRepairF2

/-! ## Part 4: at G, (F2) is exactly an earlier equal state (group F2, 2026-09-27)

* `prefix_profile_ne`, `not_residualTargetDefect_prefixPair`: for **every** pair
  `left < right` of a corridor of G in an outside component, the two (F2)
  readings lie in different `d_∂` fibres (`head right` is on `∂J_right` and
  loses its edge to `head (right-1)`), so no prefix pair is a clause-(b) exit.
* `prefix_targetDefect`, `coldFirstFailureDefectAt_iff`: on an object with no
  accepted cycle whose target accepts every `2^k`, `k ≥ 2`, the Lean (F2) at
  `right` holds iff some earlier segment carries the same state, for every
  corridor, presentation and index.  The separating context is the path of
  length `2^(right+2) − right` from `head right` to the foot; in the `J_left`
  reading `head right` is isolated, so the gluing's cycles are the object's.
* `first_lt_stateBound`: states pairwise distinct up to `first` force
  `first < Q_cold`.

So `Contracts.Spine.coldFailureDefect_excluded` at G is equivalent to: G's cut
states along each retained corridor are pairwise distinct up to its first
failure (a terminal or (F4) event), and then that failure is read within
`Q_cold` states. -/

namespace Hypostructure.Graph.ColdRepairF2.EqualStates

open Hypostructure Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ColdRepairF2

universe v

variable {object : FiniteObject.{v}} {windows component : Finset object.Vertex}

/-- The head of an initial segment is on the cut boundary of its own prefix:
before the terminal segment its successor on the inside path is outside the
prefix; at the terminal segment it is the successor foot, whose window
endpoint is outside the component. -/
theorem head_mem_cutBoundary
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) :
    corridor.head right ∈
      SupportAtom.cutBoundary object (corridor.prefixSupport right.1) := by
  rw [SupportAtom.mem_cutBoundary_iff]
  refine ⟨(head_mem_prefixSupport_iff corridor right right.1).2 le_rfl, ?_⟩
  by_cases terminal : right.1 < corridor.inside.1.length
  · refine ⟨corridor.head ⟨right.1 + 1, by omega⟩, ?_, ?_⟩
    · exact head_adj_succ corridor right.1 terminal
    · rw [head_mem_prefixSupport_iff]; simp
  · have eq : right.1 = corridor.inside.1.length := by have := right.2; omega
    have stub := (ColdCorridor.mem_boundaryStubs_iff object windows component _).1
      (List.get_mem _ (ColdCorridor.successorIndex corridor.positive corridor.entry))
    have headEq : corridor.head right =
        ((ColdCorridor.boundaryStubs object windows component).get
          (ColdCorridor.successorIndex corridor.positive corridor.entry)).1 := by
      unfold ColdCorridor.Corridor.head
      rw [eq, SimpleGraph.Walk.getVert_length]
      rfl
    rw [headEq]
    refine ⟨_, stub.2.2, fun inside => ?_⟩
    exact Finset.disjoint_left.mp outside.1
      (prefixSupport_subset_component corridor right.1 inside) stub.2.1

/-- **Every (F2) pair is a boundary-degree separation.**  For `left < right`,
`head right` is on the cut boundary of `J_right` and loses its corridor edge to
`head (right-1)` in the `J_left` reading. -/
theorem prefix_profile_ne
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (lt : left.1 < right.1) :
    (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport left.1)).boundaryDegreeProfile ≠
      (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport right.1)).boundaryDegreeProfile := by
  intro same
  let previous : corridor.Segment := ⟨right.1 - 1, by omega⟩
  have adj : object.graph.Adj (corridor.head right) (corridor.head previous) := by
    have := head_adj_succ corridor (right.1 - 1) (by have := right.2; omega)
    have e : (⟨right.1 - 1 + 1, by omega⟩ : corridor.Segment) = right :=
      Fin.ext (by simp; omega)
    rw [e] at this
    exact this.symm
  have prevIn : corridor.head previous ∈ corridor.prefixSupport right.1 :=
    (head_mem_prefixSupport_iff corridor previous right.1).2 (by simp [previous])
  have := retained_profile_eq_imp _ _ same (corridor.head right)
    (head_mem_cutBoundary outside corridor right) (corridor.head previous) prevIn adj
  have out := (head_mem_prefixSupport_iff corridor right left.1).1 this.1
  omega

/-- **No (F2) pair is a clause-(b) exit**, at every pair `left < right`
(generalizing `not_residualTargetDefect_prefixPair_zero`). -/
theorem not_residualTargetDefect_prefixPair
    (Target : FiniteObject.{v} → Prop)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (lt : left.1 < right.1) :
    ¬ ResidualTargetDefect Target object (Finset.univ : Finset Bool)
      (prefixPairSupport corridor left.1 right.1) := fun defect =>
  prefix_profile_ne outside corridor left right lt
    (prefixPair_residualTargetDefect_profile Target corridor left.1 right.1
      lt.le defect)

/-! ## The separating context at every pair `left < right` -/

/-- The inside-path vertex at position `i`. -/
noncomputable def pt (corridor : ColdCorridor.Corridor object windows component)
    (i : Nat) : object.Vertex :=
  (corridor.inside.1.getVert i).1

theorem pt_mem (corridor : ColdCorridor.Corridor object windows component)
    {i n : Nat} (hi : i ≤ n) (hn : n ≤ corridor.inside.1.length) :
    pt corridor i ∈ corridor.prefixSupport n :=
  (head_mem_prefixSupport_iff corridor ⟨i, by omega⟩ n).2 hi

theorem pt_injOn (corridor : ColdCorridor.Corridor object windows component)
    {i j : Nat} (hi : i ≤ corridor.inside.1.length) (hj : j ≤ corridor.inside.1.length)
    (e : pt corridor i = pt corridor j) : i = j :=
  corridor.inside.2.getVert_injOn (by simpa using hi) (by simpa using hj)
    (Subtype.ext e)

theorem decode_injective (Z : Finset object.Vertex) :
    Function.Injective (SupportAtom.pieceDecode object Z) := by
  intro a b e
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (Subtype.ext e)
  · have : a.1 = b.1 := e
    exact absurd (this ▸ a.2) b.2.2
  · have : b.1 = a.1 := e.symm
    exact absurd (this ▸ b.2) a.2.2
  · exact congrArg Sum.inr (Subtype.ext e)

/-- The piece-side vertex of position `i` of `J_n`. -/
noncomputable def V (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hn : n ≤ corridor.inside.1.length) (i : Nat) (hi : i ≤ n) :
    (SupportAtom.boundary object (corridor.prefixSupport n)).Vertex ⊕
      SupportAtom.PieceInternal object (corridor.prefixSupport n) :=
  enc (corridor.prefixSupport n) (pt corridor i) (pt_mem corridor hi hn)

/-- The prefix walk inside `piece J_n`, from position `0` to position `k`. -/
noncomputable def prefixPieceWalk
    (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hn : n ≤ corridor.inside.1.length) :
    (k : Nat) → (hk : k ≤ n) →
      (SupportAtom.piece object (corridor.prefixSupport n)).graph.Walk
        (V corridor n hn 0 (Nat.zero_le _)) (V corridor n hn k hk)
  | 0, _ => .nil
  | k + 1, hk =>
      (prefixPieceWalk corridor n hn k (by omega)).concat (by
        change object.graph.Adj
          (SupportAtom.pieceDecode object _ (V corridor n hn k (by omega)))
          (SupportAtom.pieceDecode object _ (V corridor n hn (k + 1) hk))
        simp only [V, pieceDecode_enc]
        exact head_adj_succ corridor k (by omega))

theorem prefixPieceWalk_length
    (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hn : n ≤ corridor.inside.1.length) :
    ∀ k (hk : k ≤ n), (prefixPieceWalk corridor n hn k hk).length = k
  | 0, _ => rfl
  | k + 1, hk => by
      simp [prefixPieceWalk, SimpleGraph.Walk.length_concat,
        prefixPieceWalk_length corridor n hn k]

theorem decode_V (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hn : n ≤ corridor.inside.1.length) (i : Nat) (hi : i ≤ n) :
    SupportAtom.pieceDecode object (corridor.prefixSupport n) (V corridor n hn i hi) =
      pt corridor i :=
  pieceDecode_enc _ _ _

theorem prefixPieceWalk_decode_support
    (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hn : n ≤ corridor.inside.1.length) :
    ∀ k (hk : k ≤ n),
      (prefixPieceWalk corridor n hn k hk).support.map
          (SupportAtom.pieceDecode object (corridor.prefixSupport n)) =
        (List.range (k + 1)).map (pt corridor)
  | 0, _ => by
      erw [prefixPieceWalk, SimpleGraph.Walk.support_nil, List.map_cons, List.map_nil,
        decode_V]
      rfl
  | k + 1, hk => by
      erw [prefixPieceWalk, SimpleGraph.Walk.support_concat,
        List.map_append, prefixPieceWalk_decode_support corridor n hn k,
        List.map_cons, List.map_nil, decode_V, List.range_succ (n := k + 1),
        List.map_append, List.map_cons, List.map_nil]

theorem prefixPieceWalk_isPath
    (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hn : n ≤ corridor.inside.1.length) (k : Nat) (hk : k ≤ n) :
    (prefixPieceWalk corridor n hn k hk).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  apply List.Nodup.of_map (SupportAtom.pieceDecode object (corridor.prefixSupport n))
  rw [prefixPieceWalk_decode_support]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj e
  simp only [List.mem_range] at hi hj
  exact pt_injOn corridor (by omega) (by omega) e

/-- **The (F2) separation at every pair `left < right` of G's corridor.**  The
path context of length `2^(right+2) − right` from `head right` to the foot
closes a cycle of length `2^(right+2)` with `piece J_right`; in the `J_left`
reading `head right` is isolated, so every cycle of that gluing lies in the
reading, i.e. is a cycle of G. -/
theorem prefix_targetDefect (LengthOK : ℕ → Prop)
    (accept : ∀ k, 2 ≤ k → LengthOK (2 ^ k))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (lt : left.1 < right.1) :
    Response.TargetDefect (HasCycleWithLength LengthOK)
      (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport left.1))
      (SupportAtom.piece object (corridor.prefixSupport right.1)) := by
  classical
  set n := right.1 with hn
  have hnLen : n ≤ corridor.inside.1.length := by have := right.2; omega
  set Z := corridor.prefixSupport n
  have headB : pt corridor n ∈ SupportAtom.cutBoundary object Z :=
    head_mem_cutBoundary outside corridor right
  have footB : pt corridor 0 ∈ SupportAtom.cutBoundary object Z := by
    have := foot_mem_cutBoundary outside corridor n
    rw [← head_zero corridor] at this
    exact this
  let x : (SupportAtom.boundary object Z).Vertex := ⟨pt corridor n, headB⟩
  let y : (SupportAtom.boundary object Z).Vertex := ⟨pt corridor 0, footB⟩
  have hxy : x ≠ y := by
    intro e
    have := pt_injOn corridor hnLen (Nat.zero_le _)
      (show pt corridor n = pt corridor 0 from
        congrArg (fun z : (SupportAtom.boundary object Z).Vertex => z.1) e)
    omega
  have Vx : V corridor n hnLen n le_rfl = .inl x := by
    unfold V enc; rw [dif_pos headB]
  have Vy : V corridor n hnLen 0 (Nat.zero_le _) = .inl y := by
    unfold V enc; rw [dif_pos footB]
  let Rwalk : (SupportAtom.piece object Z).graph.Walk (.inl x) (.inl y) :=
    ((prefixPieceWalk corridor n hnLen n le_rfl).reverse).copy Vx Vy
  have Rpath : Rwalk.IsPath :=
    (SimpleGraph.Walk.isPath_copy _ _ _).2
      (prefixPieceWalk_isPath corridor n hnLen n le_rfl).reverse
  have Rlen : Rwalk.length = n := by
    change (((prefixPieceWalk corridor n hnLen n le_rfl).reverse).copy Vx Vy).length = n
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      prefixPieceWalk_length]
  set m := 2 ^ (n + 2) - n with hm
  have pow : n + 4 ≤ 2 ^ (n + 2) := by
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_add]; omega
  have hm2 : 2 ≤ m := by omega
  refine ⟨pathContext x y m, fun equivalent => ?_⟩
  have positive : HasCycleWithLength LengthOK
      (glue (SupportAtom.piece object Z) (pathContext x y m)) := by
    refine hasCycleWithLength_glue_of_crossing _ (pathContext x y m) Rwalk
      (contextWalk x y m hxy (by omega)) Rpath
      (contextWalk_isPath x y m hxy (by omega))
      (contextWalk_labels x y m hxy (by omega))
      (Or.inr (by rw [contextWalk_length]; omega)) ?_
    rw [contextWalk_length, Rlen, show n + m = 2 ^ (n + 2) by omega]
    exact accept _ (by omega)
  have negative := equivalent.mpr positive
  -- `x = head right` is isolated in the `J_left` reading
  let L := SupportAtom.retainedPiece object Z (corridor.prefixSupport left.1)
  have isolated : ∀ b, ¬ L.graph.Adj (.inl x) b := by
    intro b h
    rw [retained_adj_iff] at h
    have := (head_mem_prefixSupport_iff corridor right left.1).1 h.2.1
    omega
  obtain ⟨certificate⟩ := negative
  have hc := certificate.isCycle
  rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
      (piece := L) (outside := pathContext x y m) hc with
    ⟨pb, lifted, liftedCycle, liftedLength⟩ | ⟨inner, hmem⟩ |
      ⟨a, a', ne, _, _, adj, _⟩
  · -- a cycle of the reading is a cycle of G
    apply avoids
    let decodeHom : L.graph →g object.graph :=
      ⟨SupportAtom.pieceDecode object Z, fun h => by
        rw [retained_adj_iff] at h; exact h.1⟩
    exact ⟨⟨_, lifted.map decodeHom,
      liftedCycle.map (decode_injective Z),
      by rw [SimpleGraph.Walk.length_map, liftedLength]; exact certificate.length_ok⟩⟩
  · have hi := inner.down.isLt
    have hat : gat L x y m (inner.down.val + 1) = Sum.inr (Sum.inr inner) := by
      unfold gat at_
      rw [dif_neg (by omega), dif_pos (by omega)]
      rfl
    have all := cycle_contains_path (P := L) hxy (by omega) hc
      (p₀ := inner.down.val + 1) (by omega) (by omega) (hat ▸ hmem)
    have zeroMem := all 0 (Nat.zero_le _)
    obtain ⟨w₁, w₂, different, a₁, a₂, _, _⟩ := cycle_two_neighbours hc zeroMem
    have only : ∀ w, (glueGraph L (pathContext x y m)).Adj (gat L x y m 0) w →
        w = gat L x y m 1 := by
      intro w h
      rcases (glueGraph_adj_iff _ _ _ _).mp h with owns | owns
      · obtain ⟨pa, pb, padj, ha, _⟩ := owns
        have g0 : gat L x y m 0 = Sum.inl x := by
          simp [gat, at_zero, contextEmbedding]
        rw [g0] at ha
        rcases pa with pa | pa
        · have : pa = x := by simpa [pieceEmbedding] using ha
          subst this
          exact (isolated _ padj).elim
        · simp [pieceEmbedding] at ha
      · obtain ⟨ca, cb, cadj, ha, hb⟩ := owns
        have ha' : ca = at_ x y m 0 := (contextEmbedding L _).injective ha
        subst ha'
        obtain ⟨p, q, hp, hq, rel⟩ := pathContext_adj_pos cadj
        rw [pos_at x y m hxy (by omega) (Nat.zero_le _)] at hp
        cases hp
        obtain ⟨_, hbq⟩ := at_of_pos x y m (by omega) hq
        subst hbq
        rcases rel with rfl | h
        · exact hb.symm
        · omega
    exact different ((only _ a₁).trans (only _ a₂).symm)
  · obtain ⟨p, q, hp, hq, rel⟩ := pathContext_adj_pos adj
    rcases pos_inl hp with rfl | rfl <;> rcases pos_inl hq with rfl | rfl <;> omega

open Hypostructure.Graph.Strategy.Spine in
/-- **At G, (F2) at `right` is exactly an earlier equal cut state.** -/
theorem coldFirstFailureDefectAt_iff (data : Parameters)
    (accept : ∀ k, 2 ≤ k → data.LengthOK (2 ^ k))
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (presentation : ColdCorridor.Presentation data.coldSignature object)
    (index : corridor.Segment → presentation.Segment)
    (right : corridor.Segment) :
    ColdFirstFailureDefectAt data object corridor presentation index right ↔
      ∃ left : corridor.Segment, left.1 < right.1 ∧
        presentation.state (index left) = presentation.state (index right) := by
  constructor
  · rintro ⟨left, lt, same, _⟩
    exact ⟨left, lt, same⟩
  · rintro ⟨left, lt, same⟩
    exact ⟨left, lt, same,
      prefix_targetDefect data.LengthOK accept avoids outside corridor left right lt⟩

/-- **The hook forces short corridors.**  If no segment up to `first` repeats an
earlier state, then `first < Q_cold`: the `first + 1` states read are distinct
elements of the `Q_cold`-element state type. -/
theorem first_lt_stateBound {S : ColdCorridor.DeclaredSignature}
    (corridor : ColdCorridor.Corridor object windows component)
    (presentation : ColdCorridor.Presentation S object)
    (index : corridor.Segment → presentation.Segment)
    (first : corridor.Segment)
    (distinct : ∀ left right : corridor.Segment, left.1 < right.1 →
      right.1 ≤ first.1 →
        presentation.state (index left) ≠ presentation.state (index right)) :
    first.1 < ColdCorridor.stateBound S := by
  classical
  let f : Fin (first.1 + 1) → ColdCorridor.CutState S :=
    fun i => presentation.state (index ⟨i.1, by have := first.2; have := i.2; omega⟩)
  have inj : Function.Injective f := by
    intro i j e
    by_contra ne
    rcases Nat.lt_or_gt_of_ne (fun h => ne (Fin.ext h)) with h | h
    · exact distinct ⟨i.1, by have := first.2; have := i.2; omega⟩
        ⟨j.1, by have := first.2; have := j.2; omega⟩ h
        (by have := j.2; simp only; omega) e
    · exact distinct ⟨j.1, by have := first.2; have := j.2; omega⟩
        ⟨i.1, by have := first.2; have := i.2; omega⟩ h
        (by have := i.2; simp only; omega) e.symm
  have := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at this
  unfold ColdCorridor.stateBound
  omega

end Hypostructure.Graph.ColdRepairF2.EqualStates

#print axioms Hypostructure.Graph.ColdRepairF2.coldF2_not_clauseB
#print axioms Hypostructure.Graph.ColdRepairF2.coldFailureDefect_excluded_is_false
#print axioms Hypostructure.Graph.ColdRepairF2.prefixPair_residualTargetDefect_profile
#print axioms Hypostructure.Graph.ColdRepairF2.retained_profile_eq_imp
#print axioms Hypostructure.Graph.ColdRepairF2.edge_twoPath_sameFibre_targetDefect
#print axioms Hypostructure.Graph.ColdRepairF2.EqualStates.coldFirstFailureDefectAt_iff
#print axioms Hypostructure.Graph.ColdRepairF2.EqualStates.not_residualTargetDefect_prefixPair
#print axioms Hypostructure.Graph.ColdRepairF2.EqualStates.first_lt_stateBound
