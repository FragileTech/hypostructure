import Hypostructure.Graph.GluedCycleSides
import Hypostructure.Graph.ColdGermFamily

/-!
# Equal cut states on a cold corridor: the separating path context

Vocabulary-free library for node `[153]`'s (F2) clause at G
(`lem:cold-corridor-first-failure` (ii), tex 7187-7197, 7265-7270).

For a cold return corridor in an outside component, and two segments
`left < right`, the two readings of the pair are `retainedPiece J_right J_left`
and `piece J_right` on the one boundary `∂J_right`:

* `prefix_profile_ne`: they have different boundary-degree profiles --
  `head right` is on `∂J_right` and loses its corridor edge to `head (right-1)`
  in the `J_left` reading;
* `prefixContext`, `prefixContext_piece_cycle`, `prefixContext_retained_noCycle`:
  the path context of length `2^(right+2) − right` from `head right` to the
  entry foot closes a cycle of length `2^(right+2)` with `piece J_right`, and
  closes no accepted cycle with the `J_left` reading on an object with no
  accepted cycle (in that reading `head right` is isolated, so every cycle of
  the gluing is a cycle of the object);
* `first_lt_stateBound`: pairwise distinct states up to `first` force
  `first < Q_cold`.

The mathematics is the group-F2 analysis (2026-09-27); this module is its live
restatement, not an import of the quarantined evidence file.
-/

namespace Hypostructure.Graph.ColdEqualStates

open Hypostructure Hypostructure.Graph

universe u

/-! ## A generic walk fact -/
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

end Hypostructure.Graph.ColdEqualStates

namespace Hypostructure.Graph.ColdEqualStates

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

/-- The entry foot of a corridor is the head of its segment `0`, and it is on
the cut boundary of every prefix. -/
theorem footHead_mem_cutBoundary
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component) (n : Nat) :
    corridor.head ⟨0, Nat.succ_pos _⟩ ∈
      SupportAtom.cutBoundary object (corridor.prefixSupport n) := by
  rw [head_zero]
  exact foot_mem_cutBoundary outside corridor n

/-- The head of segment `right`, as a boundary label of `J_right`. -/
noncomputable def headLabel
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) :
    (SupportAtom.boundary object (corridor.prefixSupport right.1)).Vertex :=
  ⟨corridor.head right, head_mem_cutBoundary outside corridor right⟩

/-- The entry foot, as a boundary label of `J_right`. -/
noncomputable def footLabel
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) :
    (SupportAtom.boundary object (corridor.prefixSupport right.1)).Vertex :=
  ⟨corridor.head ⟨0, Nat.succ_pos _⟩, footHead_mem_cutBoundary outside corridor right.1⟩

/-- **The separating context of an (F2) pair ending at `right`**: a path of
`2^(right+2) − right` edges, with fresh interior, glued at `head right` and at
the entry foot, the two labels of `T(J_right) ∩ ∂J_right`. -/
noncomputable def prefixContext
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) :
    OutsideContext (SupportAtom.boundary object (corridor.prefixSupport right.1)) :=
  pathContext (headLabel outside corridor right) (footLabel outside corridor right)
    (2 ^ (right.1 + 2) - right.1)

theorem headLabel_ne_footLabel
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) (positive : 0 < right.1) :
    headLabel outside corridor right ≠ footLabel outside corridor right := by
  intro e
  have hnLen : right.1 ≤ corridor.inside.1.length := by have := right.2; omega
  have := pt_injOn corridor hnLen (Nat.zero_le _)
    (show pt corridor right.1 = pt corridor 0 from
      congrArg (fun z : (SupportAtom.boundary object
        (corridor.prefixSupport right.1)).Vertex => z.1) e)
  omega

theorem piece_cycle_aux (LengthOK : ℕ → Prop)
    (accept : ∀ k, 2 ≤ k → LengthOK (2 ^ k))
    (corridor : ColdCorridor.Corridor object windows component)
    (n : Nat) (hnLen : n ≤ corridor.inside.1.length) (positive : 0 < n)
    (headB : pt corridor n ∈ SupportAtom.cutBoundary object (corridor.prefixSupport n))
    (footB : pt corridor 0 ∈ SupportAtom.cutBoundary object (corridor.prefixSupport n)) :
    HasCycleWithLength LengthOK
      (glue (SupportAtom.piece object (corridor.prefixSupport n))
        (pathContext (B := SupportAtom.boundary object (corridor.prefixSupport n))
          ⟨pt corridor n, headB⟩ ⟨pt corridor 0, footB⟩ (2 ^ (n + 2) - n))) := by
  classical
  let x : (SupportAtom.boundary object (corridor.prefixSupport n)).Vertex :=
    ⟨pt corridor n, headB⟩
  let y : (SupportAtom.boundary object (corridor.prefixSupport n)).Vertex :=
    ⟨pt corridor 0, footB⟩
  have hxy : x ≠ y := by
    intro e
    have := pt_injOn corridor hnLen (Nat.zero_le _)
      (show pt corridor n = pt corridor 0 from
        congrArg (fun z : (SupportAtom.boundary object
          (corridor.prefixSupport n)).Vertex => z.1) e)
    omega
  have Vx : V corridor n hnLen n le_rfl = .inl x := by
    unfold V enc; rw [dif_pos headB]
  have Vy : V corridor n hnLen 0 (Nat.zero_le _) = .inl y := by
    unfold V enc; rw [dif_pos footB]
  let Rwalk : (SupportAtom.piece object (corridor.prefixSupport n)).graph.Walk
      (.inl x) (.inl y) :=
    ((prefixPieceWalk corridor n hnLen n le_rfl).reverse).copy Vx Vy
  have Rpath : Rwalk.IsPath :=
    (SimpleGraph.Walk.isPath_copy _ _ _).2
      (prefixPieceWalk_isPath corridor n hnLen n le_rfl).reverse
  have Rlen : Rwalk.length = n := by
    change (((prefixPieceWalk corridor n hnLen n le_rfl).reverse).copy Vx Vy).length = n
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
      prefixPieceWalk_length]
  have pow : n + 4 ≤ 2 ^ (n + 2) := by
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_add]; omega
  refine hasCycleWithLength_glue_of_crossing _ (pathContext x y (2 ^ (n + 2) - n)) Rwalk
    (contextWalk x y _ hxy (by omega)) Rpath
    (contextWalk_isPath x y _ hxy (by omega))
    (contextWalk_labels x y _ hxy (by omega))
    (Or.inr (by rw [contextWalk_length]; omega)) ?_
  rw [contextWalk_length, Rlen, show n + (2 ^ (n + 2) - n) = 2 ^ (n + 2) by omega]
  exact accept _ (by omega)

/-- **The context closes a target cycle with `piece J_right`**: the corridor
prefix from the foot to `head right` (length `right`) and the context path
(length `2^(right+2) − right`) form a cycle of length `2^(right+2)`. -/
theorem prefixContext_piece_cycle (LengthOK : ℕ → Prop)
    (accept : ∀ k, 2 ≤ k → LengthOK (2 ^ k))
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (right : corridor.Segment) (positive : 0 < right.1) :
    HasCycleWithLength LengthOK
      (glue (SupportAtom.piece object (corridor.prefixSupport right.1))
        (prefixContext outside corridor right)) :=
  piece_cycle_aux LengthOK accept corridor right.1 (by have := right.2; omega) positive
    (head_mem_cutBoundary outside corridor right)
    (footHead_mem_cutBoundary outside corridor right.1)

theorem retained_noCycle_aux (LengthOK : ℕ → Prop)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (corridor : ColdCorridor.Corridor object windows component)
    (left : corridor.Segment) (n : Nat) (hnLen : n ≤ corridor.inside.1.length)
    (lt : left.1 < n)
    (headB : pt corridor n ∈ SupportAtom.cutBoundary object (corridor.prefixSupport n))
    (footB : pt corridor 0 ∈ SupportAtom.cutBoundary object (corridor.prefixSupport n)) :
    ¬ HasCycleWithLength LengthOK
      (glue (SupportAtom.retainedPiece object (corridor.prefixSupport n)
          (corridor.prefixSupport left.1))
        (pathContext (B := SupportAtom.boundary object (corridor.prefixSupport n))
          ⟨pt corridor n, headB⟩ ⟨pt corridor 0, footB⟩ (2 ^ (n + 2) - n))) := by
  classical
  let Z := corridor.prefixSupport n
  let x : (SupportAtom.boundary object Z).Vertex := ⟨pt corridor n, headB⟩
  let y : (SupportAtom.boundary object Z).Vertex := ⟨pt corridor 0, footB⟩
  have hxy : x ≠ y := by
    intro e
    have := pt_injOn corridor hnLen (Nat.zero_le _)
      (show pt corridor n = pt corridor 0 from
        congrArg (fun z : (SupportAtom.boundary object Z).Vertex => z.1) e)
    omega
  let m := 2 ^ (n + 2) - n
  have pow : n + 4 ≤ 2 ^ (n + 2) := by
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_add]; omega
  have hm2 : 2 ≤ m := by omega
  let L := SupportAtom.retainedPiece object Z (corridor.prefixSupport left.1)
  change ¬ HasCycleWithLength LengthOK (glue L (pathContext x y m))
  have isolated : ∀ b, ¬ L.graph.Adj (.inl x) b := by
    intro b h
    rw [retained_adj_iff] at h
    have := (head_mem_prefixSupport_iff corridor ⟨n, by omega⟩ left.1).1 h.2.1
    simp only at this
    omega
  rintro ⟨certificate⟩
  have hc := certificate.isCycle
  rcases GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart
      (piece := L) (outside := pathContext x y m) hc with
    ⟨pb, lifted, liftedCycle, liftedLength⟩ | ⟨inner, hmem⟩ |
      ⟨a, a', ne, _, _, adj, _⟩
  · -- a cycle of the reading is a cycle of the object
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

/-- **The context closes no target cycle with the `J_left` reading.**  In
`retainedPiece J_right J_left`, `head right` has no retained edge, so a cycle of
the gluing through the context interior would pass through the isolated label;
every other cycle of the gluing lies in the reading and is a cycle of the
object, which has none. -/
theorem prefixContext_retained_noCycle (LengthOK : ℕ → Prop)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (lt : left.1 < right.1) :
    ¬ HasCycleWithLength LengthOK
      (glue (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
          (corridor.prefixSupport left.1))
        (prefixContext outside corridor right)) :=
  retained_noCycle_aux LengthOK avoids corridor left right.1 (by have := right.2; omega) lt
    (head_mem_cutBoundary outside corridor right)
    (footHead_mem_cutBoundary outside corridor right.1)

/-- **Every pair `left < right` of the corridor is target-defective**, through
`prefixContext`. -/
theorem prefix_targetDefect (LengthOK : ℕ → Prop)
    (accept : ∀ k, 2 ≤ k → LengthOK (2 ^ k))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (outside : ColdCorridor.IsOutsideComponent object windows component)
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (lt : left.1 < right.1) :
    Response.TargetDefect (HasCycleWithLength LengthOK)
      (SupportAtom.retainedPiece object (corridor.prefixSupport right.1)
        (corridor.prefixSupport left.1))
      (SupportAtom.piece object (corridor.prefixSupport right.1)) :=
  ⟨prefixContext outside corridor right, fun equivalent =>
    prefixContext_retained_noCycle LengthOK avoids outside corridor left right lt
      (equivalent.mpr (prefixContext_piece_cycle LengthOK accept outside corridor
        right (by omega)))⟩

end Corridor

/-- **Distinct states force a short first failure.**  If no two of the first
`first + 1` states agree, then `first < Q_cold`: they are distinct elements of
the `Q_cold`-element state type. -/
theorem first_lt_stateBound {object : FiniteObject.{v}}
    {windows component : Finset object.Vertex} {S : ColdCorridor.DeclaredSignature}
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


end Hypostructure.Graph.ColdEqualStates
