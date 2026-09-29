import Hypostructure.Graph.InternalVertexFold

/-!
# Cycles of a fold lift to accepted paths of the source

Identifying two internal vertices `keep`, `remove` of a boundaried piece
(`BoundaryPiece.identifyInternal`) and gluing into an outside context: an
accepted cycle of the folded gluing lifts to an accepted cycle of the source
gluing, or to an accepted-length path of the source gluing from `keep` to
`remove` (the cycle passes the merged vertex through one edge of each origin).
The generic lemma `cycle_lift` is stated for an injective vertex map that is a
homomorphism away from one vertex.
-/

namespace Hypostructure.Graph.FoldCycleLift

open SimpleGraph

variable {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG)

/-- lift a walk of `H` avoiding `m` along `φ`. -/
def liftWalk (φ : VH → VG) (m : VH)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y)) :
    ∀ {u v : VH} (p : H.Walk u v), (∀ x ∈ p.support, x ≠ m) → G.Walk (φ u) (φ v)
  | _, _, .nil, _ => .nil
  | _, _, .cons h p, hs =>
      .cons (hadj _ _ (hs _ (by simp)) (hs _ (by simp [Walk.start_mem_support])) h)
        (liftWalk φ m hadj p (fun x hx => hs x (by simp [hx])))


theorem length_liftWalk (φ : VH → VG) (m : VH)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    {u v : VH} (p : H.Walk u v) (hs : ∀ x ∈ p.support, x ≠ m) :
    (liftWalk H G φ m hadj p hs).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftWalk, ih]

theorem support_liftWalk (φ : VH → VG) (m : VH)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    {u v : VH} (p : H.Walk u v) (hs : ∀ x ∈ p.support, x ≠ m) :
    (liftWalk H G φ m hadj p hs).support = p.support.map φ := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftWalk, ih]

theorem isPath_liftWalk (φ : VH → VG) (hinj : Function.Injective φ) (m : VH)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    {u v : VH} (p : H.Walk u v) (hs : ∀ x ∈ p.support, x ≠ m) (hp : p.IsPath) :
    (liftWalk H G φ m hadj p hs).IsPath := by
  rw [Walk.isPath_def, support_liftWalk]
  exact hp.support_nodup.map hinj

theorem edges_liftWalk (φ : VH → VG) (m : VH)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    {u v : VH} (p : H.Walk u v) (hs : ∀ x ∈ p.support, x ≠ m) :
    (liftWalk H G φ m hadj p hs).edges = p.edges.map (Sym2.map φ) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftWalk, ih]


theorem cycle_avoid (φ : VH → VG) (hinj : Function.Injective φ) (m : VH)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    {v : VH} (c : H.Walk v v) (hc : c.IsCycle) (hs : ∀ x ∈ c.support, x ≠ m) :
    ∃ (v' : VG) (c' : G.Walk v' v'), c'.IsCycle ∧ c'.length = c.length := by
  cases c with
  | nil => exact absurd hc (by simp)
  | cons h p =>
    rw [Walk.cons_isCycle_iff] at hc
    have hs' : ∀ x ∈ p.support, x ≠ m := fun x hx => hs x (by simp [hx])
    refine ⟨_, Walk.cons (hadj _ _ (hs _ (by simp)) (hs _ (by simp [Walk.start_mem_support])) h)
      (liftWalk H G φ m hadj p hs'), ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨isPath_liftWalk H G φ hinj m hadj p hs' hc.1, ?_⟩
      rw [edges_liftWalk]
      intro hmem
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
      have : e = s(_, _) := Sym2.map.injective hinj (by simpa using heq)
      exact hc.2 (this ▸ he)
    · simp [length_liftWalk]


theorem cycle_at (φ : VH → VG) (hinj : Function.Injective φ) (m : VH) (a b : VG)
    (hφm : φ m = a) (hb : ∀ x, φ x ≠ b)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    (hm : ∀ x, x ≠ m → H.Adj m x → G.Adj a (φ x) ∨ G.Adj b (φ x))
    (c : H.Walk m m) (hc : c.IsCycle) :
    (∃ (v' : VG) (c' : G.Walk v' v'), c'.IsCycle ∧ c'.length = c.length) ∨
      (∃ q : G.Walk a b, q.IsPath ∧ q.length = c.length) := by
  cases c with
  | nil => exact absurd hc (by simp)
  | @cons _ x1 _ h1 p =>
    have hcyc := (Walk.cons_isCycle_iff _ _).mp hc
    have hp : p.IsPath := hcyc.1
    have hne1 : x1 ≠ m := h1.ne.symm
    obtain ⟨xk, h2, q, hq⟩ : ∃ (xk : VH) (h2 : H.Adj m xk) (q : H.Walk xk x1),
        p.reverse = Walk.cons h2 q := by
      cases hr : p.reverse with
      | nil => exact absurd rfl hne1
      | cons h2 q => exact ⟨_, h2, q, rfl⟩
    have hrp : p.reverse.IsPath := hp.reverse
    rw [hq] at hrp
    have hqp : q.IsPath := hrp.of_cons
    have hmq : m ∉ q.support := by
      have := hrp.support_nodup
      simp at this
      exact this.1
    have hnek : xk ≠ m := h2.ne.symm
    have hlen : (Walk.cons h1 p).length = q.length + 2 := by
      have : p.reverse.length = p.length := Walk.length_reverse p
      rw [hq] at this
      simp at this ⊢
      omega
    have hqs : ∀ x ∈ q.reverse.support, x ≠ m := by
      intro x hx hxm
      rw [Walk.support_reverse, List.mem_reverse] at hx
      exact hmq (hxm ▸ hx)
    have hqrp : q.reverse.IsPath := hqp.reverse
    set L := liftWalk H G φ m hadj q.reverse hqs with hL
    have hLp : L.IsPath := isPath_liftWalk H G φ hinj m hadj _ hqs hqrp
    have hLlen : L.length = q.length := by
      rw [hL, length_liftWalk]; simp
    have hLsupp : L.support = q.reverse.support.map φ := support_liftWalk H G φ m hadj _ hqs
    have hnotA : a ∉ L.support := by
      rw [hLsupp]
      intro hmem
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hmem
      have : y = m := hinj (hyeq.trans hφm.symm)
      exact hqs y hy this
    have hnotB : b ∉ L.support := by
      rw [hLsupp]
      intro hmem
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hmem
      exact hb y hyeq
    have hne : x1 ≠ xk := by
      intro heq
      subst heq
      have hnil : q = Walk.nil := Walk.eq_nil_iff_nil.mpr (Walk.isPath_iff_nil.mp hqp)
      subst hnil
      have hedges : p.edges.reverse = [s(m, x1)] := by
        rw [← Walk.edges_reverse, hq]; simp
      apply hcyc.2
      have : s(m, x1) ∈ p.edges.reverse := by rw [hedges]; simp
      exact List.mem_reverse.mp this
    have hanb : a ≠ b := fun e => hb m (hφm.trans e)
    have hxa : ∀ x, x ≠ m → a ≠ φ x := fun x hx e => hx (hinj (e.symm.trans hφm.symm))
    have hxaL : ∀ y ∈ L.support, a ≠ y := fun y hy e => hnotA (e ▸ hy)
    have hlen' := hlen
    -- the A-end and B-end paths
    have pathA : ∀ (A1 : G.Adj a (φ x1)), (Walk.cons A1 L).IsPath ∧
        (Walk.cons A1 L).length = q.length + 1 := by
      intro A1
      exact ⟨by rw [Walk.cons_isPath_iff]; exact ⟨hLp, hnotA⟩, by simp [hLlen]⟩
    have pathB : ∀ (B1 : G.Adj b (φ x1)), (Walk.cons B1 L).IsPath ∧
        (Walk.cons B1 L).length = q.length + 1 := by
      intro B1
      exact ⟨by rw [Walk.cons_isPath_iff]; exact ⟨hLp, hnotB⟩, by simp [hLlen]⟩
    rcases hm x1 hne1 h1 with A1 | B1 <;> rcases hm xk hnek h2 with Ak | Bk
    · -- (a, a): a cycle through a
      left
      obtain ⟨hpA, hlA⟩ := pathA A1
      refine ⟨_, Walk.cons Ak.symm (Walk.cons A1 L), ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]
        refine ⟨hpA, ?_⟩
        intro hmem
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with h | h
        · rcases Sym2.eq_iff.mp h with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact hxa xk hnek e1.symm
          · exact hne (hinj e1).symm
        · have := Walk.snd_mem_support_of_mem_edges L h
          exact hnotA this
      · simp [hlA, hlen, hLlen]
    · -- (a, b)
      right
      obtain ⟨hpA, hlA⟩ := pathA A1
      have hT : (Walk.cons Bk (Walk.cons A1 L).reverse).IsPath := by
        rw [Walk.cons_isPath_iff]
        refine ⟨hpA.reverse, ?_⟩
        rw [Walk.support_reverse, List.mem_reverse]
        simp only [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hanb.symm, hnotB⟩
      refine ⟨(Walk.cons Bk (Walk.cons A1 L).reverse).reverse, hT.reverse, ?_⟩
      simp [hlA, hlen, hLlen]
    · -- (b, a)
      right
      obtain ⟨hpB, hlB⟩ := pathB B1
      have hT : (Walk.cons Ak (Walk.cons B1 L).reverse).IsPath := by
        rw [Walk.cons_isPath_iff]
        refine ⟨hpB.reverse, ?_⟩
        rw [Walk.support_reverse, List.mem_reverse]
        simp only [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hanb, hnotA⟩
      refine ⟨Walk.cons Ak (Walk.cons B1 L).reverse, hT, ?_⟩
      simp [hlB, hlen, hLlen]
    · -- (b, b)
      left
      obtain ⟨hpB, hlB⟩ := pathB B1
      refine ⟨_, Walk.cons Bk.symm (Walk.cons B1 L), ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]
        refine ⟨hpB, ?_⟩
        intro hmem
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with h | h
        · rcases Sym2.eq_iff.mp h with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact hb xk e1
          · exact hne (hinj e1).symm
        · have := Walk.snd_mem_support_of_mem_edges L h
          exact hnotB this
      · simp [hlB, hlen, hLlen]


theorem cycle_lift (φ : VH → VG) (hinj : Function.Injective φ) (m : VH) (a b : VG)
    (hφm : φ m = a) (hb : ∀ x, φ x ≠ b)
    (hadj : ∀ x y, x ≠ m → y ≠ m → H.Adj x y → G.Adj (φ x) (φ y))
    (hm : ∀ x, x ≠ m → H.Adj m x → G.Adj a (φ x) ∨ G.Adj b (φ x))
    {v : VH} (c : H.Walk v v) (hc : c.IsCycle) :
    (∃ (v' : VG) (c' : G.Walk v' v'), c'.IsCycle ∧ c'.length = c.length) ∨
      (∃ q : G.Walk a b, q.IsPath ∧ q.length = c.length) := by
  classical
  by_cases hmem : m ∈ c.support
  · have hrot := hc.rotate hmem
    have hlen : (c.rotate m hmem).length = c.length := Walk.length_rotate c m hmem
    rcases cycle_at H G φ hinj m a b hφm hb hadj hm (c.rotate m hmem) hrot with ⟨v', c', h1, h2⟩ | ⟨q, h1, h2⟩
    · exact Or.inl ⟨v', c', h1, h2.trans hlen⟩
    · exact Or.inr ⟨q, h1, h2.trans hlen⟩
  · exact Or.inl (cycle_avoid H G φ hinj m hadj c hc (fun x hx e => hmem (e ▸ hx)))


section Crossing

variable {V : Type*} (Γ : SimpleGraph V)

/-- **A path with both ends in `S` that leaves `S` crosses its boundary twice**:
two distinct edges of the path, each with exactly one endpoint in `S`. -/
theorem two_crossing (S : Set V) {u v : V} (p : Γ.Walk u v) (hp : p.IsPath)
    (hu : u ∈ S) (hv : v ∈ S) {w : V} (hw : w ∈ p.support) (hwS : w ∉ S) :
    ∃ e1 ∈ p.edges, ∃ e2 ∈ p.edges, e1 ≠ e2 ∧
      (∃ x ∈ e1, ∃ y ∈ e1, x ∈ S ∧ y ∉ S) ∧
      (∃ x ∈ e2, ∃ y ∈ e2, x ∈ S ∧ y ∉ S) := by
  classical
  obtain ⟨d1, hd1, hd1a, hd1b⟩ :=
    (p.takeUntil w hw).exists_boundary_dart S hu hwS
  obtain ⟨d2, hd2, hd2a, hd2b⟩ :=
    (p.dropUntil w hw).reverse.exists_boundary_dart S hv hwS
  have hsplit : p.edges = (p.takeUntil w hw).edges ++ (p.dropUntil w hw).edges := by
    have := congrArg Walk.edges (p.take_spec hw)
    rw [Walk.edges_append] at this
    exact this.symm
  have hnodup := hp.isTrail.edges_nodup
  rw [hsplit] at hnodup
  have e1mem : d1.edge ∈ (p.takeUntil w hw).edges :=
    List.mem_map.mpr ⟨d1, hd1, rfl⟩
  have e2mem : d2.edge ∈ (p.dropUntil w hw).edges := by
    have : d2.edge ∈ (p.dropUntil w hw).reverse.edges := List.mem_map.mpr ⟨d2, hd2, rfl⟩
    rwa [Walk.edges_reverse, List.mem_reverse] at this
  refine ⟨d1.edge, ?_, d2.edge, ?_, ?_, ?_, ?_⟩
  · rw [hsplit]; exact List.mem_append_left _ e1mem
  · rw [hsplit]; exact List.mem_append_right _ e2mem
  · intro heq
    have := List.nodup_append.mp hnodup
    exact this.2.2 _ e1mem _ e2mem heq
  · exact ⟨d1.fst, by simp [Dart.edge], d1.snd, by simp [Dart.edge], hd1a, hd1b⟩
  · exact ⟨d2.fst, by simp [Dart.edge], d2.snd, by simp [Dart.edge], hd2a, hd2b⟩

end Crossing

section Application

open Hypostructure.Graph

universe w

variable {boundary : Boundary.{w}} (piece : BoundaryPiece boundary)
  (keep remove : piece.Internal) (different : keep ≠ remove)
  (outside : OutsideContext boundary)

/-- Decode a vertex of the folded gluing into the source gluing. -/
def foldGlueDecode :
    GluedVertex (piece.identifyInternal keep remove different) outside →
      GluedVertex piece outside
  | .inl label => .inl label
  | .inr (.inl x) => .inr (.inl x.1)
  | .inr (.inr o) => .inr (.inr o)

theorem foldGlueDecode_injective :
    Function.Injective (foldGlueDecode piece keep remove different outside) := by
  intro x y h
  rcases x with l | x | o <;> rcases y with l' | y | o' <;>
    simp [foldGlueDecode] at h ⊢ <;> first | exact h | exact Subtype.ext h

/-- The merged vertex of the folded gluing. -/
def foldGlueMerged :
    GluedVertex (piece.identifyInternal keep remove different) outside :=
  .inr (.inl ⟨keep, different⟩)

theorem foldGlueDecode_adj
    (x y : GluedVertex (piece.identifyInternal keep remove different) outside)
    (hx : x ≠ foldGlueMerged piece keep remove different outside)
    (hy : y ≠ foldGlueMerged piece keep remove different outside)
    (h : (glueGraph (piece.identifyInternal keep remove different) outside).Adj x y) :
    (glueGraph piece outside).Adj
      (foldGlueDecode piece keep remove different outside x)
      (foldGlueDecode piece keep remove different outside y) := by
  rw [glueGraph_adj_iff] at h ⊢
  rcases h with ⟨pl, pr, hadj, rfl, rfl⟩ | ⟨cl, cr, hadj, rfl, rfl⟩
  · rw [BoundaryPiece.identifyInternal_adj] at hadj
    obtain ⟨ne, old | ⟨mv, _⟩ | ⟨mv, _⟩⟩ := hadj
    · refine Or.inl ⟨piece.foldDecode remove pl, piece.foldDecode remove pr, old, ?_, ?_⟩
      · cases pl <;> rfl
      · cases pr <;> rfl
    · exfalso
      apply hx
      cases pl with
      | inl _ => simp [BoundaryPiece.foldDecode] at mv
      | inr z =>
        have : z = ⟨keep, different⟩ := Subtype.ext (Sum.inr.inj mv)
        subst this; rfl
    · exfalso
      apply hy
      cases pr with
      | inl _ => simp [BoundaryPiece.foldDecode] at mv
      | inr z =>
        have : z = ⟨keep, different⟩ := Subtype.ext (Sum.inr.inj mv)
        subst this; rfl
  · exact Or.inr ⟨cl, cr, hadj, by cases cl <;> rfl, by cases cr <;> rfl⟩

theorem foldGlueDecode_merged_adj
    (x : GluedVertex (piece.identifyInternal keep remove different) outside)
    (hx : x ≠ foldGlueMerged piece keep remove different outside)
    (h : (glueGraph (piece.identifyInternal keep remove different) outside).Adj
      (foldGlueMerged piece keep remove different outside) x) :
    (glueGraph piece outside).Adj (.inr (.inl keep))
        (foldGlueDecode piece keep remove different outside x) ∨
      (glueGraph piece outside).Adj (.inr (.inl remove))
        (foldGlueDecode piece keep remove different outside x) := by
  rw [glueGraph_adj_iff] at h
  rcases h with ⟨pl, pr, hadj, hl, hr⟩ | ⟨cl, cr, hadj, hl, hr⟩
  · have hpl : pl = .inr ⟨keep, different⟩ := by
      cases pl with
      | inl _ => simp [pieceEmbedding, foldGlueMerged] at hl
      | inr z =>
        have : z = ⟨keep, different⟩ := by
          simpa [pieceEmbedding, foldGlueMerged] using hl
        rw [this]
    subst hpl
    subst hr
    rw [BoundaryPiece.identifyInternal_adj] at hadj
    obtain ⟨ne, old | ⟨mv, moved⟩ | ⟨mv, moved⟩⟩ := hadj
    · left
      rw [glueGraph_adj_iff]
      exact Or.inl ⟨.inr keep, piece.foldDecode remove pr, old, rfl, by cases pr <;> rfl⟩
    · right
      rw [glueGraph_adj_iff]
      exact Or.inl ⟨.inr remove, piece.foldDecode remove pr, moved, rfl, by cases pr <;> rfl⟩
    · exfalso
      apply hx
      cases pr with
      | inl _ => simp [BoundaryPiece.foldDecode] at mv
      | inr z =>
        have : z = ⟨keep, different⟩ := Subtype.ext (Sum.inr.inj mv)
        subst this; rfl
  · exfalso
    cases cl <;> simp [contextEmbedding, foldGlueMerged] at hl

/-- **A cycle of the folded gluing lifts to an accepted path of the source
gluing.**  If the source gluing carries no accepted cycle and the folded gluing
carries one, the source gluing has an accepted-length path from `keep` to
`remove`. -/
theorem foldGlue_path_of_cycle (LengthOK : Nat → Prop)
    (avoids : ¬ HasCycleWithLength LengthOK (glue piece outside))
    (cycle : HasCycleWithLength LengthOK
      (glue (piece.identifyInternal keep remove different) outside)) :
    ∃ p : (glue piece outside).graph.Walk (.inr (.inl keep)) (.inr (.inl remove)),
      p.IsPath ∧ LengthOK p.length := by
  obtain ⟨certificate⟩ := cycle
  have removeNe : ∀ x, foldGlueDecode piece keep remove different outside x ≠
      (.inr (.inl remove) : GluedVertex piece outside) := by
    intro x
    rcases x with l | x | o
    · simp [foldGlueDecode]
    · simp only [foldGlueDecode, ne_eq, Sum.inr.injEq, Sum.inl.injEq]
      exact x.2
    · simp [foldGlueDecode]
  rcases cycle_lift (glue (piece.identifyInternal keep remove different) outside).graph
      (glue piece outside).graph
      (foldGlueDecode piece keep remove different outside)
      (foldGlueDecode_injective piece keep remove different outside)
      (foldGlueMerged piece keep remove different outside)
      (.inr (.inl keep)) (.inr (.inl remove)) rfl removeNe
      (fun x y hx hy h => foldGlueDecode_adj piece keep remove different outside x y hx hy h)
      (fun x hx h => foldGlueDecode_merged_adj piece keep remove different outside x hx h)
      certificate.walk certificate.isCycle with
    ⟨v', c', hc', hlen⟩ | ⟨q, hq, hlen⟩
  · exact absurd ⟨⟨v', c', hc', hlen ▸ certificate.length_ok⟩⟩ avoids
  · exact ⟨q, hq, hlen ▸ certificate.length_ok⟩

end Application

end Hypostructure.Graph.FoldCycleLift