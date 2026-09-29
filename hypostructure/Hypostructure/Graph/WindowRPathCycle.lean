import Hypostructure.Graph.LocalRigidity

/-!
# The cross cycle through two placed paths joined by two vertex-disjoint outside paths

Generalises `LocalRigidity.cross_cycle`: the two joining edges `p i – q j`, `p i' – q j'`
become two vertex-disjoint paths `r₁ : a₁ ⇝ b₁`, `r₂ : a₂ ⇝ b₂` whose vertices lie in a set
`S` disjoint from both placed paths (for a window packing: `S` the remainder), with
`p i – a₁`, `b₁ – q j`, `p i' – a₂`, `b₂ – q j'` edges.  The closed walk

  `q j → b₁ ⇝ a₁ → p i ⇝ p i' → a₂ ⇝ b₂ → q j' ⇝ q j`

is a cycle of length `dist(i,i') + dist(j,j') + |r₁| + |r₂| + 4`.
-/

namespace Hypostructure.Graph.LocalRigidity

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem cross_cycle_paths {m n : ℕ} {p : Fin m → V} {q : Fin n → V}
    (hp : IsPlacedPath G p) (hq : IsPlacedPath G q) (disj : ∀ a b, p a ≠ q b)
    {S : Set V} (hSp : ∀ a, p a ∉ S) (hSq : ∀ b, q b ∉ S)
    {i i' : Fin m} {j j' : Fin n} {a₁ b₁ a₂ b₂ : V}
    (r₁ : G.Walk a₁ b₁) (r₂ : G.Walk a₂ b₂) (r₁p : r₁.IsPath) (r₂p : r₂.IsPath)
    (r₁S : ∀ v ∈ r₁.support, v ∈ S) (r₂S : ∀ v ∈ r₂.support, v ∈ S)
    (r₁₂ : ∀ v ∈ r₁.support, v ∉ r₂.support)
    (e₁ : G.Adj (p i) a₁) (e₁' : G.Adj b₁ (q j))
    (e₂ : G.Adj (p i') a₂) (e₂' : G.Adj b₂ (q j')) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = Nat.dist i.1 i'.1 + Nat.dist j.1 j'.1 + r₁.length + r₂.length + 4 := by
  obtain ⟨wP, wPp, wPl, wPs⟩ := exists_segment hp i i'
  obtain ⟨wQ, wQp, wQl, wQs⟩ := exists_segment hq j' j
  let Wm : G.Walk (p i') (q j) := Walk.cons e₂ (r₂.append (Walk.cons e₂' wQ))
  let W : G.Walk (p i) (q j) := wP.append Wm
  let tail : G.Walk b₁ (q j) := r₁.reverse.append (Walk.cons e₁.symm W)
  have Wsupport : W.support = wP.support ++ (r₂.support ++ wQ.support) := by
    simp [W, Wm, Walk.support_append, Walk.support_cons]
  have tailSupport : tail.support = r₁.support.reverse ++ W.support := by
    simp [tail, Walk.support_append, Walk.support_cons, Walk.support_reverse]
  have tailPath : tail.IsPath := by
    rw [Walk.isPath_def, tailSupport, Wsupport, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.nodup_reverse.mpr r₁p.support_nodup
    · rw [List.nodup_append]
      refine ⟨wPp.support_nodup, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨r₂p.support_nodup, wQp.support_nodup, ?_⟩
        intro a ha b hb eab
        subst eab
        obtain ⟨y, hy⟩ := wQs a hb
        exact hSq y (hy ▸ r₂S a ha)
      · intro a ha b hb eab
        subst eab
        obtain ⟨x, hx⟩ := wPs a ha
        rcases List.mem_append.mp hb with hb | hb
        · exact hSp x (hx ▸ r₂S a hb)
        · obtain ⟨y, hy⟩ := wQs a hb
          exact disj x y (hx.trans hy.symm)
    · intro a ha b hb eab
      subst eab
      have ha' : a ∈ r₁.support := List.mem_reverse.mp ha
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨x, hx⟩ := wPs a hb
        exact hSp x (hx ▸ r₁S a ha')
      · rcases List.mem_append.mp hb with hb | hb
        · exact r₁₂ a ha' hb
        · obtain ⟨y, hy⟩ := wQs a hb
          exact hSq y (hy ▸ r₁S a ha')
  refine ⟨q j, Walk.cons e₁'.symm tail, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨tailPath, ?_⟩
    intro mem
    have edgesEq : tail.edges = r₁.reverse.edges ++ (s(a₁, p i) :: (wP.edges ++
        (s(p i', a₂) :: (r₂.edges ++ (s(b₂, q j') :: wQ.edges))))) := by
      simp [tail, W, Wm, Walk.edges_append, Walk.edges_cons, Walk.edges_reverse]
    rw [edgesEq] at mem
    have qjS : ∀ v ∈ ({q j} : Set V), v ∉ S := by
      intro v hv; rw [Set.mem_singleton_iff] at hv; subst hv; exact hSq j
    simp only [List.mem_append, List.mem_cons] at mem
    rcases mem with mem | mem | mem | mem | mem | mem | mem
    · -- an edge of `r₁.reverse` at `q j`
      have : q j ∈ r₁.reverse.support :=
        Walk.fst_mem_support_of_mem_edges _ mem
      rw [Walk.support_reverse, List.mem_reverse] at this
      exact hSq j (r₁S _ this)
    · rcases Sym2.eq_iff.mp mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hSq j (h1 ▸ r₁S a₁ (Walk.start_mem_support r₁))
      · exact disj i j h1.symm
    · obtain ⟨x, hx⟩ := wPs _ (Walk.fst_mem_support_of_mem_edges _ mem)
      exact disj x j hx
    · rcases Sym2.eq_iff.mp mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact disj i' j h1.symm
      · exact hSq j (h1 ▸ r₂S a₂ (Walk.start_mem_support r₂))
    · have : q j ∈ r₂.support := Walk.fst_mem_support_of_mem_edges _ mem
      exact hSq j (r₂S _ this)
    · rcases Sym2.eq_iff.mp mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hSq j (h1 ▸ r₂S b₂ (Walk.end_mem_support r₂))
      · exact r₁₂ b₁ (Walk.end_mem_support r₁) (h2 ▸ Walk.end_mem_support r₂)
    · obtain ⟨y, hy⟩ := wQs _ (Walk.snd_mem_support_of_mem_edges _ mem)
      exact hSq y (hy ▸ r₁S b₁ (Walk.end_mem_support r₁))
  · simp only [tail, W, Wm, Walk.length_cons, Walk.length_append, Walk.length_reverse, wPl, wQl]
    rw [Nat.dist_comm j'.1 j.1]
    omega

end Hypostructure.Graph.LocalRigidity

namespace Hypostructure.Graph.LocalRigidity

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Self cycle through one placed path and one outside path.**  A placed path `p` and a
path `r : a ⇝ b` inside a set `S` disjoint from `p`, with edges `p i – a`, `b – p i'` and
`i ≠ i' ∨ a ≠ b`, close a cycle of length `dist(i,i') + |r| + 2`. -/
theorem self_cycle_path {m : ℕ} {p : Fin m → V} (hp : IsPlacedPath G p)
    {S : Set V} (hSp : ∀ a, p a ∉ S) {i i' : Fin m} {a b : V}
    (r : G.Walk a b) (rp : r.IsPath) (rS : ∀ v ∈ r.support, v ∈ S)
    (e₁ : G.Adj (p i) a) (e₂ : G.Adj b (p i')) (ne : i ≠ i' ∨ a ≠ b) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = Nat.dist i.1 i'.1 + r.length + 2 := by
  obtain ⟨wP, wPp, wPl, wPs⟩ := exists_segment hp i i'
  let tail : G.Walk b (p i') := r.reverse.append (Walk.cons e₁.symm wP)
  have tailSupport : tail.support = r.support.reverse ++ wP.support := by
    simp [tail, Walk.support_append, Walk.support_cons, Walk.support_reverse]
  have tailPath : tail.IsPath := by
    rw [Walk.isPath_def, tailSupport, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr rp.support_nodup, wPp.support_nodup, ?_⟩
    intro x hx y hy exy
    subst exy
    obtain ⟨z, hz⟩ := wPs x hy
    exact hSp z (hz ▸ rS x (List.mem_reverse.mp hx))
  refine ⟨p i', Walk.cons e₂.symm tail, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨tailPath, ?_⟩
    intro mem
    have edgesEq : tail.edges = r.reverse.edges ++ (s(a, p i) :: wP.edges) := by
      simp [tail, Walk.edges_append, Walk.edges_cons, Walk.edges_reverse]
    rw [edgesEq] at mem
    simp only [List.mem_append, List.mem_cons] at mem
    rcases mem with mem | mem | mem
    · have : p i' ∈ r.reverse.support := Walk.fst_mem_support_of_mem_edges _ mem
      rw [Walk.support_reverse, List.mem_reverse] at this
      exact hSp i' (rS _ this)
    · rcases Sym2.eq_iff.mp mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hSp i' (h1 ▸ rS a (Walk.start_mem_support r))
      · have ii : i' = i := hp.1 h1
        rcases ne with n1 | n2
        · exact n1 ii.symm
        · exact n2 h2.symm
    · obtain ⟨z, hz⟩ := wPs _ (Walk.snd_mem_support_of_mem_edges _ mem)
      exact hSp z (hz ▸ rS b (Walk.end_mem_support r))
  · simp only [tail, Walk.length_cons, Walk.length_append, Walk.length_reverse, wPl]
    omega

end Hypostructure.Graph.LocalRigidity
