import Hypostructure.Graph.CycleCounting.Object
import Hypostructure.Graph.WindowCurvatureAlgebra
import Hypostructure.Graph.WindowStubStructure

/-!
# Local rigidity around a vertex and across placed paths

Configurations a graph with no cycle of length `2^k` (`k ≥ 2`) cannot contain,
each read from an explicit cycle it would close:

* **the length-3 fan** (`three_fan`): two paths of length `3` of `G − h` from a
  neighbour `a` of `h` to distinct neighbours `b ≠ c` of `h` leave `a` through
  the same vertex and meet nowhere else.  A coincidence other than the first
  step closes a quadrilateral through `h`; distinct first steps close the
  8-cycle `h b ⋯ a ⋯ c h`;
* **the chain `3, 3, 3`** (`three_chain`): the fan at the two inner vertices of
  a chain `a → b → c → d` of such paths;
* **the cross-edge gap** (`cross_cycle`): two vertex-disjoint placed paths
  joined at positions `(i, j)` and `(i', j')` close a cycle of length
  `|i − i'| + |j − j'| + 2`; with one path a single vertex this is the
  attachment rule, with an edge it is `C₁` safety, and at gap `(1, 1)` it is the
  ladder quadrilateral;
* **window positions**: a window of a packing has a placement, and a placed
  vertex carries `d − 2` external neighbours at an interior position and
  `d − 1` at an end.

Everything is stated for any graph, any `FiniteObject` and any window packing;
nothing here names an application.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Hypostructure.Graph.LocalRigidity

open SimpleGraph

section Simple

variable {V : Type*} {G : SimpleGraph V}

/-- A placed path: injective positions, consecutive positions adjacent. -/
def IsPlacedPath (G : SimpleGraph V) {m : ℕ} (p : Fin m → V) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin m, i.1 + 1 = j.1 → G.Adj (p i) (p j)

/-- The forward segment of a placed path. -/
theorem exists_forward_segment {m : ℕ} {p : Fin m → V} (hp : IsPlacedPath G p) :
    ∀ (k : ℕ) (i : Fin m) (hk : i.1 + k < m),
      ∃ w : G.Walk (p i) (p ⟨i.1 + k, hk⟩), w.IsPath ∧ w.length = k ∧
        ∀ v ∈ w.support, ∃ l : Fin m, i.1 ≤ l.1 ∧ p l = v
  | 0, i, hk => by
      refine ⟨(Walk.nil).copy rfl (congrArg p (Fin.ext (by simp))), ?_, ?_, ?_⟩
      · simp
      · simp
      · intro v hv
        simp at hv
        exact ⟨i, le_rfl, by rw [hv]⟩
  | k + 1, i, hk => by
      let i1 : Fin m := ⟨i.1 + 1, by omega⟩
      obtain ⟨w, wp, wl, ws⟩ := exists_forward_segment hp k i1 (by simp [i1]; omega)
      have adj : G.Adj (p i) (p i1) := hp.2 i i1 rfl
      have notIn : p i ∉ w.support := by
        intro m'
        obtain ⟨l, hl, e⟩ := ws _ m'
        have := hp.1 e
        subst this
        simp [i1] at hl
      let w' : G.Walk (p i) (p ⟨i.1 + (k + 1), hk⟩) :=
        (Walk.cons adj w).copy rfl (congrArg p (Fin.ext (by simp [i1]; omega)))
      refine ⟨w', ?_, ?_, ?_⟩
      · simp only [w', Walk.isPath_copy]
        exact wp.cons notIn
      · simp [w', wl]
      · intro v hv
        simp only [w', Walk.support_copy, Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ⟨i, le_rfl, rfl⟩
        · obtain ⟨l, hl, e⟩ := ws v hv
          exact ⟨l, by simp [i1] at hl; omega, e⟩

/-- Any two positions of a placed path are joined by a path of length their
distance, inside the placed path. -/
theorem exists_segment {m : ℕ} {p : Fin m → V} (hp : IsPlacedPath G p) (i j : Fin m) :
    ∃ w : G.Walk (p i) (p j), w.IsPath ∧ w.length = Nat.dist i.1 j.1 ∧
      ∀ v ∈ w.support, v ∈ Set.range p := by
  rcases le_total i.1 j.1 with h | h
  · obtain ⟨w, wp, wl, ws⟩ := exists_forward_segment hp (j.1 - i.1) i (by omega)
    have e : (⟨i.1 + (j.1 - i.1), by omega⟩ : Fin m) = j := Fin.ext (by simp; omega)
    refine ⟨w.copy rfl (congrArg p e), by simpa using wp, ?_, ?_⟩
    · simp [wl, Nat.dist]; omega
    · intro v hv
      simp only [Walk.support_copy] at hv
      obtain ⟨l, -, e⟩ := ws v hv
      exact ⟨l, e⟩
  · obtain ⟨w, wp, wl, ws⟩ := exists_forward_segment hp (i.1 - j.1) j (by omega)
    have e : (⟨j.1 + (i.1 - j.1), by omega⟩ : Fin m) = i := Fin.ext (by simp; omega)
    refine ⟨(w.copy rfl (congrArg p e)).reverse, by simpa using wp.reverse, ?_, ?_⟩
    · simp [wl, Nat.dist]; omega
    · intro v hv
      simp only [Walk.support_reverse, List.mem_reverse, Walk.support_copy] at hv
      obtain ⟨l, -, e⟩ := ws v hv
      exact ⟨l, e⟩

/-- **Cross cycle.** Two vertex-disjoint placed paths joined by two distinct
edges `p i – q j`, `p i' – q j'` close a cycle of length
`dist(i, i') + dist(j, j') + 2`. -/
theorem cross_cycle {m n : ℕ} {p : Fin m → V} {q : Fin n → V}
    (hp : IsPlacedPath G p) (hq : IsPlacedPath G q) (disj : ∀ a b, p a ≠ q b)
    {i i' : Fin m} {j j' : Fin n} (e1 : G.Adj (p i) (q j)) (e2 : G.Adj (p i') (q j'))
    (ne : i ≠ i' ∨ j ≠ j') :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = Nat.dist i.1 i'.1 + Nat.dist j.1 j'.1 + 2 := by
  obtain ⟨wP, wPp, wPl, wPs⟩ := exists_segment hp i i'
  obtain ⟨wQ, wQp, wQl, wQs⟩ := exists_segment hq j' j
  let W : G.Walk (p i) (q j) := wP.append (Walk.cons e2 wQ)
  have Wp : W.IsPath := by
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
      List.nodup_append]
    refine ⟨wPp.support_nodup, wQp.support_nodup, ?_⟩
    intro a ha b hb eab
    subst eab
    obtain ⟨x, hx⟩ := wPs a ha
    obtain ⟨y, hy⟩ := wQs a hb
    exact disj x y (hx.trans hy.symm)
  refine ⟨q j, Walk.cons e1.symm W, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨Wp, ?_⟩
    intro mem
    rw [Walk.edges_append, Walk.edges_cons, List.mem_append, List.mem_cons] at mem
    rcases mem with mem | mem | mem
    · obtain ⟨x, hx⟩ := wPs _ (Walk.fst_mem_support_of_mem_edges _ mem)
      exact disj x j hx
    · rcases Sym2.eq_iff.mp mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact disj i' j h1.symm
      · have jj : j = j' := hq.1 h1
        have ii : i = i' := hp.1 h2
        rcases ne with n1 | n2
        · exact n1 ii
        · exact n2 jj
    · obtain ⟨y, hy⟩ := wQs _ (Walk.snd_mem_support_of_mem_edges _ mem)
      exact disj i y hy.symm
  · simp only [W, Walk.length_cons, Walk.length_append, wPl, wQl]
    rw [Nat.dist_comm j'.1 j.1]
    omega

/-- **The length-3 fan at a vertex.** In a graph with no cycle of length `4`
or `8`: if `a, b, c` are neighbours of `h` with `b ≠ c`, and `a p₁ p₂ b`,
`a q₁ q₂ c` are paths of length `3` avoiding `h`, then the two paths leave `a`
through the same vertex (`p₁ = q₁`) and meet nowhere else
(`p₂ ≠ q₂`, `p₂ ≠ c`, `q₂ ≠ b`). -/
theorem three_fan
    (no4 : ∀ {v : V} (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    (no8 : ∀ {v : V} (c : G.Walk v v), c.IsCycle → c.length ≠ 8)
    {h a b c p₁ p₂ q₁ q₂ : V}
    (ha : G.Adj h a) (hb : G.Adj h b) (hc : G.Adj h c) (bc : b ≠ c)
    (ap : G.Adj a p₁) (pp : G.Adj p₁ p₂) (pb : G.Adj p₂ b)
    (ap₂ : a ≠ p₂) (ab : a ≠ b) (p₁b : p₁ ≠ b)
    (aq : G.Adj a q₁) (qq : G.Adj q₁ q₂) (qc : G.Adj q₂ c)
    (aq₂ : a ≠ q₂) (ac : a ≠ c) (q₁c : q₁ ≠ c)
    (hp₁ : h ≠ p₁) (hp₂ : h ≠ p₂) (hq₁ : h ≠ q₁) (hq₂ : h ≠ q₂) :
    p₁ = q₁ ∧ p₂ ≠ q₂ ∧ p₂ ≠ c ∧ q₂ ≠ b := by
  -- quadrilateral helper
  have quad : ∀ {w x y z : V}, G.Adj w x → G.Adj x y → G.Adj y z → G.Adj z w →
      w ≠ y → x ≠ z → False := by
    intro w x y z wx xy yz zw wy xz
    have cyc : (Walk.cons wx (Walk.cons xy (Walk.cons yz (Walk.cons zw Walk.nil)))).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · rw [Walk.isPath_def]
        simp [wx.ne', xy.ne, yz.ne, zw.ne, wy.symm, xz]
      · simp [wx.ne, wx.ne', xy.ne, zw.ne', wy, xz]
    exact no4 _ cyc rfl
  have hb' : h ≠ b := hb.ne
  have hc' : h ≠ c := hc.ne
  have ha' : h ≠ a := ha.ne
  -- the coincidences other than `p₁ = q₁` are quadrilaterals through `h`
  have p₂q₂ : p₂ ≠ q₂ := by
    rintro rfl
    exact quad hb pb.symm qc hc.symm hp₂ bc
  have p₂c : p₂ ≠ c := by
    rintro rfl
    exact quad ha ap pp hc.symm hp₁ ac
  have q₂b : q₂ ≠ b := by
    rintro rfl
    exact quad ha aq qq hb.symm hq₁ ab
  refine ⟨?_, p₂q₂, p₂c, q₂b⟩
  by_contra p₁q₁
  have p₁q₂ : p₁ ≠ q₂ := by
    rintro rfl
    exact quad ha ap qc hc.symm hp₁ ac
  have p₂q₁ : p₂ ≠ q₁ := by
    rintro rfl
    exact quad ha aq pb hb.symm hq₁ ab
  have p₁c : p₁ ≠ c := by
    rintro rfl
    exact quad aq qq qc ap.symm aq₂ q₁c
  have q₁b : q₁ ≠ b := by
    rintro rfl
    exact quad ap pp pb aq.symm ap₂ p₁b
  -- all eight vertices are distinct: `h b p₂ p₁ a q₁ q₂ c` is an 8-cycle
  have e1 : G.Adj h b := hb
  let C : G.Walk h h :=
    Walk.cons hb (Walk.cons pb.symm (Walk.cons pp.symm (Walk.cons ap.symm
      (Walk.cons aq (Walk.cons qq (Walk.cons qc (Walk.cons hc.symm Walk.nil)))))))
  have cyc : C.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    have supp : (Walk.cons pb.symm (Walk.cons pp.symm (Walk.cons ap.symm
      (Walk.cons aq (Walk.cons qq (Walk.cons qc (Walk.cons hc.symm Walk.nil))))))).support =
        [b, p₂, p₁, a, q₁, q₂, c, h] := rfl
    have edges : (Walk.cons pb.symm (Walk.cons pp.symm (Walk.cons ap.symm
        (Walk.cons aq (Walk.cons qq (Walk.cons qc (Walk.cons hc.symm Walk.nil))))))).edges =
          [s(b, p₂), s(p₂, p₁), s(p₁, a), s(a, q₁), s(q₁, q₂), s(q₂, c), s(c, h)] := rfl
    refine ⟨?_, ?_⟩
    · rw [Walk.isPath_def, supp]
      simp [(hb' : h ≠ b), (Ne.symm hb' : b ≠ h), (hp₂ : h ≠ p₂), (Ne.symm hp₂ : p₂ ≠ h), (hp₁ : h ≠ p₁), (Ne.symm hp₁ : p₁ ≠ h), (ha' : h ≠ a), (Ne.symm ha' : a ≠ h), (hq₁ : h ≠ q₁), (Ne.symm hq₁ : q₁ ≠ h), (hq₂ : h ≠ q₂), (Ne.symm hq₂ : q₂ ≠ h), (hc' : h ≠ c), (Ne.symm hc' : c ≠ h), (pb.ne.symm : b ≠ p₂), (Ne.symm pb.ne.symm : p₂ ≠ b), (p₁b.symm : b ≠ p₁), (Ne.symm p₁b.symm : p₁ ≠ b), (ab.symm : b ≠ a), (Ne.symm ab.symm : a ≠ b), (q₁b.symm : b ≠ q₁), (Ne.symm q₁b.symm : q₁ ≠ b), (q₂b.symm : b ≠ q₂), (Ne.symm q₂b.symm : q₂ ≠ b), (bc : b ≠ c), (Ne.symm bc : c ≠ b), (pp.ne.symm : p₂ ≠ p₁), (Ne.symm pp.ne.symm : p₁ ≠ p₂), (ap₂.symm : p₂ ≠ a), (Ne.symm ap₂.symm : a ≠ p₂), (p₂q₁ : p₂ ≠ q₁), (Ne.symm p₂q₁ : q₁ ≠ p₂), (p₂q₂ : p₂ ≠ q₂), (Ne.symm p₂q₂ : q₂ ≠ p₂), (p₂c : p₂ ≠ c), (Ne.symm p₂c : c ≠ p₂), (ap.ne.symm : p₁ ≠ a), (Ne.symm ap.ne.symm : a ≠ p₁), (p₁q₁ : p₁ ≠ q₁), (Ne.symm p₁q₁ : q₁ ≠ p₁), (p₁q₂ : p₁ ≠ q₂), (Ne.symm p₁q₂ : q₂ ≠ p₁), (p₁c : p₁ ≠ c), (Ne.symm p₁c : c ≠ p₁), (aq.ne : a ≠ q₁), (Ne.symm aq.ne : q₁ ≠ a), (aq₂ : a ≠ q₂), (Ne.symm aq₂ : q₂ ≠ a), (ac : a ≠ c), (Ne.symm ac : c ≠ a), (qq.ne : q₁ ≠ q₂), (Ne.symm qq.ne : q₂ ≠ q₁), (q₁c : q₁ ≠ c), (Ne.symm q₁c : c ≠ q₁), (qc.ne : q₂ ≠ c), (Ne.symm qc.ne : c ≠ q₂)]
    · rw [edges]
      simp [Sym2.eq_iff, (hb' : h ≠ b), (Ne.symm hb' : b ≠ h), (hp₂ : h ≠ p₂), (Ne.symm hp₂ : p₂ ≠ h), (hp₁ : h ≠ p₁), (Ne.symm hp₁ : p₁ ≠ h), (ha' : h ≠ a), (Ne.symm ha' : a ≠ h), (hq₁ : h ≠ q₁), (Ne.symm hq₁ : q₁ ≠ h), (hq₂ : h ≠ q₂), (Ne.symm hq₂ : q₂ ≠ h), (hc' : h ≠ c), (Ne.symm hc' : c ≠ h), (pb.ne.symm : b ≠ p₂), (Ne.symm pb.ne.symm : p₂ ≠ b), (p₁b.symm : b ≠ p₁), (Ne.symm p₁b.symm : p₁ ≠ b), (ab.symm : b ≠ a), (Ne.symm ab.symm : a ≠ b), (q₁b.symm : b ≠ q₁), (Ne.symm q₁b.symm : q₁ ≠ b), (q₂b.symm : b ≠ q₂), (Ne.symm q₂b.symm : q₂ ≠ b), (bc : b ≠ c), (Ne.symm bc : c ≠ b), (pp.ne.symm : p₂ ≠ p₁), (Ne.symm pp.ne.symm : p₁ ≠ p₂), (ap₂.symm : p₂ ≠ a), (Ne.symm ap₂.symm : a ≠ p₂), (p₂q₁ : p₂ ≠ q₁), (Ne.symm p₂q₁ : q₁ ≠ p₂), (p₂q₂ : p₂ ≠ q₂), (Ne.symm p₂q₂ : q₂ ≠ p₂), (p₂c : p₂ ≠ c), (Ne.symm p₂c : c ≠ p₂), (ap.ne.symm : p₁ ≠ a), (Ne.symm ap.ne.symm : a ≠ p₁), (p₁q₁ : p₁ ≠ q₁), (Ne.symm p₁q₁ : q₁ ≠ p₁), (p₁q₂ : p₁ ≠ q₂), (Ne.symm p₁q₂ : q₂ ≠ p₁), (p₁c : p₁ ≠ c), (Ne.symm p₁c : c ≠ p₁), (aq.ne : a ≠ q₁), (Ne.symm aq.ne : q₁ ≠ a), (aq₂ : a ≠ q₂), (Ne.symm aq₂ : q₂ ≠ a), (ac : a ≠ c), (Ne.symm ac : c ≠ a), (qq.ne : q₁ ≠ q₂), (Ne.symm qq.ne : q₂ ≠ q₁), (q₁c : q₁ ≠ c), (Ne.symm q₁c : c ≠ q₁), (qc.ne : q₂ ≠ c), (Ne.symm qc.ne : c ≠ q₂)]
  exact no8 _ cyc rfl


/-! ## Length-3 paths, the fan and the chain -/

/-- A path `x y z w` of length `3`: three edges and four distinct vertices. -/
def ThreePath (G : SimpleGraph V) (x y z w : V) : Prop :=
  G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ x ≠ z ∧ x ≠ w ∧ y ≠ w

theorem ThreePath.reverse {x y z w : V} (path : ThreePath G x y z w) :
    ThreePath G w z y x :=
  ⟨path.2.2.1.symm, path.2.1.symm, path.1.symm, path.2.2.2.2.2.symm,
    path.2.2.2.2.1.symm, path.2.2.2.1.symm⟩

/-- `three_fan` read on `ThreePath`s. -/
theorem three_fan_path
    (no4 : ∀ {v : V} (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    (no8 : ∀ {v : V} (c : G.Walk v v), c.IsCycle → c.length ≠ 8)
    {h a b c p₁ p₂ q₁ q₂ : V}
    (ha : G.Adj h a) (hb : G.Adj h b) (hc : G.Adj h c) (bc : b ≠ c)
    (P : ThreePath G a p₁ p₂ b) (Q : ThreePath G a q₁ q₂ c)
    (hp₁ : h ≠ p₁) (hp₂ : h ≠ p₂) (hq₁ : h ≠ q₁) (hq₂ : h ≠ q₂) :
    p₁ = q₁ ∧ p₂ ≠ q₂ ∧ p₂ ≠ c ∧ q₂ ≠ b :=
  three_fan no4 no8 ha hb hc bc P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2.1 P.2.2.2.2.2
    Q.1 Q.2.1 Q.2.2.1 Q.2.2.2.1 Q.2.2.2.2.1 Q.2.2.2.2.2 hp₁ hp₂ hq₁ hq₂

/-- **The chain `3, 3, 3`.**  With no cycle of length `4` or `8`: if
`a, b, c, d` are neighbours of `h` with `a ≠ c`, `b ≠ d`, and `a p₁ p₂ b`,
`b r₁ r₂ c`, `c q₁ q₂ d` are paths of length `3` avoiding `h`, then the middle
path is `b p₂ q₁ c`: it leaves `b` through `p₂` and enters `c` through `q₁`. -/
theorem three_chain
    (no4 : ∀ {v : V} (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    (no8 : ∀ {v : V} (c : G.Walk v v), c.IsCycle → c.length ≠ 8)
    {h a b c d p₁ p₂ r₁ r₂ q₁ q₂ : V}
    (ha : G.Adj h a) (hb : G.Adj h b) (hc : G.Adj h c) (hd : G.Adj h d)
    (ac : a ≠ c) (bd : b ≠ d)
    (P : ThreePath G a p₁ p₂ b) (R : ThreePath G b r₁ r₂ c) (Q : ThreePath G c q₁ q₂ d)
    (hp₁ : h ≠ p₁) (hp₂ : h ≠ p₂) (hr₁ : h ≠ r₁) (hr₂ : h ≠ r₂)
    (hq₁ : h ≠ q₁) (hq₂ : h ≠ q₂) :
    r₁ = p₂ ∧ r₂ = q₁ := by
  have atB := three_fan_path no4 no8 hb ha hc ac P.reverse R hp₂ hp₁ hr₁ hr₂
  have atC := three_fan_path no4 no8 hc hb hd bd R.reverse Q hr₂ hr₁ hq₁ hq₂
  exact ⟨atB.1.symm, atC.1⟩

end Simple

/-! ## The properties at a finite object -/

section Object

universe u

variable (object : FiniteObject.{u})

/-- **The length-3 fan.**  At every vertex `h`, two paths of length `3` of
`G − h` from a neighbour `a` of `h` to distinct neighbours `b ≠ c` of `h` leave
`a` through the same vertex and meet nowhere else.  In particular two such
paths with distinct first steps do not exist (they would close the 8-cycle
`h b ⋯ a ⋯ c h`). -/
def ThreeRouteFan : Prop :=
  ∀ ⦃h a b c p₁ p₂ q₁ q₂ : object.Vertex⦄,
    object.graph.Adj h a → object.graph.Adj h b → object.graph.Adj h c → b ≠ c →
    ThreePath object.graph a p₁ p₂ b → ThreePath object.graph a q₁ q₂ c →
    h ≠ p₁ → h ≠ p₂ → h ≠ q₁ → h ≠ q₂ →
    p₁ = q₁ ∧ p₂ ≠ q₂ ∧ p₂ ≠ c ∧ q₂ ≠ b

/-- **The chain `3, 3, 3`.**  At every vertex `h`, paths of length `3` of
`G − h` joining neighbours `a → b → c → d` of `h` (`a ≠ c`, `b ≠ d`) have their
middle path `b p₂ q₁ c` through the inner vertices of the outer two. -/
def ThreeRouteChain : Prop :=
  ∀ ⦃h a b c d p₁ p₂ r₁ r₂ q₁ q₂ : object.Vertex⦄,
    object.graph.Adj h a → object.graph.Adj h b → object.graph.Adj h c →
    object.graph.Adj h d → a ≠ c → b ≠ d →
    ThreePath object.graph a p₁ p₂ b → ThreePath object.graph b r₁ r₂ c →
    ThreePath object.graph c q₁ q₂ d →
    h ≠ p₁ → h ≠ p₂ → h ≠ r₁ → h ≠ r₂ → h ≠ q₁ → h ≠ q₂ →
    r₁ = p₂ ∧ r₂ = q₁

/-- **The cross-edge gap.**  Two vertex-disjoint placed paths `p`, `q` of `G`
joined by edges `p i – q j` and `p i' – q j'` close no accepted cycle: the
closing length `|i − i'| + 2 + |j − j'|` is not a power of two `≥ 4`. -/
def CrossGap : Prop :=
  ∀ ⦃m n : ℕ⦄ ⦃p : Fin m → object.Vertex⦄ ⦃q : Fin n → object.Vertex⦄,
    IsPlacedPath object.graph p → IsPlacedPath object.graph q → (∀ a b, p a ≠ q b) →
    ∀ ⦃i i' : Fin m⦄ ⦃j j' : Fin n⦄,
      object.graph.Adj (p i) (q j) → object.graph.Adj (p i') (q j') →
      ¬ WindowCurvature.ForbiddenGap (Nat.dist i.1 i'.1) (Nat.dist j.1 j'.1)

/-- A placement of a window support: its `order` positions, injective, inside
the support, with adjacency exactly the path adjacency (the window is an
induced path). -/
def IsWindowPlacement {order : ℕ} (support : Finset object.Vertex)
    (q : Fin order → object.Vertex) : Prop :=
  Function.Injective q ∧ (∀ i, q i ∈ support) ∧
    ∀ i j, object.graph.Adj (q i) (q j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1

/-- The attachment label of a vertex on a placed window: the positions it is
adjacent to. -/
noncomputable def attachLabel {order : ℕ} (q : Fin order → object.Vertex)
    (x : object.Vertex) : WindowCurvature.Label order := by
  classical
  exact Finset.univ.filter fun j => object.graph.Adj x (q j)

/-- **Window positions and stubs at a packing.**  Every window of the packing
has a placement; at every placement, an interior position `i` carries
`d(q i) − 2` external neighbours (exactly one when `d(q i) = 3`), and an end
position `d(q i) − 1` (for `order ≥ 2`). -/
def WindowPositionStubs (order : ℕ) (packing : Finset (Finset object.Vertex)) : Prop :=
  ∀ P ∈ packing, (∃ q : Fin order → object.Vertex, IsWindowPlacement object P q) ∧
    ∀ q : Fin order → object.Vertex, IsWindowPlacement object P q →
      (∀ i : Fin order, 0 < i.1 → i.1 + 1 < order →
        (object.externalNeighbours P (q i)).card + 2 = object.degree (q i)) ∧
      (∀ i : Fin order, 0 < i.1 → i.1 + 1 < order → object.degree (q i) = 3 →
        (object.externalNeighbours P (q i)).card = 1) ∧
      (2 ≤ order → ∀ i : Fin order, (i.1 = 0 ∨ i.1 + 1 = order) →
        (object.externalNeighbours P (q i)).card + 1 = object.degree (q i))

/-- **Attachment rules at a packing.**  At every placed window `q` of the
packing:
* every outside vertex with a nonempty attachment label carries a legal label
  (no attachment gap `d` with `d + 2` accepted);
* two adjacent outside vertices carry `C₁`-safe labels;
* two distinct windows `p`, `q` joined at `(i, j)` and `(i', j')` have
  `|i − i'| + 2 + |j − j'|` not accepted, and in particular form no ladder
  (`|i − i'| = |j − j'| = 1`). -/
def WindowAttachmentRules (order : ℕ) (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ P ∈ packing, ∀ q : Fin order → object.Vertex, IsWindowPlacement object P q →
    ∀ x ∉ P, (attachLabel object q x).Nonempty →
      attachLabel object q x ∈ WindowCurvature.Labels order) ∧
  (∀ P ∈ packing, ∀ q : Fin order → object.Vertex, IsWindowPlacement object P q →
    ∀ x ∉ P, ∀ y ∉ P, object.graph.Adj x y →
      WindowCurvature.Safe 1 (attachLabel object q x) (attachLabel object q y)) ∧
  (∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q →
    ∀ p q : Fin order → object.Vertex, IsWindowPlacement object P p →
      IsWindowPlacement object Q q →
      ∀ i i' j j' : Fin order, object.graph.Adj (p i) (q j) → object.graph.Adj (p i') (q j') →
        ¬ WindowCurvature.ForbiddenGap (Nat.dist i.1 i'.1) (Nat.dist j.1 j'.1)) ∧
  (∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q →
    ∀ p q : Fin order → object.Vertex, IsWindowPlacement object P p →
      IsWindowPlacement object Q q →
      ∀ i i' j j' : Fin order, Nat.dist i.1 i'.1 = 1 → Nat.dist j.1 j'.1 = 1 →
        ¬ (object.graph.Adj (p i) (q j) ∧ object.graph.Adj (p i') (q j')))

variable {object}

/-! ## The properties hold -/

theorem no_cycle_four {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ∀ {v : object.Vertex} (c : object.graph.Walk v v), c.IsCycle → c.length ≠ 4 :=
  fun c cc => CycleCounting.no_dyadic_cycle avoid lengthLaw c cc 2 le_rfl

theorem no_cycle_eight {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ∀ {v : object.Vertex} (c : object.graph.Walk v v), c.IsCycle → c.length ≠ 8 :=
  fun c cc => CycleCounting.no_dyadic_cycle avoid lengthLaw c cc 3 (by norm_num)

theorem threeRouteFan {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ThreeRouteFan object := by
  intro h a b c p₁ p₂ q₁ q₂ ha hb hc bc P Q hp₁ hp₂ hq₁ hq₂
  exact three_fan_path (no_cycle_four avoid lengthLaw) (no_cycle_eight avoid lengthLaw)
    ha hb hc bc P Q hp₁ hp₂ hq₁ hq₂

theorem threeRouteChain {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ThreeRouteChain object := by
  intro h a b c d p₁ p₂ r₁ r₂ q₁ q₂ ha hb hc hd ac bd P R Q hp₁ hp₂ hr₁ hr₂ hq₁ hq₂
  exact three_chain (no_cycle_four avoid lengthLaw) (no_cycle_eight avoid lengthLaw)
    ha hb hc hd ac bd P R Q hp₁ hp₂ hr₁ hr₂ hq₁ hq₂

theorem crossGap {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    CrossGap object := by
  intro m n p q hp hq disj i i' j j' e1 e2 forbidden
  by_cases same : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := same
    simp only [Nat.dist_self] at forbidden
    exact absurd forbidden (by decide)
  · have ne : i ≠ i' ∨ j ≠ j' := by tauto
    obtain ⟨v, c, cc, cl⟩ := cross_cycle hp hq disj e1 e2 ne
    obtain ⟨k, hk, e⟩ := (Core.DyadicLength.powerOfTwoLength_iff _).mp forbidden
    refine CycleCounting.no_dyadic_cycle avoid lengthLaw c cc k hk ?_
    rw [cl, ← e, WindowCurvature.closingLength]
    omega

/-- A window placement is a placed path. -/
theorem IsWindowPlacement.isPlacedPath {order : ℕ} {support : Finset object.Vertex}
    {q : Fin order → object.Vertex} (placement : IsWindowPlacement object support q) :
    IsPlacedPath object.graph q :=
  ⟨placement.1, fun i j e => (placement.2.2 i j).2 (Or.inl e)⟩

/-- Every induced window has a placement. -/
theorem exists_windowPlacement {order : ℕ} {support : Finset object.Vertex}
    (window : object.InducesWindow order support) :
    ∃ q : Fin order → object.Vertex, IsWindowPlacement object support q := by
  obtain ⟨⟨embedding⟩, _⟩ := window
  refine ⟨fun i => (embedding i).1, ?_, fun i => (embedding i).2, ?_⟩
  · intro a b same
    exact embedding.injective (Subtype.ext same)
  · intro i j
    rw [← SimpleGraph.pathGraph_adj, ← embedding.map_adj_iff]
    rfl

/-- A placement of a window of the right size covers it. -/
theorem IsWindowPlacement.surjective {order : ℕ} {support : Finset object.Vertex}
    {q : Fin order → object.Vertex} (placement : IsWindowPlacement object support q)
    (card : support.card = order) :
    ∀ v ∈ support, ∃ i, q i = v := by
  classical
  intro v member
  have imageCard : (Finset.univ.image q).card = order := by
    rw [Finset.card_image_of_injective _ placement.1]; simp
  have imageSubset : Finset.univ.image q ⊆ support := by
    intro w hw
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.1 hw
    exact placement.2.1 index
  have imageEq : Finset.univ.image q = support :=
    Finset.eq_of_subset_of_card_le imageSubset (by rw [imageCard, card])
  rw [← imageEq] at member
  obtain ⟨index, _, eq⟩ := Finset.mem_image.1 member
  exact ⟨index, eq⟩

/-- **The stub identity at a placed window**: the external neighbours of `q i`
plus its path neighbours make up its degree. -/
theorem placement_stub_identity {order : ℕ} {support : Finset object.Vertex}
    {q : Fin order → object.Vertex} (placement : IsWindowPlacement object support q)
    (card : support.card = order) (i : Fin order) :
    (object.externalNeighbours support (q i)).card +
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card =
      object.degree (q i) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have windowNeighboursEq :
      object.windowNeighbours support (q i) =
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).image q := by
    ext w
    simp only [FiniteObject.windowNeighbours, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨adjacent, wMem⟩
      obtain ⟨j, rfl⟩ := placement.surjective card w wMem
      exact ⟨j, (placement.2.2 i j).1 adjacent, rfl⟩
    · rintro ⟨j, pathAdj, rfl⟩
      exact ⟨(placement.2.2 i j).2 pathAdj, placement.2.1 j⟩
  have windowNeighboursCard :
      (object.windowNeighbours support (q i)).card =
        (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card := by
    rw [windowNeighboursEq, Finset.card_image_of_injective _ placement.1]
  have degreeEq := FiniteObject.card_windowNeighbours_add_card_externalNeighbours
    (object := object) support (q i)
  rw [windowNeighboursCard] at degreeEq
  omega

theorem windowPositionStubs {order : ℕ} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    WindowPositionStubs object order packing := by
  intro P member
  have window := valid.1 P member
  refine ⟨exists_windowPlacement window, fun q placement => ?_⟩
  have card := window.2
  have interior : ∀ i : Fin order, 0 < i.1 → i.1 + 1 < order →
      (object.externalNeighbours P (q i)).card + 2 = object.degree (q i) := by
    intro i pos lt
    have identity := placement_stub_identity placement card i
    have two : (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) =
        {⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, by omega⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      omega
    have twoCard : ({⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, by omega⟩} :
        Finset (Fin order)).card = 2 := by
      rw [Finset.card_pair]
      intro h
      rw [Fin.ext_iff] at h
      simp only at h
      omega
    rw [two, twoCard] at identity
    exact identity
  refine ⟨interior, fun i pos lt cubic => ?_, fun two i isEnd => ?_⟩
  · have := interior i pos lt
    omega
  · have identity := placement_stub_identity placement card i
    have one : (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card
        = 1 := by
      rcases isEnd with first | last
      · have : (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) =
            {⟨1, by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Fin.ext_iff]
          omega
        rw [this, Finset.card_singleton]
      · have : (Finset.univ.filter fun j : Fin order => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) =
            {⟨order - 2, by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Fin.ext_iff]
          have := j.2
          omega
        rw [this, Finset.card_singleton]
    rw [one] at identity
    exact identity

theorem windowAttachmentRules {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {order : ℕ} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    WindowAttachmentRules object order packing := by
  classical
  have gap := crossGap avoid lengthLaw
  have mem_label : ∀ {q : Fin order → object.Vertex} {x : object.Vertex} {j : Fin order},
      j ∈ attachLabel object q x ↔ object.graph.Adj x (q j) := by
    intro q x j
    simp [attachLabel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P member q placement x outside nonempty
    rw [WindowCurvature.Labels, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, nonempty, ?_⟩
    intro j memJ j' memJ'
    let p : Fin 1 → object.Vertex := fun _ => x
    have hp : IsPlacedPath object.graph p :=
      ⟨fun a b _ => Subsingleton.elim a b, fun a b e => by omega⟩
    have disj : ∀ a b, p a ≠ q b := by
      intro a b same
      have hb := placement.2.1 b
      rw [← same] at hb
      exact outside hb
    have := @gap 1 order p q hp placement.isPlacedPath disj 0 0 j j'
      (mem_label.1 memJ) (mem_label.1 memJ')
    simpa using this
  · intro P member q placement x outsideX y outsideY xy j memJ j' memJ'
    let p : Fin 2 → object.Vertex := ![x, y]
    have hp : IsPlacedPath object.graph p := by
      refine ⟨?_, ?_⟩
      · intro a b same
        fin_cases a <;> fin_cases b
        · rfl
        · exact absurd same xy.ne
        · exact absurd same xy.ne'
        · rfl
      · intro a b e
        fin_cases a <;> fin_cases b <;> simp at e
        exact xy
    have disj : ∀ a b, p a ≠ q b := by
      intro a b same
      have hb := placement.2.1 b
      rw [← same] at hb
      fin_cases a
      · exact outsideX hb
      · exact outsideY hb
    have := @gap 2 order p q hp placement.isPlacedPath disj 0 1 j j'
      (mem_label.1 memJ) (mem_label.1 memJ')
    simpa [Nat.dist] using this
  · intro P memberP Q memberQ distinct p q placementP placementQ i i' j j' e1 e2
    have disj : ∀ a b, p a ≠ q b := by
      intro a b same
      exact Finset.disjoint_left.mp (valid.2 P memberP Q memberQ distinct)
        (placementP.2.1 a) (same ▸ placementQ.2.1 b)
    exact gap placementP.isPlacedPath placementQ.isPlacedPath disj e1 e2
  · intro P memberP Q memberQ distinct p q placementP placementQ i i' j j' di dj both
    have disj : ∀ a b, p a ≠ q b := by
      intro a b same
      exact Finset.disjoint_left.mp (valid.2 P memberP Q memberQ distinct)
        (placementP.2.1 a) (same ▸ placementQ.2.1 b)
    apply gap placementP.isPlacedPath placementQ.isPlacedPath disj both.1 both.2
    rw [di, dj]
    exact Core.DyadicLength.powerOfTwoLength_four

end Object

end Hypostructure.Graph.LocalRigidity
