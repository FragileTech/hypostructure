import Hypostructure.Graph.HubLink.TCount

/-!
# The two slots of a vertex of `A₁` against no `C₈`

Vocabulary-free.

`JointSystem` setting plus no `C₈` (`hC8`).  A vertex `x ∈ A₁` (cubic, exactly one hub `h`)
has two cubic neighbours ("slots").  Either a slot has `t ∈ {0, 2}` (at most `3|A₀| + |A₂|`
such `x`), or each slot is in `N(h)` ("matched", at most one by `C₄`) or has `t = 1` with a
hub `≠ h` ("link").

* `ml_fibre` (**matched + link**): for hubs `h ≠ c`, at most 2 vertices `x ∈ N(h) ∩ A₁` have a
  neighbour in `N(h)` and a `t = 1` neighbour in `N(c)` — two such on disjoint matched edges
  close the 8-cycle `h x₁' x₁ z₁ c z₂ x₂ x₂'`.
* `ll_fibre` (**link + link**): for hubs `a ≠ b`, at most 2 cubic vertices `x ∉ N(a) ∪ N(b)`
  have a `t = 1` neighbour in `N(a)` and one in `N(b)` — two with disjoint slots close the
  8-cycle `a y₁ x₁ z₁ b z₂ x₂ y₂`.
* `slot_bound`: `|A₁| ≤ 3|A₀| + |A₂| + 2|H|(|H| − 1) + 2·C(|H|, 2)`.
* `slot_relation`: `4σ + 21|H| ≤ 3n + 6|H|²`, i.e. `n + 21|H| ≤ 6|H|² + 4s`.
-/

open Finset Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An 8-cycle on 8 distinct vertices is excluded. -/
theorem no_c8 (hC8 : NoCycleLen G 8) (v0 v1 v2 v3 v4 v5 v6 v7 : V)
    (hnd : [v0, v1, v2, v3, v4, v5, v6, v7].Nodup)
    (a01 : G.Adj v0 v1) (a12 : G.Adj v1 v2) (a23 : G.Adj v2 v3) (a34 : G.Adj v3 v4)
    (a45 : G.Adj v4 v5) (a56 : G.Adj v5 v6) (a67 : G.Adj v6 v7) (a70 : G.Adj v7 v0) : False := by
  apply hC8 ![v0, v1, v2, v3, v4, v5, v6, v7]
  · rw [← List.nodup_ofFn]; simpa [List.ofFn_succ] using hnd
  · intro i
    fin_cases i
    · exact a01
    · exact a12
    · exact a23
    · exact a34
    · exact a45
    · exact a56
    · exact a67
    · exact a70

theorem ne_adj {u v w : V} (h1 : G.Adj u w) (h2 : ¬ G.Adj v w) : u ≠ v :=
  fun e => h2 (e ▸ h1)

theorem ne_deg {u v : V} (h1 : G.degree u = 3) (h2 : 4 ≤ G.degree v) : u ≠ v :=
  fun e => by subst e; omega

/-- `t(y) = 1` and `y ∼ a` (a hub): `a` is the only hub of `y`. -/
theorem tc_one_unique {y a w : V} (ht : tc G y = 1) (ha : 4 ≤ G.degree a) (hya : G.Adj y a)
    (hw : 4 ≤ G.degree w) (hyw : G.Adj y w) : w = a := by
  obtain ⟨h, hh⟩ := card_eq_one.1 ht
  have m1 : a ∈ G.neighborFinset y ∩ Hset G := by simp [hya, ha]
  have m2 : w ∈ G.neighborFinset y ∩ Hset G := by simp [hyw, hw]
  rw [hh] at m1 m2
  rw [mem_singleton] at m1 m2
  rw [m1, m2]

/-- Matched + link at `(h, c)`. -/
def MLat (G : SimpleGraph V) (h c x : V) : Prop :=
  G.Adj x h ∧ G.degree x = 3 ∧ (∃ x', G.Adj x x' ∧ G.Adj x' h) ∧
    ∃ z, G.Adj x z ∧ G.Adj z c ∧ tc G z = 1 ∧ G.degree z = 3

/-- Link + link at `(a, b)`. -/
def LLat (G : SimpleGraph V) (a b x : V) : Prop :=
  G.degree x = 3 ∧ ¬ G.Adj x a ∧ ¬ G.Adj x b ∧
    ∃ y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y a ∧ G.Adj z b ∧ tc G y = 1 ∧ tc G z = 1 ∧
      G.degree y = 3 ∧ G.degree z = 3

theorem LLat.swap {a b x : V} (hx : LLat G a b x) : LLat G b a x := by
  obtain ⟨d, na, nb, y, z, xy, xz, ya, zb, ty, tz, dy, dz⟩ := hx
  exact ⟨d, nb, na, z, y, xz, xy, zb, ya, tz, ty, dz, dy⟩

/-- **Matched + link: two on disjoint matched edges close a `C₈`**, so two distinct such
vertices are adjacent (matched to each other). -/
theorem ml_pair (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) {h c : V} (hh : 4 ≤ G.degree h)
    (hc : 4 ≤ G.degree c) (hne : h ≠ c) {x₁ x₂ : V} (h1 : MLat G h c x₁) (h2 : MLat G h c x₂)
    (h12 : x₁ ≠ x₂) : G.Adj x₁ x₂ := by
  by_contra hna
  obtain ⟨x₁h, d1, ⟨p₁, x₁p, p₁h⟩, z₁, x₁z, z₁c, t₁, e₁⟩ := h1
  obtain ⟨x₂h, d2, ⟨p₂, x₂p, p₂h⟩, z₂, x₂z, z₂c, t₂, e₂⟩ := h2
  have dp₁ := deg_three_of_hub_adj hmin hind hh p₁h.symm
  have dp₂ := deg_three_of_hub_adj hmin hind hh p₂h.symm
  have z₁h : ¬ G.Adj z₁ h := fun a => hne (tc_one_unique t₁ hc z₁c hh a)
  have z₂h : ¬ G.Adj z₂ h := fun a => hne (tc_one_unique t₂ hc z₂c hh a)
  have ch : ¬ G.Adj c h := hind c h hc hh
  have hhh : ¬ G.Adj h h := G.irrefl
  -- distinctness
  have f01 : h ≠ p₁ := (ne_deg dp₁ hh).symm
  have f02 : h ≠ x₁ := (ne_deg d1 hh).symm
  have f03 : h ≠ z₁ := (ne_deg e₁ hh).symm
  have f04 : h ≠ c := hne
  have f05 : h ≠ z₂ := (ne_deg e₂ hh).symm
  have f06 : h ≠ x₂ := (ne_deg d2 hh).symm
  have f07 : h ≠ p₂ := (ne_deg dp₂ hh).symm
  have f12 : p₁ ≠ x₁ := (G.ne_of_adj x₁p).symm
  have f13 : p₁ ≠ z₁ := ne_adj p₁h z₁h
  have f14 : p₁ ≠ c := ne_deg dp₁ hc
  have f15 : p₁ ≠ z₂ := ne_adj p₁h z₂h
  have f16 : p₁ ≠ x₂ := fun e => hna (e ▸ x₁p)
  have f17 : p₁ ≠ p₂ := by
    intro e; subst e
    exact h12 (hC4 p₁ h x₁ x₂ (ne_deg dp₁ hh) x₁p.symm x₁h.symm x₂p.symm x₂h.symm)
  have f23 : x₁ ≠ z₁ := ne_adj x₁h z₁h
  have f24 : x₁ ≠ c := ne_deg d1 hc
  have f25 : x₁ ≠ z₂ := ne_adj x₁h z₂h
  have f26 : x₁ ≠ x₂ := h12
  have f27 : x₁ ≠ p₂ := fun e => hna (e ▸ x₂p.symm)
  have f34 : z₁ ≠ c := ne_deg e₁ hc
  have f35 : z₁ ≠ z₂ := by
    intro e; subst e
    exact h12 (hC4 z₁ h x₁ x₂ (ne_deg e₁ hh) x₁z.symm x₁h.symm x₂z.symm x₂h.symm)
  have f36 : z₁ ≠ x₂ := (ne_adj x₂h z₁h).symm
  have f37 : z₁ ≠ p₂ := (ne_adj p₂h z₁h).symm
  have f45 : c ≠ z₂ := (ne_deg e₂ hc).symm
  have f46 : c ≠ x₂ := (ne_deg d2 hc).symm
  have f47 : c ≠ p₂ := (ne_deg dp₂ hc).symm
  have f56 : z₂ ≠ x₂ := (ne_adj x₂h z₂h).symm
  have f57 : z₂ ≠ p₂ := (ne_adj p₂h z₂h).symm
  have f67 : x₂ ≠ p₂ := G.ne_of_adj x₂p
  exact no_c8 hC8 h p₁ x₁ z₁ c z₂ x₂ p₂
    (by simp [f01, f02, f03, f04, f05, f06, f07, f12, f13, f14, f15, f16, f17, f23, f24, f25,
      f26, f27, f34, f35, f36, f37, f45, f46, f47, f56, f57, f67])
    p₁h.symm x₁p.symm x₁z z₁c z₂c.symm x₂z.symm x₂p p₂h

/-- **Matched + link fibre `≤ 2`.** -/
theorem ml_fibre (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) {h c : V} (hh : 4 ≤ G.degree h)
    (hc : 4 ≤ G.degree c) (hne : h ≠ c) : (univ.filter (MLat G h c)).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := two_lt_card_iff.1 hgt
  simp only [mem_filter, mem_univ, true_and] at ha hb hd
  have e1 := ml_pair hmin hind hC4 hC8 hh hc hne ha hb hab
  have e2 := ml_pair hmin hind hC4 hC8 hh hc hne ha hd had
  exact hbd (hC4 a h b d (ne_deg ha.2.1 hh) e1 hb.1.symm e2 hd.1.symm)

/-- **Link + link: two with disjoint slots close a `C₈`.** -/
theorem ll_pair (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC8 : NoCycleLen G 8) {a b : V} (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) (hab : a ≠ b)
    {x₁ x₂ y₁ z₁ y₂ z₂ : V} (h12 : x₁ ≠ x₂)
    (d1 : G.degree x₁ = 3) (n1a : ¬ G.Adj x₁ a) (n1b : ¬ G.Adj x₁ b)
    (x₁y : G.Adj x₁ y₁) (x₁z : G.Adj x₁ z₁) (y₁a : G.Adj y₁ a) (z₁b : G.Adj z₁ b)
    (ty₁ : tc G y₁ = 1) (tz₁ : tc G z₁ = 1) (dy₁ : G.degree y₁ = 3) (dz₁ : G.degree z₁ = 3)
    (d2 : G.degree x₂ = 3) (n2a : ¬ G.Adj x₂ a) (n2b : ¬ G.Adj x₂ b)
    (x₂y : G.Adj x₂ y₂) (x₂z : G.Adj x₂ z₂) (y₂a : G.Adj y₂ a) (z₂b : G.Adj z₂ b)
    (ty₂ : tc G y₂ = 1) (tz₂ : tc G z₂ = 1) (dy₂ : G.degree y₂ = 3) (dz₂ : G.degree z₂ = 3) :
    y₁ = y₂ ∨ z₁ = z₂ := by
  by_contra hno
  push Not at hno
  obtain ⟨hy, hz⟩ := hno
  have y₁b : ¬ G.Adj y₁ b := fun e => hab (tc_one_unique ty₁ ha y₁a hb e).symm
  have y₂b : ¬ G.Adj y₂ b := fun e => hab (tc_one_unique ty₂ ha y₂a hb e).symm
  have z₁a : ¬ G.Adj z₁ a := fun e => hab (tc_one_unique tz₁ hb z₁b ha e)
  have z₂a : ¬ G.Adj z₂ a := fun e => hab (tc_one_unique tz₂ hb z₂b ha e)
  -- cycle a y₁ x₁ z₁ b z₂ x₂ y₂
  have f01 : a ≠ y₁ := (ne_deg dy₁ ha).symm
  have f02 : a ≠ x₁ := (ne_deg d1 ha).symm
  have f03 : a ≠ z₁ := (ne_deg dz₁ ha).symm
  have f04 : a ≠ b := hab
  have f05 : a ≠ z₂ := (ne_deg dz₂ ha).symm
  have f06 : a ≠ x₂ := (ne_deg d2 ha).symm
  have f07 : a ≠ y₂ := (ne_deg dy₂ ha).symm
  have f12 : y₁ ≠ x₁ := ne_adj y₁a n1a
  have f13 : y₁ ≠ z₁ := ne_adj y₁a z₁a
  have f14 : y₁ ≠ b := ne_deg dy₁ hb
  have f15 : y₁ ≠ z₂ := ne_adj y₁a z₂a
  have f16 : y₁ ≠ x₂ := ne_adj y₁a n2a
  have f17 : y₁ ≠ y₂ := hy
  have f23 : x₁ ≠ z₁ := (ne_adj z₁b n1b).symm
  have f24 : x₁ ≠ b := ne_deg d1 hb
  have f25 : x₁ ≠ z₂ := (ne_adj z₂b n1b).symm
  have f26 : x₁ ≠ x₂ := h12
  have f27 : x₁ ≠ y₂ := (ne_adj y₂a n1a).symm
  have f34 : z₁ ≠ b := ne_deg dz₁ hb
  have f35 : z₁ ≠ z₂ := hz
  have f36 : z₁ ≠ x₂ := ne_adj z₁b n2b
  have f37 : z₁ ≠ y₂ := ne_adj z₁b y₂b
  have f45 : b ≠ z₂ := (ne_deg dz₂ hb).symm
  have f46 : b ≠ x₂ := (ne_deg d2 hb).symm
  have f47 : b ≠ y₂ := (ne_deg dy₂ hb).symm
  have f56 : z₂ ≠ x₂ := ne_adj z₂b n2b
  have f57 : z₂ ≠ y₂ := ne_adj z₂b y₂b
  have f67 : x₂ ≠ y₂ := (ne_adj y₂a n2a).symm
  exact no_c8 hC8 a y₁ x₁ z₁ b z₂ x₂ y₂
    (by simp [f01, f02, f03, f04, f05, f06, f07, f12, f13, f14, f15, f16, f17, f23, f24, f25,
      f26, f27, f34, f35, f36, f37, f45, f46, f47, f56, f57, f67])
    y₁a.symm x₁y.symm x₁z z₁b z₂b.symm x₂z.symm x₂y y₂a

/-- A cubic vertex has at most two neighbours besides a given one. -/
theorem three_nbrs {y w x₁ x₂ x₃ : V} (dy : G.degree y = 3) (hw : G.Adj y w)
    (h1 : G.Adj y x₁) (h2 : G.Adj y x₂) (h3 : G.Adj y x₃) (n1 : x₁ ≠ w) (n2 : x₂ ≠ w)
    (n3 : x₃ ≠ w) (d12 : x₁ ≠ x₂) (d13 : x₁ ≠ x₃) (d23 : x₂ ≠ x₃) : False := by
  have hsub : ({w, x₁, x₂, x₃} : Finset V) ⊆ G.neighborFinset y := by
    intro v hv; simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simpa
  have := card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, dy] at this
  rw [card_insert_of_notMem (by simp [n1.symm, n2.symm, n3.symm]),
    card_insert_of_notMem (by simp [d12, d13]), card_insert_of_notMem (by simp [d23]),
    card_singleton] at this
  omega

/-- **Link + link fibre `≤ 2`.** -/
theorem ll_fibre (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC8 : NoCycleLen G 8) {a b : V} (ha : 4 ≤ G.degree a) (hb : 4 ≤ G.degree b) (hab : a ≠ b) :
    (univ.filter (LLat G a b)).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨x₁, x₂, x₃, m1, m2, m3, d12, d13, d23⟩ := two_lt_card_iff.1 hgt
  simp only [mem_filter, mem_univ, true_and] at m1 m2 m3
  obtain ⟨e1, n1a, n1b, y₁, z₁, x₁y, x₁z, y₁a, z₁b, ty₁, tz₁, dy₁, dz₁⟩ := m1
  obtain ⟨e2, n2a, n2b, y₂, z₂, x₂y, x₂z, y₂a, z₂b, ty₂, tz₂, dy₂, dz₂⟩ := m2
  obtain ⟨e3, n3a, n3b, y₃, z₃, x₃y, x₃z, y₃a, z₃b, ty₃, tz₃, dy₃, dz₃⟩ := m3
  have p12 := ll_pair hmin hind hC8 ha hb hab d12 e1 n1a n1b x₁y x₁z y₁a z₁b ty₁ tz₁ dy₁ dz₁
    e2 n2a n2b x₂y x₂z y₂a z₂b ty₂ tz₂ dy₂ dz₂
  have p13 := ll_pair hmin hind hC8 ha hb hab d13 e1 n1a n1b x₁y x₁z y₁a z₁b ty₁ tz₁ dy₁ dz₁
    e3 n3a n3b x₃y x₃z y₃a z₃b ty₃ tz₃ dy₃ dz₃
  have p23 := ll_pair hmin hind hC8 ha hb hab d23 e2 n2a n2b x₂y x₂z y₂a z₂b ty₂ tz₂ dy₂ dz₂
    e3 n3a n3b x₃y x₃z y₃a z₃b ty₃ tz₃ dy₃ dz₃
  -- all three share `y` or all three share `z`
  have hy3 : ¬ (y₁ = y₂ ∧ y₁ = y₃) := by
    rintro ⟨r2, r3⟩
    exact three_nbrs dy₁ y₁a x₁y.symm (r2 ▸ x₂y.symm) (r3 ▸ x₃y.symm)
      (ne_deg e1 ha) (ne_deg e2 ha) (ne_deg e3 ha) d12 d13 d23
  have hz3 : ¬ (z₁ = z₂ ∧ z₁ = z₃) := by
    rintro ⟨r2, r3⟩
    exact three_nbrs dz₁ z₁b x₁z.symm (r2 ▸ x₂z.symm) (r3 ▸ x₃z.symm)
      (ne_deg e1 hb) (ne_deg e2 hb) (ne_deg e3 hb) d12 d13 d23
  rcases p12 with r12 | r12 <;> rcases p13 with r13 | r13 <;> rcases p23 with r23 | r23
  · exact hy3 ⟨r12, r13⟩
  · exact hy3 ⟨r12, r13⟩
  · exact hy3 ⟨r12, r12.trans r23⟩
  · exact hz3 ⟨r13.trans r23.symm, r13⟩
  · exact hy3 ⟨r13.trans r23.symm, r13⟩
  · exact hz3 ⟨r12, r12.trans r23⟩
  · exact hz3 ⟨r12, r13⟩
  · exact hz3 ⟨r12, r13⟩

/-! ## The slot bound -/

/-- The unordered-pair version of `LLat`. -/
noncomputable def LLset (G : SimpleGraph V) (P : Finset V) : Finset V :=
  univ.filter (fun x => ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ LLat G a b x)

theorem LLset_card (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v)
    (hC8 : NoCycleLen G 8) {P : Finset V} (hP : P ∈ (Hset G).powersetCard 2) :
    (LLset G P).card ≤ 2 := by
  rw [mem_powersetCard] at hP
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hP.2
  have ha : 4 ≤ G.degree a := by have := hP.1 (by simp : a ∈ ({a, b} : Finset V)); simpa using this
  have hb : 4 ≤ G.degree b := by have := hP.1 (by simp : b ∈ ({a, b} : Finset V)); simpa using this
  refine le_trans (card_le_card ?_) (ll_fibre hmin hind hC8 ha hb hab)
  intro x hx
  simp only [LLset, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hx ⊢
  obtain ⟨a', ha', b', hb', hne, hl⟩ := hx
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact absurd rfl hne
  · exact hl
  · exact hl.swap
  · exact absurd rfl hne

theorem A2_one_cubic (hmin : ∀ v, 3 ≤ G.degree v) {y : V} (hy : y ∈ Aset G 2) :
    (G.neighborFinset y ∩ Lset G).card = 1 := by
  simp only [mem_filter, mem_univ, true_and] at hy
  have hs := card_sdiff_add_card_inter (G.neighborFinset y) (Hset G)
  have h2 : (G.neighborFinset y ∩ Hset G).card = 2 := hy.2
  rw [G.card_neighborFinset_eq_degree, hy.1, h2] at hs
  have e : G.neighborFinset y \ Hset G = G.neighborFinset y ∩ Lset G := by
    ext w; simp only [mem_sdiff, mem_inter, mem_filter, mem_univ, true_and, not_le]
    have := hmin w
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [e] at hs; omega

/-- **The slot bound**: `|A₁| ≤ 3|A₀| + |A₂| + 2|H|(|H| − 1) + 2·C(|H|, 2)`. -/
theorem slot_bound (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) :
    (Aset G 1).card ≤ 3 * (Aset G 0).card + (Aset G 2).card
      + 2 * ((Hset G).card * (Hset G).card - (Hset G).card)
      + 2 * (Hset G).card.choose 2 := by
  set E0 := (Aset G 1).filter (fun x => ∃ w, G.Adj x w ∧ w ∈ Aset G 0) with hE0
  set E2 := (Aset G 1).filter (fun x => ∃ w, G.Adj x w ∧ w ∈ Aset G 2) with hE2
  set ML := (Hset G).offDiag.biUnion (fun p => univ.filter (MLat G p.1 p.2)) with hML
  set LL := ((Hset G).powersetCard 2).biUnion (LLset G) with hLL
  have hcover : Aset G 1 ⊆ E0 ∪ E2 ∪ ML ∪ LL := by
    intro x hx
    obtain ⟨hx3, h, hH⟩ := mem_A1 hx
    have hxL : x ∈ Lset G := (mem_filter.1 hx).1
    have hhN : h ∈ G.neighborFinset x ∩ Hset G := by rw [hH]; simp
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      at hhN
    have onehub : ∀ w, 4 ≤ G.degree w → G.Adj x w → w = h := by
      intro w hw hxw
      have : w ∈ G.neighborFinset x ∩ Hset G := by simp [hxw, hw]
      rw [hH] at this; simpa using this
    -- a slot with `t ∈ {0, 2}`
    by_cases hbad : ∃ w, G.Adj x w ∧ G.degree w = 3 ∧ ¬ G.Adj w h ∧ tc G w ≠ 1
    · obtain ⟨w, hxw, hw3, hwh, htw⟩ := hbad
      have hwL : w ∈ Lset G := by simp [hw3]
      have hle := tc_le_two hmin hdeg hwL
      by_cases h0 : tc G w = 0
      · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
        exact mem_filter.2 ⟨hx, w, hxw, mem_filter.2 ⟨hwL, h0⟩⟩
      · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
        exact mem_filter.2 ⟨hx, w, hxw, mem_filter.2 ⟨hwL, by omega⟩⟩
    push Not at hbad
    obtain ⟨z, hxz, hz3, hzs⟩ := outer_cubic hmin hC4 hx
    have hzh : ¬ G.Adj z h := fun e => hzs ⟨h, hhN.2, hhN.1, e⟩
    have tz : tc G z = 1 := hbad z hxz hz3 hzh
    obtain ⟨c, hcS⟩ := card_eq_one.1 tz
    have hcN : c ∈ G.neighborFinset z ∩ Hset G := by rw [hcS]; simp
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      at hcN
    have hch : c ≠ h := fun e => hzh (e ▸ hcN.1)
    by_cases hM : ∃ y, G.Adj x y ∧ G.Adj y h
    · refine mem_union_left _ (mem_union_right _ ?_)
      refine mem_biUnion.2 ⟨(h, c), ?_, ?_⟩
      · simp only [mem_offDiag, mem_filter, mem_univ, true_and]
        exact ⟨hhN.2, hcN.2, hch.symm⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact ⟨hhN.1, hx3, hM, z, hxz, hcN.1, tz, hz3⟩
    push Not at hM
    -- the second cubic neighbour
    have hsplit := card_sdiff_add_card_inter (G.neighborFinset x) (Hset G)
    rw [hH, card_singleton, G.card_neighborFinset_eq_degree, hx3] at hsplit
    have hzmem : z ∈ G.neighborFinset x \ Hset G := by
      simp only [mem_sdiff, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      exact ⟨hxz, by omega⟩
    obtain ⟨y, hy, hyz⟩ := exists_mem_ne (show 1 < (G.neighborFinset x \ Hset G).card
      by omega) z
    simp only [mem_sdiff, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and,
      not_le] at hy
    have hy3 : G.degree y = 3 := by have := hmin y; omega
    have hyh : ¬ G.Adj y h := hM y hy.1
    have ty : tc G y = 1 := hbad y hy.1 hy3 hyh
    obtain ⟨a, haS⟩ := card_eq_one.1 ty
    have haN : a ∈ G.neighborFinset y ∩ Hset G := by rw [haS]; simp
    simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
      at haN
    have hah : a ≠ h := fun e => hyh (e ▸ haN.1)
    have hac : a ≠ c := by
      intro e; subst e
      exact hyz (hC4 x a y z (ne_deg hx3 haN.2) hy.1 haN.1.symm hxz hcN.1.symm)
    refine mem_union_right _ (mem_biUnion.2 ⟨{a, c}, ?_, ?_⟩)
    · rw [mem_powersetCard, card_pair hac]
      refine ⟨?_, rfl⟩
      intro w hw; simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · simpa using haN.2
      · simpa using hcN.2
    · simp only [LLset, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      refine ⟨a, Or.inl rfl, c, Or.inr rfl, hac, hx3, fun e => hah (onehub a haN.2 e),
        fun e => hch (onehub c hcN.2 e), y, z, hy.1, hxz, haN.1, hcN.1, ty, tz, hy3, hz3⟩
  -- the four bounds
  have bE0 : E0.card ≤ 3 * (Aset G 0).card := by
    have h1 : E0.card ≤ ∑ x ∈ E0, (G.neighborFinset x ∩ Aset G 0).card := by
      rw [card_eq_sum_ones]; apply sum_le_sum; intro x hx
      obtain ⟨w, hxw, hw⟩ := (mem_filter.1 hx).2
      exact card_pos.2 ⟨w, by simp [hxw, hw]⟩
    rw [double_count G E0 (Aset G 0)] at h1
    have h2 : ∑ y ∈ Aset G 0, (G.neighborFinset y ∩ E0).card ≤ ∑ y ∈ Aset G 0, 3 := by
      apply sum_le_sum; intro y hy
      have hy3 : G.degree y = 3 := by simp only [mem_filter, mem_univ, true_and] at hy; exact hy.1
      rw [← hy3, ← G.card_neighborFinset_eq_degree]; exact card_le_card inter_subset_left
    rw [sum_const, smul_eq_mul] at h2
    omega
  have bE2 : E2.card ≤ (Aset G 2).card := by
    have h1 : E2.card ≤ ∑ x ∈ E2, (G.neighborFinset x ∩ Aset G 2).card := by
      rw [card_eq_sum_ones]; apply sum_le_sum; intro x hx
      obtain ⟨w, hxw, hw⟩ := (mem_filter.1 hx).2
      exact card_pos.2 ⟨w, by simp [hxw, hw]⟩
    rw [double_count G E2 (Aset G 2)] at h1
    have h2 : ∑ y ∈ Aset G 2, (G.neighborFinset y ∩ E2).card ≤ ∑ y ∈ Aset G 2, 1 := by
      apply sum_le_sum; intro y hy
      rw [← A2_one_cubic hmin hy]
      apply card_le_card; intro w hw
      simp only [mem_inter] at hw ⊢
      exact ⟨hw.1, (mem_filter.1 (mem_filter.1 hw.2).1).1⟩
    rw [sum_const, smul_eq_mul, mul_one] at h2
    omega
  have bML : ML.card ≤ 2 * ((Hset G).card * (Hset G).card - (Hset G).card) := by
    calc ML.card ≤ ∑ p ∈ (Hset G).offDiag, (univ.filter (MLat G p.1 p.2)).card :=
          card_biUnion_le
      _ ≤ ∑ p ∈ (Hset G).offDiag, 2 := by
          apply sum_le_sum; intro p hp
          simp only [mem_offDiag, mem_filter, mem_univ, true_and] at hp
          exact ml_fibre hmin hind hC4 hC8 hp.1 hp.2.1 hp.2.2
      _ = _ := by rw [sum_const, smul_eq_mul, offDiag_card, mul_comm]
  have bLL : LL.card ≤ 2 * (Hset G).card.choose 2 := by
    calc LL.card ≤ ∑ P ∈ (Hset G).powersetCard 2, (LLset G P).card := card_biUnion_le
      _ ≤ ∑ P ∈ (Hset G).powersetCard 2, 2 :=
          sum_le_sum (fun P hP => LLset_card hmin hind hC8 hP)
      _ = _ := by rw [sum_const, smul_eq_mul, card_powersetCard, mul_comm]
  have hc := card_le_card hcover
  have u1 := card_union_le (E0 ∪ E2 ∪ ML) LL
  have u2 := card_union_le (E0 ∪ E2) ML
  have u3 := card_union_le E0 E2
  omega

theorem two_choose (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

/-- **The slot relation**: `4σ + 21|H| ≤ 3n + 6|H|²`, i.e. `n + 21|H| ≤ 6|H|² + 4s`. -/
theorem slot_relation (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) :
    4 * sigma G + 21 * (Hset G).card
      ≤ 3 * Fintype.card V + 6 * ((Hset G).card * (Hset G).card) := by
  have hs := slot_bound hmin hind hdeg hC4 hC8
  obtain ⟨a1, a2⟩ := acount hmin hind hdeg
  have hL := card_L_add_H hmin
  have h2 := a2_le hC4
  have hid := exception_identity hmin hind hdeg
  have hc := two_choose (Hset G).card
  have hle : (Hset G).card ≤ (Hset G).card * (Hset G).card := Nat.le_mul_self _
  omega

end Hypostructure.Graph.HubLink

namespace Hypostructure.Graph.HubLink

open Hypostructure.Graph.JointSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **The slot relation, exact in `|A₂|`**: `4σ + 18|H| ≤ 3n + 6|A₂| + 3|H|²`, i.e.
`n + 18|H| ≤ 6|A₂| + 3|H|² + 4s`: the survivors need `6|A₂| + 3|H|² ≥ n + 18|H| − 4s`. -/
theorem slot_exact (hmin : ∀ v, 3 ≤ G.degree v)
    (hind : ∀ u v, 4 ≤ G.degree u → 4 ≤ G.degree v → ¬ G.Adj u v) (hdeg : ProperTwoLow G)
    (hC4 : C4Free G) (hC8 : NoCycleLen G 8) :
    4 * sigma G + 18 * (Hset G).card
      ≤ 3 * Fintype.card V + 6 * (Aset G 2).card + 3 * ((Hset G).card * (Hset G).card) := by
  have hs := slot_bound hmin hind hdeg hC4 hC8
  obtain ⟨a1, a2⟩ := acount hmin hind hdeg
  have hL := card_L_add_H hmin
  have hid := exception_identity hmin hind hdeg
  have hc := two_choose (Hset G).card
  have hle : (Hset G).card ≤ (Hset G).card * (Hset G).card := Nat.le_mul_self _
  omega

end Hypostructure.Graph.HubLink
