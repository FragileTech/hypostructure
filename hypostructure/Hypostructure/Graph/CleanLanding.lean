import Hypostructure.Graph.PackingExchange
import Hypostructure.Graph.NetCharge

/-!
# Clean landings of remainder pieces on a window, and the per-window cap

At a maximum window packing with remainder `R`, fix a member `P` placed by `p` (order `n`).
A vertex `x` of a support `X ⊆ R` adjacent to `p i` is a *clean `a`-landing* when some induced
path `α` of G inside `X` on `a` vertices ends at `x` and, for every arm vertex `u` and every
position `k` with `|k − i| ≤ n − 1 − a`, `u ~ p k` forces `u = x` and `k = i`
(`CleanLanding`).  A *long landing* is a clean `(n−2)`- or `(n−1)`-landing (`LongLanding`).

The packing exchange (`PackingExchange.false_of_two_windows_in_member_union_remainder`)
gives, for disjoint supports `X, Y, Z ⊆ R`:

* `false_of_clean_runs`: two clean landings with disjoint runs of positions of complementary
  sizes (each run having the landing position as an end) do not coexist;
* `long_pair_rule`: two long landings of disjoint supports land at the same position, or at
  `{0, 1}`, or at `{n−2, n−1}` (`4 ≤ n`);
* `false_of_clean_triple`: two clean landings of `X`, `Y` (no `X`–`Y` edge) at the same
  position `p e` with `a + b ≥ n − 1`, and a clean landing of `Z` with a run avoiding `e`, do
  not coexist (the path `α' · p e · β'` and the arm-plus-run of `Z` are two disjoint windows);
* `long_landing_cap`: over a family of pairwise disjoint, pairwise non-adjacent supports in
  `R`, the number of supports with a long landing on `(P, p)` is at most
  `(δ − 1) + Σ_{v ∈ P} (d(v) − δ)`.
-/

namespace Hypostructure.Graph.PackingExchange

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.LocalRigidity
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

/-- **A clean `a`-landing** of `x ∈ X` at position `i` of the placed window `p`. -/
def CleanLanding (object : FiniteObject.{u}) {n : Nat} (X : Finset object.Vertex)
    (p : Fin n → object.Vertex) (i : Fin n) (x : object.Vertex) (a : Nat) : Prop :=
  x ∈ X ∧ object.graph.Adj x (p i) ∧
    ∃ m, m + 1 = a ∧ ∃ α : Fin (m + 1) → object.Vertex,
      IsWindowPlacement object X α ∧ α (Fin.last m) = x ∧
      ∀ k (t : Fin n), Nat.dist t.1 i.1 + a + 1 ≤ n →
        object.graph.Adj (α k) (p t) → k = Fin.last m ∧ t = i

/-- **A long landing**: a clean `(n−2)`- or `(n−1)`-landing. -/
def LongLanding (object : FiniteObject.{u}) {n : Nat} (X : Finset object.Vertex)
    (p : Fin n → object.Vertex) (i : Fin n) (x : object.Vertex) : Prop :=
  ∃ a, (a + 2 = n ∨ a + 1 = n) ∧ CleanLanding object X p i x a

/-- Distinct pieces of a support are joined by no edge. -/
theorem pieceSupport_not_adj (object : FiniteObject.{u}) (S : Finset object.Vertex)
    {X Y : SupportComponents.Connected.Component object S} (ne : X ≠ Y) :
    ∀ u ∈ object.pieceSupport S X, ∀ v ∈ object.pieceSupport S Y, ¬ object.graph.Adj u v := by
  intro u hu v hv adj
  have hvS := object.pieceSupport_subset S Y hv
  have inX : v ∈ SupportComponents.Connected.vertices object S X :=
    SupportComponents.Connected.neighbor_mem_vertices object S X hu hvS adj
  exact Finset.disjoint_left.1 (SupportComponents.Connected.disjoint_members object S ne) inX hv

/-- The ambient surplus of the covered support is the sum over the members of the packing. -/
theorem sum_ambientSurplus_packing {order : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) (threshold : Nat) :
    ∑ P ∈ packing, object.ambientSurplus P threshold =
      object.ambientSurplus (FiniteObject.windowSupport packing) threshold := by
  letI : FinEnum object.Vertex := object.vertices
  unfold FiniteObject.ambientSurplus FiniteObject.windowSupport
  rw [Finset.sum_biUnion]
  · rfl
  · intro P hP Q hQ ne
    exact valid.2 P hP Q hQ ne

/-- **Clean landings with disjoint runs.**  Two clean landings of disjoint supports inside `R`
at positions `i`, `j`, with disjoint runs `[lx, lx+mx] ∋ i`, `[ly, ly+my] ∋ j` (landing
position an end) of complementary sizes `a + (mx+1) = n`, `b + (my+1) = n`, do not coexist. -/
theorem false_of_clean_runs {n : Nat} (positive : 0 < n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    {X Y : Finset object.Vertex} (hX : X ⊆ object.remainderSupport packing)
    (hY : Y ⊆ object.remainderSupport packing) (XY : Disjoint X Y)
    {i j : Fin n} {x y : object.Vertex} {a b : Nat}
    (cx : CleanLanding object X p i x a) (cy : CleanLanding object Y p j y b)
    (lx mx ly my : Nat) (bx : lx + mx < n) (byy : ly + my < n)
    (ei : i.1 = lx ∨ i.1 = lx + mx) (ej : j.1 = ly ∨ j.1 = ly + my)
    (sep : lx + mx < ly ∨ ly + my < lx)
    (sx : a + (mx + 1) = n) (sy : b + (my + 1) = n) : False := by
  obtain ⟨_, adjx, ma, hma, α, hα, αx, cleanx⟩ := cx
  obtain ⟨_, adjy, mb, hmb, β, hβ, βy, cleany⟩ := cy
  subst hma
  subst hmb
  refine false_of_two_arm_segments positive valid maximum hP hp (placement_mono hα hX)
    (placement_mono hβ hY)
    (fun k k' e => Finset.disjoint_left.1 XY (hα.2.1 k) (e ▸ hβ.2.1 k')) i j lx mx ly my
    bx byy ei ej sep (by omega) (by omega) (by rw [αx]; exact adjx) (by rw [βy]; exact adjy)
    ?_ ?_
  · intro k t h1 h2 adj
    exact cleanx k t (by unfold Nat.dist; omega) adj
  · intro k t h1 h2 adj
    exact cleany k t (by unfold Nat.dist; omega) adj

/-- **Pair rule for long landings.**  Two long landings of disjoint supports inside `R` on the
same placed window (`4 ≤ n`) land at the same position, or at `{0, 1}`, or at `{n−2, n−1}`. -/
theorem long_pair_rule {n : Nat} (four : 4 ≤ n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    {X Y : Finset object.Vertex} (hX : X ⊆ object.remainderSupport packing)
    (hY : Y ⊆ object.remainderSupport packing) (XY : Disjoint X Y)
    {i j : Fin n} {x y : object.Vertex}
    (lx : LongLanding object X p i x) (ly : LongLanding object Y p j y) :
    i = j ∨ i.1 + j.1 = 1 ∨ i.1 + j.1 + 3 = 2 * n := by
  have oriented : ∀ {X Y : Finset object.Vertex} {i j : Fin n} {x y : object.Vertex},
      X ⊆ object.remainderSupport packing → Y ⊆ object.remainderSupport packing →
      Disjoint X Y → LongLanding object X p i x → LongLanding object Y p j y → i.1 < j.1 →
      i.1 + j.1 = 1 ∨ i.1 + j.1 + 3 = 2 * n := by
    intro X Y i j x y hX hY XY lx ly lt
    obtain ⟨a, ha, cx⟩ := lx
    obtain ⟨b, hb, cy⟩ := ly
    by_contra none
    have hi := i.2
    have hj := j.2
    have runx : ∃ lx mx, lx + mx < n ∧ (i.1 = lx ∨ i.1 = lx + mx) ∧ a + (mx + 1) = n ∧
        (lx + mx ≤ i.1 ∨ (lx = 0 ∧ mx = 1 ∧ i.1 = 0)) := by
      by_cases h : n - a - 1 ≤ i.1
      · exact ⟨i.1 - (n - a - 1), n - a - 1, by omega, Or.inr (by omega), by omega,
          Or.inl (by omega)⟩
      · exact ⟨0, 1, by omega, Or.inl (by omega), by omega, Or.inr ⟨rfl, rfl, by omega⟩⟩
    have runy : ∃ ly my, ly + my < n ∧ (j.1 = ly ∨ j.1 = ly + my) ∧ b + (my + 1) = n ∧
        (j.1 ≤ ly ∨ (ly + 2 = n ∧ my = 1 ∧ j.1 + 1 = n)) := by
      by_cases h : j.1 + (n - b - 1) < n
      · exact ⟨j.1, n - b - 1, h, Or.inl rfl, by omega, Or.inl le_rfl⟩
      · exact ⟨n - 2, 1, by omega, Or.inr (by omega), by omega, Or.inr ⟨by omega, rfl, by omega⟩⟩
    obtain ⟨lx, mx, bx, ei, sx, px⟩ := runx
    obtain ⟨ly, my, byy, ej, sy, py⟩ := runy
    exact false_of_clean_runs (by omega) valid maximum hP hp hX hY XY cx cy lx mx ly my bx byy
      ei ej (by omega) sx sy
  rcases lt_trichotomy i.1 j.1 with h | h | h
  · exact Or.inr (oriented hX hY XY lx ly h)
  · exact Or.inl (Fin.ext h)
  · rcases oriented hY hX XY.symm ly lx h with e | e
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

/-- A suffix of an arm is an arm ending at the same vertex. -/
theorem exists_suffix {m : Nat} {S : Finset object.Vertex} {α : Fin (m + 1) → object.Vertex}
    (hα : IsWindowPlacement object S α) (a : Nat) (le : a ≤ m) :
    ∃ α' : Fin (a + 1) → object.Vertex, IsWindowPlacement object S α' ∧
      α' (Fin.last a) = α (Fin.last m) ∧
      ∀ k, ∃ k', α' k = α k' ∧ (k' = Fin.last m → k = Fin.last a) := by
  refine ⟨fun k => α ⟨k.1 + (m - a), by omega⟩, ⟨?_, fun k => hα.2.1 _, ?_⟩, ?_, ?_⟩
  · intro k k' e
    have := congrArg Fin.val (hα.1 e)
    exact Fin.ext (by simp at this; omega)
  · intro k k'
    rw [hα.2.2]
    simp only
    omega
  · apply congrArg α
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  · intro k
    refine ⟨⟨k.1 + (m - a), by omega⟩, rfl, fun e => ?_⟩
    have := congrArg Fin.val e
    simp only [Fin.val_last] at this
    exact Fin.ext (by simp only [Fin.val_last]; omega)

/-- **Two arms through one vertex.**  Two induced paths `α` (on `a + 1` vertices) and `β`
(on `b + 1` vertices), disjoint and joined by no edge, both avoiding `v`, whose only
neighbours of `v` are their last vertices, form with `v` an induced path on
`(a + 1 + 1) + (b + 1)` vertices. -/
theorem exists_inducesWindow_through {a b : Nat} {α : Fin (a + 1) → object.Vertex}
    {β : Fin (b + 1) → object.Vertex} {v : object.Vertex}
    (αinj : Function.Injective α)
    (αlaw : ∀ i j, object.graph.Adj (α i) (α j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (βinj : Function.Injective β)
    (βlaw : ∀ i j, object.graph.Adj (β i) (β j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (αβ : ∀ k k', α k ≠ β k') (noEdge : ∀ k k', ¬ object.graph.Adj (α k) (β k'))
    (vα : ∀ k, α k ≠ v) (vβ : ∀ k, β k ≠ v)
    (adjα : ∀ k, object.graph.Adj (α k) v ↔ k = Fin.last a)
    (adjβ : ∀ k, object.graph.Adj (β k) v ↔ k = Fin.last b) :
    ∃ W : Finset object.Vertex, object.InducesWindow ((a + 1 + 1) + (b + 1)) W ∧
      ∀ w ∈ W, (∃ k, α k = w) ∨ w = v ∨ ∃ k, β k = w := by
  let single : Fin 1 → object.Vertex := fun _ => v
  obtain ⟨inj₁, law₁⟩ := append_pathMap (σ := single) αinj αlaw
    (fun i j _ => Subsingleton.elim i j)
    (fun i j => by
      simp only [single, SimpleGraph.irrefl, false_iff]
      have := i.2; have := j.2; omega)
    (fun k _ => vα k)
    (fun k t => by
      simp only [single]
      rw [adjα k, Fin.ext_iff, Fin.val_last]
      have := t.2; have := k.2; omega)
  let σ : Fin (b + 1) → object.Vertex := fun t => β (Fin.rev t)
  have σinj : Function.Injective σ := βinj.comp Fin.rev_injective
  have σlaw : ∀ i j, object.graph.Adj (σ i) (σ j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
    intro i j
    simp only [σ]
    rw [βlaw, Fin.val_rev, Fin.val_rev]
    have := i.2; have := j.2; omega
  obtain ⟨inj, law⟩ := append_pathMap (α := Fin.append α single) (σ := σ) inj₁ law₁ σinj σlaw
    (fun k t => by
      induction k using Fin.addCases with
      | left k => simp only [Fin.append_left, σ]; exact αβ k _
      | right t0 => simp only [Fin.append_right, single, σ]; exact (vβ _).symm)
    (fun k t => by
      induction k using Fin.addCases with
      | left k =>
        simp only [Fin.append_left, σ, Fin.val_castAdd]
        have := k.2
        constructor
        · intro adj; exact absurd adj (noEdge k _)
        · intro h; omega
      | right t0 =>
        simp only [Fin.append_right, single, σ, Fin.val_natAdd]
        rw [object.graph.adj_comm, adjβ, Fin.ext_iff, Fin.val_rev, Fin.val_last]
        have := t0.2; have := t.2; omega)
  obtain ⟨W, hW, mem⟩ := exists_inducesWindow_of_pathMap inj law
  refine ⟨W, hW, fun w hw => ?_⟩
  obtain ⟨idx, rfl⟩ := (mem w).1 hw
  induction idx using Fin.addCases with
  | left k =>
    induction k using Fin.addCases with
    | left k => exact Or.inl ⟨k, by simp⟩
    | right t0 => exact Or.inr (Or.inl (by simp [single]))
  | right t => exact Or.inr (Or.inr ⟨Fin.rev t, by simp [σ]⟩)

/-- **Triple rule.**  Two clean landings of disjoint, mutually non-adjacent supports `X`, `Y`
inside `R` at the same position `p e`, with `a + b ≥ n − 1`, and a clean landing of a third
disjoint support `Z` at `p k` with a run `[l, l+m]` of complementary size (`k` an end) that
avoids `e`, do not coexist. -/
theorem false_of_clean_triple {n : Nat} (three : 3 ≤ n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    {X Y Z : Finset object.Vertex} (hX : X ⊆ object.remainderSupport packing)
    (hY : Y ⊆ object.remainderSupport packing) (hZ : Z ⊆ object.remainderSupport packing)
    (XY : Disjoint X Y) (XZ : Disjoint X Z) (YZ : Disjoint Y Z)
    (noEdge : ∀ u ∈ X, ∀ v ∈ Y, ¬ object.graph.Adj u v)
    {e k : Fin n} {x y z : object.Vertex} {a b c : Nat}
    (cx : CleanLanding object X p e x a) (cy : CleanLanding object Y p e y b)
    (ax : a + 1 ≤ n) (bx : b + 1 ≤ n) (sum : n ≤ a + b + 1)
    (cz : CleanLanding object Z p k z c) (l m : Nat) (bz : l + m < n)
    (ek : k.1 = l ∨ k.1 = l + m) (sz : c + (m + 1) = n) (avoid : e.1 < l ∨ l + m < e.1) :
    False := by
  have positive : 0 < n := by omega
  have outR : ∀ v, v ∈ object.remainderSupport packing → v ∈ P → False := fun v hR hv =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport hR
      (FiniteObject.mem_windowSupport hP hv)
  have pP : ∀ t, p t ∈ P := hp.2.1
  obtain ⟨_, adjx, ma, hma, α, hα, αx, cleanx⟩ := cx
  obtain ⟨_, adjy, mb, hmb, β, hβ, βy, cleany⟩ := cy
  obtain ⟨_, adjz, mc, hmc, γ, hγ, γz, cleanz⟩ := cz
  subst hma
  subst hmb
  subst hmc
  obtain ⟨α', hα', αlast, αback⟩ := exists_suffix hα (min ma (n - 3)) (min_le_left _ _)
  obtain ⟨β', hβ', βlast, βback⟩ := exists_suffix hβ (n - 3 - min ma (n - 3)) (by omega)
  have αX : ∀ k, α' k ∈ X := hα'.2.1
  have βY : ∀ k, β' k ∈ Y := hβ'.2.1
  obtain ⟨W₁, hW₁, mem₁⟩ := exists_inducesWindow_through (v := p e) hα'.1 hα'.2.2 hβ'.1 hβ'.2.2
    (fun k k' h => Finset.disjoint_left.1 XY (αX k) (h ▸ βY k'))
    (fun k k' => noEdge _ (αX k) _ (βY k'))
    (fun k h => outR _ (hX (αX k)) (h ▸ pP e))
    (fun k h => outR _ (hY (βY k)) (h ▸ pP e))
    (fun k => by
      constructor
      · intro adj
        obtain ⟨k', ek', back⟩ := αback k
        rw [ek'] at adj
        exact back (cleanx k' e (by simp [Nat.dist]; omega) adj).1
      · rintro rfl
        rw [αlast, αx]
        exact adjx)
    (fun k => by
      constructor
      · intro adj
        obtain ⟨k', ek', back⟩ := βback k
        rw [ek'] at adj
        exact back (cleany k' e (by simp [Nat.dist]; omega) adj).1
      · rintro rfl
        rw [βlast, βy]
        exact adjy)
  obtain ⟨W₂, hW₂, mem₂⟩ := exists_inducesWindow_arm_segment hp (placement_mono hγ hZ) l m bz k
    ek (by rw [γz]; exact adjz)
    (fun k' t h1 h2 adj => cleanz k' t (by unfold Nat.dist; omega) adj)
    (fun k' t _ _ h => outR _ (hZ (hγ.2.1 k')) (h ▸ pP t))
  have size₁ : (min ma (n - 3) + 1 + 1) + (n - 3 - min ma (n - 3) + 1) = n := by omega
  rw [size₁] at hW₁
  rw [show (mc + 1) + (m + 1) = n by omega] at hW₂
  refine false_of_two_windows_in_member_union_remainder positive valid maximum hP hW₁ hW₂
    ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro w h₁ h₂
    rcases (mem₂ w).1 h₂ with ⟨k₂, rfl⟩ | ⟨t, t1, t2, rfl⟩
    · rcases mem₁ _ h₁ with ⟨k₁, e₁⟩ | e₁ | ⟨k₁, e₁⟩
      · exact Finset.disjoint_left.1 XZ (αX k₁) (e₁ ▸ hγ.2.1 k₂)
      · exact outR _ (hZ (hγ.2.1 k₂)) (e₁ ▸ pP e)
      · exact Finset.disjoint_left.1 YZ (βY k₁) (e₁ ▸ hγ.2.1 k₂)
    · rcases mem₁ _ h₁ with ⟨k₁, e₁⟩ | e₁ | ⟨k₁, e₁⟩
      · exact outR _ (hX (αX k₁)) (e₁ ▸ pP t)
      · have := congrArg Fin.val (hp.1 e₁)
        omega
      · exact outR _ (hY (βY k₁)) (e₁ ▸ pP t)
  · intro w hw
    rcases mem₁ w hw with ⟨k₁, rfl⟩ | rfl | ⟨k₁, rfl⟩
    · exact Or.inl (hX (αX k₁))
    · exact Or.inr (pP e)
    · exact Or.inl (hY (βY k₁))
  · intro w hw
    rcases (mem₂ w).1 hw with ⟨k₂, rfl⟩ | ⟨t, _, _, rfl⟩
    · exact Or.inl (hZ (hγ.2.1 k₂))
    · exact Or.inr (pP t)

/-- **Triple rule at an end, for long landings.**  Two long landings of disjoint, mutually
non-adjacent supports at an end position `e` of the window and a long landing of a third
disjoint support at the neighbouring position `e'` do not coexist (`4 ≤ n`). -/
theorem false_of_long_triple {n : Nat} (four : 4 ≤ n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    {X Y Z : Finset object.Vertex} (hX : X ⊆ object.remainderSupport packing)
    (hY : Y ⊆ object.remainderSupport packing) (hZ : Z ⊆ object.remainderSupport packing)
    (XY : Disjoint X Y) (XZ : Disjoint X Z) (YZ : Disjoint Y Z)
    (noEdge : ∀ u ∈ X, ∀ v ∈ Y, ¬ object.graph.Adj u v)
    {e e' : Fin n} (ends : (e.1 = 0 ∧ e'.1 = 1) ∨ (e.1 + 1 = n ∧ e'.1 + 2 = n))
    {x y z : object.Vertex}
    (lx : LongLanding object X p e x) (ly : LongLanding object Y p e y)
    (lz : LongLanding object Z p e' z) : False := by
  obtain ⟨a, ha, cx⟩ := lx
  obtain ⟨b, hb, cy⟩ := ly
  obtain ⟨c, hc, cz⟩ := lz
  have run : ∃ l m, l + m < n ∧ (e'.1 = l ∨ e'.1 = l + m) ∧ c + (m + 1) = n ∧
      (e.1 < l ∨ l + m < e.1) := by
    by_cases hc1 : c + 1 = n
    · exact ⟨e'.1, 0, by omega, Or.inl rfl, by omega, by omega⟩
    · rcases ends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact ⟨1, 1, by omega, Or.inl (by omega), by omega, Or.inl (by omega)⟩
      · exact ⟨n - 3, 1, by omega, Or.inr (by omega), by omega, Or.inr (by omega)⟩
  obtain ⟨l, m, bz, ek, sz, avoid⟩ := run
  exact false_of_clean_triple (by omega) valid maximum hP hp hX hY hZ XY XZ YZ noEdge cx cy
    (by omega) (by omega) (by omega) cz l m bz ek sz avoid

/-- **The per-window cap on long landings.**  Over a family of pairwise disjoint, pairwise
non-adjacent supports inside `R`, the supports with a long landing on the placed window
`(P, p)` number at most `(δ − 1) + Σ_{v ∈ P} (d(v) − δ)` (`4 ≤ n`).

A single landing position `i` carries at most `|N(p i) \ P| ≤ d(p i) − 1` supports (distinct
supports land at distinct outside neighbours).  Two positions occupied by distinct supports
form `{0, 1}` or `{n−2, n−1}` (`long_pair_rule`); there the end carries one support
(`false_of_long_triple`) and the interior neighbour at most `d − 2`. -/
theorem long_landing_cap {ι : Type*} {n : Nat} (four : 4 ≤ n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    (threshold : Nat) (pieces : Finset ι) (supp : ι → Finset object.Vertex)
    (inR : ∀ X ∈ pieces, supp X ⊆ object.remainderSupport packing)
    (disj : ∀ X ∈ pieces, ∀ Y ∈ pieces, X ≠ Y → Disjoint (supp X) (supp Y))
    (noEdge : ∀ X ∈ pieces, ∀ Y ∈ pieces, X ≠ Y →
      ∀ u ∈ supp X, ∀ v ∈ supp Y, ¬ object.graph.Adj u v)
    [DecidablePred fun X => ∃ i x, LongLanding object (supp X) p i x] :
    (pieces.filter fun X => ∃ i x, LongLanding object (supp X) p i x).card ≤
      (threshold - 1) + object.ambientSurplus P threshold := by
  classical
  have positive : 0 < n := by omega
  set L := pieces.filter fun X => ∃ i x, LongLanding object (supp X) p i x with hL
  have memL : ∀ X ∈ L, X ∈ pieces := fun X hX => (Finset.mem_filter.1 hX).1
  let f : ι → Fin n := fun X =>
    if h : ∃ i x, LongLanding object (supp X) p i x then Classical.choose h else ⟨0, positive⟩
  let g : ι → object.Vertex := fun X =>
    if h : ∃ i x, LongLanding object (supp X) p i x then
      Classical.choose (Classical.choose_spec h) else p ⟨0, positive⟩
  have fg : ∀ X ∈ L, LongLanding object (supp X) p (f X) (g X) := by
    intro X hX
    have h := (Finset.mem_filter.1 hX).2
    simp only [f, g, dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec h)
  have gmem : ∀ X ∈ L, g X ∈ supp X := by
    intro X hX
    obtain ⟨_, _, hx, _⟩ := fg X hX
    exact hx
  have outP : ∀ v ∈ object.remainderSupport packing, v ∉ P := fun v hR hv =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport hR
      (FiniteObject.mem_windowSupport hP hv)
  have card : P.card = n := (valid.1 P hP).2
  -- One position carries at most its outside neighbours.
  have perPos : ∀ i : Fin n,
      (L.filter fun X => f X = i).card ≤ (object.externalNeighbours P (p i)).card := by
    intro i
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · intro X hX
      have hX' := Finset.mem_filter.1 hX
      obtain ⟨_, _, hx, adj, _⟩ := fg X hX'.1
      rw [hX'.2] at adj
      rw [Finset.mem_coe]
      simp only [FiniteObject.externalNeighbours, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨adj.symm, outP _ (inR X (memL X hX'.1) hx)⟩
    · intro X hX Y hY e
      by_contra ne
      have hX' := Finset.mem_filter.1 hX
      have hY' := Finset.mem_filter.1 hY
      exact Finset.disjoint_left.1 (disj X (memL X hX'.1) Y (memL Y hY'.1) ne)
        (gmem X hX'.1) (e ▸ gmem Y hY'.1)
  -- The stub identity: outside neighbours and path neighbours make up the degree.
  have stub : ∀ i : Fin n, (object.externalNeighbours P (p i)).card +
      (Finset.univ.filter fun j : Fin n => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card =
        object.degree (p i) := fun i => placement_stub_identity hp card i
  have pathOne : ∀ i : Fin n,
      1 ≤ (Finset.univ.filter fun j : Fin n => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card := by
    intro i
    apply Finset.card_pos.2
    by_cases h : i.1 + 1 < n
    · exact ⟨⟨i.1 + 1, h⟩, by simp⟩
    · exact ⟨⟨i.1 - 1, by omega⟩, by simp; omega⟩
  have pathTwo : ∀ i : Fin n, 0 < i.1 → i.1 + 1 < n →
      2 ≤ (Finset.univ.filter fun j : Fin n => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1).card := by
    intro i h0 h1
    have sub : ({⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, h1⟩} : Finset (Fin n)) ⊆
        Finset.univ.filter fun j : Fin n => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp <;> omega
    have two : ({⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, h1⟩} : Finset (Fin n)).card = 2 := by
      rw [Finset.card_pair]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    exact two ▸ Finset.card_le_card sub
  have single : ∀ i : Fin n, object.degree (p i) - threshold ≤
      object.ambientSurplus P threshold := by
    intro i
    unfold FiniteObject.ambientSurplus
    exact Finset.single_le_sum (f := fun v => object.degree v - threshold)
      (fun v _ => Nat.zero_le _) (hp.2.1 i)
  -- The pair rule on the chosen positions.
  have pair : ∀ X ∈ L, ∀ Y ∈ L, f X ≠ f Y →
      (f X).1 + (f Y).1 = 1 ∨ (f X).1 + (f Y).1 + 3 = 2 * n := by
    intro X hX Y hY ne
    have XY : X ≠ Y := fun e => ne (e ▸ rfl)
    rcases long_pair_rule four valid maximum hP hp (inR X (memL X hX)) (inR Y (memL Y hY))
      (disj X (memL X hX) Y (memL Y hY) XY) (fg X hX) (fg Y hY) with h | h
    · exact absurd h ne
    · exact h
  by_cases same : ∀ X ∈ L, ∀ Y ∈ L, f X = f Y
  · rcases L.eq_empty_or_nonempty with h | ⟨X₀, hX₀⟩
    · rw [h, Finset.card_empty]
      exact Nat.zero_le _
    · have all : L.filter (fun X => f X = f X₀) = L :=
        Finset.filter_true_of_mem fun X hX => same X hX X₀ hX₀
      have c₁ := perPos (f X₀)
      rw [all] at c₁
      have := stub (f X₀)
      have := pathOne (f X₀)
      have := single (f X₀)
      omega
  · obtain ⟨X₀, hX₀, Y₀, hY₀, ne₀⟩ : ∃ X ∈ L, ∃ Y ∈ L, f X ≠ f Y := by
      by_contra none
      exact same fun X hX Y hY => by_contra fun h => none ⟨X, hX, Y, hY, h⟩
    -- The end `e` and its neighbour `e'` carry every landing.
    have finish : ∀ e e' : Fin n, ((e.1 = 0 ∧ e'.1 = 1) ∨ (e.1 + 1 = n ∧ e'.1 + 2 = n)) →
        (∀ Z ∈ L, f Z = e ∨ f Z = e') → (∃ Z ∈ L, f Z = e') →
        L.card ≤ (threshold - 1) + object.ambientSurplus P threshold := by
      intro e e' ends cover occupied
      have ee' : e ≠ e' := fun h => by
        have := congrArg Fin.val h
        omega
      have split := Finset.card_filter_add_card_filter_not
        (s := L) (fun X => f X = e)
      have atEnd : (L.filter fun X => f X = e).card ≤ 1 := by
        by_contra many
        have many' : 1 < (L.filter fun X => f X = e).card := by omega
        obtain ⟨X, hX, Y, hY, XY⟩ := Finset.one_lt_card.1 many'
        obtain ⟨Z, hZ, fZ⟩ := occupied
        have hX' := Finset.mem_filter.1 hX
        have hY' := Finset.mem_filter.1 hY
        have XZ : X ≠ Z := fun h => ee' (by rw [← hX'.2, ← fZ, h])
        have YZ : Y ≠ Z := fun h => ee' (by rw [← hY'.2, ← fZ, h])
        have lX := fg X hX'.1
        have lY := fg Y hY'.1
        have lZ := fg Z hZ
        rw [hX'.2] at lX
        rw [hY'.2] at lY
        rw [fZ] at lZ
        exact false_of_long_triple four valid maximum hP hp (inR X (memL X hX'.1))
          (inR Y (memL Y hY'.1)) (inR Z (memL Z hZ))
          (disj X (memL X hX'.1) Y (memL Y hY'.1) XY) (disj X (memL X hX'.1) Z (memL Z hZ) XZ)
          (disj Y (memL Y hY'.1) Z (memL Z hZ) YZ)
          (noEdge X (memL X hX'.1) Y (memL Y hY'.1) XY) ends lX lY lZ
      have atNeighbour : (L.filter fun X => ¬ f X = e).card ≤
          (L.filter fun X => f X = e').card := by
        apply Finset.card_le_card
        intro X hX
        have hX' := Finset.mem_filter.1 hX
        refine Finset.mem_filter.2 ⟨hX'.1, ?_⟩
        rcases cover X hX'.1 with h | h
        · exact absurd h hX'.2
        · exact h
      have nonempty : 1 ≤ (L.filter fun X => ¬ f X = e).card := by
        obtain ⟨Z, hZ, fZ⟩ := occupied
        apply Finset.card_pos.2
        exact ⟨Z, Finset.mem_filter.2 ⟨hZ, fun h => ee' (h.symm.trans fZ)⟩⟩
      have c₁ := perPos e'
      have := stub e'
      have := pathTwo e' (by omega) (by omega)
      have := single e'
      omega
    have h₀ := pair X₀ hX₀ Y₀ hY₀ ne₀
    have v₀ := (f X₀).2
    have v₁ := (f Y₀).2
    have ne₀' : (f X₀).1 ≠ (f Y₀).1 := fun h => ne₀ (Fin.ext h)
    have coverOf : ∀ Z ∈ L, (f Z).1 + (f X₀).1 = 1 ∨ (f Z).1 + (f X₀).1 + 3 = 2 * n ∨
        f Z = f X₀ := by
      intro Z hZ
      by_cases h : f Z = f X₀
      · exact Or.inr (Or.inr h)
      · rcases pair Z hZ X₀ hX₀ h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    rcases h₀ with h₀ | h₀
    · refine finish ⟨0, by omega⟩ ⟨1, by omega⟩ (Or.inl ⟨rfl, rfl⟩) ?_ ?_
      · intro Z hZ
        have := (f Z).2
        rcases coverOf Z hZ with h | h | h
        · by_cases hz : (f Z).1 = 0
          · exact Or.inl (Fin.ext hz)
          · exact Or.inr (Fin.ext (by simp; omega))
        · omega
        · rw [h]
          by_cases hz : (f X₀).1 = 0
          · exact Or.inl (Fin.ext hz)
          · exact Or.inr (Fin.ext (by simp; omega))
      · by_cases hz : (f X₀).1 = 1
        · exact ⟨X₀, hX₀, Fin.ext hz⟩
        · exact ⟨Y₀, hY₀, Fin.ext (by simp; omega)⟩
    · refine finish ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ (Or.inr ⟨by simp; omega, by simp; omega⟩)
        ?_ ?_
      · intro Z hZ
        have := (f Z).2
        rcases coverOf Z hZ with h | h | h
        · omega
        · by_cases hz : (f Z).1 = n - 1
          · exact Or.inl (Fin.ext hz)
          · exact Or.inr (Fin.ext (by simp; omega))
        · rw [h]
          by_cases hz : (f X₀).1 = n - 1
          · exact Or.inl (Fin.ext hz)
          · exact Or.inr (Fin.ext (by simp; omega))
      · by_cases hz : (f X₀).1 = n - 2
        · exact ⟨X₀, hX₀, Fin.ext hz⟩
        · exact ⟨Y₀, hY₀, Fin.ext (by simp; omega)⟩

end Hypostructure.Graph.PackingExchange
