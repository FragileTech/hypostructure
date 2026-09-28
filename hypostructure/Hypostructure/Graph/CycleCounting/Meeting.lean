import Hypostructure.Graph.CycleCounting.Cycles

/-!
# Stars, meetings and thetas at a vertex

Two paths `x → y`, `x → z` of `G − h` to distinct neighbours `y, z` of `h`
close a cycle through `h` (the star when they meet only at `x`; in general at
their first meeting vertex).  The dyadic arithmetic that constrains these
lengths when `G` has no cycle of length `2^k` (`k ≥ 2`), and the theta parity.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Star lemma.** Two paths `x → y`, `x → z` avoiding `h`, meeting only at `x`, with
`y, z ∈ N(h)` distinct, close a cycle `h y ⋯ x ⋯ z h` of length `|p| + |q| + 2`. -/
theorem star_cycle {h x y z : V} (ay : G.Adj h y) (az : G.Adj h z) (yz : y ≠ z)
    (p : G.Walk x y) (q : G.Walk x z) (pp : p.IsPath) (qp : q.IsPath)
    (hp : h ∉ p.support) (hq : h ∉ q.support)
    (disj : ∀ v ∈ p.support, v ∈ q.support → v = x) :
    ∃ c : G.Walk h h, c.IsCycle ∧ c.length = p.length + q.length + 2 := by
  let w := p.reverse.append q
  have wp : w.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append]
    have qs := q.cons_tail_support.symm
    have qn : q.support.Nodup := qp.support_nodup
    rw [qs, List.nodup_cons] at qn
    refine ⟨(pp.reverse).support_nodup, qn.2, ?_⟩
    intro a ha b hb e
    subst e
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ha
    have := disj a ha (by rw [qs]; exact List.mem_cons_of_mem _ hb)
    subst this
    exact qn.1 hb
  have hw : h ∉ w.support := by
    intro m
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at m
    rcases m with m | m
    · exact hp m
    · exact hq m
  obtain ⟨c, cc, cl, -⟩ := pair_cycle yz ay az w wp hw
  refine ⟨c, cc, ?_⟩
  rw [cl, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]

/-- **Same-`j` star is dyadic.** If the two forced paths from `x` have the same length
`2^j − 1`, the star cycle has length `2^(j+1)`. -/
theorem star_cycle_dyadic {h x y z : V} {j : ℕ} (hj : 1 ≤ j) (ay : G.Adj h y) (az : G.Adj h z)
    (yz : y ≠ z) (p : G.Walk x y) (q : G.Walk x z) (pp : p.IsPath) (qp : q.IsPath)
    (hp : h ∉ p.support) (hq : h ∉ q.support)
    (disj : ∀ v ∈ p.support, v ∈ q.support → v = x)
    (lp : p.length + 1 = 2 ^ j) (lq : q.length + 1 = 2 ^ j) :
    ∃ c : G.Walk h h, c.IsCycle ∧ c.length = 2 ^ (j + 1) := by
  obtain ⟨c, cc, cl⟩ := star_cycle ay az yz p q pp qp hp hq disj
  exact ⟨c, cc, by rw [cl, pow_succ]; omega⟩

/-- Distinct-`j` star: `(2^a − 1) + (2^b − 1) + 2 = 2^a + 2^b`, a power of two iff `a = b`
(`a, b ≥ 1`). -/
theorem two_pow_add_two_pow_ne {a b c : ℕ} (ab : a < b) : 2 ^ a + 2 ^ b ≠ 2 ^ c := by
  intro e
  have hb : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) ab
  have pa : 0 < 2 ^ a := by positivity
  have c1 : 2 ^ b < 2 ^ c := by omega
  have c2 : 2 ^ c < 2 ^ (b + 1) := by
    calc 2 ^ c = 2 ^ a + 2 ^ b := e.symm
      _ < 2 ^ b + 2 ^ b := by omega
      _ = 2 ^ (b + 1) := by ring
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 c1
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 c2
  omega

/-- **Theta parity.** The three cycles of a theta graph with branch lengths `α, β, γ` have
lengths summing to `2(α+β+γ)`; they cannot all lie in `{2^j + 1 : j ≥ 1}`. -/
theorem theta_not_all_S {α β γ a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : α + β = 2 ^ a + 1) (h2 : α + γ = 2 ^ b + 1) (h3 : β + γ = 2 ^ c + 1) : False := by
  obtain ⟨a, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ t, b = t + 1 := ⟨b - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ t, c = t + 1 := ⟨c - 1, by omega⟩
  rw [pow_succ] at h1 h2 h3
  omega

/-- **Theta third length.** Two `S`-cycles of a theta sharing the branch `α` force the third
cycle to have length `β + γ = 2^a + 2^b + 2 − 2α` (even). -/
theorem theta_third {α β γ a b : ℕ} (h1 : α + β = 2 ^ a + 1) (h2 : α + γ = 2 ^ b + 1) :
    β + γ + 2 * α = 2 ^ a + 2 ^ b + 2 := by omega


end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Same-`j` families from one vertex: the general meet lemma -/

/-- First hit of a set along a walk. -/
theorem first_hit (S : Finset V) : ∀ {z x : V} (w : G.Walk z x), x ∈ S →
    ∃ t ∈ S, ∃ (a : G.Walk z t) (b : G.Walk t x), w = a.append b ∧
      ∀ v ∈ a.support, v ∈ S → v = t
  | _, _, .nil, hx => ⟨_, hx, .nil, .nil, rfl, by simp⟩
  | z, _, .cons hadj w', hx => by
    by_cases hz : z ∈ S
    · exact ⟨z, hz, .nil, .cons hadj w', rfl, by simp⟩
    · obtain ⟨t, ht, a, b, e, ha⟩ := first_hit S w' hx
      refine ⟨t, ht, .cons hadj a, b, by rw [e, SimpleGraph.Walk.cons_append], ?_⟩
      intro v hv hvS
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact absurd hvS hz
      · exact ha v hv hvS

/-- **Meet lemma.** Paths `P : x → y`, `Q : x → z` avoiding `h` (`y ≠ z ∈ N(h)`) meet at a
vertex `t` reached from `x` by `P₁` along `P` and `Q₁` along `Q`, and `G` has a cycle through
`h` of length `|P| + |Q| + 2 − |P₁| − |Q₁|`. (`t = x`, `|P₁| = |Q₁| = 0`, is the star.) -/
theorem meet_cycle {h x y z : V} (ay : G.Adj h y) (az : G.Adj h z) (yz : y ≠ z)
    (P : G.Walk x y) (Q : G.Walk x z) (pp : P.IsPath) (qp : Q.IsPath)
    (hp : h ∉ P.support) (hq : h ∉ Q.support) :
    ∃ t, ∃ P₁ Q₁ : G.Walk x t, P₁.length ≤ P.length ∧ Q₁.length ≤ Q.length ∧
      ∃ c : G.Walk h h, c.IsCycle ∧ c.length + P₁.length + Q₁.length = P.length + Q.length + 2 := by
  obtain ⟨t, ht, a, b, e, ha⟩ := first_hit P.support.toFinset Q.reverse
    (List.mem_toFinset.2 P.start_mem_support)
  have htP : t ∈ P.support := List.mem_toFinset.1 ht
  have qrp : (a.append b).IsPath := e ▸ qp.reverse
  have ap : a.IsPath := qrp.of_append_left
  have asub : ∀ v ∈ a.support, v ∈ Q.support := by
    intro v hv
    have : v ∈ Q.reverse.support := by
      rw [e, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hv
    simpa using this
  let d := P.dropUntil t htP
  have dsub : ∀ v ∈ d.support, v ∈ P.support := fun v hv =>
    P.support_dropUntil_subset_support htP hv
  obtain ⟨c, cc, cl⟩ := star_cycle ay az yz d a.reverse (pp.dropUntil htP) ap.reverse
    (fun m => hp (dsub _ m)) (by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
                                 exact fun m => hq (asub _ m))
    (by
      intro v hv hv'
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv'
      exact ha v hv' (List.mem_toFinset.2 (dsub v hv)))
  have lP := congrArg SimpleGraph.Walk.length (P.take_spec htP)
  have lQ := congrArg SimpleGraph.Walk.length e
  rw [SimpleGraph.Walk.length_append] at lP lQ
  rw [SimpleGraph.Walk.length_reverse] at lQ
  refine ⟨t, P.takeUntil t htP, b.reverse, by omega, by rw [SimpleGraph.Walk.length_reverse]; omega,
    c, cc, ?_⟩
  have hdl : d.length = (P.dropUntil t htP).length := rfl
  rw [cl, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_reverse]
  omega

/-- **Meet constraint for a same-`j` pair.** If `|P| + 1 = |Q| + 1 = 2^j` and `G` has no
cycle of length `2^k` (`k ≥ 2`), the meeting depths satisfy `|P₁| + |Q₁| + 2^k ≠ 2^(j+1)` for
every `k ≥ 2`; `|P₁| + |Q₁| = 0` (a star) is excluded. -/
theorem meet_constraint {h x y z : V} {j : ℕ} (ay : G.Adj h y) (az : G.Adj h z) (yz : y ≠ z)
    (P : G.Walk x y) (Q : G.Walk x z) (pp : P.IsPath) (qp : Q.IsPath)
    (hp : h ∉ P.support) (hq : h ∉ Q.support)
    (lp : P.length + 1 = 2 ^ j) (lq : Q.length + 1 = 2 ^ j)
    (noDyadic : ∀ c : G.Walk h h, c.IsCycle → ∀ k, 2 ≤ k → c.length ≠ 2 ^ k) :
    ∃ t, ∃ P₁ Q₁ : G.Walk x t, ∀ k, 2 ≤ k → P₁.length + Q₁.length + 2 ^ k ≠ 2 ^ (j + 1) := by
  obtain ⟨t, P₁, Q₁, l1, l2, c, cc, cl⟩ := meet_cycle ay az yz P Q pp qp hp hq
  refine ⟨t, P₁, Q₁, fun k hk e => noDyadic c cc k hk ?_⟩
  rw [pow_succ] at e
  omega

/-- **Every odd meeting sum is allowed**: the forbidden sums `2^(j+1) − 2^k` (`k ≥ 1`) are
all even. -/
theorem odd_meet_allowed {s j k : ℕ} (hs : Odd s) (hk : 1 ≤ k) : s + 2 ^ k ≠ 2 ^ (j + 1) := by
  obtain ⟨k, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ := hs
  rw [pow_succ, pow_succ]
  omega

end Hypostructure.Graph.CycleCounting
