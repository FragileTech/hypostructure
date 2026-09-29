import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Uncrossing two paths at their first and last common vertex

Two paths `P : a → b` and `Q : c → d` of a simple graph that share a vertex.
Along `P` let `x` be the first vertex on `Q` and `y` the last.  Then

* `P = P₁ ++ P₂` with `P₁` meeting `Q` only at `x`, and `P = P₃ ++ P₄` with `P₄`
  meeting `Q` only at `y`;
* `Q` splits at `x` as `Q₁ ++ Q₂` and at `y` as `Q₃ ++ Q₄`;
* the rerouted walks `P₁ ++ Q₂ : a → d` (through `x`) and `Q₃ ++ P₄ : c → b`
  (through `y`) are paths, with the exact lengths
  `|P₁| + |Q₂|` and `|Q₃| + |P₄|`.

The decomposition lemmas need no path hypothesis; the rerouted walks are paths
because the first-hit and last-hit segments meet `Q` only at the junction.
-/

namespace Hypostructure.Graph.PathUncrossing

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **First hit.**  A walk that meets `S` splits at its first vertex in `S`: the
initial segment meets `S` only at the junction. -/
theorem exists_first_hit (S : Set V) :
    ∀ {a b : V} (p : G.Walk a b), (∃ x ∈ p.support, x ∈ S) →
      ∃ (x : V) (p₁ : G.Walk a x) (p₂ : G.Walk x b), p = p₁.append p₂ ∧ x ∈ S ∧
        ∀ v ∈ p₁.support, v ∈ S → v = x := by
  intro a b p
  induction p with
  | @nil u =>
      rintro ⟨x, hx, hS⟩
      have hxu : x = u := by simpa using hx
      subst hxu
      exact ⟨x, .nil, .nil, rfl, hS, fun v hv _ => by simpa using hv⟩
  | @cons a c b h q ih =>
      rintro ⟨x, hx, hS⟩
      by_cases ha : a ∈ S
      · exact ⟨a, .nil, .cons h q, rfl, ha, fun v hv _ => by simpa using hv⟩
      · have hxq : x ∈ q.support := by
          rcases List.mem_cons.mp (by simpa using hx) with rfl | hq
          · exact absurd hS ha
          · exact hq
        obtain ⟨x', q₁, q₂, hq, hx', hfirst⟩ := ih ⟨x, hxq, hS⟩
        refine ⟨x', .cons h q₁, q₂, by rw [hq]; rfl, hx', ?_⟩
        intro v hv hvS
        rcases List.mem_cons.mp (by simpa using hv) with rfl | hv'
        · exact absurd hvS ha
        · exact hfirst v hv' hvS

/-- **Last hit.**  A walk that meets `S` splits at its last vertex in `S`: the
final segment meets `S` only at the junction. -/
theorem exists_last_hit (S : Set V) :
    ∀ {a b : V} (p : G.Walk a b), (∃ x ∈ p.support, x ∈ S) →
      ∃ (x : V) (p₁ : G.Walk a x) (p₂ : G.Walk x b), p = p₁.append p₂ ∧ x ∈ S ∧
        ∀ v ∈ p₂.support, v ∈ S → v = x := by
  intro a b p
  induction p with
  | @nil u =>
      rintro ⟨x, hx, hS⟩
      have hxu : x = u := by simpa using hx
      subst hxu
      exact ⟨x, .nil, .nil, rfl, hS, fun v hv _ => by simpa using hv⟩
  | @cons a c b h q ih =>
      rintro ⟨x, hx, hS⟩
      by_cases hq : ∃ z ∈ q.support, z ∈ S
      · obtain ⟨x', q₁, q₂, hqe, hx', hlast⟩ := ih hq
        exact ⟨x', .cons h q₁, q₂, by rw [hqe]; rfl, hx', hlast⟩
      · have haS : a ∈ S := by
          rcases List.mem_cons.mp (by simpa using hx) with rfl | hxq
          · exact hS
          · exact absurd ⟨x, hxq, hS⟩ hq
        refine ⟨a, .nil, .cons h q, rfl, haS, fun v hv hvS => ?_⟩
        rcases List.mem_cons.mp (by simpa using hv) with rfl | hv'
        · rfl
        · exact absurd ⟨v, hv', hvS⟩ hq

/-- Two paths meeting only at their junction concatenate to a path. -/
theorem isPath_append_of_inter {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath) (h : ∀ z ∈ p.support, z ∈ q.support → z = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def] at *
  rw [Walk.support_append, List.nodup_append]
  have hcons : v :: q.support.tail = q.support := Walk.cons_tail_support q
  rw [← hcons] at hq
  refine ⟨hp, hq.of_cons, ?_⟩
  intro z hz z' hz' hzz
  subst hzz
  have hzq : z ∈ q.support := by
    rw [← hcons]; exact List.mem_cons_of_mem _ hz'
  have := h z hz hzq
  subst this
  exact (List.nodup_cons.mp hq).1 hz'

/-- **The uncrossing of two paths** at the first and last vertex of `P` on `Q`. -/
theorem exists_uncrossing {a b c d : V} (P : G.Walk a b) (Q : G.Walk c d)
    (hP : P.IsPath) (hQ : Q.IsPath) (hit : ∃ v ∈ P.support, v ∈ Q.support) :
    ∃ (x y : V) (P₁ : G.Walk a x) (P₂ : G.Walk x b) (P₃ : G.Walk a y) (P₄ : G.Walk y b)
      (Q₁ : G.Walk c x) (Q₂ : G.Walk x d) (Q₃ : G.Walk c y) (Q₄ : G.Walk y d),
      P = P₁.append P₂ ∧ P = P₃.append P₄ ∧ Q = Q₁.append Q₂ ∧ Q = Q₃.append Q₄ ∧
      x ∈ Q.support ∧ y ∈ Q.support ∧
      (∀ v ∈ P₁.support, v ∈ Q.support → v = x) ∧
      (∀ v ∈ P₄.support, v ∈ Q.support → v = y) ∧
      (P₁.append Q₂).IsPath ∧ (Q₃.append P₄).IsPath := by
  classical
  obtain ⟨x, P₁, P₂, hPx, hxS, hfirst⟩ := exists_first_hit (G := G) {v | v ∈ Q.support} P hit
  obtain ⟨y, P₃, P₄, hPy, hyS, hlast⟩ := exists_last_hit (G := G) {v | v ∈ Q.support} P hit
  have hxS' : x ∈ Q.support := hxS
  have hyS' : y ∈ Q.support := hyS
  refine ⟨x, y, P₁, P₂, P₃, P₄, Q.takeUntil x hxS', Q.dropUntil x hxS',
    Q.takeUntil y hyS', Q.dropUntil y hyS', hPx, hPy, (Q.take_spec hxS').symm,
    (Q.take_spec hyS').symm, hxS', hyS', hfirst, hlast, ?_, ?_⟩
  · have hP₁ : P₁.IsPath := by rw [hPx] at hP; exact hP.of_append_left
    have hQ₂ : (Q.dropUntil x hxS').IsPath := hQ.dropUntil hxS'
    exact isPath_append_of_inter hP₁ hQ₂ fun z hz hz' =>
      hfirst z hz (Q.support_dropUntil_subset_support hxS' hz')
  · have hP₄ : P₄.IsPath := by rw [hPy] at hP; exact hP.of_append_right
    have hQ₃ : (Q.takeUntil y hyS').IsPath := hQ.takeUntil hyS'
    exact isPath_append_of_inter hQ₃ hP₄ fun z hz hz' =>
      hlast z hz' (Q.support_takeUntil_subset_support hyS' hz)

/-- The exact lengths of the two rerouted paths. -/
theorem length_reroute {a x d : V} (P₁ : G.Walk a x) (Q₂ : G.Walk x d) :
    (P₁.append Q₂).length = P₁.length + Q₂.length := Walk.length_append _ _

end Hypostructure.Graph.PathUncrossing
