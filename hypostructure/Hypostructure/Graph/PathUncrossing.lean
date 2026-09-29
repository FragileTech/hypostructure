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

/-- **The first ear.**  Two distinct paths `P, Q : x → y` of a simple graph: `Q` leaves
`P` at a first divergence `u` and first returns to `P` at `v`.  The segment `R : u → v`
of `Q` is a path, internally disjoint from `P`, different from the segment `Pm` of `P`
between `u` and `v`; so `Pm` and `R` are two internally disjoint `u`--`v` corridors,
the two pieces of one cell of a serial system. -/
theorem exists_ear : ∀ {x y : V} (P Q : G.Walk x y), P.IsPath → Q.IsPath → Q ≠ P →
    ∃ (u v : V) (P₁ : G.Walk x u) (Pm : G.Walk u v) (P₂ : G.Walk v y) (R : G.Walk u v),
      P = (P₁.append Pm).append P₂ ∧ R.IsPath ∧ R ≠ Pm ∧ u ≠ v ∧
      (∀ z ∈ R.support, z ∈ P.support → z = u ∨ z = v) ∧ (∀ z ∈ R.support, z ∈ Q.support) := by
  classical
  intro x y P
  induction P with
  | nil =>
      intro Q _ hQ hne
      exact absurd (Walk.isPath_iff_eq_nil.mp hQ) hne
  | @cons x x' y h P' ih =>
      intro Q hP hQ hne
      cases Q with
      | nil => exact absurd hP (by simp [Walk.isPath_def, Walk.support_cons])
      | @cons _ x'' _ h' Q' =>
          rw [Walk.cons_isPath_iff] at hP hQ
          by_cases hx : x'' = x'
          · subst hx
            have hne' : Q' ≠ P' := fun e => hne (by rw [e])
            obtain ⟨u, v, P₁, Pm, P₂, R, hPe, hR, hRne, huv, hint, hsub⟩ :=
              ih Q' hP.1 hQ.1 hne'
            refine ⟨u, v, .cons h P₁, Pm, P₂, R, by rw [hPe]; rfl, hR, hRne, huv, ?_, ?_⟩
            · intro z hz hzP
              rcases List.mem_cons.mp (by simpa using hzP) with rfl | hz'
              · exact absurd (hsub _ hz) hQ.2
              · exact hint z hz hz'
            · intro z hz
              exact List.mem_cons_of_mem _ (hsub z hz) |> fun t => by simpa using t
          · have hitex : ∃ z ∈ Q'.support, z ∈ {w | w ∈ (Walk.cons h P').support} :=
              ⟨y, Walk.end_mem_support _, by simp⟩
            obtain ⟨v, R', Q'', hQe, hvS, hfirst⟩ :=
              exists_first_hit (G := G) {w | w ∈ (Walk.cons h P').support} Q' hitex
            have hvP : v ∈ (Walk.cons h P').support := hvS
            have hvQ : v ∈ Q'.support := by rw [hQe]; simp
            have hvx : v ≠ x := fun e => hQ.2 (e ▸ hvQ)
            have hvP' : v ∈ P'.support := by
              rcases List.mem_cons.mp (by simpa using hvP) with e | e
              · exact absurd e hvx
              · exact e
            have hR'path : R'.IsPath := by
              have : Q'.IsPath := hQ.1
              rw [hQe] at this; exact this.of_append_left
            have hxR' : x ∉ R'.support := fun m => hQ.2 (by rw [hQe]; simp [m])
            refine ⟨x, v, .nil, .cons h (P'.takeUntil v hvP'), P'.dropUntil v hvP',
              .cons h' R', ?_, ?_, ?_, hvx.symm, ?_, ?_⟩
            · have := P'.take_spec hvP'
              simp only [Walk.nil_append]
              rw [Walk.cons_append, this]
            · rw [Walk.cons_isPath_iff]; exact ⟨hR'path, hxR'⟩
            · intro e
              have := congrArg (fun w => w.getVert 1) e
              simp at this
              exact hx this
            · intro z hz hzP
              rcases List.mem_cons.mp (by simpa using hz) with rfl | hz'
              · exact Or.inl rfl
              · exact Or.inr (hfirst z hz' hzP)
            · intro z hz
              rcases List.mem_cons.mp (by simpa using hz) with rfl | hz'
              · simp
              · have : z ∈ Q'.support := by rw [hQe]; simp [Walk.support_append, hz']
                simp [this]

end Hypostructure.Graph.PathUncrossing
