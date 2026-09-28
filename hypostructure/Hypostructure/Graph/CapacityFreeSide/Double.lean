import Hypostructure.Graph.CapacityFreeSide.Witness

/-!
# Π_cs: the double suppression of a centre–shoulder pair (generic layer)

`c₁ = (x_p; h, a_p, b_p)`, `c₂ = (x_q; h_q, h, b_q)` with `c₂.left = c₁.center`
(the centre of `p` is a shoulder of `q`).  The live clause (f) forbids this pair
(`center_outside_support`), but the two suppressions compose: suppress `x_p`
(a one-configuration family), then suppress `x_q` inside the result.  The
composite `G₂ = G − x_p − x_q + a_p b_p + h b_q` keeps the baseline and has
`n − 2` vertices, so minimality forces it an accepted cycle.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}

noncomputable instance : FinEnum (PUnit.{u + 1}) :=
  FinEnum.ofEquiv (Fin 1) (Equiv.equivPUnit (Fin 1)).symm

/-- A single tight configuration is a compatible family. -/
noncomputable def singleFamily (c : TightVertexSuppression.Configuration object) :
    TightVertexSuppression.CompatibleFamily object where
  Index := PUnit.{u + 1}
  indices := inferInstance
  configuration := fun _ => c
  vertex_injective := fun _ _ _ => rfl
  support_disjoint := fun i j h => (h rfl).elim
  center_outside_support := fun _ _ =>
    ⟨(object.graph.ne_of_adj c.vertex_center).symm, c.center_ne_left, c.center_ne_right⟩
  chord_injective := fun _ _ _ => rfl

theorem singleFamily_capacity (c : TightVertexSuppression.Configuration object)
    (threshold : Nat) (high : threshold < object.degree c.center) :
    (singleFamily c).CenterCapacity threshold := by
  intro v _
  unfold TightVertexSuppression.CompatibleFamily.centerLoad
  by_cases hv : c.center = v
  · subst hv
    refine le_trans ?_ (show 1 ≤ object.degree c.center - threshold by omega)
    rw [Finset.card_le_one]
    intro a _ b _; rfl
  · rw [Finset.card_eq_zero.2 ?_]
    · exact Nat.zero_le _
    refine Finset.eq_empty_of_forall_notMem ?_
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hv hi

theorem singleFamily_centerLoad_of_ne (c : TightVertexSuppression.Configuration object)
    {v : object.Vertex} (hv : c.center ≠ v) : (singleFamily c).centerLoad v = 0 := by
  unfold TightVertexSuppression.CompatibleFamily.centerLoad
  rw [Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact hv hi

theorem mem_remaining_single (c : TightVertexSuppression.Configuration object)
    {v : object.Vertex} (hv : v ≠ c.vertex) : v ∈ (singleFamily c).remainingVertices := by
  simp only [TightVertexSuppression.CompatibleFamily.remainingVertices,
    TightVertexSuppression.CompatibleFamily.deletedVertices, Finset.mem_sdiff,
    object.mem_vertexFinset, true_and, Finset.mem_image, Finset.mem_univ, not_exists]
  intro _ h; exact hv h.symm

/-- **The second suppression, read inside `G₁ = G − x_p + a_p b_p`.** -/
noncomputable def secondConfig (c₁ c₂ : TightVertexSuppression.Configuration object)
    (hl : c₂.left = c₁.center)
    (hx : c₂.vertex ≠ c₁.vertex) (hxl : c₂.vertex ≠ c₁.left) (hxr : c₂.vertex ≠ c₁.right)
    (hc : c₂.center ≠ c₁.vertex) (hr : c₂.right ≠ c₁.vertex) :
    TightVertexSuppression.Configuration (singleFamily c₁).suppressed :=
  have hlv : c₂.left ≠ c₁.vertex := hl ▸ (object.graph.ne_of_adj c₁.vertex_center).symm
  { vertex := ⟨c₂.vertex, mem_remaining_single c₁ hx⟩
    center := ⟨c₂.center, mem_remaining_single c₁ hc⟩
    left := ⟨c₂.left, mem_remaining_single c₁ hlv⟩
    right := ⟨c₂.right, mem_remaining_single c₁ hr⟩
    vertex_center := by
      change (singleFamily c₁).suppressedGraph.Adj _ _
      rw [TightVertexSuppression.CompatibleFamily.suppressed_adj]
      exact Or.inl c₂.vertex_center
    vertex_left := by
      change (singleFamily c₁).suppressedGraph.Adj _ _
      rw [TightVertexSuppression.CompatibleFamily.suppressed_adj]
      exact Or.inl c₂.vertex_left
    vertex_right := by
      change (singleFamily c₁).suppressedGraph.Adj _ _
      rw [TightVertexSuppression.CompatibleFamily.suppressed_adj]
      exact Or.inl c₂.vertex_right
    neighbors := by
      intro o h
      change (singleFamily c₁).suppressedGraph.Adj _ _ at h
      rw [TightVertexSuppression.CompatibleFamily.suppressed_adj] at h
      rcases h with h | ⟨_, h | h⟩
      · rcases c₂.neighbors o.1 h with e | e | e
        · exact Or.inl (Subtype.ext e)
        · exact Or.inr (Or.inl (Subtype.ext e))
        · exact Or.inr (Or.inr (Subtype.ext e))
      · exact (hxl h.1).elim
      · exact (hxr h.1).elim
    center_ne_left := fun e => c₂.center_ne_left (congrArg Subtype.val e)
    center_ne_right := fun e => c₂.center_ne_right (congrArg Subtype.val e)
    left_ne_right := fun e => c₂.left_ne_right (congrArg Subtype.val e)
    shoulder_missing := by
      change ¬ (singleFamily c₁).suppressedGraph.Adj _ _
      rw [TightVertexSuppression.CompatibleFamily.suppressed_adj]
      rintro (h | ⟨_, h | h⟩)
      · exact c₂.shoulder_missing h
      · exact c₁.center_ne_left (hl.symm.trans h.1)
      · exact c₁.center_ne_right (hl.symm.trans h.1) }

/-- **The double suppression keeps the baseline, is lexicographically smaller
(`n − 2` vertices), and minimality forces it an accepted cycle.** -/
theorem double_suppression_forced {LengthOK : Nat → Prop} (threshold : Nat)
    (c₁ c₂ : TightVertexSuppression.Configuration object)
    (hl : c₂.left = c₁.center)
    (hx : c₂.vertex ≠ c₁.vertex) (hxl : c₂.vertex ≠ c₁.left) (hxr : c₂.vertex ≠ c₁.right)
    (hc : c₂.center ≠ c₁.vertex) (hr : c₂.right ≠ c₁.vertex)
    (baseline : threshold ≤ object.minDegree)
    (high₁ : threshold < object.degree c₁.center) (high₂ : threshold < object.degree c₂.center)
    (minimal : ∀ smaller : FiniteObject.{u}, smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller) :
    let G₂ := (singleFamily (secondConfig c₁ c₂ hl hx hxl hxr hc hr)).suppressed
    threshold ≤ G₂.minDegree ∧ G₂.vertexCount + 2 = object.vertexCount ∧
      G₂.LexicographicallySmaller object ∧ HasCycleWithLength LengthOK G₂ := by
  intro G₂
  set F₁ := singleFamily c₁
  set c₂' := secondConfig c₁ c₂ hl hx hxl hxr hc hr
  set F₂ := singleFamily c₂'
  have hcv : c₁.center ≠ c₁.vertex := (object.graph.ne_of_adj c₁.vertex_center).symm
  haveI : Nonempty F₁.suppressed.Vertex := ⟨⟨c₁.center, mem_remaining_single c₁ hcv⟩⟩
  have pres₁ := F₁.minimumDegree_preserved threshold baseline
    (singleFamily_capacity c₁ threshold high₁)
  have cc : c₁.center ≠ c₂.center := fun e => c₂.center_ne_left (e.symm.trans hl.symm) |>.elim
  have deg₂ : F₁.suppressed.degree c₂'.center = object.degree c₂.center := by
    have h := F₁.degree_add_centerLoad c₂'.center
    change F₁.suppressed.degree c₂'.center + F₁.centerLoad c₂.center = object.degree c₂.center at h
    rw [singleFamily_centerLoad_of_ne c₁ cc] at h
    simpa using h
  have hcv' : c₂'.center ≠ c₂'.vertex := (F₁.suppressed.graph.ne_of_adj c₂'.vertex_center).symm
  haveI : Nonempty F₂.suppressed.Vertex := ⟨⟨c₂'.center, mem_remaining_single c₂' hcv'⟩⟩
  have pres₂ := F₂.minimumDegree_preserved threshold pres₁
    (singleFamily_capacity c₂' threshold (by rw [deg₂]; exact high₂))
  have n₁ := F₁.vertexCount_suppressed
  have n₂ := F₂.vertexCount_suppressed
  have one₁ : Fintype.card F₁.Index = 1 :=
    Fintype.card_eq_one_iff.2 ⟨PUnit.unit, fun _ => rfl⟩
  have one₂ : Fintype.card F₂.Index = 1 :=
    Fintype.card_eq_one_iff.2 ⟨PUnit.unit, fun _ => rfl⟩
  have ca : F₂.suppressed.vertexCount + 1 = F₁.suppressed.vertexCount := by
    rw [← one₂]; exact n₂
  have cb : F₁.suppressed.vertexCount + 1 = object.vertexCount := by
    rw [← one₁]; exact n₁
  have count : G₂.vertexCount + 2 = object.vertexCount := by
    change F₂.suppressed.vertexCount + 2 = _
    omega
  have lex : G₂.LexicographicallySmaller object :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by omega)
  exact ⟨pres₂, count, lex, minimal G₂ lex pres₂⟩

/-- **The forced cycle is already present: `Q_p + a_p b_p`.**  If some suppression
path `Q_p` of the first configuration avoids `x_q`, the double suppression
carries the accepted cycle `Q_p + a_p b_p` (length `|Q_p| + 1`).  So the
minimality consequence of `double_suppression_forced` is discharged by the
single-port witness of `p` and imposes no further constraint on the pair. -/
theorem double_suppression_realized {LengthOK : Nat → Prop}
    (c₁ c₂ : TightVertexSuppression.Configuration object)
    (hl : c₂.left = c₁.center)
    (hx : c₂.vertex ≠ c₁.vertex) (hxl : c₂.vertex ≠ c₁.left) (hxr : c₂.vertex ≠ c₁.right)
    (hc : c₂.center ≠ c₁.vertex) (hr : c₂.right ≠ c₁.vertex)
    (W : FiniteObject.SurplusPort.OpenPortWitness object LengthOK c₁.vertex c₁.left c₁.right)
    (avoid : c₂.vertex ∉ W.path.support) :
    HasCycleWithLength LengthOK
      (singleFamily (secondConfig c₁ c₂ hl hx hxl hxr hc hr)).suppressed := by
  classical
  set F₁ := singleFamily c₁
  set c₂' := secondConfig c₁ c₂ hl hx hxl hxr hc hr
  set F₂ := singleFamily c₂'
  have r₁ : ∀ z ∈ W.path.support, z ∈ F₁.remainingVertices := fun z hz =>
    mem_remaining_single c₁ (fun e => W.avoids_endpoint (e ▸ hz))
  let Q₁ := liftWalk F₁ W.path r₁
  have r₂ : ∀ z ∈ Q₁.support, z ∈ F₂.remainingVertices := by
    intro z hz
    apply mem_remaining_single c₂'
    intro e
    apply avoid
    have : z.1 ∈ Q₁.support.map Subtype.val := List.mem_map_of_mem hz
    rw [liftWalk_support] at this
    rw [e] at this
    exact this
  let Q₂ := liftWalk F₂ Q₁ r₂
  have la : c₁.left ∈ F₁.remainingVertices := r₁ _ W.path.start_mem_support
  have lb : c₁.right ∈ F₁.remainingVertices := r₁ _ W.path.end_mem_support
  have la₂ : (⟨c₁.left, la⟩ : F₁.suppressed.Vertex) ∈ F₂.remainingVertices :=
    r₂ _ Q₁.start_mem_support
  have lb₂ : (⟨c₁.right, lb⟩ : F₁.suppressed.Vertex) ∈ F₂.remainingVertices :=
    r₂ _ Q₁.end_mem_support
  have chord : F₂.suppressed.graph.Adj ⟨⟨c₁.right, lb⟩, lb₂⟩ ⟨⟨c₁.left, la⟩, la₂⟩ := by
    change F₂.suppressedGraph.Adj _ _
    rw [TightVertexSuppression.CompatibleFamily.suppressed_adj]
    left
    change F₁.suppressedGraph.Adj _ _
    rw [TightVertexSuppression.CompatibleFamily.suppressed_adj]
    exact Or.inr ⟨PUnit.unit, Or.inr ⟨rfl, rfl⟩⟩
  let C : F₂.suppressed.graph.Walk ⟨⟨c₁.right, lb⟩, lb₂⟩ ⟨⟨c₁.right, lb⟩, lb₂⟩ := .cons chord Q₂
  have edges : ∀ e ∈ Q₂.edges, Sym2.map Subtype.val (Sym2.map Subtype.val e) ∈ W.path.edges := by
    intro e he
    have h1 : Sym2.map Subtype.val e ∈ Q₁.edges := by
      rw [← liftWalk_edges F₂ Q₁ r₂]; exact List.mem_map_of_mem he
    rw [← liftWalk_edges F₁ W.path r₁]; exact List.mem_map_of_mem h1
  have cyc : C.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨liftWalk_isPath F₂ Q₁ r₂ (liftWalk_isPath F₁ W.path r₁ W.isPath), fun h => ?_⟩
    have := W.path.adj_of_mem_edges (edges _ h)
    exact c₁.shoulder_missing this.symm
  refine ⟨⟨_, C, cyc, ?_⟩⟩
  simp only [C, SimpleGraph.Walk.length_cons]
  rw [liftWalk_length, liftWalk_length]
  exact W.restored_length_ok

end Hypostructure.Graph.CapacityFreeSide
