import Hypostructure.Graph.CapacityFreeSide.Compat

/-!
# Free side, step 1 (cont.): the two-port suppression family and its clause-(f) blocker
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- The support `T(d) = {x(d)} ∪ s(d)` of a selected port, as the activation reads it. -/
noncomputable abbrev portT {d : object.Vertex × object.Vertex}
    (hd : d ∈ object.excessPorts threshold) : Finset object.Vertex :=
  (object.surplusPortOfMem hd).support

/-- The activation's shoulder pair of a selected port, as a configuration. -/
noncomputable def portConfig
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {d : object.Vertex × object.Vertex} (hd : d ∈ object.excessPorts threshold)
    (openD : ¬ object.graph.Adj (pairResponseChordEnds active d).1
      (pairResponseChordEnds active d).2) :
    TightVertexSuppression.Configuration object :=
  (object.surplusPortOfMem hd).configuration
    (active.shoulderPair d hd).choose_spec.choose_spec.1
    (active.shoulderPair d hd).choose_spec.choose_spec.2
    (by
      have e : pairResponseChordEnds active d =
          ((active.shoulderPair d hd).choose,
            (active.shoulderPair d hd).choose_spec.choose) := by
        simp [pairResponseChordEnds, hd]
      rw [e] at openD
      exact openD)

section fields

variable (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
  {d : object.Vertex × object.Vertex} (hd : d ∈ object.excessPorts threshold)
  (openD : ¬ object.graph.Adj (pairResponseChordEnds active d).1
      (pairResponseChordEnds active d).2)

theorem portConfig_vertex : (portConfig active hd openD).vertex = d.2 := rfl
theorem portConfig_center : (portConfig active hd openD).center = d.1 := rfl
theorem portConfig_ends :
    pairResponseChordEnds active d =
      ((portConfig active hd openD).left, (portConfig active hd openD).right) := by
  simp only [pairResponseChordEnds, hd, dite_true]; rfl

theorem portConfig_vertex_mem : (portConfig active hd openD).vertex ∈ portT hd :=
  FiniteObject.SurplusPort.endpoint_mem_support _

theorem portConfig_left_mem : (portConfig active hd openD).left ∈ portT hd :=
  FiniteObject.SurplusPort.mem_support_of_mem_shoulders _
    (((active.shoulderPair d hd).choose_spec.choose_spec.1 _).2 (Or.inl rfl))

theorem portConfig_right_mem : (portConfig active hd openD).right ∈ portT hd :=
  FiniteObject.SurplusPort.mem_support_of_mem_shoulders _
    (((active.shoulderPair d hd).choose_spec.choose_spec.1 _).2 (Or.inr rfl))

end fields

noncomputable instance : FinEnum (ULift.{u} Bool) :=
  FinEnum.ofEquiv (Fin 2) (Equiv.ulift.trans finTwoEquiv.symm)

/-- **The two-port compatible family** `{p, q}` (index `true ↦ p`, `false ↦ q`). -/
noncomputable def pairFamily
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (disjT : Disjoint (portT hp) (portT hq))
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp) :
    TightVertexSuppression.CompatibleFamily object where
  Index := ULift.{u} Bool
  indices := inferInstance
  configuration := fun i => if i.down then portConfig active hp openP else portConfig active hq openQ
  vertex_injective := by
    have hx : (portConfig active hp openP).vertex ≠ (portConfig active hq openQ).vertex :=
      fun e => Finset.disjoint_left.1 disjT (portConfig_vertex_mem active hp openP)
        (e ▸ portConfig_vertex_mem active hq openQ)
    rintro ⟨i⟩ ⟨j⟩ h
    cases i <;> cases j <;> simp only [Bool.false_eq_true, if_false, if_true] at h
    · rfl
    · exact (hx h.symm).elim
    · exact (hx h).elim
    · rfl
  support_disjoint := by
    rintro ⟨i⟩ ⟨j⟩ hij
    have key : ∀ (c c' : TightVertexSuppression.Configuration object)
        (A B : Finset object.Vertex), Disjoint A B →
        c.vertex ∈ A → c.left ∈ A → c.right ∈ A →
        c'.vertex ∈ B → c'.left ∈ B → c'.right ∈ B →
        Disjoint ({c.vertex, c.left, c.right} : Set object.Vertex)
          {c'.vertex, c'.left, c'.right} := by
      intro c c' A B dAB h1 h2 h3 h4 h5 h6
      rw [Set.disjoint_left]
      intro a ha hb
      have hA : a ∈ A := by
        rcases ha with rfl | rfl | rfl <;> assumption
      have hB : a ∈ B := by
        rcases hb with rfl | rfl | rfl <;> assumption
      exact Finset.disjoint_left.1 dAB hA hB
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact key _ _ _ _ disjT.symm (portConfig_vertex_mem active hq openQ)
        (portConfig_left_mem active hq openQ) (portConfig_right_mem active hq openQ)
        (portConfig_vertex_mem active hp openP)
        (portConfig_left_mem active hp openP) (portConfig_right_mem active hp openP)
    · exact key _ _ _ _ disjT (portConfig_vertex_mem active hp openP)
        (portConfig_left_mem active hp openP) (portConfig_right_mem active hp openP)
        (portConfig_vertex_mem active hq openQ)
        (portConfig_left_mem active hq openQ) (portConfig_right_mem active hq openQ)
    · exact (hij rfl).elim
  center_outside_support := by
    have self : ∀ c : TightVertexSuppression.Configuration object,
        c.center ≠ c.vertex ∧ c.center ≠ c.left ∧ c.center ≠ c.right :=
      fun c => ⟨(object.graph.ne_of_adj c.vertex_center).symm, c.center_ne_left,
        c.center_ne_right⟩
    have cross : ∀ (c c' : TightVertexSuppression.Configuration object)
        (B : Finset object.Vertex), c.center ∉ B →
        c'.vertex ∈ B → c'.left ∈ B → c'.right ∈ B →
        c.center ≠ c'.vertex ∧ c.center ≠ c'.left ∧ c.center ≠ c'.right := by
      intro c c' B h h1 h2 h3
      exact ⟨fun e => h (e ▸ h1), fun e => h (e ▸ h2), fun e => h (e ▸ h3)⟩
    rintro ⟨i⟩ ⟨j⟩
    cases i <;> cases j
    · exact self _
    · exact cross _ _ _ hqT (portConfig_vertex_mem active hp openP)
        (portConfig_left_mem active hp openP) (portConfig_right_mem active hp openP)
    · exact cross _ _ _ hpT (portConfig_vertex_mem active hq openQ)
        (portConfig_left_mem active hq openQ) (portConfig_right_mem active hq openQ)
    · exact self _
  chord_injective := by
    classical
    have bad : ∀ (c c' : TightVertexSuppression.Configuration object)
        (A B : Finset object.Vertex), Disjoint A B →
        c.left ∈ A → c'.left ∈ B → c'.right ∈ B →
        s(c.left, c.right) ≠ s(c'.left, c'.right) := by
      intro c c' A B dAB h1 h2 h3 e
      have : c.left ∈ ({c'.left, c'.right} : Finset object.Vertex) := by
        have hm : c.left ∈ s(c.left, c.right) := Sym2.mem_mk_left _ _
        rw [e] at hm
        rcases Sym2.mem_iff.1 hm with h | h <;> simp [h]
      have hB : c.left ∈ B := by
        rcases Finset.mem_insert.1 this with h | h
        · exact h ▸ h2
        · exact (Finset.mem_singleton.1 h) ▸ h3
      exact Finset.disjoint_left.1 dAB h1 hB
    rintro ⟨i⟩ ⟨j⟩ h
    cases i <;> cases j
    · rfl
    · exact (bad _ _ _ _ disjT.symm (portConfig_left_mem active hq openQ)
        (portConfig_left_mem active hp openP) (portConfig_right_mem active hp openP) h).elim
    · exact (bad _ _ _ _ disjT (portConfig_left_mem active hp openP)
        (portConfig_left_mem active hq openQ) (portConfig_right_mem active hq openQ) h).elim
    · rfl

end Hypostructure.Graph.CapacityFreeSide
