import Hypostructure.Graph.CapacityFreeSide.Double
import Hypostructure.Graph.SparseOrderArithmetic

/-!
# Π_cs counted: a hub is in the support `T(q)` of at most `|H| − 1` ports

Generic: with no `C₄` and `H` independent, `q ↦ c(q)` injects
`{q ∈ 𝒜₀ : v ∈ T(q)}` into `H ∖ {v}` for every hub `v` (two such `q` with the
same centre `h'` give `v x_q h' x_{q'}`, a `C₄`).
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

theorem centreIncidence_le
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (hL4 : LengthOK 4) (noC4 : ¬ HasCycleWithLength LengthOK object)
    (indep : ∀ l r : object.Vertex, threshold < object.degree l →
      threshold < object.degree r → ¬ object.graph.Adj l r)
    (v : object.Vertex) (hv : threshold < object.degree v) :
    letI : FinEnum object.Vertex := object.vertices
    ((object.excessPorts threshold).filter fun q =>
        v ∈ (pairResponseActivation active).localBuffer q).card ≤
      ((Finset.univ.filter fun w => object.degree w ≠ threshold).erase v).card := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
    obtain ⟨hq, hvq⟩ := hq
    rw [pairResponseActivation_localBuffer_of_mem active hq] at hvq
    have high := FiniteObject.centre_high_of_mem_excessPorts hq
    have adj := FiniteObject.adj_of_mem_excessPorts hq
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨by omega, fun e => ?_⟩
    -- `v = c(q)` would make `v` its own shoulder or its own endpoint
    unfold FiniteObject.SurplusPort.support at hvq
    rcases Finset.mem_insert.1 hvq with h | h
    · exact object.graph.ne_of_adj adj (e.trans h)
    · exact ((FiniteObject.SurplusPort.mem_shoulders_iff _ _).1 h).1 e.symm
  · intro q hq q' hq' e
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
    obtain ⟨hq, hvq⟩ := hq
    obtain ⟨hq', hvq'⟩ := hq'
    rw [pairResponseActivation_localBuffer_of_mem active hq] at hvq
    rw [pairResponseActivation_localBuffer_of_mem active hq'] at hvq'
    have adj := FiniteObject.adj_of_mem_excessPorts hq
    have adj' := FiniteObject.adj_of_mem_excessPorts hq'
    have high := FiniteObject.centre_high_of_mem_excessPorts hq
    -- `v` is a shoulder of both (not an endpoint: the endpoint touches a hub)
    have sh : ∀ {d} (hd : d ∈ object.excessPorts threshold),
        v ∈ (object.surplusPortOfMem hd).support →
        v ≠ d.1 ∧ object.graph.Adj d.2 v := by
      intro d hd hvd
      unfold FiniteObject.SurplusPort.support at hvd
      rcases Finset.mem_insert.1 hvd with h | h
      · exact (indep _ _ (FiniteObject.centre_high_of_mem_excessPorts hd) hv
          (by rw [h]; exact FiniteObject.adj_of_mem_excessPorts hd)).elim
      · exact (FiniteObject.SurplusPort.mem_shoulders_iff _ _).1 h
    obtain ⟨n1, a1⟩ := sh hq hvq
    obtain ⟨n1', a1'⟩ := sh hq' hvq'
    by_contra hne
    have hx : q.2 ≠ q'.2 := fun hx => hne (Prod.ext e hx)
    apply noC4
    refine FiniteObject.hasC4_of_square hL4 (x := v) (y := q.1) (z := q.2) (w := q'.2)
      n1 (object.graph.ne_of_adj a1).symm (object.graph.ne_of_adj a1').symm
      (object.graph.ne_of_adj adj) (e ▸ object.graph.ne_of_adj adj') hx
      a1.symm adj.symm (e ▸ adj') a1'


/-- Double counting `Λ = Σ_p #{q : c(p) ∈ T(q)}`. -/
theorem Lambda_eq {α β : Type*} [DecidableEq α] [DecidableEq β] (P : Finset α) (c : α → β)
    (T : α → Finset β) :
    ∑ q ∈ P, ∑ v ∈ T q, (P.filter fun p => c p = v).card =
      ∑ p ∈ P, (P.filter fun q => c p ∈ T q).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq]

end Hypostructure.Graph.CapacityFreeSide
